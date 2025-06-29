package vexiiriscv.memory

import spinal.core._
import spinal.lib._
import spinal.lib.misc.pipeline.{NodeBaseApi, Payload}
import spinal.lib.misc.plugin.FiberPlugin
import vexiiriscv.Global
import vexiiriscv.execute.{CsrAccessPlugin, CsrListFilter, CsrRamService}
import vexiiriscv.misc.{PipelineBuilderPlugin, PrivilegedPlugin, TrapReason}
import vexiiriscv.riscv.{CSR, Riscv}

import scala.collection.mutable.ArrayBuffer

/**
 * Reading the RISC-V spec to figure out all the flags/details of the PMP is just too tricky.
 * A good way to figure things out is to loook at spike (software implementation) :
 * - https://github.com/riscv-software-src/riscv-isa-sim/blob/2c67071743d4b55719cee22fdb319df2a0756db7/riscv/mmu.cc#L348
 * - https://github.com/riscv-software-src/riscv-isa-sim/blob/2c67071743d4b55719cee22fdb319df2a0756db7/riscv/csrs.cc#L183
 * - https://github.com/riscv-software-src/riscv-isa-sim/blob/2c67071743d4b55719cee22fdb319df2a0756db7/riscv/mmu.cc#L348
 *
 * In particular, one tricky thing with the PMP is how the PMPADDRx LSB bits are handled in regard of the granularity.
 * Their value change depending the PMPCFGx XD
 *
 * Smepmp (Enhanced PMP) Plugin implementation
 * 
 * This plugin implements the RISC-V Smepmp extension which enhances the Physical Memory Protection (PMP)
 * with additional security features including:
 * - Machine Security Configuration register (mseccfg)
 * - Rule Locking Bypass (RLB) 
 * - Machine Mode Whitelist Policy (MMWP)
 * - Machine Mode Lock Bypass (MML)
 * 
 * Key differences from standard PMP:
 * 1. When MML=1, locked PMP entries can be bypassed by M-mode when RLB=1
 * 2. When MMWP=1, M-mode follows PMP rules (whitelist policy) instead of bypass
 * 3. Additional security controls for preventing M-mode from accessing certain regions
 * 
 * Reference: RISC-V Smepmp Extension Specification v1.0
 */


case class PmpStorageParameter(slots : Int)
case class PmpPortParameter(var napotMatchAt : Int,
                            var napotHitsAt : Int,
                            var torCmpAt : Int,
                            var torHitsAt : Int,
                            var hitsAt : Int,
                            var rspAt : Int)


case class PmpParam(
  var pmpSize: Int,
  var granularity: Int,
  var withTor: Boolean = true,
  var withNapot: Boolean = true
)

/**
 * This PMP implementation is quite regular, but allows the user to get ports which are pipelined (to improve FMax / timings)
 */
class PmpPlugin(val p : PmpParam) extends FiberPlugin with PmpService{
  import p._

  override def getPmpNum(): Int = p.pmpSize

  assert(isPow2(granularity))
  val granularityWidth = log2Up(granularity)

  case class PortSpec(stages: Seq[NodeBaseApi],
                      physicalAddress: Payload[UInt],
                      forceCheck: NodeBaseApi => Bool,
                      read: NodeBaseApi => Bool,
                      write: NodeBaseApi => Bool,
                      execute: NodeBaseApi => Bool,
                      pp: PmpPortParameter,
                      rsp : PmpRsp){
    val permStage = stages(0)
    val napotMatchStage = stages(pp.napotMatchAt)
    val napotHitsStage = stages(pp.napotHitsAt)
    val torCmpStage = stages(pp.torCmpAt)
    val torHitsStage = stages(pp.torHitsAt)
    val hitsStage = stages(pp.hitsAt)
    val rspStage  = stages(pp.rspAt)
  }
  val portSpecs = ArrayBuffer[PortSpec]()

  override def createPmpPort(nodes: Seq[NodeBaseApi],
                             physicalAddress: Payload[UInt],
                             forceCheck: NodeBaseApi => Bool,
                             read: NodeBaseApi => Bool,
                             write: NodeBaseApi => Bool,
                             execute: NodeBaseApi => Bool,
                             portSpec: Any,
                             storageSpec: Any): PmpRsp = {
    val pp = portSpec.asInstanceOf[PmpPortParameter]
    portSpecs.addRet(
      new PortSpec(
        stages          = nodes,
        physicalAddress = physicalAddress,
        forceCheck      = forceCheck,
        read            = read,
        write           = write,
        execute         = execute,
        pp              = pp,
        rsp             = new PmpRsp()
      )
    ).rsp
  }

  val logic = during setup new Area{
    val priv = host[PrivilegedPlugin]
    val csr = host[CsrAccessPlugin]
    val ram = host[CsrRamService]

    val csrLock = retains(csr.csrLock, ram.csrLock)
    val buildBefore = retains(List(host[PipelineBuilderPlugin].elaborationLock))

    awaitBuild()

    if(Riscv.XLEN.get == 64) assert(
      granularity >= 8,
      """VexiiRiscv RV64 doesn't support granularity smaller than 8 bytes, as during 8 bytes accesses,
        | it would need to check that the upper 4 bytes of access are contained in the pmp regions as well""".stripMargin
    )

    case class Cfg() extends Bundle{
      val kind = Bits(2 bits)
      val read, write, execute = Bool()
      val locked = Bool()
    }

    // Machine Security Configuration register (mseccfg) - Enhanced PMP feature
    case class MseccfgReg() extends Bundle {
      val reserved = Bits(29 bits)
      val mml = Bool()  // Machine Mode Lock Bypass
      val mmwp = Bool() // Machine Mode Whitelist Policy  
      val rlb = Bool()  // Rule Locking Bypass
    }

    val mseccfg = withMseccfg generate Reg(MseccfgReg())
    if (withMseccfg) {
      mseccfg.reserved.init(0)
      mseccfg.mml.init(False)
      mseccfg.mmwp.init(False)
      mseccfg.rlb.init(False)
    }

    val pRange = Global.PHYSICAL_WIDTH - 1 downto granularityWidth
    val extraBit = granularity > 4

    // Generate all the PMP entries storage + CSR mapping
    val entries = for(i <- 0 until pmpSize) yield new Area{
      val isLocked = Bool()
      val address = Reg(UInt(Global.PHYSICAL_WIDTH.get - granularityWidth + extraBit.toInt bits))
      val cfg = Reg(Cfg())
      val cfgNext = CombInit(cfg)

      // Enhanced PMP locking logic with MML and RLB support
      val effectiveLocked = withMseccfg.mux(
        cfg.locked && !(mseccfg.mml && mseccfg.rlb),
        cfg.locked
      )

      when(!effectiveLocked) {
        cfg := cfgNext
        cfg.write clearWhen (!cfgNext.read)
        if(!p.withTor) when(cfgNext.kind === 1) {cfg.kind := 0}
        if(!p.withNapot){
          if(granularity > 4) when(cfgNext.kind === 2) {cfg.kind := 0}
          when(cfgNext.kind === 3) {cfg.kind := 0}
        }
      }

      if(i == 0){
        // Allow software unaware of PMP to access all memory by default
        assert(p.withNapot)
        address.init(address.getAllTrue)
        cfg.read init(True)
        cfg.write init(True)
        cfg.execute init(True)
        cfg.kind init(3)
        cfg.locked init(False)
      } else {
        address.init(0)
        cfg.initZero()
      }


      val isNapot = RegNext(cfg.kind(1))
      val isTor = RegNext(cfg.kind === 1)
      val napot = Napot(address.dropHigh(1)).dropLow(extraBit.toInt)
      if(granularity == 4) when(!cfg.kind(0)){ napot.setAll() }
      val mask = RegNext(napot)

      val (cfgId, cfgOffset) = Riscv.XLEN.get match{
        case 32 => (i/4, i%4*8)
        case 64 => (i/8*2, i%8*8)
      }

      csr.writeCancel(CSR.PMPADDR + i, isLocked)
      csr.read(address(address.bitsRange.drop(extraBit.toInt)), CSR.PMPADDR + i, granularityWidth-2)
      csr.write(address(address.bitsRange), CSR.PMPADDR + i, granularityWidth-2-extraBit.toInt)
      if(granularity > 4 && p.withNapot) csr.read(U(granularityWidth-2 bits, default -> isNapot, granularityWidth-3 -> (address.lsb && isNapot)), CSR.PMPADDR + i) //WTF
      csr.read(CSR.PMPCFG + cfgId,  0+cfgOffset -> cfg.read, 1+cfgOffset -> cfg.write, 2+cfgOffset -> cfg.execute, 3+cfgOffset -> cfg.kind, 7+cfgOffset -> cfg.locked)
      csr.write(CSR.PMPCFG + cfgId,  0+cfgOffset -> cfgNext.read, 1+cfgOffset -> cfgNext.write, 2+cfgOffset -> cfgNext.execute, 3+cfgOffset -> cfgNext.kind, 7+cfgOffset -> cfgNext.locked)
    }

    for (i <- 0 until pmpSize; self = entries(i)) {
      val nextEntryLocked = (i + 1 != pmpSize).mux(entries(i + 1).cfg.locked && entries(i + 1).isTor, False)
      val effectiveNextLocked = withMseccfg.mux(
        nextEntryLocked && !(mseccfg.mml && mseccfg.rlb),
        nextEntryLocked
      )
      self.isLocked := self.cfg.locked || effectiveNextLocked
    }

    // Add mseccfg CSR mapping
    if (withMseccfg) {
      val MSECCFG = 0x747
      csr.read(MSECCFG, 0 -> mseccfg.rlb, 1 -> mseccfg.mmwp, 2 -> mseccfg.mml)
      csr.write(MSECCFG, 0 -> mseccfg.rlb, 1 -> mseccfg.mmwp, 2 -> mseccfg.mml)
    }

    val allFilter = CsrListFilter((0 to 15).map(_ + CSR.PMPADDR) ++ (0 to 3).filter(i => Riscv.XLEN.get == 32 || (i % 2) == 0).map(_ + CSR.PMPCFG) ++ (if (withMseccfg) Seq(0x747) else Seq.empty))
    if(p.pmpSize > 0) csr.onDecode(allFilter) {
      when(csr.bus.decode.write) {
        csr.bus.decode.doTrap(TrapReason.NEXT)
      }
    }

    assert(Global.HART_COUNT.get == 1)

    csrLock.release()
    portsLock.await()

    val isMachine = priv.isMachine(0)
    
    // Enhanced PMP logic with Smepmp features
    val instructionShouldHit = withMseccfg.mux(
      !isMachine || (mseccfg.mmwp && isMachine),
      !isMachine
    )
    
    val dataShouldHit = withMseccfg.mux(
      !isMachine || (mseccfg.mmwp && isMachine) || (priv.logic.harts(0).m.status.mprv && priv.logic.harts(0).m.status.mpp =/= 3),
      !isMachine || priv.logic.harts(0).m.status.mprv && priv.logic.harts(0).m.status.mpp =/= 3
    )

    val ports = for(ps <- portSpecs) yield new Composite(ps.rsp, "logic", false){
      import ps._
      val dataShouldHitPort = dataShouldHit || ps.forceCheck(permStage)
      val torCmpAddress = torCmpStage(ps.physicalAddress) >> granularityWidth
      val TOR_SMALLER = new Array[Payload[Bool]](p.pmpSize)
      val onEntries = for((e, id) <- entries.zipWithIndex) yield new Area{
        val napot = p.withNapot generate new Area {
          val MATCH = napotMatchStage.insert(((e.address.dropLow(extraBit.toInt).asUInt << granularityWidth)(pRange) ^ napotMatchStage(ps.physicalAddress)(pRange)).asBits & e.mask)
          val HIT = napotHitsStage.insert(napotHitsStage(MATCH) === 0)
        }
        val tor = p.withTor generate new Area{
          val BIGGER = torCmpStage.insert((e.address >> extraBit.toInt) > torCmpAddress)
          val HIT = { import torHitsStage._ ; insert(BIGGER && (id != 0).mux(!TOR_SMALLER(id-1), True))}
          TOR_SMALLER(id) = BIGGER
        }
        val HIT_ANY = { import hitsStage._ ; insert(p.withNapot.mux(e.isNapot && napot.HIT, False) || p.withTor.mux(e.isTor && tor.HIT, False)) }

        // Enhanced permission checking with Smepmp features
        val modeCheck = withMseccfg.mux(
          // With Smepmp: check if entry is locked or if we should enforce PMP rules
          e.cfg.locked || instructionShouldHit || dataShouldHitPort,
          // Without Smepmp: original logic
          e.cfg.locked || instructionShouldHit
        )

        val instructionCheck = withMseccfg.mux(
          e.cfg.locked || instructionShouldHit,
          e.cfg.locked || instructionShouldHit
        )
        
        val dataCheck = withMseccfg.mux(
          e.cfg.locked || dataShouldHitPort,
          e.cfg.locked || dataShouldHitPort
        )

        val normalRwx = (!ps.execute(permStage) || e.cfg.execute || !instructionCheck) &&
          (((!ps.write(permStage) || e.cfg.write) && (!ps.read(permStage) || e.cfg.read)) || !dataCheck)
        val PERM_OK = permStage.insert(normalRwx)
      }
      val NEED_HIT = permStage.insert(instructionShouldHit && ps.execute(permStage) || dataShouldHitPort && (ps.read(permStage) || ps.write(permStage)))

      val onCtrl = (p.pmpSize > 0) generate new Area{
        import ps.rspStage._
        val hits = Cat(onEntries.map(e => ps.rspStage(e.HIT_ANY)))
        val oh = OHMasking.firstV2(hits)
        val reader = onEntries.reader(oh)
        val entriesReader = entries.reader(oh)

        // Enhanced access fault logic with Smepmp considerations
        val baseFault = (NEED_HIT || entriesReader(e => e.isLocked)) && !(reader(e => ps.rspStage(e.PERM_OK)))
        
        rsp.ACCESS_FAULT := withMseccfg.mux(
          // With Smepmp: consider MML and MMWP flags
          baseFault && !(mseccfg.mml && mseccfg.rlb && isMachine && !mseccfg.mmwp),
          // Without Smepmp: original logic
          baseFault
        )
      }
      if(p.pmpSize == 0) ps.rspStage(rsp.ACCESS_FAULT) := False
    }


    buildBefore.release()
  }
}