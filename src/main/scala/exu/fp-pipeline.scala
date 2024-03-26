//******************************************************************************
// Copyright (c) 2015 - 2018, The Regents of the University of California (Regents).
// All Rights Reserved. See LICENSE and LICENSE.SiFive for license details.
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
//------------------------------------------------------------------------------
// Floating Point Datapath Pipeline
//------------------------------------------------------------------------------
//------------------------------------------------------------------------------

package boom.exu

import chisel3._
import chisel3.util._

import freechips.rocketchip.config.{Parameters}
import freechips.rocketchip.rocket
import freechips.rocketchip.tile

import boom.exu.FUConstants._
import boom.common._
import boom.util.{BoomCoreStringPrefix}

/**
 * Top level datapath that wraps the floating point issue window, regfile, and arithmetic units.
 */
class FpPipeline(implicit p: Parameters) extends BoomModule with tile.HasFPUParameters
{
  val fpIssueParams = issueParams.find(_.iqType == IQT_FP.litValue).get
  val dispatchWidth = fpIssueParams.dispatchWidth
  val numLlPorts = memWidth
  val numWakeupPorts = fpIssueParams.issueWidth + numLlPorts
  val fpPregSz = log2Ceil(numFpPhysRegs)

  val io = IO(new Bundle {
    val brupdate         = Input(new BrUpdateInfo())
    val flush_pipeline   = Input(Bool())
    val fcsr_rm          = Input(UInt(width=freechips.rocketchip.tile.FPConstants.RM_SZ.W))
    val status           = Input(new freechips.rocketchip.rocket.MStatus())

    val dis_uops         = Vec(dispatchWidth, Flipped(Decoupled(new MicroOp)))

    // +1 for recoding.
    val ll_wports        = if (!enableNDA) Flipped(Vec(memWidth, Decoupled(new ExeUnitResp(fLen+1)))) else null// from memory unit
    val ll_mem_wports    = if (enableNDA) Flipped(Vec(memWidth, Decoupled(new MemExeUnitResp(fLen+1)))) else null
    val from_int         = Flipped(Decoupled(new ExeUnitResp(fLen+1)))// from integer RF
    val to_sdq           = Decoupled(new ExeUnitResp(fLen))           // to Load/Store Unit
    val to_int           = Decoupled(new ExeUnitResp(xLen))           // to integer RF

    val wakeups          = Vec(numWakeupPorts, Valid(new ExeUnitResp(fLen+1)))
    // Taint tracking
    val taint_wakeup_port     = Flipped(Vec(numTaintWakeupPorts, Valid(UInt(ldqAddrSz.W))))
    val ldq_head = Input(UInt(ldqAddrSz.W))
    val ldq_tail = Input(UInt(ldqAddrSz.W))
    val wb_valids        = Input(Vec(numWakeupPorts, Bool()))
    val wb_pdsts         = Input(Vec(numWakeupPorts, UInt(width=fpPregSz.W)))

    val ldq_flipped         = Input(Bool())

    val req_uops        = if (enableRegisterTaintTracking) Output(Vec(issueParams.find(_.iqType == IQT_FP.litValue).get.issueWidth, Valid(new MicroOp()))) else null

    val yrot_resp        = if (enableRegisterTaintTracking) Input(Vec(issueParams.find(_.iqType == IQT_FP.litValue).get.issueWidth, Valid(new RegYrotResp()))) else null
    
    val debug_tsc_reg    = Input(UInt(width=xLen.W))
    val debug_wb_wdata   = Output(Vec(numWakeupPorts, UInt((fLen+1).W)))
    val slot0_valid      = Output(Bool())
    val slot0_yrot       = Output(UInt(ldqAddrSz.W))
    val slot0_yrot_r     = Output(Bool())
  })

  //**********************************
  // construct all of the modules

  val exe_units      = new boom.exu.ExecutionUnits(fpu=true)
  val issue_unit     = Module(new IssueUnitCollapsing(
                         issueParams.find(_.iqType == IQT_FP.litValue).get,
                         numWakeupPorts))
  issue_unit.suggestName("fp_issue_unit")
  val fregfile       = Module(new RegisterFileSynthesizable(numFpPhysRegs,
                         exe_units.numFrfReadPorts,
                         exe_units.numFrfWritePorts + memWidth,
                         fLen+1,
                         // No bypassing for any FP units, + memWidth for ll_wb
                         Seq.fill(exe_units.numFrfWritePorts + memWidth){ false }
                         ))
  val fregister_read = Module(new RegisterRead(
                         issue_unit.issueWidth,
                         exe_units.withFilter(_.readsFrf).map(_.supportedFuncUnits),
                         exe_units.numFrfReadPorts,
                         exe_units.withFilter(_.readsFrf).map(x => 3),
                         0, // No bypass for FP
                         0,
                         fLen+1))

  require (exe_units.count(_.readsFrf) == issue_unit.issueWidth)
  require (exe_units.numFrfWritePorts + numLlPorts == numWakeupPorts)

  //*************************************************************
  // Issue window logic

  val iss_valids = Wire(Vec(exe_units.numFrfReaders, Bool()))
  val iss_uops   = Wire(Vec(exe_units.numFrfReaders, new MicroOp()))

  issue_unit.io.tsc_reg := io.debug_tsc_reg
  issue_unit.io.brupdate := io.brupdate
  issue_unit.io.flush_pipeline := io.flush_pipeline
  // Don't support ld-hit speculation to FP window.
  for (w <- 0 until memWidth) {
    issue_unit.io.spec_ld_wakeup(w).valid := false.B
    issue_unit.io.spec_ld_wakeup(w).bits := 0.U
  }
  issue_unit.io.ld_miss := false.B

  io.slot0_valid := issue_unit.io.slot0_valid
  io.slot0_yrot := issue_unit.io.slot0_yrot
  io.slot0_yrot_r := issue_unit.io.slot0_yrot_r

  require (exe_units.numTotalBypassPorts == 0)

  if (enableRegisterTaintTracking) {

    for (i <- 0 until issue_unit.issueWidth) {
      io.req_uops(i) := issue_unit.io.req_uops(i)
      issue_unit.io.yrot_resp(i) := io.yrot_resp(i)
    }
  }

  if (enableRegisterTaintTracking) {
    dontTouch(io.req_uops)
  }

  //-------------------------------------------------------------
  // **** Dispatch Stage ****
  //-------------------------------------------------------------

  // Input (Dispatch)
  for (w <- 0 until dispatchWidth) {
    issue_unit.io.dis_uops(w) <> io.dis_uops(w)
  }

  //-------------------------------------------------------------
  // **** Issue Stage ****
  //-------------------------------------------------------------

  // Output (Issue)
  for (i <- 0 until issue_unit.issueWidth) {
    if (enableRegisterTaintTracking) {
      iss_valids(i) := issue_unit.io.iss_valids(i) && (io.yrot_resp(i).bits.yrot_r || (!io.req_uops(i).valid))
    } else {
      iss_valids(i) := issue_unit.io.iss_valids(i)
    }
    iss_uops(i) := issue_unit.io.iss_uops(i)

    var fu_types = exe_units(i).io.fu_types
    if (exe_units(i).supportedFuncUnits.fdiv) {
      val fdiv_issued = iss_valids(i) && iss_uops(i).fu_code_is(FU_FDV)
      fu_types = fu_types & RegNext(~Mux(fdiv_issued, FU_FDV, 0.U))
    }
    issue_unit.io.fu_types(i) := fu_types

    require (exe_units(i).readsFrf)
  }

  // Taint Tracking
  for ((iu, twp) <- issue_unit.io.taint_wakeup_port zip io.taint_wakeup_port) {
    iu.valid := twp.valid
    iu.bits := twp.bits
  }

  issue_unit.io.ldq_head := io.ldq_head
  issue_unit.io.ldq_tail := io.ldq_tail

  // Wakeup
  for ((writeback, issue_wakeup) <- io.wakeups zip issue_unit.io.wakeup_ports) {
    issue_wakeup.valid := writeback.valid
    issue_wakeup.bits.pdst  := writeback.bits.uop.pdst
    issue_wakeup.bits.poisoned := false.B
  }
  issue_unit.io.pred_wakeup_port.valid := false.B
  issue_unit.io.pred_wakeup_port.bits := DontCare

  //-------------------------------------------------------------
  // **** Register Read Stage ****
  //-------------------------------------------------------------

  // Register Read <- Issue (rrd <- iss)
  fregister_read.io.rf_read_ports <> fregfile.io.read_ports
  fregister_read.io.prf_read_ports map { port => port.data := false.B }

  fregister_read.io.iss_valids <> iss_valids
  fregister_read.io.iss_uops := iss_uops

  fregister_read.io.brupdate := io.brupdate
  fregister_read.io.kill := io.flush_pipeline

  //-------------------------------------------------------------
  // **** Execute Stage ****
  //-------------------------------------------------------------

  exe_units.map(_.io.brupdate := io.brupdate)

  for ((ex,w) <- exe_units.withFilter(_.readsFrf).map(x=>x).zipWithIndex) {
    ex.io.req <> fregister_read.io.exe_reqs(w)
    require (!ex.bypassable)
  }
  require (exe_units.numTotalBypassPorts == 0)

  //-------------------------------------------------------------
  // **** Writeback Stage ****
  //-------------------------------------------------------------

  val ll_wbarb = if (!enableNDA) Module(new Arbiter(new ExeUnitResp(fLen+1), 2)) else null
  val ll_mem_wbarb = if (enableNDA) Module(new Arbiter(new MemExeUnitResp(fLen+1), 2)) else null


  val ifpu_resp = io.from_int
  if (!enableNDA) {
  // Hookup load writeback -- and recode FP values.
  ll_wbarb.io.in(0) <> io.ll_wports(0)
  ll_wbarb.io.in(0).bits.data := recode(io.ll_wports(0).bits.data,
                                        io.ll_wports(0).bits.uop.mem_size =/= 2.U)

  ll_wbarb.io.in(1) <> ifpu_resp
  } else {
  // Hookup load writeback -- and recode FP values.
  ll_mem_wbarb.io.in(0) <> io.ll_mem_wports(0)
  ll_mem_wbarb.io.in(0).bits.data := recode(io.ll_mem_wports(0).bits.data,
                                        io.ll_mem_wports(0).bits.uop.mem_size =/= 2.U)

  ll_mem_wbarb.io.in(1) <> ifpu_resp  
  ll_mem_wbarb.io.in(1).bits.noBroadcast := false.B
  ll_mem_wbarb.io.in(1).bits.noData := false.B
  ll_mem_wbarb.io.in(1).bits.splitDataAndBroadcast := false.B
  ll_mem_wbarb.io.in(1).bits.broadcastUop := ifpu_resp.bits.uop
  }


  // Cut up critical path by delaying the write by a cycle.
  // Wakeup signal is sent on cycle S0, write is now delayed until end of S1,
  // but Issue happens on S1 and RegRead doesn't happen until S2 so we're safe.
  if (!enableNDA) {
  fregfile.io.write_ports(0) := RegNext(WritePort(ll_wbarb.io.out, fpregSz, fLen+1, RT_FLT))
  } else {
  fregfile.io.write_ports(0) := RegNext(WritePort(ll_mem_wbarb.io.out, fpregSz, fLen+1, RT_FLT))
  }

  if (!enableNDA) {
  assert (ll_wbarb.io.in(0).ready) // never backpressure the memory unit.
  } else {
  assert (ll_mem_wbarb.io.in(0).ready) // never backpressure the memory unit.
  }
  when (ifpu_resp.valid) { assert (ifpu_resp.bits.uop.rf_wen && ifpu_resp.bits.uop.dst_rtype === RT_FLT) }

  var w_cnt = 1
  for (i <- 1 until memWidth) {
    if (!enableNDA) {
    fregfile.io.write_ports(w_cnt) := RegNext(WritePort(io.ll_wports(i), fpregSz, fLen+1, RT_FLT))
    fregfile.io.write_ports(w_cnt).bits.data := RegNext(recode(io.ll_wports(i).bits.data,
                                                               io.ll_wports(i).bits.uop.mem_size =/= 2.U))
    } else {
    fregfile.io.write_ports(w_cnt) := RegNext(WritePort(io.ll_mem_wports(i), fpregSz, fLen+1, RT_FLT))
    fregfile.io.write_ports(w_cnt).bits.data := RegNext(recode(io.ll_mem_wports(i).bits.data,
                                                               io.ll_mem_wports(i).bits.uop.mem_size =/= 2.U))
    }
    w_cnt += 1
  }
  for (eu <- exe_units) {
    if (eu.writesFrf) {
      fregfile.io.write_ports(w_cnt).valid     := eu.io.fresp.valid && eu.io.fresp.bits.uop.rf_wen
      fregfile.io.write_ports(w_cnt).bits.addr := eu.io.fresp.bits.uop.pdst
      fregfile.io.write_ports(w_cnt).bits.data := eu.io.fresp.bits.data
      eu.io.fresp.ready                        := true.B
      when (eu.io.fresp.valid) {
        assert(eu.io.fresp.ready, "No backpressuring the FPU")
        assert(eu.io.fresp.bits.uop.rf_wen, "rf_wen must be high here")
        assert(eu.io.fresp.bits.uop.dst_rtype === RT_FLT, "wb type must be FLT for fpu")
      }
      w_cnt += 1
    }
  }
  require (w_cnt == fregfile.io.write_ports.length)

  val fpiu_unit = exe_units.fpiu_unit
  if (!enableNDA) {
  val fpiu_is_sdq = fpiu_unit.io.ll_iresp.bits.uop.uopc === uopSTA
  io.to_int.valid := fpiu_unit.io.ll_iresp.fire && !fpiu_is_sdq
  io.to_sdq.valid := fpiu_unit.io.ll_iresp.fire &&  fpiu_is_sdq
  io.to_int.bits  := fpiu_unit.io.ll_iresp.bits
  io.to_sdq.bits  := fpiu_unit.io.ll_iresp.bits
  fpiu_unit.io.ll_iresp.ready := io.to_sdq.ready && io.to_int.ready
  } else {
  val fpiu_is_sdq = fpiu_unit.io.ll_mem_iresp.bits.uop.uopc === uopSTA
  io.to_int.valid := fpiu_unit.io.ll_mem_iresp.fire && !fpiu_is_sdq
  io.to_sdq.valid := fpiu_unit.io.ll_mem_iresp.fire &&  fpiu_is_sdq
  io.to_int.bits  := fpiu_unit.io.ll_mem_iresp.bits
  io.to_sdq.bits  := fpiu_unit.io.ll_mem_iresp.bits
  fpiu_unit.io.ll_mem_iresp.ready := io.to_sdq.ready && io.to_int.ready
  }

  //-------------------------------------------------------------
  //-------------------------------------------------------------
  // **** Commit Stage ****
  //-------------------------------------------------------------
  //-------------------------------------------------------------

  if (!enableNDA) {
  io.wakeups(0).valid := ll_wbarb.io.out.valid
  io.wakeups(0).bits := ll_wbarb.io.out.bits
  ll_wbarb.io.out.ready := true.B
  } else {
  io.wakeups(0).valid := ll_mem_wbarb.io.out.valid &&
                         ll_mem_wbarb.io.out.bits.broadcastUop.dst_rtype === RT_FLT &&
                         !ll_mem_wbarb.io.out.bits.noBroadcast
  io.wakeups(0).bits.uop := ll_mem_wbarb.io.out.bits.broadcastUop
  io.wakeups(0).bits.predicated := ll_mem_wbarb.io.out.bits.predicated
  io.wakeups(0).bits.fflags := ll_mem_wbarb.io.out.bits.fflags
  io.wakeups(0).bits.data := ll_mem_wbarb.io.out.bits.data
  ll_mem_wbarb.io.out.ready := true.B  
  }

  w_cnt = 1
  for (i <- 1 until memWidth) {
    if (!enableNDA) {
    io.wakeups(w_cnt) := io.ll_wports(i)
    io.wakeups(w_cnt).bits.data := recode(io.ll_wports(i).bits.data,
      io.ll_wports(i).bits.uop.mem_size =/= 2.U)
    } else {
    io.wakeups(w_cnt).valid := io.ll_mem_wports(i).valid &&
                               io.ll_mem_wports(i).bits.broadcastUop.dst_rtype === RT_FLT &&
                               !io.ll_mem_wports(i).bits.noBroadcast
    io.wakeups(w_cnt).bits.uop := io.ll_mem_wports(i).bits.broadcastUop
    io.wakeups(w_cnt).bits.predicated := io.ll_mem_wports(i).bits.predicated
    io.wakeups(w_cnt).bits.fflags := io.ll_mem_wports(i).bits.fflags
    io.wakeups(w_cnt).bits.data := recode(io.ll_mem_wports(i).bits.data,
      io.ll_mem_wports(i).bits.uop.mem_size =/= 2.U)
    }
    w_cnt += 1
  }
  for (eu <- exe_units) {
    if (eu.writesFrf) {
      val exe_resp = eu.io.fresp
      val wb_uop = eu.io.fresp.bits.uop
      val wport = io.wakeups(w_cnt)
      wport.valid := exe_resp.valid && wb_uop.dst_rtype === RT_FLT
      wport.bits := exe_resp.bits

      w_cnt += 1

      assert(!(exe_resp.valid && wb_uop.uses_ldq))
      assert(!(exe_resp.valid && wb_uop.uses_stq))
      assert(!(exe_resp.valid && wb_uop.is_amo))
    }
  }

  for ((wdata, wakeup) <- io.debug_wb_wdata zip io.wakeups) {
    wdata := ieee(wakeup.bits.data)
  }

  exe_units.map(_.io.fcsr_rm := io.fcsr_rm)
  exe_units.map(_.io.status := io.status)

  //-------------------------------------------------------------
  // **** Flush Pipeline ****
  //-------------------------------------------------------------
  // flush on exceptions, miniexeptions, and after some special instructions

  for (w <- 0 until exe_units.length) {
    exe_units(w).io.req.bits.kill := io.flush_pipeline
  }

  override def toString: String =
    (BoomCoreStringPrefix("===FP Pipeline===") + "\n"
    + fregfile.toString
    + BoomCoreStringPrefix(
      "Num Wakeup Ports      : " + numWakeupPorts,
      "Num Bypass Ports      : " + exe_units.numTotalBypassPorts))
}
