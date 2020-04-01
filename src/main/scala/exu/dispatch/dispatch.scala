//******************************************************************************
// Copyright (c) 2012 - 2019, The Regents of the University of California (Regents).
// All Rights Reserved. See LICENSE and LICENSE.SiFive for license details.
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
//------------------------------------------------------------------------------
// BOOM Instruction Dispatcher
//------------------------------------------------------------------------------
//------------------------------------------------------------------------------


package boom.exu

import chisel3._
import chisel3.util._
import freechips.rocketchip.config.Parameters
import boom.common.{IQT_MFP, MicroOp, O3PIPEVIEW_PRINTF, uopLD, _}
import boom.util._
import chisel3.internal.naming.chiselName


class DispatchIO(implicit p: Parameters) extends BoomBundle
{
  // incoming microops from rename2
  val ren_uops = Vec(coreWidth, Flipped(DecoupledIO(new MicroOp)))

  // outgoing microops to issue queues
  // N issues each accept up to dispatchWidth uops
  // dispatchWidth may vary between issue queues
  val dis_uops = MixedVec(issueParams.map(ip=>Vec(ip.dispatchWidth, DecoupledIO(new MicroOp))))
  // io for busy table - used only for LSC
  val busy_req_uops = if(boomParams.busyLookupMode) Some(Output(Vec(boomParams.busyLookupParams.get.lookupAtDisWidth, new MicroOp))) else None //TODO: change width
  val busy_resps = if(boomParams.busyLookupMode) Some(Input(Vec(boomParams.busyLookupParams.get.lookupAtDisWidth, new BusyResp))) else None
  val fp_busy_req_uops = if(boomParams.busyLookupMode && usingFPU) Some(Output(Vec(boomParams.busyLookupParams.get.lookupAtDisWidth, new MicroOp))) else None
  val fp_busy_resps = if(boomParams.busyLookupMode && usingFPU) Some(Input(Vec(boomParams.busyLookupParams.get.lookupAtDisWidth, new BusyResp))) else None
  // brinfo & flush for LSC
  val brinfo = if(boomParams.loadSliceMode || boomParams.dnbMode || boomParams.casMode) Some(Input(new BrResolutionInfo())) else None
  val flush = if(boomParams.loadSliceMode || boomParams.dnbMode || boomParams.casMode) Some(Input(Bool())) else None

  // CAS ports to UIQ
  val inq_heads =if(boomParams.casMode) Some(Vec(boomParams.casParams.get.inqDispatches, DecoupledIO(new MicroOp))) else None
  val sq_heads = if(boomParams.casMode) Some(Vec(boomParams.casParams.get.windowSize, DecoupledIO(new MicroOp))) else None

  // DnB ports to UIQ
  val dlq_head = if(boomParams.dnbMode) Some(Vec(boomParams.dnbParams.get.dlqDispatches, DecoupledIO(new MicroOp))) else None
  val crq_head = if(boomParams.dnbMode) Some(Vec(boomParams.dnbParams.get.crqDispatches, DecoupledIO(new MicroOp))) else None

  val tsc_reg = Input(UInt(width=xLen.W))

  val lsc_perf = if(boomParams.loadSliceMode) Some(Output(new LscDispatchPerfCounters)) else None
  val dnb_perf = if(boomParams.dnbMode) Some(Output(new DnbDispatchPerfCounters)) else None
  val cas_perf = if(boomParams.casMode) Some(Output(new CasDispatchPerfCounters)) else None
}


/**
  *
  * Performance counters for LSC
  */


class LscDispatchPerfCounters(implicit p: Parameters) extends BoomBundle {
  val aq = Vec(decodeWidth, Bool()) // Number of insts in A-Q
  val bq = Vec(decodeWidth, Bool()) // Number of insts on B-Q
}

class DnbDispatchPerfCounters(implicit p: Parameters) extends BoomBundle {
  val dlq = Vec(decodeWidth, Bool()) // Number of insts in DLQ
  val crq = Vec(decodeWidth, Bool()) // Number of insts on CRQ
  val iq = Vec(decodeWidth, Bool()) // Number of insts on IQ
}

class CasDispatchPerfCounters(implicit p: Parameters) extends BoomBundle {
  val inq_dis = Vec(boomParams.casParams.get.inqDispatches, Bool())
  val sq_dis = Vec(boomParams.casParams.get.windowSize, Bool())
}


abstract class Dispatcher(implicit p: Parameters) extends BoomModule
{
  val io = IO(new DispatchIO)
}

/**
 * This Dispatcher assumes worst case, all dispatched uops go to 1 issue queue
 * This is equivalent to BOOMv2 behavior
 */
class BasicDispatcher(implicit p: Parameters) extends Dispatcher
{
  issueParams.map(ip=>require(ip.dispatchWidth == coreWidth))

  val ren_readys = io.dis_uops.map(d=>VecInit(d.map(_.ready)).asUInt).reduce(_&_)

  for (w <- 0 until coreWidth) {
    io.ren_uops(w).ready := ren_readys(w)
  }

  for {i <- 0 until issueParams.size
       w <- 0 until coreWidth} {
    val issueParam = issueParams(i)
    val dis        = io.dis_uops(i)

    dis(w).valid := io.ren_uops(w).valid && ((io.ren_uops(w).bits.iq_type & issueParam.iqType.U) =/= 0.U)
    dis(w).bits  := io.ren_uops(w).bits
  }
}



/**
 *  Tries to dispatch as many uops as it can to issue queues,
 *  which may accept fewer than coreWidth per cycle.
 *  When dispatchWidth == coreWidth, its behavior differs
 *  from the BasicDispatcher in that it will only stall dispatch when
 *  an issue queue required by a uop is full.
 */
class CompactingDispatcher(implicit p: Parameters) extends Dispatcher
{
  issueParams.map(ip => require(ip.dispatchWidth >= ip.issueWidth))

  val ren_readys = Wire(Vec(issueParams.size, Vec(coreWidth, Bool())))

  for (((ip, dis), rdy) <- issueParams zip io.dis_uops zip ren_readys) {
    val ren = Wire(Vec(coreWidth, Decoupled(new MicroOp)))
    ren <> io.ren_uops

    val uses_iq = ren map (u => (u.bits.iq_type & ip.iqType.U).orR)

    // Only request an issue slot if the uop needs to enter that queue.
    (ren zip io.ren_uops zip uses_iq) foreach {case ((u,v),q) =>
      u.valid := v.valid && q}

    val compactor = Module(new Compactor(coreWidth, ip.dispatchWidth, new MicroOp))
    compactor.io.in  <> ren
    dis <> compactor.io.out

    // The queue is considered ready if the uop doesn't use it.
    rdy := ren zip uses_iq map {case (u,q) => u.ready || !q}
  }

  (ren_readys.reduce((r,i) =>
      VecInit(r zip i map {case (r,i) =>
        r && i})) zip io.ren_uops) foreach {case (r,u) =>
          u.ready := r}
}

