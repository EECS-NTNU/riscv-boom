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

@chiselName
class DnbDispatcher(implicit p: Parameters) extends Dispatcher {
  // FIFOs
  val dnbParams = boomParams.dnbParams.get
  val dlq = Module(new SramDispatchQueueCompactingShifting( DispatchQueueParams(
    numEntries = dnbParams.numDlqEntries,
    qName="DLQ",
    deqWidth=dnbParams.dlqDispatches,
    enqWidth= coreWidth)))


  val crq = Module(new SramDispatchQueueCompactingShifting( DispatchQueueParams(
    numEntries = dnbParams.numCrqEntries,
    qName="CRQ",
    deqWidth=dnbParams.crqDispatches,
    enqWidth = coreWidth)))

  // DLQ is the only FIFO doing Busy lookup. Its deq width must match the width of the ports to Busy table
  require(dnbParams.dlqDispatches == boomParams.busyLookupParams.get.lookupAtDisWidth)

  // Route brinfo and flush into the fifos
  dlq.io.brinfo := io.brinfo.get
  dlq.io.flush := io.flush.get
  crq.io.brinfo := io.brinfo.get
  crq.io.flush  := io.flush.get

  // Route in tsc for pipeview
  dlq.io.tsc_reg := io.tsc_reg
  crq.io.tsc_reg := io.tsc_reg

  // Initialize the perf counters
  io.dnb_perf.get.dlq.map(_ := false.B)
  io.dnb_perf.get.crq.map(_ := false.B)
  io.dnb_perf.get.iq.map(_ := false.B)


  val dis_stall = WireInit(VecInit(Seq.fill(coreWidth)(false.B)))
  var previous_ready = true.B
  for (i <- 0 until coreWidth) {
    // Just get uop bits, valid and critical/busy info
    val uop = io.ren_uops(i).bits
    val uop_critical = uop.is_lsc_b
    val uop_iq = uop.uopc === uopLD || uop.uopc === uopSTA || uop.uopc === uopSTD //TODO: FP STW?
    val uop_busy = (uop.prs1_busy || uop.prs2_busy || uop.prs3_busy)

    // Check if this uop must be split into 2 which creates some extra corner cases
    val uop_split = uop.uopc === uopSTA

    // Initialize the ports to false and just add the uop
    dlq.io.enq_uops(i).bits := uop
    dlq.io.enq_uops(i).valid := false.B
    io.dis_uops(LSC_DIS_COMB_PORT_IDX)(i).bits := uop
    io.dis_uops(LSC_DIS_COMB_PORT_IDX)(i).valid := false.B
    crq.io.enq_uops(i).bits := uop
    crq.io.enq_uops(i).valid := false.B

    //ready logic - only ready if all lower rename ports and all possible target ports are ready
    io.ren_uops(i).ready := previous_ready &&
      dlq.io.enq_uops(i).ready &&
      io.dis_uops(LSC_DIS_COMB_PORT_IDX)(i).ready &&
      crq.io.enq_uops(i).ready
    previous_ready = io.ren_uops(i).ready

    when(io.ren_uops(i).fire()) {
      when(!uop_split) {
        // Normal non-splitting case
        // Based on critical/busy which FIFO/IQ do we wanna use?
        when(!uop_critical && !uop_iq) {
          //dlq
          dlq.io.enq_uops(i).valid := true.B
          io.dnb_perf.get.dlq(i) := true.B
        }.otherwise {
          when(uop_busy || uop_iq) {
            //iq
            io.dis_uops(LSC_DIS_COMB_PORT_IDX)(i).valid := true.B
            io.dnb_perf.get.iq(i) := true.B

          }.otherwise {
            //crq
            crq.io.enq_uops(i).valid := true.B
            io.dnb_perf.get.crq(i) := true.B
          }
        }
      }.otherwise { // Uop splitting case
        // Currently 2 cases. STORE and FP STORE. We want the uopSTD to go in the DLQ and the uopSTA on the IQ
        //  If we dont have place for both, i.e. in DLQ and IQ we will stall
        val uop_sta = WireInit(uop)
        val uop_std = WireInit(uop)

        // address
        uop_sta.lrs2_rtype := RT_X
        uop_sta.prs2_busy := false.B
        // data
        uop_std.lrs1_rtype := RT_X
        uop_std.prs1_busy := false.B

        when(uop.iq_type === IQT_MEM) {
          // INT stores
          uop_sta.uopc := uopSTA
          uop_std.uopc := uopSTD
        }.otherwise {
          // FP stores
          uop_sta.uopc := uopSTA
          uop_sta.iq_type := IQT_MEM
          uop_std.iq_type := IQT_FP
        }
        io.dis_uops(LSC_DIS_COMB_PORT_IDX)(i).valid := true.B
        io.dis_uops(LSC_DIS_COMB_PORT_IDX)(i).bits := uop_sta

        dlq.io.enq_uops(i).valid := true.B
        dlq.io.enq_uops(i).bits := uop_std

        io.dnb_perf.get.dlq(i) := true.B
        io.dnb_perf.get.iq(i) := true.B
      }
    }
  }

  if(O3PIPEVIEW_PRINTF){ // dispatch is here because it only happens for IQ and not dlq/crq
    io.dis_uops(LSC_DIS_COMB_PORT_IDX).foreach( port =>{
      when (port.fire()) {
        printf("%d; O3PipeView:dispatch: %d\n", port.bits.debug_events.fetch_seq, io.tsc_reg)
      }
    })
  }

  // Handle CRQ dequeue
  io.crq_head.get <> crq.io.heads

  // Handle DLQ dequeues
  //  A little more complicated as we need to pass along the updated ready info
  //  Connect uop to both FP and INT busy table. Pick the resp based on the lrs-types

  for (i <- 0 until dnbParams.dlqDispatches) {
    io.busy_req_uops.get(i) := dlq.io.heads(i).bits
    io.fp_busy_req_uops.get(i) := dlq.io.heads(i).bits

    io.dlq_head.get(i) <> dlq.io.heads(i)
    // Now, update busy info
    when(io.dlq_head.get(i).bits.lrs1_rtype === RT_FLT) {
      io.dlq_head.get(i).bits.prs1_busy := io.fp_busy_resps.get(i).prs1_busy
    }.elsewhen(io.dlq_head.get(i).bits.lrs1_rtype === RT_FIX) {
      io.dlq_head.get(i).bits.prs1_busy := io.busy_resps.get(i).prs1_busy
    }.otherwise{
      io.dlq_head.get(i).bits.prs1_busy := false.B
    }

    when(io.dlq_head.get(i).bits.lrs2_rtype === RT_FLT) {
      io.dlq_head.get(i).bits.prs2_busy := io.fp_busy_resps.get(i).prs2_busy
    }.elsewhen(io.dlq_head.get(i).bits.lrs2_rtype === RT_FIX) {
      io.dlq_head.get(i).bits.prs2_busy := io.busy_resps.get(i).prs2_busy
    }.otherwise{
      io.dlq_head.get(i).bits.prs2_busy := false.B
    }

    io.dlq_head.get(i).bits.prs3_busy := io.dlq_head.get(i).bits.frs3_en && io.fp_busy_resps.get(i).prs3_busy
  }

}