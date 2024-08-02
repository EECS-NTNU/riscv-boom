package boom.exu

import java.nio.file.Paths
import chisel3._
import chisel3.util._
import freechips.rocketchip.config.Parameters
import freechips.rocketchip.rocket.Instructions._
import freechips.rocketchip.rocket.{Causes, PRV, TraceDoctor}
import freechips.rocketchip.util.{CoreMonitorBundle, SeqToAugmentedSeq, Str, UIntIsOneOf}
import freechips.rocketchip.devices.tilelink.{CLINTConsts, PLICConsts}
import testchipip.ExtendedTracedInstruction
import boom.common._
import boom.ifu.{GlobalHistory}
import boom.exu.FUConstants._
import boom.util._


class TaintEntry()(implicit p: Parameters) extends BoomBundle
    with HasBoomCoreParameters
{
    val valid           = Bool()
    val ldq_idx         = UInt(ldqAddrSz.W)
    val flipped_age     = Bool()
}

class RenameTaintTracker(
  val plWidth: Int,
  val numLregs: Int)(implicit p: Parameters) extends BoomModule
    with HasBoomCoreParameters
{

    //The io bundle inputs are now identical to that of the rename stage
    val io = IO(new Bundle {
        val stt_stalls = Output(Vec(plWidth, Bool()))

        val kill = Input(Bool())

        val dec_fire        = Input(Vec(plWidth, Bool()))
        val dec_uops        = Input(Vec(plWidth, new MicroOp()))

        val ldq_tail        = Input(UInt(ldqAddrSz.W))
        val ldq_head        = Input(UInt(ldqAddrSz.W))
        val ldq_btc_head    = Input(UInt(ldqAddrSz.W))

        val brupdate        = Input(new BrUpdateInfo())

        val ren2_yrot       = Output(Vec(plWidth, (UInt(ldqAddrSz.W))))
        val ren2_yrot_r     = Output(Vec(plWidth, Bool()))
        val ren2_valid      = Output(Vec(plWidth, Bool()))

        val taint_wakeup_port = Flipped(Vec(numTaintWakeupPorts, Valid(UInt(ldqAddrSz.W))))

        val dis_fire        = Input(Vec(coreWidth, Bool()))
        val dis_ready       = Input(Bool())

        val com_valids      = Input(Vec(plWidth, Bool()))
        val com_uops        = Input(Vec(plWidth, new MicroOp()))
        val rbk_valids      = Input(Vec(plWidth, Bool()))
        val rollback        = Input(Bool())
        val exception       = Input(Bool())

        val ldq_flipped     = Input(Bool())

        val taints_calc     = Output(UInt(4.W))
        val yrot_r_on_dis   = Output(UInt(4.W))
        val tainted_loads   = Output(UInt(4.W))

        // Debug
        val int_taint_valids = Output(UInt(32.W))
        val ren1_yrot = Output(Vec(plWidth, (UInt(ldqAddrSz.W))))
        val ren1_yrot_r = Output(Vec(plWidth, Bool()))

        val loads_last_cycle = Output(UInt(2.W))
        val load_ops = Output(Vec(plWidth + 1, UInt(2.W)))
        val ldq_will_flip = Output(Vec(plWidth + 2, Bool()))
        val ren1_tent_ldq_idx = Output(Vec(plWidth, UInt(ldqAddrSz.W)))

        // Assert debug
        val ren2_ldq_idx = Output(Vec(plWidth, UInt(ldqAddrSz.W)))
    })

    val int_type = RT_FIX
    val fp_type = RT_FLT
    val dud_entry = Wire(new TaintEntry())
    dud_entry.valid := false.B
    dud_entry.ldq_idx := 0.U
    dud_entry.flipped_age := false.B

    def idxBetween(idx: UInt) : Bool = {
        val isBetween = Mux(io.ldq_btc_head <= io.ldq_tail,
                           (io.ldq_btc_head <= idx) && (idx < io.ldq_tail),
                           (io.ldq_btc_head <= idx) || (idx < io.ldq_tail))

        isBetween
    }

    def mispredictIdxBetween(idx: UInt) : Bool = {
        val isBetween = Mux(io.ldq_btc_head <= io.brupdate.b2.uop.ldq_idx,
                           (io.ldq_btc_head <= idx) && (idx < io.brupdate.b2.uop.ldq_idx),
                           (io.ldq_btc_head <= idx) || (idx < io.brupdate.b2.uop.ldq_idx))
            isBetween
    }

    // Helper function for finding the correct dependencies intra-cycle and then
    // invoking GetTaintEntry() to find the youngest root
    def FindAndCompareTaints(
            uop: MicroOp, 
            older_uops: Seq[MicroOp], 
            taint_entries: Seq[TaintEntry],
            idx: UInt) 
            : TaintEntry = {
        val matching_uop = Wire(new MicroOp)
        matching_uop := uop

        val bypass_hits_rs1 = older_uops map {case r => r.ldst_val && r.dst_rtype === uop.lrs1_rtype && r.ldst === uop.lrs1}
        val bypass_hits_rs2 = older_uops map {case r => r.ldst_val && r.dst_rtype === uop.lrs2_rtype && r.ldst === uop.lrs2}
        val bypass_hits_rs3 = older_uops map {case r => r.ldst_val && r.dst_rtype === fp_type && uop.frs3_en && r.ldst === uop.lrs3}

        val bypass_sel_rs1 = PriorityEncoderOH(bypass_hits_rs1.reverse).reverse
        val bypass_sel_rs2 = PriorityEncoderOH(bypass_hits_rs2.reverse).reverse
        val bypass_sel_rs3 = PriorityEncoderOH(bypass_hits_rs3.reverse).reverse

        val do_bypass_rs1 = bypass_hits_rs1.reduce(_||_)
        val do_bypass_rs2 = bypass_hits_rs2.reduce(_||_)
        val do_bypass_rs3 = bypass_hits_rs3.reduce(_||_)

        val t1 = Wire(new TaintEntry)
        val t2 = Wire(new TaintEntry)
        val t3 = Wire(new TaintEntry)

        val (d_t1, d_t2, d_t3) = GetRegTaints(uop)

        t1 := Mux(do_bypass_rs1, Mux1H(bypass_sel_rs1, taint_entries), d_t1)
        t2 := Mux(do_bypass_rs2, Mux1H(bypass_sel_rs2, taint_entries), d_t2)
        t3 := Mux(do_bypass_rs3, Mux1H(bypass_sel_rs3, taint_entries), d_t3)

        GetTaintEntry(matching_uop, t1, t2, t3, idx)

    }

    // Helper function for finding youngest root of taint amongst several TaintEntry options
    def GetTaintEntry(
        uop: MicroOp,
        t1: TaintEntry,
        t2: TaintEntry,
        t3: TaintEntry,
        idx: UInt)
        : TaintEntry = {

        val rs3_en = uop.frs3_en

        val t1_valid = t1.valid
        val t2_valid = t2.valid
        val t3_valid = t3.valid && rs3_en

        val t1_age = t1.ldq_idx 
        val t1_flipped = t1.flipped_age
        val t2_age = t2.ldq_idx 
        val t2_flipped = t2.flipped_age
        val t3_age = t3.ldq_idx 
        val t3_flipped = t3.flipped_age

        val any_valid = t1_valid || t2_valid || t3_valid

        val t1_youngness = Mux(Mux(ldq_will_flip(idx), io.ldq_flipped =/= t1_flipped, io.ldq_flipped === t1_flipped), 
                                                    numLdqEntries.U - t1_age, (numLdqEntries*2).U - t1_age)
        val t2_youngness = Mux(Mux(ldq_will_flip(idx), io.ldq_flipped =/= t2_flipped, io.ldq_flipped === t2_flipped),
                                                    numLdqEntries.U - t2_age, (numLdqEntries*2).U - t2_age)
        val t3_youngness = Mux(Mux(ldq_will_flip(idx), io.ldq_flipped =/= t3_flipped, io.ldq_flipped === t3_flipped),
                                                    numLdqEntries.U - t3_age, (numLdqEntries*2).U - t3_age)
        
        val t1_youngest = (t1_valid 
                        && ((!t2_valid) || t1_youngness <= t2_youngness)
                        && ((!t3_valid) || t1_youngness <= t3_youngness))
        val t2_youngest = ((!t1_youngest)
                        && t2_valid
                        && ((!t3_valid) || t2_youngness <= t3_youngness))
        val t3_youngest = ((!t1_youngest)
                        && (!t2_youngest)
                        && t3_valid) 
        
        assert(!(t1_youngest && t2_youngest))
        assert(!(t1_youngest && t3_youngest))
        assert(!(t2_youngest && t3_youngest)) 

        val chosen_t = Wire(new TaintEntry())

        chosen_t.valid := false.B
        chosen_t.ldq_idx := 0.U
        chosen_t.flipped_age := false.B
        
        when(t1_youngest) {
            chosen_t := t1
        } .elsewhen(t2_youngest) {
            chosen_t := t2
        } .elsewhen(t3_youngest) {
            chosen_t := t3
        }
        
        chosen_t
    }

    // Get the matching TaintEntries from TaintFile for a given UOP
    def GetRegTaints(uop: MicroOp) : (TaintEntry, TaintEntry, TaintEntry) = {

        val t1 = MuxLookup(uop.lrs1_rtype, dud_entry,
                    Array(int_type -> int_taint_file_freed_taints(uop.lrs1),
                          fp_type -> fp_taint_file_freed_taints(uop.lrs1)))

        val t2 = MuxLookup(uop.lrs2_rtype, dud_entry,
                    Array(int_type -> int_taint_file_freed_taints(uop.lrs2),
                          fp_type -> fp_taint_file_freed_taints(uop.lrs2)))

        val t3 = Mux(uop.frs3_en, fp_taint_file_freed_taints(uop.lrs3), dud_entry)
        
        (t1, t2, t3)
    }

    // Taint files for int and fp registers
    val int_taint_file              = Reg(Vec(numLregs, new TaintEntry()))
    val fp_taint_file               = Reg(Vec(numLregs, new TaintEntry()))

    val int_br_snapshots            = Reg(Vec(maxBrCount, Vec(numLregs, new TaintEntry())))
    val fp_br_snapshots             = Reg(Vec(maxBrCount, Vec(numLregs, new TaintEntry())))

    val int_br_remap_table          = Wire(Vec(plWidth+1, Vec(numLregs, new TaintEntry())))
    val fp_br_remap_table           = Wire(Vec(plWidth+1, Vec(numLregs, new TaintEntry())))

    val ren1_uops                   = Wire(Vec(plWidth, new MicroOp()))
    val ren1_fire                   = Wire(Vec(plWidth, Bool()))

    val ren1_br_tags                = Wire(Vec(plWidth, Valid(UInt(brTagSz.W))))

    val int_taint_file_freed_taints = Wire(Vec(numLregs, new TaintEntry()))
    val fp_taint_file_freed_taints  = Wire(Vec(numLregs, new TaintEntry()))

    val ren2_fire       = io.dis_fire
    val ren2_ready      = io.dis_ready
    val ren2_valids     = Wire(Vec(plWidth, Bool()))
    val ren2_uops       = Wire(Vec(plWidth, new MicroOp))

    val load_ops = ((io.dec_fire zip io.dec_uops) map { case (f, u) => (f && u.uses_ldq)})
                    .scanLeft(0.U(ldqAddrSz.W))((total, load) => total + load.asUInt())

    val loads_last_cycle = ((ren2_valids zip ren2_uops) map { case (v, u) => (v && u.uses_ldq)})
                        .foldLeft(0.U(ldqAddrSz.W))((total, load) => total + load.asUInt())

    val ldq_will_flip = load_ops.scanLeft(io.ldq_tail + loads_last_cycle)
                            { case (sum, add) => sum + add}
                            .map( i => i >= numLdqEntries.U)

    val last_cycle_int_snapshot = Reg(Vec(numLregs, new TaintEntry()))
    val last_cycle_fp_snapshot = Reg(Vec(numLregs, new TaintEntry()))

    // Handle same-cycle wakeups
    for (i <- 0 until numLregs) {
        val i_ent = int_taint_file(i)
        val f_ent = fp_taint_file(i)
        
        int_taint_file_freed_taints(i) := i_ent
        int_taint_file_freed_taints(i).valid := io.taint_wakeup_port.foldLeft(i_ent.valid)
            {case (valid, twake) => valid && !(twake.valid && (twake.bits === i_ent.ldq_idx))}

        fp_taint_file_freed_taints(i) := f_ent
        fp_taint_file_freed_taints(i).valid := io.taint_wakeup_port.foldLeft(f_ent.valid)
            {case (valid, twake) => valid && !(twake.valid && (twake.bits === f_ent.ldq_idx))}
    }


    last_cycle_int_snapshot := int_taint_file_freed_taints
    last_cycle_fp_snapshot := fp_taint_file_freed_taints

    dontTouch(int_taint_file_freed_taints)
    dontTouch(fp_taint_file_freed_taints)
    dontTouch(ren1_uops)
    dontTouch(ren1_fire)

    for (w <- 0 until plWidth) {
        ren1_fire(w) := io.dec_fire(w)
        ren1_uops(w) := io.dec_uops(w)
    }

    for (w <- 0 until plWidth) {
        ren1_br_tags(w).valid := ren1_fire(w) && ren1_uops(w).allocate_brtag
        ren1_br_tags(w).bits := ren1_uops(w).br_tag
    }

    val new_taint_entries = Wire(Vec(plWidth, new TaintEntry()))

    // Handle new taint allocations
    for (i <- 0 until plWidth) {
        val t_ent = Wire(new TaintEntry())
        val (t1, t2, t3) = GetRegTaints(ren1_uops(i))

        if (i > 0) {
            t_ent := FindAndCompareTaints(ren1_uops(i), 
                                          ren1_uops.slice(0, i),
                                          new_taint_entries.slice(0, i),
                                          i.U)
        } else {
            t_ent := GetTaintEntry(ren1_uops(i), t1, t2, t3, i.U)
        }
        
        val new_tent = WireInit(t_ent)

        when(ren1_fire(i) && ren1_uops(i).uses_ldq && (!ren1_uops(i).is_problematic)) {
            new_tent.ldq_idx := WrapAdd(io.ldq_tail, loads_last_cycle + load_ops(i), numLdqEntries) //ren1_uops(i).ldq_idx
            new_tent.flipped_age := Mux(ldq_will_flip(i), !io.ldq_flipped, io.ldq_flipped)
            new_tent.valid := true.B
        }. elsewhen(ren1_fire(i) && !ren1_uops(i).is_problematic) {
            new_taint_entries(i) := t_ent
        }. otherwise {
            new_tent.valid := false.B
        }

        
        new_taint_entries(i) := new_tent

        ren1_uops(i).yrot := t_ent.ldq_idx
        ren1_uops(i).yrot_r := !(t_ent.valid)

        // Assert Debug
        ren1_uops(i).ldq_idx := WrapAdd(io.ldq_tail, loads_last_cycle + load_ops(i), numLdqEntries)
        io.ren1_tent_ldq_idx(i) := WrapAdd(io.ldq_tail, loads_last_cycle + load_ops(i), numLdqEntries)
    }

    // Find remapped int entries, by checking reallocations for each of the width micro-ops
    for (i <- 0 until numLregs) {
        val remapped_int_entry = (ren1_uops.map(uop => (uop.ldst_val, uop.ldst, uop.dst_rtype)) zip ren1_fire zip new_taint_entries)
            .scanLeft(int_taint_file_freed_taints(i)) {case (t_ent, (((ldst_val, ldst, rtype), fire), new_t_ent)) =>
                Mux(fire && ldst_val && ldst === i.U && rtype === int_type, new_t_ent, t_ent)}
        
        for (j <- 0 until plWidth+1) {
            int_br_remap_table(j)(i) := remapped_int_entry(j)
        }
    }

    // Find remapped float entries, by checking reallocations for each of the width micro-ops
    for (i <- 0 until numLregs) {
        val remapped_float_entry = (ren1_uops.map(uop => (uop.ldst_val, uop.ldst, uop.dst_rtype)) zip ren1_fire zip new_taint_entries)
            .scanLeft(fp_taint_file_freed_taints(i)) {case (t_ent, (((ldst_val, ldst, rtype), fire), new_t_ent)) =>
                Mux(fire && ldst_val && ldst === i.U && rtype === fp_type, new_t_ent, t_ent)}

        for (j <- 0 until plWidth+1) {
            fp_br_remap_table(j)(i) := remapped_float_entry(j)
        }
    }


    if (enableCheckpointTaints) {
        for (i <- 0 until plWidth) {
            when(ren1_br_tags(i).valid) {
                int_br_snapshots(ren1_br_tags(i).bits) := int_br_remap_table(i+1)
                fp_br_snapshots(ren1_br_tags(i).bits) := fp_br_remap_table(i+1)
            }
        }
    }

    
    val temp_int_file = Wire(Vec(numLregs, new TaintEntry()))
    val temp_fp_file = Wire(Vec(numLregs, new TaintEntry()))
    temp_int_file := int_taint_file
    temp_fp_file := fp_taint_file
    dontTouch(temp_int_file)
    
    // Reset to a known taint area, but check all tainted entries to see if they have been cleared. 
    when (io.brupdate.b2.mispredict) {
        if (enableCheckpointTaints) {
            temp_int_file := int_br_snapshots(io.brupdate.b2.uop.br_tag)
            temp_fp_file := fp_br_snapshots(io.brupdate.b2.uop.br_tag)

            for (i <- 0 until numLregs) {
                val temp_i_reg = int_br_snapshots(io.brupdate.b2.uop.br_tag)(i)
                temp_int_file(i) := temp_i_reg
                temp_int_file(i).valid := io.taint_wakeup_port.foldLeft(temp_i_reg.valid && mispredictIdxBetween(temp_i_reg.ldq_idx))
                                            {case (valid, wakeup) => valid && !(wakeup.valid && wakeup.bits === temp_i_reg.ldq_idx)}


                val temp_f_reg = fp_br_snapshots(io.brupdate.b2.uop.br_tag)(i)
                temp_fp_file(i) := temp_f_reg
                temp_fp_file(i).valid := io.taint_wakeup_port.foldLeft(temp_f_reg.valid && mispredictIdxBetween(temp_f_reg.ldq_idx))
                                            {case (valid, wakeup) => valid && !(wakeup.valid && wakeup.bits === temp_f_reg.ldq_idx)}
            }

            int_taint_file := temp_int_file
            fp_taint_file := temp_fp_file
        } else {
            int_taint_file := VecInit.fill(numLregs)(dud_entry)
            fp_taint_file := VecInit.fill(numLregs)(dud_entry)
        }
    // When frontend is stalled, only receive taint wakeup requests
    }.elsewhen(!io.dis_ready) {
        int_taint_file := int_taint_file_freed_taints
        fp_taint_file := fp_taint_file_freed_taints
    // Update the taint_file with the most updated mappings
    } .otherwise {
        int_taint_file := int_br_remap_table(plWidth)
        fp_taint_file := fp_br_remap_table(plWidth)
    }

    dontTouch(ren2_uops)
    dontTouch(ren2_valids)

    // Buffer stop between rename 1 and rename 2 (dispatch)
    for (w <- 0 until plWidth) {
        val r_valid = RegInit(false.B)
        val r_uop = Reg(new MicroOp)
        val next_uop = Wire(new MicroOp)

        next_uop := r_uop

        when (io.kill) {
            r_valid := false.B
        }.elsewhen (ren2_ready) {
            r_valid := ren1_fire(w)
            next_uop := ren1_uops(w)
        }.otherwise {
            r_valid := r_valid && !ren2_fire(w)
            next_uop := r_uop

            for (i <- 0 until numTaintWakeupPorts) {
                 when(io.taint_wakeup_port(i).valid && (io.taint_wakeup_port(i).bits === r_uop.yrot)) {
                    next_uop.yrot_r := true.B
                }
            }
        }

        val temp = WireInit(next_uop)
        r_uop := temp

        ren2_valids(w) := r_valid
        ren2_uops(w) := r_uop

        dontTouch(next_uop)
        dontTouch(r_uop)

        //Debug 
        io.ren1_yrot(w) := temp.yrot
        io.ren1_yrot_r(w) := temp.yrot_r
    }


    // Outputs
    for (w <- 0 until plWidth) {
        io.ren2_yrot(w)     := ren2_uops(w).yrot
        io.ren2_valid(w)    := ren2_valids(w)
        io.ren2_yrot_r(w)   := io.taint_wakeup_port.foldLeft(ren2_uops(w).yrot_r)
                                {case (yrot_r, wakeup) => yrot_r || (wakeup.valid && wakeup.bits === ren2_uops(w).yrot)}
    }
    // For debug purposes
    io.int_taint_valids := temp_int_file.foldLeft(0.U(32.W))
                            {(uint, entry) => (uint << 1) | (entry.valid.asUInt(0))}
    io.loads_last_cycle := loads_last_cycle
    io.load_ops := load_ops
    io.ldq_will_flip := ldq_will_flip

    // Assert Debug
    io.ren2_ldq_idx := ren2_uops map {u => u.ldq_idx}

    when(io.rollback || io.exception) {
        for (i <- 0 until numLregs) {
            int_taint_file(i)   := dud_entry
            fp_taint_file(i)    := dud_entry

            for (j <- 0 until maxBrCount)  {
                int_br_snapshots(j)(i)  := dud_entry
                fp_br_snapshots(j)(i)   := dud_entry
            }
        }
    }.elsewhen(io.kill && !io.brupdate.b2.mispredict) {
        for (i <- 0 until numLregs) {
            int_taint_file(i) := last_cycle_int_snapshot(i)
            int_taint_file(i).valid := io.taint_wakeup_port.foldLeft(last_cycle_int_snapshot(i).valid)
            {case (valid, twake) => valid && !(twake.valid && (twake.bits === last_cycle_int_snapshot(i).ldq_idx))}

            fp_taint_file(i) := last_cycle_fp_snapshot(i)
            fp_taint_file(i).valid := io.taint_wakeup_port.foldLeft(last_cycle_fp_snapshot(i).valid)
            {case (valid, twake) => valid && !(twake.valid && (twake.bits === last_cycle_fp_snapshot(i).ldq_idx))}
        }
    }


    //Stat information
    //val taints_calc_total = RegInit(0.U(40.W))
    //val yrot_r_on_dis = RegInit(0.U(40.W))


    //taints_calc_total := taints_calc_total + PopCount(io.dis_fire)
    //yrot_r_on_dis := yrot_r_on_dis + PopCount((io.dis_fire zip io.ren2_yrot_r) map { case (d, r) => d && r })
    io.taints_calc := PopCount(io.dis_fire)
    io.yrot_r_on_dis := PopCount((io.dis_fire zip io.ren2_yrot_r) map { case (d, r) => d && r })
    io.tainted_loads := PopCount((io.dis_fire zip io.ren2_yrot_r) map { case (r, y) => r && !y} zip (ren2_uops map (u => u.uses_ldq)) map { case (t, l) => t && l})


    dontTouch(int_taint_file)
    dontTouch(fp_taint_file)
    if (enableCheckpointTaints) {
        dontTouch(int_br_snapshots)
        dontTouch(fp_br_snapshots)
    }
    dontTouch(int_br_remap_table)
    dontTouch(fp_br_remap_table)
    dontTouch(io)
    dontTouch(new_taint_entries)

}