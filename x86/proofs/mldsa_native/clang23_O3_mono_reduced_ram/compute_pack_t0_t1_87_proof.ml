(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The vector t of key generation, split and packed: the proof (see          *)
(* compute_pack_t0_t1_87_spec.ml).                                           *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/compute_pack_t0_t1_87_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/lazy_eq_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/compute_pack_t0_t1_87_inline.ml";;
needs "x86/proofs/utils/mldsa_native_polyvec.ml";;
needs "x86/proofs/utils/mldsa_native_top.ml";;
needs "x86/proofs/utils/mldsa_native_lazy_matrix.ml";;
needs "x86/proofs/utils/mldsa_native_matrix.ml";;
needs "x86/proofs/utils/mldsa_native_sampling.ml";;
needs "x86/proofs/utils/mldsa_native_realign.ml";;

let CPT87_EXEC = MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The frame of 4901 bytes below the return address: the six registers that  *)
(* the function saves (k = 4853 bytes below the return address, so that the  *)
(* AND of the stack pointer is of word_add stackpointer (word 4853) after    *)
(* REPEAT_GEN_AND_OFFSET_STACKPTR_TAC), and the aligned part (bot,4822) of   *)
(* utils/mldsa_native_realign.ml, with RSP at bot + 1654 after the SUB, the  *)
(* spill of s2 at bot + 1678, the polynomial of t and t0 at bot + 1686, the  *)
(* unpacked s2 and the t1 at bot + 2710, the structure mld_polymat_lazy at   *)
(* bot + 3734 (its polynomial, and rho at bot + 4758) up to the AND, and the *)
(* stacks of the callees below RSP. Polynomial k of t, as the code computes  *)
(* it.                                                                       *)
(* ------------------------------------------------------------------------- *)

let CPT87_PACK_T1 =
  CONV_RULE NUM_REDUCE_CONV
   (SPECL [`7`; `mld_polyeta_unpack_2`; `96`] MLD_COMPUTE_T_LAZY_PACK_T1);;

let CPT87_PACK_T0 =
  CONV_RULE NUM_REDUCE_CONV
   (SPECL [`7`; `mld_polyeta_unpack_2`; `96`] MLD_COMPUTE_T_LAZY_PACK_T0);;

let CPT87_ALLOWED =
  [`pc:num`; `pkt1:int64`; `t0:int64`; `s1hat:int64`; `s2:int64`;
   `rho:int64`; `r:num`; `mf:int64`; `mc:int64`; `stackpointer:int64`;
   `returnaddress:int64`; `bot:int64`];;

let CPT87_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc CPT87_EXEC name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   CPT87_ALLOWED n;;

let CPT87_LOOP_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc CPT87_EXEC name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   (`i:num`::CPT87_ALLOWED) n;;

(* the inlined loops: the lemmas are about the value of RSP *)
let CPT87_INLINE_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc CPT87_EXEC name
   (`read RSP s`::`pc:num`::ilist)
   (`i:num`::CPT87_ALLOWED) n;;

(* ------------------------------------------------------------------------- *)
(* The invariant of the loop over the 8 rows, for i rows done: the frame,    *)
(* the counter in R13, the pointers, the spill of s2, rho in the structure,  *)
(* the inputs, and the packed polynomials of t1 and t0 so far. The direction *)
(* flag is kept for the zeroing at the end.                                  *)
(* ------------------------------------------------------------------------- *)

let CPT87_INVARIANT =
 `\i s. read RSP s = word_add bot (word 1654) /\
        read RBP s = word_add stackpointer (word 4893) /\
        read (memory :> bytes64 (word_add stackpointer (word 4893))) s =
        rbp_init /\
        read (memory :> bytes64 (word_add stackpointer (word 4885))) s =
        r15_init /\
        read (memory :> bytes64 (word_add stackpointer (word 4877))) s =
        r14_init /\
        read (memory :> bytes64 (word_add stackpointer (word 4869))) s =
        r13_init /\
        read (memory :> bytes64 (word_add stackpointer (word 4861))) s =
        r12_init /\
        read (memory :> bytes64 (word_add stackpointer (word 4853))) s =
        rbx_init /\
        read (memory :> bytes64 (word_add stackpointer (word 4901))) s =
        returnaddress /\
        read RBX s = word_add bot (word 1686) /\
        read R12 s = word_add pkt1 (word(320 * i + 4)) /\
        read R13 s = word i /\
        read R14 s = s1hat /\
        read R15 s = t0 /\
        read (memory :> bytes64 (word_add bot (word 1678))) s = s2 /\
        ~read DF s /\
        read (memory :> bytes(word_add bot (word 4758),32)) s = r /\
        read (memory :> bytes64(word(pc + got_memset))) s = mf /\
        read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
        read (memory :> bytes(ea,el)) s = ev /\
        (!j. j < 1792
             ==> read(memory :> bytes32(word_add s1hat (word(4 * j)))) s =
                 sh j) /\
        (!j. j < 768
             ==> read(memory :> bytes8(word_add s2 (word j))) s =
                 s2b j) /\
        (!j. j < 320 * i
             ==> read(memory :> bytes8(word_add pkt1 (word j))) s =
                 mld_polyvec_pack 320 mld_polyt1_pack
                  (mld_polyvec_map mld_poly_power2round_hi
                    (mld_compute_t_lazy 7 mld_polyeta_unpack_2 96 r sh s2b))
                  j) /\
        (!j. j < 416 * i
             ==> read(memory :> bytes8(word_add t0 (word j))) s =
                 mld_polyvec_pack 416 mld_polyt0_pack
                  (mld_polyvec_map mld_poly_power2round_lo
                    (mld_compute_t_lazy 7 mld_polyeta_unpack_2 96 r sh s2b))
                  j)`;;

(* ------------------------------------------------------------------------- *)
(* The prologue, with the copy of rho into the structure; RSP gets the value *)
(* of the AND after step 8.                                                  *)
(* ------------------------------------------------------------------------- *)

let CPT87_PROLOGUE_TAC =
  FULL_INIT_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MLD_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(rho,32)) s = n`) o concl)) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `r < 2 EXP 256` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check
     (can (term_match [] `read (memory :> bytes(rho,32)) s = n`) o concl)) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
    MP_TAC(ISPECL [`rho:int64`; `32`; `read memory (s0:x86state)`]
                  READ_BYTES_BOUND) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SAMPLING_GHOST_REGS_TAC [`YMM0`; `YMM1`] "s0" THEN
  X86_STEPS_TAC CPT87_EXEC (1--8) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC CPT87_EXEC (9--21) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SAMPLING_SUBWORD_JOIN_128]) THEN
  MP_TAC(SPECL [`word_add bot (word 4758):int64`; `r:num`; `s21:x86state`]
               LAZY_RHO_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[] THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let CPT87_ACC = `mld_polyvec_matrix_row_lazy 7 r (sh:num->int32) i`;;

let CPT87_UNPACK = `mld_polyeta_unpack_2 (\j. (s2b:num->byte)(96 * i + j))`;;

let CPT87_ADD =
  mk_comb(mk_comb(`mld_poly_add`,mk_comb(`mld_poly_invntt_tomont`,CPT87_ACC)),
          CPT87_UNPACK);;

let CPT87_RED = mk_comb(`mld_poly_reduce`,CPT87_ADD);;

let CPT87_CADDQ = mk_comb(`mld_poly_caddq`,CPT87_RED);;

let CPT87_JOIN_TAC pth =
  MATCH_MP_TAC VEC_JOIN_POLY THEN CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[pth]];;

(* ------------------------------------------------------------------------- *)
(* The constants that the code loads into XMM5, XMM6 and XMM7 for the loops  *)
(* inlined from mld_poly_reduce, mld_poly_power2round: the 128-bit values in *)
(* the image at pc + 0x25000 + 16 k, and the form of the registers that the  *)
(* lemmas for the loops use.                                                 *)
(* ------------------------------------------------------------------------- *)

let CPT87_CONST_RULE = IMAGE_CONST_RULE_FOR mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc;;

let CPT87_LOAD_CONST_TAC k r =
  IMAGE_RIPREL_TAC (CPT87_CONST_RULE (0x25000 + 16 * k) 128) (0x180e0 + r);;

(* the low 128 bits of YMMk as XMMk, with the value of the constant *)
let CPT87_XMM_TAC k xmm s v =
  SUBGOAL_THEN (parse_term(Printf.sprintf "read XMM%d (%s:x86state) = word %s" k s v))
   ASSUME_TAC THENL
   [REWRITE_TAC[xmm; READ_ZEROTOP_128] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST;
    ALL_TAC];;

(* the source pointer s2 + 96 i of the unpacking, as the code computes it *)

let CPT_SHL5 = prove
 (`!x:int64. word_shl x 5 = word_mul x (word 32)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let CPT87_T0PTR = prove
 (`!i t0. word_add (word_mul (word i:int64) (word 416)) t0 =
          word_add t0 (word (416 * i))`,
  REPEAT GEN_TAC THEN CONV_TAC WORD_RULE);;

let CPT87_S2PTR = prove
 (`!i s2:int64.
        i < 8
        ==> word_add (word_shl (word_add (word (0 + 2 * val (word i:int64)))
                                          (word i)) 5) s2 =
            word_add s2 (word (96 * i))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word i:int64) = i` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `i < 8` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[CPT_SHL5] THEN CONV_TAC WORD_RULE);;

(* The inlined loops address the polynomials relative to RSP, as            *)
(* word_add bot (word (1654 + (32 + 4 * i))), the callees relative to the    *)
(* pointers, as word_add bot (word (1686 + 4 * i)): CPT87_REBASE_TAC adds    *)
(* the facts about the polynomials of the frame in the other form.           *)

let CPT87_REBASE_TAC lths =
  W(fun (asl,w) ->
    MAP_EVERY (fun (_,th) ->
      let c = concl th in
      if is_forall c && free_in `bot:int64` c
      then (try let th' = REWRITE_RULE lths th in
                if concl th' = c then ALL_TAC else ASSUME_TAC th'
            with Failure _ -> ALL_TAC)
      else ALL_TAC) asl);;

let CPT87_TO_RSP =
  CPT87_REBASE_TAC [ARITH_RULE `!n. 1686 + n = 1654 + (32 + n)`;
                    ARITH_RULE `!n. 2710 + n = 1654 + (1056 + n)`];;

let CPT87_FROM_RSP =
  CPT87_REBASE_TAC [ARITH_RULE `!n. 1654 + (32 + n) = 1686 + n`;
                    ARITH_RULE `!n. 1654 + (1056 + n) = 2710 + n`];;

(* ------------------------------------------------------------------------- *)
(* The body of the loop for row i, with the loop test. The counter is in     *)
(* R13 (as 64 bits) and is passed to the callee as 32 bits, in ECX.          *)
(* ------------------------------------------------------------------------- *)

let CPT87_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN X86_STEPS_TAC CPT87_EXEC (1--4) THEN
  SUBGOAL_THEN `word_zx(word_zx(word i:int64):int32):int64 = word i`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC WORD_ZX_ZX_SMALL THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  X86_STEPS_TAC CPT87_EXEC (5--5) THEN
  CPT87_LOOP_CALL_TAC "H_ROW"
   [`read RDI s`; `read RSI s`; `read RDX s`; `r:num`; `sh:num->int32`;
    `i:num`] 6 THEN
  X86_STEPS_TAC CPT87_EXEC (7--8) THEN
  CPT87_LOOP_CALL_TAC "H_INV" [`read RDI s`; CPT87_ACC] 9 THEN
  X86_STEPS_TAC CPT87_EXEC (10--15) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPEC_ALL(MATCH_MP CPT87_S2PTR (ASSUME `i < 8`))]) THEN
  VEC_SLICE_TAC
   `!j. j < 96
        ==> read(memory :> bytes8(word_add s2 (word(96 * i + j)))) s15 =
            (s2b:num->byte)(96 * i + j)` THEN
  CPT87_LOOP_CALL_TAC "H_UNPACK"
   [`read RDI s`; `read RSI s`; `\j. (s2b:num->byte)(96 * i + j)`] 16 THEN
  X86_STEPS_TAC CPT87_EXEC (17--18) THEN CPT87_TO_RSP THEN
  CPT87_INLINE_TAC "H_ADD"
   [mk_comb(`mld_poly_invntt_tomont`,CPT87_ACC); CPT87_UNPACK] 19 THEN
  X86_STEPS_TAC CPT87_EXEC (20--20) THEN
  SAMPLING_GHOST_REGS_TAC [`YMM5`; `YMM6`] "s20" THEN
  CPT87_LOAD_CONST_TAC 0 0x10b THEN CPT87_LOAD_CONST_TAC 1 0x113 THEN
  X86_STEPS_TAC CPT87_EXEC (21--23) THEN
  CPT87_XMM_TAC 5 XMM5 "s23" "0x00400000004000000040000000400000" THEN
  CPT87_XMM_TAC 6 XMM6 "s23" "0xff801fffff801fffff801fffff801fff" THEN
  CPT87_INLINE_TAC "H_RED" [CPT87_ADD] 24 THEN
  X86_STEPS_TAC CPT87_EXEC (25--25) THEN
  SAMPLING_GHOST_REGS_TAC [`YMM7`] "s25" THEN
  CPT87_LOAD_CONST_TAC 3 0x1a6 THEN
  X86_STEPS_TAC CPT87_EXEC (26--27) THEN
  CPT87_INLINE_TAC "H_CADDQ" [CPT87_RED] 28 THEN
  X86_STEPS_TAC CPT87_EXEC (29--29) THEN
  SAMPLING_GHOST_REGS_TAC [`YMM6`] "s29" THEN
  CPT87_LOAD_CONST_TAC 2 0x1e4 THEN
  X86_STEPS_TAC CPT87_EXEC (30--31) THEN
  CPT87_XMM_TAC 6 XMM6 "s31" "0x00000fff00000fff00000fff00000fff" THEN
  CPT87_XMM_TAC 7 XMM7 "s31" "0xffffe000ffffe000ffffe000ffffe000" THEN
  CPT87_INLINE_TAC "H_P2R" [CPT87_CADDQ] 32 THEN
  X86_STEPS_TAC CPT87_EXEC (33--34) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc CPT87_EXEC
   "H_T1"
   [`read RSP s`; `word_add (pkt1:int64) (word(320 * i))`; `pc:num`;
    mk_comb(`mld_poly_power2round_hi`,CPT87_CADDQ)]
   (`i:num`::CPT87_ALLOWED) 35 THEN
  X86_STEPS_TAC CPT87_EXEC (36--39) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CPT87_T0PTR]) THEN
  CPT87_FROM_RSP THEN
  CPT87_LOOP_CALL_TAC "H_T0"
   [`read RDI s`; `read RSI s`;
    mk_comb(`mld_poly_power2round_lo`,CPT87_CADDQ)] 40 THEN
  X86_STEPS_TAC CPT87_EXEC (41--44) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CPT87_JOIN_TAC CPT87_PACK_T1 THEN NO_TAC) THEN
  TRY(CPT87_JOIN_TAC CPT87_PACK_T0 THEN NO_TAC) THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The zeroing of the two polynomials and of the structure with memset, and  *)
(* the return.                                                               *)
(* ------------------------------------------------------------------------- *)

let CPT87_MEMSET_TAC c =
  LIBC_PLT_TAC CPT87_EXEC (layout "plt_memset") (layout "got_memset") c THEN
  LIBC_FULL_CALL_TAC "H_MEMSET" CPT87_EXEC
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
    `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   (ref CPT87_ALLOWED) (c + 2);;

let CPT87_EPILOGUE_TAC =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  X86_STEPS_TAC CPT87_EXEC (1--5) THEN
  CPT87_MEMSET_TAC 5 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE `word_add (word_sub (x:int64) (word 8)) (word 8) = x`]) THEN
  X86_STEPS_TAC CPT87_EXEC (8--12) THEN
  CPT87_MEMSET_TAC 12 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE `word_add (word_sub (x:int64) (word 8)) (word 8) = x`]) THEN
  X86_STEPS_TAC CPT87_EXEC (15--19) THEN
  CPT87_MEMSET_TAC 19 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE `word_add (word_sub (x:int64) (word 8)) (word 8) = x`]) THEN
  X86_STEPS_TAC CPT87_EXEC (22--35) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM(MATCH_ACCEPT_TAC o
        CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN NO_TAC) THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together, with t as the code *)
(* computes it (mld_compute_t_lazy) and without the bound on s1hat: the      *)
(* statement of the FULL theorem with these changes (MLD_LAZY_FULL0 of       *)
(* common/fips204/properties/mldsa_native_lazy_matrix.ml). The theorems for  *)
(* the callees and for the inlined loops are assumed before the events are   *)
(* instantiated; the libc contracts, instantiated for the same (ea,el,ev),   *)
(* are those of memset and, for the callees, of memset and memcpy.           *)
(* ------------------------------------------------------------------------- *)

let CPT87_FULL0 = prove
 (MLD_LAZY_FULL0
   MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let ms,mcb = CONJ_PAIR th in
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP
       MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
       th) "H_ROW" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
     "H_INV" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     MLDSA_NATIVE_POLYETA_UNPACK_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
     "H_UNPACK" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
     "H_T0" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC CPT87_ADD_LOOP "H_ADD" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC CPT87_RED_LOOP "H_RED" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC CPT87_CADDQ_LOOP "H_CADDQ" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC CPT87_P2R_LOOP "H_P2R" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC CPT87_T1_LOOP "H_T1" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] ms)
     "H_MEMSET") THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(pkt1:int64) (t0:int64) (s1hat:int64) (s2:int64) (rho:int64) (r:num)
     (mf:int64) (mc:int64) (pc:num) (stackpointer:int64)
     (returnaddress:int64).
     APPEND
      (f_ev_epil pkt1 t0 s1hat s2 rho r mf mc pc stackpointer returnaddress)
      (APPEND
        (ENUMERATEL 8
          (\i. f_ev_loop pkt1 t0 s1hat s2 rho r mf mc pc stackpointer
                         returnaddress i))
        (f_ev_prol pkt1 t0 s1hat s2 rho r mf mc pc stackpointer
                   returnaddress))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst CPT87_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REALIGN_TAC 4853 THEN REALIGN_FRAME_TAC 4901 4853 THEN
  REALIGN_NONOV_TAC 4822
   [`pkt1:int64,2560`; `t0:int64,3328`; `s1hat:int64,7168`; `s2:int64,768`;
    `rho:int64,32`; `word pc:int64,libmldsa_size`;
    `word(pc + got_memset):int64,8`; `word(pc + got_memcpy):int64,8`;
    `ea:int64,el:num`;
    `word_add stackpointer (word 4853):int64,48`;
    `word_add stackpointer (word 4901):int64,8`] THEN
  REALIGN_ALIGNED_TAC [1654; 1686; 2710; 3734; 4758] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `8`
   `pc + mld_compute_pack_t0_t187_loop1`
   `pc + mld_compute_pack_t0_t187_loop1_exit`
   CPT87_INVARIANT THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; CPT87_PROLOGUE_TAC; CPT87_BODY_TAC; CPT87_EPILOGUE_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together, with t =           *)
(* mld_compute_t for s1hat within the bound (MLD_LAZY_COMPUTE_T_PACK of      *)
(* lazy_eq_spec.ml, with the bound of the unpacked coefficients of s2).      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun cth ->
    MLD_LAZY_FULL_OF_FULL0_TAC
     (MP (SPEC_ALL CPT87_FULL0) cth)
     (MP_TAC(SPECL [`8`; `7`; `mld_polyeta_unpack_2`; `96`; `r:num`;
                    `sh:num->int32`; `s2b:num->byte`]
                   MLD_LAZY_COMPUTE_T_PACK) THEN
      ANTS_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV THEN
        ASM_REWRITE_TAC[MLD_LAZY_ETA_UNPACK_BOUND];
        CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN STRIP_TAC])));;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    CORRECT_OF_FULL_TAC
     (MP (SPEC_ALL
       MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    SAFE_OF_FULL_TAC (MP (SPEC_ALL CPT87_FULL0) th)));;
