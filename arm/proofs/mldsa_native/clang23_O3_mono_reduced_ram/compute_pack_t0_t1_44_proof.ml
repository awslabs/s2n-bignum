(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The vector t of key generation, split and packed: the proof (see          *)
(* compute_pack_t0_t1_44_spec.ml). It follows the proof for the gcc 12 -O2   *)
(* reduced-RAM build: a loop over the rows with the invariant of the packed  *)
(* rows so far, for the polynomials of t as the code computes them           *)
(* (mld_compute_t_lazy). clang has inlined poly_add, poly_reduce,            *)
(* poly_caddq, poly_power2round and polyt1_pack into the row, which the      *)
(* proof uses through the lemmas of compute_pack_t0_t1_44_inline.ml in the   *)
(* way the gcc proof uses the theorems of the callees.                       *)
(*                                                                           *)
(* The function saves 160 bytes of registers at stackpointer + 5152 (with    *)
(* stackpointer the bottom of the 5312 bytes), and its frame F of 3456 bytes *)
(* is 32-byte aligned below them, at stackpointer + b with b = 1696 if the   *)
(* stack pointer is a multiple of 32 and 1680 otherwise, one proof for each  *)
(* (CPT44_CASE_TAC b). The frame holds the TBL indices and -q at F + 32 to   *)
(* F + 319, s2 unpacked and then t1 at F + 320, t at F + 1344, the matrix    *)
(* structure (its polynomial, then rho at F + 3392) at F + 2368 and the      *)
(* canary at F + 3448.                                                       *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/compute_pack_t0_t1_44_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/lazy_eq_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/compute_pack_t0_t1_44_inline.ml";;
needs "arm/proofs/utils/mldsa_native_wrap.ml";;

let CPT44_EXEC = MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;
let CPT44_MC = mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc;;

let CPT44_ROW_FULL =
  MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL;;

let CPT44_PACK_T1 =
  CONV_RULE NUM_REDUCE_CONV
   (SPECL [`4`; `mld_polyeta_unpack_2`; `96`] MLD_COMPUTE_T_LAZY_PACK_T1);;

let CPT44_PACK_T0 =
  CONV_RULE NUM_REDUCE_CONV
   (SPECL [`4`; `mld_polyeta_unpack_2`; `96`] MLD_COMPUTE_T_LAZY_PACK_T0);;

let CPT44_ALLOWED =
  [`pc:num`; `pkt1:int64`; `t0:int64`; `s1hat:int64`; `s2:int64`;
   `rho:int64`; `r:num`; `guard:int64`; `mf:int64`; `mc:int64`;
   `stackpointer:int64`; `returnaddress:int64`];;

let CPT44_CALL_TAC name ilist n =
  FULL_CALL_TAC CPT44_MC CPT44_EXEC name ilist CPT44_ALLOWED n;;

let CPT44_LOOP_CALL_TAC name ilist n =
  FULL_CALL_TAC CPT44_MC CPT44_EXEC name ilist (`i:num`::CPT44_ALLOWED) n;;

let CPT44_ARGS =
  "pkt1 t0 s1hat s2 rho r guard mf mc pc stackpointer returnaddress";;

let CPT44_TEMPLATE =
  let f n = "(f_ev_" ^ n ^ " " ^ CPT44_ARGS ^ ")"
  and fi n = "(\\i. f_ev_" ^ n ^ " " ^ CPT44_ARGS ^ " i)" in
  let case x =
    "APPEND " ^ f ("epil_"^x) ^ " (APPEND (ENUMERATEL 4 " ^ fi ("loop_"^x) ^
    ") " ^ f ("prol_"^x) ^ ")" in
  parse_term
   ("\\(pkt1:int64) (t0:int64) (s1hat:int64) (s2:int64) (rho:int64) (r:num) " ^
    "(guard:int64) (mf:int64) (mc:int64) (pc:num) (stackpointer:int64) " ^
    "(returnaddress:int64). if aligned 32 stackpointer then " ^ case "a" ^
    " else " ^ case "u" ^ " :(uarch_event)list");;

(* ------------------------------------------------------------------------- *)
(* The facts of the frame, with F = stackpointer + b: the saved registers,   *)
(* the canary, the TBL indices and -q, rho in the structure of the matrix.   *)
(* ------------------------------------------------------------------------- *)

let CPT44_SAVED_FACTS =
  String.concat " /\\\n" (map (fun (r,k) ->
     Printf.sprintf
      "read (memory :> bytes64 (word_add stackpointer (word %d))) s = %s" k r)
   ["d15_init",5152; "d14_init",5160; "d13_init",5168; "d12_init",5176;
    "d11_init",5184; "d10_init",5192; "d9_init",5200; "d8_init",5208;
    "x29_init",5216; "returnaddress",5224; "x28_init",5232;
    "x27_init",5240; "x26_init",5248; "x25_init",5256; "x24_init",5264;
    "x23_init",5272; "x22_init",5280; "x21_init",5288; "x20_init",5296;
    "x19_init",5304]);;

let CPT44_CONSTS =
  [80,"0x3c3834302c2824201c1814100c080400";
   64,"0x03ffffff1202ffffff1101ffffff1000";
   48,"0x0fff1a120b0aff19110605ff18100100";
   32,"0x0f120d0c0b0a11080706051003020100";
   96,"0xff801fffff801fffff801fffff801fff"] @ CPT_TBL_STACK;;

let CPT44_FRAME_FACTS b =
  String.concat " /\\\n"
  ([Printf.sprintf "read SP s = word_add stackpointer (word %d)" b;
    "read X29 s = word_add stackpointer (word 5216)";
    CPT44_SAVED_FACTS;
    Printf.sprintf
     "read (memory :> bytes64 (word_add stackpointer (word %d))) s = canary"
     (b + 3448);
    "read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard))) s = guard";
    "read (memory :> bytes64 guard) s = canary";
    "read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf";
    "read (memory :> bytes64 (word_add (word pc) (word got_memcpy))) s = mc";
    "read (memory :> bytes (ea,el)) s = ev";
    Printf.sprintf
     "read (memory :> bytes (word_add stackpointer (word %d),32)) s = r"
     (b + 3392);
    "(!j. j < 1024
          ==> read(memory :> bytes32(word_add s1hat (word(4 * j)))) s = sh j)";
    "(!j. j < 384
          ==> read(memory :> bytes8(word_add s2 (word j))) s = s2b j)"] @
   map (fun (k,v) -> Printf.sprintf
     "read (memory :> bytes128 (word_add stackpointer (word %d))) s = word %s"
     (b + k) v) CPT44_CONSTS);;

let CPT44_INVARIANT b =
  parse_term(Printf.sprintf
   "\\i s. %s /\\
          read X19 s = s2 /\\ read X20 s = s1hat /\\ read X21 s = t0 /\\
          read X22 s = word_add pkt1 (word(320 * i)) /\\
          read X23 s = word i /\\
          read X24 s = word_add stackpointer (word %d) /\\
          read X25 s = word 96 /\\
          read X26 s = word_add stackpointer (word %d) /\\
          read X27 s = word 8380417 /\\ read X28 s = word 416 /\\
          (!j. j < 320 * i
               ==> read(memory :> bytes8(word_add pkt1 (word j))) s =
                   mld_polyvec_pack 320 mld_polyt1_pack
                    (mld_polyvec_map mld_poly_power2round_hi
                      (mld_compute_t_lazy 4 mld_polyeta_unpack_2 96 r sh s2b)) j) /\\
          (!j. j < 416 * i
               ==> read(memory :> bytes8(word_add t0 (word j))) s =
                   mld_polyvec_pack 416 mld_polyt0_pack
                    (mld_polyvec_map mld_poly_power2round_lo
                      (mld_compute_t_lazy 4 mld_polyeta_unpack_2 96 r sh s2b)) j)"
   (CPT44_FRAME_FACTS b) (b + 1344) (b + 320));;

let CPT44_SP k =
  mk_comb(`word_add (stackpointer:int64)`,
          mk_comb(`word:num->int64`,mk_small_numeral k));;

(* ------------------------------------------------------------------------- *)
(* The prologue: the saved registers, the frame, the copy of rho into the    *)
(* structure, the canary and the spill of the 17 vectors of constants of the *)
(* image (and -q) to F + 32 .. F + 319.                                      *)
(* ------------------------------------------------------------------------- *)

let CPT44_IMG_CONSTS =
  map (fun k -> MLDSA_NATIVE_IMAGE_CONST_RULE
                 (layout ("mld_compute_pack_t0_t144_const" ^ string_of_int k)) 128)
      (1--17);;

let CPT44_IMG_CONSTS_TAC =
  MAP_EVERY (fun th -> FIRST_ASSUM(fun ath ->
     try ASSUME_TAC(MATCH_MP th ath) with Failure _ -> NO_TAC)) CPT44_IMG_CONSTS;;

let CPT44_BUF_TAC =
  FIRST_ASSUM(fun a16 ->
    if concl a16 <> `aligned 16 (stackpointer:int64)` then NO_TAC else
    let th = MP (SPEC `stackpointer:int64` (MLD_WRAP_BUFFER_RULE `1696`)) a16 in
    FIRST_ASSUM(fun cth ->
      if concl cth = `aligned 32 (stackpointer:int64)` ||
         concl cth = `~aligned 32 (stackpointer:int64)`
      then RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_RULE[cth] th])
      else NO_TAC));;

let CPT44_ADRPS = [14;16;18;34;38;41;45;48;51;54;57;60;63;66;69;72;75;78];;

let rec CPT44_STEPTO adrps lo hi =
  if lo > hi then ALL_TAC else
  match filter (fun k -> k >= lo && k <= hi) adrps with
    [] -> ARM_STEPS_TAC CPT44_EXEC (lo--hi)
  | k::_ -> ARM_STEPS_TAC CPT44_EXEC (lo--k) THEN MLKEM_NATIVE_ADRP_TAC THEN
            CPT44_STEPTO adrps (k+1) hi;;

let CPT44_RHO_TAC =
  FIRST_ASSUM(MP_TAC o MATCH_MP MLD_BYTES128_HALVES o check
   (can (term_match [] `read (memory :> bytes(rho,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `r < 2 EXP 256` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check
     (can (term_match [] `read (memory :> bytes(rho,32)) s = n`) o concl)) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
    MP_TAC(ISPECL [`rho:int64`; `32`; `read memory (s0:armstate)`]
                  READ_BYTES_BOUND) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC];;

let CPT44_PROLOGUE_TAC b =
  FULL_INIT_TAC THEN CPT44_IMG_CONSTS_TAC THEN CPT44_RHO_TAC THEN
  ARM_STEPS_TAC CPT44_EXEC (1--13) THEN CPT44_BUF_TAC THEN
  CPT44_STEPTO CPT44_ADRPS 14 85 THEN
  MP_TAC(SPECL [CPT44_SP(b + 3392); `r:num`; `s85:armstate`]
               MLD_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[CONV_RULE NUM_REDUCE_CONV (ASSUME `r < 2 EXP 256`)];
    DISCH_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The body of the loop for row i: row_lazy, the inverse NTT, the unpacking  *)
(* of s2, the five inlined parts (sum, reduce, caddq, power2round, packing   *)
(* of t1), polyt0_pack and the loop test.                                    *)
(* ------------------------------------------------------------------------- *)

let CPT44_ROW = `mld_polyvec_matrix_row_lazy 4 r (sh:num->int32) i`;;

let CPT44_UNPACK = `mld_polyeta_unpack_2 (\j. (s2b:num->byte)(96 * i + j))`;;

let CPT44_INVT = mk_comb(`mld_poly_invntt_tomont`,CPT44_ROW);;

let CPT44_ADDP = list_mk_comb(`mld_poly_add`,[CPT44_INVT; CPT44_UNPACK]);;

let CPT44_REDP = mk_comb(`mld_poly_reduce`,CPT44_ADDP);;

let CPT44_CADDQP = mk_comb(`mld_poly_caddq`,CPT44_REDP);;

let CPT44_HI = mk_comb(`mld_poly_power2round_hi`,CPT44_CADDQP);;

let CPT44_LO = mk_comb(`mld_poly_power2round_lo`,CPT44_CADDQP);;

let CPT44_JOIN_TAC pth =
  MATCH_MP_TAC VEC_JOIN_POLY THEN CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[pth]];;

let CPT44_BODY_TAC b =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC CPT44_EXEC (1--5) THEN
  SUBGOAL_THEN `word_zx(word_zx(word i:int64):int32):int64 = word i`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC WORD_ZX_ZX_SMALL THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CPT44_LOOP_CALL_TAC "H_ROW"
   [`read X0 s`; `read X1 s`; `read X2 s`; `r:num`; `sh:num->int32`;
    `i:num`; `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 6 THEN
  ARM_STEPS_TAC CPT44_EXEC (7--8) THEN
  CPT44_LOOP_CALL_TAC "H_INV"
   [`read X0 s`; CPT44_ROW; `pc:num`; `read SP s`; `read X30 s`] 9 THEN
  ARM_STEPS_TAC CPT44_EXEC (10--12) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CPT_MADD]) THEN
  VEC_SLICE_TAC
   `!j. j < 96
        ==> read(memory :> bytes8(word_add s2 (word(96 * i + j)))) s12 =
            (s2b:num->byte)(96 * i + j)` THEN
  CPT44_LOOP_CALL_TAC "H_UNPACK"
   [`read X0 s`; `read X1 s`; `\j. (s2b:num->byte)(96 * i + j)`; `pc:num`;
    `read SP s`; `read X30 s`] 13 THEN
  CPT_UNFOLD_TAC b 1344 THEN CPT_UNFOLD_TAC b 320 THEN
  CPT44_LOOP_CALL_TAC "H_ADD" [`read SP s`; CPT44_INVT; CPT44_UNPACK; `pc:num`] 14 THEN
  CPT_FOLD_TAC THEN
  CPT44_LOOP_CALL_TAC "H_RED" [`read X24 s`; CPT44_ADDP; `pc:num`] 15 THEN
  ARM_STEPS_TAC CPT44_EXEC [16] THEN
  CPT44_LOOP_CALL_TAC "H_CADDQ" [`read X24 s`; CPT44_REDP; `pc:num`] 17 THEN
  ARM_STEPS_TAC CPT44_EXEC (18--22) THEN
  CPT44_LOOP_CALL_TAC "H_P2R" [`read X24 s`; `read X26 s`; CPT44_CADDQP; `pc:num`] 23 THEN
  ARM_STEPS_TAC CPT44_EXEC (24--25) THEN
  CPT44_LOOP_CALL_TAC "H_T1"
   [`read SP s`; `read X26 s`; `read X9 s`; CPT44_HI; `pc:num`] 26 THEN
  ARM_STEPS_TAC CPT44_EXEC (27--29) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CPT_MADD]) THEN
  CPT44_LOOP_CALL_TAC "H_T0"
   [`read X0 s`; `read X1 s`; CPT44_LO; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 30 THEN
  ARM_STEPS_TAC CPT44_EXEC (31--34) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CPT44_JOIN_TAC CPT44_PACK_T1 THEN NO_TAC) THEN
  TRY(CPT44_JOIN_TAC CPT44_PACK_T0 THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The zeroing of the two polynomials and of the structure with memset, the  *)
(* check of the canary, the restoring of the registers and the return.       *)
(* ------------------------------------------------------------------------- *)

let CPT44_MEMSET_TAC n =
  LIBC_PLT_TAC CPT44_EXEC n THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" CPT44_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`]
   (ref CPT44_ALLOWED) (n + 5);;

let CPT44_EPILOGUE_TAC b =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  ARM_STEPS_TAC CPT44_EXEC (1--5) THEN CPT44_MEMSET_TAC 5 THEN
  ARM_STEPS_TAC CPT44_EXEC (11--15) THEN CPT44_MEMSET_TAC 15 THEN
  ARM_STEPS_TAC CPT44_EXEC (21--25) THEN CPT44_MEMSET_TAC 25 THEN
  ARM_STEPS_TAC CPT44_EXEC [31] THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC CPT44_EXEC (32--57) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[CPT_ZX128] THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM(MATCH_ACCEPT_TAC o
        CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let CPT44_CASE_TAC b =
  ENSURES_EVENTS_WHILE_UP2_TAC `4`
   `pc + mld_compute_pack_t0_t144_loop1`
   `pc + mld_compute_pack_t0_t144_loop1_exit`
   (CPT44_INVARIANT b) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; CPT44_PROLOGUE_TAC b; CPT44_BODY_TAC b; CPT44_EPILOGUE_TAC b];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, with t as the code computes *)
(* it (mld_compute_t_lazy) and without the bound on s1hat: the statement of  *)
(* the FULL theorem with these changes (MLD_LAZY_FULL0).                     *)
(* ------------------------------------------------------------------------- *)

let CPT44_CALLEES_TAC =
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP CPT44_ROW_FULL th) "H_ROW") THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_full_contract] (CONJUNCT1 th)) "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_INV" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYETA_UNPACK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_UNPACK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_T0" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC CPT44_ADD "H_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC CPT44_RED "H_RED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC CPT44_CADDQ "H_CADDQ" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC CPT44_P2R "H_P2R" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC CPT44_T1 "H_T1";;

let CPT44_SETUP_TAC =
  CONCRETIZE_F_EVENTS_TAC CPT44_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst CPT44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 5312):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
    SPECL [`pc:num`; `got_memset:num`] WORD_ADD;
    SPECL [`pc:num`; `got_memcpy:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const("X"^string_of_int n,[]))) (19--29) THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_DREG_TAC ("d"^string_of_int n^"_init")
     (mk_const("D"^string_of_int n,[]))) (8--15);;

let CPT44_FULL0 = prove
 (MLD_LAZY_FULL0
   MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CPT44_CALLEES_TAC THEN CPT44_SETUP_TAC THEN
  ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [REWRITE_TAC[ASSUME `aligned 32 (stackpointer:int64)`] THEN CPT44_CASE_TAC 1696;
    REWRITE_TAC[ASSUME `~aligned 32 (stackpointer:int64)`] THEN CPT44_CASE_TAC 1680]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, with t = mld_compute_t for  *)
(* s1hat within the bound (MLD_LAZY_COMPUTE_T_PACK, with the bound of the    *)
(* unpacked coefficients of s2).                                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  MLD_LAZY_FULL_OF_FULL0_TAC CPT44_FULL0
   (MP_TAC(SPECL [`4`; `4`; `mld_polyeta_unpack_2`; `96`; `r:num`; `sh:num->int32`;
                  `s2b:num->byte`] MLD_LAZY_COMPUTE_T_PACK) THEN
    ANTS_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[MLD_LAZY_ETA_UNPACK_BOUND];
      CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN STRIP_TAC]));;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC (MP (SPEC_ALL CPT44_FULL0) th)));;
