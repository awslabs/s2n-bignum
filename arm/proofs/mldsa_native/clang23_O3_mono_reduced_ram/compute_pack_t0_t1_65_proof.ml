(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The vector t of key generation, split and packed: the proof (see          *)
(* compute_pack_t0_t1_65_spec.ml). It follows the proof for the gcc 12 -O2   *)
(* reduced-RAM build: a loop over the rows with the invariant of the packed  *)
(* rows so far, for the polynomials of t as the code computes them           *)
(* (mld_compute_t_lazy). clang has inlined polyeta_unpack (eta = 4),         *)
(* poly_add, poly_reduce, poly_caddq, poly_power2round and polyt1_pack into  *)
(* the row, which the proof uses through the lemmas of                       *)
(* compute_pack_t0_t1_65_inline.ml in the way the gcc proof uses the         *)
(* theorems of the callees.                                                  *)
(*                                                                           *)
(* The function saves 160 bytes of registers at stackpointer + 5152 (with    *)
(* stackpointer the bottom of the 5312 bytes), and its frame F of 3456 bytes *)
(* is 32-byte aligned below them, at stackpointer + b with b = 1696 if the   *)
(* stack pointer is a multiple of 32 and 1680 otherwise, one proof for each  *)
(* (CPT65_CASE_TAC b). The frame holds the TBL indices at F + 16 to F + 79   *)
(* and F + 112 to F + 319, the pointers t0, s1hat and s2 at F + 88, F + 96   *)
(* and F + 104, s2 unpacked and then t1 at F + 320, t at F + 1344, the       *)
(* matrix structure (its polynomial, then rho at F + 3392) at F + 2368 and   *)
(* the canary at F + 3448.                                                   *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/compute_pack_t0_t1_65_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/lazy_eq_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/compute_pack_t0_t1_65_inline.ml";;
needs "arm/proofs/utils/mldsa_native_wrap.ml";;

let CPT65_EXEC = MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC;;
let CPT65_MC = mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc;;

let CPT65_ROW_FULL =
  MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL;;

let CPT65_PACK_T1 =
  CONV_RULE NUM_REDUCE_CONV
   (SPECL [`5`; `mld_polyeta_unpack_4`; `128`] MLD_COMPUTE_T_LAZY_PACK_T1);;

let CPT65_PACK_T0 =
  CONV_RULE NUM_REDUCE_CONV
   (SPECL [`5`; `mld_polyeta_unpack_4`; `128`] MLD_COMPUTE_T_LAZY_PACK_T0);;

let CPT65_ALLOWED =
  [`pc:num`; `pkt1:int64`; `t0:int64`; `s1hat:int64`; `s2:int64`;
   `rho:int64`; `r:num`; `guard:int64`; `mf:int64`; `mc:int64`;
   `stackpointer:int64`; `returnaddress:int64`];;

let CPT65_CALL_TAC name ilist n =
  FULL_CALL_TAC CPT65_MC CPT65_EXEC name ilist CPT65_ALLOWED n;;

let CPT65_LOOP_CALL_TAC name ilist n =
  FULL_CALL_TAC CPT65_MC CPT65_EXEC name ilist (`i:num`::CPT65_ALLOWED) n;;

let CPT65_ARGS =
  "pkt1 t0 s1hat s2 rho r guard mf mc pc stackpointer returnaddress";;

let CPT65_TEMPLATE =
  let f n = "(f_ev_" ^ n ^ " " ^ CPT65_ARGS ^ ")"
  and fi n = "(\\i. f_ev_" ^ n ^ " " ^ CPT65_ARGS ^ " i)" in
  let case x =
    "APPEND " ^ f ("epil_"^x) ^ " (APPEND (ENUMERATEL 6 " ^ fi ("loop_"^x) ^
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

let CPT65_SAVED_FACTS =
  String.concat " /\\\n" (map (fun (r,k) ->
     Printf.sprintf
      "read (memory :> bytes64 (word_add stackpointer (word %d))) s = %s" k r)
   ["d15_init",5152; "d14_init",5160; "d13_init",5168; "d12_init",5176;
    "d11_init",5184; "d10_init",5192; "d9_init",5200; "d8_init",5208;
    "x29_init",5216; "returnaddress",5224; "x28_init",5232;
    "x27_init",5240; "x26_init",5248; "x25_init",5256; "x24_init",5264;
    "x23_init",5272; "x22_init",5280; "x21_init",5288; "x20_init",5296;
    "x19_init",5304]);;

let CPT65_CONSTS =
  [64,"0x3c3834302c2824201c1814100c080400";
   48,"0x03ffffff1202ffffff1101ffffff1000";
   32,"0x0fff1a120b0aff19110605ff18100100";
   16,"0x0f120d0c0b0a11080706051003020100"] @ CPT_TBL_STACK;;

let CPT65_FRAME_FACTS b =
  String.concat " /\\\n"
  ([Printf.sprintf "read SP s = word_add stackpointer (word %d)" b;
    "read X29 s = word_add stackpointer (word 5216)";
    CPT65_SAVED_FACTS;
    Printf.sprintf
     "read (memory :> bytes64 (word_add stackpointer (word %d))) s = canary"
     (b + 3448);
    "read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard))) s = guard";
    "read (memory :> bytes64 guard) s = canary";
    "read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf";
    "read (memory :> bytes64 (word_add (word pc) (word got_memcpy))) s = mc";
    "read (memory :> bytes (ea,el)) s = ev";
    Printf.sprintf "read (memory :> bytes64 (word_add stackpointer (word %d))) s = t0" (b + 88);
    Printf.sprintf "read (memory :> bytes64 (word_add stackpointer (word %d))) s = s1hat" (b + 96);
    Printf.sprintf "read (memory :> bytes64 (word_add stackpointer (word %d))) s = s2" (b + 104);
    Printf.sprintf
     "read (memory :> bytes (word_add stackpointer (word %d),32)) s = r"
     (b + 3392);
    "(!j. j < 1280
          ==> read(memory :> bytes32(word_add s1hat (word(4 * j)))) s = sh j)";
    "(!j. j < 768
          ==> read(memory :> bytes8(word_add s2 (word j))) s = s2b j)"] @
   map (fun (k,v) -> Printf.sprintf
     "read (memory :> bytes128 (word_add stackpointer (word %d))) s = word %s"
     (b + k) v) CPT65_CONSTS);;

let CPT65_INVARIANT b =
  parse_term(Printf.sprintf
   "\\i s. %s /\\
          read X19 s = word_add stackpointer (word %d) /\\
          read X20 s = word_add stackpointer (word %d) /\\
          read X21 s = word 8380417 /\\
          read X22 s = word_add pkt1 (word(320 * i)) /\\
          read X23 s = word i /\\
          read X24 s = word_add stackpointer (word %d) /\\
          read X25 s = word_add stackpointer (word %d) /\\
          read X26 s = word_add stackpointer (word %d) /\\
          read X27 s = word_add stackpointer (word %d) /\\
          read X28 s = word 4286586879 /\\
          (!j. j < 320 * i
               ==> read(memory :> bytes8(word_add pkt1 (word j))) s =
                   mld_polyvec_pack 320 mld_polyt1_pack
                    (mld_polyvec_map mld_poly_power2round_hi
                      (mld_compute_t_lazy 5 mld_polyeta_unpack_4 128 r sh s2b)) j) /\\
          (!j. j < 416 * i
               ==> read(memory :> bytes8(word_add t0 (word j))) s =
                   mld_polyvec_pack 416 mld_polyt0_pack
                    (mld_polyvec_map mld_poly_power2round_lo
                      (mld_compute_t_lazy 5 mld_polyeta_unpack_4 128 r sh s2b)) j)"
   (CPT65_FRAME_FACTS b) (b + 960) (b + 1216) (b + 320) (b + 1344) (b + 832)
   (b + 1088));;

let CPT65_SP k =
  mk_comb(`word_add (stackpointer:int64)`,
          mk_comb(`word:num->int64`,mk_small_numeral k));;

(* ------------------------------------------------------------------------- *)
(* The prologue: the saved registers, the frame, the copy of rho into the    *)
(* structure, the canary and the spill of the 17 vectors of constants of the *)
(* image (and -q) to F + 32 .. F + 319.                                      *)
(* ------------------------------------------------------------------------- *)

let CPT65_IMG_CONSTS =
  map (fun k -> MLDSA_NATIVE_IMAGE_CONST_RULE
                 (layout ("mld_compute_pack_t0_t165_const" ^ string_of_int k)) 128)
      (1--17);;

let CPT65_IMG_CONSTS_TAC =
  MAP_EVERY (fun th -> FIRST_ASSUM(fun ath ->
     try ASSUME_TAC(MATCH_MP th ath) with Failure _ -> NO_TAC)) CPT65_IMG_CONSTS;;

let CPT65_BUF_TAC =
  FIRST_ASSUM(fun a16 ->
    if concl a16 <> `aligned 16 (stackpointer:int64)` then NO_TAC else
    let th = MP (SPEC `stackpointer:int64` (MLD_WRAP_BUFFER_RULE `1696`)) a16 in
    FIRST_ASSUM(fun cth ->
      if concl cth = `aligned 32 (stackpointer:int64)` ||
         concl cth = `~aligned 32 (stackpointer:int64)`
      then RULE_ASSUM_TAC(REWRITE_RULE[REWRITE_RULE[cth] th])
      else NO_TAC));;

let CPT65_ADRPS = [16;18;19;33;38;42;45;48;51;54;57;60;63;66;69;72;75;78];;

let rec CPT65_STEPTO adrps lo hi =
  if lo > hi then ALL_TAC else
  match filter (fun k -> k >= lo && k <= hi) adrps with
    [] -> ARM_STEPS_TAC CPT65_EXEC (lo--hi)
  | k::_ -> ARM_STEPS_TAC CPT65_EXEC (lo--k) THEN MLKEM_NATIVE_ADRP_TAC THEN
            CPT65_STEPTO adrps (k+1) hi;;

let CPT65_RHO_TAC =
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

let CPT65_PROLOGUE_TAC b =
  FULL_INIT_TAC THEN CPT65_IMG_CONSTS_TAC THEN CPT65_RHO_TAC THEN
  ARM_STEPS_TAC CPT65_EXEC (1--13) THEN CPT65_BUF_TAC THEN
  CPT65_STEPTO CPT65_ADRPS 14 85 THEN
  MP_TAC(SPECL [CPT65_SP(b + 3392); `r:num`; `s85:armstate`]
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

let CPT65_ROW = `mld_polyvec_matrix_row_lazy 5 r (sh:num->int32) i`;;

let CPT65_UNPACK = `mld_polyeta_unpack_4 (\j. (s2b:num->byte)(128 * i + j))`;;

let CPT65_INVT = mk_comb(`mld_poly_invntt_tomont`,CPT65_ROW);;

let CPT65_ADDP = list_mk_comb(`mld_poly_add`,[CPT65_INVT; CPT65_UNPACK]);;

let CPT65_REDP = mk_comb(`mld_poly_reduce`,CPT65_ADDP);;

let CPT65_CADDQP = mk_comb(`mld_poly_caddq`,CPT65_REDP);;

let CPT65_HI = mk_comb(`mld_poly_power2round_hi`,CPT65_CADDQP);;

let CPT65_LO = mk_comb(`mld_poly_power2round_lo`,CPT65_CADDQP);;

let CPT65_JOIN_TAC pth =
  MATCH_MP_TAC VEC_JOIN_POLY THEN CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[pth]];;

let CPT65_NOV_TAC b =
  MP_TAC(SPECL [`stackpointer:int64`; `s2:int64`; mk_small_numeral(b + 320);
                `768`; `i:num`; `128`] CPT_NOV_ROW) THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMPLE_ARITH_TAC];
    DISCH_TAC];;

let CPT65_BODY_TAC b =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  FULL_INIT_TAC THEN ARM_STEPS_TAC CPT65_EXEC (1--5) THEN
  SUBGOAL_THEN `word_zx(word_zx(word i:int64):int32):int64 = word i`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC WORD_ZX_ZX_SMALL THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CPT65_LOOP_CALL_TAC "H_ROW"
   [`read X0 s`; `read X1 s`; `read X2 s`; `r:num`; `sh:num->int32`;
    `i:num`; `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 6 THEN
  ARM_STEPS_TAC CPT65_EXEC (7--8) THEN
  CPT65_LOOP_CALL_TAC "H_INV"
   [`read X0 s`; CPT65_ROW; `pc:num`; `read SP s`; `read X30 s`] 9 THEN
  VEC_SLICE_TAC
   `!j. j < 128
        ==> read(memory :> bytes8(word_add s2 (word(128 * i + j)))) s9 =
            (s2b:num->byte)(128 * i + j)` THEN
  CPT65_NOV_TAC b THEN CPT_UNFOLD_TAC b 1344 THEN
  CPT65_LOOP_CALL_TAC "H_ADD"
   [`read SP s`; `s2:int64`; `i:num`; `word_add (s2:int64) (word(128 * i))`;
    CPT65_INVT; `\j. (s2b:num->byte)(128 * i + j)`; `pc:num`] 10 THEN
  CPT_FOLD_TAC THEN
  CPT65_LOOP_CALL_TAC "H_RED" [`read X25 s`; CPT65_ADDP; `pc:num`] 11 THEN
  ARM_STEPS_TAC CPT65_EXEC [12] THEN
  CPT65_LOOP_CALL_TAC "H_CADDQ" [`read X25 s`; CPT65_REDP; `pc:num`] 13 THEN
  ARM_STEPS_TAC CPT65_EXEC (14--18) THEN
  CPT65_LOOP_CALL_TAC "H_P2R" [`read X25 s`; `read X24 s`; CPT65_CADDQP; `pc:num`] 19 THEN
  ARM_STEPS_TAC CPT65_EXEC (20--21) THEN
  CPT65_LOOP_CALL_TAC "H_T1"
   [`read SP s`; `read X24 s`; `read X9 s`; CPT65_HI; `pc:num`] 22 THEN
  ARM_STEPS_TAC CPT65_EXEC (23--27) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CPT_MADD]) THEN
  CPT65_LOOP_CALL_TAC "H_T0"
   [`read X0 s`; `read X1 s`; CPT65_LO; `guard:int64`; `pc:num`; `read SP s`;
    `read X30 s`] 28 THEN
  ARM_STEPS_TAC CPT65_EXEC (29--32) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CPT65_JOIN_TAC CPT65_PACK_T1 THEN NO_TAC) THEN
  TRY(CPT65_JOIN_TAC CPT65_PACK_T0 THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The zeroing of the two polynomials and of the structure with memset, the  *)
(* check of the canary, the restoring of the registers and the return.       *)
(* ------------------------------------------------------------------------- *)

let CPT65_MEMSET_TAC n =
  LIBC_PLT_TAC CPT65_EXEC n THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" CPT65_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`]
   (ref CPT65_ALLOWED) (n + 5);;

let CPT65_EPILOGUE_TAC b =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  ARM_STEPS_TAC CPT65_EXEC (1--5) THEN CPT65_MEMSET_TAC 5 THEN
  ARM_STEPS_TAC CPT65_EXEC (11--15) THEN CPT65_MEMSET_TAC 15 THEN
  ARM_STEPS_TAC CPT65_EXEC (21--25) THEN CPT65_MEMSET_TAC 25 THEN
  ARM_STEPS_TAC CPT65_EXEC [31] THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC CPT65_EXEC (32--57) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[CPT_ZX128] THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM(MATCH_ACCEPT_TAC o
        CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let CPT65_CASE_TAC b =
  ENSURES_EVENTS_WHILE_UP2_TAC `6`
   `pc + mld_compute_pack_t0_t165_loop1`
   `pc + mld_compute_pack_t0_t165_loop1_exit`
   (CPT65_INVARIANT b) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC; CPT65_PROLOGUE_TAC b; CPT65_BODY_TAC b; CPT65_EPILOGUE_TAC b];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, with t as the code computes *)
(* it (mld_compute_t_lazy) and without the bound on s1hat: the statement of  *)
(* the FULL theorem with these changes (MLD_LAZY_FULL0).                     *)
(* ------------------------------------------------------------------------- *)

let CPT65_CALLEES_TAC =
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (MATCH_MP CPT65_ROW_FULL th) "H_ROW") THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_full_contract] (CONJUNCT1 th)) "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_INV" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL
   "H_T0" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC CPT65_ADD "H_ADD" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC CPT65_RED "H_RED" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC CPT65_CADDQ "H_CADDQ" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC CPT65_P2R "H_P2R" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC CPT65_T1 "H_T1";;

let CPT65_SETUP_TAC =
  CONCRETIZE_F_EVENTS_TAC CPT65_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst CPT65_EXEC] THEN
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

let CPT65_FULL0 = prove
 (MLD_LAZY_FULL0
   MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CPT65_CALLEES_TAC THEN CPT65_SETUP_TAC THEN
  ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [REWRITE_TAC[ASSUME `aligned 32 (stackpointer:int64)`] THEN CPT65_CASE_TAC 1696;
    REWRITE_TAC[ASSUME `~aligned 32 (stackpointer:int64)`] THEN CPT65_CASE_TAC 1680]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, with t = mld_compute_t for  *)
(* s1hat within the bound (MLD_LAZY_COMPUTE_T_PACK, with the bound of the    *)
(* unpacked coefficients of s2).                                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  MLD_LAZY_FULL_OF_FULL0_TAC CPT65_FULL0
   (MP_TAC(SPECL [`6`; `5`; `mld_polyeta_unpack_4`; `128`; `r:num`; `sh:num->int32`;
                  `s2b:num->byte`] MLD_LAZY_COMPUTE_T_PACK) THEN
    ANTS_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[MLD_LAZY_ETA_UNPACK_BOUND];
      CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN STRIP_TAC]));;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC (MP (SPEC_ALL CPT65_FULL0) th)));;
