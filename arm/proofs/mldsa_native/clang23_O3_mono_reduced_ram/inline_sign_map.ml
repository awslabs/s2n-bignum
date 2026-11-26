(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Straight-line code that clang 23 -O3 has made of the loops of poly_shiftl *)
(* and poly_sub inlined into mldsa{44,65,87}_verify_internal: 64 loads of 16 *)
(* bytes (four coefficients) of each input polynomial on the stack, 64       *)
(* vector operations and 64 stores, in an order that has no loop structure. *)
(* The lemmas are stated as those for the loops (inline_sign.ml), from the   *)
(* start of the code to its end, with the frame F (the stack pointer) as a   *)
(* parameter fp and the polynomials at fp + offset.                              *)
(*                                                                           *)
(* The proof takes each input polynomial as 64 128-bit values               *)
(* (INLINE_MAP_INPUT_TAC), simulates the code, splits the 64 stores into    *)
(* 32-bit lanes and proves the 256 outputs by rewriting with the lanes.      *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;

(*** The 64 128-bit values of a polynomial x at F + off ***)

let INLINE_MAP_INPUT_TAC (off:int) (x:term) =
  let fv = `fp:int64` in
  let addr n = mk_comb(mk_comb(`word_add:int64->int64->int64`,fv),
                       mk_comb(`word:num->int64`,mk_small_numeral n)) in
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if not(is_forall c && free_in x c && free_in fv c) then NO_TAC else
    let lanes = map (fun i ->
      let th1 = SPEC (mk_small_numeral i) th in
      let th2 = MP th1 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th1)))) in
      CONV_RULE(LAND_CONV(DEPTH_CONV NUM_RED_CONV)) th2) (0--255) in
    let ths = map (fun k ->
      let tm = subst [addr(off + 16 * k),`A:int64`]
                `read (memory :> bytes128 A) (s0:armstate)` in
      let eth = READ_MEMORY_MERGE_CONV 2 tm in
      let eth = CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV
                  NORMALIZE_RELATIVE_ADDRESS_CONV)) eth in
      REWRITE_RULE lanes eth) (0--63) in
    MAP_EVERY ASSUME_TAC ths);;

(*** The statement: inputs xs (name, offset), output at offset out with the ***)
(*** value fout (a term in the inputs and i), the registers written, extra   ***)
(*** pre- and postconditions, the readable region (lo, len) of the stack     ***)

let INLINE_MAP_STMT mc start stop ins out fout readlo readlen
                    (mods:string list) extrapre extrapost =
  let qmods,xmods = partition (fun r -> String.get r 0 = 'Q') mods in
  let binders = String.concat " " (map (fun (x,_) -> "("^x^":num->int32)") ins) in
  let infacts = String.concat " /\\\n" (map (fun (x,off) ->
    Printf.sprintf
     "(!i. i < 256
           ==> read(memory :> bytes32(word_add fp (word(%d + 4 * i)))) s =
               %s i)" off x) ins) in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e (fp:int64) %s pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        aligned 16 fp /\\
        nonoverlapping (word_add fp (word %d),1024) (word pc,libmldsa_size)
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read SP s = fp /\\ %s
                  %s /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\ %s
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add fp (word(%d + 4 * i))))
                             s = %s) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events fp pc /\\
                     memaccess_inbounds e2
                      [word_add fp (word %d),%d]
                      [word_add fp (word %d),1024]))
             (MAYCHANGE [PC; %s] ,, MAYCHANGE [%s] ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(word_add fp (word %d),1024)])"
   binders out mc start extrapre infacts stop extrapost out fout
   readlo readlen out (String.concat "; " xmods) (String.concat "; " qmods) out);;

(*** The proof, with n the number of instructions and lanes the lemmas for ***)
(*** the 32-bit lanes of the outputs                                       ***)

let INLINE_MAP_PROVE tm exec ins n (defs:thm list) (lanes:thm list) =
  prove(tm,
  CONCRETIZE_F_EVENTS_TAC
   `\(fp:int64) (pc:num). f_ev_map fp pc :(uarch_event)list` THEN
  META_EXISTS_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; fst exec] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  MAP_EVERY (fun (x,off) -> INLINE_MAP_INPUT_TAC off (mk_var(x,`:num->int32`)))
    ins THEN
  ARM_STEPS_TAC exec (1--n) THEN
  WIDE_STORE_SPLIT_TAC `fp:int64` 32 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
    ASM_REWRITE_TAC defs THEN
    CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
    REWRITE_TAC lanes;
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* poly_shiftl in place at F + 448 (verify_internal_44: +0x1c14 to +0x1e88,  *)
(* 157 instructions, the last one add x0, sp, #0x1c0 is the argument of the  *)
(* following call of poly_ntt).                                              *)
(* ------------------------------------------------------------------------- *)

let INLINE_SHL13_LANE = prove
 (`!x:int32. word_shl x 13 = word_mul x (word 8192)`,
  GEN_TAC THEN BITBLAST_TAC);;

let INLINE_SHIFTL_STMT mc start stop (mods:string list) =
  INLINE_MAP_STMT mc start stop ["x",448] 448 "mld_poly_shiftl x i" 448 1024
   mods "" "read X0 s = word_add fp (word 448) /\\";;

(* ------------------------------------------------------------------------- *)
(* poly_sub at F + 1472 of the polynomial at F + 448 (verify_internal_44:    *)
(* +0x1f10 to +0x22d4, 241 instructions), which also sets x8 = 0, q4 =       *)
(* 2^22 and q5 = -q (from F + 320) in each lane for the poly_reduce loop     *)
(* that follows.                                                             *)
(* ------------------------------------------------------------------------- *)

let INLINE_SUB_STMT mc start stop (mods:string list) =
  INLINE_MAP_STMT mc start stop ["x",448; "y",1472] 1472 "mld_poly_sub y x i"
   320 2176 mods
   "read (memory :> bytes128 (word_add fp (word 320))) s =
      word 0xff801fffff801fffff801fffff801fff /\\"
   "read X8 s = word 0 /\\
    read Q4 s = word 0x00400000004000000040000000400000 /\\
    read Q5 s = word 0xff801fffff801fffff801fffff801fff /\\";;

(*** The instances in mldsa44_verify_internal: the statements and proofs ***)
(*** (shiftl 157 instructions, sub 241; about 2 and 5 minutes)           ***)

let INLINE_MAP_QMODS =
  ["Q0";"Q1";"Q2";"Q3";"Q4";"Q5";"Q6";"Q7";"Q16";"Q17";"Q18";"Q19";"Q20";
   "Q21";"Q22";"Q23";"Q24";"Q25";"Q26";"Q27";"Q28";"Q29";"Q30";"Q31"];;

let INLINE_SHIFTL44_START = "mldsa44_verify_internal_loop7_exit";;

let INLINE_SHIFTL44_STOP =
  string_of_int (layout "mldsa44_verify_internal_after_mldsa_poly_ntt_6" - 4);;

let INLINE_SHIFTL44_TERM =
  INLINE_SHIFTL_STMT "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc"
   INLINE_SHIFTL44_START INLINE_SHIFTL44_STOP ("X0"::INLINE_MAP_QMODS);;

let INLINE_SHIFTL44 () =
  INLINE_MAP_PROVE INLINE_SHIFTL44_TERM
   (INLINE_LOOP_EXEC INLINE_SHIFTL44_START INLINE_SHIFTL44_STOP)
   ["x",448] 157 [mld_poly_shiftl] [INLINE_SHL13_LANE];;

let INLINE_SUB44_TERM =
  INLINE_SUB_STMT "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc"
   "mldsa44_verify_internal_loop8_exit" "mldsa44_verify_internal_loop9"
   ("X8"::INLINE_MAP_QMODS);;

let INLINE_SUB44 () =
  INLINE_MAP_PROVE INLINE_SUB44_TERM
   (INLINE_LOOP_EXEC "mldsa44_verify_internal_loop8_exit"
                     "mldsa44_verify_internal_loop9")
   ["x",448; "y",1472] 241 [mld_poly_sub] [];;
