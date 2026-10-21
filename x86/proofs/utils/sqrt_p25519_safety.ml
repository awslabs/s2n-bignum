(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time and memory safety proofs of bignum_sqrt_p25519,           *)
(* bignum_invsqrt_p25519, edwards25519_decode and their _alt versions,     *)
(* which compute powers modulo p_25519 with a local multiplication         *)
(* (LOCAL_MUL_P25519) and a local repeated squaring (LOCAL_NSQR_P25519).   *)
(* ========================================================================= *)

needs "x86/proofs/consttime.ml";;

(* The safety proof of LOCAL_NSQR_P25519, given the decoding theorem, the  *)
(* PCs of the start and the end of its loop and the number of steps of one *)
(* squaring.                                                               *)

let NSQR_P25519_SAFETY_TAC exec ~loop:(loop_start,loop_end) ~sqr =
  let pcoff off = mk_comb(`(+) (pc:num)`,mk_small_numeral off) in
  CONCRETIZE_F_EVENTS_TAC
    `\(z:int64) (k:int64) (x:int64) (pc:num) (stackpointer:int64).
      APPEND
        (f_ev_loop_post z k x pc stackpointer)
        (APPEND
          (ENUMERATEL (val k) (f_ev_loop z k x pc stackpointer))
            (f_ev_loop_pre z k x pc stackpointer))
      :(uarch_event) list` THEN

  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN

  REPEAT STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; ALL; SOME_FLAGS] THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `val (k:int64)`
    (pcoff loop_start) (pcoff loop_end)
   `\i s. read RSP s = stackpointer /\
          read RDI s = z /\
          read RSI s = word((val (k:int64)) - i)` THEN REPEAT CONJ_TAC THENL [
    ASM_ARITH_TAC;

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC exec (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REWRITE_TAC[SUB_0;WORD_VAL];ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC; (*** Main loop invariant ***)

    ENSURES_INIT_TAC "s0" THEN
    STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC exec (1--17) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC
  ] THEN

  REPEAT STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  STRIP_EXISTS_ASSUM_TAC THEN
  X86_STEPS_TAC exec (1--sqr) THEN
  X86_STEPS_TAC exec ((sqr+1)--(sqr+1)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
    ABBREV_TAC `k' = val (k:int64)` THEN
    VAL_INT64_TAC `k' - i` THEN VAL_INT64_TAC `1` THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN
    SIMPLE_ARITH_TAC; ALL_TAC
  ] THEN
  CONJ_TAC THENL [
    IMP_REWRITE_TAC[WORD_SUB2] THEN
    ABBREV_TAC `k' = val (k:int64)` THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN SIMPLE_ARITH_TAC; SIMPLE_ARITH_TAC];
    ALL_TAC
  ] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* Simulate a call of LOCAL_MUL_P25519 or LOCAL_NSQR_P25519, with          *)
(* arguments args, using the safety theorem registered under the label     *)
(* assump_name; vars are the variables of the theorem being proved.        *)

let SQRT_P25519_CALL_TAC (tmc,exec) args vars (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (tmc,exec,0x0,tmc,safety_th)
      (`e:(uarch_event)list`::args) n
    THENL [
      EXISTS_E2_TAC (ref vars);

      LABEL_TAC assump_name safety_th
    ]);;

(* The safety proofs of the cores, given their code and decoding theorem   *)
(* and the safety theorems of LOCAL_MUL_P25519 and LOCAL_NSQR_P25519.      *)

let BIGNUM_SQRT_P25519_SAFETY_TAC (tmc,exec) (mul_th,nsqr_th) =
  let vars = [`z:int64`;`x:int64`;`pc:num`;`stackpointer:int64`] in
  let mul_tac = SQRT_P25519_CALL_TAC (tmc,exec)
    [`read RDI s`; `read RSI s`; `read RDX s`; `pc:num`] vars
  and nsqr_tac = SQRT_P25519_CALL_TAC (tmc,exec)
    [`read RDI s`; `read RSI s`; `read RDX s`; `pc:num`; `stackpointer:int64`]
    vars in
  ASSUME_CALLEE_SAFETY_TAILED_TAC mul_th "H_MUL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC nsqr_th "H_NSQR" THEN
  META_EXISTS_TAC THEN
  REWRITE_TAC[ALL;SOME_FLAGS;C_ARGUMENTS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EXISTING_PRESERVED_TAC `RSP` THEN

  ENSURES_INIT_TAC "s0" THEN

  (*** Initial modular reduction ***)

  X86_STEPS_TAC exec (1--25) THEN

  (*** The exponentiation tower and the final computations; the step
       numbers are those of the correctness proof plus 100 ***)

  X86_STEPS_TAC exec (101--104) THEN nsqr_tac "H_NSQR" 105 THEN
  X86_STEPS_TAC exec (106--110) THEN mul_tac "H_MUL" 111 THEN
  X86_STEPS_TAC exec (112--116) THEN nsqr_tac "H_NSQR" 117 THEN
  X86_STEPS_TAC exec (118--122) THEN mul_tac "H_MUL" 123 THEN
  X86_STEPS_TAC exec (124--128) THEN nsqr_tac "H_NSQR" 129 THEN
  X86_STEPS_TAC exec (130--134) THEN mul_tac "H_MUL" 135 THEN
  X86_STEPS_TAC exec (136--140) THEN nsqr_tac "H_NSQR" 141 THEN
  X86_STEPS_TAC exec (142--146) THEN mul_tac "H_MUL" 147 THEN
  X86_STEPS_TAC exec (148--152) THEN nsqr_tac "H_NSQR" 153 THEN
  X86_STEPS_TAC exec (154--158) THEN mul_tac "H_MUL" 159 THEN
  X86_STEPS_TAC exec (160--164) THEN nsqr_tac "H_NSQR" 165 THEN
  X86_STEPS_TAC exec (166--170) THEN mul_tac "H_MUL" 171 THEN
  X86_STEPS_TAC exec (172--176) THEN nsqr_tac "H_NSQR" 177 THEN
  X86_STEPS_TAC exec (178--182) THEN mul_tac "H_MUL" 183 THEN
  X86_STEPS_TAC exec (184--188) THEN nsqr_tac "H_NSQR" 189 THEN
  X86_STEPS_TAC exec (190--194) THEN mul_tac "H_MUL" 195 THEN
  X86_STEPS_TAC exec (196--200) THEN nsqr_tac "H_NSQR" 201 THEN
  X86_STEPS_TAC exec (202--206) THEN mul_tac "H_MUL" 207 THEN
  X86_STEPS_TAC exec (208--212) THEN nsqr_tac "H_NSQR" 213 THEN
  X86_STEPS_TAC exec (214--218) THEN mul_tac "H_MUL" 219 THEN
  X86_STEPS_TAC exec (220--224) THEN nsqr_tac "H_NSQR" 225 THEN
  X86_STEPS_TAC exec (226--230) THEN mul_tac "H_MUL" 231 THEN
  X86_STEPS_TAC exec (232--236) THEN nsqr_tac "H_NSQR" 237 THEN
  X86_STEPS_TAC exec (238--250) THEN mul_tac "H_MUL" 251 THEN
  X86_STEPS_TAC exec (252--256) THEN nsqr_tac "H_NSQR" 257 THEN
  X86_STEPS_TAC exec (258--304) THEN nsqr_tac "H_NSQR" 305 THEN
  X86_STEPS_TAC exec (306--326) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let BIGNUM_INVSQRT_P25519_SAFETY_TAC (tmc,exec) (mul_th,nsqr_th) =
  let vars = [`z:int64`;`x:int64`;`pc:num`;`stackpointer:int64`] in
  let mul_tac = SQRT_P25519_CALL_TAC (tmc,exec)
    [`read RDI s`; `read RSI s`; `read RDX s`; `pc:num`] vars
  and nsqr_tac = SQRT_P25519_CALL_TAC (tmc,exec)
    [`read RDI s`; `read RSI s`; `read RDX s`; `pc:num`; `stackpointer:int64`]
    vars in
  ASSUME_CALLEE_SAFETY_TAILED_TAC mul_th "H_MUL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC nsqr_th "H_NSQR" THEN
  META_EXISTS_TAC THEN
  REWRITE_TAC[ALL;SOME_FLAGS;C_ARGUMENTS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EXISTING_PRESERVED_TAC `RSP` THEN

  ENSURES_INIT_TAC "s0" THEN

  (*** Initial modular reduction ***)

  X86_STEPS_TAC exec (1--25) THEN

  (*** The exponentiation tower and the final computations; the step
       numbers are those of the correctness proof plus 100 ***)

  X86_STEPS_TAC exec (101--104) THEN nsqr_tac "H_NSQR" 105 THEN
  X86_STEPS_TAC exec (106--110) THEN mul_tac "H_MUL" 111 THEN
  X86_STEPS_TAC exec (112--116) THEN nsqr_tac "H_NSQR" 117 THEN
  X86_STEPS_TAC exec (118--122) THEN mul_tac "H_MUL" 123 THEN
  X86_STEPS_TAC exec (124--128) THEN nsqr_tac "H_NSQR" 129 THEN
  X86_STEPS_TAC exec (130--134) THEN mul_tac "H_MUL" 135 THEN
  X86_STEPS_TAC exec (136--140) THEN nsqr_tac "H_NSQR" 141 THEN
  X86_STEPS_TAC exec (142--146) THEN mul_tac "H_MUL" 147 THEN
  X86_STEPS_TAC exec (148--152) THEN nsqr_tac "H_NSQR" 153 THEN
  X86_STEPS_TAC exec (154--158) THEN mul_tac "H_MUL" 159 THEN
  X86_STEPS_TAC exec (160--164) THEN nsqr_tac "H_NSQR" 165 THEN
  X86_STEPS_TAC exec (166--170) THEN mul_tac "H_MUL" 171 THEN
  X86_STEPS_TAC exec (172--176) THEN nsqr_tac "H_NSQR" 177 THEN
  X86_STEPS_TAC exec (178--182) THEN mul_tac "H_MUL" 183 THEN
  X86_STEPS_TAC exec (184--188) THEN nsqr_tac "H_NSQR" 189 THEN
  X86_STEPS_TAC exec (190--194) THEN mul_tac "H_MUL" 195 THEN
  X86_STEPS_TAC exec (196--200) THEN nsqr_tac "H_NSQR" 201 THEN
  X86_STEPS_TAC exec (202--206) THEN mul_tac "H_MUL" 207 THEN
  X86_STEPS_TAC exec (208--212) THEN nsqr_tac "H_NSQR" 213 THEN
  X86_STEPS_TAC exec (214--218) THEN mul_tac "H_MUL" 219 THEN
  X86_STEPS_TAC exec (220--224) THEN nsqr_tac "H_NSQR" 225 THEN
  X86_STEPS_TAC exec (226--230) THEN mul_tac "H_MUL" 231 THEN
  X86_STEPS_TAC exec (232--244) THEN mul_tac "H_MUL" 245 THEN
  X86_STEPS_TAC exec (246--250) THEN nsqr_tac "H_NSQR" 251 THEN
  X86_STEPS_TAC exec (252--256) THEN mul_tac "H_MUL" 257 THEN
  X86_STEPS_TAC exec (258--301) THEN nsqr_tac "H_NSQR" 302 THEN
  X86_STEPS_TAC exec (303--307) THEN mul_tac "H_MUL" 308 THEN
  X86_STEPS_TAC exec (309--325) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let EDWARDS25519_DECODE_SAFETY_TAC (tmc,exec) (mul_th,nsqr_th) =
  let vars = [`z:int64`;`c:int64`;`pc:num`;`stackpointer:int64`] in
  let mul_tac = SQRT_P25519_CALL_TAC (tmc,exec)
    [`read RDI s`; `read RSI s`; `read RDX s`; `pc:num`] vars
  and nsqr_tac = SQRT_P25519_CALL_TAC (tmc,exec)
    [`read RDI s`; `read RSI s`; `read RDX s`; `pc:num`; `stackpointer:int64`]
    vars in
  ASSUME_CALLEE_SAFETY_TAILED_TAC mul_th "H_MUL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC nsqr_th "H_NSQR" THEN
  META_EXISTS_TAC THEN
  REWRITE_TAC[ALL;SOME_FLAGS;C_ARGUMENTS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EXISTING_PRESERVED_TAC `RSP` THEN

  ENSURES_INIT_TAC "s0" THEN
  (* simply use symbolic sim to cover the first part of ENSURES_SEQUENCE_TAC *)
  X86_STEPS_TAC exec (1--19) THEN
  (* now the second part of ENSURES_SEQUENCE_TAC. *)
  X86_STEPS_TAC exec (20--23) THEN
  nsqr_tac "H_NSQR" 24 THEN
  X86_STEPS_TAC exec (25--50) THEN
  mul_tac "H_MUL" 51 THEN
  X86_STEPS_TAC exec (52--64) THEN
  X86_STEPS_TAC exec (65--68) THEN
  mul_tac "H_MUL" 69 THEN

  (*** The power tower. Simply add 100 to the step numbers of fn correctness
       proof... ***)

  X86_STEPS_TAC exec (151--155) THEN nsqr_tac "H_NSQR"  156 THEN
  X86_STEPS_TAC exec (157--161) THEN mul_tac "H_MUL"  162 THEN
  X86_STEPS_TAC exec (163--167) THEN nsqr_tac "H_NSQR"  168 THEN
  X86_STEPS_TAC exec (169--173) THEN mul_tac "H_MUL"  174 THEN
  X86_STEPS_TAC exec (175--179) THEN nsqr_tac "H_NSQR"  180 THEN
  X86_STEPS_TAC exec (181--185) THEN mul_tac "H_MUL"  186 THEN
  X86_STEPS_TAC exec (187--191) THEN nsqr_tac "H_NSQR"  192 THEN
  X86_STEPS_TAC exec (193--197) THEN mul_tac "H_MUL"  198 THEN
  X86_STEPS_TAC exec (199--203) THEN nsqr_tac "H_NSQR"  204 THEN
  X86_STEPS_TAC exec (205--209) THEN mul_tac "H_MUL"  210 THEN
  X86_STEPS_TAC exec (211--215) THEN nsqr_tac "H_NSQR"  216 THEN
  X86_STEPS_TAC exec (217--221) THEN mul_tac "H_MUL"  222 THEN
  X86_STEPS_TAC exec (223--227) THEN nsqr_tac "H_NSQR"  228 THEN
  X86_STEPS_TAC exec (229--233) THEN mul_tac "H_MUL"  234 THEN
  X86_STEPS_TAC exec (235--239) THEN nsqr_tac "H_NSQR"  240 THEN
  X86_STEPS_TAC exec (241--245) THEN mul_tac "H_MUL"  246 THEN
  X86_STEPS_TAC exec (247--251) THEN nsqr_tac "H_NSQR"  252 THEN
  X86_STEPS_TAC exec (253--257) THEN mul_tac "H_MUL"  258 THEN
  X86_STEPS_TAC exec (259--263) THEN nsqr_tac "H_NSQR"  264 THEN
  X86_STEPS_TAC exec (265--269) THEN mul_tac "H_MUL"  270 THEN
  X86_STEPS_TAC exec (271--275) THEN nsqr_tac "H_NSQR"  276 THEN
  X86_STEPS_TAC exec (277--281) THEN mul_tac "H_MUL"  282 THEN

  (*** e^2 * w computation ***)
  X86_STEPS_TAC exec (283--287) THEN nsqr_tac "H_NSQR" 288 THEN
  X86_STEPS_TAC exec (289--293) THEN mul_tac "H_MUL" 294 THEN

  (*** s = u * e ***)
  X86_STEPS_TAC exec (295--299) THEN mul_tac "H_MUL" 300 THEN

  (*** t = j_25519 * s ***)
  X86_STEPS_TAC exec (301--313) THEN
  mul_tac "H_MUL" 314 THEN

  (*** Comparison with 0 or 1 ***)
  X86_STEPS_TAC exec (315--325) THEN

  (*** Comparison with -1 ***)
  X86_STEPS_TAC exec (326--333) THEN

  (*** Multiplexing of s or t ***)
  X86_STEPS_TAC exec (334--350) THEN

  (*** Error indication (so far) ***)
  X86_STEPS_TAC exec (351--355) THEN

  (*** Computation of p_25519 - x and all ***)
  X86_STEPS_TAC exec (356--367) THEN
  X86_STEPS_TAC exec (368--400) THEN

  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;
