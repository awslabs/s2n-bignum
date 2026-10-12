(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Helpers for the constant-time and memory safety proofs of AES-XTS         *)
(* encryption and decryption (arm/proofs/aes_xts_{en,de}crypt.ml).           *)
(* ========================================================================= *)

needs "arm/proofs/consttime.ml";;

let AES_XTS_BLT_LEMMA = BITBLAST_RULE
 `~(ival(word_sub (x:int64) (word 16)) < &0 <=>
    ~(ival x - &16 = ival(word_sub x (word 16)))) <=> ival x < &16`;;

let AES_XTS_LEN_BOUND_LEMMA = BITBLAST_RULE
 `~(ival (x:int64) < &16) ==> 16 <= val x /\ val x < 2 EXP 63`;;

let AES_XTS_TAIL_LEMMA = prove
 (`!x:int64. word_and x (word 15) = word (val x MOD 16)`,
  REWRITE_TAC[ARITH_RULE `15 = 2 EXP 4 - 1`; WORD_AND_MASK_WORD] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let AES_XTS_TAIL_AND_LEMMA = prove
 (`!n. n < 16 ==> val (word_and (word n) (word 15):int64) = n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[AES_XTS_TAIL_LEMMA] THEN
  SUBGOAL_THEN `val (word n:int64) = n` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN MATCH_MP_TAC VAL_WORD_EQ THEN
  REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC);;

let AES_XTS_BGT_LEMMA = prove
 (`!n m. 1 <= n /\ n < 2 EXP 63 /\ m = n - 1
         ==> ((~(val (word m:int64) = 0) /\
               (ival (word m:int64) < &0 <=>
                ~(ival (word n:int64) - &1 = ival (word m:int64)))) <=>
              1 < n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `ival (word n:int64) = &n /\ ival (word m:int64) = &m /\
    val (word m:int64) = m`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC IVAL_WORD_LT THEN ASM_ARITH_TAC;
      MATCH_MP_TAC IVAL_WORD_LT THEN ASM_ARITH_TAC;
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[INT_OF_NUM_LT; INT_LT_REFL] THEN
  REWRITE_TAC[ARITH_RULE `~(m < 0)`] THEN
  ASM_SIMP_TAC[INT_OF_NUM_SUB; GSYM INT_OF_NUM_EQ] THEN ASM_ARITH_TAC);;

(* The final memory-safety reasoning wants plain numerals, so abbreviate the
   length after the event trace has been unified.                           *)

let AES_XTS_DISCHARGE_TAC =
  GEN_DISCHARGE_SAFETY_PROPERTY_TAC (ABBREV_TAC `vl = val (len:int64)`);;

(* Narrow the output-buffer part of the frame to what a straight-line part
   actually writes, before simulating it (as in the correctness proof).     *)

let AES_XTS_NARROW_FRAME_TAC (newmem:term) : tactic =
  fun (asl,w) ->
    let frame = rand w in
    let oldmem = find_term (fun t ->
      match t with
        Comb(Const("MAYCHANGE",_),l) ->
          (match dest_list l with
             [c] -> (try let m,b = dest_binary ":>" c in
                         name_of m = "memory" &&
                         (let f,a = dest_comb b in
                          name_of f = "bytes" && rand a = `val (len:int64)`)
                     with Failure _ -> false)
           | _ -> false)
      | _ -> false) frame in
    let frame' = subst [newmem, oldmem] frame in
    (MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN
     EXISTS_TAC frame' THEN
     CONJ_TAC THENL
      [REPEAT (GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM SEQ_ASSOC] THEN
               MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN
       ABBREV_TAC `vallen = val (len:int64)` THEN SUBSUMED_MAYCHANGE_TAC;
       ALL_TAC]) (asl,w);;

let AES_XTS_PEEL_TAC =
  REPEAT(W(fun (asl,w) ->
    if is_conj w && not (is_exists (lhand w)) then
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]
    else NO_TAC));;

(* One iteration of the byte-swapping loop of cipher stealing; the second
   argument is the output buffer and the third the offset in it (in X1) of
   the last full block.                                                     *)

let AES_XTS_CS_BODY_TAC exec outp off =
  SUBGOAL_THEN
   `word_sub (word (val (len:int64) MOD 16 - i)) (word 1):int64 =
    word (val len MOD 16 - (i + 1))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `val (len:int64) MOD 16 - i = (val len MOD 16 - (i + 1)) + 1`
    SUBST1_TAC THENL [ASM_ARITH_TAC; CONV_TAC WORD_RULE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`val (len:int64) MOD 16 - i`; `val (len:int64) MOD 16 - (i + 1)`]
    AES_XTS_BGT_LEMMA) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `1 < val (len:int64) MOD 16 - i <=> i + 1 < val len MOD 16`
  SUBST1_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  AES_XTS_NARROW_FRAME_TAC
   (subst [outp,`outp:int64`; off,`off:num`]
     `MAYCHANGE
       [memory :> bytes8 (word_add (word_add outp (word (16 * val (len:int64) DIV 16)))
                                   (word (val len MOD 16 - (i + 1))));
        memory :> bytes8 (word_add (word_add outp (word off))
                                   (word (val len MOD 16 - (i + 1))))]`) THEN
  ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC exec (1--6) THEN
  SAFETY_REWRITE_READS_TAC ["PC"] [SAFETY_COND_WORD_LIFT] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  AES_XTS_DISCHARGE_TAC;;
