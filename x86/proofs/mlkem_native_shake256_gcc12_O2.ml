(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHAKE256 with an output of any length. This is the code for               *)
(* mlkem_shake256 from mlkem-native's portable C implementation compiled by  *)
(* gcc 12 with -O2 (see mlkem_native/README.md), which absorbs the input     *)
(* into a state on the stack with mlk_keccak_absorb_once, and then for each  *)
(* block of the output permutes the state and extracts up to 136 bytes of    *)
(* it, the rate of SHAKE256, before zeroing the state with REP STOSQ. It is  *)
(* verified in the whole image (see mlkem_native_libmlkem_gcc12_O2.ml),      *)
(* where it is at address 0x3480, using the theorems for                     *)
(* mlk_keccak_absorb_once at 0x32b0, mlkem_keccakf1600_permute at 0x3e70 and *)
(* mlkem_keccakf1600_extract_bytes at 0x3d10 in the image. The result is     *)
(* shake256 of common/fips202.ml.                                            *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_keccak_absorb_once_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_keccakf1600_extract_bytes_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    3480: push   rbp
    3481: mov    r8d,0x1f
    3487: mov    rbp,rsp
    348a: push   r14
    348c: push   r13
    348e: mov    r13,rdi
    3491: push   r12
    3493: mov    r12,rsi
    3496: mov    esi,0x88
    349b: push   rbx
    349c: and    rsp,0xffffffffffffffe0
    34a0: sub    rsp,0xe0
    34a7: mov    r14,rsp
    34aa: mov    rdi,r14
    34ad: call   32b0 <mlk_keccak_absorb_once>
    34b2: test   r12,r12
    34b5: je     34eb <mlkem_shake256+0x6b>
    34b7: nop    WORD PTR [rax+rax*1+0x0]
    34c0: mov    rdi,r14
    34c3: mov    ebx,0x88
    34c8: call   3e70 <mlkem_keccakf1600_permute>
    34cd: cmp    r12,rbx
    34d0: mov    rsi,r13
    34d3: mov    rdi,r14
    34d6: cmovbe rbx,r12
    34da: xor    edx,edx
    34dc: mov    ecx,ebx
    34de: add    r13,rbx
    34e1: call   3d10 <mlkem_keccakf1600_extract_bytes>
    34e6: sub    r12,rbx
    34e9: jne    34c0 <mlkem_shake256+0x40>
    34eb: xor    eax,eax
    34ed: mov    rdi,r14
    34f0: mov    ecx,0x1c
    34f5: rep    stos QWORD PTR es:[rdi],rax
    34f8: lea    rsp,[rbp-0x20]
    34fc: pop    rbx
    34fd: pop    r12
    34ff: pop    r13
    3501: pop    r14
    3503: pop    rbp
    3504: ret
 ***)

let MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x3480,0x3505];;

(* ------------------------------------------------------------------------- *)
(* The state is aligned down to a multiple of 32 within the stack frame, by  *)
(* AND with -32 after the pushes, so its address is                          *)
(* stackpointer + (360 - k) for k = val(stackpointer + 584) MOD 32, where    *)
(* stackpointer is the bottom of the 624 bytes of the stack below the return *)
(* address. Addresses below it, for the calls, are put in the same form by   *)
(* SHAKE256_NORM_TAC, so that the simulation can show that they are in that  *)
(* part of the stack, with the bounds on k from SHAKE256_SETUP_TAC.          *)
(* ------------------------------------------------------------------------- *)

let WORD_AND_ALIGN_32 = prove
 (`!x:int64. word_and x (word 18446744073709551584) =
             word_sub x (word(val x MOD 32))`,
  GEN_TAC THEN
  SUBGOAL_THEN `val(x:int64) MOD 32 = val(word_and x (word 31):int64)`
  SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `31 = 2 EXP 5 - 1`] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 5 = 32`];
    REWRITE_TAC[WORD_VAL] THEN
    W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w))]);;

let SHAKE256_STATE_ADDRESS = prove
 (`!a:int64.
        word_sub (word_and (word_add a (word 584)) (word 18446744073709551584))
                 (word 224) =
        word_add a (word(360 - val(word_add a (word 584)) MOD 32))`,
  GEN_TAC THEN REWRITE_TAC[WORD_AND_ALIGN_32] THEN
  MP_TAC(SPECL [`val(word_add a (word 584):int64)`; `32`] MOD_LT_EQ) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`val(word_add a (word 584):int64) MOD 32`,`k:num`) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(INST [`360`,`x:num`; `k:num`,`y:num`]
    (INST_TYPE [`:64`,`:N`] WORD_SUB2)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `k < 32` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC WORD_RULE);;

let SHAKE256_ST =
 `word_add (stackpointer:int64)
           (word(360 - val(word_add stackpointer (word 584)) MOD 32))`;;

(*** The bound on outlen from the nonoverlapping, and its 64-bit word ***)

let SHAKE256_BOUND_TAC =
  SUBGOAL_THEN `632 + outlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(stackpointer:int64)`; `val(out:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word outlen:int64) = outlen` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC];;

(*** The addresses below the state, with the offset 352 - k and below ***)

let SHAKE256_NORM_TAC =
  let k = `val(word_add (stackpointer:int64) (word 584)) MOD 32` in
  let kth = REWRITE_RULE[ARITH_EQ]
   (SPECL [`val(word_add (stackpointer:int64) (word 584))`; `32`] MOD_LT_EQ) in
  let mk t = subst [k,`k:num`] t in
  let sub2 a = INST [mk_small_numeral a,`x:num`; `k:num`,`y:num`]
                    (INST_TYPE [`:64`,`:N`] WORD_SUB2) in
  let n t = mk_small_numeral t in
  let prv tm a b =
    prove(mk tm,
      MP_TAC kth THEN SPEC_TAC(k,`k:num`) THEN REPEAT STRIP_TAC THEN
      MP_TAC(sub2 a) THEN MP_TAC(sub2 b) THEN
      REPEAT(ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)]) THEN
      CONV_TAC WORD_RULE) in
  let sub_lemma a d =
    prv (subst [n a,`a:num`; n d,`d:num`; n (a - d),`e:num`]
         `word_sub (word_add stackpointer (word (a - k))) (word d):int64 =
          word_add stackpointer (word (e - k))`) a (a - d)
  and add_lemma a d =
    prv (subst [n a,`a:num`; n d,`d:num`; n (a + d),`e:num`]
         `word_add (word_add stackpointer (word (a - k))) (word d):int64 =
          word_add stackpointer (word (e - k))`) a (a + d)
  and wsub_lemma a d =
    prv (subst [n a,`a:num`; n d,`d:num`; n (a - d),`e:num`]
         `word_sub (word (a - k)) (word d):int64 = word (e - k)`) a (a - d)
  and wadd_lemma a d =
    prv (subst [n a,`a:num`; n d,`d:num`; n (a + d),`e:num`]
         `word_add (word (a - k)) (word d):int64 = word (e - k)`) a (a + d) in
  let arith = prove(mk `352 - k + 8 = 360 - k`,
    MP_TAC kth THEN SPEC_TAC(k,`k:num`) THEN ARITH_TAC) in
  let ths = [sub_lemma 360 8; sub_lemma 352 320; sub_lemma 352 256;
             add_lemma 352 8; wsub_lemma 360 8; wsub_lemma 352 320;
             wsub_lemma 352 256; wadd_lemma 352 8; arith] in
  RULE_ASSUM_TAC(REWRITE_RULE ths);;

(*** The setup, with the bounds on the offset of the state ***)

let SHAKE256_SETUP_TAC =
  SUBGOAL_THEN
   `val(word_add (stackpointer:int64) (word 584)) MOD 32 < 32 /\
    329 <= 360 - val(word_add (stackpointer:int64) (word 584)) MOD 32 /\
    360 - val(word_add (stackpointer:int64) (word 584)) MOD 32 <= 360`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`val(word_add (stackpointer:int64) (word 584))`; `32`]
      MOD_LT_EQ) THEN ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14`;;

let SHAKE256_MID =
 `\s. read R12 s = word outlen /\ read R13 s = out /\
      read R14 s =
      word_add stackpointer
       (word(360 - val(word_add stackpointer (word 584)) MOD 32)) /\
      read RBP s = word_add stackpointer (word 616) /\
      read RSP s =
      word_add stackpointer
       (word(360 - val(word_add stackpointer (word 584)) MOD 32)) /\
      read (memory :> bytes64 (word_add stackpointer (word 584))) s =
      rbx_init /\
      read (memory :> bytes64 (word_add stackpointer (word 592))) s =
      r12_init /\
      read (memory :> bytes64 (word_add stackpointer (word 600))) s =
      r13_init /\
      read (memory :> bytes64 (word_add stackpointer (word 608))) s =
      r14_init /\
      read (memory :> bytes64 (word_add stackpointer (word 616))) s =
      rbp_init /\
      read (memory :> bytes64 (word_add stackpointer (word 624))) s =
      returnaddress /\
      (read DF s <=> false) /\
      read (memory :> bytes(word_add stackpointer
              (word(360 - val(word_add stackpointer (word 584)) MOD 32)),
              200)) s =
      val(word_xor
       (keccak_absorb 136
         (num_of_bytelist inp +
          2 EXP (8 * LENGTH inp) *
          num_of_bytelist(keccak_pad 136 31 (LENGTH inp)))
         (LENGTH(inp:byte list) DIV 136))
       (word((num_of_bytelist inp +
              2 EXP (8 * LENGTH inp) *
              num_of_bytelist(keccak_pad 136 31 (LENGTH inp))) DIV
             2 EXP (8 * 136 * LENGTH inp DIV 136) MOD
             2 EXP (8 * 136))):1600 word)`;;
(* ------------------------------------------------------------------------- *)
(* Tactics for the loop, as for the AArch64 code.                            *)
(* ------------------------------------------------------------------------- *)

let SHAKE256_INV =
 `\i s. read R12 s = word(outlen - MIN outlen (136 * i)) /\
        read R13 s = word_add out (word(MIN outlen (136 * i))) /\
        read R14 s =
        word_add stackpointer
         (word(360 - val(word_add stackpointer (word 584)) MOD 32)) /\
        read RBP s = word_add stackpointer (word 616) /\
        read RSP s =
        word_add stackpointer
         (word(360 - val(word_add stackpointer (word 584)) MOD 32)) /\
        read (memory :> bytes64 (word_add stackpointer (word 584))) s =
        rbx_init /\
        read (memory :> bytes64 (word_add stackpointer (word 592))) s =
        r12_init /\
        read (memory :> bytes64 (word_add stackpointer (word 600))) s =
        r13_init /\
        read (memory :> bytes64 (word_add stackpointer (word 608))) s =
        r14_init /\
        read (memory :> bytes64 (word_add stackpointer (word 616))) s =
        rbp_init /\
        read (memory :> bytes64 (word_add stackpointer (word 624))) s =
        returnaddress /\
        (read DF s <=> false) /\
        read (memory :> bytes(out,MIN outlen (136 * i))) s =
        num_of_bytelist
         (list_of_seq (shake256 inp) (MIN outlen (136 * i))) /\
        read (memory :> bytes(word_add stackpointer
                (word(360 - val(word_add stackpointer (word 584)) MOD 32)),
                200)) s =
        val(keccak_squeeze i
         (word_xor
           (keccak_absorb 136
             (num_of_bytelist inp +
              2 EXP (8 * LENGTH inp) *
              num_of_bytelist(keccak_pad 136 31 (LENGTH inp)))
             (LENGTH(inp:byte list) DIV 136))
           (word((num_of_bytelist inp +
                  2 EXP (8 * LENGTH inp) *
                  num_of_bytelist(keccak_pad 136 31 (LENGTH inp))) DIV
                 2 EXP (8 * 136 * LENGTH inp DIV 136) MOD
                 2 EXP (8 * 136))):1600 word))`;;

(*** The test of outlen = 0 at the start, when it is known to be false ***)

let SHAKE256_NONZERO_TAC =
  let t1 = `val(word outlen:int64) = outlen` and t2 = `~(outlen = 0)` in
  RULE_ASSUM_TAC(fun th ->
    if concl th = t1 || concl th = t2 then th
    else REWRITE_RULE[ASSUME t1; ASSUME t2] th);;

(*** Iteration i of the loop, with 136 * i bytes done ***)

let SHAKE256_ITERATION_TAC tac =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN tac THEN
  SUBGOAL_THEN `136 * i < outlen` ASSUME_TAC THENL
   [UNDISCH_TAC `i < (outlen + 135) DIV 136` THEN
    REWRITE_TAC[ARITH_RULE `i < q <=> i + 1 <= q`] THEN
    SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `MIN outlen (136 * i) = 136 * i` SUBST1_TAC THENL
   [UNDISCH_TAC `136 * i < outlen` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `0 < MIN (outlen - 136 * i) 136 /\ MIN (outlen - 136 * i) 136 <= 136 /\
    0 + MIN (outlen - 136 * i) 136 <= 200 /\
    136 * i + MIN (outlen - 136 * i) 136 <= outlen /\
    MIN outlen (136 * (i + 1)) = 136 * i + MIN (outlen - 136 * i) 136 /\
    (outlen - 136 * i - MIN (outlen - 136 * i) 136 = 0 <=>
     ~(i + 1 < (outlen + 135) DIV 136))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `i + 1 < q <=> i + 2 <= q`] THEN
    SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN
    UNDISCH_TAC `136 * i < outlen` THEN ARITH_TAC;
    ALL_TAC];;

(*** The number of bytes extracted in each iteration, MIN x 136 ***)

let SHAKE256_CMOV_LEMMA = prove
 (`!x. x < 2 EXP 64
       ==> (if val (word x:int64) < 136 \/
               val (word_sub (word x) (word 136):int64) = 0
            then word x else word 136):int64 = word(MIN x 136)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
  SUBGOAL_THEN `val(word x:int64) = x /\ val(word 136:int64) = 136`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `x < 2 EXP 64` THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    COND_CASES_TAC THEN AP_TERM_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC]);;

let SHAKE256_LENGTH_TAC =
  MP_TAC(SPEC `outlen - 136 * i` SHAKE256_CMOV_LEMMA) THEN
  ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))];;

let SHAKE256_COUNTER_TAC =
  SUBGOAL_THEN
   `word_sub (word (outlen - 136 * i))
             (word(MIN (outlen - 136 * i) 136)):int64 =
    word(outlen - 136 * i - MIN (outlen - 136 * i) 136)` SUBST_ALL_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `val(word(outlen - 136 * i - MIN (outlen - 136 * i) 136):int64) =
    outlen - 136 * i - MIN (outlen - 136 * i) 136`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   `outlen - 136 * i - MIN (outlen - 136 * i) 136 = 0 <=>
    ~(i + 1 < (outlen + 135) DIV 136)`]);;

(*** The done count at the end of the loop ***)

let SHAKE256_EXIT_TAC =
  SUBGOAL_THEN `MIN outlen (136 * (outlen + 135) DIV 136) = outlen`
   SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `MIN a b = a <=> a <= b`] THEN
    MP_TAC(SPECL [`outlen + 135`; `136`] DIVISION) THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUB_REFL];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The input is a list of bytes, and the outlen bytes of  *)
(* the output, as a number, are the first outlen bytes of shake256 in        *)
(* common/fips202.ml. Each iteration of the loop extracts                    *)
(* MIN (outlen - 136 * i) 136 bytes, and the state is zeroed at the end,     *)
(* with REP STOSQ, so the specifications assume that the direction flag DF   *)
(* is clear, as the ABI requires on entry.                                   *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!out outlen m (inp:byte list) pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        PAIRWISE nonoverlapping
         [(out,outlen); (m,LENGTH inp);
          (word_sub stackpointer (word 624),632)] /\
        ALL (nonoverlapping (word pc,0x82a0))
         [(out,outlen); (word_sub stackpointer (word 624),632)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x3480) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; m; word(LENGTH inp)] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(m,LENGTH inp)) s =
                  num_of_bytelist inp)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> bytes(out,outlen)) s =
                  num_of_bytelist(list_of_seq (shake256 inp) outlen))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(out,outlen);
                memory :> bytes(word_sub stackpointer (word 624),624)])`,
  MAP_EVERY X_GEN_TAC
   [`out:int64`; `outlen:num`; `m:int64`; `inp:byte list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 624 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SHAKE256_SETUP_TAC THEN

  (*** The absorption, up to the test of outlen ***)

  ENSURES_SEQUENCE_TAC `pc + 0x34b2` SHAKE256_MID THEN CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (1--14) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SHAKE256_STATE_ADDRESS]) THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC [15] THEN
    SHAKE256_NORM_TAC THEN
    X86_SUBROUTINE_SIM_TAC
     (mlkem_native_libmlkem_gcc12_O2_mc,MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC,
      0x0,mlkem_native_libmlkem_gcc12_O2_mc,
      MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT)
     [`read RDI s`; `136`; `read RDX s`; `LENGTH(inp:byte list)`; `31`;
      `num_of_bytelist(inp:byte list)`; `pc:num`; `read RSP s`;
      `read (memory :> bytes64(read RSP s)) s`] 16 THEN
    SHAKE256_NORM_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** The case outlen = 0, with no output ***)

  ASM_CASES_TAC `outlen = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (1--13) THEN
    SHAKE256_NORM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[list_of_seq; num_of_bytelist; READ_MEMORY_BYTES_TRIVIAL];
    ALL_TAC] THEN

  (*** Otherwise the loop, with MIN outlen (136 * i) bytes done ***)

  SHAKE256_BOUND_TAC THEN
  ENSURES_WHILE_UP2_TAC `(outlen + 135) DIV 136` `pc + 0x34c0` `pc + 0x34eb`
   SHAKE256_INV THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[DIV_EQ_0; ARITH_EQ] THEN UNDISCH_TAC `~(outlen = 0)` THEN
    ARITH_TAC;

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (1--1) THEN
    SHAKE256_NONZERO_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (2--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ARITH_RULE `MIN n 0 = 0`; SUB_0; WORD_ADD_0;
                READ_MEMORY_BYTES_TRIVIAL; list_of_seq; num_of_bytelist;
                keccak_squeeze];

    (*** The loop body: permute and extract the next block ***)

    SHAKE256_ITERATION_TAC ALL_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (1--3) THEN
    SHAKE256_NORM_TAC THEN
    KECCAK_STATE_AT_TAC SHAKE256_ST THEN
    KECCAK_STATE_THEN SHAKE256_ST (fun v ->
      X86_SUBROUTINE_SIM_TAC
       (mlkem_native_libmlkem_gcc12_O2_mc,
        MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC,
        0x0,mlkem_native_libmlkem_gcc12_O2_mc,
      MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600)
       [`read RDI s`; v; `pc:num`; `read RSP s`;
        `read (memory :> bytes64(read RSP s)) s`] 4) THEN
    SHAKE256_NORM_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (5--8) THEN
    SHAKE256_LENGTH_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (9--12) THEN
    ARGS_32_TAC [`MIN (outlen - 136 * i) 136`] THEN
    SHAKE256_NORM_TAC THEN
    KECCAK_STATE_AT_TAC SHAKE256_ST THEN
    KECCAK_STATE_THEN SHAKE256_ST (fun v ->
      X86_SUBROUTINE_SIM_TAC
       (mlkem_native_libmlkem_gcc12_O2_mc,
        MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC,
        0x0,mlkem_native_libmlkem_gcc12_O2_mc,
      MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT)
       [`read RDI s`; `read RSI s`; `0`; `MIN (outlen - 136 * i) 136`; v;
        `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`]
       13) THEN
    SHAKE256_NORM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (14--15) THEN
    SHAKE256_COUNTER_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [COND_CASES_TAC THEN REWRITE_TAC[];
      AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD];
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
      REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[NUM_OF_BYTELIST_LIST_OF_SEQ_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[shake256] THEN CONV_TAC SYM_CONV THEN
      REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1] THEN
      REWRITE_TAC[GSYM(CONJUNCT2 keccak_squeeze); ADD1] THEN
      MATCH_MP_TAC KECCAK_SPONGE_BLOCK THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[GSYM ADD1; keccak_squeeze]];

    (*** Zeroing the state and the return ***)

    SHAKE256_EXIT_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (1--11) THEN
    SHAKE256_NORM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, for any input, with the events     *)
(* given in parts as for the AArch64 code.                                   *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let SHAKE256_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      ilist n THENL
     [ABSORB_EXISTS_E2_TAC (ref
       [`pc:num`; `m:int64`; `out:int64`; `outlen:num`; `inlen:num`;
        `stackpointer:int64`; `returnaddress:int64`; `i:num`]);
      LABEL_TAC name safety_th]);;

let SHAKE256_SAFE_MID =
 `\s. read R12 s = word outlen /\ read R13 s = out /\
      read R14 s =
      word_add stackpointer
       (word(360 - val(word_add stackpointer (word 584)) MOD 32)) /\
      read RBP s = word_add stackpointer (word 616) /\
      read RSP s =
      word_add stackpointer
       (word(360 - val(word_add stackpointer (word 584)) MOD 32)) /\
      read (memory :> bytes64 (word_add stackpointer (word 584))) s =
      rbx_init /\
      read (memory :> bytes64 (word_add stackpointer (word 592))) s =
      r12_init /\
      read (memory :> bytes64 (word_add stackpointer (word 600))) s =
      r13_init /\
      read (memory :> bytes64 (word_add stackpointer (word 608))) s =
      r14_init /\
      read (memory :> bytes64 (word_add stackpointer (word 616))) s =
      rbp_init /\
      read (memory :> bytes64 (word_add stackpointer (word 624))) s =
      returnaddress /\
      (read DF s <=> false)`;;

let SHAKE256_SAFE_INV =
 `\i s. read R12 s = word(outlen - MIN outlen (136 * i)) /\
        read R13 s = word_add out (word(MIN outlen (136 * i))) /\
        read R14 s =
        word_add stackpointer
         (word(360 - val(word_add stackpointer (word 584)) MOD 32)) /\
        read RBP s = word_add stackpointer (word 616) /\
        read RSP s =
        word_add stackpointer
         (word(360 - val(word_add stackpointer (word 584)) MOD 32)) /\
        read (memory :> bytes64 (word_add stackpointer (word 584))) s =
        rbx_init /\
        read (memory :> bytes64 (word_add stackpointer (word 592))) s =
        r12_init /\
        read (memory :> bytes64 (word_add stackpointer (word 600))) s =
        r13_init /\
        read (memory :> bytes64 (word_add stackpointer (word 608))) s =
        r14_init /\
        read (memory :> bytes64 (word_add stackpointer (word 616))) s =
        rbp_init /\
        read (memory :> bytes64 (word_add stackpointer (word 624))) s =
        returnaddress /\
        (read DF s <=> false)`;;

let MLKEM_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
     forall e out outlen m inlen pc stackpointer returnaddress.
       aligned 16 (word pc:int64) /\
       PAIRWISE nonoverlapping
        [out,outlen; m,inlen; word_sub stackpointer (word 624),632] /\
       ALL (nonoverlapping (word pc,0x82a0))
        [out,outlen; word_sub stackpointer (word 624),632]
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + 0x3480) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [out; word outlen; m; word inlen] s /\
                 (read DF s <=> false) /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m out outlen inlen pc
                           (word_sub stackpointer (word 624)) returnaddress /\
                    memaccess_inbounds e2
                     [m,inlen; out,outlen;
                      word_sub stackpointer (word 624),632;
                      word(pc + 0x80c0),192]
                     [out,outlen; word_sub stackpointer (word 624),624]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(out,outlen);
               memory :> bytes(word_sub stackpointer (word 624),624)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_ABSORB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_PERMUTE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_EXTRACT" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(m:int64) (out:int64) (outlen:num) (inlen:num) (pc:num)
      (stackpointer:int64) (returnaddress:int64).
      APPEND
       (if outlen = 0
        then f_ev_zero m out outlen inlen pc stackpointer returnaddress
        else APPEND
              (f_ev_epil m out outlen inlen pc stackpointer returnaddress)
              (APPEND
                (ENUMERATEL ((outlen + 135) DIV 136)
                  (\i. f_ev_loop m out outlen inlen pc stackpointer
                                 returnaddress i))
                (f_ev_prol m out outlen inlen pc stackpointer
                           returnaddress)))
       (f_ev_absorb m out outlen inlen pc stackpointer returnaddress)
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`out:int64`; `outlen:num`; `m:int64`; `inlen:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 624 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SHAKE256_SETUP_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x34b2` SHAKE256_SAFE_MID THEN
  CONJ_TAC THENL
   [REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (1--14) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SHAKE256_STATE_ADDRESS]) THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC [15] THEN
    SHAKE256_NORM_TAC THEN
    SHAKE256_SAFE_CALL_TAC "H_ABSORB"
     [`e:(uarch_event)list`; `read RDI s`; `136`; `read RDX s`; `inlen:num`;
      `31`; `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`]
     16 THEN
    SHAKE256_NORM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `outlen = 0` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (1--13) THEN
    SHAKE256_NORM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  SHAKE256_BOUND_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `(outlen + 135) DIV 136`
    `pc + 0x34c0` `pc + 0x34eb` SHAKE256_SAFE_INV THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[DIV_EQ_0; ARITH_EQ] THEN UNDISCH_TAC `~(outlen = 0)` THEN
    ARITH_TAC;

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (1--1) THEN
    SHAKE256_NONZERO_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (2--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ARITH_RULE `MIN n 0 = 0`; SUB_0; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    SHAKE256_ITERATION_TAC (REWRITE_TAC[]) THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (1--3) THEN
    SHAKE256_NORM_TAC THEN
    SHAKE256_SAFE_CALL_TAC "H_PERMUTE"
     [`e:(uarch_event)list`; `read RDI s`; `pc:num`; `read RSP s`;
      `read (memory :> bytes64(read RSP s)) s`] 4 THEN
    SHAKE256_NORM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (5--8) THEN
    SHAKE256_LENGTH_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (9--12) THEN
    ARGS_32_TAC [`MIN (outlen - 136 * i) 136`] THEN
    SHAKE256_NORM_TAC THEN
    SHAKE256_SAFE_CALL_TAC "H_EXTRACT"
     [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `0`;
      `MIN (outlen - 136 * i) 136`; `pc:num`; `read RSP s`;
      `read (memory :> bytes64(read RSP s)) s`] 13 THEN
    SHAKE256_NORM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (14--15) THEN
    SHAKE256_COUNTER_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    SHAKE256_EXIT_TAC THEN
    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (1--11) THEN
    SHAKE256_NORM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;
