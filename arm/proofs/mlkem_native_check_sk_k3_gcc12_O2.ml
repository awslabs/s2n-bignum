(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The hash check of an ML-KEM-768 decapsulation key. This is the code for   *)
(* mlkem768_check_sk from mlkem-native's portable C implementation compiled  *)
(* by gcc 12 with -O2 (see mlkem_native/README.md), which computes the       *)
(* SHA3-256 hash of the encapsulation key in the decapsulation key into a    *)
(* buffer on the stack, compares it in constant time with the hash stored in *)
(* the decapsulation key, and zeroes the buffer. It is verified in the whole *)
(* image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at address     *)
(* 0x5880, using the theorems for mlkem_sha3_256 at 0x2650 in the image.     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_sha3_256_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    5880: stp     x19, x20, [sp, #-96]!
    5884: mov     x20, x0
    5888: add     x1, x0, #0x480
    588c: adrp    x3, 1f000 <mlk_zetas+0x18c80>
    5890: ldr     x3, [x3, #4088]
    5894: str     x30, [sp, #16]
    5898: add     x19, sp, #0x3f
    589c: mov     x2, #0x4a0
    58a0: ldr     x4, [x3]
    58a4: str     x4, [sp, #88]
    58a8: mov     x4, #0x0
    58ac: and     x19, x19, #0xffffffffffffffe0
    58b0: mov     x0, x19
    58b4: bl      2650 <mlkem_sha3_256>
    58b8: ldp     q1, q3, [x19]
    58bc: ldr     q0, [x20, #2336]
    58c0: ldr     q2, [x20, #2352]
    58c4: eor     v0.16b, v0.16b, v1.16b
    58c8: movi    v1.4s, #0x0
    58cc: eor     v2.16b, v2.16b, v3.16b
    58d0: orr     v4.16b, v0.16b, v2.16b
    58d4: eor     v0.16b, v0.16b, v2.16b
    58d8: ext     v3.16b, v4.16b, v1.16b, #8
    58dc: ext     v2.16b, v0.16b, v1.16b, #8
    58e0: orr     v3.16b, v3.16b, v4.16b
    58e4: eor     v2.16b, v2.16b, v0.16b
    58e8: ext     v4.16b, v3.16b, v1.16b, #4
    58ec: ext     v0.16b, v2.16b, v1.16b, #4
    58f0: orr     v4.16b, v4.16b, v3.16b
    58f4: eor     v0.16b, v0.16b, v2.16b
    58f8: ext     v3.16b, v4.16b, v1.16b, #2
    58fc: ext     v2.16b, v0.16b, v1.16b, #2
    5900: orr     v3.16b, v3.16b, v4.16b
    5904: eor     v2.16b, v2.16b, v0.16b
    5908: ext     v0.16b, v3.16b, v1.16b, #1
    590c: ext     v1.16b, v2.16b, v1.16b, #1
    5910: orr     v0.16b, v0.16b, v3.16b
    5914: eor     v1.16b, v1.16b, v2.16b
    5918: umov    w1, v0.b[0]
    591c: umov    w2, v1.b[0]
    5920: neg     w1, w1
    5924: eor     w1, w2, w1, asr #16
    5928: cmp     w2, w1, uxtb
    592c: mov     w0, #0xfffffffb
    5930: csel    w0, wzr, w0, eq
    5934: stp     xzr, xzr, [x19]
    5938: stp     xzr, xzr, [x19, #16]
    593c: adrp    x1, 1f000 <mlk_zetas+0x18c80>
    5940: ldr     x1, [x1, #4088]
    5944: ldr     x3, [sp, #88]
    5948: ldr     x2, [x1]
    594c: subs    x3, x3, x2
    5950: mov     x2, #0x0
    5954: b.ne    5964 <mlkem768_check_sk+0xe4>
    5958: ldr     x30, [sp, #16]
    595c: ldp     x19, x20, [sp], #96
    5960: ret
    5964: bl      830 <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_CHECK_SK_K3_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x5880,0x5968];;

(* ------------------------------------------------------------------------- *)
(* The buffer for the hash is aligned to 32 bytes within the stack frame, so *)
(* its address depends on whether the stack pointer is a multiple of 32 or   *)
(* just of 16, and it is loaded as two 128-bit words, as is the stored hash. *)
(* ------------------------------------------------------------------------- *)

let CHECK_SK_ALIGNED_16_32 = prove
 (`(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`,
  CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[aligned; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`x:int64`; `4`] (CONJUNCT1 WORD_AND_MASK_WORD));
    MP_TAC(ISPECL [`x:int64`; `5`] (CONJUNCT1 WORD_AND_MASK_WORD))] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIVIDES_MOD; GSYM VAL_EQ_0; VAL_WORD; DIMINDEX_64] THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x MOD 16 < 16`; ARITH_RULE `x MOD 32 < 32`;
           ARITH_RULE `x < 16 ==> x < 2 EXP 64`;
           ARITH_RULE `x < 32 ==> x < 2 EXP 64`]);;

let CHECK_SK_BUFFER_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 559)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 544 else 528))`,
  REWRITE_TAC[CHECK_SK_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let CHECK_SK_BUFFER = `word_add (stackpointer:int64)
                        (word(if aligned 32 stackpointer then 544 else 528))`;;

let CHECK_SK_BUFFER_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 559))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word(if aligned 32 stackpointer then 544 else 528))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC CHECK_SK_BUFFER_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;

let READ_MEMORY_BYTES128_HALVES = prove
 (`!a:int64 n s:armstate.
        read (memory :> bytes(a,32)) s = n
        ==> read (memory :> bytes128 a) s = word(n MOD 2 EXP 128) /\
            read (memory :> bytes128(word_add a (word 16))) s =
            word(n DIV 2 EXP 128)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `340282366920938463463374607431768211456 =
                          2 EXP (8 * 16)`; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The comparison of the two hashes, as two 128-bit words each, which ORs    *)
(* together the bytes of their XOR (also XORing them, which does not affect  *)
(* the result), and the result of the function from it.                      *)
(* ------------------------------------------------------------------------- *)

let CHECK_SK_EQ = prove
 (`!h n. h < 2 EXP 256 /\ n < 2 EXP 256
         ==> (h = n <=>
              word(n MOD 2 EXP 128):int128 = word(h MOD 2 EXP 128) /\
              word(n DIV 2 EXP 128):int128 = word(h DIV 2 EXP 128))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_128; MOD_MOD_REFL] THEN
  SUBGOAL_THEN `n DIV 2 EXP 128 < 2 EXP 128 /\ h DIV 2 EXP 128 < 2 EXP 128`
   (fun th -> SIMP_TAC[th; MOD_LT]) THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD;
                 ARITH_RULE `128 + 128 = 256`];
    ALL_TAC] THEN
  EQ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
  MESON_TAC[DIVISION_SIMP]);;

let READ_MEMORY_BYTES_32_BOUND = prove
 (`!a n s:armstate.
        read (memory :> bytes(a,32)) s = n ==> n < 2 EXP 256`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; ARITH_RULE `256 = 8 * 32`;
              READ_BYTES_BOUND]);;

let CHECK_SK_RESULT = prove
 (`!c c'. (c <=> c')
          ==> word_zx (if c then word 0 else word 4294967291:int32):int64 =
              (if c' then word 0 else word 4294967291)`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV);;

(*** The comparison, with the four 128-bit words as hl, hh, nl and nh ***)

let CHECK_SK_EXPAND_TAC v =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Const("word",_),_)),r) when r = v ->
        SUBST1_TAC(SYM th)
    | _ -> NO_TAC);;

let CHECK_SK_COMPARE_TAC =
  MATCH_MP_TAC CHECK_SK_RESULT THEN
  SUBGOAL_THEN
   `h = num_of_bytelist(sha3_256 ek) <=>
    (nl:int128) = hl /\ (nh:int128) = hh`
  SUBST1_TAC THENL
   [MAP_EVERY CHECK_SK_EXPAND_TAC
     [`nl:int128`; `nh:int128`; `hl:int128`; `hh:int128`] THEN
    MATCH_MP_TAC CHECK_SK_EQ THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((nl:int128) = hl /\ (nh:int128) = hh) <=>
    (word_xor nl hl = word 0 /\ word_xor nh hh = word 0)`
  SUBST1_TAC THENL [REWRITE_TAC[WORD_XOR_EQ_0]; ALL_TAC] THEN
  SPEC_TAC(`word_xor nh hh:int128`,`y:int128`) THEN
  SPEC_TAC(`word_xor nl hl:int128`,`x:int128`) THEN REPEAT GEN_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The decapsulation key of 2400 bytes at sk contains the *)
(* encapsulation key of 1184 bytes at offset 1152, given as a list of bytes  *)
(* ek, and its hash h at offset 2336, as a number. The result is 0 if h is   *)
(* the SHA3-256 hash of ek, as in common/fips202.ml, and -5 otherwise. The   *)
(* stack guard is handled as for mlkem_sha3_256, and the stack is the 96     *)
(* bytes of the function and the 496 used by mlkem_sha3_256 below them.      *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SHA3_256_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,MLKEM_NATIVE_CHECK_SK_K3_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHA3_256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

(*** The setup for both proofs, with bounds on the offset of the buffer ***)

let CHECK_SK_SETUP_TAC =
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 592):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `528 <= (if aligned 32 (stackpointer:int64) then 544 else 528) /\
    (if aligned 32 (stackpointer:int64) then 544 else 528) <= 544`
  STRIP_ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `0x1fff8`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `0x1fff8`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20`;;

(*** The GOT entry in the form in the precondition of mlkem_sha3_256 ***)

let CHECK_SK_GOT_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes64 (word_add (word pc) (word 131064))) s = g`)
         (concl th)
    then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else NO_TAC);;

(*** A 32-byte value as two 128-bit words, named by l and h ***)

let CHECK_SK_HALVES_TAC a v l h =
  FIRST_ASSUM(fun th ->
    if can (term_match [] (subst [a,`a:int64`; v,`v:num`]
             `read (memory :> bytes(a,32)) s = v`)) (concl th)
    then ASSUME_TAC(MATCH_MP READ_MEMORY_BYTES_32_BOUND th) THEN
         MP_TAC(CONV_RULE(ONCE_DEPTH_CONV(REWRITE_CONV
                  [GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THENC
                  DEPTH_CONV NUM_ADD_CONV))
                  (MATCH_MP READ_MEMORY_BYTES128_HALVES th)) THEN
         ABBREV_TAC(mk_eq(mk_var(l,`:int128`),
                    mk_comb(`word:num->int128`,
                     mk_binop `MOD` v `2 EXP 128`))) THEN
         ABBREV_TAC(mk_eq(mk_var(h,`:int128`),
                    mk_comb(`word:num->int128`,
                     mk_binop `DIV` v `2 EXP 128`))) THEN
         STRIP_TAC
    else NO_TAC);;

let MLKEM_NATIVE_CHECK_SK_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!sk (ek:byte list) h guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH ek = 1184 /\
        nonoverlapping (sk,2400) (word_sub stackpointer (word 592),592) /\
        ALLPAIRS nonoverlapping
         [(word_sub stackpointer (word 592),592)]
         [(word pc,0x6480); (word(pc + 0x1fff8),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x5880) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [sk] s /\
                  read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                  read (memory :> bytes(word_add sk (word 1152),1184)) s =
                  num_of_bytelist ek /\
                  read (memory :> bytes(word_add sk (word 2336),32)) s = h)
             (\s. read PC s = returnaddress /\
                  C_RETURN s =
                  (if h = num_of_bytelist(sha3_256 ek) then word 0
                   else word 0xfffffffb))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(word_sub stackpointer (word 592),592)])`,
  MAP_EVERY X_GEN_TAC
   [`sk:int64`; `ek:byte list`; `h:num`; `guard:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 592 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  CHECK_SK_SETUP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  CHECK_SK_HALVES_TAC `word_add (sk:int64) (word 2336)` `h:num` "hl" "hh" THEN

  (*** Saving the registers and the stack guard, and the hash ***)

  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K3_GCC12_O2_EXEC (1--4) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K3_GCC12_O2_EXEC (5--12) THEN
  CHECK_SK_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K3_GCC12_O2_EXEC (13--14) THEN
  CHECK_SK_GOT_TAC THEN
  LOCAL_SHA3_256_TAC
   [`read X0 s`; `read X1 s`; `ek:byte list`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 15 THEN

  (*** The comparison and the zeroing of the buffer ***)

  CHECK_SK_HALVES_TAC CHECK_SK_BUFFER `num_of_bytelist(sha3_256 ek)`
    "nl" "nh" THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K3_GCC12_O2_EXEC [k] THEN
    SIMD_SIMPLIFY_TAC[]) (16--45) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K3_GCC12_O2_EXEC [46] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K3_GCC12_O2_EXEC (47--49) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K3_GCC12_O2_EXEC (50--58) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CHECK_SK_COMPARE_TAC);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. As for mlkem_sha3_256, it is       *)
(* stated directly, since the events depend on the address of the stack      *)
(* guard, read from the GOT. They do not depend on the keys.                 *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_CHECK_SK_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
     forall e sk guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       nonoverlapping (sk,2400) (word_sub stackpointer (word 592),592) /\
       ALLPAIRS nonoverlapping
        [word_sub stackpointer (word 592),592]
        [word pc,0x6480; word(pc + 0x1fff8),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read PC s = word (pc + 0x5880) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [sk] s /\
                 read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events sk guard pc
                           (word_sub stackpointer (word 592)) returnaddress /\
                    memaccess_inbounds e2
                     [word_add sk (word 1152),1184;
                      word_add sk (word 2336),32;
                      word_sub stackpointer (word 592),592;
                      word(pc + 0x1fff8),8; guard,8; word(pc + 0x62b0),192]
                     [word_sub stackpointer (word 592),592]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(word_sub stackpointer (word 592),592)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHA3_256_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_SHA3_256" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  CHECK_SK_SETUP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K3_GCC12_O2_EXEC (1--4) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K3_GCC12_O2_EXEC (5--12) THEN
  CHECK_SK_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K3_GCC12_O2_EXEC (13--14) THEN
  CHECK_SK_GOT_TAC THEN
  REMOVE_THEN "H_SHA3_256" (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_CHECK_SK_K3_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `1184`;
       `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 15 THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `sk:int64`; `guard:int64`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC "H_SHA3_256" safety_th]) THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K3_GCC12_O2_EXEC [k] THEN
    SIMD_SIMPLIFY_TAC[]) (16--45) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K3_GCC12_O2_EXEC [46] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K3_GCC12_O2_EXEC (47--49) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_CHECK_SK_K3_GCC12_O2_EXEC (50--58) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
