(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of a noise polynomial with eta = 2 from a seed and a nonce. This *)
(* is the code for mlkem1024_poly_getnoise_eta2 from mlkem-native's portable *)
(* C implementation compiled by gcc 12 with -O2 (see                         *)
(* mlkem_native/README.md), which computes 128 bytes of SHAKE256 of the seed *)
(* and the nonce into a buffer on the stack, applies mlkem_poly_cbd2 to them *)
(* and zeroes the buffer. It is verified in the whole image (see             *)
(* libmlkem.ml), using the theorems for mlkem_shake256                       *)
(* and mlkem_poly_cbd2 in the image.                                         *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/gcc12_O2/shake256_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/poly_cbd2_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem1024_poly_getnoise_eta2:
       +0x0: stp     x19, x20, [sp, #-240]!
       +0x4: mov     x3, #0x21
       +0x8: add     x19, sp, #0x3f
       +0xc: stp     x21, x30, [sp, #16]
      +0x10: and     x19, x19, #0xffffffffffffffe0
      +0x14: adrp    x4, <page>
      +0x18: ldr     x4, [x4, #4088]  // got_stack_chk_guard
      +0x1c: add     x20, x19, #0x80
      +0x20: ldp     q0, q1, [x1]
      +0x24: mov     x21, x0
      +0x28: ldr     x0, [x4]
      +0x2c: str     x0, [sp, #232]
      +0x30: mov     x0, #0x0
      +0x34: strb    w2, [x20, #32]
      +0x38: mov     x2, x20
      +0x3c: mov     x0, x19
      +0x40: mov     x1, #0x80
      +0x44: stp     q0, q1, [x20]
      +0x48: bl      <mlkem_shake256>
      +0x4c: mov     x1, x19
      +0x50: mov     x0, x21
      +0x54: bl      <mlkem_poly_cbd2>
      +0x58: movi    v0.4s, #0x0
      +0x5c: stp     q0, q0, [x19]
      +0x60: stp     q0, q0, [x19, #32]
      +0x64: stp     q0, q0, [x19, #64]
      +0x68: stp     q0, q0, [x19, #96]
      +0x6c: stp     xzr, xzr, [x19, #128]
      +0x70: stp     xzr, xzr, [x20, #16]
      +0x74: strb    wzr, [x20, #32]
      +0x78: adrp    x0, <page>
      +0x7c: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0x80: ldr     x2, [sp, #232]
      +0x84: ldr     x1, [x0]
      +0x88: subs    x2, x2, x1
      +0x8c: mov     x1, #0x0
      +0x90: b.ne    <mlkem1024_poly_getnoise_eta2+0xa0>
      +0x94: ldp     x21, x30, [sp, #16]
      +0x98: ldp     x19, x20, [sp], #240
      +0x9c: ret
      +0xa0: bl      <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_POLY_GETNOISE_ETA2_K4_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [layout_range "mlkem1024_poly_getnoise_eta2"];;

(* ------------------------------------------------------------------------- *)
(* The buffer for the output of SHAKE256, followed by the one for its input, *)
(* the seed and the nonce, is aligned to 32 bytes within the stack frame, so *)
(* its address depends on whether the stack pointer is a multiple of 32 or   *)
(* just of 16. The seed is copied there as two 128-bit words.                *)
(* ------------------------------------------------------------------------- *)

let GETNOISE_BUFFER_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 623)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 608 else 592))`,
  REWRITE_TAC[ALIGNED_16_32_WORD_AND] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let GETNOISE_BUFFER = `word_add (stackpointer:int64)
                        (word(if aligned 32 stackpointer then 608 else 592))`;;

let GETNOISE_INPUT_BUFFER =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,GETNOISE_BUFFER),
          `word 128:int64`);;

let GETNOISE_BUFFER_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 623))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word(if aligned 32 stackpointer then 608 else 592))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC GETNOISE_BUFFER_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;

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

let READ_MEMORY_BYTES_32_OF_HALVES = prove
 (`!a:int64 n s:armstate.
        n < 2 EXP 256 /\
        read (memory :> bytes128 a) s = word(n MOD 2 EXP 128) /\
        read (memory :> bytes128(word_add a (word 16))) s =
        word(n DIV 2 EXP 128)
        ==> read (memory :> bytes(a,32)) s = n`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `32 = 16 + 16`; READ_BYTES_COMBINE] THEN
  MP_TAC(ISPECL [`a:int64`; `16`; `read memory s`] READ_BYTES_BOUND) THEN
  MP_TAC(ISPECL [`word_add a (word 16):int64`; `16`; `read memory s`]
                READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `n DIV 340282366920938463463374607431768211456 <
                340282366920938463463374607431768211456`
   (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL
   [UNDISCH_TAC `n < 2 EXP 256` THEN SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    MESON_TAC[DIVISION_SIMP; ADD_SYM; MULT_SYM]]);;

(*** The offsets of addresses in the buffer as single numbers ***)

let GETNOISE_ADDRESS_CONV =
  REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THENC
  DEPTH_CONV NUM_ADD_CONV;;

let GETNOISE_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE GETNOISE_ADDRESS_CONV th else th);;

(*** The 33 bytes of the input to SHAKE256 from the seed and the nonce ***)

let GETNOISE_INPUT = prove
 (`!a:int64 (sd:byte list) b s:armstate.
        LENGTH sd = 32 /\
        read (memory :> bytes(a,32)) s = num_of_bytelist sd /\
        read (memory :> bytes8(word_add a (word 32))) s = b
        ==> LENGTH(APPEND sd [b]) = 33 /\
            read (memory :> bytes(a,33)) s = num_of_bytelist(APPEND sd [b])`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; NUM_OF_BYTELIST_APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `33 = 32 + 1`; READ_MEMORY_BYTES_SNOC] THEN
  ASM_REWRITE_TAC[num_of_bytelist] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The seed is 32 bytes at seed, given as a list of bytes *)
(* sd, and the nonce is the low byte of the third argument. As for PRF and   *)
(* SamplePolyCBD with eta = 2 in FIPS 203, the result is the centered        *)
(* binomial distribution of mlkem_poly_cbd2 applied to the first 128 bytes   *)
(* of shake256 of the seed followed by the nonce, as in common/fips202.ml.   *)
(* The stack guard is handled as for mlkem_poly_compress_d4, and the stack   *)
(* is the 240 bytes of the function and the 560 used by mlkem_shake256 below *)
(* them.                                                                     *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SHAKE256_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_GETNOISE_ETA2_K4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_CBD2_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_GETNOISE_ETA2_K4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

(*** The GOT entry in the form in the precondition of mlkem_shake256 ***)

let GETNOISE_GOT_TAC =
  TRY(FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes64 (word_add (word pc) (word 131064))) s = g`)
         (concl th)
    then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else NO_TAC));;

(*** The setup for both proofs, with bounds on the offset of the buffer ***)

let GETNOISE_SETUP_TAC =
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 800):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `592 <= (if aligned 32 (stackpointer:int64) then 608 else 592) /\
    (if aligned 32 (stackpointer:int64) then 608 else 592) <= 608`
  STRIP_ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21`;;

let MLKEM_NATIVE_POLY_GETNOISE_ETA2_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!r seed (sd:byte list) nonce guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH sd = 32 /\
        PAIRWISE nonoverlapping
         [(r,512); (seed,32); (word_sub stackpointer (word 800),800)] /\
        ALLPAIRS nonoverlapping
         [(r,512); (word_sub stackpointer (word 800),800)]
         [(word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + mlkem1024_poly_getnoise_eta2) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; seed; nonce] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes(seed,32)) s = num_of_bytelist sd)
             (\s. read PC s = returnaddress /\
                  let n = num_of_bytelist
                           (list_of_seq
                             (shake256 (APPEND sd [word_zx nonce])) 128) in
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(&((n DIV 2 EXP (4 * i)) MOD 2 +
                                  (n DIV 2 EXP (4 * i + 1)) MOD 2) -
                                &((n DIV 2 EXP (4 * i + 2)) MOD 2 +
                                  (n DIV 2 EXP (4 * i + 3)) MOD 2)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(r,512);
                memory :> bytes(word_sub stackpointer (word 800),800)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `seed:int64`; `sd:byte list`; `nonce:int64`; `guard:int64`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 800 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  GETNOISE_SETUP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP READ_MEMORY_BYTES128_HALVES o check
    (can (term_match [] `read (memory :> bytes(seed,32)) s = n`) o concl)) THEN
  STRIP_TAC THEN

  (*** The input to SHAKE256, the seed and the nonce, in the buffer ***)

  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA2_K4_GCC12_O2_EXEC (1--5) THEN
  GETNOISE_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA2_K4_GCC12_O2_EXEC (6--6) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA2_K4_GCC12_O2_EXEC (7--18) THEN
  MP_TAC(SPECL [GETNOISE_INPUT_BUFFER;
                `num_of_bytelist(sd:byte list)`; `s18:armstate`]
               READ_MEMORY_BYTES_32_OF_HALVES) THEN
  ANTS_TAC THENL
   [CONV_TAC(GETNOISE_ADDRESS_CONV THENC NUM_REDUCE_CONV) THEN
    RULE_ASSUM_TAC(CONV_RULE GETNOISE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `sd:byte list` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    DISCH_TAC] THEN
  MP_TAC(SPECL [GETNOISE_INPUT_BUFFER;
                `sd:byte list`; `word_zx(nonce:int64):byte`; `s18:armstate`]
               GETNOISE_INPUT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC GETNOISE_ADDRESS_CONV THEN
    RULE_ASSUM_TAC(CONV_RULE GETNOISE_ADDRESS_CONV) THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [] `read (memory :> bytes8 a) s = x`) (concl th)
      then REWRITE_TAC[th] else NO_TAC) THEN
    CONV_TAC WORD_BLAST;
    STRIP_TAC] THEN
  GETNOISE_NORMALIZE_TAC THEN

  (*** The calls ***)

  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA2_K4_GCC12_O2_EXEC (19--19) THEN
  GETNOISE_GOT_TAC THEN
  LOCAL_SHAKE256_TAC
   [`read X0 s`; `128`; `read X2 s`;
    `APPEND (sd:byte list) [word_zx(nonce:int64)]`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 20 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA2_K4_GCC12_O2_EXEC (21--23) THEN
  LOCAL_CBD2_TAC
   [`read X0 s`; `read X1 s`;
    `num_of_bytelist(list_of_seq
       (shake256(APPEND (sd:byte list) [word_zx(nonce:int64)])) 128)`;
    `pc:num`; `read X30 s`] 24 THEN

  (*** Zeroing the buffer, the check of the stack guard and the return ***)

  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA2_K4_GCC12_O2_EXEC (25--33) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA2_K4_GCC12_O2_EXEC (34--42) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly as for             *)
(* mlkem_poly_compress_d4. The events do not depend on the nonce.            *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let GETNOISE_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLY_GETNOISE_ETA2_K4_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `r:int64`; `seed:int64`; `guard:int64`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC name safety_th]);;

let MLKEM_NATIVE_POLY_GETNOISE_ETA2_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
     forall e r seed nonce guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [r,512; seed,32; word_sub stackpointer (word 800),800] /\
       ALLPAIRS nonoverlapping
        [r,512; word_sub stackpointer (word 800),800]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read PC s = word (pc + mlkem1024_poly_getnoise_eta2) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [r; seed; nonce] s /\
                 read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                   guard /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events seed r guard pc
                           (word_sub stackpointer (word 800)) returnaddress /\
                    memaccess_inbounds e2
                     [seed,32; r,512; word_sub stackpointer (word 800),800;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                      word(pc + mlkem_poly_cbd2_consts),64]
                     [r,512; word_sub stackpointer (word 800),800]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(r,512);
               memory :> bytes(word_sub stackpointer (word 800),800)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_SHAKE256" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_CBD2" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  GETNOISE_SETUP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA2_K4_GCC12_O2_EXEC (1--5) THEN
  GETNOISE_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA2_K4_GCC12_O2_EXEC (6--6) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA2_K4_GCC12_O2_EXEC (7--19) THEN
  GETNOISE_GOT_TAC THEN GETNOISE_NORMALIZE_TAC THEN
  GETNOISE_SAFE_CALL_TAC "H_SHAKE256"
   [`e:(uarch_event)list`; `read X0 s`; `128`; `read X2 s`; `33`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 20 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA2_K4_GCC12_O2_EXEC (21--23) THEN
  GETNOISE_SAFE_CALL_TAC "H_CBD2"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `pc:num`;
    `read X30 s`] 24 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA2_K4_GCC12_O2_EXEC (25--33) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_GETNOISE_ETA2_K4_GCC12_O2_EXEC (34--42) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
