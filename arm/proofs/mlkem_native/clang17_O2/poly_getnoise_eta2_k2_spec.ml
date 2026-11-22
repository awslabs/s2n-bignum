(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of a noise polynomial with eta = 2 from a seed and a nonce. This *)
(* is the code for mlkem512_poly_getnoise_eta2 from mlkem-native's portable  *)
(* C implementation compiled by clang 17 with -O2 (see                       *)
(* mlkem_native/README.md), which computes 128 bytes of SHAKE256 of the seed *)
(* and the nonce into a buffer on the stack, applies mlkem_poly_cbd2 to them *)
(* and zeroes the buffer. It is verified in the whole image (see             *)
(* libmlkem.ml), using the theorems for mlkem_shake256 and mlkem_poly_cbd2   *)
(* in the image.                                                             *)
(*                                                                           *)
(* The buffers are aligned to 32 bytes within the stack frame, which the     *)
(* code makes by rounding the stack pointer down, so the proof is by cases   *)
(* on whether the incoming stack pointer is a multiple of 32. The zeroing is *)
(* inline stores and has no call of memset.                                  *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/shake256_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/poly_cbd2_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem512_poly_getnoise_eta2:
       +0x0: stp     x29, x30, [sp, #-48]!
       +0x4: stp     x28, x21, [sp, #16]
       +0x8: stp     x20, x19, [sp, #32]
       +0xc: mov     x29, sp
      +0x10: sub     x9, sp, #0xd0
      +0x14: and     sp, x9, #0xffffffffffffffe0
      +0x18: adrp    x8, <page>
      +0x1c: mov     x19, x0
      +0x20: add     x0, sp, #0x40
      +0x24: mov     w3, #0x21
      +0x28: add     x20, sp, #0x40
      +0x2c: mov     x21, sp
      +0x30: ldr     x8, [x8, #4088]  // got_stack_chk_guard
      +0x34: ldr     x8, [x8]
      +0x38: str     x8, [sp, #200]
      +0x3c: ldp     q0, q1, [x1]
      +0x40: strb    w2, [sp, #32]
      +0x44: mov     x2, sp
      +0x48: mov     w1, #0x80
      +0x4c: stp     q0, q1, [sp]
      +0x50: bl      <mlkem_shake256>
      +0x54: add     x1, sp, #0x40
      +0x58: mov     x0, x19
      +0x5c: bl      <mlkem_poly_cbd2>
      +0x60: movi    v0.2d, #0x0
      +0x64: adrp    x8, <page>
      +0x68: stp     q0, q0, [sp, #64]
      +0x6c: stp     q0, q0, [sp, #96]
      +0x70: stp     q0, q0, [sp, #128]
      +0x74: stp     q0, q0, [sp, #160]
      +0x78: strb    wzr, [sp, #32]
      +0x7c: stp     q0, q0, [sp]
      +0x80: ldr     x8, [x8, #4088]  // got_stack_chk_guard
      +0x84: ldr     x9, [sp, #200]
      +0x88: ldr     x8, [x8]
      +0x8c: cmp     x8, x9
      +0x90: b.ne    <mlkem512_poly_getnoise_eta2+0xa8>
      +0x94: mov     sp, x29
      +0x98: ldp     x20, x19, [sp, #32]
      +0x9c: ldp     x28, x21, [sp, #16]
      +0xa0: ldp     x29, x30, [sp], #48
      +0xa4: ret
      +0xa8: bl      __stack_chk_fail
 ***)

let MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_CLANG17_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O2_mc
   [layout_range "mlkem512_poly_getnoise_eta2"];;

(* ------------------------------------------------------------------------- *)
(* The buffer for the input of SHAKE256, the seed and the nonce, is aligned  *)
(* to 32 bytes within the stack frame and followed by the one for its        *)
(* output, so its address depends on whether the stack pointer is a multiple *)
(* of 32 or just of 16. The seed is copied there as two 128-bit words.       *)
(* ------------------------------------------------------------------------- *)

let GETNOISE_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 640)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 640 else 624))`;;

let GETNOISE_BUFFER_ADDRESS = assume_spec GETNOISE_BUFFER_ADDRESS_STMT;;

let GETNOISE_BUFFER_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 640))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word(if aligned 32 stackpointer then 640 else 624))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC GETNOISE_BUFFER_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;

let GETNOISE_BUFFER = `word_add (stackpointer:int64)
                        (word(if aligned 32 stackpointer then 640 else 624))`;;

let READ_MEMORY_BYTES128_HALVES_STMT =
  `!a:int64 n s:armstate.
        read (memory :> bytes(a,32)) s = n
        ==> read (memory :> bytes128 a) s = word(n MOD 2 EXP 128) /\
            read (memory :> bytes128(word_add a (word 16))) s =
            word(n DIV 2 EXP 128)`;;

let READ_MEMORY_BYTES128_HALVES =
  assume_spec READ_MEMORY_BYTES128_HALVES_STMT;;

let READ_MEMORY_BYTES_32_OF_HALVES_STMT =
  `!a:int64 n s:armstate.
        n < 2 EXP 256 /\
        read (memory :> bytes128 a) s = word(n MOD 2 EXP 128) /\
        read (memory :> bytes128(word_add a (word 16))) s =
        word(n DIV 2 EXP 128)
        ==> read (memory :> bytes(a,32)) s = n`;;

let READ_MEMORY_BYTES_32_OF_HALVES =
  assume_spec READ_MEMORY_BYTES_32_OF_HALVES_STMT;;

(*** The offsets of addresses in the buffer as single numbers ***)

let GETNOISE_ADDRESS_CONV =
  REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THENC
  DEPTH_CONV NUM_ADD_CONV;;

let GETNOISE_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE GETNOISE_ADDRESS_CONV th else th);;

(*** The 33 bytes of the input to SHAKE256 from the seed and the nonce ***)

let GETNOISE_INPUT_STMT =
  `!a:int64 (sd:byte list) b s:armstate.
        LENGTH sd = 32 /\
        read (memory :> bytes(a,32)) s = num_of_bytelist sd /\
        read (memory :> bytes8(word_add a (word 32))) s = b
        ==> LENGTH(APPEND sd [b]) = 33 /\
            read (memory :> bytes(a,33)) s = num_of_bytelist(APPEND sd [b])`;;

let GETNOISE_INPUT = assume_spec GETNOISE_INPUT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The seed is 32 bytes at seed, given as a list of bytes *)
(* sd, and the nonce is the low byte of the third argument. As for PRF and   *)
(* SamplePolyCBD with eta = 2 in FIPS 203, the result is the centered        *)
(* binomial distribution of mlkem_poly_cbd2 applied to the first 128 bytes   *)
(* of shake256 of the seed followed by the nonce, as in                      *)
(* common/fips202/fips202.ml. The stack guard is handled as for              *)
(* mlkem_poly_compress_d4, and the stack is the 48 bytes of saved registers, *)
(* 208 bytes of the buffers and the canary, up to 16 bytes of padding for    *)
(* the alignment, and the 624 used by mlkem_shake256 below them.             *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SHAKE256_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_CLANG17_O2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_SHAKE256_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_CBD2_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_CLANG17_O2_EXEC,
    0x0,mlkem_native_libmlkem_clang17_O2_mc,
    MLKEM_NATIVE_POLY_CBD2_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT);;

(*** The GOT entry in the form in the precondition of mlkem_shake256 ***)

let GETNOISE_GOT_TAC =
  W(fun (asl,_) ->
    MAP_EVERY (fun (_,th) ->
      if can (term_match []
        `read (memory :> bytes64 (word_add (word pc) (word n))) s = g`)
        (concl th)
      then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else ALL_TAC) asl);;

(*** The setup for both proofs, with bounds on the offset of the buffer ***)

let GETNOISE_SETUP_TAC =
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 896):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `624 <= (if aligned 32 (stackpointer:int64) then 640 else 624) /\
    (if aligned 32 (stackpointer:int64) then 640 else 624) <= 640`
  STRIP_ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `aligned 16 (word_add (stackpointer:int64)
                         (word(if aligned 32 stackpointer then 640 else 624)))`
  ASSUME_TAC THENL
   [COND_CASES_TAC THEN CONV_TAC NORMALIZE_ALIGNED_WORD_CONV THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `word_sub (word (if aligned 32 (stackpointer:int64) then 640 else 624))
             (word 624):int64 =
    word((if aligned 32 stackpointer then 640 else 624) - 624)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WORD_SUB2 THEN COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x28_init" `X28` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29`;;

(*** The region below the buffers for the callee, in the form word(x - 624) ***)

let GETNOISE_FIX_TAC =
  RULE_ASSUM_TAC(fun th ->
    if maychange_term (concl th)
    then REWRITE_RULE[ASSUME
     `word_sub (word (if aligned 32 (stackpointer:int64) then 640 else 624))
               (word 624):int64 =
      word((if aligned 32 stackpointer then 640 else 624) - 624)`] th
    else th);;

let MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r seed (sd:byte list) nonce guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH sd = 32 /\
        PAIRWISE nonoverlapping
         [(r,512); (seed,32); (word_sub stackpointer (word 896),896)] /\
        ALLPAIRS nonoverlapping
         [(r,512); (word_sub stackpointer (word 896),896)]
         [(word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O2_mc /\
                  read PC s = word (pc + mlkem512_poly_getnoise_eta2) /\
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
                memory :> bytes(word_sub stackpointer (word 896),896)])`;;

let MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly as for             *)
(* mlkem_poly_compress_d4. The events do not depend on the nonce.            *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let GETNOISE_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O2_mc,
       MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_CLANG17_O2_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O2_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `r:int64`; `seed:int64`; `guard:int64`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC name safety_th]);;

let MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e r seed nonce guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [r,512; seed,32; word_sub stackpointer (word 896),896] /\
       ALLPAIRS nonoverlapping
        [r,512; word_sub stackpointer (word 896),896]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_clang17_O2_mc /\
                 read PC s = word (pc + mlkem512_poly_getnoise_eta2) /\
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
                           (word_sub stackpointer (word 896)) returnaddress /\
                    memaccess_inbounds e2
                     [seed,32; r,512; word_sub stackpointer (word 896),896;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                      word(pc + mlkem_poly_cbd2_consts),
                      mlkem_poly_cbd2_consts_size]
                     [r,512; word_sub stackpointer (word 896),896]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(r,512);
               memory :> bytes(word_sub stackpointer (word 896),896)])`;;

let MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_CLANG17_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
