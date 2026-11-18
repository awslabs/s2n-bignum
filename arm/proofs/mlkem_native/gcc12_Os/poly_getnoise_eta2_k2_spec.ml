(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of a noise polynomial with eta = 2 from a seed and a nonce. This *)
(* is the code for mlkem512_poly_getnoise_eta2 from mlkem-native's portable  *)
(* C implementation compiled by gcc 12 with -Os (see                         *)
(* mlkem_native/README.md), which computes 128 bytes of SHAKE256 of the seed *)
(* and the nonce into a buffer on the stack, applies mlkem_poly_cbd2 to them *)
(* and zeroes the buffer and the input with mlk_zeroize_6, which calls       *)
(* memset. It is verified in the whole image (see libmlkem.ml), using the    *)
(* theorems for mlkem_shake256, mlkem_poly_cbd2 and mlk_zeroize_6 in the     *)
(* image and assuming the contract for memset in                             *)
(* utils/mlkem_native_libc.ml.                                               *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/shake256_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/poly_cbd2_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/zeroize_6_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/libmlkem.ml";;

(*** The code in the image:

    mlkem512_poly_getnoise_eta2:
       +0x0: stp     x19, x20, [sp, #-240]!
       +0x4: add     x19, sp, #0x3f
       +0x8: stp     x21, x30, [sp, #16]
       +0xc: and     x19, x19, #0xffffffffffffffe0
      +0x10: add     x20, x19, #0x80
      +0x14: mov     x21, x0
      +0x18: adrp    x0, <page>
      +0x1c: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0x20: ldp     q0, q1, [x1]
      +0x24: ldr     x3, [x0]
      +0x28: str     x3, [sp, #232]
      +0x2c: mov     x3, #0x0
      +0x30: strb    w2, [x20, #32]
      +0x34: mov     x2, x20
      +0x38: mov     x3, #0x21
      +0x3c: mov     x0, x19
      +0x40: mov     x1, #0x80
      +0x44: stp     q0, q1, [x20]
      +0x48: bl      <mlkem_shake256>
      +0x4c: mov     x1, x19
      +0x50: mov     x0, x21
      +0x54: bl      <mlkem_poly_cbd2>
      +0x58: mov     x0, x19
      +0x5c: mov     x1, #0x80
      +0x60: bl      <mlk_zeroize_6>
      +0x64: mov     x0, x20
      +0x68: mov     x1, #0x21
      +0x6c: bl      <mlk_zeroize_6>
      +0x70: adrp    x0, <page>
      +0x74: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0x78: ldr     x2, [sp, #232]
      +0x7c: ldr     x1, [x0]
      +0x80: subs    x2, x2, x1
      +0x84: mov     x1, #0x0
      +0x88: b.eq    <mlkem512_poly_getnoise_eta2+0x90>
      +0x8c: bl      <__stack_chk_fail@plt>
      +0x90: ldp     x21, x30, [sp, #16]
      +0x94: ldp     x19, x20, [sp], #240
      +0x98: ret
 ***)

let MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlkem512_poly_getnoise_eta2"];;

(* ------------------------------------------------------------------------- *)
(* The buffer for the output of SHAKE256, followed by the one for its input, *)
(* the seed and the nonce, is aligned to 32 bytes within the stack frame, so *)
(* its address depends on whether the stack pointer is a multiple of 32 or   *)
(* just of 16. The seed is copied there as two 128-bit words.                *)
(* ------------------------------------------------------------------------- *)

let GETNOISE_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 655)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 640 else 624))`;;

let GETNOISE_BUFFER_ADDRESS = assume_spec GETNOISE_BUFFER_ADDRESS_STMT;;

let GETNOISE_BUFFER = `word_add (stackpointer:int64)
                        (word(if aligned 32 stackpointer then 640 else 624))`;;

let GETNOISE_INPUT_BUFFER =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,GETNOISE_BUFFER),
          `word 128:int64`);;

let GETNOISE_BUFFER_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 655))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word(if aligned 32 stackpointer then 640 else 624))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC GETNOISE_BUFFER_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;

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
(* mlkem_poly_compress_d4, and the stack is the 240 bytes of the function    *)
(* and the 592 used by mlkem_shake256 below them.                            *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SHAKE256_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_GCC12_OS_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_SHAKE256_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_ZEROIZE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_GCC12_OS_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_ZEROIZE_6_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_CBD2_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_GCC12_OS_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_Os_mc,
    MLKEM_NATIVE_POLY_CBD2_GCC12_OS_IMAGE_SUBROUTINE_CORRECT);;

(*** The GOT entries in the form in the precondition of the callees ***)

let GETNOISE_GOT_TAC =
  MAP_EVERY (fun t ->
    FIRST_ASSUM(fun th ->
      if can (term_match [] t) (concl th)
      then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else NO_TAC))
   [`read (memory :> bytes64
           (word_add (word pc) (word got_stack_chk_guard))) s =
     g:int64`;
    `read (memory :> bytes64 (word_add (word pc) (word got_memset))) s =
     g:int64`];;

(*** The setup for both proofs, with bounds on the offset of the buffer ***)

let GETNOISE_SETUP_TAC =
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 832):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `624 <= (if aligned 32 (stackpointer:int64) then 640 else 624) /\
    (if aligned 32 (stackpointer:int64) then 640 else 624) <= 640`
  STRIP_ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`; `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21`;;

let MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r seed (sd:byte list) nonce guard mf ea el ev pc stackpointer
    returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH sd = 32 /\
        PAIRWISE nonoverlapping
         [(r,512); (seed,32); (word_sub stackpointer (word 832),832)] /\
        ALLPAIRS nonoverlapping
         [(r,512); (word_sub stackpointer (word 832),832)]
         [(word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8); (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_Os_mc /\
                  read PC s = word (pc + mlkem512_poly_getnoise_eta2) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; seed; nonce] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev /\
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
                memory :> bytes(word_sub stackpointer (word 832),832)])`;;

let MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly as for             *)
(* mlkem_poly_compress_d4. The events do not depend on the nonce.            *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let GETNOISE_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_Os_mc,
       MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_GCC12_OS_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_Os_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `r:int64`; `seed:int64`; `guard:int64`;
                          `mf:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC name safety_th]);;

let MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_safety_contract mf ea el ev
     ==> exists f_events.
     forall e r seed nonce guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [r,512; seed,32; word_sub stackpointer (word 832),832] /\
       ALLPAIRS nonoverlapping
        [r,512; word_sub stackpointer (word 832),832]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8;
         word(pc + got_memset),8; ea,el]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_Os_mc /\
                 read PC s = word (pc + mlkem512_poly_getnoise_eta2) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [r; seed; nonce] s /\
                 read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                   guard /\
                 read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                 read (memory :> bytes(ea,el)) s = ev /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events seed r guard mf pc
                           (word_sub stackpointer (word 832)) returnaddress /\
                    memaccess_inbounds e2
                     [seed,32; r,512; word_sub stackpointer (word 832),832;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + got_memset),8; ea,el;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [r,512; word_sub stackpointer (word 832),832]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(r,512);
               memory :> bytes(word_sub stackpointer (word 832),832)])`;;

let MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_GETNOISE_ETA2_K2_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
