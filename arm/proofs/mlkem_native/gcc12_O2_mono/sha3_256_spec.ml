(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA3-256. This is the code for mlkem_sha3_256 from mlkem-native's         *)
(* portable C implementation compiled by gcc 12 with -O2 as one translation  *)
(* unit (see mlkem_native/README.md), with the specification that it has in  *)
(* the separately compiled gcc12_O2 build, with one difference: the input    *)
(* must be nonempty (0 < LENGTH inp), since mlk_keccak_absorb_once, of which *)
(* it is the caller, requires a nonempty message. It absorbs the input into  *)
(* a state on the stack with mlk_keccak_absorb_once, permutes it with        *)
(* mlk_keccakf1600_permute_c, and extracts the 32 bytes of the hash, which   *)
(* gcc has inlined as two 16-byte loads and stores, and then zeroes the      *)
(* state. It is verified in the whole image (see libmlkem.ml), using the     *)
(* theorems for mlk_keccak_absorb_once and mlk_keccakf1600_permute_c in the  *)
(* image. The result is sha3_256 of common/fips202.ml.                       *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native_kem.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/keccak_absorb_once_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/keccakf1600_permute_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/libmlkem.ml";;

(*** The code in the image:

    mlkem_sha3_256:
     +0x0  stp     x19, x20, [sp, #-240]!
     +0x4  mov     x3, x2
     +0x8  mov     x2, x1
  adrp1:
     +0xc  adrp    x5, <page>
    +0x10  ldr     x5, [x5, #4088]    // got_stack_chk_guard
    +0x14  str     x30, [sp, #16]
    +0x18  add     x19, sp, #0x20
    +0x1c  mov     w4, #0x6
    +0x20  ldr     x6, [x5]
    +0x24  str     x6, [sp, #232]
    +0x28  mov     x6, #0x0
    +0x2c  mov     w1, #0x88
    +0x30  mov     x20, x0
    +0x34  mov     x0, x19
    +0x38  bl      mlk_keccak_absorb_once
    +0x3c  movi    v0.4s, #0x0
    +0x40  mov     x0, x19
    +0x44  bl      mlk_keccakf1600_permute_c
    +0x48  str     xzr, [x19, #192]
    +0x4c  ldp     q1, q2, [x19]
    +0x50  stp     q0, q0, [x19]
    +0x54  stp     q1, q2, [x20]
    +0x58  stp     q0, q0, [x19, #32]
    +0x5c  stp     q0, q0, [x19, #64]
    +0x60  stp     q0, q0, [x19, #96]
    +0x64  stp     q0, q0, [x19, #128]
    +0x68  stp     q0, q0, [x19, #160]
  adrp2:
    +0x6c  adrp    x0, <page>
    +0x70  ldr     x0, [x0, #4088]    // got_stack_chk_guard
    +0x74  ldr     x2, [sp, #232]
    +0x78  ldr     x1, [x0]
    +0x7c  subs    x2, x2, x1
    +0x80  mov     x1, #0x0
    +0x84  b.ne    stack_chk_fail
    +0x88  ldr     x30, [sp, #16]
    +0x8c  ldp     x19, x20, [sp], #240
  ret:
    +0x90  ret
    +0x94  bl      stack_chk_fail
 ***)

let MLKEM_NATIVE_SHA3_256_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "mlkem_sha3_256"];;

(* ------------------------------------------------------------------------- *)
(* The hash is extracted by 16-byte loads of the state and 16-byte stores:   *)
(* if the 128-bit words at offsets 0 and 16 of memory are the two halves of  *)
(* the low 256 bits of a number n, the first 32 bytes are n MOD 2 EXP 256.   *)
(* ------------------------------------------------------------------------- *)

let SHA3_BYTES32_STMT =
  `!a:int64 n s:armstate.
        read (memory :> bytes128 a) s = word(n MOD 2 EXP 128) /\
        read (memory :> bytes128(word_add a (word 16))) s =
        word((n DIV 2 EXP 128) MOD 2 EXP 128)
        ==> read (memory :> bytes(a,32)) s = n MOD 2 EXP 256`;;

let SHA3_BYTES32 = assume_spec SHA3_BYTES32_STMT;;

(*** The two 16-byte loads of the state (in the state after the permutation,
     s20, which is the number val X), from the bytes of the state ***)

let SHA3_HALVES_TAC =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhand c =
       `read (memory :> bytes(word_add (stackpointer:int64) (word 288),200)) s20`
    then
      MAP_EVERY (fun k ->
        MP_TAC(SPECL [`word_add (stackpointer:int64) (word 288)`; `200`;
                      k; rand c; `s20:armstate`] KEM_BYTES128) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1; WORD_ADD_0] THEN
        CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
        DISCH_TAC) [`0`; `1`]
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The input is a list of bytes, and the 32 bytes of the  *)
(* output, as a number, are those of sha3_256 in common/fips202.ml. The      *)
(* address of the stack guard is read from the GOT, and the stack is the 240 *)
(* bytes of the function and the 256 used by mlk_keccak_absorb_once below    *)
(* them.                                                                     *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHA3_256_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!out m (inp:byte list) guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ 0 < LENGTH inp /\
        PAIRWISE nonoverlapping
         [(out,32); (m,LENGTH inp); (word_sub stackpointer (word 496),496)] /\
        ALLPAIRS nonoverlapping
         [(out,32); (word_sub stackpointer (word 496),496)]
         [(word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlkem_sha3_256) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; m; word(LENGTH inp)] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes(m,LENGTH inp)) s =
                  num_of_bytelist inp)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out,32)) s =
                  num_of_bytelist(sha3_256 inp))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out,32);
                memory :> bytes(word_sub stackpointer (word 496),496)])`;;

let MLKEM_NATIVE_SHA3_256_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_SHA3_256_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety, together with the correctness proof.     *)
(* The events depend on the address of the stack guard, read from the GOT,   *)
(* so the theorem is stated directly. As for the correctness theorem the     *)
(* input must be nonempty.                                                   *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let SHA3_256_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mono_mc,
       MLKEM_NATIVE_SHA3_256_GCC12_O2_MONO_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `m:int64`; `out:int64`; `inlen:num`;
                          `guard:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC name safety_th]);;

let MLKEM_NATIVE_SHA3_256_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
     forall e out m (inp:byte list) inlen guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ LENGTH inp = inlen /\ 0 < inlen /\
       PAIRWISE nonoverlapping
        [out,32; m,inlen; word_sub stackpointer (word 496),496] /\
       ALLPAIRS nonoverlapping
        [out,32; word_sub stackpointer (word 496),496]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                 read PC s = word (pc + mlkem_sha3_256) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [out; m; word inlen] s /\
                 read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                   guard /\
                 read (memory :> bytes(m,inlen)) s = num_of_bytelist inp /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 read (memory :> bytes(out,32)) s =
                 num_of_bytelist(sha3_256 inp) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m out inlen guard pc
                           (word_sub stackpointer (word 496)) returnaddress /\
                    memaccess_inbounds e2
                     [m,inlen; out,32; word_sub stackpointer (word 496),496;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [out,32; word_sub stackpointer (word 496),496]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(out,32);
               memory :> bytes(word_sub stackpointer (word 496),496)])`;;

let MLKEM_NATIVE_SHA3_256_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_SHA3_256_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* The safety theorem, from FULL, for any input in memory: its bytes are the *)
(* list for its number.                                                      *)
(* ------------------------------------------------------------------------- *)

let SHA3_LIST_OF_BYTES_STMT =
  `!m:int64 inlen X s:armstate.
        read (memory :> bytes(m,inlen)) s = X
        ==> read (memory :> bytes(m,inlen)) s =
            num_of_bytelist(bytelist_of_num inlen X)`;;

let SHA3_LIST_OF_BYTES = assume_spec SHA3_LIST_OF_BYTES_STMT;;

let MLKEM_NATIVE_SHA3_256_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e out m inlen guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ 0 < inlen /\
       PAIRWISE nonoverlapping
        [out,32; m,inlen; word_sub stackpointer (word 496),496] /\
       ALLPAIRS nonoverlapping
        [out,32; word_sub stackpointer (word 496),496]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                 read PC s = word (pc + mlkem_sha3_256) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [out; m; word inlen] s /\
                 read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                   guard /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m out inlen guard pc
                           (word_sub stackpointer (word 496)) returnaddress /\
                    memaccess_inbounds e2
                     [m,inlen; out,32; word_sub stackpointer (word 496),496;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [out,32; word_sub stackpointer (word 496),496]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(out,32);
               memory :> bytes(word_sub stackpointer (word 496),496)])`;;

let MLKEM_NATIVE_SHA3_256_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_SHA3_256_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT;;
