(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHAKE256 with an output of any length. This is the code for               *)
(* mlkem_shake256 from mlkem-native's portable C implementation compiled by  *)
(* gcc 12 with -Os (see mlkem_native/README.md), which absorbs the input     *)
(* into a state on the stack with mlk_keccak_absorb_once, extracts the       *)
(* output with mlk_keccak_squeeze_once at the rate 136 of SHAKE256, and then *)
(* zeroes the state with memset from the C library, called through the PLT   *)
(* of the image. It is verified in the whole image (see libmlkem.ml), using  *)
(* the theorems for mlk_keccak_absorb_once and mlk_keccak_squeeze_once in    *)
(* the image and assuming the contracts for memset in                        *)
(* utils/mlkem_native_libc.ml. The result is shake256 of                     *)
(* common/fips202/fips202.ml.                                                *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/keccak_absorb_once_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/keccak_squeeze_once_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/libmlkem.ml";;

(*** The code in the image, and the PLT stub for memset:

    mlkem_shake256:
       +0x0: stp     x19, x20, [sp, #-288]!
       +0x4: mov     x20, x0
       +0x8: mov     w4, #0x1f
       +0xc: adrp    x0, <page>
      +0x10: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0x14: stp     x21, x30, [sp, #16]
      +0x18: add     x19, sp, #0x3f
      +0x1c: and     x19, x19, #0xffffffffffffffe0
      +0x20: mov     x21, x1
      +0x24: ldr     x1, [x0]
      +0x28: str     x1, [sp, #280]
      +0x2c: mov     x1, #0x0
      +0x30: mov     x0, x19
      +0x34: mov     w1, #0x88
      +0x38: bl      <mlk_keccak_absorb_once>
      +0x3c: mov     w3, #0x88
      +0x40: mov     x2, x19
      +0x44: mov     x1, x21
      +0x48: mov     x0, x20
      +0x4c: bl      <mlk_keccak_squeeze_once>
      +0x50: mov     x0, x19
      +0x54: mov     x2, #0xe0
      +0x58: mov     w1, #0x0
      +0x5c: bl      <memset@plt>
      +0x60: adrp    x0, <page>
      +0x64: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0x68: ldr     x2, [sp, #280]
      +0x6c: ldr     x1, [x0]
      +0x70: subs    x2, x2, x1
      +0x74: mov     x1, #0x0
      +0x78: b.eq    <mlkem_shake256+0x80>
      +0x7c: bl      <__stack_chk_fail@plt>
      +0x80: ldp     x21, x30, [sp, #16]
      +0x84: ldp     x19, x20, [sp], #288
      +0x88: ret

    memset@plt:
      +0x0: adrp    x16, <page>
      +0x4: ldr     x17, [x16, #4072]  // got_memset
      +0x8: add     x16, x16, #0xfe8  // got_memset
      +0xc: br      x17
 ***)

let MLKEM_NATIVE_SHAKE256_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlkem_shake256"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* The state is aligned to 32 bytes within the stack frame, so its address   *)
(* depends on whether the stack pointer is a multiple of 32 or just of 16.   *)
(* ------------------------------------------------------------------------- *)

let ALIGNED_16_32_WORD_AND_STMT =
  `(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`;;

let ALIGNED_16_32_WORD_AND = assume_spec ALIGNED_16_32_WORD_AND_STMT;;

let SHAKE256_STATE_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 367)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 352 else 336))`;;

let SHAKE256_STATE_ADDRESS = assume_spec SHAKE256_STATE_ADDRESS_STMT;;

let SHAKE256_STATE_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 367))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word(if aligned 32 stackpointer then 352 else 336))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC SHAKE256_STATE_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;

let SHAKE256_ST = `word_add (stackpointer:int64)
                    (word(if aligned 32 stackpointer then 352 else 336))`;;

(*** The setup for all proofs, with the bounds on the offset of the state ***)

let SHAKE256_SETUP_TAC =
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 592):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `336 <= (if aligned 32 (stackpointer:int64) then 352 else 336) /\
    (if aligned 32 (stackpointer:int64) then 352 else 336) <= 352`
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

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The input is a list of bytes, and the outlen bytes of  *)
(* the output, as a number, are the first outlen bytes of shake256 in        *)
(* common/fips202/fips202.ml. The address of the stack guard is read from    *)
(* the GOT, as for mlkem_poly_compress_d4, and the contract for memset is    *)
(* that at the address mf in its GOT entry, with its code and data in the    *)
(* region (ea,el), which must not overlap the output or the stack. The       *)
(* stack is the 288 bytes of the function and the 304 used by                *)
(* mlk_keccak_absorb_once below them.                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE256_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!out outlen m (inp:byte list) guard mf ea el ev pc stackpointer
    returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(out,outlen); (m,LENGTH inp);
          (word_sub stackpointer (word 592),592)] /\
        ALLPAIRS nonoverlapping
         [(out,outlen); (word_sub stackpointer (word 592),592)]
         [(word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8); (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_Os_mc /\
                  read PC s = word (pc + mlkem_shake256) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; m; word(LENGTH inp)] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(m,LENGTH inp)) s =
                  num_of_bytelist inp)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out,outlen)) s =
                  num_of_bytelist(list_of_seq (shake256 inp) outlen))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out,outlen);
                memory :> bytes(word_sub stackpointer (word 592),592)])`;;

let MLKEM_NATIVE_SHAKE256_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_SHAKE256_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. As for mlkem_poly_compress_d4, it  *)
(* is stated directly, since the events depend on the address of the stack   *)
(* guard, read from the GOT, and on the address of memset, as well as on the *)
(* events of memset given by its contract.                                   *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let SHAKE256_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_Os_mc,MLKEM_NATIVE_SHAKE256_GCC12_OS_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_Os_mc,safety_th)
      ilist n THENL
     [ABSORB_EXISTS_E2_TAC (ref
       [`pc:num`; `m:int64`; `out:int64`; `outlen:num`; `inlen:num`;
        `guard:int64`; `mf:int64`; `stackpointer:int64`;
        `returnaddress:int64`]);
      LABEL_TAC name safety_th]);;

let MLKEM_NATIVE_SHAKE256_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_safety_contract mf ea el ev
     ==> exists f_events.
     forall e out outlen m inlen guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [out,outlen; m,inlen; word_sub stackpointer (word 592),592] /\
       ALLPAIRS nonoverlapping
        [out,outlen; word_sub stackpointer (word 592),592]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8;
         word(pc + got_memset),8; ea,el]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_Os_mc /\
                 read PC s = word (pc + mlkem_shake256) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [out; word outlen; m; word inlen] s /\
                 read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                   guard /\
                 read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                 read (memory :> bytes(ea,el)) s = ev /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m out outlen inlen guard mf pc
                           (word_sub stackpointer (word 592)) returnaddress /\
                    memaccess_inbounds e2
                     [m,inlen; out,outlen;
                      word_sub stackpointer (word 592),592;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + got_memset),8; ea,el;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [out,outlen; word_sub stackpointer (word 592),592]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(out,outlen);
               memory :> bytes(word_sub stackpointer (word 592),592)])`;;

let MLKEM_NATIVE_SHAKE256_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_SHAKE256_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
