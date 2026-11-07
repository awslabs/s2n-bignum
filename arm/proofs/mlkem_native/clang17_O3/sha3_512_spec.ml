(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA3-512. This is the code for mlkem_sha3_512 from mlkem-native's         *)
(* portable C implementation compiled by clang 17 with -O3 (see              *)
(* mlkem_native/README.md), which absorbs the input into a state on the      *)
(* stack with mlk_keccak_absorb_once, with the rate 72 of SHA3-512, permutes *)
(* it and extracts the 64 bytes of the hash, and then zeroes the state. The  *)
(* specifications are those of gcc12_O2, except for the stack: the code uses *)
(* the 240 bytes of its own frame, with the state at their base and the      *)
(* stack guard above it, and the 288 bytes of mlk_keccak_absorb_once below   *)
(* them, which are the 80 bytes of its frame and the 208 used by             *)
(* mlkem_keccakf1600_permute. It is verified in the whole image (see         *)
(* libmlkem.ml), using the theorems for mlk_keccak_absorb_once,              *)
(* mlkem_keccakf1600_permute and mlkem_keccakf1600_extract_bytes in the      *)
(* image. The result is sha3_512 of common/fips202.ml.                       *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/keccak_absorb_once_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/keccakf1600_extract_bytes_spec.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_sha3_512:
      +0x0: sub     sp, sp, #0xf0
      +0x4: str     x30, [sp, #208]
      +0x8: stp     x20, x19, [sp, #224]
      +0xc: adrp    x8, <page>
     +0x10: mov     x3, x2
     +0x14: mov     x2, x1
     +0x18: mov     x19, x0
     +0x1c: mov     x0, sp
     +0x20: mov     w1, #0x48
     +0x24: ldr     x8, [x8, #4088]  // got_stack_chk_guard
     +0x28: mov     w4, #0x6
     +0x2c: mov     x20, sp
     +0x30: ldr     x8, [x8]
     +0x34: str     x8, [sp, #200]
     +0x38: bl      mlk_keccak_absorb_once
     +0x3c: mov     x0, sp
     +0x40: bl      mlkem_keccakf1600_permute
     +0x44: mov     x0, sp
     +0x48: mov     x1, x19
     +0x4c: mov     w2, wzr
     +0x50: mov     w3, #0x40
     +0x54: bl      mlkem_keccakf1600_extract_bytes
     +0x58: movi    v0.2d, #0x0
     +0x5c: adrp    x8, <page>
     +0x60: str     xzr, [sp, #192]
     +0x64: stp     q0, q0, [sp]
     +0x68: stp     q0, q0, [sp, #32]
     +0x6c: stp     q0, q0, [sp, #64]
     +0x70: stp     q0, q0, [sp, #96]
     +0x74: stp     q0, q0, [sp, #128]
     +0x78: stp     q0, q0, [sp, #160]
     +0x7c: ldr     x8, [x8, #4088]  // got_stack_chk_guard
     +0x80: ldr     x9, [sp, #200]
     +0x84: ldr     x8, [x8]
     +0x88: cmp     x8, x9
     +0x8c: b.ne    +0xa0
     +0x90: ldp     x20, x19, [sp, #224]
     +0x94: ldr     x30, [sp, #208]
     +0x98: add     sp, sp, #0xf0
     +0x9c: ret
     +0xa0: bl      __stack_chk_fail
 ***)

let MLKEM_NATIVE_SHA3_512_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_sha3_512"];;

(*** The callee mlk_keccak_absorb_once has the GOT entry of the stack guard ***)
(*** as a precondition, in the form word(pc + got_stack_chk_guard), but    ***)
(*** the code reads it as word_add (word pc) (word got_stack_chk_guard)    ***)

let SHA3_GUARD_TAC =
  W(fun (asl,_) ->
    MAP_EVERY (fun (_,th) ->
      if can (term_match []
        `read (memory :> bytes64 (word_add (word pc) (word n))) s = guard`)
        (concl th)
      then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else ALL_TAC) asl);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The input is a list of bytes, and the 32 bytes of the  *)
(* output, as a number, are those of sha3_512 in common/fips202.ml. As for   *)
(* mlkem_poly_compress_d4, the address of the stack guard is read from the   *)
(* GOT, and the stack is the 240 bytes of the function and the 256 used by   *)
(* mlk_keccak_absorb_once below them.                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHA3_512_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!out m (inp:byte list) guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(out,64); (m,LENGTH inp); (word_sub stackpointer (word 528),528)] /\
        ALLPAIRS nonoverlapping
         [(out,64); (word_sub stackpointer (word 528),528)]
         [(word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem_sha3_512) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; m; word(LENGTH inp)] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes(m,LENGTH inp)) s =
                  num_of_bytelist inp)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out,64)) s =
                  num_of_bytelist(sha3_512 inp))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out,64);
                memory :> bytes(word_sub stackpointer (word 528),528)])`;;

let MLKEM_NATIVE_SHA3_512_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_SHA3_512_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. As for mlkem_poly_compress_d4, it  *)
(* is stated directly, since the events depend on the address of the stack   *)
(* guard, read from the GOT.                                                 *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let SHA3_512_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_clang17_O3_mc,MLKEM_NATIVE_SHA3_512_CLANG17_O3_EXEC,
       0x0,mlkem_native_libmlkem_clang17_O3_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `m:int64`; `out:int64`; `inlen:num`;
                          `guard:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC name safety_th]);;

let MLKEM_NATIVE_SHA3_512_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e out m inlen guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [out,64; m,inlen; word_sub stackpointer (word 528),528] /\
       ALLPAIRS nonoverlapping
        [out,64; word_sub stackpointer (word 528),528]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_clang17_O3_mc /\
                 read PC s = word (pc + mlkem_sha3_512) /\
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
                           (word_sub stackpointer (word 528)) returnaddress /\
                    memaccess_inbounds e2
                     [m,inlen; out,64; word_sub stackpointer (word 528),528;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [out,64; word_sub stackpointer (word 528),528]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(out,64);
               memory :> bytes(word_sub stackpointer (word 528),528)])`;;

let MLKEM_NATIVE_SHA3_512_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_SHA3_512_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, using those  *)
(* of mlk_keccak_absorb_once, mlkem_keccakf1600_permute and                  *)
(* mlkem_keccakf1600_extract_bytes, for the hash check of the decapsulation  *)
(* key, whose result the decapsulation branches on.                          *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHA3_512_CLANG17_O3_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
     forall e out m (inp:byte list) inlen guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ LENGTH inp = inlen /\
       PAIRWISE nonoverlapping
        [out,64; m,inlen; word_sub stackpointer (word 528),528] /\
       ALLPAIRS nonoverlapping
        [out,64; word_sub stackpointer (word 528),528]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_clang17_O3_mc /\
                 read PC s = word (pc + mlkem_sha3_512) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [out; m; word inlen] s /\
                 read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                   guard /\
                 read (memory :> bytes(m,inlen)) s = num_of_bytelist inp /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 read (memory :> bytes(out,64)) s =
                 num_of_bytelist(sha3_512 inp) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m out inlen guard pc
                           (word_sub stackpointer (word 528)) returnaddress /\
                    memaccess_inbounds e2
                     [m,inlen; out,64; word_sub stackpointer (word 528),528;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [out,64; word_sub stackpointer (word 528),528]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(out,64);
               memory :> bytes(word_sub stackpointer (word 528),528)])`;;

let MLKEM_NATIVE_SHA3_512_CLANG17_O3_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_SHA3_512_CLANG17_O3_IMAGE_SUBROUTINE_FULL_STMT;;
