(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Squeezing bytes from a SHAKE128 context: the statement. This is the code  *)
(* for mldsa_shake128_squeeze (mld_shake128_squeeze in fips202.c) from       *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -Os (see *)
(* mldsa_native/README.md), which passes the output, its length, the         *)
(* context, its position and the rate 168 to keccak_squeeze (the static      *)
(* function of fips202.c, named keccak_squeeze_fn in layout.ml) and stores   *)
(* the position that it returns. keccak_squeeze copies the bytes of the      *)
(* state from the position on, permuting it whenever the position reaches    *)
(* the rate and more bytes are wanted. It is verified in the whole image     *)
(* (see libmldsa.ml), using the theorem for keccak_squeeze in the image,     *)
(* against mld_keccak_squeeze_byte and mld_keccak_squeeze_state of           *)
(* common/mldsa_native_fips202.ml, for a position up to the rate, as the C   *)
(* code requires. The stack is the 16 bytes of the function and the 288 used *)
(* by keccak_squeeze below them. It is also shown to be constant time and    *)
(* memory safe.                                                              *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_absorb.ml";;
needs "common/mldsa_native_fips202.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/keccak_squeeze_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa_shake128_squeeze:
       +0x0: ldr     w3, [x2, #200]
       +0x4: mov     w4, #0xa8
       +0x8: stp     x19, x30, [sp, #-16]!
       +0xc: mov     x19, x2
      +0x10: bl      <keccak_squeeze_fn>
      +0x14: str     w0, [x19, #200]
      +0x18: ldp     x19, x30, [sp], #16
      +0x1c: ret
 ***)

let MLDSA_NATIVE_SHAKE128_SQUEEZE_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa_shake128_squeeze"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE128_SQUEEZE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!out outlen ctx (S:1600 word) pos pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ pos <= 168 /\
        PAIRWISE nonoverlapping
         [(ctx,204); (out,outlen); (word_sub stackpointer (word 304),304)] /\
        ALL (nonoverlapping (word pc,libmldsa_size))
         [(ctx,204); (out,outlen); (word_sub stackpointer (word 304),304)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_shake128_squeeze) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; ctx] s /\
                  read (memory :> wbytes ctx) s = S /\
                  read (memory :> bytes32(word_add ctx (word 200))) s =
                  word pos)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out,outlen)) s =
                  num_of_bytelist
                   (list_of_seq (mld_keccak_squeeze_byte 168 S pos) outlen) /\
                  read (memory :> wbytes ctx) s =
                  FST(mld_keccak_squeeze_state 168 S pos outlen) /\
                  read (memory :> bytes32(word_add ctx (word 200))) s =
                  word(SND(mld_keccak_squeeze_state 168 S pos outlen)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE [memory :> bytes(ctx,204); memory :> bytes(out,outlen);
                         memory :> bytes(word_sub stackpointer (word 304),304)])`;;

let MLDSA_NATIVE_SHAKE128_SQUEEZE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_SHAKE128_SQUEEZE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the length and the position only  *)
(* (which give the number of blocks), with all accesses within the output,   *)
(* the context, the stack and the round constants of the permutation, and    *)
(* the writes within the context, the output and the stack.                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE128_SQUEEZE_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e out outlen ctx (S:1600 word) pos pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ pos <= 168 /\
        PAIRWISE nonoverlapping
         [(ctx,204); (out,outlen); (word_sub stackpointer (word 304),304)] /\
        ALL (nonoverlapping (word pc,libmldsa_size))
         [(ctx,204); (out,outlen); (word_sub stackpointer (word 304),304)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_shake128_squeeze) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; ctx] s /\
                  read (memory :> wbytes ctx) s = S /\
                  read (memory :> bytes32(word_add ctx (word 200))) s =
                  word pos /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out,outlen)) s =
                  num_of_bytelist
                   (list_of_seq (mld_keccak_squeeze_byte 168 S pos) outlen) /\
                  read (memory :> wbytes ctx) s =
                  FST(mld_keccak_squeeze_state 168 S pos outlen) /\
                  read (memory :> bytes32(word_add ctx (word 200))) s =
                  word(SND(mld_keccak_squeeze_state 168 S pos outlen)) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events out outlen ctx pos pc
                                 (word_sub stackpointer (word 304))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [out,outlen; ctx,204;
                       word_sub stackpointer (word 304),304;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [ctx,204; out,outlen;
                       word_sub stackpointer (word 304),304]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(ctx,204); memory :> bytes(out,outlen);
                memory :> bytes(word_sub stackpointer (word 304),304)])`;;

let MLDSA_NATIVE_SHAKE128_SQUEEZE_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_SHAKE128_SQUEEZE_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE128_SQUEEZE_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e out outlen ctx pos pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ pos <= 168 /\
        PAIRWISE nonoverlapping
         [(ctx,204); (out,outlen); (word_sub stackpointer (word 304),304)] /\
        ALL (nonoverlapping (word pc,libmldsa_size))
         [(ctx,204); (out,outlen); (word_sub stackpointer (word 304),304)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_shake128_squeeze) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; ctx] s /\
                  read (memory :> bytes32(word_add ctx (word 200))) s =
                  word pos /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events out outlen ctx pos pc
                                 (word_sub stackpointer (word 304))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [out,outlen; ctx,204;
                       word_sub stackpointer (word 304),304;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [ctx,204; out,outlen;
                       word_sub stackpointer (word 304),304]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(ctx,204); memory :> bytes(out,outlen);
                memory :> bytes(word_sub stackpointer (word 304),304)])`;;

let MLDSA_NATIVE_SHAKE128_SQUEEZE_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_SHAKE128_SQUEEZE_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
