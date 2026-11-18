(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Addition of polynomials, coefficientwise with wraparound. This is the     *)
(* code for mlkem_poly_add from mlkem-native's portable C implementation     *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md), which the       *)
(* compiler has vectorized. It is verified in the whole image (see           *)
(* libmlkem.ml). Since the code uses aligned SSE loads and stores, the       *)
(* polynomials must be aligned, as they are in mlkem-native.                 *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_add:
       +0x0: xor    eax,eax
       +0x2: nop    WORD PTR [rax+rax*1+0x0]
       +0x8: movdqa xmm0,XMMWORD PTR [rdi+rax*1]
       +0xd: paddw  xmm0,XMMWORD PTR [rsi+rax*1]
      +0x12: movaps XMMWORD PTR [rdi+rax*1],xmm0
      +0x16: add    rax,0x10
      +0x1a: cmp    rax,0x200
      +0x20: jne    <mlkem_poly_add+0x8>
      +0x22: ret
 ***)

let MLKEM_NATIVE_POLY_ADD_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem_poly_add"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_ADD_GCC12_O2_IMAGE_CORRECT_STMT =
  `!r b x y pc.
    aligned 16 (word pc:int64) /\ aligned 16 r /\ aligned 16 b /\
    ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (b,512)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + mlkem_poly_add) /\
           C_ARGUMENTS [r; b] s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                    x i) /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add b (word(2 * i)))) s =
                    y i))
      (\s. read RIP s = word (pc + mlkem_poly_add_ret) /\
           !i. i < 256
               ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                   word_add (x i) (y i))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_ADD_GCC12_O2_IMAGE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_ADD_GCC12_O2_IMAGE_CORRECT_STMT;;

let MLKEM_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r b x y pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\ aligned 16 r /\ aligned 16 b /\
    ALL (nonoverlapping (r,512))
        [(word pc,libmlkem_size); (b,512); (stackpointer,8)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + mlkem_poly_add) /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [r; b] s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                    x i) /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add b (word(2 * i)))) s =
                    y i))
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           !i. i < 256
               ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                   word_add (x i) (y i))
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SAFE_STMT =
  `exists f_events.
       forall e r b pc.
           aligned 16 (word pc:int64) /\ aligned 16 r /\ aligned 16 b /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; b,512]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_add) /\
                    C_ARGUMENTS [r; b] s /\
                    read events s = e)
               (\s. read RIP s = word (pc + mlkem_poly_add_ret) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events r b pc /\
                         memaccess_inbounds e2 [r,512; b,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SAFE_STMT;;

let MLKEM_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r b pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\ aligned 16 r /\ aligned 16 b /\
           ALL (nonoverlapping (r,512))
               [word pc,libmlkem_size; b,512; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_add) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; b] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events r b pc stackpointer returnaddress /\
                         memaccess_inbounds e2
                          [r,512; b,512; stackpointer,8] [r,512]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
