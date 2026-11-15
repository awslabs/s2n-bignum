(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a polynomial from 4 bits per coefficient. This is the    *)
(* code for mlkem_poly_decompress_d4 from mlkem-native's portable C          *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md).  *)
(* It is verified in the whole image (see libmlkem.ml).                      *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_decompress_d4:
       +0x0: xor    edx,edx
       +0x2: nop    WORD PTR [rax+rax*1+0x0]
       +0x8: movzx  eax,BYTE PTR [rsi+rdx*1]
       +0xc: and    eax,0xf
       +0xf: imul   eax,eax,0xd01
      +0x15: add    eax,0x8
      +0x18: shr    eax,0x4
      +0x1b: mov    WORD PTR [rdi+rdx*4],ax
      +0x1f: movzx  eax,BYTE PTR [rsi+rdx*1]
      +0x23: shr    al,0x4
      +0x26: movzx  eax,al
      +0x29: imul   eax,eax,0xd01
      +0x2f: add    eax,0x8
      +0x32: shr    eax,0x4
      +0x35: mov    WORD PTR [rdi+rdx*4+0x2],ax
      +0x3a: add    rdx,0x1
      +0x3e: cmp    rdx,0x80
      +0x45: jne    <mlkem_poly_decompress_d4+0x8>
      +0x47: ret
 ***)

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem_poly_decompress_d4"];;

(* ------------------------------------------------------------------------- *)
(* The two 4-bit fields of a byte of an array given as a number.             *)
(* ------------------------------------------------------------------------- *)

let BYTE_NIBBLES_STMT =
  `(!n k. (n DIV 2 EXP k) MOD 2 EXP 4 = ((n DIV 2 EXP k) MOD 256) MOD 16) /\
   (!n k. (n DIV 2 EXP (k + 4)) MOD 2 EXP 4 =
          ((n DIV 2 EXP k) MOD 256) DIV 16)`;;

let BYTE_NIBBLES =
  assume_spec BYTE_NIBBLES_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decompress 4 in                           *)
(* common/fips203/fips203.ml, the result for a 4-bit field y is the integer  *)
(* closest to 3329 * y / 16, rounding up on ties, i.e.                       *)
(* (3329 * y + 8) DIV 16.                                                    *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_IMAGE_CORRECT_STMT =
  `!r a n pc.
    aligned 16 (word pc:int64) /\
    ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,128)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + mlkem_poly_decompress_d4) /\
           C_ARGUMENTS [r; a] s /\
           read (memory :> bytes(a,128)) s = n)
      (\s. read RIP s = word (pc + mlkem_poly_decompress_d4_ret) /\
           !i. i < 256
               ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                   word((3329 * (n DIV 2 EXP (4 * i)) MOD 2 EXP 4 + 8) DIV 16))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_IMAGE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_IMAGE_CORRECT_STMT;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\
    ALL (nonoverlapping (r,512))
        [(word pc,libmlkem_size); (a,128); (stackpointer,8)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + mlkem_poly_decompress_d4) /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [r; a] s /\
           read (memory :> bytes(a,128)) s = n)
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           !i. i < 256
               ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                   word((3329 * (n DIV 2 EXP (4 * i)) MOD 2 EXP 4 + 8) DIV 16))
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_IMAGE_SAFE_STMT =
  `exists f_events.
       forall e r a pc.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,128]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_decompress_d4) /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = word (pc + mlkem_poly_decompress_d4_ret) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc /\
                         memaccess_inbounds e2 [a,128; r,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_IMAGE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_IMAGE_SAFE_STMT;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,512))
               [word pc,libmlkem_size; a,128; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_decompress_d4) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc stackpointer returnaddress /\
                         memaccess_inbounds e2
                          [a,128; r,512; stackpointer,8] [r,512]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
