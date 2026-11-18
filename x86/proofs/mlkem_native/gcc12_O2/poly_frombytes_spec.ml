(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a polynomial from bytes, 12 bits per coefficient. This is    *)
(* the code for mlkem_poly_frombytes from mlkem-native's portable C          *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md).  *)
(* It is verified in the whole image (see libmlkem.ml). As in mlkem_decode   *)
(* in common/fips203/fips203.ml, the bytes are given as a number n, with     *)
(* coefficient i being bits 12 * i to 12 * i + 11 of n.                      *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_frombytes:
       +0x0: lea    r9,[rsi+0x180]
       +0x7: nop    WORD PTR [rax+rax*1+0x0]
      +0x10: movzx  eax,BYTE PTR [rsi+0x1]
      +0x14: movzx  edx,BYTE PTR [rsi+0x2]
      +0x18: add    rsi,0x3
      +0x1c: add    rdi,0x4
      +0x20: movzx  r8d,BYTE PTR [rsi-0x3]
      +0x25: mov    ecx,eax
      +0x27: shr    al,0x4
      +0x2a: shl    ecx,0x8
      +0x2d: movzx  eax,al
      +0x30: shl    edx,0x4
      +0x33: and    cx,0xf00
      +0x38: or     eax,edx
      +0x3a: or     ecx,r8d
      +0x3d: mov    WORD PTR [rdi-0x2],ax
      +0x41: mov    WORD PTR [rdi-0x4],cx
      +0x45: cmp    r9,rsi
      +0x48: jne    <mlkem_poly_frombytes+0x10>
      +0x4a: ret
 ***)

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem_poly_frombytes"];;

(* ------------------------------------------------------------------------- *)
(* The two coefficients from three bytes.                                    *)
(* ------------------------------------------------------------------------- *)

let FROMBYTES_LANES_STMT =
  `!n i.
     word_zx(word_join
              (word_subword (word((n DIV 2 EXP (24 * i + 8)) MOD 256):byte)
                            (0,4):4 word)
              (word((n DIV 2 EXP (24 * i)) MOD 256):byte):12 word):int16 =
     word((n DIV 2 EXP (24 * i)) MOD 4096) /\
     word_zx(word_join
              (word((n DIV 2 EXP (24 * i + 16)) MOD 256):byte)
              (word_subword (word((n DIV 2 EXP (24 * i + 8)) MOD 256):byte)
                            (4,4):4 word):12 word):int16 =
     word((n DIV 2 EXP (24 * i + 12)) MOD 4096)`;;

let FROMBYTES_LANES =
  assume_spec FROMBYTES_LANES_STMT;;

(* ------------------------------------------------------------------------- *)
(* The address of the first of the two coefficients stored in an iteration   *)
(* is computed as word_add (word_add r (word(4 * i))) (word 2), and it is    *)
(* put in the form word_add r (word(4 * i + 2)) before the second store, so  *)
(* that the simulation knows that they do not overlap.                       *)
(* ------------------------------------------------------------------------- *)

let ADDR_NORM_BYTES16_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (term_match []
         `read (memory :> bytes16 (word_add (word_add a (word m)) (word n)))
               s = v`) (concl th)
    then CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV(REWR_CONV(GSYM WORD_ADD_ASSOC))
                             THENC ONCE_DEPTH_CONV(REWR_CONV(GSYM WORD_ADD))))
                  th
    else th);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_CORRECT_STMT =
  `!r a n pc.
    aligned 16 (word pc:int64) /\
    ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,384)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + mlkem_poly_frombytes) /\
           C_ARGUMENTS [r; a] s /\
           read (memory :> bytes(a,384)) s = n)
      (\s. read RIP s = word (pc + mlkem_poly_frombytes_ret) /\
           !i. i < 256
               ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                   word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_CORRECT_STMT;;

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\
    ALL (nonoverlapping (r,512))
        [(word pc,libmlkem_size); (a,384); (stackpointer,8)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + mlkem_poly_frombytes) /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [r; a] s /\
           read (memory :> bytes(a,384)) s = n)
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           !i. i < 256
               ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                   word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12))
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SAFE_STMT =
  `exists f_events.
       forall e r a pc.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,384]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_frombytes) /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = word (pc + mlkem_poly_frombytes_ret) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc /\
                         memaccess_inbounds e2 [a,384; r,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SAFE_STMT;;

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,512))
               [word pc,libmlkem_size; a,384; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_frombytes) /\
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
                          [a,384; r,512; stackpointer,8] [r,512]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, as for       *)
(* mlkem_poly_reduce, and the version as a subroutine.                       *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_FULL_STMT =
  `exists f_events.
       forall e r a n pc.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,384]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_frombytes) /\
                    C_ARGUMENTS [r; a] s /\
                    read (memory :> bytes(a,384)) s = n /\
                    read events s = e)
               (\s. read RIP s = word (pc + mlkem_poly_frombytes_ret) /\
                    (!i. i < 256
                         ==> read(memory :> bytes16
                                   (word_add r (word(2 * i)))) s =
                             word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12)) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc /\
                         memaccess_inbounds e2 [a,384; r,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_FULL =
  assume_spec MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_FULL_STMT;;

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
       forall e r a n pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,512))
               [word pc,libmlkem_size; a,384; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_frombytes) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read (memory :> bytes(a,384)) s = n /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (!i. i < 256
                         ==> read(memory :> bytes16
                                   (word_add r (word(2 * i)))) s =
                             word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12)) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc stackpointer returnaddress /\
                         memaccess_inbounds e2
                          [a,384; r,512; stackpointer,8] [r,512]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;
