(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decomposition of a vector of 4 polynomials with the packing of the high   *)
(* parts: the statement. This is the code for                                *)
(* mldsa44_polyveck_decompose_pack_w1 (mld_polyveck_decompose_pack_w1 in     *)
(* polyvec.c) from mldsa-native's portable C implementation compiled by gcc  *)
(* 12 with -O2 (see mldsa_native/README.md), which, for each polynomial in a *)
(* loop, decomposes it with mldsa44_poly_decompose, the low part in place    *)
(* and the high part in the scratch polynomial, and packs the high part with *)
(* mldsa_polyw1_pack_88. It is verified in the whole image (see libmldsa.ml) *)
(* against mld_polyvec_map and mld_polyvec_pack of                           *)
(* common/mldsa_native_polyvec.ml, using the theorems for                    *)
(* mldsa44_poly_decompose and mldsa_polyw1_pack_88, and shown to be constant *)
(* time and memory safe.                                                     *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_decompose_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyw1_pack_88_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_polyveck_decompose_pack_w1:
       +0x0  push    r13
       +0x2  lea     r13, [rdi+0x300]
       +0x9  push    r12
       +0xb  mov     r12, rdx
       +0xe  push    rbp
       +0xf  mov     rbp, rsi
      +0x12  push    rbx
      +0x13  mov     rbx, rdi
      +0x16  sub     rsp, 0x8
     loop1:
      +0x1a  mov     rsi, rbp
      +0x1d  mov     rdi, r12
      +0x20  add     rbp, 0x400
      +0x27  call    mldsa44_poly_decompose
     after_mldsa44_poly_decompose:
      +0x2c  mov     rdi, rbx
      +0x2f  mov     rsi, r12
      +0x32  add     rbx, 0xc0
      +0x39  call    mldsa_polyw1_pack_88
     loop1_test: after_mldsa_polyw1_pack_88:
      +0x3e  cmp     rbx, r13
     loop1_back:
      +0x41  jne     loop1
     loop1_exit:
      +0x43  add     rsp, 0x8
      +0x47  pop     rbx
      +0x48  pop     rbp
      +0x49  pop     r12
      +0x4b  pop     r13
     ret:
      +0x4d  ret
 ***)

let MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_polyveck_decompose_pack_w1"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The vector x at v, 4 polynomials of 256 coefficients of 32   *)
(* bits each (see common/mldsa_native_polyvec.ml), becomes mld_polyvec_map   *)
(* mld_poly_decompose_lo_88 x, the low parts, and the 4 packed high parts of *)
(* 192 bytes each at r are given byte by byte by mld_polyvec_pack 192        *)
(* (mld_polyw1_pack_88 o mld_poly_decompose_hi_88) x. The scratch polynomial *)
(* at scratch is overwritten. The function saves R13, R12, RBP and RBX below *)
(* the return address and keeps 8 more bytes there, and each call puts its   *)
(* return address below them (48 bytes in all).                              *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r v x scratch pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(r,768); (v,4096); (scratch,1024);
          (word_sub stackpointer (word 48),48); (word pc,libmldsa_size)] /\
        ALL (nonoverlapping (stackpointer,8))
            [(r,768); (v,4096); (scratch,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_polyveck_decompose_pack_w1) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; v; scratch] s /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = x i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s =
                           mld_polyvec_map mld_poly_decompose_lo_88 x i) /\
                  (!j. j < 768
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           mld_polyvec_pack 192
                             (mld_polyw1_pack_88 o
                              mld_poly_decompose_hi_88) x j))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,768);
                memory :> bytes(v,4096);
                memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let
 MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
 MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* vector, the packed high parts, the scratch polynomial, the stack frame    *)
(* and the slot of the return address, and the writes within the vector, the *)
(* packed high parts, the scratch polynomial and the stack frame.            *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r v x scratch pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(r,768); (v,4096); (scratch,1024);
          (word_sub stackpointer (word 48),48); (word pc,libmldsa_size)] /\
        ALL (nonoverlapping (stackpointer,8))
            [(r,768); (v,4096); (scratch,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_polyveck_decompose_pack_w1) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; v; scratch] s /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s =
                           mld_polyvec_map mld_poly_decompose_lo_88 x i) /\
                  (!j. j < 768
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           mld_polyvec_pack 192
                             (mld_polyw1_pack_88 o
                              mld_poly_decompose_hi_88) x j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r v scratch pc
                            (word_sub stackpointer (word 48)) returnaddress /\
                     memaccess_inbounds e2
                      [v,4096; r,768; scratch,1024;
                       word_sub stackpointer (word 48),48; stackpointer,8]
                      [v,4096; r,768; scratch,1024;
                       word_sub stackpointer (word 48),48]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,768);
                memory :> bytes(v,4096);
                memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
 MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r v scratch pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(r,768); (v,4096); (scratch,1024);
          (word_sub stackpointer (word 48),48); (word pc,libmldsa_size)] /\
        ALL (nonoverlapping (stackpointer,8))
            [(r,768); (v,4096); (scratch,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_polyveck_decompose_pack_w1) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; v; scratch] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r v scratch pc
                            (word_sub stackpointer (word 48)) returnaddress /\
                     memaccess_inbounds e2
                      [v,4096; r,768; scratch,1024;
                       word_sub stackpointer (word 48),48; stackpointer,8]
                      [v,4096; r,768; scratch,1024;
                       word_sub stackpointer (word 48),48]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,768);
                memory :> bytes(v,4096);
                memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
 MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
