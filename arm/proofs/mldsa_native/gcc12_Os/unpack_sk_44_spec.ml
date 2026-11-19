(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a secret key: the statement. This is the code for            *)
(* mldsa44_unpack_sk (mld_unpack_sk in packing.c) from mldsa-native's        *)
(* portable C implementation compiled by gcc 12 with -Os (see                *)
(* mldsa_native/README.md): it copies rho, key and tr out of the 2560 bytes  *)
(* of the secret key with 128-bit loads and stores, and unpacks the 4        *)
(* polynomials of s1, the 4 of s2 and the 4 of t0 and transforms them to the *)
(* NTT domain, calling mldsa44_polyvecl_unpack_eta, mldsa44_polyvecl_ntt,    *)
(* mldsa44_polyveck_unpack_eta and mldsa44_polyveck_ntt, then                *)
(* mldsa_polyt0_unpack for each polynomial of t0 in a loop and               *)
(* mldsa44_polyveck_ntt in a tail call. It is verified in the whole image    *)
(* (see libmldsa.ml) against mld_polyvec_map mld_poly_ntt and                *)
(* mld_polyvec_unpack of common/mldsa_native_polyvec.ml, using the theorems  *)
(* for the callees, and shown to be constant time and memory safe.           *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyvecl_unpack_eta_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyvecl_ntt_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyveck_unpack_eta_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyveck_ntt_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyt0_unpack_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa44_unpack_sk:
       +0x0: ldp     q0, q1, [x6]
       +0x4: stp     x19, x20, [sp, #-48]!
       +0x8: mov     x19, x6
       +0xc: stp     x21, x22, [sp, #16]
      +0x10: mov     x20, x3
      +0x14: mov     x21, x5
      +0x18: str     x30, [sp, #32]
      +0x1c: mov     x22, x4
      +0x20: stp     q0, q1, [x0]
      +0x24: add     x0, x6, #0x40
      +0x28: ldp     q0, q1, [x6, #32]
      +0x2c: stp     q0, q1, [x2]
      +0x30: ldp     q0, q1, [x0]
      +0x34: stp     q0, q1, [x1]
      +0x38: ldp     q0, q1, [x0, #32]
      +0x3c: mov     x0, x4
      +0x40: stp     q0, q1, [x1, #32]
      +0x44: add     x1, x6, #0x80
      +0x48: bl      <mldsa44_polyvecl_unpack_eta>
      +0x4c: mov     x0, x22
      +0x50: mov     x22, x20
      +0x54: bl      <mldsa44_polyvecl_ntt>
      +0x58: add     x1, x19, #0x200
      +0x5c: mov     x0, x21
      +0x60: bl      <mldsa44_polyveck_unpack_eta>
      +0x64: mov     x0, x21
      +0x68: add     x21, x19, #0x380
      +0x6c: add     x19, x19, #0xa00
      +0x70: bl      <mldsa44_polyveck_ntt>
      +0x74: mov     x1, x21
      +0x78: mov     x0, x22
      +0x7c: add     x21, x21, #0x1a0
      +0x80: bl      <mldsa_polyt0_unpack>
      +0x84: add     x22, x22, #0x400
      +0x88: cmp     x21, x19
      +0x8c: b.ne    <mldsa44_unpack_sk+0x74>
      +0x90: ldp     x21, x22, [sp, #16]
      +0x94: mov     x0, x20
      +0x98: ldr     x30, [sp, #32]
      +0x9c: ldp     x19, x20, [sp], #48
      +0xa0: b       <mldsa44_polyveck_ntt>
 ***)

let MLDSA_NATIVE_UNPACK_SK_44_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa44_unpack_sk"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The secret key at sk, given byte by byte by skb, has rho,    *)
(* key and tr in its first 128 bytes, then the packed polynomials of s1 (4   *)
(* of 96 bytes each, from byte 128), s2 (4, from byte 512) and t0 (4 of 416  *)
(* bytes, from byte 896). The bytes of rho, tr and key are copied to rho, tr *)
(* and key, and the vectors of the unpacked polynomials of t0, s1 and s2 in  *)
(* the NTT domain to t0, s1 and s2, with 256 coefficients of 32 bits for     *)
(* each polynomial (see common/mldsa_native_polyvec.ml). The outputs and the *)
(* stack frame, of the function and its callees, are disjoint from each      *)
(* other, the code and the secret key.                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_UNPACK_SK_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!rho tr key t0 s1 s2 sk skb pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,4096); (s1,4096); (s2,4096);
          (word_sub stackpointer (word 80),80)] /\
        ALLPAIRS nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,4096); (s1,4096); (s2,4096);
          (word_sub stackpointer (word 80),80)]
         [(word pc,libmldsa_size); (sk,2560)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa44_unpack_sk) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [rho; tr; key; t0; s1; s2; sk] s /\
                  (!j. j < 2560
                       ==> read(memory :> bytes8(word_add sk (word j))) s =
                           skb j))
             (\s. read PC s = returnaddress /\
                  (!j. j < 32
                       ==> read(memory :> bytes8(word_add rho (word j))) s =
                           skb j) /\
                  (!j. j < 64
                       ==> read(memory :> bytes8(word_add tr (word j))) s =
                           skb(64 + j)) /\
                  (!j. j < 32
                       ==> read(memory :> bytes8(word_add key (word j))) s =
                           skb(32 + j)) /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add t0 (word(4 * i))))
                             s =
                           mld_polyvec_map mld_poly_ntt
                            (mld_polyvec_unpack 416 mld_polyt0_unpack
                              (\j. skb(896 + j))) i) /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add s1 (word(4 * i))))
                             s =
                           mld_polyvec_map mld_poly_ntt
                            (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                              (\j. skb(128 + j))) i) /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add s2 (word(4 * i))))
                             s =
                           mld_polyvec_map mld_poly_ntt
                            (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                              (\j. skb(512 + j))) i))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(rho,32); memory :> bytes(tr,64);
                memory :> bytes(key,32); memory :> bytes(t0,4096);
                memory :> bytes(s1,4096); memory :> bytes(s2,4096);
                memory :> bytes(word_sub stackpointer (word 80),80)])`;;

let MLDSA_NATIVE_UNPACK_SK_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_UNPACK_SK_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* secret key, t0, s1, s2, the stack frame and the table of the NTT (the     *)
(* copies rho, tr and key are only written), and the writes within the       *)
(* outputs and the stack frame.                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_UNPACK_SK_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e rho tr key t0 s1 s2 sk skb pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,4096); (s1,4096); (s2,4096);
          (word_sub stackpointer (word 80),80)] /\
        ALLPAIRS nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,4096); (s1,4096); (s2,4096);
          (word_sub stackpointer (word 80),80)]
         [(word pc,libmldsa_size); (sk,2560)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa44_unpack_sk) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [rho; tr; key; t0; s1; s2; sk] s /\
                  (!j. j < 2560
                       ==> read(memory :> bytes8(word_add sk (word j))) s =
                           skb j) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!j. j < 32
                       ==> read(memory :> bytes8(word_add rho (word j))) s =
                           skb j) /\
                  (!j. j < 64
                       ==> read(memory :> bytes8(word_add tr (word j))) s =
                           skb(64 + j)) /\
                  (!j. j < 32
                       ==> read(memory :> bytes8(word_add key (word j))) s =
                           skb(32 + j)) /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add t0 (word(4 * i))))
                             s =
                           mld_polyvec_map mld_poly_ntt
                            (mld_polyvec_unpack 416 mld_polyt0_unpack
                              (\j. skb(896 + j))) i) /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add s1 (word(4 * i))))
                             s =
                           mld_polyvec_map mld_poly_ntt
                            (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                              (\j. skb(128 + j))) i) /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add s2 (word(4 * i))))
                             s =
                           mld_polyvec_map mld_poly_ntt
                            (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                              (\j. skb(512 + j))) i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events rho tr key t0 s1 s2 sk pc
                                 (word_sub stackpointer (word 80))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [sk,2560; t0,4096; s1,4096; s2,4096;
                       word_sub stackpointer (word 80),80;
                       word(pc + rodata_mld_zetas),1024]
                      [rho,32; tr,64; key,32; t0,4096; s1,4096; s2,4096;
                       word_sub stackpointer (word 80),80]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(rho,32); memory :> bytes(tr,64);
                memory :> bytes(key,32); memory :> bytes(t0,4096);
                memory :> bytes(s1,4096); memory :> bytes(s2,4096);
                memory :> bytes(word_sub stackpointer (word 80),80)])`;;

let MLDSA_NATIVE_UNPACK_SK_44_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_UNPACK_SK_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_UNPACK_SK_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e rho tr key t0 s1 s2 sk pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,4096); (s1,4096); (s2,4096);
          (word_sub stackpointer (word 80),80)] /\
        ALLPAIRS nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,4096); (s1,4096); (s2,4096);
          (word_sub stackpointer (word 80),80)]
         [(word pc,libmldsa_size); (sk,2560)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa44_unpack_sk) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [rho; tr; key; t0; s1; s2; sk] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events rho tr key t0 s1 s2 sk pc
                                 (word_sub stackpointer (word 80))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [sk,2560; t0,4096; s1,4096; s2,4096;
                       word_sub stackpointer (word 80),80;
                       word(pc + rodata_mld_zetas),1024]
                      [rho,32; tr,64; key,32; t0,4096; s1,4096; s2,4096;
                       word_sub stackpointer (word 80),80]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(rho,32); memory :> bytes(tr,64);
                memory :> bytes(key,32); memory :> bytes(t0,4096);
                memory :> bytes(s1,4096); memory :> bytes(s2,4096);
                memory :> bytes(word_sub stackpointer (word 80),80)])`;;

let MLDSA_NATIVE_UNPACK_SK_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_UNPACK_SK_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
