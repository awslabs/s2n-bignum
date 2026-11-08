(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a polynomial with 3 bits per coefficient, of 2 - a: the      *)
(* statement. This is the code for mldsa44_polyeta_unpack                    *)
(* (mld_polyeta_unpack in poly_kl.c with MLDSA_ETA = 2, for ML-DSA-44) from  *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mldsa_native/README.md), which reads 3 bytes for each 8 coefficients,     *)
(* stores the masked fields and then 2 - a over them, four coefficients at a *)
(* time from a vector register. It is verified in the whole image (see       *)
(* libmldsa.ml) against mld_polyeta_unpack_2 of                              *)
(* common/mldsa_native_packing.ml. It is also shown to be constant time and  *)
(* memory safe.                                                              *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "common/mldsa_native_packing.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_polyeta_unpack:
       +0x0: movi    v2.4s, #0x2
       +0x4: add     x5, x1, #0x60
       +0x8: ldrb    w2, [x1]
       +0xc: add     x1, x1, #0x3
      +0x10: add     x0, x0, #0x20
      +0x14: and     w2, w2, #0x7
      +0x18: stur    w2, [x0, #-32]
      +0x1c: fmov    s1, w2
      +0x20: ldurb   w3, [x1, #-3]
      +0x24: ubfx    x3, x3, #3, #3
      +0x28: stur    w3, [x0, #-28]
      +0x2c: ldurb   w4, [x1, #-2]
      +0x30: mov     v1.s[1], w3
      +0x34: ldurb   w2, [x1, #-3]
      +0x38: lsl     w3, w4, #2
      +0x3c: orr     w2, w3, w2, lsr #6
      +0x40: and     w2, w2, #0x7
      +0x44: stur    w2, [x0, #-24]
      +0x48: ldurb   w3, [x1, #-2]
      +0x4c: mov     v1.s[2], w2
      +0x50: ubfx    x3, x3, #1, #3
      +0x54: stur    w3, [x0, #-20]
      +0x58: ldurb   w2, [x1, #-2]
      +0x5c: mov     v1.s[3], w3
      +0x60: ubfx    x2, x2, #4, #3
      +0x64: stur    w2, [x0, #-16]
      +0x68: fmov    d0, x2
      +0x6c: ldurb   w3, [x1, #-1]
      +0x70: sub     v1.4s, v2.4s, v1.4s
      +0x74: ldurb   w2, [x1, #-2]
      +0x78: lsl     w3, w3, #1
      +0x7c: orr     w2, w3, w2, lsr #7
      +0x80: and     w2, w2, #0x7
      +0x84: stur    w2, [x0, #-12]
      +0x88: ldurb   w3, [x1, #-1]
      +0x8c: mov     v0.s[1], w2
      +0x90: ubfx    x2, x3, #2, #3
      +0x94: stur    w2, [x0, #-8]
      +0x98: ldurb   w3, [x1, #-1]
      +0x9c: mov     v0.s[2], w2
      +0xa0: stur    q1, [x0, #-32]
      +0xa4: fmov    s1, w3
      +0xa8: ushr    v1.2s, v1.2s, #5
      +0xac: mov     v0.s[3], v1.s[0]
      +0xb0: sub     v0.4s, v2.4s, v0.4s
      +0xb4: stur    q0, [x0, #-16]
      +0xb8: cmp     x5, x1
      +0xbc: b.ne    <mldsa44_polyeta_unpack+0x8>
      +0xc0: ret
 ***)

let MLDSA_NATIVE_POLYETA_UNPACK_44_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_polyeta_unpack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (a,96)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa44_polyeta_unpack) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 96
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j))
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add r (word(4 * i))))
                            s = mld_polyeta_unpack_2 b i)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYETA_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYETA_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the writes within the outputs.                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (a,96)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa44_polyeta_unpack) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 96
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r (word(4 * i))))
                             s = mld_polyeta_unpack_2 b i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc returnaddress /\
                     memaccess_inbounds e2 [a,96; r,1024] [r,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYETA_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYETA_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (a,96)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa44_polyeta_unpack) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc returnaddress /\
                     memaccess_inbounds e2 [a,96; r,1024] [r,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYETA_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYETA_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
