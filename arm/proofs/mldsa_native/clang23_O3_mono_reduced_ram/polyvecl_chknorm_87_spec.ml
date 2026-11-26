(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Norm check of a vector of 7 polynomials: the statement. This is the code  *)
(* for mldsa87_polyvecl_chknorm (mld_polyvecl_chknorm in polyvec.c) from     *)
(* mldsa-native's portable C implementation compiled by clang 23 with -O3 as *)
(* a monolithic build with MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md). *)
(* Clang has inlined mld_poly_chknorm: the code is 7 loops of 256 iterations, *)
(* one per polynomial, each ORing the mask of a coefficient into its own     *)
(* accumulator register; the accumulators are ORed after the last loop. The  *)
(* function has no stack frame (its events do not mention the stack, so the  *)
(* frame in the statements has size 0) and clears the scratch registers      *)
(* before it returns.                                                        *)
(* It uses x18 as a scratch register, so the frame has MAYCHANGE [X18] added. *)
(* It is verified in the whole image (see libmldsa.ml) against               *)
(* mld_polyvec_chknorm of common/mldsa_native_polyvec.ml, and shown to be    *)
(* constant time and memory safe.                                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa87_polyvecl_chknorm:
       +0x0: mov     x9, xzr
       +0x4: mov     w8, wzr
       +0x8: ldrsw   x10, [x0, x9]
       +0xc: add     x9, x9, #0x4
      +0x10: cmp     x9, #0x400
      +0x14: mov     w11, w10
      +0x18: lsr     x10, x10, #31
      +0x1c: neg     w12, w11
      +0x20: bic     w11, w11, w10
      +0x24: and     w10, w12, w10
      +0x28: eon     w10, w10, w11
      +0x2c: add     w10, w1, w10
      +0x30: sxtw    x10, w10
      +0x34: lsr     x10, x10, #31
      +0x38: orr     w8, w8, w10
      +0x3c: b.ne    <mldsa87_polyvecl_chknorm+0x8>
      +0x40: mov     x10, xzr
      +0x44: mov     w9, wzr
      +0x48: add     x11, x0, #0x400
      +0x4c: ldrsw   x12, [x11, x10]
      +0x50: add     x10, x10, #0x4
      +0x54: cmp     x10, #0x400
      +0x58: mov     w13, w12
      +0x5c: lsr     x12, x12, #31
      +0x60: neg     w14, w13
      +0x64: bic     w13, w13, w12
      +0x68: and     w12, w14, w12
      +0x6c: eon     w12, w12, w13
      +0x70: add     w12, w1, w12
      +0x74: sxtw    x12, w12
      +0x78: lsr     x12, x12, #31
      +0x7c: orr     w9, w9, w12
      +0x80: b.ne    <mldsa87_polyvecl_chknorm+0x4c>
      +0x84: mov     x11, xzr
      +0x88: mov     w10, wzr
      +0x8c: add     x12, x0, #0x800
      +0x90: ldrsw   x13, [x12, x11]
      +0x94: add     x11, x11, #0x4
      +0x98: cmp     x11, #0x400
      +0x9c: mov     w14, w13
      +0xa0: lsr     x13, x13, #31
      +0xa4: neg     w15, w14
      +0xa8: bic     w14, w14, w13
      +0xac: and     w13, w15, w13
      +0xb0: eon     w13, w13, w14
      +0xb4: add     w13, w1, w13
      +0xb8: sxtw    x13, w13
      +0xbc: lsr     x13, x13, #31
      +0xc0: orr     w10, w10, w13
      +0xc4: b.ne    <mldsa87_polyvecl_chknorm+0x90>
      +0xc8: mov     x12, xzr
      +0xcc: mov     w11, wzr
      +0xd0: add     x13, x0, #0xc00
      +0xd4: ldrsw   x14, [x13, x12]
      +0xd8: add     x12, x12, #0x4
      +0xdc: cmp     x12, #0x400
      +0xe0: mov     w15, w14
      +0xe4: lsr     x14, x14, #31
      +0xe8: neg     w16, w15
      +0xec: bic     w15, w15, w14
      +0xf0: and     w14, w16, w14
      +0xf4: eon     w14, w14, w15
      +0xf8: add     w14, w1, w14
      +0xfc: sxtw    x14, w14
     +0x100: lsr     x14, x14, #31
     +0x104: orr     w11, w11, w14
     +0x108: b.ne    <mldsa87_polyvecl_chknorm+0xd4>
     +0x10c: mov     x13, xzr
     +0x110: mov     w12, wzr
     +0x114: add     x14, x0, #0x1, lsl #12
     +0x118: ldrsw   x15, [x14, x13]
     +0x11c: add     x13, x13, #0x4
     +0x120: cmp     x13, #0x400
     +0x124: mov     w16, w15
     +0x128: lsr     x15, x15, #31
     +0x12c: neg     w17, w16
     +0x130: bic     w16, w16, w15
     +0x134: and     w15, w17, w15
     +0x138: eon     w15, w15, w16
     +0x13c: add     w15, w1, w15
     +0x140: sxtw    x15, w15
     +0x144: lsr     x15, x15, #31
     +0x148: orr     w12, w12, w15
     +0x14c: b.ne    <mldsa87_polyvecl_chknorm+0x118>
     +0x150: mov     w15, #0x1400
     +0x154: mov     x14, xzr
     +0x158: mov     w13, wzr
     +0x15c: add     x15, x0, x15
     +0x160: ldrsw   x16, [x15, x14]
     +0x164: add     x14, x14, #0x4
     +0x168: cmp     x14, #0x400
     +0x16c: mov     w17, w16
     +0x170: lsr     x16, x16, #31
     +0x174: neg     w18, w17
     +0x178: bic     w17, w17, w16
     +0x17c: and     w16, w18, w16
     +0x180: eon     w16, w16, w17
     +0x184: add     w16, w1, w16
     +0x188: sxtw    x16, w16
     +0x18c: lsr     x16, x16, #31
     +0x190: orr     w13, w13, w16
     +0x194: b.ne    <mldsa87_polyvecl_chknorm+0x160>
     +0x198: mov     w16, #0x1800
     +0x19c: mov     x15, xzr
     +0x1a0: mov     w14, wzr
     +0x1a4: add     x16, x0, x16
     +0x1a8: ldrsw   x17, [x16, x15]
     +0x1ac: add     x15, x15, #0x4
     +0x1b0: cmp     x15, #0x400
     +0x1b4: mov     w18, w17
     +0x1b8: lsr     x17, x17, #31
     +0x1bc: neg     w0, w18
     +0x1c0: bic     w18, w18, w17
     +0x1c4: and     w17, w0, w17
     +0x1c8: eon     w17, w17, w18
     +0x1cc: add     w17, w1, w17
     +0x1d0: sxtw    x17, w17
     +0x1d4: lsr     x17, x17, #31
     +0x1d8: orr     w14, w14, w17
     +0x1dc: b.ne    <mldsa87_polyvecl_chknorm+0x1a8>
     +0x1e0: orr     w8, w9, w8
     +0x1e4: orr     w9, w11, w10
     +0x1e8: mov     x1, #0x0
     +0x1ec: orr     w8, w9, w8
     +0x1f0: orr     w9, w13, w12
     +0x1f4: mov     x10, #0x0
     +0x1f8: orr     w8, w9, w8
     +0x1fc: mov     x9, #0x0
     +0x200: mov     x11, #0x0
     +0x204: orr     w0, w14, w8
     +0x208: mov     x8, #0x0
     +0x20c: mov     x12, #0x0
     +0x210: mov     x13, #0x0
     +0x214: mov     x14, #0x0
     +0x218: mov     x15, #0x0
     +0x21c: mov     x16, #0x0
     +0x220: mov     x17, #0x0
     +0x224: mov     x18, #0x0
     +0x228: ret     
 ***)

let MLDSA_NATIVE_POLYVECL_CHKNORM_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa87_polyvecl_chknorm"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. For the vector x at v, 7 polynomials of 256 coefficients of  *)
(* 32 bits each (see common/mldsa_native_polyvec.ml), and the bound in the   *)
(* low 32 bits of bnd, the result is mld_polyvec_chknorm 7 x bnd: all ones   *)
(* if some coefficient is not below the bound in absolute value, zero        *)
(* otherwise.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_CHKNORM_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!v x bnd pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 0),0))
            [(v,7168); (word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read PC s = word (pc + mldsa87_polyvecl_chknorm) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [v; bnd] s /\
                  (!i. i < 1792
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  C_RETURN s = word_zx(mld_polyvec_chknorm 7 x (word_zx bnd)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(word_sub stackpointer (word 0),0)])`;;

let MLDSA_NATIVE_POLYVECL_CHKNORM_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLYVECL_CHKNORM_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses and the bound only, with all       *)
(* accesses within the vector and the stack frame, and the writes within the *)
(* stack frame.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_CHKNORM_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e v x bnd pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 0),0))
            [(v,7168); (word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read PC s = word (pc + mldsa87_polyvecl_chknorm) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [v; bnd] s /\
                  (!i. i < 1792
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  C_RETURN s =
                    word_zx(mld_polyvec_chknorm 7 x (word_zx bnd)) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events v bnd pc (word_sub stackpointer (word 0))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [v,7168; word_sub stackpointer (word 0),0]
                      [word_sub stackpointer (word 0),0]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(word_sub stackpointer (word 0),0)])`;;

let MLDSA_NATIVE_POLYVECL_CHKNORM_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYVECL_CHKNORM_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_CHKNORM_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e v bnd pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 0),0))
            [(v,7168); (word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read PC s = word (pc + mldsa87_polyvecl_chknorm) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [v; bnd] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events v bnd pc (word_sub stackpointer (word 0))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [v,7168; word_sub stackpointer (word 0),0]
                      [word_sub stackpointer (word 0),0]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(word_sub stackpointer (word 0),0)])`;;

let MLDSA_NATIVE_POLYVECL_CHKNORM_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYVECL_CHKNORM_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
