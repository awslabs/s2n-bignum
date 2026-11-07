(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* XOR of bytes into a Keccak state. This is the code for                    *)
(* mlkem_keccakf1600_xor_bytes from mlkem-native's portable C implementation *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md), which XORs len  *)
(* bytes of data into the 200-byte state starting at byte off. It is         *)
(* verified in the whole image (see libmlkem.ml).                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_keccakf1600_xor_bytes:
       +0x0: mov     w2, w2
       +0x4: cbz     w3, <mlkem_keccakf1600_xor_bytes+0x34>
       +0x8: mov     w5, w3
       +0xc: add     x3, x0, x2
      +0x10: mov     x0, #0x0
      +0x14: nop
      +0x18: ldrb    w2, [x3, x0]
      +0x1c: ldrb    w4, [x1, x0]
      +0x20: eor     w2, w2, w4
      +0x24: strb    w2, [x3, x0]
      +0x28: add     x0, x0, #0x1
      +0x2c: cmp     x5, x0
      +0x30: b.ne    <mlkem_keccakf1600_xor_bytes+0x18>
      +0x34: ret
 ***)

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [layout_range "mlkem_keccakf1600_xor_bytes"];;

(*** The zero-extended arguments off and len, and the test of len ***)

let XOR_BYTES_ARGS_TAC =
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  FIRST_ASSUM(fun th ->
    if concl th <> `~(len = 0)` then NO_TAC else
    RULE_ASSUM_TAC(fun th' ->
      if concl th' = concl th then th' else REWRITE_RULE[th] th'));;

(* ------------------------------------------------------------------------- *)
(* The state after i of the bytes of the data m have been XORed into it, as  *)
(* bytes. Only byte off + i changes in the next step.                        *)
(* ------------------------------------------------------------------------- *)

let BYTE_UPDATE_STMT =
  `!x c k j.
        x < 2 EXP (8 * k) /\ c < 256
        ==> ((x + 2 EXP (8 * k) * c) DIV 2 EXP (8 * j)) MOD 256 =
            if j = k then c else (x DIV 2 EXP (8 * j)) MOD 256`;;

let BYTE_UPDATE = assume_spec BYTE_UPDATE_STMT;;

let XOR_BYTES_STEP_STMT =
  `!(S:1600 word) m off i j.
        off + i < 200 /\ j < 200
        ==> word_subword
             (word_xor S (word(2 EXP (8 * off) *
                               m MOD 2 EXP (8 * (i + 1)))))
             (8 * j,8):byte =
            if j = off + i
            then word_xor
                  (word_subword
                    (word_xor S (word(2 EXP (8 * off) * m MOD 2 EXP (8 * i))))
                    (8 * j,8))
                  (word((m DIV 2 EXP (8 * i)) MOD 256))
            else word_subword
                  (word_xor S (word(2 EXP (8 * off) * m MOD 2 EXP (8 * i))))
                  (8 * j,8)`;;

let XOR_BYTES_STEP = assume_spec XOR_BYTES_STEP_STMT;;

(*** The invariant for the bytes other than byte t ***)

let XOR_BYTES_RESTRICT_RULE t th =
  let j,bod = dest_forall(concl th) in
  let p,q = dest_imp bod in
  let p' = mk_conj(p,mk_neg(mk_eq(j,t))) in
  GEN j (DISCH p' (MP (SPEC j th) (CONJUNCT1(ASSUME p'))));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As in keccak_absorb in common/fips202.ml, the state is *)
(* a 1600-bit word S. The len bytes of data, as a number m, are XORed into   *)
(* it starting at byte off, giving word_xor S (word(2 EXP (8 * off) * m)).   *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a d off len (S:1600 word) m pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        off + len <= 200 /\
        ALL (nonoverlapping (a,200)) [(word pc,libmlkem_size); (d,len)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + mlkem_keccakf1600_xor_bytes) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; d; word off; word len] s /\
                  read (memory :> wbytes a) s = S /\
                  read (memory :> bytes(d,len)) s = m)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes a) s =
                  word_xor S (word(2 EXP (8 * off) * m)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,200)])`;;

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. The events depend on off as well   *)
(* as len, so the theorem is stated directly rather than by mk_safety_spec.  *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e a d off len pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           off + len <= 200 /\
           ALL (nonoverlapping (a,200)) [word pc,libmlkem_size; d,len]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + mlkem_keccakf1600_xor_bytes) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; d; word off; word len] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a d off len pc returnaddress /\
                         memaccess_inbounds e2 [a,200; d,len] [a,200]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (a,200)])`;;

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, as for       *)
(* mlkem_keccakf1600_extract_bytes.                                          *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
       forall e a d off len (S:1600 word) m pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           off + len <= 200 /\
           ALL (nonoverlapping (a,200)) [word pc,libmlkem_size; d,len]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + mlkem_keccakf1600_xor_bytes) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; d; word off; word len] s /\
                    read (memory :> wbytes a) s = S /\
                    read (memory :> bytes(d,len)) s = m /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    read (memory :> wbytes a) s =
                    word_xor S (word(2 EXP (8 * off) * m)) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a d off len pc returnaddress /\
                         memaccess_inbounds e2 [a,200; d,len] [a,200]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (a,200)])`;;

let MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;
