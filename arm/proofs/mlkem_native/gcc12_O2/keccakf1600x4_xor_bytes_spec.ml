(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* XOR of bytes into four Keccak states. This is the code for                *)
(* mlkem_keccakf1600x4_xor_bytes from mlkem-native's portable C              *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md),  *)
(* which calls mlkem_keccakf1600_xor_bytes for each of the states, the last  *)
(* time as a tail call. It is verified in the whole image (see               *)
(* libmlkem.ml), using the theorems for                                      *)
(* mlkem_keccakf1600_xor_bytes in the image.                                 *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/keccakf1600_xor_bytes_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_keccakf1600x4_xor_bytes:
       +0x0: stp     x19, x20, [sp, #-64]!
       +0x4: mov     w19, w5
       +0x8: mov     w20, w6
       +0xc: stp     x21, x22, [sp, #16]
      +0x10: mov     x22, x4
      +0x14: mov     x21, x0
      +0x18: stp     x23, x24, [sp, #32]
      +0x1c: mov     x24, x2
      +0x20: mov     x23, x3
      +0x24: mov     w2, w5
      +0x28: mov     w3, w6
      +0x2c: str     x30, [sp, #48]
      +0x30: bl      <mlkem_keccakf1600_xor_bytes>
      +0x34: mov     w3, w20
      +0x38: mov     w2, w19
      +0x3c: mov     x1, x24
      +0x40: add     x0, x21, #0xc8
      +0x44: bl      <mlkem_keccakf1600_xor_bytes>
      +0x48: mov     w3, w20
      +0x4c: mov     w2, w19
      +0x50: mov     x1, x23
      +0x54: add     x0, x21, #0x190
      +0x58: bl      <mlkem_keccakf1600_xor_bytes>
      +0x5c: ldp     x23, x24, [sp, #32]
      +0x60: mov     w3, w20
      +0x64: ldr     x30, [sp, #48]
      +0x68: mov     w2, w19
      +0x6c: mov     x1, x22
      +0x70: add     x0, x21, #0x258
      +0x74: ldp     x21, x22, [sp, #16]
      +0x78: ldp     x19, x20, [sp], #64
      +0x7c: b       <mlkem_keccakf1600_xor_bytes>
 ***)

let MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [layout_range "mlkem_keccakf1600x4_xor_bytes"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The four states, each a 1600-bit word as for           *)
(* mlkem_keccakf1600_xor_bytes, are consecutive in memory. The data for the  *)
(* states, which are only read, may overlap, e.g. all be the same.           *)
(* ------------------------------------------------------------------------- *)

let LOCAL_XOR_BYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let XOR_BYTES_X4_CALL_TAC sv dv n =
  KECCAK_STATE_WBYTES_TAC sv THEN
  LOCAL_XOR_BYTES_TAC [`read X0 s`; `read X1 s`; `off:num`; `len:num`;
                       sv; dv; `pc:num`; `read X30 s`] n THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

let MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a d0 d1 d2 d3 off len (S0:1600 word) (S1:1600 word) (S2:1600 word)
    (S3:1600 word) m0 m1 m2 m3 pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ off + len <= 200 /\
        ALLPAIRS nonoverlapping
         [(a,800); (word_sub stackpointer (word 64),64)]
         [(word pc,libmlkem_size); (d0,len); (d1,len); (d2,len); (d3,len)] /\
        nonoverlapping (a,800) (word_sub stackpointer (word 64),64)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + mlkem_keccakf1600x4_xor_bytes) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; d0; d1; d2; d3; word off; word len] s /\
                  read (memory :> wbytes a) s = S0 /\
                  read (memory :> wbytes (word_add a (word 200))) s = S1 /\
                  read (memory :> wbytes (word_add a (word 400))) s = S2 /\
                  read (memory :> wbytes (word_add a (word 600))) s = S3 /\
                  read (memory :> bytes(d0,len)) s = m0 /\
                  read (memory :> bytes(d1,len)) s = m1 /\
                  read (memory :> bytes(d2,len)) s = m2 /\
                  read (memory :> bytes(d3,len)) s = m3)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes a) s =
                  word_xor S0 (word(2 EXP (8 * off) * m0)) /\
                  read (memory :> wbytes (word_add a (word 200))) s =
                  word_xor S1 (word(2 EXP (8 * off) * m1)) /\
                  read (memory :> wbytes (word_add a (word 400))) s =
                  word_xor S2 (word(2 EXP (8 * off) * m2)) /\
                  read (memory :> wbytes (word_add a (word 600))) s =
                  word_xor S3 (word(2 EXP (8 * off) * m3)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,800);
                         memory :> bytes(word_sub stackpointer
                                                  (word 64),64)])`;;

let MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly as for             *)
(* mlkem_keccakf1600_xor_bytes.                                              *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let LOCAL_XOR_BYTES_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `off:num`;
       `len:num`; `pc:num`; `read X30 s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `a:int64`; `d0:int64`; `d1:int64`;
                          `d2:int64`; `d3:int64`; `off:num`; `len:num`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e a d0 d1 d2 d3 off len pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ off + len <= 200 /\
       ALLPAIRS nonoverlapping
        [a,800; word_sub stackpointer (word 64),64]
        [word pc,libmlkem_size; d0,len; d1,len; d2,len; d3,len] /\
       nonoverlapping (a,800) (word_sub stackpointer (word 64),64)
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read PC s = word (pc + mlkem_keccakf1600x4_xor_bytes) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [a; d0; d1; d2; d3; word off; word len] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a d0 d1 d2 d3 off len pc
                           (word_sub stackpointer (word 64)) returnaddress /\
                    memaccess_inbounds e2
                     [a,800; d0,len; d1,len; d2,len; d3,len;
                      word_sub stackpointer (word 64),64]
                     [a,800; word_sub stackpointer (word 64),64]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,800);
                        memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, using that   *)
(* of mlkem_keccakf1600_xor_bytes for the states as 1600-bit words.          *)
(* ------------------------------------------------------------------------- *)

let XOR_BYTES_X4_CS_CALL_TAC sv dv n =
  KECCAK_STATE_WBYTES_TAC sv THEN
  REMOVE_THEN "H_XOR_BYTES" (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `off:num`;
       `len:num`; sv; dv; `pc:num`; `read X30 s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `a:int64`; `d0:int64`; `d1:int64`;
                          `d2:int64`; `d3:int64`; `off:num`; `len:num`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC "H_XOR_BYTES" safety_th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

let MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
     forall e a d0 d1 d2 d3 off len (S0:1600 word) (S1:1600 word)
            (S2:1600 word) (S3:1600 word) m0 m1 m2 m3
            pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ off + len <= 200 /\
       ALLPAIRS nonoverlapping
        [a,800; word_sub stackpointer (word 64),64]
        [word pc,libmlkem_size; d0,len; d1,len; d2,len; d3,len] /\
       nonoverlapping (a,800) (word_sub stackpointer (word 64),64)
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read PC s = word (pc + mlkem_keccakf1600x4_xor_bytes) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [a; d0; d1; d2; d3; word off; word len] s /\
                 read (memory :> wbytes a) s = S0 /\
                 read (memory :> wbytes (word_add a (word 200))) s = S1 /\
                 read (memory :> wbytes (word_add a (word 400))) s = S2 /\
                 read (memory :> wbytes (word_add a (word 600))) s = S3 /\
                 read (memory :> bytes(d0,len)) s = m0 /\
                 read (memory :> bytes(d1,len)) s = m1 /\
                 read (memory :> bytes(d2,len)) s = m2 /\
                 read (memory :> bytes(d3,len)) s = m3 /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 read (memory :> wbytes a) s =
                 word_xor S0 (word(2 EXP (8 * off) * m0)) /\
                 read (memory :> wbytes (word_add a (word 200))) s =
                 word_xor S1 (word(2 EXP (8 * off) * m1)) /\
                 read (memory :> wbytes (word_add a (word 400))) s =
                 word_xor S2 (word(2 EXP (8 * off) * m2)) /\
                 read (memory :> wbytes (word_add a (word 600))) s =
                 word_xor S3 (word(2 EXP (8 * off) * m3)) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a d0 d1 d2 d3 off len pc
                           (word_sub stackpointer (word 64)) returnaddress /\
                    memaccess_inbounds e2
                     [a,800; d0,len; d1,len; d2,len; d3,len;
                      word_sub stackpointer (word 64),64]
                     [a,800; word_sub stackpointer (word 64),64]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,800);
                        memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;
