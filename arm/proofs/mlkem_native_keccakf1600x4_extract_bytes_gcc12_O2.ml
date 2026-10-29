(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Extraction of bytes from four Keccak states. This is the code for         *)
(* mlkem_keccakf1600x4_extract_bytes from mlkem-native's portable C          *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md),  *)
(* which calls mlkem_keccakf1600_extract_bytes for each of the states, the   *)
(* last time as a tail call. It is verified in the whole image (see          *)
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x2cd0, using  *)
(* the theorems for mlkem_keccakf1600_extract_bytes at 0x2c60 in the image.  *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_keccakf1600_extract_bytes_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    2cd0: stp     x19, x20, [sp, #-64]!
    2cd4: mov     w19, w5
    2cd8: mov     w20, w6
    2cdc: stp     x21, x22, [sp, #16]
    2ce0: mov     x22, x4
    2ce4: mov     x21, x0
    2ce8: stp     x23, x24, [sp, #32]
    2cec: mov     x24, x2
    2cf0: mov     x23, x3
    2cf4: mov     w2, w5
    2cf8: mov     w3, w6
    2cfc: str     x30, [sp, #48]
    2d00: bl      2c60 <mlkem_keccakf1600_extract_bytes>
    2d04: mov     w3, w20
    2d08: mov     w2, w19
    2d0c: mov     x1, x24
    2d10: add     x0, x21, #0xc8
    2d14: bl      2c60 <mlkem_keccakf1600_extract_bytes>
    2d18: mov     w3, w20
    2d1c: mov     w2, w19
    2d20: mov     x1, x23
    2d24: add     x0, x21, #0x190
    2d28: bl      2c60 <mlkem_keccakf1600_extract_bytes>
    2d2c: ldp     x23, x24, [sp, #32]
    2d30: mov     w3, w20
    2d34: ldr     x30, [sp, #48]
    2d38: mov     w2, w19
    2d3c: mov     x1, x22
    2d40: add     x0, x21, #0x258
    2d44: ldp     x21, x22, [sp, #16]
    2d48: ldp     x19, x20, [sp], #64
    2d4c: b       2c60 <mlkem_keccakf1600_extract_bytes>
 ***)

let MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x2cd0,0x2d50];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The four states, each a 1600-bit word as for           *)
(* mlkem_keccakf1600_extract_bytes, are consecutive in memory.               *)
(* ------------------------------------------------------------------------- *)

let LOCAL_EXTRACT_BYTES_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let EXTRACT_BYTES_X4_CALL_TAC sv n =
  KECCAK_STATE_WBYTES_TAC sv THEN
  LOCAL_EXTRACT_BYTES_TAC [`read X0 s`; `read X1 s`; `off:num`; `len:num`;
                           sv; `pc:num`; `read X30 s`] n;;

let MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
  = prove
 (`!a d0 d1 d2 d3 off len (S0:1600 word) (S1:1600 word) (S2:1600 word)
    (S3:1600 word) pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\ off + len <= 200 /\
        PAIRWISE nonoverlapping
         [(d0,len); (d1,len); (d2,len); (d3,len);
          (word_sub stackpointer (word 64),64)] /\
        ALLPAIRS nonoverlapping
         [(d0,len); (d1,len); (d2,len); (d3,len);
          (word_sub stackpointer (word 64),64)]
         [(word pc,0x6480); (a,800)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x2cd0) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; d0; d1; d2; d3; word off; word len] s /\
                  read (memory :> wbytes a) s = S0 /\
                  read (memory :> wbytes (word_add a (word 200))) s = S1 /\
                  read (memory :> wbytes (word_add a (word 400))) s = S2 /\
                  read (memory :> wbytes (word_add a (word 600))) s = S3)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(d0,len)) s =
                  (val S0 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                  read (memory :> bytes(d1,len)) s =
                  (val S1 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                  read (memory :> bytes(d2,len)) s =
                  (val S2 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                  read (memory :> bytes(d3,len)) s =
                  (val S3 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(d0,len); memory :> bytes(d1,len);
                         memory :> bytes(d2,len); memory :> bytes(d3,len);
                         memory :> bytes(word_sub stackpointer
                                                  (word 64),64)])`,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `d0:int64`; `d1:int64`; `d2:int64`; `d3:int64`;
    `off:num`; `len:num`; `S0:1600 word`; `S1:1600 word`; `S2:1600 word`;
    `S3:1600 word`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 64 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  ENSURES_PRESERVED_TAC "x24_init" `X24` THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC
   (1--13) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  EXTRACT_BYTES_X4_CALL_TAC `S0:1600 word` 14 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC
   (15--19) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  EXTRACT_BYTES_X4_CALL_TAC `S1:1600 word` 20 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC
   (21--25) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  EXTRACT_BYTES_X4_CALL_TAC `S2:1600 word` 26 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC
   (27--35) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  EXTRACT_BYTES_X4_CALL_TAC `S3:1600 word` 36 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly as for             *)
(* mlkem_keccakf1600_extract_bytes.                                          *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let LOCAL_EXTRACT_BYTES_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `off:num`;
       `len:num`; `pc:num`; `read X30 s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `a:int64`; `d0:int64`; `d1:int64`;
                          `d2:int64`; `d3:int64`; `off:num`; `len:num`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
     forall e a d0 d1 d2 d3 off len pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
       aligned 16 stackpointer /\ off + len <= 200 /\
       PAIRWISE nonoverlapping
        [d0,len; d1,len; d2,len; d3,len;
         word_sub stackpointer (word 64),64] /\
       ALLPAIRS nonoverlapping
        [d0,len; d1,len; d2,len; d3,len;
         word_sub stackpointer (word 64),64]
        [word pc,0x6480; a,800]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read PC s = word (pc + 0x2cd0) /\
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
                     [d0,len; d1,len; d2,len; d3,len;
                      word_sub stackpointer (word 64),64]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(d0,len); memory :> bytes(d1,len);
                        memory :> bytes(d2,len); memory :> bytes(d3,len);
                        memory :> bytes(word_sub stackpointer (word 64),64)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_EXTRACT_BYTES" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  ENSURES_PRESERVED_TAC "x24_init" `X24` THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC
   (1--13) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  LOCAL_EXTRACT_BYTES_SAFETY_TAC "H_EXTRACT_BYTES" 14 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC
   (15--19) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  LOCAL_EXTRACT_BYTES_SAFETY_TAC "H_EXTRACT_BYTES" 20 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC
   (21--25) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  LOCAL_EXTRACT_BYTES_SAFETY_TAC "H_EXTRACT_BYTES" 26 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC
   (27--35) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  LOCAL_EXTRACT_BYTES_SAFETY_TAC "H_EXTRACT_BYTES" 36 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
