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
(* libmlkem.ml), using the theorems for mlkem_keccakf1600_extract_bytes in   *)
(* the image. Its seventh argument, len, is passed on the stack, and as an   *)
(* unsigned int only the low 32 bits of its slot are read.                   *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/gcc12_O2/keccakf1600_extract_bytes_proof.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_keccakf1600x4_extract_bytes:
       +0x0: push   r15
       +0x2: mov    r15,rdx
       +0x5: mov    edx,r9d
       +0x8: push   r14
       +0xa: mov    r14,rcx
       +0xd: push   r13
       +0xf: mov    r13,r8
      +0x12: push   r12
      +0x14: push   rbp
      +0x15: mov    ebp,r9d
      +0x18: push   rbx
      +0x19: mov    rbx,rdi
      +0x1c: sub    rsp,0x8
      +0x20: mov    r12d,DWORD PTR [rsp+0x40]
      +0x25: mov    ecx,r12d
      +0x28: call   <mlkem_keccakf1600_extract_bytes>
      +0x2d: mov    ecx,r12d
      +0x30: mov    edx,ebp
      +0x32: mov    rsi,r15
      +0x35: lea    rdi,[rbx+0xc8]
      +0x3c: call   <mlkem_keccakf1600_extract_bytes>
      +0x41: mov    ecx,r12d
      +0x44: mov    edx,ebp
      +0x46: mov    rsi,r14
      +0x49: lea    rdi,[rbx+0x190]
      +0x50: call   <mlkem_keccakf1600_extract_bytes>
      +0x55: add    rsp,0x8
      +0x59: mov    ecx,r12d
      +0x5c: mov    edx,ebp
      +0x5e: lea    rdi,[rbx+0x258]
      +0x65: mov    rsi,r13
      +0x68: pop    rbx
      +0x69: pop    rbp
      +0x6a: pop    r12
      +0x6c: pop    r13
      +0x6e: pop    r14
      +0x70: pop    r15
      +0x72: jmp    <mlkem_keccakf1600_extract_bytes>
 ***)

let MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem_keccakf1600x4_extract_bytes"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The four states, each a 1600-bit word as for           *)
(* mlkem_keccakf1600_extract_bytes, are consecutive in memory.               *)
(* ------------------------------------------------------------------------- *)

let LOCAL_EXTRACT_BYTES_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let EXTRACT_BYTES_X4_CALL_TAC sv n =
  KECCAK_STATE_WBYTES_TAC sv THEN
  LOCAL_EXTRACT_BYTES_TAC [`read RDI s`; `read RSI s`; `off:num`; `len:num`;
                           sv; `pc:num`; `read RSP s`;
                           `read (memory :> bytes64(read RSP s)) s`] n;;

let MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
  = prove
 (`!a d0 d1 d2 d3 off len (S0:1600 word) (S1:1600 word) (S2:1600 word)
    (S3:1600 word) pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\ off + len <= 200 /\
        PAIRWISE nonoverlapping
         [(d0,len); (d1,len); (d2,len); (d3,len);
          (word_sub stackpointer (word 64),76)] /\
        ALLPAIRS nonoverlapping
         [(d0,len); (d1,len); (d2,len); (d3,len);
          (word_sub stackpointer (word 64),76)]
         [(word pc,libmlkem_size); (a,800)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + mlkem_keccakf1600x4_extract_bytes) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; d0; d1; d2; d3; word off] s /\
                  read (memory :> bytes32 (word_add stackpointer (word 8))) s =
                  word len /\
                  read (memory :> wbytes a) s = S0 /\
                  read (memory :> wbytes (word_add a (word 200))) s = S1 /\
                  read (memory :> wbytes (word_add a (word 400))) s = S2 /\
                  read (memory :> wbytes (word_add a (word 600))) s = S3)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> bytes(d0,len)) s =
                  (val S0 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                  read (memory :> bytes(d1,len)) s =
                  (val S1 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                  read (memory :> bytes(d2,len)) s =
                  (val S2 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                  read (memory :> bytes(d3,len)) s =
                  (val S3 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
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
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC
   (1--16) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  EXTRACT_BYTES_X4_CALL_TAC `S0:1600 word` 17 THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC
   (18--22) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  EXTRACT_BYTES_X4_CALL_TAC `S1:1600 word` 23 THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC
   (24--28) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  EXTRACT_BYTES_X4_CALL_TAC `S2:1600 word` 29 THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC
   (30--41) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  EXTRACT_BYTES_X4_CALL_TAC `S3:1600 word` 42 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let LOCAL_EXTRACT_BYTES_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `off:num`;
       `len:num`; `pc:num`; `read RSP s`;
       `read (memory :> bytes64(read RSP s)) s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `a:int64`; `d0:int64`; `d1:int64`;
                          `d2:int64`; `d3:int64`; `off:num`; `len:num`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
     forall e a d0 d1 d2 d3 off len pc stackpointer returnaddress.
       aligned 16 (word pc:int64) /\ off + len <= 200 /\
       PAIRWISE nonoverlapping
        [d0,len; d1,len; d2,len; d3,len;
         word_sub stackpointer (word 64),76] /\
       ALLPAIRS nonoverlapping
        [d0,len; d1,len; d2,len; d3,len;
         word_sub stackpointer (word 64),76]
        [word pc,libmlkem_size; a,800]
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + mlkem_keccakf1600x4_extract_bytes) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [a; d0; d1; d2; d3; word off] s /\
                 read (memory :> bytes32 (word_add stackpointer (word 8))) s =
                 word len /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a d0 d1 d2 d3 off len pc
                           (word_sub stackpointer (word 64)) returnaddress /\
                    memaccess_inbounds e2
                     [a,800; d0,len; d1,len; d2,len; d3,len;
                      word_sub stackpointer (word 64),76]
                     [d0,len; d1,len; d2,len; d3,len;
                      word_sub stackpointer (word 64),64]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(d0,len); memory :> bytes(d1,len);
                        memory :> bytes(d2,len); memory :> bytes(d3,len);
                        memory :> bytes(word_sub stackpointer (word 64),64)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_EXTRACT_BYTES" THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `d0:int64`; `d1:int64`; `d2:int64`;
    `d3:int64`; `off:num`; `len:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 64 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC
   (1--16) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  LOCAL_EXTRACT_BYTES_SAFETY_TAC "H_EXTRACT_BYTES" 17 THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC
   (18--22) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  LOCAL_EXTRACT_BYTES_SAFETY_TAC "H_EXTRACT_BYTES" 23 THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC
   (24--28) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  LOCAL_EXTRACT_BYTES_SAFETY_TAC "H_EXTRACT_BYTES" 29 THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC
   (30--41) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  LOCAL_EXTRACT_BYTES_SAFETY_TAC "H_EXTRACT_BYTES" 42 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, using that   *)
(* of mlkem_keccakf1600_extract_bytes for the states as 1600-bit words.      *)
(* ------------------------------------------------------------------------- *)

let EXTRACT_BYTES_X4_FULL_CALL_TAC sv n =
  KECCAK_STATE_WBYTES_TAC sv THEN
  REMOVE_THEN "H_EXTRACT_BYTES" (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `off:num`;
       `len:num`; sv; `pc:num`; `read RSP s`;
       `read (memory :> bytes64(read RSP s)) s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `a:int64`; `d0:int64`; `d1:int64`;
                          `d2:int64`; `d3:int64`; `off:num`; `len:num`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC "H_EXTRACT_BYTES" safety_th]);;

let MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (`exists f_events.
     forall e a d0 d1 d2 d3 off len (S0:1600 word) (S1:1600 word)
            (S2:1600 word) (S3:1600 word) pc stackpointer returnaddress.
       aligned 16 (word pc:int64) /\ off + len <= 200 /\
       PAIRWISE nonoverlapping
        [d0,len; d1,len; d2,len; d3,len;
         word_sub stackpointer (word 64),76] /\
       ALLPAIRS nonoverlapping
        [d0,len; d1,len; d2,len; d3,len;
         word_sub stackpointer (word 64),76]
        [word pc,libmlkem_size; a,800]
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + mlkem_keccakf1600x4_extract_bytes) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [a; d0; d1; d2; d3; word off] s /\
                 read (memory :> bytes32 (word_add stackpointer (word 8))) s =
                 word len /\
                 read (memory :> wbytes a) s = S0 /\
                 read (memory :> wbytes (word_add a (word 200))) s = S1 /\
                 read (memory :> wbytes (word_add a (word 400))) s = S2 /\
                 read (memory :> wbytes (word_add a (word 600))) s = S3 /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 read (memory :> bytes(d0,len)) s =
                 (val S0 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                 read (memory :> bytes(d1,len)) s =
                 (val S1 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                 read (memory :> bytes(d2,len)) s =
                 (val S2 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                 read (memory :> bytes(d3,len)) s =
                 (val S3 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a d0 d1 d2 d3 off len pc
                           (word_sub stackpointer (word 64)) returnaddress /\
                    memaccess_inbounds e2
                     [a,800; d0,len; d1,len; d2,len; d3,len;
                      word_sub stackpointer (word 64),76]
                     [d0,len; d1,len; d2,len; d3,len;
                      word_sub stackpointer (word 64),64]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(d0,len); memory :> bytes(d1,len);
                        memory :> bytes(d2,len); memory :> bytes(d3,len);
                        memory :> bytes(word_sub stackpointer (word 64),64)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_EXTRACT_BYTES" THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `d0:int64`; `d1:int64`; `d2:int64`;
    `d3:int64`; `off:num`; `len:num`; `S0:1600 word`; `S1:1600 word`;
    `S2:1600 word`; `S3:1600 word`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 64 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC
   (1--16) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  EXTRACT_BYTES_X4_FULL_CALL_TAC `S0:1600 word` 17 THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC
   (18--22) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  EXTRACT_BYTES_X4_FULL_CALL_TAC `S1:1600 word` 23 THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC
   (24--28) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  EXTRACT_BYTES_X4_FULL_CALL_TAC `S2:1600 word` 29 THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC
   (30--41) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  EXTRACT_BYTES_X4_FULL_CALL_TAC `S3:1600 word` 42 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
