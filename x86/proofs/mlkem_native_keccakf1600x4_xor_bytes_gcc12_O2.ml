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
(* mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x3df0, using  *)
(* the theorems for mlkem_keccakf1600_xor_bytes at 0x3d40 in the image. As   *)
(* for mlkem_keccakf1600x4_extract_bytes, its seventh argument, len, is      *)
(* passed on the stack, and only the low 32 bits of its slot are read.       *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_keccakf1600_xor_bytes_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    3df0: push   r15
    3df2: mov    r15,rdx
    3df5: mov    edx,r9d
    3df8: push   r14
    3dfa: mov    r14,rcx
    3dfd: push   r13
    3dff: mov    r13,r8
    3e02: push   r12
    3e04: push   rbp
    3e05: mov    ebp,r9d
    3e08: push   rbx
    3e09: mov    rbx,rdi
    3e0c: sub    rsp,0x8
    3e10: mov    r12d,DWORD PTR [rsp+0x40]
    3e15: mov    ecx,r12d
    3e18: call   3d40 <mlkem_keccakf1600_xor_bytes>
    3e1d: mov    ecx,r12d
    3e20: mov    edx,ebp
    3e22: mov    rsi,r15
    3e25: lea    rdi,[rbx+0xc8]
    3e2c: call   3d40 <mlkem_keccakf1600_xor_bytes>
    3e31: mov    ecx,r12d
    3e34: mov    edx,ebp
    3e36: mov    rsi,r14
    3e39: lea    rdi,[rbx+0x190]
    3e40: call   3d40 <mlkem_keccakf1600_xor_bytes>
    3e45: add    rsp,0x8
    3e49: mov    ecx,r12d
    3e4c: mov    edx,ebp
    3e4e: lea    rdi,[rbx+0x258]
    3e55: mov    rsi,r13
    3e58: pop    rbx
    3e59: pop    rbp
    3e5a: pop    r12
    3e5c: pop    r13
    3e5e: pop    r14
    3e60: pop    r15
    3e62: jmp    3d40 <mlkem_keccakf1600_xor_bytes>
 ***)

let MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x3df0,0x3e67];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The four states, each a 1600-bit word as for           *)
(* mlkem_keccakf1600_xor_bytes, are consecutive in memory. The data for the  *)
(* states, which are only read, may overlap, e.g. all be the same.           *)
(* ------------------------------------------------------------------------- *)

let LOCAL_XOR_BYTES_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let XOR_BYTES_X4_CALL_TAC sv dv n =
  KECCAK_STATE_WBYTES_TAC sv THEN
  LOCAL_XOR_BYTES_TAC [`read RDI s`; `read RSI s`; `off:num`; `len:num`;
                       sv; dv; `pc:num`; `read RSP s`;
                       `read (memory :> bytes64(read RSP s)) s`] n THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

let MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!a d0 d1 d2 d3 off len (S0:1600 word) (S1:1600 word) (S2:1600 word)
    (S3:1600 word) m0 m1 m2 m3 pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\ off + len <= 200 /\
        ALLPAIRS nonoverlapping
         [(a,800); (word_sub stackpointer (word 64),76)]
         [(word pc,0x82a0); (d0,len); (d1,len); (d2,len); (d3,len)] /\
        nonoverlapping (a,800) (word_sub stackpointer (word 64),76)
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x3df0) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; d0; d1; d2; d3; word off] s /\
                  read (memory :> bytes32 (word_add stackpointer (word 8))) s =
                  word len /\
                  read (memory :> wbytes a) s = S0 /\
                  read (memory :> wbytes (word_add a (word 200))) s = S1 /\
                  read (memory :> wbytes (word_add a (word 400))) s = S2 /\
                  read (memory :> wbytes (word_add a (word 600))) s = S3 /\
                  read (memory :> bytes(d0,len)) s = m0 /\
                  read (memory :> bytes(d1,len)) s = m1 /\
                  read (memory :> bytes(d2,len)) s = m2 /\
                  read (memory :> bytes(d3,len)) s = m3)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> wbytes a) s =
                  word_xor S0 (word(2 EXP (8 * off) * m0)) /\
                  read (memory :> wbytes (word_add a (word 200))) s =
                  word_xor S1 (word(2 EXP (8 * off) * m1)) /\
                  read (memory :> wbytes (word_add a (word 400))) s =
                  word_xor S2 (word(2 EXP (8 * off) * m2)) /\
                  read (memory :> wbytes (word_add a (word 600))) s =
                  word_xor S3 (word(2 EXP (8 * off) * m3)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,800);
                         memory :> bytes(word_sub stackpointer
                                                  (word 64),64)])`,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `d0:int64`; `d1:int64`; `d2:int64`; `d3:int64`;
    `off:num`; `len:num`; `S0:1600 word`; `S1:1600 word`; `S2:1600 word`;
    `S3:1600 word`; `m0:num`; `m1:num`; `m2:num`; `m3:num`; `pc:num`] THEN
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
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC
   (1--16) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  XOR_BYTES_X4_CALL_TAC `S0:1600 word` `m0:num` 17 THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC
   (18--22) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  XOR_BYTES_X4_CALL_TAC `S1:1600 word` `m1:num` 23 THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC
   (24--28) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  XOR_BYTES_X4_CALL_TAC `S2:1600 word` `m2:num` 29 THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC
   (30--41) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  XOR_BYTES_X4_CALL_TAC `S3:1600 word` `m3:num` 42 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let LOCAL_XOR_BYTES_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `off:num`;
       `len:num`; `pc:num`; `read RSP s`;
       `read (memory :> bytes64(read RSP s)) s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `a:int64`; `d0:int64`; `d1:int64`;
                          `d2:int64`; `d3:int64`; `off:num`; `len:num`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
     forall e a d0 d1 d2 d3 off len pc stackpointer returnaddress.
       aligned 16 (word pc:int64) /\ off + len <= 200 /\
       ALLPAIRS nonoverlapping
        [a,800; word_sub stackpointer (word 64),76]
        [word pc,0x82a0; d0,len; d1,len; d2,len; d3,len] /\
       nonoverlapping (a,800) (word_sub stackpointer (word 64),76)
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + 0x3df0) /\
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
                     [a,800; word_sub stackpointer (word 64),64]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,800);
                        memory :> bytes(word_sub stackpointer (word 64),64)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_XOR_BYTES" THEN
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
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC
   (1--16) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  LOCAL_XOR_BYTES_SAFETY_TAC "H_XOR_BYTES" 17 THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC
   (18--22) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  LOCAL_XOR_BYTES_SAFETY_TAC "H_XOR_BYTES" 23 THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC
   (24--28) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  LOCAL_XOR_BYTES_SAFETY_TAC "H_XOR_BYTES" 29 THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC
   (30--41) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  LOCAL_XOR_BYTES_SAFETY_TAC "H_XOR_BYTES" 42 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, using that   *)
(* of mlkem_keccakf1600_xor_bytes for the states as 1600-bit words.          *)
(* ------------------------------------------------------------------------- *)

let XOR_BYTES_X4_FULL_CALL_TAC sv dv n =
  KECCAK_STATE_WBYTES_TAC sv THEN
  REMOVE_THEN "H_XOR_BYTES" (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `off:num`;
       `len:num`; sv; dv; `pc:num`; `read RSP s`;
       `read (memory :> bytes64(read RSP s)) s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `a:int64`; `d0:int64`; `d1:int64`;
                          `d2:int64`; `d3:int64`; `off:num`; `len:num`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC "H_XOR_BYTES" safety_th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

let MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (`exists f_events.
     forall e a d0 d1 d2 d3 off len (S0:1600 word) (S1:1600 word)
            (S2:1600 word) (S3:1600 word) m0 m1 m2 m3
            pc stackpointer returnaddress.
       aligned 16 (word pc:int64) /\ off + len <= 200 /\
       ALLPAIRS nonoverlapping
        [a,800; word_sub stackpointer (word 64),76]
        [word pc,0x82a0; d0,len; d1,len; d2,len; d3,len] /\
       nonoverlapping (a,800) (word_sub stackpointer (word 64),76)
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + 0x3df0) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [a; d0; d1; d2; d3; word off] s /\
                 read (memory :> bytes32 (word_add stackpointer (word 8))) s =
                 word len /\
                 read (memory :> wbytes a) s = S0 /\
                 read (memory :> wbytes (word_add a (word 200))) s = S1 /\
                 read (memory :> wbytes (word_add a (word 400))) s = S2 /\
                 read (memory :> wbytes (word_add a (word 600))) s = S3 /\
                 read (memory :> bytes(d0,len)) s = m0 /\
                 read (memory :> bytes(d1,len)) s = m1 /\
                 read (memory :> bytes(d2,len)) s = m2 /\
                 read (memory :> bytes(d3,len)) s = m3 /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
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
                      word_sub stackpointer (word 64),76]
                     [a,800; word_sub stackpointer (word 64),64]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,800);
                        memory :> bytes(word_sub stackpointer (word 64),64)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_XOR_BYTES" THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `d0:int64`; `d1:int64`; `d2:int64`;
    `d3:int64`; `off:num`; `len:num`; `S0:1600 word`; `S1:1600 word`;
    `S2:1600 word`; `S3:1600 word`; `m0:num`; `m1:num`; `m2:num`;
    `m3:num`; `pc:num`] THEN
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
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC
   (1--16) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  XOR_BYTES_X4_FULL_CALL_TAC `S0:1600 word` `m0:num` 17 THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC
   (18--22) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  XOR_BYTES_X4_FULL_CALL_TAC `S1:1600 word` `m1:num` 23 THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC
   (24--28) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  XOR_BYTES_X4_FULL_CALL_TAC `S2:1600 word` `m2:num` 29 THEN
  X86_STEPS_TAC MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_EXEC
   (30--41) THEN
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  XOR_BYTES_X4_FULL_CALL_TAC `S3:1600 word` `m3:num` 42 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
