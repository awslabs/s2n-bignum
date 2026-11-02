(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA3-256. This is the code for mlkem_sha3_256 from mlkem-native's         *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md), which absorbs the input into a state on the      *)
(* stack with mlk_keccak_absorb_once, permutes it and extracts the 32 bytes  *)
(* of the hash, and then zeroes the state with REP STOSQ. It is verified in  *)
(* the whole image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at   *)
(* address 0x3510, using the theorems for mlk_keccak_absorb_once at 0x32b0,  *)
(* mlkem_keccakf1600_permute at 0x3e70 and mlkem_keccakf1600_extract_bytes   *)
(* at 0x3d10 in the image. The result is sha3_256 of common/fips202.ml.      *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_keccak_absorb_once_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_keccakf1600_extract_bytes_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    3510: push   rbp
    3511: mov    rcx,rdx
    3514: mov    r8d,0x6
    351a: mov    rdx,rsi
    351d: push   rbx
    351e: mov    rbp,rdi
    3521: mov    esi,0x88
    3526: sub    rsp,0xd8
    352d: mov    rbx,rsp
    3530: mov    rdi,rbx
    3533: call   32b0 <mlk_keccak_absorb_once>
    3538: mov    rdi,rbx
    353b: call   3e70 <mlkem_keccakf1600_permute>
    3540: mov    rdi,rbx
    3543: mov    ecx,0x20
    3548: xor    edx,edx
    354a: mov    rsi,rbp
    354d: call   3d10 <mlkem_keccakf1600_extract_bytes>
    3552: xor    eax,eax
    3554: mov    rdi,rbx
    3557: mov    ecx,0x19
    355c: rep    stos QWORD PTR es:[rdi],rax
    355f: add    rsp,0xd8
    3566: pop    rbx
    3567: pop    rbp
    3568: ret
 ***)

let MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x3510,0x3569];;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, using those  *)
(* of mlk_keccak_absorb_once, mlkem_keccakf1600_permute and                  *)
(* mlkem_keccakf1600_extract_bytes. The input is a list of bytes, and the 32 *)
(* bytes of the output, as a number, are those of sha3_256 in                *)
(* common/fips202.ml. The stack is the 232 bytes of the function, the        *)
(* return address of a call and the 320 bytes used by mlk_keccak_absorb_once *)
(* below that.                                                               *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let SHA3_256_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `m:int64`; `out:int64`; `inlen:num`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC name safety_th]);;

let MLKEM_NATIVE_SHA3_256_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (`exists f_events.
     forall e out m (inp:byte list) inlen pc stackpointer returnaddress.
       aligned 16 (word pc:int64) /\ LENGTH inp = inlen /\
       PAIRWISE nonoverlapping
        [out,32; m,inlen; word_sub stackpointer (word 560),568] /\
       ALL (nonoverlapping (word pc,0x82a0))
        [out,32; word_sub stackpointer (word 560),568]
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + 0x3510) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [out; m; word inlen] s /\
                 (read DF s <=> false) /\
                 read (memory :> bytes(m,inlen)) s = num_of_bytelist inp /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 read (memory :> bytes(out,32)) s =
                 num_of_bytelist(sha3_256 inp) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m out inlen pc
                           (word_sub stackpointer (word 560)) returnaddress /\
                    memaccess_inbounds e2
                     [m,inlen; out,32; word_sub stackpointer (word 560),568;
                      word(pc + 0x80c0),192]
                     [out,32; word_sub stackpointer (word 560),560]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(out,32);
               memory :> bytes(word_sub stackpointer (word 560),560)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_ABSORB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERMUTE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_EXTRACT" THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `out:int64`; `m:int64`; `inp:byte list`;
    `inlen:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 560 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** Saving the registers, and the absorption ***)

  X86_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC (1--11) THEN
  SHA3_256_SAFE_CALL_TAC "H_ABSORB"
   [`e:(uarch_event)list`; `read RDI s`; `136`; `read RDX s`; `inlen:num`;
    `6`; `num_of_bytelist(inp:byte list)`; `pc:num`; `read RSP s`;
    `read (memory :> bytes64(read RSP s)) s`] 12 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN

  (*** The permutation and the extraction of the hash ***)

  X86_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC (13--14) THEN
  KECCAK_STATE_AT_TAC `word_add (stackpointer:int64) (word 328)` THEN
  KECCAK_STATE_THEN `word_add (stackpointer:int64) (word 328)` (fun v ->
    SHA3_256_SAFE_CALL_TAC "H_PERMUTE"
     [`e:(uarch_event)list`; `read RDI s`; v; `pc:num`; `read RSP s`;
      `read (memory :> bytes64(read RSP s)) s`] 15) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC (16--20) THEN
  KECCAK_STATE_AT_TAC `word_add (stackpointer:int64) (word 328)` THEN
  KECCAK_STATE_THEN `word_add (stackpointer:int64) (word 328)` (fun v ->
    SHA3_256_SAFE_CALL_TAC "H_EXTRACT"
     [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `0`; `32`; v;
      `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`]
     21) THEN

  (*** Zeroing the state and the return ***)

  X86_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC (22--29) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [UNDISCH_THEN `LENGTH(inp:byte list) = inlen` (SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC[sha3_256] THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1] THEN
    MATCH_MP_TAC KECCAK_SPONGE_BYTES THEN
    REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem alone, from the combined one.                     *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHA3_256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!out m (inp:byte list) pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        PAIRWISE nonoverlapping
         [(out,32); (m,LENGTH inp); (word_sub stackpointer (word 560),568)] /\
        ALL (nonoverlapping (word pc,0x82a0))
         [(out,32); (word_sub stackpointer (word 560),568)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x3510) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [out; m; word(LENGTH inp)] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(m,LENGTH inp)) s =
                  num_of_bytelist inp)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> bytes(out,32)) s =
                  num_of_bytelist(sha3_256 inp))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(out,32);
                memory :> bytes(word_sub stackpointer (word 560),560)])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  GHOST_INTRO_TAC `e:(uarch_event)list` `read events` THEN
  MP_TAC MLKEM_NATIVE_SHA3_256_GCC12_O2_IMAGE_SUBROUTINE_FULL THEN
  DISCH_THEN(CHOOSE_THEN (MP_TAC o SPECL
   [`e:(uarch_event)list`; `out:int64`; `m:int64`; `inp:byte list`;
    `LENGTH(inp:byte list)`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`])) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_WEAKEN_RULE) THEN
  SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, for any input.                     *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHA3_256_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
     forall e out m inlen pc stackpointer returnaddress.
       aligned 16 (word pc:int64) /\
       PAIRWISE nonoverlapping
        [out,32; m,inlen; word_sub stackpointer (word 560),568] /\
       ALL (nonoverlapping (word pc,0x82a0))
        [out,32; word_sub stackpointer (word 560),568]
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + 0x3510) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [out; m; word inlen] s /\
                 (read DF s <=> false) /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m out inlen pc
                           (word_sub stackpointer (word 560)) returnaddress /\
                    memaccess_inbounds e2
                     [m,inlen; out,32; word_sub stackpointer (word 560),568;
                      word(pc + 0x80c0),192]
                     [out,32; word_sub stackpointer (word 560),560]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(out,32);
               memory :> bytes(word_sub stackpointer (word 560),560)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_ABSORB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_PERMUTE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_EXTRACT" THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `out:int64`; `m:int64`; `inlen:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 560 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC (1--11) THEN
  SHA3_256_SAFE_CALL_TAC "H_ABSORB"
   [`e:(uarch_event)list`; `read RDI s`; `136`; `read RDX s`; `inlen:num`;
    `6`; `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`]
   12 THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC (13--14) THEN
  SHA3_256_SAFE_CALL_TAC "H_PERMUTE"
   [`e:(uarch_event)list`; `read RDI s`; `pc:num`; `read RSP s`;
    `read (memory :> bytes64(read RSP s)) s`] 15 THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC (16--20) THEN
  SHA3_256_SAFE_CALL_TAC "H_EXTRACT"
   [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `0`; `32`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] 21 THEN
  X86_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC (22--29) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
