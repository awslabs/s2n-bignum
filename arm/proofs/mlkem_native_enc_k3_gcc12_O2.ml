(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The encapsulation of ML-KEM-768 (FIPS 203 Algorithm 20). This is the code *)
(* for mlkem768_enc from mlkem-native's portable C implementation compiled   *)
(* by gcc 12 with -O2 (see mlkem_native/README.md). It gets 32 random bytes  *)
(* with randombytes into a buffer on the stack, and returns -3 if that       *)
(* fails, and otherwise encapsulates with them as the message with           *)
(* mlkem768_enc_derand. In both cases it zeroes the buffer. It is verified   *)
(* in the whole image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is   *)
(* at address 0x5b70, using the theorem for mlkem768_enc_derand in the image *)
(* and the contract for randombytes.                                         *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_enc_derand_k3_gcc12_O2.ml";;

(*** The code in the image:

    5b70: stp     x19, x20, [sp, #-112]!
    5b74: mov     x20, x0
    5b78: adrp    x3, 1f000 <mlk_zetas+0x18c80>
    5b7c: ldr     x3, [x3, #4088]
    5b80: stp     x21, x22, [sp, #16]
    5b84: add     x19, sp, #0x4f
    5b88: str     x30, [sp, #32]
    5b8c: and     x19, x19, #0xffffffffffffffe0
    5b90: mov     x21, x1
    5b94: mov     x22, x2
    5b98: ldr     x1, [x3]
    5b9c: str     x1, [sp, #104]
    5ba0: mov     x1, #0x0
    5ba4: mov     x0, x19
    5ba8: mov     x1, #0x20
    5bac: bl      820 <randombytes@plt>
    5bb0: cbnz    w0, 5bfc <mlkem768_enc+0x8c>
    5bb4: mov     x2, x22
    5bb8: mov     x1, x21
    5bbc: mov     x0, x20
    5bc0: mov     x3, x19
    5bc4: bl      5a90 <mlkem768_enc_derand>
    5bc8: stp     xzr, xzr, [x19]
    5bcc: stp     xzr, xzr, [x19, #16]
    5bd0: adrp    x1, 1f000 <mlk_zetas+0x18c80>
    5bd4: ldr     x1, [x1, #4088]
    5bd8: ldr     x3, [sp, #104]
    5bdc: ldr     x2, [x1]
    5be0: subs    x3, x3, x2
    5be4: mov     x2, #0x0
    5be8: b.ne    5c04 <mlkem768_enc+0x94>
    5bec: ldp     x21, x22, [sp, #16]
    5bf0: ldr     x30, [sp, #32]
    5bf4: ldp     x19, x20, [sp], #112
    5bf8: ret
    5bfc: mov     w0, #0xfffffffd
    5c00: b       5bc8 <mlkem768_enc+0x58>
    5c04: bl      830 <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_ENC_K3_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x820,0x830; 0x5b70,0x5c08];;

let KER3_EXEC = MLKEM_NATIVE_ENC_K3_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The address of the buffer, which is aligned to 32 bytes within the stack  *)
(* frame, the callee, and the message as the random bytes.                   *)
(* ------------------------------------------------------------------------- *)

let KER3_BUFFER_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 17199)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 17184 else 17168))`,
  REWRITE_TAC[REJ_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let KER3_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` KER3_BUFFER_ADDRESS))
    else NO_TAC);;

let LOCAL_ENC_DERAND_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KER3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_ENC_DERAND_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let KER3_M = `bytelist_of_num 32 rnd`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset, memcpy and          *)
(* randombytes. Either randombytes succeeds, and then for some message m of  *)
(* 32 bytes (the random bytes) the function behaves as mlkem768_enc_derand   *)
(* with m: if the encapsulation key ek of 1184 bytes at pk passes the check  *)
(* of FIPS 203, it returns 0 and the shared secret at ss and the ciphertext  *)
(* at ct are those of mlkem_encaps_internal mlkem768 ek m, and otherwise it  *)
(* returns -4. Or randombytes fails and the function returns -3. The theorem *)
(* assumes that SampleNTT terminates for each entry of the matrix and that   *)
(* the stack does not contain address 0, as for mlkem768_enc_derand. The     *)
(* stack is the 112 bytes of the function and the 17120 used by              *)
(* mlkem768_enc_derand below them. The proof is by cases on whether the      *)
(* stack pointer is a multiple of 32, which gives the address b of the       *)
(* buffer, and on whether randombytes succeeds.                              *)
(* ------------------------------------------------------------------------- *)

let KER3_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`ct:int64`; `ss:int64`; `pk:int64`; `ek:byte list`; `guard:int64`;
    `mf:int64`; `mc:int64`; `mr:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 17232 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 17232):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `0x1fff8`] WORD_ADD;
              SPECL [`pc:num`; `0x1ffd8`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `0x1fff8`] WORD_ADD;
                              SPECL [`pc:num`; `0x1ffd8`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--28) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `randombytes_contract mr ea el ev`) (concl th)
    then LABEL_TAC "H_RANDOMBYTES" (REWRITE_RULE[randombytes_contract] th)
    else NO_TAC);;

let KER3_CASE_TAC b =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC KER3_EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KER3_EXEC (4--8) THEN KER3_BUFFER_TAC THEN
  ARM_STEPS_TAC KER3_EXEC (9--16) THEN
  LIBC_PLT_TAC KER3_EXEC 16 THEN
  LIBC_CALL_TAC "H_RANDOMBYTES" KER3_EXEC
   [`read X0 s`; `read X1 s`; `read X30 s`] 21 THEN
  ABBREV_TAC `rv = read X0 s21` THEN
  ABBREV_TAC (mk_eq(`rnd:num`,
   subst [KEM_SP b,`a:int64`] `read (memory :> bytes(a,32)) s21`)) THEN
  ASM_CASES_TAC `val(word_zx(rv:int64):int32) = 0` THENL
   [ARM_STEPS_TAC KER3_EXEC (22--27) THEN KEM_GOT_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP KEM_RANDOM_32 o
      check (fun th -> rand(concl th) = `rnd:num`)) THEN
    SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,KER3_M),`32`))
    ASSUME_TAC THENL [REWRITE_TAC[LENGTH_BYTELIST_OF_NUM]; ALL_TAC] THEN
    LOCAL_ENC_DERAND_TAC
     [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `ek:byte list`;
      KER3_M; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`;
      `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 28 THEN
    ARM_STEPS_TAC KER3_EXEC (29--31) THEN MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC KER3_EXEC (32--41) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISJ1_TAC THEN EXISTS_TAC KER3_M THEN
    ASM_REWRITE_TAC[LENGTH_BYTELIST_OF_NUM];
    ARM_STEPS_TAC KER3_EXEC (22--27) THEN MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC KER3_EXEC (28--37) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];;

let MLKEM_NATIVE_ENC_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!ct ss pk (ek:byte list) guard mf mc mr ea el ev pc
    stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        randombytes_contract mr ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH ek = 1184 /\
        (!i j. i < 3 /\ j < 3
               ==> mlkem_samplentt_terminates
                    (APPEND (mlkem_slice 1152 32 ek) [word j; word i])) /\
        nonoverlapping (word 0,1) (word_sub stackpointer (word 17232),17232) /\
        nonoverlapping (pk,1184) (word pc,0x6480) /\
        PAIRWISE nonoverlapping
         [(ct,1088); (ss,32); (word_sub stackpointer (word 17232),17232)] /\
        ALLPAIRS nonoverlapping
         [(ct,1088); (ss,32); (word_sub stackpointer (word 17232),17232)]
         [(pk,1184); (word pc,0x6480); (word(pc + 0x1fff8),8); (guard,8);
          (word(pc + 0x1ffe8),8); (word(pc + 0x1ffd0),8);
          (word(pc + 0x1ffd8),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x5b70) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [ct; ss; pk] s /\
                  read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                  read (memory :> bytes64(word(pc + 0x1ffe8))) s = mf /\
                  read (memory :> bytes64(word(pc + 0x1ffd0))) s = mc /\
                  read (memory :> bytes64(word(pc + 0x1ffd8))) s = mr /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(pk,1184)) s = num_of_bytelist ek)
             (\s. read PC s = returnaddress /\
                  ((?m. LENGTH m = 32 /\
                        (mlkem_ek_check mlkem768 ek
                         ==> read (memory :> bytes(ss,32)) s =
                             num_of_bytelist
                              (FST(mlkem_encaps_internal mlkem768 ek m)) /\
                             read (memory :> bytes(ct,1088)) s =
                             num_of_bytelist
                              (SND(mlkem_encaps_internal mlkem768 ek m))) /\
                        C_RETURN s =
                        (if mlkem_ek_check mlkem768 ek then word 0
                         else word 0xfffffffc)) \/
                   C_RETURN s = word 0xfffffffd))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(ct,1088); memory :> bytes(ss,32);
                memory :> bytes(word_sub stackpointer (word 17232),17232)])`,
  KER3_INTRO_TAC THEN ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [KER3_CASE_TAC 17184; KER3_CASE_TAC 17168]);;
