(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The encapsulation of ML-KEM-512 (FIPS 203 Algorithm 20). This is the code *)
(* for mlkem512_enc from mlkem-native's portable C implementation compiled   *)
(* by gcc 12 with -O2 (see mlkem_native/README.md). It gets 32 random bytes  *)
(* with randombytes into a buffer on the stack, and returns -3 if that       *)
(* fails, and otherwise encapsulates with them as the message with           *)
(* mlkem512_enc_derand. In both cases it zeroes the buffer. It is verified   *)
(* in the whole image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is   *)
(* at address 0x3e90, using the theorem for mlkem512_enc_derand in the image *)
(* and the contract for randombytes.                                         *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_enc_derand_k2_gcc12_O2.ml";;

(*** The code in the image:

    3e90: stp     x19, x20, [sp, #-112]!
    3e94: mov     x20, x0
    3e98: adrp    x3, 1f000 <mlk_zetas+0x18c80>
    3e9c: ldr     x3, [x3, #4088]
    3ea0: stp     x21, x22, [sp, #16]
    3ea4: add     x19, sp, #0x4f
    3ea8: str     x30, [sp, #32]
    3eac: and     x19, x19, #0xffffffffffffffe0
    3eb0: mov     x21, x1
    3eb4: mov     x22, x2
    3eb8: ldr     x1, [x3]
    3ebc: str     x1, [sp, #104]
    3ec0: mov     x1, #0x0
    3ec4: mov     x0, x19
    3ec8: mov     x1, #0x20
    3ecc: bl      820 <randombytes@plt>
    3ed0: cbnz    w0, 3f1c <mlkem512_enc+0x8c>
    3ed4: mov     x2, x22
    3ed8: mov     x1, x21
    3edc: mov     x0, x20
    3ee0: mov     x3, x19
    3ee4: bl      3db0 <mlkem512_enc_derand>
    3ee8: stp     xzr, xzr, [x19]
    3eec: stp     xzr, xzr, [x19, #16]
    3ef0: adrp    x1, 1f000 <mlk_zetas+0x18c80>
    3ef4: ldr     x1, [x1, #4088]
    3ef8: ldr     x3, [sp, #104]
    3efc: ldr     x2, [x1]
    3f00: subs    x3, x3, x2
    3f04: mov     x2, #0x0
    3f08: b.ne    3f24 <mlkem512_enc+0x94>
    3f0c: ldp     x21, x22, [sp, #16]
    3f10: ldr     x30, [sp, #32]
    3f14: ldp     x19, x20, [sp], #112
    3f18: ret
    3f1c: mov     w0, #0xfffffffd
    3f20: b       3ee8 <mlkem512_enc+0x58>
    3f24: bl      830 <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_ENC_K2_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x820,0x830; 0x3e90,0x3f28];;

let KER2_EXEC = MLKEM_NATIVE_ENC_K2_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The address of the buffer, which is aligned to 32 bytes within the stack  *)
(* frame, the callee, and the message as the random bytes.                   *)
(* ------------------------------------------------------------------------- *)

let KER2_BUFFER_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 12303)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 12288 else 12272))`,
  REWRITE_TAC[REJ_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let KER2_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` KER2_BUFFER_ADDRESS))
    else NO_TAC);;

let LOCAL_ENC_DERAND_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KER2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_ENC_DERAND_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let KER2_M = `bytelist_of_num 32 rnd`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset, memcpy and          *)
(* randombytes. Either randombytes succeeds, and then for some message m of  *)
(* 32 bytes (the random bytes) the function behaves as mlkem512_enc_derand   *)
(* with m: if the encapsulation key ek of 800 bytes at pk passes the check   *)
(* of FIPS 203, it returns 0 and the shared secret at ss and the ciphertext  *)
(* at ct are those of mlkem_encaps_internal mlkem512 ek m, and otherwise it  *)
(* returns -4. Or randombytes fails and the function returns -3. The theorem *)
(* assumes that SampleNTT terminates for each entry of the matrix, as for    *)
(* mlkem512_enc_derand. The stack is the 112 bytes of the function and the   *)
(* 12224 used by mlkem512_enc_derand below them. The proof is by cases on    *)
(* whether the stack pointer is a multiple of 32, which gives the address b  *)
(* of the buffer, and on whether randombytes succeeds.                       *)
(* ------------------------------------------------------------------------- *)

let KER2_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`ct:int64`; `ss:int64`; `pk:int64`; `ek:byte list`; `guard:int64`;
    `mf:int64`; `mc:int64`; `mr:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 12336 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 12336):int64)` THEN
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

let KER2_CASE_TAC b =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC KER2_EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KER2_EXEC (4--8) THEN KER2_BUFFER_TAC THEN
  ARM_STEPS_TAC KER2_EXEC (9--16) THEN
  LIBC_PLT_TAC KER2_EXEC 16 THEN
  LIBC_CALL_TAC "H_RANDOMBYTES" KER2_EXEC
   [`read X0 s`; `read X1 s`; `read X30 s`] 21 THEN
  ABBREV_TAC `rv = read X0 s21` THEN
  ABBREV_TAC (mk_eq(`rnd:num`,
   subst [KEM_SP b,`a:int64`] `read (memory :> bytes(a,32)) s21`)) THEN
  ASM_CASES_TAC `val(word_zx(rv:int64):int32) = 0` THENL
   [ARM_STEPS_TAC KER2_EXEC (22--27) THEN KEM_GOT_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP KEM_RANDOM_32 o
      check (fun th -> rand(concl th) = `rnd:num`)) THEN
    SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,KER2_M),`32`))
    ASSUME_TAC THENL [REWRITE_TAC[LENGTH_BYTELIST_OF_NUM]; ALL_TAC] THEN
    LOCAL_ENC_DERAND_TAC
     [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `ek:byte list`;
      KER2_M; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`;
      `ev:num`; `pc:num`; `read SP s`; `read X30 s`] 28 THEN
    ARM_STEPS_TAC KER2_EXEC (29--31) THEN MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC KER2_EXEC (32--41) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISJ1_TAC THEN EXISTS_TAC KER2_M THEN
    ASM_REWRITE_TAC[LENGTH_BYTELIST_OF_NUM];
    ARM_STEPS_TAC KER2_EXEC (22--27) THEN MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC KER2_EXEC (28--37) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];;

let MLKEM_NATIVE_ENC_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!ct ss pk (ek:byte list) guard mf mc mr ea el ev pc
    stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        randombytes_contract mr ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH ek = 800 /\
        (!i j. i < 2 /\ j < 2
               ==> mlkem_samplentt_terminates
                    (APPEND (mlkem_slice 768 32 ek) [word j; word i])) /\
        nonoverlapping (pk,800) (word pc,0x6480) /\
        PAIRWISE nonoverlapping
         [(ct,768); (ss,32); (word_sub stackpointer (word 12336),12336)] /\
        ALLPAIRS nonoverlapping
         [(ct,768); (ss,32); (word_sub stackpointer (word 12336),12336)]
         [(pk,800); (word pc,0x6480); (word(pc + 0x1fff8),8); (guard,8);
          (word(pc + 0x1ffe8),8); (word(pc + 0x1ffd0),8);
          (word(pc + 0x1ffd8),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x3e90) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [ct; ss; pk] s /\
                  read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                  read (memory :> bytes64(word(pc + 0x1ffe8))) s = mf /\
                  read (memory :> bytes64(word(pc + 0x1ffd0))) s = mc /\
                  read (memory :> bytes64(word(pc + 0x1ffd8))) s = mr /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(pk,800)) s = num_of_bytelist ek)
             (\s. read PC s = returnaddress /\
                  ((?m. LENGTH m = 32 /\
                        (mlkem_ek_check mlkem512 ek
                         ==> read (memory :> bytes(ss,32)) s =
                             num_of_bytelist
                              (FST(mlkem_encaps_internal mlkem512 ek m)) /\
                             read (memory :> bytes(ct,768)) s =
                             num_of_bytelist
                              (SND(mlkem_encaps_internal mlkem512 ek m))) /\
                        C_RETURN s =
                        (if mlkem_ek_check mlkem512 ek then word 0
                         else word 0xfffffffc)) \/
                   C_RETURN s = word 0xfffffffd))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(ct,768); memory :> bytes(ss,32);
                memory :> bytes(word_sub stackpointer (word 12336),12336)])`,
  KER2_INTRO_TAC THEN ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [KER2_CASE_TAC 12288; KER2_CASE_TAC 12272]);;
