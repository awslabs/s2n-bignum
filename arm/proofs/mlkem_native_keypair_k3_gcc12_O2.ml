(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The key generation of ML-KEM-768 (FIPS 203 Algorithm 19). This is the     *)
(* code for mlkem768_keypair from mlkem-native's portable C implementation   *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md). It gets 64      *)
(* random bytes with randombytes into a buffer on the stack, and returns -3  *)
(* if that fails, and otherwise generates the keys from them with            *)
(* mlkem768_keypair_derand. In both cases it zeroes the buffer. It is        *)
(* verified in the whole image (see mlkem_native_libmlkem_gcc12_O2.ml),      *)
(* where it is at address 0x5a04, using the theorem for                      *)
(* mlkem768_keypair_derand in the image and the contract for randombytes.    *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_keypair_derand_k3_gcc12_O2.ml";;

(*** The code in the image:

    5a04: stp     x19, x20, [sp, #-128]!
    5a08: mov     x20, x0
    5a0c: adrp    x2, 1f000 <mlk_zetas+0x18c80>
    5a10: ldr     x2, [x2, #4088]
    5a14: stp     x21, x30, [sp, #16]
    5a18: add     x19, sp, #0x3f
    5a1c: and     x19, x19, #0xffffffffffffffe0
    5a20: mov     x21, x1
    5a24: ldr     x1, [x2]
    5a28: str     x1, [sp, #120]
    5a2c: mov     x1, #0x0
    5a30: mov     x0, x19
    5a34: mov     x1, #0x40
    5a38: bl      820 <randombytes@plt>
    5a3c: cbnz    w0, 5a84 <mlkem768_keypair+0x80>
    5a40: mov     x1, x21
    5a44: mov     x0, x20
    5a48: mov     x2, x19
    5a4c: bl      5970 <mlkem768_keypair_derand>
    5a50: movi    v0.4s, #0x0
    5a54: stp     q0, q0, [x19]
    5a58: stp     q0, q0, [x19, #32]
    5a5c: adrp    x1, 1f000 <mlk_zetas+0x18c80>
    5a60: ldr     x1, [x1, #4088]
    5a64: ldr     x3, [sp, #120]
    5a68: ldr     x2, [x1]
    5a6c: subs    x3, x3, x2
    5a70: mov     x2, #0x0
    5a74: b.ne    5a8c <mlkem768_keypair+0x88>
    5a78: ldp     x21, x30, [sp, #16]
    5a7c: ldp     x19, x20, [sp], #128
    5a80: ret
    5a84: mov     w0, #0xfffffffd
    5a88: b       5a50 <mlkem768_keypair+0x4c>
    5a8c: bl      830 <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_KEYPAIR_K3_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x820,0x830; 0x5a04,0x5a90];;

let KR3_EXEC = MLKEM_NATIVE_KEYPAIR_K3_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The address of the buffer, which is aligned to 32 bytes within the stack  *)
(* frame, the callee, and the seeds as the random bytes.                     *)
(* ------------------------------------------------------------------------- *)

let KR3_BUFFER_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 13999)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 13984 else 13968))`,
  REWRITE_TAC[REJ_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let KR3_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` KR3_BUFFER_ADDRESS))
    else NO_TAC);;

let LOCAL_KEYPAIR_DERAND_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KR3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KEYPAIR_DERAND_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let KR3_D = `bytelist_of_num 32 (rnd MOD 2 EXP 256)`;;

let KR3_Z = `bytelist_of_num 32 (rnd DIV 2 EXP 256)`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset, memcpy and          *)
(* randombytes. Either randombytes succeeds and the function returns 0, and  *)
(* then the encapsulation key of 1184 bytes at pk and the decapsulation key  *)
(* of 2400 bytes at sk are those of mlkem_keygen mlkem768 d z in             *)
(* common/fips203.ml for some d and z of 32 bytes (the random bytes), or it  *)
(* fails and the function returns -3. The theorem assumes that SampleNTT     *)
(* terminates for each entry of the matrix for any seed d. The stack is the  *)
(* 128 bytes of the function and the 13936 used by mlkem768_keypair_derand   *)
(* below them. The proof is by cases on whether the stack pointer is a       *)
(* multiple of 32, which gives the address b of the buffer, and on whether   *)
(* randombytes succeeds.                                                     *)
(* ------------------------------------------------------------------------- *)

let KR3_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`pk:int64`; `sk:int64`; `guard:int64`; `mf:int64`; `mc:int64`;
    `mr:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 14064 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 14064):int64)` THEN
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

let KR3_CASE_TAC b =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC KR3_EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KR3_EXEC (4--7) THEN KR3_BUFFER_TAC THEN
  ARM_STEPS_TAC KR3_EXEC (8--14) THEN
  LIBC_PLT_TAC KR3_EXEC 14 THEN
  LIBC_CALL_TAC "H_RANDOMBYTES" KR3_EXEC
   [`read X0 s`; `read X1 s`; `read X30 s`] 19 THEN
  ABBREV_TAC `rv = read X0 s19` THEN
  ABBREV_TAC (mk_eq(`rnd:num`,
   subst [KEM_SP b,`a:int64`] `read (memory :> bytes(a,64)) s19`)) THEN
  ASM_CASES_TAC `val(word_zx(rv:int64):int32) = 0` THENL
   [ARM_STEPS_TAC KR3_EXEC (20--24) THEN KEM_GOT_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                ONCE_DEPTH_CONV NUM_ADD_CONV) o
      MATCH_MP KEM_RANDOM_SPLIT o
      check (fun th -> rand(concl th) = `rnd:num`)) THEN
    SUBGOAL_THEN (mk_conj(mk_eq(mk_comb(`LENGTH:byte list->num`,KR3_D),`32`),
                          mk_eq(mk_comb(`LENGTH:byte list->num`,KR3_Z),`32`)))
    STRIP_ASSUME_TAC THENL [REWRITE_TAC[LENGTH_BYTELIST_OF_NUM]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC KR3_D o check (is_forall o concl)) THEN
    REWRITE_TAC[LENGTH_BYTELIST_OF_NUM] THEN DISCH_TAC THEN
    LOCAL_KEYPAIR_DERAND_TAC
     [`read X0 s`; `read X1 s`; `read X2 s`; KR3_D; KR3_Z; `guard:int64`;
      `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
      `read SP s`; `read X30 s`] 25 THEN
    ARM_STEPS_TAC KR3_EXEC (26--29) THEN MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC KR3_EXEC (30--38) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [KR3_D; KR3_Z] THEN
    ASM_REWRITE_TAC[LENGTH_BYTELIST_OF_NUM];
    ARM_STEPS_TAC KR3_EXEC (20--26) THEN MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC KR3_EXEC (27--35) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];;

let MLKEM_NATIVE_KEYPAIR_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!pk sk guard mf mc mr ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        randombytes_contract mr ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        (!d. LENGTH d = 32
             ==> !i j. i < 3 /\ j < 3
                       ==> mlkem_samplentt_terminates
                            (APPEND (FST(mlkem_g(APPEND d [word 3])))
                                    [word j; word i])) /\
        PAIRWISE nonoverlapping
         [(pk,1184); (sk,2400); (word_sub stackpointer (word 14064),14064)] /\
        ALLPAIRS nonoverlapping
         [(pk,1184); (sk,2400); (word_sub stackpointer (word 14064),14064)]
         [(word pc,0x6480); (word(pc + 0x1fff8),8); (guard,8);
          (word(pc + 0x1ffe8),8); (word(pc + 0x1ffd0),8);
          (word(pc + 0x1ffd8),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x5a04) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [pk; sk] s /\
                  read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                  read (memory :> bytes64(word(pc + 0x1ffe8))) s = mf /\
                  read (memory :> bytes64(word(pc + 0x1ffd0))) s = mc /\
                  read (memory :> bytes64(word(pc + 0x1ffd8))) s = mr /\
                  read (memory :> bytes(ea,el)) s = ev)
             (\s. read PC s = returnaddress /\
                  (C_RETURN s = word 0 /\
                   (?d z. LENGTH d = 32 /\ LENGTH z = 32 /\
                          read (memory :> bytes(pk,1184)) s =
                          num_of_bytelist(FST(mlkem_keygen mlkem768 d z)) /\
                          read (memory :> bytes(sk,2400)) s =
                          num_of_bytelist(SND(mlkem_keygen mlkem768 d z))) \/
                   C_RETURN s = word 0xfffffffd))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(pk,1184); memory :> bytes(sk,2400);
                memory :> bytes(word_sub stackpointer (word 14064),14064)])`,
  KR3_INTRO_TAC THEN ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [KR3_CASE_TAC 13984; KR3_CASE_TAC 13968]);;
