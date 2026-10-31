(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The key generation of ML-KEM-1024 (FIPS 203 Algorithm 19). This is the    *)
(* code for mlkem1024_keypair from mlkem-native's portable C implementation  *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md). It gets 64      *)
(* random bytes with randombytes into a buffer on the stack, and returns -3  *)
(* if that fails, and otherwise generates the keys from them with            *)
(* mlkem1024_keypair_derand. In both cases it zeroes the buffer. It is       *)
(* verified in the whole image (see mlkem_native_libmlkem_gcc12_O2.ml),      *)
(* where it is at address 0x12d4, using the theorem for                      *)
(* mlkem1024_keypair_derand in the image and the contract for randombytes.   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_keypair_derand_k4_gcc12_O2.ml";;

(*** The code in the image:

    12d4: stp     x19, x20, [sp, #-128]!
    12d8: mov     x20, x0
    12dc: adrp    x2, 1f000 <mlk_zetas+0x18c80>
    12e0: ldr     x2, [x2, #4088]
    12e4: stp     x21, x30, [sp, #16]
    12e8: add     x19, sp, #0x3f
    12ec: and     x19, x19, #0xffffffffffffffe0
    12f0: mov     x21, x1
    12f4: ldr     x1, [x2]
    12f8: str     x1, [sp, #120]
    12fc: mov     x1, #0x0
    1300: mov     x0, x19
    1304: mov     x1, #0x40
    1308: bl      820 <randombytes@plt>
    130c: cbnz    w0, 1354 <mlkem1024_keypair+0x80>
    1310: mov     x1, x21
    1314: mov     x0, x20
    1318: mov     x2, x19
    131c: bl      1240 <mlkem1024_keypair_derand>
    1320: movi    v0.4s, #0x0
    1324: stp     q0, q0, [x19]
    1328: stp     q0, q0, [x19, #32]
    132c: adrp    x1, 1f000 <mlk_zetas+0x18c80>
    1330: ldr     x1, [x1, #4088]
    1334: ldr     x3, [sp, #120]
    1338: ldr     x2, [x1]
    133c: subs    x3, x3, x2
    1340: mov     x2, #0x0
    1344: b.ne    135c <mlkem1024_keypair+0x88>
    1348: ldp     x21, x30, [sp, #16]
    134c: ldp     x19, x20, [sp], #128
    1350: ret
    1354: mov     w0, #0xfffffffd
    1358: b       1320 <mlkem1024_keypair+0x4c>
    135c: bl      830 <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_KEYPAIR_K4_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x820,0x830; 0x12d4,0x1360];;

let KR4_EXEC = MLKEM_NATIVE_KEYPAIR_K4_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The address of the buffer, which is aligned to 32 bytes within the stack  *)
(* frame, the callee, and the seeds as the random bytes.                     *)
(* ------------------------------------------------------------------------- *)

let KR4_BUFFER_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 19423)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 19392 else 19408))`,
  REWRITE_TAC[REJ_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let KR4_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` KR4_BUFFER_ADDRESS))
    else NO_TAC);;

let LOCAL_KEYPAIR_DERAND_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KR4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KEYPAIR_DERAND_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let KR4_D = `bytelist_of_num 32 (rnd MOD 2 EXP 256)`;;

let KR4_Z = `bytelist_of_num 32 (rnd DIV 2 EXP 256)`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset, memcpy and          *)
(* randombytes. Either randombytes succeeds and the function returns 0, and  *)
(* then the encapsulation key of 1568 bytes at pk and the decapsulation key  *)
(* of 3168 bytes at sk are those of mlkem_keygen mlkem1024 d z in            *)
(* common/fips203.ml for some d and z of 32 bytes (the random bytes), or it  *)
(* fails and the function returns -3. The theorem assumes that SampleNTT     *)
(* terminates for each entry of the matrix for any seed d and that the stack *)
(* does not contain address 0. The stack is the 128 bytes of the function    *)
(* and the 19360 used by mlkem1024_keypair_derand below them. The proof is   *)
(* by cases on whether the stack pointer is a multiple of 32, which gives    *)
(* the address b of the buffer, and on whether randombytes succeeds.         *)
(* ------------------------------------------------------------------------- *)

let KR4_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`pk:int64`; `sk:int64`; `guard:int64`; `mf:int64`; `mc:int64`;
    `mr:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 19488 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 19488):int64)` THEN
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

let KR4_CASE_TAC b =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC KR4_EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KR4_EXEC (4--7) THEN KR4_BUFFER_TAC THEN
  ARM_STEPS_TAC KR4_EXEC (8--14) THEN
  LIBC_PLT_TAC KR4_EXEC 14 THEN
  LIBC_CALL_TAC "H_RANDOMBYTES" KR4_EXEC
   [`read X0 s`; `read X1 s`; `read X30 s`] 19 THEN
  ABBREV_TAC `rv = read X0 s19` THEN
  ABBREV_TAC (mk_eq(`rnd:num`,
   subst [KEM_SP b,`a:int64`] `read (memory :> bytes(a,64)) s19`)) THEN
  ASM_CASES_TAC `val(word_zx(rv:int64):int32) = 0` THENL
   [ARM_STEPS_TAC KR4_EXEC (20--24) THEN KEM_GOT_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                ONCE_DEPTH_CONV NUM_ADD_CONV) o
      MATCH_MP KEM_RANDOM_SPLIT o
      check (fun th -> rand(concl th) = `rnd:num`)) THEN
    SUBGOAL_THEN (mk_conj(mk_eq(mk_comb(`LENGTH:byte list->num`,KR4_D),`32`),
                          mk_eq(mk_comb(`LENGTH:byte list->num`,KR4_Z),`32`)))
    STRIP_ASSUME_TAC THENL [REWRITE_TAC[LENGTH_BYTELIST_OF_NUM]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC KR4_D o check (is_forall o concl)) THEN
    REWRITE_TAC[LENGTH_BYTELIST_OF_NUM] THEN DISCH_TAC THEN
    LOCAL_KEYPAIR_DERAND_TAC
     [`read X0 s`; `read X1 s`; `read X2 s`; KR4_D; KR4_Z; `guard:int64`;
      `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
      `read SP s`; `read X30 s`] 25 THEN
    ARM_STEPS_TAC KR4_EXEC (26--29) THEN MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC KR4_EXEC (30--38) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [KR4_D; KR4_Z] THEN
    ASM_REWRITE_TAC[LENGTH_BYTELIST_OF_NUM];
    ARM_STEPS_TAC KR4_EXEC (20--26) THEN MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC KR4_EXEC (27--35) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];;

let MLKEM_NATIVE_KEYPAIR_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!pk sk guard mf mc mr ea el ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        randombytes_contract mr ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        (!d. LENGTH d = 32
             ==> !i j. i < 4 /\ j < 4
                       ==> mlkem_samplentt_terminates
                            (APPEND (FST(mlkem_g(APPEND d [word 4])))
                                    [word j; word i])) /\
        nonoverlapping (word 0,1) (word_sub stackpointer (word 19488),19488) /\
        PAIRWISE nonoverlapping
         [(pk,1568); (sk,3168); (word_sub stackpointer (word 19488),19488)] /\
        ALLPAIRS nonoverlapping
         [(pk,1568); (sk,3168); (word_sub stackpointer (word 19488),19488)]
         [(word pc,0x6480); (word(pc + 0x1fff8),8); (guard,8);
          (word(pc + 0x1ffe8),8); (word(pc + 0x1ffd0),8);
          (word(pc + 0x1ffd8),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x12d4) /\
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
                          read (memory :> bytes(pk,1568)) s =
                          num_of_bytelist(FST(mlkem_keygen mlkem1024 d z)) /\
                          read (memory :> bytes(sk,3168)) s =
                          num_of_bytelist(SND(mlkem_keygen mlkem1024 d z))) \/
                   C_RETURN s = word 0xfffffffd))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(pk,1568); memory :> bytes(sk,3168);
                memory :> bytes(word_sub stackpointer (word 19488),19488)])`,
  KR4_INTRO_TAC THEN ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [KR4_CASE_TAC 19392; KR4_CASE_TAC 19408]);;
