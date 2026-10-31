(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The encapsulation of ML-KEM-1024 (FIPS 203 Algorithm 17, with the input   *)
(* check of Algorithm 20). This is the code for mlkem1024_enc_derand from    *)
(* mlkem-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mlkem_native/README.md). It checks the encapsulation key with             *)
(* mlkem1024_check_pk, and returns -4 if the check fails. Otherwise it       *)
(* hashes the key with mlkem_sha3_256, computes K and r as G of the message  *)
(* m (the 32 bytes at coins) followed by that hash with mlkem_sha3_512,      *)
(* encrypts m with r by mlkem1024_indcpa_enc into the ciphertext, and writes *)
(* K as the shared secret. In both cases it zeroes its buffers. It is        *)
(* verified in the whole image (see mlkem_native_libmlkem_gcc12_O2.ml),      *)
(* where it is at address 0x1360, using the theorems for mlkem1024_check_pk, *)
(* mlkem_sha3_256, mlkem_sha3_512 and mlkem1024_indcpa_enc in the image.     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_check_pk_k4_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_sha3_256_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_sha3_512_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_indcpa_enc_k4_gcc12_O2.ml";;
needs "arm/proofs/utils/mlkem_native_kem.ml";;

(*** The code in the image:

    1360: stp     x19, x20, [sp, #-224]!
    1364: adrp    x4, 1f000 <mlk_zetas+0x18c80>
    1368: ldr     x4, [x4, #4088]
    136c: stp     x21, x22, [sp, #16]
    1370: add     x19, sp, #0x5f
    1374: stp     x23, x24, [sp, #32]
    1378: mov     x23, x1
    137c: and     x19, x19, #0xffffffffffffffe0
    1380: str     x30, [sp, #48]
    1384: mov     x24, x0
    1388: mov     x21, x2
    138c: mov     x22, x3
    1390: ldr     x1, [x4]
    1394: str     x1, [sp, #216]
    1398: mov     x1, #0x0
    139c: mov     x0, x2
    13a0: add     x20, x19, #0x40
    13a4: bl      1010 <mlkem1024_check_pk>
    13a8: cbz     w0, 13f0 <mlkem1024_enc_derand+0x90>
    13ac: movi    v0.4s, #0x0
    13b0: stp     q0, q0, [x19]
    13b4: stp     q0, q0, [x19, #32]
    13b8: stp     q0, q0, [x20]
    13bc: stp     q0, q0, [x20, #32]
    13c0: adrp    x1, 1f000 <mlk_zetas+0x18c80>
    13c4: ldr     x1, [x1, #4088]
    13c8: ldr     x3, [sp, #216]
    13cc: ldr     x2, [x1]
    13d0: subs    x3, x3, x2
    13d4: mov     x2, #0x0
    13d8: b.ne    143c <mlkem1024_enc_derand+0xdc>
    13dc: ldp     x21, x22, [sp, #16]
    13e0: ldp     x23, x24, [sp, #32]
    13e4: ldr     x30, [sp, #48]
    13e8: ldp     x19, x20, [sp], #224
    13ec: ret
    13f0: ldp     q0, q1, [x22]
    13f4: mov     x1, x21
    13f8: add     x0, x19, #0x60
    13fc: mov     x2, #0x620
    1400: stp     q0, q1, [x20]
    1404: bl      2650 <mlkem_sha3_256>
    1408: mov     x1, x20
    140c: mov     x0, x19
    1410: mov     x2, #0x40
    1414: bl      26f4 <mlkem_sha3_512>
    1418: mov     x2, x21
    141c: mov     x0, x24
    1420: add     x3, x19, #0x20
    1424: mov     x1, x20
    1428: bl      be0 <mlkem1024_indcpa_enc>
    142c: cbnz    w0, 13ac <mlkem1024_enc_derand+0x4c>
    1430: ldp     q0, q1, [x19]
    1434: stp     q0, q1, [x23]
    1438: b       13ac <mlkem1024_enc_derand+0x4c>
    143c: bl      830 <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_ENC_DERAND_K4_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x1360,0x1440];;

let KE4_EXEC = MLKEM_NATIVE_ENC_DERAND_K4_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The input check of FIPS 203 for ML-KEM-1024 in terms of the result of     *)
(* mlkem1024_check_pk, and the address of the buffers, which are aligned to  *)
(* 32 bytes within the stack frame.                                          *)
(* ------------------------------------------------------------------------- *)

let MLKEM_EK_CHECK_1024 = prove
 (`!ek. LENGTH ek = 1568
        ==> (mlkem_ek_check mlkem1024 ek <=>
             !i. i < 1024
                 ==> (num_of_bytelist ek DIV 2 EXP (12 * i)) MOD 2 EXP 12
                     < 3329)`,
  SIMP_TAC[mlkem1024; MLKEM_EK_CHECK] THEN CONV_TAC NUM_REDUCE_CONV);;

let KE4_CHECK_EQ = prove
 (`!n. (!i. i < 1024
            ==> ((n MOD 2 EXP (8 * 1536)) DIV 2 EXP (12 * i)) MOD 2 EXP 12
                < 3329) <=>
       (!i. i < 1024 ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329)`,
  GEN_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  MATCH_MP_TAC(TAUT `(p ==> (q <=> r)) ==> (p ==> q <=> p ==> r)`) THEN
  DISCH_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC DIV_MOD_EXP_LOW THEN ASM_ARITH_TAC);;

let KE4_BUFFER_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 22927)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 22912 else 22896))`,
  REWRITE_TAC[REJ_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let KE4_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` KE4_BUFFER_ADDRESS))
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The callees, the input of G (the message followed by H of the key), and   *)
(* its output as K and r.                                                    *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CHECK_PK_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KE4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_CHECK_PK_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_SHA3_256_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KE4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHA3_256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_SHA3_512_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KE4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_SHA3_512_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_INDCPA_ENC_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KE4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_INDCPA_ENC_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let KE4_HM_TAC b s =
  let st = mk_var(s,`:armstate`) in
  SUBGOAL_THEN
   (subst [st,`s:armstate`; KEM_SP(b + 64),`a:int64`]
     `read (memory :> bytes(a,64)) s =
      num_of_bytelist(APPEND (m:byte list) (sha3_256 ek))`)
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `64 = 32 + 32`; READ_COMPONENT_COMPOSE;
                READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ASM_REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(APPEND (m:byte list) (sha3_256 ek)) = 64`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_SHA3_256] THEN ARITH_TAC;
    ALL_TAC];;

let KE4_KR_TAC b s =
  let st = mk_var(s,`:armstate`) and a = KEM_SP b in
  let gt = `sha3_512 (APPEND (m:byte list) (sha3_256 ek))` in
  FIRST_ASSUM(fun th ->
    if can (term_match [] (subst [a,`a:int64`; st,`s:armstate`]
         `read (memory :> bytes(a,64)) s = num_of_bytelist(sha3_512 x)`))
         (concl th)
    then
      MP_TAC(SPECL [a; gt; `0`; `32`; st] READ_MEMORY_BYTES_SLICE) THEN
      MP_TAC(SPECL [a; gt; `32`; `32`; st] READ_MEMORY_BYTES_SLICE) THEN
      ASM_REWRITE_TAC[LENGTH_SHA3_512] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
      REPEAT DISCH_TAC
    else NO_TAC) THEN
  SUBGOAL_THEN
   `LENGTH(mlkem_slice 0 32 (sha3_512 (APPEND (m:byte list) (sha3_256 ek))))
    = 32 /\
    LENGTH(mlkem_slice 32 32 (sha3_512 (APPEND m (sha3_256 ek)))) = 32`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]; ALL_TAC];;

let KE4_FINAL_TAC =
  REWRITE_TAC[mlkem1024; MLKEM_ENCAPS_PAIR] THEN
  REWRITE_TAC[GSYM mlkem1024] THEN
  ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset and memcpy (for the  *)
(* callees). The encapsulation key ek of 1568 bytes is at pk and the message *)
(* m of 32 bytes at coins, and if ek passes the check of FIPS 203, the       *)
(* shared secret of 32 bytes written at ss and the ciphertext of 1568 bytes  *)
(* written at ct are those of mlkem_encaps_internal mlkem1024 ek m in        *)
(* common/fips203.ml and the function returns 0, and otherwise it returns    *)
(* -4. The theorem assumes that SampleNTT terminates for each entry of the   *)
(* matrix and that the stack does not contain address 0, as for              *)
(* mlkem1024_indcpa_enc. The stack is the 224 bytes of the function and the  *)
(* 22832 used by mlkem1024_indcpa_enc below them. The proof is by cases on   *)
(* whether the stack pointer is a multiple of 32, which gives the address b  *)
(* of the buffers, at offsets 0 (K and r) and 64 (m and H of the key).       *)
(* ------------------------------------------------------------------------- *)

let KE4_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`ct:int64`; `ss:int64`; `pk:int64`; `coins:int64`; `ek:byte list`;
    `m:byte list`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 23056 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 23056):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[MLKEM_EK_CHECK_1024; ASSUME `LENGTH(ek:byte list) = 1568`] THEN
  REWRITE_TAC[SPECL [`pc:num`; `0x1fff8`] WORD_ADD;
              SPECL [`pc:num`; `0x1ffe8`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `0x1fff8`] WORD_ADD;
                              SPECL [`pc:num`; `0x1ffe8`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--28);;

let KE4_CASE_TAC b =
  ENSURES_INIT_TAC "s0" THEN KEM_HALVES_TAC `coins:int64` THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes(pk,1568)) s = num_of_bytelist ek`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE]
          (REWRITE_RULE[READ_COMPONENT_COMPOSE; READ_BYTES_MOD;
                        ARITH_RULE `MIN 1568 1536 = 1536`]
           (AP_THM(AP_TERM `(MOD):num->num->num`
                    (REWRITE_RULE[READ_COMPONENT_COMPOSE] th))
              `2 EXP (8 * 1536)`)))
    else NO_TAC) THEN

  (*** The check of the encapsulation key ***)

  ARM_STEPS_TAC KE4_EXEC (1--2) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KE4_EXEC (3--8) THEN KE4_BUFFER_TAC THEN
  ARM_STEPS_TAC KE4_EXEC (9--18) THEN KEM_GOT_TAC THEN
  LOCAL_CHECK_PK_TAC
   [`read X0 s`; `num_of_bytelist ek MOD 2 EXP (8 * 1536)`; `guard:int64`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`; `read SP s`;
    `read X30 s`] 19 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[KE4_CHECK_EQ]) THEN
  ASM_CASES_TAC
   `!i. i < 1024
        ==> (num_of_bytelist ek DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329` THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o rand o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
   [ALL_TAC;
    ARM_STEPS_TAC KE4_EXEC (20--26) THEN MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC KE4_EXEC (27--37) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]] THEN

  (*** H(ek), G(m || H(ek)) and the encryption ***)

  ARM_STEPS_TAC KE4_EXEC (20--26) THEN
  KEM_JOIN_TAC (KEM_SP(b + 64)) `m:byte list` "s26" THEN
  KEM_GOT_TAC THEN
  LOCAL_SHA3_256_TAC
   [`read X0 s`; `read X1 s`; `ek:byte list`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 27 THEN
  KE4_HM_TAC b "s27" THEN
  ARM_STEPS_TAC KE4_EXEC (28--31) THEN KEM_GOT_TAC THEN
  LOCAL_SHA3_512_TAC
   [`read X0 s`; `read X1 s`; `APPEND (m:byte list) (sha3_256 ek)`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 32 THEN
  KE4_KR_TAC b "s32" THEN
  KEM_HALVES_TAC (KEM_SP b) THEN
  ARM_STEPS_TAC KE4_EXEC (33--37) THEN KEM_GOT_TAC THEN
  LOCAL_INDCPA_ENC_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `ek:byte list`;
    `m:byte list`;
    `mlkem_slice 32 32 (sha3_512 (APPEND (m:byte list) (sha3_256 ek)))`;
    `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`; `read SP s`; `read X30 s`] 38 THEN

  (*** The shared secret K, zeroing the buffers, the return ***)

  ARM_STEPS_TAC KE4_EXEC (39--48) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KE4_EXEC (49--59) THEN
  KEM_JOIN_TAC `ss:int64`
   `mlkem_slice 0 32 (sha3_512 (APPEND (m:byte list) (sha3_256 ek)))`
   "s59" THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN KE4_FINAL_TAC;;

let MLKEM_NATIVE_ENC_DERAND_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!ct ss pk coins (ek:byte list) (m:byte list) guard mf mc ea el
    ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH ek = 1568 /\ LENGTH m = 32 /\
        (!i j. i < 4 /\ j < 4
               ==> mlkem_samplentt_terminates
                    (APPEND (mlkem_slice 1536 32 ek) [word j; word i])) /\
        nonoverlapping (word 0,1) (word_sub stackpointer (word 23056),23056) /\
        nonoverlapping (pk,1568) (word pc,0x6480) /\
        PAIRWISE nonoverlapping
         [(ct,1568); (ss,32); (word_sub stackpointer (word 23056),23056)] /\
        ALLPAIRS nonoverlapping
         [(ct,1568); (ss,32); (word_sub stackpointer (word 23056),23056)]
         [(pk,1568); (coins,32); (word pc,0x6480); (word(pc + 0x1fff8),8);
          (guard,8); (word(pc + 0x1ffe8),8); (word(pc + 0x1ffd0),8);
          (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x1360) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [ct; ss; pk; coins] s /\
                  read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                  read (memory :> bytes64(word(pc + 0x1ffe8))) s = mf /\
                  read (memory :> bytes64(word(pc + 0x1ffd0))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(pk,1568)) s = num_of_bytelist ek /\
                  read (memory :> bytes(coins,32)) s = num_of_bytelist m)
             (\s. read PC s = returnaddress /\
                  (mlkem_ek_check mlkem1024 ek
                   ==> read (memory :> bytes(ss,32)) s =
                       num_of_bytelist
                        (FST(mlkem_encaps_internal mlkem1024 ek m)) /\
                       read (memory :> bytes(ct,1568)) s =
                       num_of_bytelist
                        (SND(mlkem_encaps_internal mlkem1024 ek m))) /\
                  C_RETURN s =
                  (if mlkem_ek_check mlkem1024 ek then word 0
                   else word 0xfffffffc))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(ct,1568); memory :> bytes(ss,32);
                memory :> bytes(word_sub stackpointer (word 23056),23056)])`,
  KE4_INTRO_TAC THEN ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [KE4_CASE_TAC 22912; KE4_CASE_TAC 22896]);;
