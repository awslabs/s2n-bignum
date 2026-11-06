(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The encapsulation of ML-KEM-768 (FIPS 203 Algorithm 17, with the input    *)
(* check of Algorithm 20). This is the code for mlkem768_enc_derand from     *)
(* mlkem-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mlkem_native/README.md). It checks the encapsulation key with             *)
(* mlkem768_check_pk, and returns -4 if the check fails. Otherwise it hashes *)
(* the key with mlkem_sha3_256, computes K and r as G of the message m (the  *)
(* 32 bytes at coins) followed by that hash with mlkem_sha3_512, encrypts m  *)
(* with r by mlkem768_indcpa_enc into the ciphertext, and writes K as the    *)
(* shared secret. In both cases it zeroes its buffers. It is verified in the *)
(* whole image (see libmlkem.ml), using the theorems                         *)
(* for mlkem768_check_pk, mlkem_sha3_256, mlkem_sha3_512 and                 *)
(* mlkem768_indcpa_enc in the image.                                         *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/gcc12_O2_mono/check_pk_k3.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/sha3_256.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/sha3_512.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/indcpa_enc_k3.ml";;
needs "arm/proofs/utils/mlkem_native_kem.ml";;

(*** The code in the image, from the layout of gcc12_O2_mono:

    mlkem768_enc_derand:
     +0x0  stp     x19, x20, [sp, #-224]!
  adrp1:
     +0x4  adrp    x4, <page>
     +0x8  ldr     x4, [x4, #4088]
                   // got_stack_chk_guard
     +0xc  stp     x21, x22, [sp, #16]
    +0x10  add     x19, sp, #0x5f
    +0x14  stp     x23, x24, [sp, #32]
    +0x18  mov     x23, x1
    +0x1c  and     x19, x19, #0xffffffffffffffe0
    +0x20  str     x30, [sp, #48]
    +0x24  mov     x24, x0
    +0x28  mov     x21, x2
    +0x2c  mov     x22, x3
    +0x30  ldr     x1, [x4]
    +0x34  str     x1, [sp, #216]
    +0x38  mov     x1, #0x0
    +0x3c  mov     x0, x2
    +0x40  add     x20, x19, #0x40
    +0x44  bl      mlkem768_check_pk
  after_mlkem768_check_pk:
    +0x48  cbz     w0, +0x90                      -+
  join1:                                           |
    +0x4c  movi    v0.4s, #0x0                    <----+-+
    +0x50  stp     q0, q0, [x19]                   |   | |
    +0x54  stp     q0, q0, [x19, #32]              |   | |
    +0x58  stp     q0, q0, [x20]                   |   | |
    +0x5c  stp     q0, q0, [x20, #32]              |   | |
  adrp2:                                           |   | |
    +0x60  adrp    x1, <page>                      |   | |
    +0x64  ldr     x1, [x1, #4088]                 |   | |
                   // got_stack_chk_guard          |   | |
    +0x68  ldr     x3, [sp, #216]                  |   | |
    +0x6c  ldr     x2, [x1]                        |   | |
    +0x70  subs    x3, x3, x2                      |   | |
    +0x74  mov     x2, #0x0                        |   | |
    +0x78  b.ne    +0xdc                          ---+ | |
    +0x7c  ldp     x21, x22, [sp, #16]             | | | |
    +0x80  ldp     x23, x24, [sp, #32]             | | | |
    +0x84  ldr     x30, [sp, #48]                  | | | |
    +0x88  ldp     x19, x20, [sp], #224            | | | |
  ret:                                             | | | |
    +0x8c  ret                                     | | | |
    +0x90  ldp     q0, q1, [x22]                  <+ | | |
    +0x94  mov     x1, x21                           | | |
    +0x98  add     x0, x19, #0x60                    | | |
    +0x9c  mov     x2, #0x4a0                        | | |
    +0xa0  stp     q0, q1, [x20]                     | | |
    +0xa4  bl      mlkem_sha3_256                    | | |
  after_mlkem_sha3_256:                              | | |
    +0xa8  mov     x1, x20                           | | |
    +0xac  mov     x0, x19                           | | |
    +0xb0  mov     x2, #0x40                         | | |
    +0xb4  bl      mlkem_sha3_512                    | | |
  after_mlkem_sha3_512:                              | | |
    +0xb8  mov     x2, x21                           | | |
    +0xbc  mov     x0, x24                           | | |
    +0xc0  add     x3, x19, #0x20                    | | |
    +0xc4  mov     x1, x20                           | | |
    +0xc8  bl      mlkem768_indcpa_enc               | | |
  after_mlkem768_indcpa_enc:                         | | |
    +0xcc  cbnz    w0, join1                      -----+ |
    +0xd0  ldp     q0, q1, [x19]                     |   |
    +0xd4  stp     q0, q1, [x23]                     |   |
    +0xd8  b       join1                          -------+
    +0xdc  bl      stack_chk_fail                 <--+
 ***)

let MLKEM_NATIVE_ENC_DERAND_K3_GCC12_O2_MONO_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "mlkem768_enc_derand"];;

let KE3_EXEC = MLKEM_NATIVE_ENC_DERAND_K3_GCC12_O2_MONO_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The input check of FIPS 203 for ML-KEM-768 in terms of the result of      *)
(* mlkem768_check_pk, and the address of the buffers, which are aligned to   *)
(* 32 bytes within the stack frame.                                          *)
(* ------------------------------------------------------------------------- *)

let MLKEM_EK_CHECK_768 = prove
 (`!ek. LENGTH ek = 1184
        ==> (mlkem_ek_check mlkem768 ek <=>
             !i. i < 768
                 ==> (num_of_bytelist ek DIV 2 EXP (12 * i)) MOD 2 EXP 12
                     < 3329)`,
  SIMP_TAC[mlkem768; MLKEM_EK_CHECK] THEN CONV_TAC NUM_REDUCE_CONV);;

let KE3_CHECK_EQ = prove
 (`!n. (!i. i < 768
            ==> ((n MOD 2 EXP (8 * 1152)) DIV 2 EXP (12 * i)) MOD 2 EXP 12
                < 3329) <=>
       (!i. i < 768 ==> (n DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329)`,
  GEN_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  MATCH_MP_TAC(TAUT `(p ==> (q <=> r)) ==> (p ==> q <=> p ==> r)`) THEN
  DISCH_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC DIV_MOD_EXP_LOW THEN ASM_ARITH_TAC);;

let KE3_BUFFER_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 17775)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 17760 else 17744))`,
  REWRITE_TAC[REJ_ALIGNED_16_32] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let KE3_BUFFER_TAC =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then SUBST_ALL_TAC
          (REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` KE3_BUFFER_ADDRESS))
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The callees, the input of G (the message followed by H of the key), and   *)
(* its output as K and r.                                                    *)
(* ------------------------------------------------------------------------- *)

let LOCAL_CHECK_PK_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,KE3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_CHECK_PK_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_SHA3_256_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,KE3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_SHA3_256_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_SHA3_512_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,KE3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_SHA3_512_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_INDCPA_ENC_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,KE3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let KE3_HM_TAC b s =
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

let KE3_KR_TAC b s =
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

let KE3_FINAL_TAC =
  REWRITE_TAC[mlkem768; MLKEM_ENCAPS_PAIR] THEN REWRITE_TAC[GSYM mlkem768] THEN
  ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contracts for memset and memcpy (for the  *)
(* callees). The encapsulation key ek of 1184 bytes is at pk and the message *)
(* m of 32 bytes at coins, and if ek passes the check of FIPS 203, the       *)
(* shared secret of 32 bytes written at ss and the ciphertext of 1088 bytes  *)
(* written at ct are those of mlkem_encaps_internal mlkem768 ek m in         *)
(* common/fips203.ml and the function returns 0, and otherwise it returns    *)
(* -4. The theorem assumes that SampleNTT terminates for each entry of the   *)
(* matrix and that the stack does not contain address 0, as for              *)
(* mlkem768_indcpa_enc. The stack is the 224 bytes of the function and the   *)
(* 17680 used by mlkem768_indcpa_enc below them. The proof is by cases on    *)
(* whether the stack pointer is a multiple of 32, which gives the address b  *)
(* of the buffers, at offsets 0 (K and r) and 64 (m and H of the key).       *)
(* ------------------------------------------------------------------------- *)

let KE3_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`ct:int64`; `ss:int64`; `pk:int64`; `coins:int64`; `ek:byte list`;
    `m:byte list`; `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`;
    `el:num`; `ev:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 17904 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 17904):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[MLKEM_EK_CHECK_768; ASSUME `LENGTH(ek:byte list) = 1184`] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--28);;

let KE3_CASE_TAC b =
  ENSURES_INIT_TAC "s0" THEN KEM_HALVES_TAC `coins:int64` THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes(pk,1184)) s = num_of_bytelist ek`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE]
          (REWRITE_RULE[READ_COMPONENT_COMPOSE; READ_BYTES_MOD;
                        ARITH_RULE `MIN 1184 1152 = 1152`]
           (AP_THM(AP_TERM `(MOD):num->num->num`
                    (REWRITE_RULE[READ_COMPONENT_COMPOSE] th))
              `2 EXP (8 * 1152)`)))
    else NO_TAC) THEN

  (*** The check of the encapsulation key ***)

  ARM_STEPS_TAC KE3_EXEC (1--2) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KE3_EXEC (3--8) THEN KE3_BUFFER_TAC THEN
  ARM_STEPS_TAC KE3_EXEC (9--18) THEN KEM_GOT_TAC THEN
  LOCAL_CHECK_PK_TAC
   [`read X0 s`; `num_of_bytelist ek MOD 2 EXP (8 * 1152)`; `guard:int64`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`; `read SP s`;
    `read X30 s`] 19 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[KE3_CHECK_EQ]) THEN
  ASM_CASES_TAC
   `!i. i < 768
        ==> (num_of_bytelist ek DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329` THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o rand o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
   [ALL_TAC;
    ARM_STEPS_TAC KE3_EXEC (20--26) THEN MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC KE3_EXEC (27--37) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]] THEN

  (*** H(ek), G(m || H(ek)) and the encryption ***)

  ARM_STEPS_TAC KE3_EXEC (20--26) THEN
  KEM_JOIN_TAC (KEM_SP(b + 64)) `m:byte list` "s26" THEN
  KEM_GOT_TAC THEN
  LOCAL_SHA3_256_TAC
   [`read X0 s`; `read X1 s`; `ek:byte list`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 27 THEN
  KE3_HM_TAC b "s27" THEN
  ARM_STEPS_TAC KE3_EXEC (28--31) THEN KEM_GOT_TAC THEN
  LOCAL_SHA3_512_TAC
   [`read X0 s`; `read X1 s`; `APPEND (m:byte list) (sha3_256 ek)`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 32 THEN
  KE3_KR_TAC b "s32" THEN
  KEM_HALVES_TAC (KEM_SP b) THEN
  ARM_STEPS_TAC KE3_EXEC (33--37) THEN KEM_GOT_TAC THEN
  LOCAL_INDCPA_ENC_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `ek:byte list`;
    `m:byte list`;
    `mlkem_slice 32 32 (sha3_512 (APPEND (m:byte list) (sha3_256 ek)))`;
    `guard:int64`; `mf:int64`; `mc:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`; `read SP s`; `read X30 s`] 38 THEN

  (*** The shared secret K, zeroing the buffers, the return ***)

  ARM_STEPS_TAC KE3_EXEC (39--48) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KE3_EXEC (49--59) THEN
  KEM_JOIN_TAC `ss:int64`
   `mlkem_slice 0 32 (sha3_512 (APPEND (m:byte list) (sha3_256 ek)))`
   "s59" THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN KE3_FINAL_TAC;;

let MLKEM_NATIVE_ENC_DERAND_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!ct ss pk coins (ek:byte list) (m:byte list) guard mf mc ea el
    ev pc stackpointer returnaddress.
        memset_contract mf ea el ev /\ memcpy_contract mc ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ LENGTH ek = 1184 /\ LENGTH m = 32 /\
        (!i j. i < 3 /\ j < 3
               ==> mlkem_samplentt_terminates
                    (APPEND (mlkem_slice 1152 32 ek) [word j; word i])) /\
        nonoverlapping (word 0,1) (word_sub stackpointer (word 17904),17904) /\
        nonoverlapping (pk,1184) (word pc,libmlkem_size) /\
        PAIRWISE nonoverlapping
         [(ct,1088); (ss,32); (word_sub stackpointer (word 17904),17904)] /\
        ALLPAIRS nonoverlapping
         [(ct,1088); (ss,32); (word_sub stackpointer (word 17904),17904)]
         [(pk,1184); (coins,32); (word pc,libmlkem_size);
          (word(pc + got_stack_chk_guard),8);
          (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
          (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                  read PC s = word (pc + mlkem768_enc_derand) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [ct; ss; pk; coins] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(pk,1184)) s = num_of_bytelist ek /\
                  read (memory :> bytes(coins,32)) s = num_of_bytelist m)
             (\s. read PC s = returnaddress /\
                  (mlkem_ek_check mlkem768 ek
                   ==> read (memory :> bytes(ss,32)) s =
                       num_of_bytelist
                        (FST(mlkem_encaps_internal mlkem768 ek m)) /\
                       read (memory :> bytes(ct,1088)) s =
                       num_of_bytelist
                        (SND(mlkem_encaps_internal mlkem768 ek m))) /\
                  C_RETURN s =
                  (if mlkem_ek_check mlkem768 ek then word 0
                   else word 0xfffffffc))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(ct,1088); memory :> bytes(ss,32);
                memory :> bytes(word_sub stackpointer (word 17904),17904)])`,
  KE3_INTRO_TAC THEN ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [KE3_CASE_TAC 17760; KE3_CASE_TAC 17744]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, assuming the combined contract for *)
(* memset (for mlkem768_indcpa_enc) and the safety contract for memcpy. The  *)
(* events depend only on the addresses and on the encapsulation key, which   *)
(* is public: the function branches on the result of the check of the key,   *)
(* given by the combined theorem for mlkem768_check_pk, and the events of    *)
(* the encryption depend on rho. They are given by a template with cases on  *)
(* whether the stack pointer is a multiple of 32, as for the correctness     *)
(* proof, and on whether the key passes the check.                           *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let KE_SAFE_TEMPLATE =
 `\(ct:int64) (ss:int64) (pk:int64) (coins:int64) (guard:int64)
   (mf:int64) (mc:int64) (pc:num) (stackpointer:int64)
   (returnaddress:int64) (ek:byte list).
   if aligned 32 stackpointer
   then (if mlkem_ek_check mlkem768 ek
         then f_ev_a1 ct ss pk coins guard mf mc pc stackpointer
                      returnaddress ek
         else f_ev_a0 ct ss pk coins guard mf mc pc stackpointer
                      returnaddress ek)
   else (if mlkem_ek_check mlkem768 ek
         then f_ev_u1 ct ss pk coins guard mf mc pc stackpointer
                      returnaddress ek
         else f_ev_u0 ct ss pk coins guard mf mc pc stackpointer
                      returnaddress ek)
   :(uarch_event)list`;;

let KE_SAFE_ALLOWED =
  [`pc:num`; `ct:int64`; `ss:int64`; `pk:int64`; `coins:int64`;
   `guard:int64`; `mf:int64`; `mc:int64`; `stackpointer:int64`;
   `returnaddress:int64`; `ek:byte list`];;

let KE3_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th1 ->
    if can (term_match [] `memset_full_contract mf ea el ev`) (concl th1)
    then FIRST_X_ASSUM(fun th2 ->
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (MATCH_MP MLKEM_NATIVE_INDCPA_ENC_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE
                 (CONJ th1 th2)) "H_INDCPA" THEN
      ASSUME_CALLEE_SAFETY_TAILED_TAC
       (MATCH_MP MLKEM_NATIVE_CHECK_PK_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL
         (CONJUNCT2(MATCH_MP MEMSET_FULL_CONTRACT th1))) "H_CHECK")
    else NO_TAC) THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHA3_256_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_SHA3_256" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHA3_512_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE "H_SHA3_512" THEN
  CONCRETIZE_F_EVENTS_TAC KE_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES]) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 17904):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[MLKEM_EK_CHECK_768; ASSUME `LENGTH(ek:byte list) = 1184`] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (parse_term("X"^string_of_int n))) (19--28);;

let KE3_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mono_mc,KE3_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref KE_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let KE3_SAFE_CASE_TAC b =
  let e = `e:(uarch_event)list` in
  let x n = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,
                            mk_const("X"^string_of_int n,[])),`s:armstate`) in
  let rest = [`guard:int64`; `pc:num`; `read SP s`; `read X30 s`] in
  let call = KE3_SAFE_CALL_TAC in
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes(pk,1184)) s = num_of_bytelist ek`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE]
          (REWRITE_RULE[READ_COMPONENT_COMPOSE; READ_BYTES_MOD;
                        ARITH_RULE `MIN 1184 1152 = 1152`]
           (AP_THM(AP_TERM `(MOD):num->num->num`
                    (REWRITE_RULE[READ_COMPONENT_COMPOSE] th))
              `2 EXP (8 * 1152)`)))
    else NO_TAC) THEN
  ARM_STEPS_TAC KE3_EXEC (1--2) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KE3_EXEC (3--8) THEN KE3_BUFFER_TAC THEN
  ARM_STEPS_TAC KE3_EXEC (9--18) THEN KEM_GOT_TAC THEN
  call "H_CHECK"
   ([e; x 0; `num_of_bytelist ek MOD 2 EXP (8 * 1152)`] @ rest) 19 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[KE3_CHECK_EQ]) THEN
  ASM_CASES_TAC
   `!i. i < 768
        ==> (num_of_bytelist ek DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329` THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o rand o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
   [ALL_TAC;
    ARM_STEPS_TAC KE3_EXEC (20--26) THEN MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC KE3_EXEC (27--37) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN
  ARM_STEPS_TAC KE3_EXEC (20--26) THEN KEM_GOT_TAC THEN
  call "H_SHA3_256" ([e; x 0; x 1; `1184`] @ rest) 27 THEN
  ARM_STEPS_TAC KE3_EXEC (28--31) THEN KEM_GOT_TAC THEN
  call "H_SHA3_512" ([e; x 0; x 1; `64`] @ rest) 32 THEN
  ARM_STEPS_TAC KE3_EXEC (33--37) THEN KEM_GOT_TAC THEN
  call "H_INDCPA" ([e; x 0; x 1; x 2; x 3; `ek:byte list`] @ rest) 38 THEN
  ARM_STEPS_TAC KE3_EXEC (39--48) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KE3_EXEC (49--59) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_ENC_DERAND_K3_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE =
  prove
 (`!mf mc ea el ev.
   memset_full_contract mf ea el ev /\ memcpy_safety_contract mc ea el ev
   ==> exists f_events.
        forall e ct ss pk coins (ek:byte list) guard pc stackpointer
               returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\ LENGTH ek = 1184 /\
          (!i j. i < 3 /\ j < 3
                 ==> mlkem_samplentt_terminates
                      (APPEND (mlkem_slice 1152 32 ek) [word j; word i])) /\
          nonoverlapping (word 0,1)
           (word_sub stackpointer (word 17904),17904) /\
          nonoverlapping (pk,1184) (word pc,libmlkem_size) /\
          PAIRWISE nonoverlapping
           [(ct,1088); (ss,32); (word_sub stackpointer (word 17904),17904)] /\
          ALLPAIRS nonoverlapping
           [(ct,1088); (ss,32); (word_sub stackpointer (word 17904),17904)]
           [(pk,1184); (coins,32); (word pc,libmlkem_size);
            (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mono_mc /\
                    read PC s = word (pc + mlkem768_enc_derand) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [ct; ss; pk; coins] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s
                     = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(pk,1184)) s = num_of_bytelist ek /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mlkem_ek_check mlkem768 ek then word 0
                     else word 0xfffffffc) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events ct ss pk coins guard mf mc pc
                              (word_sub stackpointer (word 17904))
                              returnaddress ek /\
                       memaccess_inbounds e2
                        [pk,1184; coins,32; ct,1088; ss,32;
                         word_sub stackpointer (word 17904),17904;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                         word(pc + mlkem_poly_cbd2_consts),64;
                         word(pc + rodata_mlk_zetas),256;
                         word(pc + mlk_poly_invntt_tomont_c_consts),32]
                        [ct,1088; ss,32;
                         word_sub stackpointer (word 17904),17904]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(ct,1088); memory :> bytes(ss,32);
                  memory :> bytes(word_sub stackpointer (word 17904),17904)])`,
  KE3_SAFE_INTRO_TAC THEN ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [KE3_SAFE_CASE_TAC 17760; KE3_SAFE_CASE_TAC 17744]);;
