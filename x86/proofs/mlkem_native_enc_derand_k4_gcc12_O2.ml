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
(* where it is at address 0x1b30, using the theorems for mlkem1024_check_pk, *)
(* mlkem_sha3_256, mlkem_sha3_512 and mlkem1024_indcpa_enc in the image.     *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native_check_pk_k4_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_sha3_256_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_sha3_512_gcc12_O2.ml";;
needs "x86/proofs/mlkem_native_indcpa_enc_k4_gcc12_O2.ml";;
needs "x86/proofs/utils/mlkem_native_kem.ml";;

(*** The code in the image:

    1b30: push   rbp
    1b31: mov    rbp,rsp
    1b34: push   r15
    1b36: mov    r15,rcx
    1b39: push   r14
    1b3b: push   r13
    1b3d: mov    r13,rsi
    1b40: push   r12
    1b42: mov    r12,rdi
    1b45: mov    rdi,rdx
    1b48: push   rbx
    1b49: mov    rbx,rdx
    1b4c: and    rsp,0xffffffffffffffe0
    1b50: add    rsp,0xffffffffffffff80
    1b54: call   1790 <mlkem1024_check_pk>
    1b59: mov    r14,rsp
    1b5c: test   eax,eax
    1b5e: je     1ba0 <mlkem1024_enc_derand+0x70>
    1b60: lea    r15,[rsp+0x40]
    1b65: pxor   xmm0,xmm0
    1b69: movaps XMMWORD PTR [rsp+0x40],xmm0
    1b6e: movaps XMMWORD PTR [rsp+0x50],xmm0
    1b73: movaps XMMWORD PTR [rsp+0x60],xmm0
    1b78: movaps XMMWORD PTR [rsp+0x70],xmm0
    1b7d: movaps XMMWORD PTR [rsp],xmm0
    1b81: movaps XMMWORD PTR [rsp+0x10],xmm0
    1b86: movaps XMMWORD PTR [rsp+0x20],xmm0
    1b8b: movaps XMMWORD PTR [rsp+0x30],xmm0
    1b90: lea    rsp,[rbp-0x28]
    1b94: pop    rbx
    1b95: pop    r12
    1b97: pop    r13
    1b99: pop    r14
    1b9b: pop    r15
    1b9d: pop    rbp
    1b9e: ret
    1b9f: nop
    1ba0: movdqu xmm1,XMMWORD PTR [r15]
    1ba5: movdqu xmm2,XMMWORD PTR [r15+0x10]
    1bab: lea    rdi,[rsp+0x20]
    1bb0: mov    rsi,rbx
    1bb3: mov    edx,0x620
    1bb8: lea    r15,[rsp+0x40]
    1bbd: movaps XMMWORD PTR [rsp],xmm1
    1bc1: movaps XMMWORD PTR [rsp+0x10],xmm2
    1bc6: call   3510 <mlkem_sha3_256>
    1bcb: mov    edx,0x40
    1bd0: mov    rsi,r14
    1bd3: mov    rdi,r15
    1bd6: call   3570 <mlkem_sha3_512>
    1bdb: lea    rcx,[rsp+0x60]
    1be0: mov    rdx,rbx
    1be3: mov    rsi,r14
    1be6: mov    rdi,r12
    1be9: call   1390 <mlkem1024_indcpa_enc>
    1bee: test   eax,eax
    1bf0: jne    1b65 <mlkem1024_enc_derand+0x35>
    1bf6: movdqa xmm3,XMMWORD PTR [rsp+0x40]
    1bfc: movdqa xmm4,XMMWORD PTR [rsp+0x50]
    1c02: movups XMMWORD PTR [r13+0x0],xmm3
    1c07: movups XMMWORD PTR [r13+0x10],xmm4
    1c0c: jmp    1b65 <mlkem1024_enc_derand+0x35>
 ***)

let MLKEM_NATIVE_ENC_DERAND_K4_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [0x1b30,0x1c11];;

let KE4_EXEC = MLKEM_NATIVE_ENC_DERAND_K4_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The input check of FIPS 203 for ML-KEM-1024 in terms of the result of     *)
(* mlkem1024_check_pk.                                                       *)
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

(* ------------------------------------------------------------------------- *)
(* The input of G (the message followed by H of the key), and its output as  *)
(* K and r. This is as for AArch64, with the buffers at offsets from the     *)
(* frame variable bot of INDCPA_BOT_TAC, the bottom of the stacks of the     *)
(* callees 22912 bytes below them: the message m at bot + 22912, H of the    *)
(* key at bot + 22944, K at bot + 22976 and r at bot + 23008.                *)
(* ------------------------------------------------------------------------- *)

let KE4_HM_TAC s =
  let st = mk_var(s,`:x86state`) in
  SUBGOAL_THEN
   (subst [st,`s:x86state`; INDCPA_SP 22912,`a:int64`]
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

let KE4_KR_TAC s =
  let st = mk_var(s,`:x86state`) and a = INDCPA_SP 22976 in
  let gt = `sha3_512 (APPEND (m:byte list) (sha3_256 ek))` in
  FIRST_ASSUM(fun th ->
    if can (term_match [] (subst [a,`a:int64`; st,`s:x86state`]
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
(* Correctness proof. The encapsulation key ek of 1568 bytes is at pk and    *)
(* the message m of 32 bytes at coins, and if ek passes the check of FIPS    *)
(* 203, the shared secret of 32 bytes written at ss and the ciphertext of    *)
(* 1568 bytes written at ct are those of mlkem_encaps_internal mlkem1024 ek  *)
(* m in common/fips203.ml and the function returns 0, and otherwise it       *)
(* returns -4. The theorem assumes that SampleNTT terminates for each entry  *)
(* of the matrix, as for mlkem1024_indcpa_enc, and that the stack does not   *)
(* contain address 0. The stack is the 23120 bytes below the return address, *)
(* for the six saved registers, up to 31 bytes for the alignment, the 128    *)
(* bytes of the buffers (aligned to 32 bytes by AND with -32 after the       *)
(* pushes, as in mlkem1024_indcpa_dec) and the 22912 used by the callees     *)
(* below them. The function branches on the result of the check, and the     *)
(* proof considers the two cases. The message and K are copied by legacy SSE *)
(* moves through XMM1 and XMM2 after the check and through XMM3 and XMM4     *)
(* after the encryption, so the values of those registers are named there.   *)
(* ------------------------------------------------------------------------- *)

let KE4_FRAME = (23120,48,22912,128);;

let KE4_CALL th =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,KE4_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,REWRITE_RULE[ALL] th);;

let KE4_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`ct:int64`; `ss:int64`; `pk:int64`; `coins:int64`; `ek:byte list`;
    `m:byte list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 23120 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SIMP_TAC[MLKEM_EK_CHECK_1024; ASSUME `LENGTH(ek:byte list) = 1568`];;

let KE4_SETUP_TAC =
  INDCPA_BOT_TAC KE4_FRAME [22912] THEN
  INDCPA_FRAME_TAC
   ["memory :> bytes(ct:int64,1568)"; "memory :> bytes(ss:int64,32)"]
   KE4_FRAME THEN
  INDCPA_NONOV_TAC 23040
   [`ct:int64,1568`; `ss:int64,32`; `pk:int64,1568`; `coins:int64,32`;
    `word pc:int64,0x82a0`; `word_add stackpointer (word 23072):int64,56`;
    `word 0:int64,1`]
  THEN
  MAP_EVERY (fun (n,r) -> ENSURES_PRESERVED_TAC n r)
   ["rbx_init",`RBX`; "rbp_init",`RBP`; "r12_init",`R12`;
    "r13_init",`R13`; "r14_init",`R14`; "r15_init",`R15`];;

let KE4_PK_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes(pk,1568)) s = num_of_bytelist ek`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE]
          (REWRITE_RULE[READ_COMPONENT_COMPOSE; READ_BYTES_MOD;
                        ARITH_RULE `MIN 1568 1536 = 1536`]
           (AP_THM(AP_TERM `(MOD):num->num->num`
                    (REWRITE_RULE[READ_COMPONENT_COMPOSE] th))
              `2 EXP (8 * 1536)`)))
    else NO_TAC);;

let KE4_CHECK_CASES_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[KE4_CHECK_EQ]) THEN
  ASM_CASES_TAC
   `!i. i < 1024
        ==> (num_of_bytelist ek DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329` THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o rand o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC;;

let KE4_MAIN_TAC =
  let post = [`pc:num`; `read RSP s`;
              `read (memory :> bytes64(read RSP s)) s`] in
  let call = KE4_CALL in
  ENSURES_INIT_TAC "s0" THEN KEM_HALVES_TAC `coins:int64` THEN KE4_PK_TAC THEN

  (*** The check of the encapsulation key ***)

  X86_STEPS_TAC KE4_EXEC (1--13) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC KE4_EXEC (14--15) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_CHECK_PK_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `num_of_bytelist ek MOD 2 EXP (8 * 1536)`] @ post) 16 THEN
  INDCPA_NORM_TAC THEN INDCPA_YMM_TAC "s16" THEN KE4_CHECK_CASES_TAC THENL
   [ALL_TAC;
    X86_STEPS_TAC KE4_EXEC (17--37) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]] THEN

  (*** H(ek), G(m || H(ek)) and the encryption ***)

  X86_STEPS_TAC KE4_EXEC (17--19) THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KE4_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (20--27) THEN
  INDCPA_NORM_TAC THEN KEM_JOIN_TAC (INDCPA_SP 22912) `m:byte list` "s27" THEN
  X86_STEPS_TAC KE4_EXEC [28] THEN
  call MLKEM_NATIVE_SHA3_256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `ek:byte list`] @ post) 29 THEN
  INDCPA_NORM_TAC THEN KE4_HM_TAC "s29" THEN
  X86_STEPS_TAC KE4_EXEC (30--33) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_SHA3_512_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `APPEND (m:byte list) (sha3_256 ek)`] @
    post) 34 THEN
  INDCPA_NORM_TAC THEN KE4_KR_TAC "s34" THEN
  KEM_HALVES_TAC (INDCPA_SP 22976) THEN
  X86_STEPS_TAC KE4_EXEC (35--39) THEN INDCPA_NORM_TAC THEN
  call MLKEM_NATIVE_INDCPA_ENC_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   ([`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `ek:byte list`;
     `m:byte list`;
     `mlkem_slice 32 32 (sha3_512 (APPEND (m:byte list) (sha3_256 ek)))`] @
    post) 40 THEN

  (*** The shared secret K, zeroing the buffers, the return ***)

  INDCPA_NORM_TAC THEN INDCPA_YMMS_TAC "s40" [3; 4] THEN
  X86_STEPS_TAC KE4_EXEC (41--42) THEN
  MAP_EVERY (fun k -> X86_STEPS_TAC KE4_EXEC [k] THEN SIMD_SIMPLIFY_TAC[])
   (43--46) THEN
  KEM_JOIN_TAC `ss:int64`
   `mlkem_slice 0 32 (sha3_512 (APPEND (m:byte list) (sha3_256 ek)))`
   "s46" THEN
  X86_STEPS_TAC KE4_EXEC (47--64) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN KE4_FINAL_TAC;;

let MLKEM_NATIVE_ENC_DERAND_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = time prove
 (`!ct ss pk coins (ek:byte list) (m:byte list) pc stackpointer
    returnaddress.
    aligned 16 (word pc:int64) /\ LENGTH ek = 1568 /\ LENGTH m = 32 /\
    (!i j. i < 4 /\ j < 4
           ==> mlkem_samplentt_terminates
                (APPEND (mlkem_slice 1536 32 ek) [word j; word i])) /\
    nonoverlapping (word 0,1) (word_sub stackpointer (word 23120),23128) /\
    PAIRWISE nonoverlapping
     [(ct,1568); (ss,32); (word_sub stackpointer (word 23120),23128)] /\
    ALLPAIRS nonoverlapping
     [(ct,1568); (ss,32); (word_sub stackpointer (word 23120),23128)]
     [(pk,1568); (coins,32); (word pc,0x82a0)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + 0x1b30) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [ct; ss; pk; coins] s /\
              (read DF s <=> false) /\
              read (memory :> bytes(pk,1568)) s = num_of_bytelist ek /\
              read (memory :> bytes(coins,32)) s = num_of_bytelist m)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
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
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(ct,1568); memory :> bytes(ss,32);
            memory :> bytes(word_sub stackpointer (word 23120),23120)])`,
  KE4_INTRO_TAC THEN KE4_SETUP_TAC THEN KE4_MAIN_TAC);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. The events depend only on the      *)
(* addresses and on the encapsulation key, which is public: the function     *)
(* branches on the result of the check of the key, given by the combined     *)
(* theorem for mlkem1024_check_pk, and the events of the encryption depend   *)
(* on rho. They are given by a template with cases on whether the key passes *)
(* the check, and the frame variables are expanded in them at the end by     *)
(* INDCPA_UNBOT_TAC, since they are not arguments of the template.           *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let KE4_SAFE_TEMPLATE =
 `\(ct:int64) (ss:int64) (pk:int64) (coins:int64) (pc:num)
   (stackpointer:int64) (returnaddress:int64) (ek:byte list).
   if mlkem_ek_check mlkem1024 ek
   then f_ev1 ct ss pk coins pc stackpointer returnaddress ek
   else f_ev0 ct ss pk coins pc stackpointer returnaddress ek
   :(uarch_event)list`;;

let KE4_SAFE_ALLOWED =
  [`pc:num`; `ct:int64`; `ss:int64`; `pk:int64`; `coins:int64`;
   `stackpointer:int64`; `returnaddress:int64`; `ek:byte list`;
   `bot:int64`];;

let KE4_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,KE4_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      (`e:(uarch_event)list`::ilist @
       [`pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`])
      n THENL
     [EXISTS_E2_TAC (ref KE4_SAFE_ALLOWED); LABEL_TAC name safety_th]);;

let KE4_SAFE_INTRO_TAC =
  MAP_EVERY (fun (th,n) -> ASSUME_CALLEE_SAFETY_TAILED_TAC th n)
   [MLKEM_NATIVE_CHECK_PK_K4_GCC12_O2_IMAGE_SUBROUTINE_FULL,
    "H_CHECK";
    MLKEM_NATIVE_SHA3_256_GCC12_O2_IMAGE_SUBROUTINE_SAFE, "H_SHA3_256";
    MLKEM_NATIVE_SHA3_512_GCC12_O2_IMAGE_SUBROUTINE_SAFE, "H_SHA3_512";
    MLKEM_NATIVE_INDCPA_ENC_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE,
    "H_INDCPA"] THEN
  CONCRETIZE_F_EVENTS_TAC KE4_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`ct:int64`; `ss:int64`; `pk:int64`; `coins:int64`; `ek:byte list`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 23120 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SIMP_TAC[MLKEM_EK_CHECK_1024; ASSUME `LENGTH(ek:byte list) = 1568`];;

let KE4_SAFE_MAIN_TAC =
  let call = KE4_SAFE_CALL_TAC in
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  KE4_PK_TAC THEN
  X86_STEPS_TAC KE4_EXEC (1--13) THEN INDCPA_RSP_TAC THEN
  X86_STEPS_TAC KE4_EXEC (14--15) THEN INDCPA_NORM_TAC THEN
  call "H_CHECK"
   [`read RDI s`; `num_of_bytelist ek MOD 2 EXP (8 * 1536)`] 16 THEN
  INDCPA_NORM_TAC THEN KE4_CHECK_CASES_TAC THENL
   [ALL_TAC;
    X86_STEPS_TAC KE4_EXEC (17--37) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC] THEN
  X86_STEPS_TAC KE4_EXEC (17--28) THEN INDCPA_NORM_TAC THEN
  call "H_SHA3_256" [`read RDI s`; `read RSI s`; `1568`] 29 THEN
  INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KE4_EXEC (30--33) THEN INDCPA_NORM_TAC THEN
  call "H_SHA3_512" [`read RDI s`; `read RSI s`; `64`] 34 THEN
  INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KE4_EXEC (35--39) THEN INDCPA_NORM_TAC THEN
  call "H_INDCPA"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `ek:byte list`]
   40 THEN INDCPA_NORM_TAC THEN
  X86_STEPS_TAC KE4_EXEC (41--64) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  INDCPA_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLKEM_NATIVE_ENC_DERAND_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
   forall e ct ss pk coins (ek:byte list) pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\ LENGTH ek = 1568 /\
    (!i j. i < 4 /\ j < 4
           ==> mlkem_samplentt_terminates
                (APPEND (mlkem_slice 1536 32 ek) [word j; word i])) /\
    nonoverlapping (word 0,1) (word_sub stackpointer (word 23120),23128) /\
    PAIRWISE nonoverlapping
     [(ct,1568); (ss,32); (word_sub stackpointer (word 23120),23128)] /\
    ALLPAIRS nonoverlapping
     [(ct,1568); (ss,32); (word_sub stackpointer (word 23120),23128)]
     [(pk,1568); (coins,32); (word pc,0x82a0)]
    ==> ensures x86
         (\s. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc /\
              read RIP s = word (pc + 0x1b30) /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [ct; ss; pk; coins] s /\
              (read DF s <=> false) /\
              read (memory :> bytes(pk,1568)) s = num_of_bytelist ek /\
              read events s = e)
         (\s. read RIP s = returnaddress /\
              read RSP s = word_add stackpointer (word 8) /\
              C_RETURN s =
              (if mlkem_ek_check mlkem1024 ek then word 0
               else word 0xfffffffc) /\
              (exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_events ct ss pk coins pc
                        (word_sub stackpointer (word 23120)) returnaddress
                        ek /\
                 memaccess_inbounds e2
                  [pk,1568; coins,32; ct,1568; ss,32;
                   word_sub stackpointer (word 23120),23128;
                   word(pc + 0x8008),8; word(pc + 0x8018),8;
                   word(pc + 0x8030),16; word(pc + 0x8040),16;
                   word(pc + 0x8080),48; word(pc + 0x80c0),192;
                   word(pc + 0x81a0),256]
                  [ct,1568; ss,32; word_sub stackpointer (word 23120),23120]))
         (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE
           [memory :> bytes(ct,1568); memory :> bytes(ss,32);
            memory :> bytes(word_sub stackpointer (word 23120),23120)])`,
  KE4_SAFE_INTRO_TAC THEN KE4_SETUP_TAC THEN KE4_SAFE_MAIN_TAC);;
