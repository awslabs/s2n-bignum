(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Key generation: the proof (see keypair_internal_44_spec.ml).              *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/keypair_internal_44_spec.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "x86/proofs/utils/mldsa_native_keypair.ml";;
needs "x86/proofs/utils/mldsa_native_top.ml";;

let KP44_EXEC = MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The frame. After REPEAT_GEN_AND_OFFSET_STACKPTR_TAC, stackpointer is the  *)
(* bottom of the 28228 bytes of stack below the return address, at           *)
(* stackpointer + 28228; the code first aligns RSP to 32 bytes, at bot +     *)
(* 28197 (see utils/mldsa_native_realign.ml), with R10 keeping the original  *)
(* RSP + 8, and then pushes a copy of the return address (at bot + 28189),   *)
(* RBP (at bot + 28181, the frame pointer), R15, R14, R13, R12, R10 and RBX, *)
(* and reserves 4416 bytes, with RSP at bot + 23717, below which             *)
(* mld_compute_pack_t0_t144 uses the stack down to bot. The buffers are the  *)
(* input of SHAKE256 at bot + 23781 (the seed, k and l), tr at bot + 23845,  *)
(* the seed buffer at bot + 23909 (rho, rho' at bot + 23941 and the key at   *)
(* bot + 24005) and four polynomials at bot + 24037 (for s2 and then s1).    *)
(* The aligned SSE stores through RBP need its alignment, and the            *)
(* simulation of the legacy SSE loads needs the old values of the vector     *)
(* registers as variables (YMM_GHOST_TAC).                                   *)
(* ------------------------------------------------------------------------- *)

let KP44_N n = mk_small_numeral n;;

let KP44_CONST = IMAGE_CONST_RULE_FOR mldsa_native_libmldsa_gcc12_O2_mc
  (layout "mldsa44_keypair_internal_consts") 16;;

let KP_SUBWORD_JOIN = prove
 (`!(h:int128) (l:int128).
        word_subword (word_join h l:int256) (0,128):int128 = l`,
  CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* The calls, with the FULL theorems of the callees assumed as "H_SHAKE",    *)
(* "H_ETA", "H_PACK", "H_NTT", "H_CPT" and "H_PACKSK". The events before a   *)
(* call are functions of the public arguments, rho (rhov), the declassified  *)
(* values of the samplings (D, as a function of the nonce), bot and the      *)
(* events of the callees.                                                    *)
(* ------------------------------------------------------------------------- *)

let KP44_ALLOWED =
  [`pc:num`; `pk:int64`; `sk:int64`; `seed:int64`; `rhov:num`;
   `D:num->bool list`; `mf:int64`; `stackpointer:int64`;
   `returnaddress:int64`; `bot:int64`];;

let KP44_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc KP44_EXEC name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   KP44_ALLOWED n;;

let KP44_POLY n =
  mk_comb(`mld_poly_uniform_eta 2 (mld_keypair_rhoprime 4 4 SEED)`,
          mk_comb(`word:num->byte`,KP44_N n));;

(*** The sampling of four polynomials, with the nonce n0 in R9 and n1, n2,
     n3 pushed, after the steps m to n - 1 ***)

let KP44_ETA_TAC m n n0 n1 n2 n3 =
  X86_STEPS_TAC KP44_EXEC (m--(n-1)) THEN
  KP44_CALL_TAC "H_ETA"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`;
    `mld_keypair_rhoprime 4 4 SEED`;
    mk_comb(`word:num->int64`,KP44_N n0);
    mk_comb(`word:num->int64`,KP44_N n1);
    mk_comb(`word:num->int64`,KP44_N n2);
    mk_comb(`word:num->int64`,KP44_N n3)] n;;

(*** The packing of the polynomial of the given nonce ***)

let KP44_PACK_TAC nonce m n =
  X86_STEPS_TAC KP44_EXEC (m--(n-1)) THEN
  KP44_CALL_TAC "H_PACK" [`read RDI s`; `read RSI s`; KP44_POLY nonce] n;;

(* ------------------------------------------------------------------------- *)
(* For each nonce n of the samplings, as a numeral: the termination of its   *)
(* sampling and its declassified values D n in the form of the callee        *)
(* mldsa44_poly_uniform_eta_4x, with the nonce as val(word_zx(word n)),      *)
(* reduced by the facts val(word n) = n and word_zx(word n) = word n.        *)
(* ------------------------------------------------------------------------- *)

let KP44_USED = `\n. n < 8`;;

let KP44_NONCE_TAC =
  FIRST_ASSUM(fun th ->
    if concl th <> `mld_keypair_terminates_44 SEED` then NO_TAC else
    let tth = REWRITE_RULE[mld_keypair_terminates_44] th in
    MAP_EVERY (fun n ->
      let nt = KP44_N n in
      let uth = prove(mk_comb(KP44_USED,nt), BETA_TAC THEN ARITH_TAC) in
      let ith = SPECL [`2`; `4`; `4`; KP44_USED; `SEED:num`; nt] in
      let th1 = MP (ith MLD_KEYPAIR_TERMINATES_USED) (CONJ tth uth) in
      let th2 = REWRITE_RULE[GSYM mld_keypair_declass_44]
                 (MP (ith MLD_KEYPAIR_DECLASS_USED) uth) in
      ASSUME_TAC th1 THEN
      FIRST_ASSUM(fun dth ->
        if concl dth = `mld_keypair_declass_44 SEED = D`
        then ASSUME_TAC(REWRITE_RULE[dth] th2) else NO_TAC) THEN
      ASSUME_TAC(WORD_REDUCE_CONV
        (mk_comb(`val:byte->num`,mk_comb(`word:num->byte`,nt)))) THEN
      ASSUME_TAC(WORD_REDUCE_CONV
        (mk_comb(`word_zx:int64->byte`,mk_comb(`word:num->int64`,nt)))))
     [0;1;2;3;4;5;6;7]);;

(* ------------------------------------------------------------------------- *)
(* Facts about the buffers: the 128-bit halves of 32 bytes, the seed buffer  *)
(* from the output of SHAKE256 (with rho as rhov), and the removal of the    *)
(* facts that are no longer needed, which makes the later steps faster.      *)
(* ------------------------------------------------------------------------- *)

let KP44_HALVES_TAC tm =
  FIRST_ASSUM(fun th ->
    if can (term_match [] tm) (concl th)
    then MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                          ONCE_DEPTH_CONV NUM_ADD_CONV)
                 (MATCH_MP MLD_BYTES128_HALVES th)) THEN STRIP_TAC
    else NO_TAC);;

let KP44_SEEDBUF_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes(a,128)) s =
          num_of_bytelist(list_of_seq (mld_shake256_byte 34 x) 128)`)
         (concl th)
    then W(fun (asl,w) ->
           let ath = snd(find (fun (_,a) ->
                       concl a = `mld_keypair_rho 4 4 SEED = rhov`) asl) in
           STRIP_ASSUME_TAC
            (REWRITE_RULE[ath]
              (CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                         NUM_REDUCE_CONV)
                (MATCH_MP MLD_KEYPAIR_SEEDBUF th))))
    else NO_TAC);;

let KP44_DROP_TAC pats =
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    exists (fun p -> can (term_match [] p) (concl th)) pats)));;

(*** The vector s in the secret key, after the eight packings ***)

let KP44_SREGION n =
  subst [mk_var("s"^string_of_int n,`:x86state`),`s:x86state`]
   `!j. j < 768
        ==> read (memory :> bytes8 (word_add sk (word (128 + j)))) s =
            mld_polyvec_pack 96 mld_polyeta_pack_2 (mld_keypair_s 2 4 4 SEED)
             j`;;

let KP44_SEEDBUF_FACT c =
  subst [KP44_N c,`c:num`]
   `!j. j < 128
        ==> read (memory :> bytes8 (word_add bot (word (c + j)))) s =
            mld_keypair_seedbuf 4 4 SEED j`;;

(* ------------------------------------------------------------------------- *)
(* The parts of the simulation. To the call of mldsa_shake256: the input of  *)
(* 34 bytes from the seed (two 128-bit words) and the 16-bit word            *)
(* k + 256 * l, a constant of the image read RIP-relative.                   *)
(* ------------------------------------------------------------------------- *)

let KP44_INBUF_TH = CONV_RULE NUM_REDUCE_CONV MLD_SEED_INPUT;;

let KP44_PART1_TAC =
  KP44_NONCE_TAC THEN FULL_INIT_TAC THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(seed,32)) s = SEED`)
           (concl th)
    then MP_TAC(MATCH_MP MLD_BYTES128_HALVES th) THEN STRIP_TAC THEN
         MP_TAC(ISPECL [`seed:int64`; `32`; `read memory s0`]
                       READ_BYTES_BOUND) THEN
         REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; th] THEN
         CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN DISCH_TAC
    else NO_TAC) THEN
  X86_STEPS_TAC KP44_EXEC (1--2) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC KP44_EXEC (3--19) THEN
  YMM_GHOST_TAC `s19:x86state` ["YMM1","y1"; "YMM2","y2"] THEN
  X86_STEPS_TAC KP44_EXEC (20--20) THEN
  IMAGE_RIPREL_TAC KP44_CONST (layout "mldsa44_keypair_internal" + 0x55) THEN
  X86_STEPS_TAC KP44_EXEC (21--31) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[KP_SUBWORD_JOIN]) THEN
  SUBGOAL_THEN
   `read (memory :> bytes(word_add bot (word 23813),2)) s31 = 1028`
   ASSUME_TAC THENL
   [REWRITE_TAC[CONJUNCT1 MLD_BYTES2] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(SPECL [`word_add bot (word 23781):int64`; `SEED:num`; `4`; `4`;
                `s31:x86state`] KP44_INBUF_TH) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[mld_matrix_seed] THEN DISCH_TAC] THEN
  X86_STEPS_TAC KP44_EXEC (32--32);;

(*** The expansion of the seed into the seed buffer ***)

let KP44_PART2_TAC =
  KP44_CALL_TAC "H_SHAKE"
   [`read RDI s`; `128`; `read RDX s`; `34`;
    `SEED + 2 EXP 256 * (4 + 256 * 4)`] 33 THEN
  KP44_SEEDBUF_TAC;;

(*** The two samplings, each followed by the packings into sk ***)

let KP44_PART3_TAC =
  KP44_ETA_TAC 34 50 4 5 6 7 THEN
  KP44_PACK_TAC 4 51 55 THEN KP44_PACK_TAC 5 56 59 THEN
  KP44_PACK_TAC 6 60 63 THEN KP44_PACK_TAC 7 64 67 THEN
  KP44_ETA_TAC 68 79 0 1 2 3 THEN
  KP44_PACK_TAC 0 80 84 THEN KP44_PACK_TAC 1 85 89 THEN
  KP44_PACK_TAC 2 90 93 THEN KP44_PACK_TAC 3 94 97 THEN
  SUBGOAL_THEN (KP44_SREGION 97) ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `768 = 96 * 8`] THEN
    MATCH_MP_TAC MLD_KEYPAIR_JOIN8 THEN SIMP_TAC[MLD_KEYPAIR_S_PACK_2] THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  KP44_DROP_TAC
   [`!j. j < 96
         ==> read (memory :> bytes8 (word_add sk (word (n + j)))) s =
             mld_polyeta_pack_2 x j`];;

(*** The NTT of s1, the copy of rho into pk and the computation of t ***)

let KP44_PART4_TAC =
  X86_STEPS_TAC KP44_EXEC (98--99) THEN
  SUBGOAL_THEN
   `!i. i < 1024
        ==> read (memory :> bytes32
                   (word_add bot (word (24037 + 4 * i)))) s99 =
            mld_keypair_s 2 4 4 SEED i`
   ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1024 = 256 * 4`] THEN
    MATCH_MP_TAC MLD_KEYPAIR_JOIN32 THEN
    SIMP_TAC[MLD_KEYPAIR_S_COEFF] THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  KP44_CALL_TAC "H_NTT" [`read RDI s`; `mld_keypair_s 2 4 4 SEED`] 100 THEN
  KP44_HALVES_TAC
   `read (memory :> bytes(word_add bot (word 23909),32)) s = rhov` THEN
  YMM_GHOST_TAC `s100:x86state` ["YMM3","y3"; "YMM4","y4"] THEN
  X86_STEPS_TAC KP44_EXEC (101--109) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[KP_SUBWORD_JOIN]) THEN
  X86_STEPS_TAC KP44_EXEC (110--110) THEN
  SUBGOAL_THEN
   `!j. j < 384
        ==> read (memory :> bytes8 (word_add sk (word (512 + j)))) s110 =
            mld_polyvec_pack 96 mld_polyeta_pack_2 (mld_keypair_s 2 4 4 SEED)
             (4 * 96 + j)`
   ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `4 * 96 + j` o check (fun th ->
      can (term_match [] (KP44_SREGION 110)) (concl th))) THEN
    REWRITE_TAC[ARITH_RULE `128 + 4 * 96 + j = 512 + j`] THEN
    DISCH_THEN MATCH_MP_TAC THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  KP44_CALL_TAC "H_CPT"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`;
    `mld_polyvec_map mld_poly_ntt (mld_keypair_s 2 4 4 SEED)`;
    `\j. mld_polyvec_pack 96 mld_polyeta_pack_2 (mld_keypair_s 2 4 4 SEED)
          (4 * 96 + j)`;
    `rhov:num`] 111;;

(*** The public key, as mld_keypair_pk_44 byte by byte and as a number ***)

let KP44_PART5_TAC =
  SUBGOAL_THEN
   `mld_compute_t 4 mld_polyeta_unpack_2 96 rhov
     (mld_polyvec_map mld_poly_ntt (mld_keypair_s 2 4 4 SEED))
     (\j. mld_polyvec_pack 96 mld_polyeta_pack_2 (mld_keypair_s 2 4 4 SEED)
           (4 * 96 + j)) =
    mld_keypair_t 2 4 4 mld_polyeta_pack_2 mld_polyeta_unpack_2 96 SEED`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[mld_keypair_t] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `rhov < 2 EXP 256` (ASSUME_TAC o CONV_RULE NUM_REDUCE_CONV)
  THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check
      (fun th -> concl th = `mld_keypair_rho 4 4 SEED = rhov`)) THEN
    REWRITE_TAC[mld_keypair_rho] THEN
    MP_TAC(ISPEC `list_of_seq (mld_keypair_seedbuf 4 4 SEED) 32`
           NUM_OF_BYTELIST_BOUND) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `read (memory :> bytes(pk,32)) s111 = mld_keypair_rho 4 4 SEED`
   ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MLD_KEYPAIR_BYTES_32_OF_HALVES THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
   (SPECL [`pk:int64`; `s111:x86state`; `2`; `4`; `4`; `mld_polyeta_pack_2`;
           `mld_polyeta_unpack_2`; `96`; `SEED:num`]
          MLD_KEYPAIR_PK_BYTES)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM mld_keypair_pk_44] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `!j. j < 1312
              ==> read (memory :> bytes8 (word_add pk (word j))) s =
                  mld_keypair_pk_44 SEED j`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ETA_AX]
          (REWRITE_RULE[GSYM MLD_KEYPAIR_BYTES_EQ_BYTES8] th))
    else NO_TAC) THEN
  KP44_DROP_TAC
   [`read (memory :> bytes(pk,32)) s = x`;
    `read (memory :> bytes128 pk) s = x`;
    `read (memory :> bytes128 (word_add pk (word 16))) s = x`;
    `!j. j < 1280
         ==> read (memory :> bytes8 (word_add pk (word (32 + j)))) s = x j`];;

(*** tr = H(pk, 64), and the parts of the seed buffer for the secret key,
     after the test of the result 0 of mld_compute_pack_t0_t144 ***)

let KP44_PART6_TAC =
  X86_STEPS_TAC KP44_EXEC (112--119) THEN
  KP44_CALL_TAC "H_SHAKE"
   [`read RDI s`; `64`; `read RDX s`; `1312`;
    `num_of_bytelist(list_of_seq (mld_keypair_pk_44 SEED) 1312)`] 120 THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes(a,64)) s =
          num_of_bytelist(list_of_seq (mld_shake256_byte 1312 x) 64)`)
         (concl th)
    then ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                     (REWRITE_RULE[MLD_KEYPAIR_BYTES_EQ_BYTES8] th))
    else NO_TAC) THEN
  SUBGOAL_THEN
   `!j. j < 32
        ==> read (memory :> bytes8 (word_add bot (word (23909 + j)))) s120 =
            mld_keypair_seedbuf 4 4 SEED j`
   ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] (KP44_SEEDBUF_FACT 23909)) (concl th))) THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j < 32
        ==> read (memory :> bytes8 (word_add bot (word (24005 + j)))) s120 =
            mld_keypair_seedbuf 4 4 SEED (96 + j)`
   ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `96 + j` o check (fun th ->
      can (term_match [] (KP44_SEEDBUF_FACT 23909)) (concl th))) THEN
    REWRITE_TAC[ARITH_RULE `23909 + 96 + j = 24005 + j`] THEN
    DISCH_THEN MATCH_MP_TAC THEN SIMPLE_ARITH_TAC;
    ALL_TAC];;

(*** The rest of the secret key, and the whole as mld_keypair_sk_44 ***)

let KP44_PART7_TAC =
  X86_STEPS_TAC KP44_EXEC (121--125) THEN
  KP44_CALL_TAC "H_PACKSK"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`;
    `mld_keypair_seedbuf 4 4 SEED`;
    `mld_shake256_byte 1312
      (num_of_bytelist(list_of_seq (mld_keypair_pk_44 SEED) 1312))`;
    `\j. mld_keypair_seedbuf 4 4 SEED (96 + j)`] 126 THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
   (SPECL [`sk:int64`; `s126:x86state`; `2`; `4`; `4`; `mld_polyeta_pack_2`;
           `mld_polyeta_unpack_2`; `96`; `SEED:num`]
          MLD_KEYPAIR_SK_BYTES)) THEN
  REWRITE_TAC[GSYM mld_keypair_pk_44; GSYM mld_keypair_sk_44] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  KP44_DROP_TAC
   [`!j. j < 32 ==> read (memory :> bytes8 (word_add sk (word j))) s = x j`;
    `!j. j < 32
         ==> read (memory :> bytes8 (word_add sk (word (32 + j)))) s = x j`;
    `!j. j < 64
         ==> read (memory :> bytes8 (word_add sk (word (64 + j)))) s = x j`;
    `!j. j < 768
         ==> read (memory :> bytes8 (word_add sk (word (128 + j)))) s = x j`;
    `!j. j < 1664
         ==> read (memory :> bytes8 (word_add sk (word (896 + j)))) s = x j`;
    `!j. j < n
         ==> read (memory :> bytes8 (word_add bot (word (c + j))))
               s = mld_keypair_seedbuf 4 4 SEED x`;
    `!j. j < 64
         ==> read (memory :> bytes8 (word_add bot (word (c + j))))
               s = mld_shake256_byte 1312 x j`];;

(*** The zeroing of the buffers, with REP STOSQ and SSE stores, the test of
     the result again and the return ***)

let KP44_PART8_TAC =
  X86_STEPS_TAC KP44_EXEC (127--130) THEN
  YMM_GHOST_TAC `s130:x86state` ["YMM0","y0"] THEN
  X86_STEPS_TAC KP44_EXEC (131--157) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. rho and the declassified    *)
(* values are named rhov and D.                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP
       MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL th)
     "H_CPT") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_44_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_ETA"
  THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_SHAKE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYETA_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_PACK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECL_NTT_44_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_44_GCC12_O2_IMAGE_SUBROUTINE_FULL
   "H_PACKSK" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  ABBREV_TAC `rhov = mld_keypair_rho 4 4 SEED` THEN
  ABBREV_TAC `D = mld_keypair_declass_44 SEED` THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst KP44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REALIGN_TAC 28228 THEN REALIGN_FRAME_TAC 28228 28228 THEN
  REALIGN_NONOV_TAC 28197
   [`pk:int64,1312`; `sk:int64,2560`; `seed:int64,32`;
    `word pc:int64,libmldsa_size`; `word(pc + got_memset):int64,8`;
    `ea:int64,el:num`;
    `word_add stackpointer (word 28228):int64,8`] THEN
  REALIGN_ALIGNED_TAC [28181; 23717] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  KP44_PART1_TAC THEN KP44_PART2_TAC THEN KP44_PART3_TAC THEN
  KP44_PART4_TAC THEN KP44_PART5_TAC THEN KP44_PART6_TAC THEN
  KP44_PART7_TAC THEN KP44_PART8_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;
