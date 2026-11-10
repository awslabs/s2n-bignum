(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Key generation: the proof (see keypair_internal_65_spec.ml).              *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/keypair_internal_65_spec.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "x86/proofs/utils/mldsa_native_keypair.ml";;
needs "x86/proofs/utils/mldsa_native_top.ml";;
needs "x86/proofs/utils/mldsa_native_api.ml";;

let KP65_EXEC = MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The frame. After REPEAT_GEN_AND_OFFSET_STACKPTR_TAC, stackpointer is the  *)
(* bottom of the 43596 bytes of stack below the return address, at           *)
(* stackpointer + 43596; the code first aligns RSP to 32 bytes, at bot +     *)
(* 43565 (see utils/mldsa_native_realign.ml), with R10 keeping the original  *)
(* RSP + 8, and then pushes a copy of the return address (at bot + 43557),   *)
(* RBP (at bot + 43549, the frame pointer), R15, R14, R13, R12, R10 and RBX, *)
(* and reserves 5440 bytes, with RSP at bot + 38061, below which             *)
(* mld_compute_pack_t0_t165 uses the stack down to bot. The buffers are the  *)
(* input of SHAKE256 at bot + 38125 (the seed, k and l), tr at bot + 38189,  *)
(* the seed buffer at bot + 38253 (rho, rho' at bot + 38285 and the key at   *)
(* bot + 38349) and 5 polynomials at bot + 38381 (for the samplings, and s1  *)
(* at the end). The aligned SSE stores through RBP need its alignment, and   *)
(* the simulation of the legacy SSE loads needs the old values of the vector *)
(* registers as variables (YMM_GHOST_TAC).                                   *)
(* ------------------------------------------------------------------------- *)

let KP65_N n = mk_small_numeral n;;

let KP65_CONST = IMAGE_CONST_RULE_FOR mldsa_native_libmldsa_gcc12_O2_mc
  (layout "mldsa65_keypair_internal_consts") 16;;

let KP65_SUBWORD_JOIN = prove
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

let KP65_ALLOWED =
  [`pc:num`; `pk:int64`; `sk:int64`; `seed:int64`; `rhov:num`;
   `D:num->bool list`; `mf:int64`; `stackpointer:int64`;
   `returnaddress:int64`; `bot:int64`];;

let KP65_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc KP65_EXEC name
   (ilist @ [`pc:num`; `read RSP s`;
             `read (memory :> bytes64 (read RSP s)) s`])
   KP65_ALLOWED n;;

let KP65_POLY n =
  mk_comb(`mld_poly_uniform_eta 4 (mld_keypair_rhoprime 6 5 SEED)`,
          mk_comb(`word:num->byte`,KP65_N n));;

(*** The sampling of four polynomials, with the nonce n0 in R9 and n1, n2,
     n3 pushed, after the steps m to n - 1 ***)

let KP65_ETA_TAC m n n0 n1 n2 n3 =
  X86_STEPS_TAC KP65_EXEC (m--(n-1)) THEN
  KP65_CALL_TAC "H_ETA"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`;
    `mld_keypair_rhoprime 6 5 SEED`;
    mk_comb(`word:num->int64`,KP65_N n0);
    mk_comb(`word:num->int64`,KP65_N n1);
    mk_comb(`word:num->int64`,KP65_N n2);
    mk_comb(`word:num->int64`,KP65_N n3)] n;;

(*** The packing of the polynomial of the given nonce ***)

let KP65_PACK_TAC nonce m n =
  X86_STEPS_TAC KP65_EXEC (m--(n-1)) THEN
  KP65_CALL_TAC "H_PACK" [`read RDI s`; `read RSI s`; KP65_POLY nonce] n;;

(* ------------------------------------------------------------------------- *)
(* For each nonce n of the samplings, as a numeral: the termination of its   *)
(* sampling and its declassified values D n in the form of the callee        *)
(* mldsa65_poly_uniform_eta_4x, with the nonce as val(word_zx(word n)),      *)
(* reduced by the facts val(word n) = n and word_zx(word n) = word n. The    *)
(* nonces are those of s1 and s2 and the irrelevant nonce 255 of the         *)
(* polynomial that one call samples in vain.                                 *)
(* ------------------------------------------------------------------------- *)

let KP65_USED = `\n. n < 11 \/ n = 255`;;

let KP65_NONCE_TAC =
  FIRST_ASSUM(fun th ->
    if concl th <> `mld_keypair_terminates_65 SEED` then NO_TAC else
    let tth = REWRITE_RULE[mld_keypair_terminates_65] th in
    MAP_EVERY (fun n ->
      let nt = KP65_N n in
      let uth = prove(mk_comb(KP65_USED,nt), BETA_TAC THEN ARITH_TAC) in
      let ith = SPECL [`4`; `6`; `5`; KP65_USED; `SEED:num`; nt] in
      let th1 = MP (ith MLD_KEYPAIR_TERMINATES_USED) (CONJ tth uth) in
      let th2 = REWRITE_RULE[GSYM mld_keypair_declass_65]
                 (MP (ith MLD_KEYPAIR_DECLASS_USED) uth) in
      ASSUME_TAC th1 THEN
      FIRST_ASSUM(fun dth ->
        if concl dth = `mld_keypair_declass_65 SEED = D`
        then ASSUME_TAC(REWRITE_RULE[dth] th2) else NO_TAC) THEN
      ASSUME_TAC(WORD_REDUCE_CONV
        (mk_comb(`val:byte->num`,mk_comb(`word:num->byte`,nt)))) THEN
      ASSUME_TAC(WORD_REDUCE_CONV
        (mk_comb(`word_zx:int64->byte`,mk_comb(`word:num->int64`,nt)))))
     [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 255]);;

(* ------------------------------------------------------------------------- *)
(* Facts about the buffers: the 128-bit halves of 32 bytes, the seed buffer  *)
(* from the output of SHAKE256 (with rho as rhov), and the removal of the    *)
(* facts that are no longer needed, which makes the later steps faster.      *)
(* ------------------------------------------------------------------------- *)

let KP65_HALVES_TAC tm =
  FIRST_ASSUM(fun th ->
    if can (term_match [] tm) (concl th)
    then MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                          ONCE_DEPTH_CONV NUM_ADD_CONV)
                 (MATCH_MP MLD_BYTES128_HALVES th)) THEN STRIP_TAC
    else NO_TAC);;

let KP65_SEEDBUF_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes(a,128)) s =
          num_of_bytelist(list_of_seq (mld_shake256_byte 34 x) 128)`)
         (concl th)
    then W(fun (asl,w) ->
           let ath = snd(find (fun (_,a) ->
                       concl a = `mld_keypair_rho 6 5 SEED = rhov`) asl) in
           STRIP_ASSUME_TAC
            (REWRITE_RULE[ath]
              (CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                         NUM_REDUCE_CONV)
                (MATCH_MP MLD_KEYPAIR_SEEDBUF th))))
    else NO_TAC);;

let KP65_DROP_TAC pats =
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    exists (fun p -> can (term_match [] p) (concl th)) pats)));;

(*** The vector s in the secret key, after the 11 packings ***)

let KP65_SREGION n =
  subst [mk_var("s"^string_of_int n,`:x86state`),`s:x86state`]
   `!j. j < 1408
        ==> read (memory :> bytes8 (word_add sk (word (128 + j)))) s =
            mld_polyvec_pack 128 mld_polyeta_pack_4 (mld_keypair_s 4 6 5 SEED)
             j`;;

let KP65_SEEDBUF_FACT c =
  subst [KP65_N c,`c:num`]
   `!j. j < 128
        ==> read (memory :> bytes8 (word_add bot (word (c + j)))) s =
            mld_keypair_seedbuf 6 5 SEED j`;;

(* ------------------------------------------------------------------------- *)
(* The parts of the simulation. To the call of mldsa_shake256: the input of  *)
(* 34 bytes from the seed (two 128-bit words) and the 16-bit word k + 256 *  *)
(* l, a constant of the image read RIP-relative.                             *)
(* ------------------------------------------------------------------------- *)

let KP65_INBUF_TH = CONV_RULE NUM_REDUCE_CONV MLD_SEED_INPUT;;

let KP65_PART1_TAC =
  KP65_NONCE_TAC THEN FULL_INIT_TAC THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(seed,32)) s = SEED`)
           (concl th)
    then MP_TAC(MATCH_MP MLD_BYTES128_HALVES th) THEN STRIP_TAC THEN
         MP_TAC(ISPECL [`seed:int64`; `32`; `read memory s0`]
                       READ_BYTES_BOUND) THEN
         REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; th] THEN
         CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN DISCH_TAC
    else NO_TAC) THEN
  X86_STEPS_TAC KP65_EXEC (1--2) THEN REALIGN_RSP_TAC THEN
  X86_STEPS_TAC KP65_EXEC (3--19) THEN
  YMM_GHOST_TAC `s19:x86state` ["YMM1","y1"; "YMM2","y2"] THEN
  X86_STEPS_TAC KP65_EXEC (20--20) THEN
  IMAGE_RIPREL_CONST_TAC KP65_CONST
   (layout "mldsa65_keypair_internal" + 0x55) THEN
  X86_STEPS_TAC KP65_EXEC (21--31) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[KP65_SUBWORD_JOIN]) THEN
  SUBGOAL_THEN
   `read (memory :> bytes(word_add bot (word 38157),2)) s31 = 1286`
   ASSUME_TAC THENL
   [REWRITE_TAC[CONJUNCT1 MLD_BYTES2] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(SPECL [`word_add bot (word 38125):int64`; `SEED:num`; `5`; `6`;
                `s31:x86state`] KP65_INBUF_TH) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[mld_matrix_seed] THEN DISCH_TAC] THEN
  X86_STEPS_TAC KP65_EXEC (32--32);;

(*** The expansion of the seed into the seed buffer ***)

let KP65_PART2_TAC =
  KP65_CALL_TAC "H_SHAKE"
   [`read RDI s`; `128`; `read RDX s`; `34`;
    `SEED + 2 EXP 256 * (6 + 256 * 5)`] 33 THEN
  KP65_SEEDBUF_TAC;;

(*** The samplings, each followed by the packings into sk ***)

let KP65_PART3_TAC =
  KP65_ETA_TAC 34 50 7 8 9 10 THEN
  KP65_PACK_TAC 7 51 55 THEN KP65_PACK_TAC 8 56 59 THEN
  KP65_PACK_TAC 9 60 63 THEN KP65_PACK_TAC 10 64 67 THEN
  KP65_ETA_TAC 68 82 4 5 6 255 THEN
  KP65_PACK_TAC 4 83 87 THEN KP65_PACK_TAC 5 88 91 THEN
  KP65_PACK_TAC 6 92 95 THEN
  KP65_ETA_TAC 96 107 0 1 2 3 THEN
  KP65_PACK_TAC 0 108 112 THEN KP65_PACK_TAC 1 113 116 THEN
  KP65_PACK_TAC 2 117 121 THEN KP65_PACK_TAC 3 122 125 THEN
  SUBGOAL_THEN (KP65_SREGION 125) ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1408 = 128 * 11`] THEN
    MATCH_MP_TAC MLD_KEYPAIR_JOIN8 THEN SIMP_TAC[MLD_KEYPAIR_S_PACK_4] THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  KP65_DROP_TAC
   [`!j. j < 128
         ==> read (memory :> bytes8 (word_add sk (word (n + j)))) s =
             mld_polyeta_pack_4 x j`];;

(*** The NTT of s1, the copy of rho into pk and the computation of t ***)

let KP65_PART4_TAC =
  X86_STEPS_TAC KP65_EXEC (126--127) THEN
  SUBGOAL_THEN
   `!i. i < 1280
        ==> read (memory :> bytes32
                   (word_add bot (word (38381 + 4 * i)))) s127 =
            mld_keypair_s 4 6 5 SEED i`
   ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1280 = 256 * 5`] THEN
    MATCH_MP_TAC MLD_KEYPAIR_JOIN32 THEN
    SIMP_TAC[MLD_KEYPAIR_S_COEFF] THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  KP65_CALL_TAC "H_NTT" [`read RDI s`; `mld_keypair_s 4 6 5 SEED`] 128 THEN
  KP65_HALVES_TAC
   `read (memory :> bytes(word_add bot (word 38253),32)) s = rhov` THEN
  YMM_GHOST_TAC `s128:x86state` ["YMM3","y3"; "YMM4","y4"] THEN
  X86_STEPS_TAC KP65_EXEC (129--137) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[KP65_SUBWORD_JOIN]) THEN
  X86_STEPS_TAC KP65_EXEC (138--138) THEN
  SUBGOAL_THEN
   `!j. j < 768
        ==> read (memory :> bytes8 (word_add sk (word (768 + j)))) s138 =
            mld_polyvec_pack 128 mld_polyeta_pack_4 (mld_keypair_s 4 6 5 SEED)
             (5 * 128 + j)`
   ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `5 * 128 + j` o check (fun th ->
      can (term_match [] (KP65_SREGION 138)) (concl th))) THEN
    REWRITE_TAC[ARITH_RULE `128 + 5 * 128 + j = 768 + j`] THEN
    DISCH_THEN MATCH_MP_TAC THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  KP65_CALL_TAC "H_CPT"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`; `read R8 s`;
    `mld_polyvec_map mld_poly_ntt (mld_keypair_s 4 6 5 SEED)`;
    `\j. mld_polyvec_pack 128 mld_polyeta_pack_4 (mld_keypair_s 4 6 5 SEED)
          (5 * 128 + j)`;
    `rhov:num`] 139;;

(*** The public key, as mld_keypair_pk_65 byte by byte and as a number ***)

let KP65_PART5_TAC =
  SUBGOAL_THEN
   `mld_compute_t 5 mld_polyeta_unpack_4 128 rhov
     (mld_polyvec_map mld_poly_ntt (mld_keypair_s 4 6 5 SEED))
     (\j. mld_polyvec_pack 128 mld_polyeta_pack_4 (mld_keypair_s 4 6 5 SEED)
           (5 * 128 + j)) =
    mld_keypair_t 4 6 5 mld_polyeta_pack_4 mld_polyeta_unpack_4 128 SEED`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[mld_keypair_t] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `rhov < 2 EXP 256` (ASSUME_TAC o CONV_RULE NUM_REDUCE_CONV)
  THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check
      (fun th -> concl th = `mld_keypair_rho 6 5 SEED = rhov`)) THEN
    REWRITE_TAC[mld_keypair_rho] THEN
    MP_TAC(ISPEC `list_of_seq (mld_keypair_seedbuf 6 5 SEED) 32`
           NUM_OF_BYTELIST_BOUND) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `read (memory :> bytes(pk,32)) s139 = mld_keypair_rho 6 5 SEED`
   ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MLD_KEYPAIR_BYTES_32_OF_HALVES THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
   (SPECL [`pk:int64`; `s139:x86state`; `4`; `6`; `5`; `mld_polyeta_pack_4`;
           `mld_polyeta_unpack_4`; `128`; `SEED:num`]
          MLD_KEYPAIR_PK_BYTES)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM mld_keypair_pk_65] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `!j. j < 1952
              ==> read (memory :> bytes8 (word_add pk (word j))) s =
                  mld_keypair_pk_65 SEED j`) (concl th)
    then ASSUME_TAC(REWRITE_RULE[ETA_AX]
          (REWRITE_RULE[GSYM MLD_KEYPAIR_BYTES_EQ_BYTES8] th))
    else NO_TAC) THEN
  KP65_DROP_TAC
   [`read (memory :> bytes(pk,32)) s = x`;
    `read (memory :> bytes128 pk) s = x`;
    `read (memory :> bytes128 (word_add pk (word 16))) s = x`;
    `!j. j < 1920
         ==> read (memory :> bytes8 (word_add pk (word (32 + j)))) s = x j`];;

(*** tr = H(pk, 64), and the parts of the seed buffer for the secret key,
     after the test of the result 0 of mld_compute_pack_t0_t165 ***)

let KP65_PART6_TAC =
  X86_STEPS_TAC KP65_EXEC (140--147) THEN
  KP65_CALL_TAC "H_SHAKE"
   [`read RDI s`; `64`; `read RDX s`; `1952`;
    `num_of_bytelist(list_of_seq (mld_keypair_pk_65 SEED) 1952)`] 148 THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes(a,64)) s =
          num_of_bytelist(list_of_seq (mld_shake256_byte 1952 x) 64)`)
         (concl th)
    then ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                     (REWRITE_RULE[MLD_KEYPAIR_BYTES_EQ_BYTES8] th))
    else NO_TAC) THEN
  SUBGOAL_THEN
   `!j. j < 32
        ==> read (memory :> bytes8 (word_add bot (word (38253 + j)))) s148 =
            mld_keypair_seedbuf 6 5 SEED j`
   ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] (KP65_SEEDBUF_FACT 38253)) (concl th))) THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j < 32
        ==> read (memory :> bytes8 (word_add bot (word (38349 + j)))) s148 =
            mld_keypair_seedbuf 6 5 SEED (96 + j)`
   ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `96 + j` o check (fun th ->
      can (term_match [] (KP65_SEEDBUF_FACT 38253)) (concl th))) THEN
    REWRITE_TAC[ARITH_RULE `38253 + 96 + j = 38349 + j`] THEN
    DISCH_THEN MATCH_MP_TAC THEN SIMPLE_ARITH_TAC;
    ALL_TAC];;

(*** The rest of the secret key, and the whole as mld_keypair_sk_65 ***)

let KP65_PART7_TAC =
  X86_STEPS_TAC KP65_EXEC (149--153) THEN
  KP65_CALL_TAC "H_PACKSK"
   [`read RDI s`; `read RSI s`; `read RDX s`; `read RCX s`;
    `mld_keypair_seedbuf 6 5 SEED`;
    `mld_shake256_byte 1952
      (num_of_bytelist(list_of_seq (mld_keypair_pk_65 SEED) 1952))`;
    `\j. mld_keypair_seedbuf 6 5 SEED (96 + j)`] 154 THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
   (SPECL [`sk:int64`; `s154:x86state`; `4`; `6`; `5`; `mld_polyeta_pack_4`;
           `mld_polyeta_unpack_4`; `128`; `SEED:num`]
          MLD_KEYPAIR_SK_BYTES)) THEN
  REWRITE_TAC[GSYM mld_keypair_pk_65; GSYM mld_keypair_sk_65] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  KP65_DROP_TAC
   [`!j. j < 32 ==> read (memory :> bytes8 (word_add sk (word j))) s = x j`;
    `!j. j < 32
         ==> read (memory :> bytes8 (word_add sk (word (32 + j)))) s = x j`;
    `!j. j < 64
         ==> read (memory :> bytes8 (word_add sk (word (64 + j)))) s = x j`;
    `!j. j < 1408
         ==> read (memory :> bytes8 (word_add sk (word (128 + j)))) s = x j`;
    `!j. j < 2496
         ==> read (memory :> bytes8 (word_add sk (word (1536 + j)))) s = x j`;
    `!j. j < n
         ==> read (memory :> bytes8 (word_add bot (word (c + j))))
               s = mld_keypair_seedbuf 6 5 SEED x`;
    `!j. j < 64
         ==> read (memory :> bytes8 (word_add bot (word (c + j))))
               s = mld_shake256_byte 1952 x j`];;

(*** The zeroing of the buffers, with REP STOSQ and SSE stores, the test of
     the result again and the return ***)

let KP65_PART8_TAC =
  X86_STEPS_TAC KP65_EXEC (155--158) THEN
  YMM_GHOST_TAC `s158:x86state` ["YMM0","y0"] THEN
  X86_STEPS_TAC KP65_EXEC (159--185) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REALIGN_UNBOT_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. rho and the declassified    *)
(* values are named rhov and D.                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP
       MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL th)
     "H_CPT") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_ETA"
  THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_SHAKE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYETA_PACK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_PACK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECL_NTT_65_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_65_GCC12_O2_IMAGE_SUBROUTINE_FULL
   "H_PACKSK" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  ABBREV_TAC `rhov = mld_keypair_rho 6 5 SEED` THEN
  ABBREV_TAC `D = mld_keypair_declass_65 SEED` THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst KP65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REALIGN_TAC 43596 THEN REALIGN_FRAME_TAC 43596 43596 THEN
  REALIGN_NONOV_TAC 43565
   [`pk:int64,1952`; `sk:int64,4032`; `seed:int64,32`;
    `word pc:int64,libmldsa_size`; `word(pc + got_memset):int64,8`;
    `ea:int64,el:num`;
    `word_add stackpointer (word 43596):int64,8`] THEN
  REALIGN_ALIGNED_TAC [43549; 38061] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  KP65_PART1_TAC THEN KP65_PART2_TAC THEN KP65_PART3_TAC THEN
  KP65_PART4_TAC THEN KP65_PART5_TAC THEN KP65_PART6_TAC THEN
  KP65_PART7_TAC THEN KP65_PART8_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
          MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL)
        th)));;
