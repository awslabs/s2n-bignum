(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Key generation: the proof (see keypair_internal_65_spec.ml).              *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/keypair_internal_65_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_keypair.ml";;

let KP65_EXEC = MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The frame of 5504 bytes is at stackpointer + 37936 (the 37936 bytes below *)
(* it are those of mld_compute_pack_t0_t165), with the saved registers at    *)
(* stackpointer + 37952, the fourth nonce of the samplings at                *)
(* stackpointer + 37936, the canary at stackpointer + 43432 and the buffers, *)
(* aligned to 32 bytes, from b = stackpointer + 38048 or + 38064: s1 (5      *)
(* polynomials) at b, the seed buffer at b + 5120 (rho, rho' at b + 5152 and *)
(* the key at b + 5216), tr at b + 5248 and the input of SHAKE256 (the seed, *)
(* k and l) at b + 5312.                                                     *)
(* ------------------------------------------------------------------------- *)

let KP65_BUFFER_ADDRESS = MEXP_BUFFER_ADDRESS_RULE 38079 38048 38064;;

let KP65_N n = mk_small_numeral n;;

let KP65_SP n =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
          mk_comb(`word:num->int64`,KP65_N n));;

let KP65_ST n = mk_var("s"^string_of_int n,`:armstate`);;

(* ------------------------------------------------------------------------- *)
(* The calls, with the FULL theorems of the callees assumed as "H_SHAKE",    *)
(* "H_ETA", "H_PACK", "H_NTT", "H_CPT", "H_PACKSK" and "H_MEMSET". The       *)
(* events before a call are functions of the public arguments, rho (rhov)    *)
(* and the declassified values of the samplings (D, as a function of the     *)
(* nonce), of the events of the callees and of the functions f_ev_a, f_ev_u  *)
(* of the template.                                                          *)
(* ------------------------------------------------------------------------- *)

let KP65_ALLOWED =
  [`pc:num`; `pk:int64`; `sk:int64`; `seed:int64`; `rhov:num`;
   `D:num->bool list`; `guard:int64`; `mf:int64`; `stackpointer:int64`;
   `returnaddress:int64`];;

let KP65_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc KP65_EXEC name ilist
   KP65_ALLOWED n;;

let KP65_POLY n =
  mk_comb(`mld_poly_uniform_eta 4 (mld_keypair_rhoprime 6 5 SEED)`,
          mk_comb(`word:num->byte`,KP65_N n));;

(*** The sampling of four polynomials, with the nonces n0, n1, n2 in X5, X6,
     X7 and the byte n3 at the stack pointer, after the steps m to n - 1 ***)

let KP65_ETA_TAC m n n0 n1 n2 n3 =
  ARM_STEPS_TAC KP65_EXEC (m--(n-1)) THEN
  KP65_CALL_TAC "H_ETA"
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `mld_keypair_rhoprime 6 5 SEED`;
    mk_comb(`word:num->int64`,KP65_N n0);
    mk_comb(`word:num->int64`,KP65_N n1);
    mk_comb(`word:num->int64`,KP65_N n2);
    mk_comb(`word:num->byte`,KP65_N n3);
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] n;;

(*** The packing of the polynomial of the given nonce ***)

let KP65_PACK_TAC nonce m n =
  ARM_STEPS_TAC KP65_EXEC (m--(n-1)) THEN
  KP65_CALL_TAC "H_PACK"
   [`read X0 s`; `read X1 s`; KP65_POLY nonce; `pc:num`; `read X30 s`] n;;

(* ------------------------------------------------------------------------- *)
(* For each nonce n of the samplings, as a numeral: the termination of its   *)
(* sampling and its declassified values D n in the form of the callee        *)
(* mldsa65_poly_uniform_eta_4x, with the nonce as val(word_zx(word n)) or    *)
(* val(word n), reduced by the facts val(word n) = n and                     *)
(* word_zx(word n) = word n.                                                 *)
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
      (if n < 255 then
         ASSUME_TAC(WORD_REDUCE_CONV
           (mk_comb(`word_zx:int64->byte`,mk_comb(`word:num->int64`,nt))))
       else ALL_TAC)) [0;1;2;3;4;5;6;7;8;9;10;255]);;

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

(* ------------------------------------------------------------------------- *)
(* The vector s in the secret key, after the eleven packings.                *)
(* ------------------------------------------------------------------------- *)

let KP65_SREGION n =
  subst [KP65_ST n,`s:armstate`]
   `!j. j < 1408
        ==> read (memory :> bytes8 (word_add sk (word (128 + j)))) s =
            mld_polyvec_pack 128 mld_polyeta_pack_4 (mld_keypair_s 4 6 5 SEED)
             j`;;

(* ------------------------------------------------------------------------- *)
(* The parts of the simulation, in each case of the stack alignment, with    *)
(* the buffers from b. To the call of mldsa_shake256: the input of 34 bytes  *)
(* from the seed (two 128-bit words) and the 16-bit word k + 256 * l.        *)
(* ------------------------------------------------------------------------- *)

let KP65_INBUF_TH = CONV_RULE NUM_REDUCE_CONV MLD_SEED_INPUT;;

let KP65_PART1_TAC b =
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
  ARM_STEPS_TAC KP65_EXEC (1--7) THEN MEXP_BUFFER_TAC KP65_BUFFER_ADDRESS THEN
  ARM_STEPS_TAC KP65_EXEC (8--26) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP65_EXEC (27--34) THEN
  SUBGOAL_THEN
   (subst [KP65_SP(b + 5344),`a:int64`]
     `read (memory :> bytes(a,2)) s34 = 1286`)
   ASSUME_TAC THENL
   [REWRITE_TAC[CONJUNCT1 MLD_BYTES2] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(SPECL [KP65_SP(b + 5312); `SEED:num`; `5`; `6`; `s34:armstate`]
               KP65_INBUF_TH) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[mld_matrix_seed] THEN DISCH_TAC] THEN
  ARM_STEPS_TAC KP65_EXEC (35--35) THEN
  KP65_DROP_TAC
   [`read (memory :> bytes(seed,32)) s = SEED`;
    `read (memory :> bytes128 seed) s = x`;
    `read (memory :> bytes128 (word_add seed (word 16))) s = x`];;

(*** The expansion of the seed into the seed buffer ***)

let KP65_PART2_TAC =
  KP65_CALL_TAC "H_SHAKE"
   [`read X0 s`; `128`; `read X2 s`; `34`;
    `SEED + 2 EXP 256 * (6 + 256 * 5)`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 36 THEN
  KP65_SEEDBUF_TAC THEN
  KP65_DROP_TAC
   [`read (memory :> bytes(a,34)) s = SEED + x`;
    `read (memory :> bytes(a,2)) s = 1286`;
    `read (memory :> bytes16 a) s = word 1286`;
    `read (memory :> bytes128 a) s = word (SEED MOD n)`;
    `read (memory :> bytes128 a) s = word (SEED DIV n)`;
    `read (memory :> bytes(a,128)) s =
     num_of_bytelist(list_of_seq (mld_shake256_byte 34 x) 128)`];;

(*** The three samplings, each followed by the packings into sk ***)

let KP65_PART3_TAC =
  KP65_ETA_TAC 37 48 7 8 9 10 THEN
  KP65_PACK_TAC 7 49 52 THEN KP65_PACK_TAC 8 53 56 THEN
  KP65_PACK_TAC 9 57 60 THEN KP65_PACK_TAC 10 61 64 THEN
  KP65_ETA_TAC 65 76 4 5 6 255 THEN
  KP65_PACK_TAC 4 77 81 THEN KP65_PACK_TAC 5 82 85 THEN
  KP65_PACK_TAC 6 86 89 THEN
  KP65_ETA_TAC 90 101 0 1 2 3 THEN
  KP65_PACK_TAC 0 102 105 THEN KP65_PACK_TAC 1 106 109 THEN
  KP65_PACK_TAC 2 110 113 THEN KP65_PACK_TAC 3 114 117 THEN
  SUBGOAL_THEN (KP65_SREGION 117) ASSUME_TAC THENL
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

let KP65_PART4_TAC b =
  ARM_STEPS_TAC KP65_EXEC (118--119) THEN
  SUBGOAL_THEN
   (subst [KP65_N b,`b:num`]
     `!i. i < 1280
          ==> read (memory :> bytes32
                     (word_add stackpointer (word (b + 4 * i)))) s119 =
              mld_keypair_s 4 6 5 SEED i`)
   ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1280 = 256 * 5`] THEN
    MATCH_MP_TAC MLD_KEYPAIR_JOIN32 THEN
    SIMP_TAC[MLD_KEYPAIR_S_COEFF] THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  KP65_CALL_TAC "H_NTT"
   [`read X0 s`; `mld_keypair_s 4 6 5 SEED`; `pc:num`; `read SP s`;
    `read X30 s`] 120 THEN
  KP65_HALVES_TAC
   (subst [KP65_SP(b + 5120),`a:int64`]
     `read (memory :> bytes(a,32)) s = rhov`) THEN
  ARM_STEPS_TAC KP65_EXEC (121--128) THEN
  SUBGOAL_THEN
   `!j. j < 768
        ==> read (memory :> bytes8 (word_add sk (word (768 + j)))) s128 =
            mld_polyvec_pack 128 mld_polyeta_pack_4 (mld_keypair_s 4 6 5 SEED)
             (5 * 128 + j)`
   ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `5 * 128 + j` o check (fun th ->
      can (term_match [] (KP65_SREGION 128)) (concl th))) THEN
    REWRITE_TAC[ARITH_RULE `128 + 5 * 128 + j = 768 + j`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  KP65_CALL_TAC "H_CPT"
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `mld_polyvec_map mld_poly_ntt (mld_keypair_s 4 6 5 SEED)`;
    `\j. mld_polyvec_pack 128 mld_polyeta_pack_4 (mld_keypair_s 4 6 5 SEED)
          (5 * 128 + j)`;
    `rhov:num`; `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 129 THEN
  KP65_DROP_TAC
   [`!j. j < 768
         ==> read (memory :> bytes8 (word_add sk (word (768 + j)))) s = x j`];;

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
   `read (memory :> bytes(pk,32)) s129 = mld_keypair_rho 6 5 SEED`
   ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MLD_KEYPAIR_BYTES_32_OF_HALVES THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
   (SPECL [`pk:int64`; `s129:armstate`; `4`; `6`; `5`; `mld_polyeta_pack_4`;
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

(*** tr = H(pk, 64), and the parts of the seed buffer for the secret key ***)

let KP65_SEEDBUF_FACT c =
  subst [KP65_N c,`c:num`]
   `!j. j < 128
        ==> read (memory :> bytes8 (word_add stackpointer (word (c + j)))) s =
            mld_keypair_seedbuf 6 5 SEED j`;;

let KP65_PART6_TAC b =
  ARM_STEPS_TAC KP65_EXEC (130--138) THEN
  KP65_CALL_TAC "H_SHAKE"
   [`read X0 s`; `64`; `read X2 s`; `1952`;
    `num_of_bytelist(list_of_seq (mld_keypair_pk_65 SEED) 1952)`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 139 THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes(a,64)) s =
          num_of_bytelist(list_of_seq (mld_shake256_byte 1952 x) 64)`)
         (concl th)
    then ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                     (REWRITE_RULE[MLD_KEYPAIR_BYTES_EQ_BYTES8] th))
    else NO_TAC) THEN
  SUBGOAL_THEN
   (subst [KP65_N(b + 5120),`c:num`]
     `!j. j < 32
          ==> read (memory :> bytes8 (word_add stackpointer (word (c + j))))
                s139 =
              mld_keypair_seedbuf 6 5 SEED j`)
   ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] (KP65_SEEDBUF_FACT(b + 5120))) (concl th))) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   (subst [KP65_N(b + 5216),`c:num`]
     `!j. j < 32
          ==> read (memory :> bytes8 (word_add stackpointer (word (c + j))))
                s139 =
              mld_keypair_seedbuf 6 5 SEED (96 + j)`)
   ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `96 + j` o check (fun th ->
      can (term_match [] (KP65_SEEDBUF_FACT(b + 5120))) (concl th))) THEN
    REWRITE_TAC[ARITH_RULE
     (subst [KP65_N(b + 5120),`c:num`; KP65_N(b + 5216),`d:num`]
       `c + 96 + j = d + j`)] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  KP65_DROP_TAC
   [`read (memory :> bytes(pk,1952)) s = x`;
    `read (memory :> bytes(a,64)) s =
     num_of_bytelist(list_of_seq (mld_shake256_byte 1952 x) 64)`];;

(*** The rest of the secret key, and the whole as mld_keypair_sk_65 ***)

let KP65_PART7_TAC =
  ARM_STEPS_TAC KP65_EXEC (140--144) THEN
  KP65_CALL_TAC "H_PACKSK"
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`;
    `mld_keypair_seedbuf 6 5 SEED`;
    `mld_shake256_byte 1952
      (num_of_bytelist(list_of_seq (mld_keypair_pk_65 SEED) 1952))`;
    `\j. mld_keypair_seedbuf 6 5 SEED (96 + j)`;
    `pc:num`; `read X30 s`] 145 THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
   (SPECL [`sk:int64`; `s145:armstate`; `4`; `6`; `5`; `mld_polyeta_pack_4`;
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
         ==> read (memory :> bytes8 (word_add stackpointer (word (c + j))))
               s = mld_keypair_seedbuf 6 5 SEED x`;
    `!j. j < 64
         ==> read (memory :> bytes8 (word_add stackpointer (word (c + j))))
               s = mld_shake256_byte 1952 x j`];;

(*** The zeroing of the buffers, the check of the canary and the return ***)

let KP65_PART8_TAC =
  ARM_STEPS_TAC KP65_EXEC (146--149) THEN LIBC_PLT_TAC KP65_EXEC 149 THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" KP65_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref KP65_ALLOWED) 154 THEN
  ARM_STEPS_TAC KP65_EXEC (155--166) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP65_EXEC (167--182) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let KP65_CASE_TAC b =
  KP65_PART1_TAC b THEN KP65_PART2_TAC THEN KP65_PART3_TAC THEN
  KP65_PART4_TAC b THEN KP65_PART5_TAC THEN KP65_PART6_TAC b THEN
  KP65_PART7_TAC THEN KP65_PART8_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. The template of the events  *)
(* has one function for each case of the stack alignment, and rho and the    *)
(* declassified values are named rhov and D.                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP
       MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_GCC12_O2_IMAGE_SUBROUTINE_FULL th)
     "H_ETA") THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP
       MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL th)
     "H_CPT") THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] th)
     "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_SHAKE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYETA_PACK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_PACK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECL_NTT_65_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_65_GCC12_O2_IMAGE_SUBROUTINE_FULL
   "H_PACKSK" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(pk:int64) (sk:int64) (seed:int64) (rho:num) (D:num->bool list)
     (guard:int64) (mf:int64) (pc:num) (stackpointer:int64)
     (returnaddress:int64).
     if aligned 32 stackpointer
     then f_ev_a pk sk seed rho D guard mf pc stackpointer returnaddress
     else f_ev_u pk sk seed rho D guard mf pc stackpointer returnaddress
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  ABBREV_TAC `rhov = mld_keypair_rho 6 5 SEED` THEN
  ABBREV_TAC `D = mld_keypair_declass_65 SEED` THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst KP65_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 43440):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
    SPECL [`pc:num`; `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--28) THEN
  ASM_CASES_TAC `aligned 32 (stackpointer:int64)` THENL
   [REWRITE_TAC[ASSUME `aligned 32 (stackpointer:int64)`] THEN
    KP65_CASE_TAC 38048;
    REWRITE_TAC[ASSUME `~aligned 32 (stackpointer:int64)`] THEN
    KP65_CASE_TAC 38064]);;

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
