(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Key generation: the proof (see keypair_internal_44_spec.ml).              *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/keypair_internal_44_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_keypair.ml";;

let KP44_EXEC = MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The frame of 4480 bytes is at stackpointer + 23616 (the 23616 bytes below *)
(* it are those of mld_compute_pack_t0_t144), with the saved registers at    *)
(* stackpointer + 23632, the fourth nonce of the samplings at                *)
(* stackpointer + 23616, the canary at stackpointer + 28088 and the buffers, *)
(* aligned to 32 bytes, from b = stackpointer + 23744 or + 23728: s1 (4      *)
(* polynomials) at b, the seed buffer at b + 4096 (rho, rho' at b + 4128 and *)
(* the key at b + 4192), tr at b + 4224 and the input of SHAKE256 (the seed, *)
(* k and l) at b + 4288.                                                     *)
(* ------------------------------------------------------------------------- *)

let KP44_BUFFER_ADDRESS = MEXP_BUFFER_ADDRESS_RULE 23759 23744 23728;;

let KP44_N n = mk_small_numeral n;;

let KP44_SP n =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
          mk_comb(`word:num->int64`,KP44_N n));;

let KP44_ST n = mk_var("s"^string_of_int n,`:armstate`);;

(* ------------------------------------------------------------------------- *)
(* The calls, with the FULL theorems of the callees assumed as "H_SHAKE",    *)
(* "H_ETA", "H_PACK", "H_NTT", "H_CPT", "H_PACKSK" and "H_MEMSET". The       *)
(* events before a call are functions of the public arguments, rho (rhov)    *)
(* and the declassified values of the samplings (D, as a function of the     *)
(* nonce), of the events of the callees and of the functions f_ev_a, f_ev_u  *)
(* of the template.                                                          *)
(* ------------------------------------------------------------------------- *)

let KP44_ALLOWED =
  [`pc:num`; `pk:int64`; `sk:int64`; `seed:int64`; `rhov:num`;
   `D:num->bool list`; `guard:int64`; `mf:int64`; `stackpointer:int64`;
   `returnaddress:int64`];;

let KP44_CALL_TAC name ilist n =
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc KP44_EXEC name ilist
   KP44_ALLOWED n;;

let KP44_POLY n =
  mk_comb(`mld_poly_uniform_eta 2 (mld_keypair_rhoprime 4 4 SEED)`,
          mk_comb(`word:num->byte`,KP44_N n));;

(*** The sampling of four polynomials, with the nonces n0, n1, n2 in X5, X6,
     X7 and the byte n3 at the stack pointer, after the steps m to n - 1 ***)

let KP44_ETA_TAC m n n0 n1 n2 n3 =
  ARM_STEPS_TAC KP44_EXEC (m--(n-1)) THEN
  KP44_CALL_TAC "H_ETA"
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `mld_keypair_rhoprime 4 4 SEED`;
    mk_comb(`word:num->int64`,KP44_N n0);
    mk_comb(`word:num->int64`,KP44_N n1);
    mk_comb(`word:num->int64`,KP44_N n2);
    mk_comb(`word:num->byte`,KP44_N n3);
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] n;;

(*** The packing of the polynomial of the given nonce ***)

let KP44_PACK_TAC nonce m n =
  ARM_STEPS_TAC KP44_EXEC (m--(n-1)) THEN
  KP44_CALL_TAC "H_PACK"
   [`read X0 s`; `read X1 s`; KP44_POLY nonce; `pc:num`; `read X30 s`] n;;

(* ------------------------------------------------------------------------- *)
(* For each nonce n of the samplings, as a numeral: the termination of its   *)
(* sampling and its declassified values D n in the form of the callee        *)
(* mldsa44_poly_uniform_eta_4x, with the nonce as val(word_zx(word n)) or    *)
(* val(word n), reduced by the facts val(word n) = n and                     *)
(* word_zx(word n) = word n.                                                 *)
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

(* ------------------------------------------------------------------------- *)
(* The vector s in the secret key, after the eleven packings.                *)
(* ------------------------------------------------------------------------- *)

let KP44_SREGION n =
  subst [KP44_ST n,`s:armstate`]
   `!j. j < 768
        ==> read (memory :> bytes8 (word_add sk (word (128 + j)))) s =
            mld_polyvec_pack 96 mld_polyeta_pack_2 (mld_keypair_s 2 4 4 SEED)
             j`;;

(* ------------------------------------------------------------------------- *)
(* The parts of the simulation, in each case of the stack alignment, with    *)
(* the buffers from b. To the call of mldsa_shake256: the input of 34 bytes  *)
(* from the seed (two 128-bit words) and the 16-bit word k + 256 * l.        *)
(* ------------------------------------------------------------------------- *)

let KP44_INBUF_TH = CONV_RULE NUM_REDUCE_CONV MLD_SEED_INPUT;;

let KP44_PART1_TAC b =
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
  ARM_STEPS_TAC KP44_EXEC (1--7) THEN MEXP_BUFFER_TAC KP44_BUFFER_ADDRESS THEN
  ARM_STEPS_TAC KP44_EXEC (8--25) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP44_EXEC (26--33) THEN
  SUBGOAL_THEN
   (subst [KP44_SP(b + 4320),`a:int64`]
     `read (memory :> bytes(a,2)) s33 = 1028`)
   ASSUME_TAC THENL
   [REWRITE_TAC[CONJUNCT1 MLD_BYTES2] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC WORD_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(SPECL [KP44_SP(b + 4288); `SEED:num`; `4`; `4`; `s33:armstate`]
               KP44_INBUF_TH) THEN
  ANTS_TAC THENL
   [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[mld_matrix_seed] THEN DISCH_TAC] THEN
  ARM_STEPS_TAC KP44_EXEC (34--34) THEN
  KP44_DROP_TAC
   [`read (memory :> bytes(seed,32)) s = SEED`;
    `read (memory :> bytes128 seed) s = x`;
    `read (memory :> bytes128 (word_add seed (word 16))) s = x`];;

(*** The expansion of the seed into the seed buffer ***)

let KP44_PART2_TAC =
  KP44_CALL_TAC "H_SHAKE"
   [`read X0 s`; `128`; `read X2 s`; `34`;
    `SEED + 2 EXP 256 * (4 + 256 * 4)`; `guard:int64`; `pc:num`;
    `read SP s`; `read X30 s`] 35 THEN
  KP44_SEEDBUF_TAC THEN
  KP44_DROP_TAC
   [`read (memory :> bytes(a,34)) s = SEED + x`;
    `read (memory :> bytes(a,2)) s = 1028`;
    `read (memory :> bytes16 a) s = word 1028`;
    `read (memory :> bytes128 a) s = word (SEED MOD n)`;
    `read (memory :> bytes128 a) s = word (SEED DIV n)`;
    `read (memory :> bytes(a,128)) s =
     num_of_bytelist(list_of_seq (mld_shake256_byte 34 x) 128)`];;

(*** The three samplings, each followed by the packings into sk ***)

let KP44_PART3_TAC =
  KP44_ETA_TAC 36 47 4 5 6 7 THEN
  KP44_PACK_TAC 4 48 51 THEN KP44_PACK_TAC 5 52 55 THEN
  KP44_PACK_TAC 6 56 59 THEN KP44_PACK_TAC 7 60 63 THEN
  KP44_ETA_TAC 64 75 0 1 2 3 THEN
  KP44_PACK_TAC 0 76 79 THEN KP44_PACK_TAC 1 80 83 THEN
  KP44_PACK_TAC 2 84 87 THEN KP44_PACK_TAC 3 88 91 THEN
  SUBGOAL_THEN (KP44_SREGION 91) ASSUME_TAC THENL
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

let KP44_PART4_TAC b =
  ARM_STEPS_TAC KP44_EXEC (92--93) THEN
  SUBGOAL_THEN
   (subst [KP44_N b,`b:num`]
     `!i. i < 1024
          ==> read (memory :> bytes32
                     (word_add stackpointer (word (b + 4 * i)))) s93 =
              mld_keypair_s 2 4 4 SEED i`)
   ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1024 = 256 * 4`] THEN
    MATCH_MP_TAC MLD_KEYPAIR_JOIN32 THEN
    SIMP_TAC[MLD_KEYPAIR_S_COEFF] THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  KP44_CALL_TAC "H_NTT"
   [`read X0 s`; `mld_keypair_s 2 4 4 SEED`; `pc:num`; `read SP s`;
    `read X30 s`] 94 THEN
  KP44_HALVES_TAC
   (subst [KP44_SP(b + 4096),`a:int64`]
     `read (memory :> bytes(a,32)) s = rhov`) THEN
  ARM_STEPS_TAC KP44_EXEC (95--102) THEN
  SUBGOAL_THEN
   `!j. j < 384
        ==> read (memory :> bytes8 (word_add sk (word (512 + j)))) s102 =
            mld_polyvec_pack 96 mld_polyeta_pack_2 (mld_keypair_s 2 4 4 SEED)
             (4 * 96 + j)`
   ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `4 * 96 + j` o check (fun th ->
      can (term_match [] (KP44_SREGION 102)) (concl th))) THEN
    REWRITE_TAC[ARITH_RULE `128 + 4 * 96 + j = 512 + j`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  KP44_CALL_TAC "H_CPT"
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`;
    `mld_polyvec_map mld_poly_ntt (mld_keypair_s 2 4 4 SEED)`;
    `\j. mld_polyvec_pack 96 mld_polyeta_pack_2 (mld_keypair_s 2 4 4 SEED)
          (4 * 96 + j)`;
    `rhov:num`; `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 103 THEN
  KP44_DROP_TAC
   [`!j. j < 384
         ==> read (memory :> bytes8 (word_add sk (word (512 + j)))) s = x j`];;

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
   `read (memory :> bytes(pk,32)) s103 = mld_keypair_rho 4 4 SEED`
   ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MLD_KEYPAIR_BYTES_32_OF_HALVES THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
   (SPECL [`pk:int64`; `s103:armstate`; `2`; `4`; `4`; `mld_polyeta_pack_2`;
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

(*** tr = H(pk, 64), and the parts of the seed buffer for the secret key ***)

let KP44_SEEDBUF_FACT c =
  subst [KP44_N c,`c:num`]
   `!j. j < 128
        ==> read (memory :> bytes8 (word_add stackpointer (word (c + j)))) s =
            mld_keypair_seedbuf 4 4 SEED j`;;

let KP44_PART6_TAC b =
  ARM_STEPS_TAC KP44_EXEC (104--112) THEN
  KP44_CALL_TAC "H_SHAKE"
   [`read X0 s`; `64`; `read X2 s`; `1312`;
    `num_of_bytelist(list_of_seq (mld_keypair_pk_44 SEED) 1312)`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 113 THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `read (memory :> bytes(a,64)) s =
          num_of_bytelist(list_of_seq (mld_shake256_byte 1312 x) 64)`)
         (concl th)
    then ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                     (REWRITE_RULE[MLD_KEYPAIR_BYTES_EQ_BYTES8] th))
    else NO_TAC) THEN
  SUBGOAL_THEN
   (subst [KP44_N(b + 4096),`c:num`]
     `!j. j < 32
          ==> read (memory :> bytes8 (word_add stackpointer (word (c + j))))
                s113 =
              mld_keypair_seedbuf 4 4 SEED j`)
   ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] (KP44_SEEDBUF_FACT(b + 4096))) (concl th))) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   (subst [KP44_N(b + 4192),`c:num`]
     `!j. j < 32
          ==> read (memory :> bytes8 (word_add stackpointer (word (c + j))))
                s113 =
              mld_keypair_seedbuf 4 4 SEED (96 + j)`)
   ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `96 + j` o check (fun th ->
      can (term_match [] (KP44_SEEDBUF_FACT(b + 4096))) (concl th))) THEN
    REWRITE_TAC[ARITH_RULE
     (subst [KP44_N(b + 4096),`c:num`; KP44_N(b + 4192),`d:num`]
       `c + 96 + j = d + j`)] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  KP44_DROP_TAC
   [`read (memory :> bytes(pk,1312)) s = x`;
    `read (memory :> bytes(a,64)) s =
     num_of_bytelist(list_of_seq (mld_shake256_byte 1312 x) 64)`];;

(*** The rest of the secret key, and the whole as mld_keypair_sk_44 ***)

let KP44_PART7_TAC =
  ARM_STEPS_TAC KP44_EXEC (114--118) THEN
  KP44_CALL_TAC "H_PACKSK"
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`;
    `mld_keypair_seedbuf 4 4 SEED`;
    `mld_shake256_byte 1312
      (num_of_bytelist(list_of_seq (mld_keypair_pk_44 SEED) 1312))`;
    `\j. mld_keypair_seedbuf 4 4 SEED (96 + j)`;
    `pc:num`; `read X30 s`] 119 THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV
   (SPECL [`sk:int64`; `s119:armstate`; `2`; `4`; `4`; `mld_polyeta_pack_2`;
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
         ==> read (memory :> bytes8 (word_add stackpointer (word (c + j))))
               s = mld_keypair_seedbuf 4 4 SEED x`;
    `!j. j < 64
         ==> read (memory :> bytes8 (word_add stackpointer (word (c + j))))
               s = mld_shake256_byte 1312 x j`];;

(*** The zeroing of the buffers, the check of the canary and the return ***)

let KP44_PART8_TAC =
  ARM_STEPS_TAC KP44_EXEC (120--123) THEN LIBC_PLT_TAC KP44_EXEC 123 THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" KP44_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref KP44_ALLOWED) 128 THEN
  ARM_STEPS_TAC KP44_EXEC (129--140) THEN MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC KP44_EXEC (141--156) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let KP44_CASE_TAC b =
  KP44_PART1_TAC b THEN KP44_PART2_TAC THEN KP44_PART3_TAC THEN
  KP44_PART4_TAC b THEN KP44_PART5_TAC THEN KP44_PART6_TAC b THEN
  KP44_PART7_TAC THEN KP44_PART8_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. The template of the events  *)
(* has one function for each case of the stack alignment, and rho and the    *)
(* declassified values are named rhov and D.                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP
       MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_44_GCC12_O2_IMAGE_SUBROUTINE_FULL th)
     "H_ETA") THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP
       MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL th)
     "H_CPT") THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] th)
     "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_SHAKE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYETA_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_PACK" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_POLYVECL_NTT_44_GCC12_O2_IMAGE_SUBROUTINE_FULL "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_44_GCC12_O2_IMAGE_SUBROUTINE_FULL
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
  ABBREV_TAC `rhov = mld_keypair_rho 4 4 SEED` THEN
  ABBREV_TAC `D = mld_keypair_declass_44 SEED` THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst KP44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 28096):int64)` THEN
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
    KP44_CASE_TAC 23744;
    REWRITE_TAC[ASSUME `~aligned 32 (stackpointer:int64)`] THEN
    KP44_CASE_TAC 23728]);;

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
