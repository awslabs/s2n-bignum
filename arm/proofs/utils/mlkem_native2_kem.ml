(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of key generation, encapsulation and decapsulation   *)
(* in mlkem_native2 (arm/proofs/mlkem_native/asm/mlkem512.ml, mlkem768.ml    *)
(* and mlkem1024.ml): the tables of the constants block in the forms the     *)
(* kernels take them, tactics for the steps of the functions in the image    *)
(* (the calls of the kernels as single steps with their results as ghost     *)
(* functions for the coefficients, and the loops as lemmas), and the proofs  *)
(* for a parameter set from the results of K-PKE in                          *)
(* utils/mlkem_native2_kpke.ml.                                              *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native2_kpke.ml";;
needs "arm/proofs/utils/mlkem_native2_api.ml";;
needs "arm/proofs/utils/mlkem_bytes.ml";;
needs "arm/proofs/mlkem_native/asm/mlkem_hash_g.ml";;
needs "arm/proofs/mlkem_native/asm/mlkem_gen_matrix.ml";;
needs "arm/proofs/mlkem_ntt_alt.ml";;
needs "arm/proofs/mlkem_intt_alt.ml";;
needs "arm/proofs/mlkem_mulcache_compute.ml";;
needs "arm/proofs/mlkem_tomont.ml";;
needs "arm/proofs/mlkem_reduce.ml";;
needs "arm/proofs/mlkem_add_reduce.ml";;
needs "arm/proofs/mlkem_sub_reduce.ml";;
needs "arm/proofs/mlkem_tobytes_alt.ml";;
needs "arm/proofs/mlkem_frombytes.ml";;
needs "arm/proofs/mlkem_frommsg.ml";;
needs "arm/proofs/mlkem_tomsg.ml";;

(* ------------------------------------------------------------------------- *)
(* The tables of the constants block in the forms the callees take them.     *)
(* ------------------------------------------------------------------------- *)

let mlkem_native2_ntt_z1_data = MLKEM_NATIVE2_IMAGE_DATA
  "mlkem_native2_ntt_z1_data" (layout "mlkem_native2_constants" + 192) 160;;
let mlkem_native2_ntt_z2_data = MLKEM_NATIVE2_IMAGE_DATA
  "mlkem_native2_ntt_z2_data" (layout "mlkem_native2_constants" + 352) 768;;
let mlkem_native2_intt_z1_data = MLKEM_NATIVE2_IMAGE_DATA
  "mlkem_native2_intt_z1_data" (layout "mlkem_native2_constants" + 1120) 160;;
let mlkem_native2_intt_z2_data = MLKEM_NATIVE2_IMAGE_DATA
  "mlkem_native2_intt_z2_data" (layout "mlkem_native2_constants" + 1280) 768;;
let mlkem_native2_mc_z_data = MLKEM_NATIVE2_IMAGE_DATA
  "mlkem_native2_mc_z_data" (layout "mlkem_native2_constants" + 2048) 256;;
let mlkem_native2_mc_zt_data = MLKEM_NATIVE2_IMAGE_DATA
  "mlkem_native2_mc_zt_data" (layout "mlkem_native2_constants" + 2304) 256;;
let mlkem_native2_rej_data = MLKEM_NATIVE2_IMAGE_DATA
  "mlkem_native2_rej_data" (layout "mlkem_native2_constants" + 2560) 4096;;

(*** The data as numbers of the lists that the callees take ***)

let MLKEM_NATIVE2_TABLE_NUM data lst =
  let tm = mk_eq(mk_comb(`num_of_bytelist`,lhand(concl data)),
                 mk_comb(`num_of_wordlist:int16 list->num`,lst)) in
  prove(tm,
    REWRITE_TAC[data] THEN
    CONV_TAC(RAND_CONV(REWRITE_CONV[ntt_zetas_layer01234; ntt_zetas_layer56;
       intt_zetas_layer01234; intt_zetas_layer56; mulcache_zetas;
       mulcache_zetas_twisted])) THEN
    REWRITE_TAC[MAP; num_of_bytelist; num_of_wordlist] THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
    REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV);;

(*** The tables in the forms of the preconditions, at
 *** word_add (word pc) (word(mlkem_native2_constants + off))
 ***)

let MLKEM_NATIVE2_TABLE_RULE (def,loaded) =
  let lenth = CONV_RULE(RAND_CONV LENGTH_CONV)
               (AP_TERM `LENGTH:byte list->num` def) in
  REWRITE_RULE[WORD_ADD]
   (REWRITE_RULE[bytes_loaded; READ_BYTELIST_EQ_BYTES; lenth] loaded);;

let NUM_OF_BYTELIST_WORDLIST = prove
 (`!l:byte list. num_of_bytelist l = num_of_wordlist l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[num_of_bytelist; num_of_wordlist; DIMINDEX_8] THEN
  ARITH_TAC);;

let MLKEM_NATIVE2_REJ_TABLE_DATA = prove
 (`mlkem_native2_rej_data = mlkem_rej_uniform_table`,
  REWRITE_TAC[fst mlkem_native2_rej_data; mlkem_rej_uniform_table]);;

let MLKEM_NATIVE2_REJ_TABLE = prove
 (`!s pc. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc
          ==> read (memory :> bytes(word_add (word pc) (word 31744),4096)) s =
              num_of_wordlist mlkem_rej_uniform_table`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MLKEM_NATIVE2_TABLE_RULE
                                 mlkem_native2_rej_data)) THEN
  REWRITE_TAC[MLKEM_NATIVE2_REJ_TABLE_DATA; NUM_OF_BYTELIST_WORDLIST] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN SIMP_TAC[]);;

let MLKEM_NATIVE2_RC_BYTES = prove
 (`!s pc. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc
          ==> read (memory :> bytes(word_add (word pc) (word 29184),192)) s =
              num_of_wordlist round_constants`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MLKEM_NATIVE2_TABLE_RULE
               (mlkem_native2_rc_data,MLKEM_NATIVE2_RC_DATA_LOADED))) THEN
  REWRITE_TAC[MLKEM_NATIVE2_RC_DATA] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN SIMP_TAC[]);;

(*** The zeta tables of the NTTs as 16-bit word lists ***)

let MLKEM_NATIVE2_TABLE_DEFS =
  [ntt_zetas_layer01234; ntt_zetas_layer56; intt_zetas_layer01234;
   intt_zetas_layer56; mulcache_zetas; mulcache_zetas_twisted];;

let MLKEM_NATIVE2_WORDLIST16_RULE dataval off len lst =
  let numth = MLKEM_NATIVE2_TABLE_NUM (fst dataval) lst in
  let lenth = (REWRITE_CONV(LENGTH_MAP::MLKEM_NATIVE2_TABLE_DEFS) THENC
               REWRITE_CONV[LENGTH] THENC NUM_REDUCE_CONV)
              (mk_comb(`LENGTH:int16 list->num`,lst)) in
  let addr = mk_comb(mk_comb(`word_add:int64->int64->int64`,
                             mk_comb(`word:num->int64`,`pc:num`)),
               mk_comb(`word:num->int64`,
                 mk_small_numeral(layout "mlkem_native2_constants" + off))) in
  let tm = list_mk_forall([`s:armstate`; `pc:num`],
    vsubst [addr,`a:int64`; mk_small_numeral len,`n:num`;
            lst,`l:int16 list`]
     `aligned_bytes_loaded s (word pc) mlkem_native2_image_mc
      ==> wordlist_from_memory(a,n) s = (l:int16 list)`) in
  prove(tm,
    REPEAT GEN_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP (MLKEM_NATIVE2_TABLE_RULE dataval)) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [addr; mk_small_numeral len; mk_small_numeral(2 * len);
                   lst; `s:armstate`]
            (INST_TYPE [`:16`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
    REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[lenth; GSYM numth]);;

let MLKEM_NATIVE2_NTT_Z1 = MLKEM_NATIVE2_WORDLIST16_RULE
  mlkem_native2_ntt_z1_data 192 80
  `MAP iword ntt_zetas_layer01234:int16 list`;;
let MLKEM_NATIVE2_NTT_Z2 = MLKEM_NATIVE2_WORDLIST16_RULE
  mlkem_native2_ntt_z2_data 352 384 `MAP iword ntt_zetas_layer56:int16 list`;;
let MLKEM_NATIVE2_INTT_Z1 = MLKEM_NATIVE2_WORDLIST16_RULE
  mlkem_native2_intt_z1_data 1120 80
  `MAP iword intt_zetas_layer01234:int16 list`;;
let MLKEM_NATIVE2_INTT_Z2 = MLKEM_NATIVE2_WORDLIST16_RULE
  mlkem_native2_intt_z2_data 1280 384
  `MAP iword intt_zetas_layer56:int16 list`;;

let MLKEM_NATIVE2_LENGTH16 lst =
  (REWRITE_CONV(LENGTH_MAP::MLKEM_NATIVE2_TABLE_DEFS) THENC
   REWRITE_CONV[LENGTH] THENC NUM_REDUCE_CONV)
  (mk_icomb(`LENGTH:A list->num`,lst));;

let MLKEM_NATIVE2_MULCACHE_ZETAS =
  let l1 = `MAP iword mulcache_zetas:int16 list`
  and l2 = `MAP iword mulcache_zetas_twisted:int16 list` in
  let n1 = MLKEM_NATIVE2_TABLE_NUM (fst mlkem_native2_mc_z_data) l1
  and n2 = MLKEM_NATIVE2_TABLE_NUM (fst mlkem_native2_mc_zt_data) l2
  and len1 = MLKEM_NATIVE2_LENGTH16 l1 and len2 = MLKEM_NATIVE2_LENGTH16 l2
  and len1' = MLKEM_NATIVE2_LENGTH16 `mulcache_zetas:int list`
  and len2' = MLKEM_NATIVE2_LENGTH16 `mulcache_zetas_twisted:int list` in
  prove
 (`!s pc. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc
          ==> have_mulcache_zetas (word_add (word pc) (word 31232))
                                  (word_add (word pc) (word 31488)) s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[have_mulcache_zetas] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP
    (MLKEM_NATIVE2_TABLE_RULE mlkem_native2_mc_z_data)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP
    (MLKEM_NATIVE2_TABLE_RULE mlkem_native2_mc_zt_data)) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[n1; n2] THEN REPEAT DISCH_TAC THEN
  CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THENL
   [MP_TAC(SPECL [`word_add (word pc) (word 31232):int64`; l1; `i:num`;
                  `s:armstate`] READ_MEMORY_BYTES16_EL);
    MP_TAC(SPECL [`word_add (word pc) (word 31488):int64`; l2; `i:num`;
                  `s:armstate`] READ_MEMORY_BYTES16_EL)] THEN
  ASM_REWRITE_TAC[len1; len2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC EL_MAP THEN ASM_REWRITE_TAC[len1'; len2']);;

(* ------------------------------------------------------------------------- *)
(* Vectors stored polynomial by polynomial, and the copy of values 32 bytes  *)
(* at a time.                                                                *)
(* ------------------------------------------------------------------------- *)

(*** A vector of k polynomials encoded as m bytes each, from the encodings
 *** of its polynomials
 ***)

let READ_MEMORY_BYTES_MAP_BLOCKS = prove
 (`!a m (g:int16->N word) (f:num->num->int16) s:armstate k.
     8 * m = dimindex(:N) * 256 /\
     (!j. j < k
          ==> read (memory :> bytes(word_add a (word(m * j)),m)) s =
              num_of_wordlist(MAP g (list_of_seq (f j) 256)))
     ==> read (memory :> bytes(a,m * k)) s =
         num_of_wordlist(MAP g (list_of_seq (\i. f (i DIV 256) (i MOD 256))
                                            (256 * k)))`,
  REPEAT GEN_TAC THEN SPEC_TAC(`k:num`,`k:num`) THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; list_of_seq; MAP; num_of_wordlist;
                READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL];
    STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    DISCH_TAC] THEN
  REWRITE_TAC[ARITH_RULE `m * SUC k = m * k + m`;
              ARITH_RULE `256 * SUC k = 256 * k + 256`] THEN
  REWRITE_TAC[READ_MEMORY_BYTES_SPLIT; LIST_OF_SEQ_APPEND_ADD; MAP_APPEND;
              NUM_OF_WORDLIST_APPEND] THEN
  ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_LIST_OF_SEQ] THEN
  AP_TERM_TAC THEN BINOP_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[MULT_ASSOC] THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
    REWRITE_TAC[ARITH_RULE `k < SUC k`] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC LIST_OF_SEQ_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[DIVMOD_256_BLOCK]]);;

(*** One more 32-byte block of a value v copied 16 bytes at a time ***)

let READ_MEMORY_BYTES_32_STEP = prove
 (`!a i v s:armstate.
     read (memory :> bytes(a,32 * i)) s = v MOD 2 EXP (256 * i) /\
     read (memory :> bytes128 (word_add a (word(32 * i)))) s =
     word((v DIV 2 EXP (8 * (32 * i))) MOD 2 EXP 128) /\
     read (memory :> bytes128 (word_add a (word(32 * i + 16)))) s =
     word((v DIV 2 EXP (8 * (32 * i + 16))) MOD 2 EXP 128)
     ==> read (memory :> bytes(a,32 * (i + 1))) s =
         v MOD 2 EXP (256 * (i + 1))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `32 * (i + 1) = 32 * i + 16 + 16`] THEN
  REWRITE_TAC[READ_MEMORY_BYTES_SPLIT; READ_MEMORY_BYTES_16] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_128; MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `8 * (32 * i) = 256 * i`;
              ARITH_RULE `8 * (32 * i + 16) = 256 * i + 128`;
              ARITH_RULE `256 * (i + 1) = 256 * i + 128 + 128`;
              ARITH_RULE `8 * 16 = 128`] THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV; MOD_MULT_MOD] THEN
  ARITH_TAC);;

(*** A vector of k polynomials compressed to d bits per coefficient, m
 *** bytes each, from the compressions of its polynomials
 ***)

let READ_MEMORY_BYTES_NSUM_BLOCKS = prove
 (`!a m d (g:num->num->num) s:armstate k.
     8 * m = d * 256 /\
     (!j. j < k
          ==> read (memory :> bytes(word_add a (word(m * j)),m)) s =
              nsum {i | i < 256} (\i. g j i * 2 EXP (d * i)))
     ==> read (memory :> bytes(a,m * k)) s =
         nsum {i | i < 256 * k}
              (\i. g (i DIV 256) (i MOD 256) * 2 EXP (d * i))`,
  REPEAT GEN_TAC THEN SPEC_TAC(`k:num`,`k:num`) THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; NSUM_CLAUSES_NUMSEG_LT;
                READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL];
    STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    DISCH_TAC] THEN
  REWRITE_TAC[ARITH_RULE `m * SUC k = m * k + m`;
              ARITH_RULE `256 * SUC k = 256 * k + 256`] THEN
  REWRITE_TAC[READ_MEMORY_BYTES_SPLIT; NSUM_LT_ADD] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
  REWRITE_TAC[ARITH_RULE `k < SUC k`] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM NSUM_LMUL] THEN MATCH_MP_TAC NSUM_EQ THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[DIVMOD_256_BLOCK] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD] THEN
  SUBGOAL_THEN `8 * (m * k) = d * (256 * k)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[MULT_ASSOC]; REWRITE_TAC[MULT_AC]]);;

(* ------------------------------------------------------------------------- *)
(* The frames of the functions for k: the offsets of the buffers from the    *)
(* bottom of the stack used by the function (the stack pointer on entry      *)
(* less the size of the stack), where the stack of the callees comes first   *)
(* and then the frame, with the saved registers; and the sizes of the keys   *)
(* and ciphertexts.                                                          *)
(* ------------------------------------------------------------------------- *)

(*** The names of the parameter sets as in FIPS 203, and their values ***)

let kp_params k = match k with
    2 -> [`2`; `3`; `2`; `10`; `4`] | 3 -> [`3`; `2`; `2`; `10`; `4`]
  | _ -> [`4`; `2`; `2`; `11`; `5`];;
let kp_param_def k = match k with
    2 -> mlkem512 | 3 -> mlkem768 | _ -> mlkem1024;;

(*** keypair_derand: the matrix A_hat, s_hat, e_hat, the mulcache of s_hat
 *** and t_hat, and the sizes of pk and sk
 ***)

let kp_cstack k = if k = 4 then 5040 else 3312;;
let kp_a k = kp_cstack k + 256;;
let kp_s k = kp_a k + 512 * k * k;;
let kp_e k = kp_s k + 512 * k;;
let kp_sc k = kp_e k + 512 * k;;
let kp_t k = kp_sc k + 256 * k;;
let kp_stack k = kp_t k + 512 * k;;
let kp_pkb k = 384 * k + 32;;
let kp_skb k = 768 * k + 96;;

(*** pke_encrypt: the mulcache of y_hat, t_hat, u, v and the message mu,
 *** and the sizes of the ciphertext and of the noise
 ***)

let pe_cstack = 64;;
let pe_yc k = pe_cstack + 96;;
let pe_t k = pe_yc k + 256 * k;;
let pe_u k = pe_t k + 512 * k;;
let pe_v k = pe_u k + 512 * k;;
let pe_m k = pe_v k + 512;;
let pe_stack k = pe_m k + 512;;
let pe_ctb k = 32 * api_du k * k + 32 * api_dv k;;
let pe_nb k = 512 * (2 * k + 1);;

(*** pke_decrypt: u, its mulcache, v, s_hat and w ***)

let pd_cstack = 64;;
let pd_u k = pd_cstack + 96;;
let pd_uc k = pd_u k + 512 * k;;
let pd_v k = pd_uc k + 256 * k;;
let pd_s k = pd_v k + 512;;
let pd_w k = pd_s k + 512 * k;;
let pd_stack k = pd_w k + 512;;

(*** enc_derand: the input and output of G, the noise and the transposed
 *** matrix
 ***)

let en_cstack k = pe_stack k;;
let en_gin k = en_cstack k + 96;;
let en_kr k = en_cstack k + 160;;
let en_noise k = en_cstack k + 288;;
let en_at k = en_noise k + 512 * (2 * k + 1);;
let en_stack k = en_at k + 512 * k * k;;

(*** dec: the input and output of G, H(ek), J(z || c), z || c, the
 *** reencryption c', the noise and the transposed matrix
 ***)

let de_cstack k = match k with 2 -> 3744 | 3 -> 5040 | _ -> 6304;;
let de_gin k = de_cstack k + 96;;
let de_kr k = de_cstack k + 160;;
let de_hek k = de_cstack k + 224;;
let de_j k = de_cstack k + 256;;
let de_zc k = de_cstack k + 384;;
let de_ct2 k = de_zc k + 32 + pe_ctb k;;
let de_noise k = de_ct2 k + pe_ctb k;;
let de_at k = de_noise k + 512 * (2 * k + 1);;
let de_stack k = de_at k + 512 * k * k;;

(* ------------------------------------------------------------------------- *)
(* Tactics for the steps of the API functions: addresses and ghosts, and the *)
(* calls of the kernels with their posts.                                    *)
(* ------------------------------------------------------------------------- *)

(*** Addresses: base + N as word_add base (word N), or base for N = 0 ***)

let api_addr_parts a =
  match a with
    Comb(Comb(Const("word_add",_),b),Comb(Const("word",_),n))
      when is_numeral n -> b,dest_small_numeral n
  | _ -> a,0;;

let api_mk_addr b n =
  if n = 0 then b else
  mk_comb(mk_comb(`word_add:int64->int64->int64`,b),
          mk_comb(`word:num->int64`,mk_small_numeral n));;

let api_sp_off a =
  let b,n = api_addr_parts a in
  if b = `stackpointer:int64` then n else failwith "api_sp_off";;

(*** The normalized read of word i of a buffer at base + N in state s ***)

let api_rd16 b nn i s =
  let off = if nn = 0 then mk_binop `( * ):num->num->num` `2` i
            else mk_binop `(+):num->num->num` (mk_small_numeral nn)
                   (mk_binop `( * ):num->num->num` `2` i) in
  vsubst [b,`b:int64`; off,`off:num`; s,`s:armstate`]
   `read (memory :> bytes16 (word_add b (word off))) s`;;

(*** The fact !i. i < n ==> read(bytes16(base + N + 2 * i)) sk = F i about
 *** the buffer at base + N, and its function F
 ***)

let api_buf_fact (b,nn) n k gl =
  let sv = state_of k in
  let ok c =
    try let iv,body = dest_forall c in
        let ant,eq = dest_imp body in
        ant = mk_binop `(<):num->num->bool` iv (mk_small_numeral n) &&
        lhand eq = api_rd16 b nn iv sv
    with Failure _ -> false in
  find_asm ok gl;;

let api_buf_fun th =
  let _,body = dest_forall(concl th) in
  let i = fst(dest_forall(concl th)) in
  mk_abs(i,rand(rand body));;

let api_fun16_at bn n k gl = api_buf_fun(api_buf_fact bn n k gl);;

let api_fun16 a n k gl = api_fun16_at (api_addr_parts a) n k gl;;

(*** Whether c mentions the buffer at base + N: word_add base (word(N + x)),
 *** or for N = 0 word_add base (word x) with x not numeral + ...
 ***)

let api_has_addr (b,nn) c =
  can (find_term (fun t ->
    match t with
      Comb(Comb(Const("word_add",_),b'),Comb(Const("word",_),x)) when b' = b ->
        if nn = 0 then
          not(is_numeral x) &&
          not(is_binary "+" x && is_numeral(lhand x))
        else is_binary "+" x && is_numeral(lhand x) &&
             dest_small_numeral(lhand x) = nn
    | _ -> false)) c;;

(*** A ghost v for the n words at base + N in state k ***)

let API_GHOST16_TAC v (b,nn) n k =
  let vt = mk_var(v,`:num->int16`) and sv = state_of k in
  let rd i = api_rd16 b nn i sv in
  let fact = mk_forall(`i:num`,
    mk_imp(mk_binop `(<):num->num->bool` `i:num` (mk_small_numeral n),
           mk_eq(rd `i:num`,mk_comb(vt,`i:num`)))) in
  SUBGOAL_THEN (mk_exists(vt,fact)) (X_CHOOSE_TAC vt) THENL
   [EXISTS_TAC (mk_abs(`i:num`,rd `i:num`)) THEN REWRITE_TAC[]; ALL_TAC];;

(*** The 16-bit words at a + 2 * i as given by a quantified fact about a
 *** base b and offset o (b + o + 2 * i), in the form a callee takes them.
 ***)

let READ16_REBASE = prove
 (`!a b off n (x:num->int16) s:armstate.
        a = word_add b (word off) /\
        (!i. i < n
             ==> read (memory :> bytes16(word_add b (word(off + 2 * i)))) s =
                 x i)
        ==> !i. i < n
                ==> read (memory :> bytes16(word_add a (word(2 * i)))) s =
                    x i`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
  ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]);;

(*** The two 16-byte words of 32 bytes p known as the number v, at s0 ***)

let API_BYTES128_OF_32_TAC p v =
  MP_TAC(SPECL [p; `32`; v; `0`; `s0:armstate`]
    READ_MEMORY_BYTES128_OF_NUM) THEN
  MP_TAC(SPECL [p; `32`; v; `16`; `s0:armstate`]
    READ_MEMORY_BYTES128_OF_NUM) THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 + 16 <= 32 /\ 16 + 16 <= 32`; WORD_ADD_0;
                  MULT_CLAUSES; EXP; DIV_1] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REPEAT DISCH_TAC;;

(*** The input of G: the 32 bytes of d (as two 16-byte words) and a byte ***)

let READ_MEMORY_BYTES_33_OF_PIECES = prove
 (`!a (d:byte list) c s:armstate.
     LENGTH d = 32 /\
     read (memory :> bytes128 a) s = word(num_of_bytelist d MOD 2 EXP 128) /\
     read (memory :> bytes128 (word_add a (word 16))) s =
     word((num_of_bytelist d DIV 2 EXP 128) MOD 2 EXP 128) /\
     read (memory :> bytes8 (word_add a (word 32))) s = c
     ==> read (memory :> bytes(a,33)) s = num_of_bytelist(APPEND d [c])`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `33 = 16 + 16 + 1`; READ_MEMORY_BYTES_SPLIT] THEN
  REWRITE_TAC[READ_MEMORY_BYTES_16; READ_MEMORY_BYTES_1] THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  ASM_REWRITE_TAC[NUM_OF_BYTELIST_APPEND; num_of_bytelist; VAL_WORD;
                  DIMINDEX_128; MOD_MOD_REFL] THEN
  MP_TAC(ISPEC `d:byte list` NUM_OF_BYTELIST_BOUND) THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`num_of_bytelist(d:byte list)`,`x:num`) THEN GEN_TAC THEN
  DISCH_TAC THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  SUBGOAL_THEN `x DIV 2 EXP 128 < 2 EXP 128` ASSUME_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
    UNDISCH_TAC `x < 256 EXP 32` THEN CONV_TAC NUM_REDUCE_CONV THEN
    ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT]] THEN
  MP_TAC(SPECL [`x:num`; `2 EXP 128`] DIVISION) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(*** G = SHA3-512 on the 33 bytes d || K at a, the output at X0 ***)

let API_HASH_G_CALL_TAC exec d kbyte k gl =
  let a = find_read_fact `X1` k gl and sv = state_of k in
  let m = mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,d),
                  mk_list([mk_comb(`word:num->byte`,mk_small_numeral kbyte)],
                          `:byte`)) in
  let gin = SPECL [a; d; mk_comb(`word:num->byte`,mk_small_numeral kbyte); sv]
              READ_MEMORY_BYTES_33_OF_PIECES in
  let ldth = find_asm (fun c ->
    c = mk_eq(mk_comb(`LENGTH:byte list->num`,d),`32`)) gl in
  let lenth = (REWRITE_CONV[LENGTH_APPEND; LENGTH; ldth] THENC
               NUM_REDUCE_CONV) (mk_comb(`LENGTH:byte list->num`,m)) in
  let th = REWRITE_RULE[lenth]
            (SPECL [find_read_fact `X0` k gl; a; m; find_read_fact `X3` k gl;
                    `pc:num`; find_read_fact `SP` k gl;
                    find_read_fact `X30` k gl]
                   MLKEM_HASH_G_SUBROUTINE_CORRECT) in
  (MP_TAC gin THEN ANTS_TAC THENL
    [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
     CONV_TAC(DEPTH_CONV NUM_EXP_CONV) THEN ASM_REWRITE_TAC[] THEN NO_TAC;
     DISCH_TAC] THEN
   FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[WORD_ADD] o
     MATCH_MP MLKEM_NATIVE2_ROUND_CONSTANTS o
     check (can (term_match [] `aligned_bytes_loaded s (word pc) mc`) o
            concl)) THEN
   ARM_SUBROUTINE_SIM_TAC
    (mlkem_native2_image_mc,exec,0,mlkem_native2_image_mc,th) [] (k+1)) gl;;

(*** The facts about the constants block from the image, at a state ***)

let API_CONSTS_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `aligned_bytes_loaded s (word pc) mc`) (concl th)
    then MAP_EVERY (fun lem -> ASSUME_TAC(MATCH_MP lem th))
          [MLKEM_NATIVE2_RC_BYTES; MLKEM_NATIVE2_REJ_TABLE;
           REWRITE_RULE[WORD_ADD] (SPEC_ALL MLKEM_NATIVE2_ROUND_CONSTANTS)]
    else NO_TAC);;

(*** G's output: rho and sigma from the 64 bytes of SHA3-512 at a ***)

let API_G_SPLIT_TAC k =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read (memory :> bytes(a,64)) s =
                            num_of_bytelist(sha3_512 m)`) c &&
       rand(lhand c) = state_of k
    then ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                     (MATCH_MP MLKEM_G_BYTES th))
    else NO_TAC) THEN
  RULE_ASSUM_TAC(fun th ->
    if is_conj(concl th) &&
       can (find_term (fun t -> try fst(dest_const t) = "mlkem_g"
                                with Failure _ -> false)) (concl th)
    then th else th) THEN
  FIRST_X_ASSUM(fun th ->
    if is_conj(concl th) &&
       can (find_term (fun t -> try fst(dest_const t) = "mlkem_g"
                                with Failure _ -> false)) (concl th)
    then MAP_EVERY ASSUME_TAC (CONJUNCTS th) else NO_TAC);;

(*** A call of a function of the image as one step, by its theorem with
 *** the variables given and the addresses normalized
 ***)

let API_IMAGE_CALL_TAC exec th k =
  let th' = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th in
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native2_image_mc,exec,0,mlkem_native2_image_mc,th') [] (k+1);;

(*** The round constants as a word list at the current state k, from the
 *** image (the simulation does not keep wordlist_from_memory facts)
 ***)

let API_RC_TAC k =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `aligned_bytes_loaded s (word pc) mc`) c &&
       rand(rator(rator c)) = state_of k
    then ASSUME_TAC(REWRITE_RULE[WORD_ADD]
                     (MATCH_MP MLKEM_NATIVE2_ROUND_CONSTANTS th))
    else NO_TAC);;

(*** The precondition form at an address a = base + N ***)

let API_PRE16_TAC a n k gl =
  let b,nn = api_addr_parts a in
  let th = api_buf_fact (b,nn) n k gl in
  if nn = 0 then ASSUME_TAC th gl else
  ASSUME_TAC(BETA_RULE(MATCH_MP READ16_REBASE (CONJ (REFL a) th))) gl;;

(*** Facts !s pc. aligned_bytes_loaded s (word pc) image ==> P s at the
 *** current state k
 ***)

let API_IMAGE_FACTS_TAC lems k =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `aligned_bytes_loaded s (word pc) mc`) c &&
       rand(rator(rator c)) = state_of k
    then MAP_EVERY (fun lem -> ASSUME_TAC(MATCH_MP lem th)) lems
    else NO_TAC);;

(*** The function F of a callee-form fact about address a at state k ***)

let api_pre16_fun a k gl =
  let sv = state_of k in
  let ok c =
    try let iv,body = dest_forall c in
        let _,eq = dest_imp body in
        lhand eq = vsubst [iv,`i:num`; a,`a:int64`; sv,`s:armstate`]
          `read (memory :> bytes16 (word_add a (word(2 * i)))) s`
    with Failure _ -> false in
  let c = concl(find_asm ok gl) in
  let iv,body = dest_forall c in
  mk_abs(iv,rand(rand body));;

(*** The NTT of the polynomial at X0, the zetas from the image ***)

let API_NTT_CALL_TAC exec k gl =
  let a = find_read_fact `X0` k gl in
  (API_PRE16_TAC a 256 k THEN
   API_IMAGE_FACTS_TAC [MLKEM_NATIVE2_NTT_Z1; MLKEM_NATIVE2_NTT_Z2] k THEN
   (fun gl ->
     let f = api_pre16_fun a k gl in
     ARM_SUBROUTINE_SIM_TAC
      (mlkem_native2_image_mc,exec,
       layout "mlkem_ntt_alt",mlkem_ntt_alt_mc,
       MLKEM_NTT_ALT_SUBROUTINE_CORRECT)
      [`read X0 s`; `read X1 s`; `read X2 s`;
       `MAP iword ntt_zetas_layer01234:int16 list`;
       `MAP iword ntt_zetas_layer56:int16 list`; f;
       `pc + mlkem_ntt_alt`; `read SP s`; `read X30 s`] (k+1) gl)) gl;;

(*** The CBD coefficients as 16-bit words: congruent to those of the
 *** polynomial mlkem_cbd eta b, and small
 ***)

let API_CBD_CONG = prove
 (`!eta b i.
        (eta = 2 \/ eta = 3) /\ i < 256
        ==> (ival(iword(mlkem_cbd_coeff eta b i):int16) ==
             coeff i (mlkem_cbd eta b)) (mod &3329) /\
            abs(ival(iword(mlkem_cbd_coeff eta b i):int16)) <= &eta`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (DISJ_CASES_THEN SUBST1_TAC) ASSUME_TAC) THEN
  REWRITE_TAC[MLKEM_CBD_COEFF_2; MLKEM_CBD_COEFF_3] THENL
   [MATCH_MP_TAC MLKEM_NATIVE_CBD2_CONG;
    MATCH_MP_TAC MLKEM_NATIVE_CBD3_CONG] THEN
  ASM_REWRITE_TAC[]);;

(*** After the NTT of noise polynomial eta, b (CBD input) at base + N
 *** in state k: the ghost v with its coefficients congruent to those of
 *** mlkem_ntt (mlkem_cbd eta b) and bounded
 ***)

let API_NTT_POST_TAC v bn eta b k (asl,w as gl) =
  let sv = state_of k in
  let isfn c = can (find_term (fun t ->
     try fst(dest_const t) = "forward_ntt" with Failure _ -> false)) c in
  let hasaddr c = api_has_addr bn c in
  let ispost c = free_in sv c && isfn c && hasaddr c in
  let etan = mk_small_numeral eta in
  let vt = mk_var(v,`:num->int16`) in
  let goal = vsubst [vt,`v:num->int16`; etan,`eta:num`; b,`b:byte list`]
   `!i. i < 256
        ==> (ival((v:num->int16) i) == mlkem_ntt (mlkem_cbd eta b) i)
            (mod &3329) /\
            abs(ival((v:num->int16) i)) <= &23594` in
  let isghost c =
    try let _,body = dest_forall c in
        let _,eq = dest_imp body in
        rator(rand eq) = vt && free_in sv c
    with Failure _ -> false in
  (FIRST_X_ASSUM(fun pth ->
     let c = concl pth in
     if is_imp c && ispost c then
       SUBGOAL_THEN (lhand c) (fun ath -> ASSUME_TAC(MP pth ath)) THENL
        [REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
         MP_TAC(SPECL [etan; b; `i:num`] API_CBD_CONG) THEN
         ASM_REWRITE_TAC[ARITH_EQ] THEN INT_ARITH_TAC;
         ALL_TAC]
     else NO_TAC) THEN
   API_GHOST16_TAC v bn 256 k THEN
   SUBGOAL_THEN goal ASSUME_TAC THENL
    [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
     FIRST_ASSUM(fun th -> if isghost(concl th)
       then SUBST1_TAC(SYM(MP (SPEC `i:num` th) (ASSUME `i < 256`)))
       else NO_TAC) THEN
     FIRST_X_ASSUM(fun th -> if is_forall(concl th) && ispost(concl th)
                            then MP_TAC(SPEC `i:num` th) else NO_TAC) THEN
     ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
     STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC MLKEM_NATIVE_NTT_CONG THEN
     EXISTS_TAC (mk_abs(`j:num`,vsubst [etan,`eta:num`; b,`b:byte list`]
       `iword(mlkem_cbd_coeff eta b j):int16`)) THEN
     REWRITE_TAC[MLKEM_CBD_IN_RQ] THEN
     CONJ_TAC THENL
      [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
       MP_TAC(SPECL [etan; b; `n:num`] API_CBD_CONG) THEN
       ASM_REWRITE_TAC[ARITH_EQ] THEN SIMP_TAC[];
       FIRST_X_ASSUM(MP_TAC o check (fun th -> isfn(concl th) &&
                                     not(is_forall(concl th)))) THEN
       REWRITE_TAC[o_DEF]];
     FIRST_X_ASSUM(fun th -> if is_forall(concl th) && ispost(concl th)
                            then ALL_TAC else NO_TAC)]) gl;;

(*** The mulcache of the polynomial at X1 into X0, the zetas from the
 *** image
 ***)

let API_MULCACHE_CALL_TAC exec k gl =
  let a = find_read_fact `X1` k gl in
  (API_PRE16_TAC a 256 k THEN
   API_IMAGE_FACTS_TAC [MLKEM_NATIVE2_MULCACHE_ZETAS] k THEN
   (fun gl ->
     let f = api_pre16_fun a k gl in
     ARM_SUBROUTINE_SIM_TAC
      (mlkem_native2_image_mc,exec,
       layout "mlkem_mulcache_compute",mlkem_mulcache_compute_mc,
       MLKEM_MULCACHE_COMPUTE_SUBROUTINE_CORRECT)
      [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; f;
       `pc + mlkem_mulcache_compute`; `read X30 s`] (k+1) gl)) gl;;

(*** A ghost v for the n words at base + N after a call at state k,
 *** with the facts goal (!p. p < m ==> ...) about it from the post (the
 *** quantified fact at state k with the numeral N, consumed) by rewriting
 *** with addr_rws and the tactic fin
 ***)

let API_POST16_TAC v bn n k goal addr_rws fin (asl,w as gl) =
  let sv = state_of k in
  let vt = mk_var(v,`:num->int16`) in
  let hasaddr c = api_has_addr bn c in
  let isghost c =
    try let _,body = dest_forall c in
        let _,eq = dest_imp body in
        rator(rand eq) = vt && free_in sv c
    with Failure _ -> false in
  let ispost c = is_forall c && free_in sv c && hasaddr c &&
                 not(isghost c) in
  let iv,_ = dest_forall goal in
  let UNGHOST_TAC bth gth (asl,w as gl) =
    let occs = setify(find_terms (fun t -> is_comb t && rator t = vt) w) in
    let inst t =
      let th = SPEC (rand t) gth in
      MP th (MP (ARITH_RULE(mk_imp(concl bth,lhand(concl th)))) bth) in
    REWRITE_TAC(map (GSYM o inst) occs) gl in
  (API_GHOST16_TAC v bn n k THEN
   SUBGOAL_THEN goal ASSUME_TAC THENL
    [X_GEN_TAC iv THEN DISCH_THEN(fun bth ->
       FIRST_ASSUM(fun gth -> if isghost(concl gth)
                              then UNGHOST_TAC bth gth else NO_TAC) THEN
       FIRST_X_ASSUM(fun pth -> if ispost(concl pth)
                                then MP_TAC(MP (SPEC iv pth) bth)
                                else NO_TAC) THEN
       REWRITE_TAC addr_rws THEN fin bth);
     FIRST_X_ASSUM(fun th -> if ispost(concl th) then ALL_TAC else NO_TAC)])
  gl;;

(*** After the mulcache of the polynomial x into base + N ***)

let API_MC_POST_TAC v bn x k =
  let goal = vsubst [mk_var(v,`:num->int16`),`v:num->int16`;
                     x,`x:num->int16`]
   `!p. p < 128
        ==> (ival((v:num->int16) p) ==
             ival((x:num->int16)(2 * p + 1)) *
             &17 pow (2 * bitreverse7 p + 1)) (mod &3329) /\
            abs(ival(v p)) <= &3328` in
  API_POST16_TAC v bn 128 k goal []
   (fun _ ->
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[mulcache; o_THM] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[INT_CONG_RREM] THEN
    SIMP_TAC[]);;

(*** The polynomial (r,c) of the matrix of gen_matrix as a buffer fact at
 *** state k
 ***)

let API_MATRIX_POLY_TAC r c k gl =
  let sv = state_of k in
  let ismat c = is_forall c && free_in sv c &&
    length(fst(strip_forall c)) = 3 &&
    can (find_term (fun t -> try fst(dest_const t) = "mlkem_sample_ntt"
                             with Failure _ -> false)) c in
  let th = find_asm ismat gl in
  let th1 = SPECL [mk_small_numeral r; mk_small_numeral c] th in
  let th2 = CONV_RULE NUM_REDUCE_CONV th1 in
  let th3 = CONV_RULE NUM_REDUCE_CONV
              (REWRITE_RULE[ADD_ASSOC; ADD_CLAUSES] th2) in
  ASSUME_TAC th3 gl;;

(*** The coefficients of SampleNTT as 16-bit words, and in [0,q) ***)

let API_SAMPLE_NTT_BOUNDS = prove
 (`!b n. mlkem_samplentt_terminates b /\ n < 256
         ==> ival(iword(mlkem_sample_ntt b n):int16) = mlkem_sample_ntt b n /\
             &0 <= mlkem_sample_ntt b n /\ mlkem_sample_ntt b n < &3329`,
  REWRITE_TAC[MLKEM_SAMPLENTT_TERMINATES_REJ] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`b:byte list`; `k:num`; `n:num`]
         MLKEM_SAMPLE_NTT_REJ_BOUND) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  MAP_EVERY UNDISCH_TAC [`&0 <= mlkem_sample_ntt b n`;
                         `mlkem_sample_ntt b n < &3329`] THEN
  INT_ARITH_TAC);;


(*** tomont, add_reduce and reduce in place, and their posts ***)

let API_TOMONT_CALL_TAC exec k gl =
  let a = find_read_fact `X0` k gl in
  let f = api_fun16 a 256 k gl in
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native2_image_mc,exec,
    layout "mlkem_tomont",mlkem_tomont_mc,MLKEM_TOMONT_SUBROUTINE_CORRECT)
   [`read X0 s`; f; `pc + mlkem_tomont`; `read X30 s`] (k+1) gl;;

let API_TOMONT_POST_TAC v bn x k =
  let goal = vsubst [mk_var(v,`:num->int16`),`v:num->int16`;
                     x,`x:num->int16`]
   `!i. i < 256
        ==> (ival((v:num->int16) i) == &65536 * ival((x:num->int16) i))
            (mod &3329) /\
            abs(ival(v i)) <= &3328` in
  API_POST16_TAC v bn 256 k goal []
   (fun _ ->
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[tomont_3329; o_THM] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[INT_CONG_RREM; INT_REDUCE_CONV `(&2:int) pow 16`] THEN
    SIMP_TAC[]);;

let API_ADD_REDUCE_CALL_TAC exec k gl =
  let a = find_read_fact `X0` k gl and b = find_read_fact `X1` k gl in
  let f = api_fun16 a 256 k gl and g = api_fun16 b 256 k gl in
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native2_image_mc,exec,
    layout "mlkem_add_reduce",mlkem_add_reduce_mc,
    MLKEM_ADD_REDUCE_SUBROUTINE_CORRECT)
   [`read X0 s`; `read X1 s`; f; g; `pc + mlkem_add_reduce`; `read X30 s`]
   (k+1) gl;;

let API_ADD_REDUCE_POST_TAC v bn x y k =
  let goal = vsubst [mk_var(v,`:num->int16`),`v:num->int16`;
                     x,`x:num->int16`; y,`y:num->int16`]
   `!i. i < 256
        ==> ival((v:num->int16) i) =
            ival(word_add ((x:num->int16) i) ((y:num->int16) i)) rem &3329` in
  let goal = rand(concl(DEPTH_CONV BETA_CONV goal)) in
  API_POST16_TAC v bn 256 k goal []
   (fun _ -> CONV_TAC(DEPTH_CONV BETA_CONV) THEN SIMP_TAC[]);;

let API_REDUCE_CALL_TAC exec k gl =
  let a = find_read_fact `X0` k gl in
  let f = api_fun16 a 256 k gl in
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native2_image_mc,exec,
    layout "mlkem_reduce",mlkem_reduce_mc,MLKEM_REDUCE_SUBROUTINE_CORRECT)
   [`read X0 s`; f; `pc + mlkem_reduce`; `read X30 s`] (k+1) gl;;

let API_REDUCE_POST_TAC v bn x k =
  let goal = vsubst [mk_var(v,`:num->int16`),`v:num->int16`;
                     x,`x:num->int16`]
   `!i. i < 256
        ==> ival((v:num->int16) i) = ival((x:num->int16) i) rem &3329` in
  API_POST16_TAC v bn 256 k goal []
   (fun _ -> CONV_TAC(DEPTH_CONV BETA_CONV) THEN SIMP_TAC[]);;

(*** The side goals of a call left by the simulation: the quantified facts
 *** of the precondition with addresses N + m + 2 * i
 ***)

let API_SIDE_TAC (asl,w as gl) =
  if (try fst(dest_const(fst(strip_comb w))) = "eventually"
      with Failure _ -> false)
  then ALL_TAC gl
  else (REWRITE_TAC[ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
        ASM_REWRITE_TAC[] THEN NO_TAC) gl;;

(*** tobytes of the polynomial at X1 (a ghost F at stackpointer + N) into X0;
 *** its post with the length discharged
 ***)

let API_TOBYTES_CALL_TAC exec k gl =
  let a = find_read_fact `X1` k gl in
  let f = api_fun16 a 256 k gl in
  let f' = try rand(concl(ETA_CONV f)) with Failure _ -> f in
  let l = mk_comb(mk_comb(`list_of_seq:(num->int16)->num->int16 list`,f'),
                  `256`) in
  (API_PRE16_TAC a 256 k THEN
   (fun gl ->
     let sv = state_of k in
     let th = find_asm (fun c ->
       try let iv,body = dest_forall c in
           let _,eq = dest_imp body in
           lhand eq = vsubst [iv,`i:num`; a,`a:int64`; sv,`s:armstate`]
             `read (memory :> bytes16 (word_add a (word(2 * i)))) s`
       with Failure _ -> false) gl in
     ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
       (MATCH_MP READ_MEMORY_BYTES16_LIST_OF_SEQ th)) gl) THEN
   ARM_SUBROUTINE_SIM_TAC
    (mlkem_native2_image_mc,exec,
     layout "mlkem_tobytes_alt",mlkem_tobytes_alt_mc,
     MLKEM_TOBYTES_ALT_SUBROUTINE_CORRECT)
    [`read X0 s`; `read X1 s`; l; `pc + mlkem_tobytes_alt`; `read X30 s`]
    (k+1) THEN
   FIRST_X_ASSUM(fun th ->
     let c = concl th in
     if is_imp c && free_in (state_of(k+1)) c &&
        can (find_term (fun t -> t = l)) c
     then MP_TAC th THEN REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN DISCH_TAC
     else NO_TAC)) gl;;

(*** The two 16-byte words of 32 bytes p known as the number v, at state k ***)

let API_BYTES128_OF_32_AT_TAC p v k =
  let sv = state_of k in
  MP_TAC(SPECL [p; `32`; v; `0`; sv] READ_MEMORY_BYTES128_OF_NUM) THEN
  MP_TAC(SPECL [p; `32`; v; `16`; sv] READ_MEMORY_BYTES128_OF_NUM) THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 + 16 <= 32 /\ 16 + 16 <= 32`; WORD_ADD_0;
                  MULT_CLAUSES; EXP; DIV_1] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REPEAT DISCH_TAC;;

(*** 32 bytes as two 16-byte words ***)

let READ_MEMORY_BYTES_32_OF_PIECES = prove
 (`!a (l:byte list) s:armstate.
     LENGTH l = 32 /\
     read (memory :> bytes128 a) s = word(num_of_bytelist l MOD 2 EXP 128) /\
     read (memory :> bytes128 (word_add a (word 16))) s =
     word((num_of_bytelist l DIV 2 EXP 128) MOD 2 EXP 128)
     ==> read (memory :> bytes(a,32)) s = num_of_bytelist l`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `32 = 16 + 16`; READ_MEMORY_BYTES_SPLIT] THEN
  REWRITE_TAC[READ_MEMORY_BYTES_16] THEN
  ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_128; MOD_MOD_REFL] THEN
  MP_TAC(ISPEC `l:byte list` NUM_OF_BYTELIST_BOUND) THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`num_of_bytelist(l:byte list)`,`x:num`) THEN GEN_TAC THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `x DIV 2 EXP 128 < 2 EXP 128` ASSUME_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
    UNDISCH_TAC `x < 256 EXP 32` THEN CONV_TAC NUM_REDUCE_CONV THEN
    ARITH_TAC;
    ASM_SIMP_TAC[MOD_LT]] THEN
  MP_TAC(SPECL [`x:num`; `2 EXP 128`] DIVISION) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(*** The 32 bytes at a known as l from their two 16-byte words, state k ***)

let API_JOIN32_TAC a l k gl =
  let sv = state_of k in
  let lenth = find_asm (fun c ->
    try lhand c = mk_comb(`LENGTH:byte list->num`,l) && rand c = `32`
    with Failure _ -> false) gl in
  let th = SPECL [a; l; sv] READ_MEMORY_BYTES_32_OF_PIECES in
  (MP_TAC th THEN ANTS_TAC THENL
    [REWRITE_TAC[lenth] THEN CONV_TAC NUM_REDUCE_CONV THEN
     CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
     ASM_REWRITE_TAC[] THEN NO_TAC;
     DISCH_TAC]) gl;;

(*** The case split of a block index j < 2 among the assumptions ***)

let API_CASES_TAC n =
  let lt = mk_small_numeral n in
  let cases = ARITH_RULE(vsubst [lt,`n:num`]
    (match n with
       2 -> `!x. x < 2 ==> x = 0 \/ x = 1`
     | 3 -> `!x. x < 3 ==> x = 0 \/ x = 1 \/ x = 2`
     | _ -> `!x. x < 4 ==> x = 0 \/ x = 1 \/ x = 2 \/ x = 3`)) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_binary "<" c && is_var(lhand c) && rand c = lt
    then REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC (MATCH_MP cases th)
    else NO_TAC);;

(*** The list of ghost functions [X0; ...] as a block function
 *** \j. EL j [X0; ...]
 ***)

let api_blk names =
  let lst = mk_list(map (fun n -> mk_var(n,`:num->int16`)) names,
                    `:num->int16`) in
  mk_abs(`j:num`,
         list_mk_icomb "EL" [`j:num`; lst]);;

(*** H = SHA3-256 of the message m at X1 (length via lenth), digest at X0 ***)

let API_HASH_H_CALL_TAC exec m lenth k gl =
  let th = REWRITE_RULE[lenth]
            (SPECL [find_read_fact `X0` k gl; find_read_fact `X1` k gl; m;
                    find_read_fact `X3` k gl; `pc:num`;
                    find_read_fact `SP` k gl; find_read_fact `X30` k gl]
                   MLKEM_HASH_H_SUBROUTINE_CORRECT) in
  (API_RC_TAC k THEN
   ARM_SUBROUTINE_SIM_TAC
    (mlkem_native2_image_mc,exec,0,mlkem_native2_image_mc,th) [] (k+1)) gl;;

(*** A lemma of the image (loops) as one step, fully specialized ***)

let API_LEMMA_STEP_TAC exec th k =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native2_image_mc,exec,0,mlkem_native2_image_mc,th) [] (k+1);;

(*** Tactic forms: the state number of the goal, stepping while the PC
 *** offset satisfies p, to a callee (the PC outside [lo,hi)) or to an offset
 ***)

let api_state_of_goal (asl,w) =
  let s = fst(dest_var(rand w)) in
  int_of_string(String.sub s 1 (String.length s - 1));;

let ON_STATE f gl = f (api_state_of_goal gl) gl;;

let rec API_STEP_WHILE_TAC exec p k gl =
  let off = get_pc_offset k gl in
  if p off then (ARM_STEPS_TAC exec [k+1] THEN
                 API_STEP_WHILE_TAC exec p (k+1)) gl
  else ALL_TAC gl;;

let API_TO_CALL_TAC exec lo hi =
  ON_STATE(API_STEP_WHILE_TAC exec (fun off -> lo <= off && off < hi));;

let API_TO_PC_TAC exec target =
  ON_STATE(API_STEP_WHILE_TAC exec (fun off -> off >= 0 && off <> target));;

(*** The calls of gen_matrix and getnoise with their theorems specialized ***)

let API_GM_CALL_TAC exec gmth args k gl =
  let r c = find_read_fact c k gl in
  let th = REWRITE_RULE[PAIRWISE; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES;
                        LENGTH_MLKEM_G; LENGTH_MLKEM_SLICE]
            (SPECL (args r) gmth) in
  API_IMAGE_CALL_TAC exec th k gl;;

let api_getnoise_th seed k gl =
  let v reg = dest_small_numeral(rand(find_read_fact reg k gl)) in
  let ns = mk_small_numeral in
  let th = SPECL [find_read_fact `X0` k gl; find_read_fact `X1` k gl; seed;
                  ns(v `X2`); ns(v `X3`); ns(v `X4`); ns(v `X5`);
                  find_read_fact `X6` k gl; `pc:num`;
                  find_read_fact `SP` k gl; find_read_fact `X30` k gl]
                 MLKEM_GETNOISE_SUBROUTINE_CORRECT in
  let th' = CONV_RULE(LAND_CONV(LAND_CONV(REWRITE_CONV[ARITH_EQ]))) th in
  REWRITE_RULE[COND_ID; LENGTH_MLKEM_G; ALL; NONOVERLAPPING_CLAUSES]
   (CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) (REWRITE_RULE[] th'));;

let API_GETNOISE_CALL_TAC exec seed k gl =
  (API_RC_TAC k THEN
   API_IMAGE_CALL_TAC exec (api_getnoise_th seed k gl) k) gl;;

(*** The kernels that depend on the parameter set, basemul_kK_alt and the
 *** compression and decompression for du and dv: the proof of a parameter
 *** set loads only its own and adds them here with their code, for the
 *** calls below
 ***)

let api_param_kernels = ref ([]:(string * thm * thm) list);;

let api_add_kernels l = api_param_kernels := !api_param_kernels @ l;;

let api_param_kernel name =
  let mc,th =
    try let _,mc,th = find (fun (n,_,_) -> n = name) !api_param_kernels in
        mc,th
    with Failure _ -> failwith("api_param_kernel: no " ^ name) in
  mc,th,layout name,parse_term("pc + " ^ name);;

(*** The definitions of the results of basemul_kK_alt (pmull, and
 *** basemul2_even etc.), added with the kernel
 ***)

let api_param_basemul_defs = ref ([]:(int * (thm * thm list)) list);;

let api_add_basemul_defs k pmull_th defs =
  api_param_basemul_defs := (k,(pmull_th,defs)) :: !api_param_basemul_defs;;

let api_basemul_defs k =
  try assoc k !api_param_basemul_defs
  with Failure _ -> failwith("api_basemul_defs: no " ^ string_of_int k);;

(*** basemul_kK of row r of the matrix (X1) by s (X2) with its mulcache (X3)
 *** into X0
 ***)

let api_basemul_th k =
  api_param_kernel("mlkem_basemul_k" ^ string_of_int k ^ "_alt");;

let API_BASEMUL_CALL_TAC exec k r kk gl =
  let ab,a = api_addr_parts(find_read_fact `X1` kk gl)
  and bb,b = api_addr_parts(find_read_fact `X2` kk gl)
  and btb,bt = api_addr_parts(find_read_fact `X3` kk gl) in
  let mc,th,off,pct = api_basemul_th k in
  (MAP_EVERY (fun c -> API_MATRIX_POLY_TAC r c kk) (0--(k-1)) THEN
   (fun gl ->
     let fs = flat(map (fun c ->
       [api_fun16_at (ab,a + 512 * c) 256 kk gl;
        api_fun16_at (bb,b + 512 * c) 256 kk gl;
        api_fun16_at (btb,bt + 256 * c) 128 kk gl]) (0--(k-1))) in
     (ARM_SUBROUTINE_SIM_TAC (mlkem_native2_image_mc,exec,off,mc,th)
       ([`read X1 s`; `read X2 s`; `read X3 s`; `read X0 s`] @ fs @
        [pct; `read SP s`; `read X30 s`]) (kk+1) THEN
      API_SIDE_TAC) gl))
  gl;;

(*** After basemul_kK of row r into stackpointer + N: the ghost v with its
 *** coefficients as in the K-PKE lemmas, in terms of sh (the s ghosts) and
 *** mc (their mulcache); sred are facts !i. i < 256 ==> ival(y' i) =
 *** ival(y i) rem &3329 for the polynomials of s already reduced
 ***)

let API_BASEMUL_POST_TAC v bn k r sh mc sred kk (asl,w as gl) =
  let sv = state_of kk in
  let rt = mk_small_numeral r and kt = mk_small_numeral k in
  let ks = string_of_int k in
  let hasc name c = can (find_term (fun t -> try fst(dest_const t) = name
                                             with Failure _ -> false)) c in
  let pth = find_asm (fun c -> is_imp c && free_in sv c &&
                               hasc ("basemul"^ks^"_even") c) gl in
  let termth = find_asm (fun c -> is_forall c &&
                           hasc "mlkem_samplentt_terminates" c) gl in
  let lt a b = mk_binop `(<):num->num->bool` a b in
  let tth c =
    let ct = mk_small_numeral c in
    MP (SPECL [rt; ct] termth) (ARITH_RULE(mk_conj(lt rt kt,lt ct kt))) in
  let seed c = rand(concl(tth c)) in
  let bnd c ith = MATCH_MP API_SAMPLE_NTT_BOUNDS (CONJ (tth c) ith) in
  let a c = mk_comb(`mlkem_sample_ntt`,seed c) in
  let vt = mk_var(v,`:num->int16`) in
  let ap f x = mk_comb(f,x) in
  let iv t = mk_comb(`ival:int16->int`,t) in
  let p = `p:num` in
  let p2 = `2 * p` and p21 = `2 * p + 1` in
  let mul x y = mk_binop `( * ):int->int->int` x y
  and add x y = mk_binop `(+):int->int->int` x y in
  let sum f = end_itlist add (map f (rev(0--(k-1)))) in
  let ev c = add (mul (ap (a c) p21) (iv(ap (el c mc) p)))
                 (mul (ap (a c) p2) (iv(ap (el c sh) p2)))
  and od c = add (mul (ap (a c) p21) (iv(ap (el c sh) p2)))
                 (mul (ap (a c) p2) (iv(ap (el c sh) p21))) in
  let cong x y = vsubst [x,`x:int`; y,`y:int`] `(x:int == y) (mod &3329)` in
  let goal = mk_forall(p,mk_imp(lt p `128`,
    mk_conj(cong (iv(ap vt p2)) (mul `&169:int` (sum ev)),
            cong (iv(ap vt p21)) (mul `&169:int` (sum od))))) in
  let ant = lhand(concl pth) in
  let ivar = fst(dest_forall ant) in
  let ith = ASSUME(lt ivar `256`) in
  let idx = [p2; p21] in
  let fin bth =
    let sub e = MP (ARITH_RULE(mk_imp(concl bth,lt e `256`))) bth in
    let ivals = flat(map (fun c -> map (fun e -> CONJUNCT1(bnd c (sub e))) idx)
                         (0--(k-1))) in
    let sreds = flat(map (fun th -> map (fun e -> MP (SPEC e th) (sub e)) idx)
                         sred) in
    let pmull_th,bdefs = api_basemul_defs k in
    REWRITE_TAC bdefs THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC(pmull_th :: o_THM :: bdefs) THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[INVERSE_MOD_CONV `inverse_mod 3329 65536`; INT_CONG_RREM] THEN
    REWRITE_TAC(ivals @ sreds) THEN
    (if sred = [] then SIMP_TAC[] else
     REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
     SIMP_TAC[]) in
  (SUBGOAL_THEN ant (fun ath -> ASSUME_TAC(MP pth ath)) THENL
    [X_GEN_TAC ivar THEN DISCH_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     MAP_EVERY (fun c -> MP_TAC(bnd c ith)) (0--(k-1)) THEN
     CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC;
     FIRST_X_ASSUM(fun th -> if concl th = concl pth then ALL_TAC
                             else NO_TAC)] THEN
   API_POST16_TAC v bn 256 kk goal
    [ARITH_RULE `2 * (2 * p) = 4 * p`;
     ARITH_RULE `2 * (2 * p + 1) = 4 * p + 2`] fin) gl;;

(*** The key generation of K-PKE for k: the encodings of t || rho at pk and
 *** of s at sk at state kk, from the ghosts SHj, EHj, MCj, PTj, PUj, TRj,
 *** SRj (j < k), as the K-PKE key pair of FIPS 203 (blocks lemma kth)
 ***)

let API_KEYGEN_TAC k kth kk gl =
  let sv = state_of kk in
  let ks = string_of_int k in
  let rho = parse_term("FST(mlkem_g(APPEND d [word "^ks^"]))")
  and sigma = parse_term("SND(mlkem_g(APPEND d [word "^ks^"]))") in
  let blk x = api_blk (map (fun j -> x^string_of_int j) (0--(k-1))) in
  let kth' = ISPECL [`d:byte list`; rho; sigma; blk "SH"; blk "EH"; blk "MC";
                     blk "PT"; blk "PU"; blk "TR"; blk "SR"] kth in
  let mth a x = ISPECL [a; `384`; `word_zx:int16->12 word`; blk x; sv;
                        mk_small_numeral k]
                  READ_MEMORY_BYTES_MAP_BLOCKS in
  let MEM_TAC =
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] in
  let pkb = 384 * k + 32 and par = api_param k in
  let pkgoal = vsubst [sv,`s:armstate`; mk_small_numeral pkb,`n:num`]
    (parse_term("read (memory :> bytes(pk,n)) s = "^
                "num_of_bytelist(FST(kpke_keygen "^par^" d))")) in
  let splitth = ARITH_RULE(mk_eq(mk_small_numeral pkb,
    mk_binop `(+):num->num->num` (mk_small_numeral(384 * k)) `32`)) in
  (MP_TAC kth' THEN ANTS_TAC THENL
    [REWRITE_TAC[PAIR] THEN CONJ_TAC THENL
      [REPEAT STRIP_TAC THEN
       MP_TAC(ISPECL [mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,
                       rho),`[word j; word i]:byte list`); `n:num`]
                API_SAMPLE_NTT_BOUNDS) THEN
       ASM_SIMP_TAC[];
       ALL_TAC] THEN
     REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
     API_CASES_TAC k THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
     ASM_SIMP_TAC[];
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN STRIP_TAC] THEN
   MP_TAC(mth `pk:int64` "TR") THEN ANTS_TAC THENL [MEM_TAC; ALL_TAC] THEN
   MP_TAC(mth `sk:int64` "SR") THEN ANTS_TAC THENL [MEM_TAC; ALL_TAC] THEN
   CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
   ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
   SUBGOAL_THEN pkgoal ASSUME_TAC THENL
    [REWRITE_TAC[splitth; READ_MEMORY_BYTES_SPLIT] THEN
     ASM_REWRITE_TAC[] THEN NO_TAC;
     ALL_TAC]) gl;;

(*** frombytes of the slice of ek at X1 into X0, and its post as the fields
 *** of ek
 ***)

let API_FROMBYTES_CALL_TAC exec ek j kk gl =
  let sv = state_of kk in
  let a = find_read_fact `X1` kk gl in
  let pk,_ = api_addr_parts a in
  let ekth = find_asm (fun c ->
    try let l,r = dest_eq c in
        rand r = ek && rand l = sv &&
        fst(dest_pair(rand(rand(rand(rator l))))) = pk
    with Failure _ -> false) gl in
  let lenth = find_asm (fun c ->
    try lhand c = mk_comb(`LENGTH:byte list->num`,ek) with Failure _ -> false)
    gl in
  let len = rand(concl lenth) in
  let lem = SPECL [pk; ek; mk_small_numeral(384 * j); `384`; sv]
                  READ_MEMORY_BYTES_SLICE in
  let lem' = REWRITE_RULE[lenth] lem in
  let th = MP lem' (CONJ ekth (ARITH_RULE(mk_binop `(<=):num->num->bool`
             (mk_binop `(+):num->num->num` (mk_small_numeral(384 * j)) `384`)
             len))) in
  let th' = if a = pk then REWRITE_RULE[WORD_ADD_0] th else th in
  let n = rand(concl th') in
  (ASSUME_TAC th' THEN
   ARM_SUBROUTINE_SIM_TAC
    (mlkem_native2_image_mc,exec,layout "mlkem_frombytes",mlkem_frombytes_mc,
     MLKEM_FROMBYTES_SUBROUTINE_CORRECT)
    [`read X0 s`; `read X1 s`; n; `pc + mlkem_frombytes`; `read X30 s`]
    (kk+1)) gl;;

let API_FROMBYTES_POST_TAC v bn ek j kk =
  let vt = mk_var(v,`:num->int16`) in
  let goal0 = vsubst [vt,`v:num->int16`; ek,`ek:byte list`;
                      mk_small_numeral j,`j:num`]
   `!i. i < 256
        ==> (v:num->int16) i =
            word((num_of_bytelist ek DIV 2 EXP (12 * (256 * j + i))) MOD
                 2 EXP 12)` in
  let goal = rand(concl(NUM_REDUCE_CONV goal0)) in
  API_POST16_TAC v bn 256 kk goal []
   (fun bth ->
     DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
     MP_TAC(SPECL [ek; mk_small_numeral j; `i:num`] FIELD_OF_SLICE_EK) THEN
     ASM_REWRITE_TAC[bth] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

(*** frommsg of the message at X1 (32 bytes known as num_of_bytelist m) ***)

let API_FROMMSG_CALL_TAC exec m kk gl =
  let n = mk_comb(`num_of_bytelist`,m) in
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native2_image_mc,exec,layout "mlkem_frommsg",mlkem_frommsg_mc,
    MLKEM_FROMMSG_SUBROUTINE_CORRECT)
   [`read X0 s`; `read X1 s`; n; `pc + mlkem_frommsg`; `read X30 s`]
   (kk+1) gl;;

let API_FROMMSG_POST_TAC v bn m kk =
  let vt = mk_var(v,`:num->int16`) in
  let goal = vsubst [vt,`v:num->int16`; m,`m:byte list`]
   `!i. i < 256
        ==> (v:num->int16) i =
            word((3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1) DIV 2)` in
  API_POST16_TAC v bn 256 kk goal [] (fun _ -> SIMP_TAC[]);;

(*** The inverse NTT of the polynomial at X0, the zetas from the image ***)

let API_INTT_CALL_TAC exec k gl =
  let a = find_read_fact `X0` k gl in
  (API_PRE16_TAC a 256 k THEN
   API_IMAGE_FACTS_TAC [MLKEM_NATIVE2_INTT_Z1; MLKEM_NATIVE2_INTT_Z2] k THEN
   (fun gl ->
     let f = api_pre16_fun a k gl in
     ARM_SUBROUTINE_SIM_TAC
      (mlkem_native2_image_mc,exec,
       layout "mlkem_intt_alt",mlkem_intt_alt_mc,
       MLKEM_INTT_ALT_SUBROUTINE_CORRECT)
      [`read X0 s`; `read X1 s`; `read X2 s`;
       `MAP iword intt_zetas_layer01234:int16 list`;
       `MAP iword intt_zetas_layer56:int16 list`; f;
       `pc + mlkem_intt_alt`; `read SP s`; `read X30 s`] (k+1) gl)) gl;;

let API_INTT_POST_TAC v bn x kk (asl,w as gl) =
  let sv = state_of kk in
  let vt = mk_var(v,`:num->int16`) in
  let goal = vsubst [vt,`v:num->int16`; x,`x:num->int16`]
   `!i. i < 256
        ==> (ival((v:num->int16) i) ==
             inverse_ntt (\n. ival((x:num->int16) n)) i) (mod &3329) /\
            abs(ival(v i)) <= &26624` in
  let isinv c = can (find_term (fun t ->
    try fst(dest_const t) = "inverse_ntt" with Failure _ -> false)) c in
  (TRY(FIRST_X_ASSUM(fun pth ->
     let c = concl pth in
     if is_imp c && free_in sv c && isinv c && api_has_addr bn c
     then MP_TAC pth THEN REWRITE_TAC[] THEN DISCH_TAC else NO_TAC)) THEN
   API_POST16_TAC v bn 256 kk goal []
    (fun _ -> CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[o_DEF] THEN
              CONV_TAC(DEPTH_CONV BETA_CONV) THEN SIMP_TAC[])) gl;;

(*** compress_d of the polynomial at X1 (all < q) into X0, the stack pointer
 *** an argument only for compress_d10, the one with a stack frame
 ***)

let api_compress_th d =
  let mc,th,lo,pct = api_param_kernel("mlkem_compress_d" ^ string_of_int d) in
  mc,th,lo,pct,(d = 10);;

let API_COMPRESS_CALL_TAC exec d kk gl =
  let a = find_read_fact `X1` kk gl in
  let f = api_fun16 a 256 kk gl in
  let f' = try rand(concl(ETA_CONV f)) with Failure _ -> f in
  let mc,th,off,pct,stk = api_compress_th d in
  let ilist = [`read X0 s`; `read X1 s`; f'; pct] @
              (if stk then [`read SP s`] else []) @ [`read X30 s`] in
  let remth = find_asm (fun c ->
    try let iv,body = dest_forall c in
        let _,eq = dest_imp body in
        lhand eq = mk_comb(`ival:int16->int`,mk_comb(f',iv)) &&
        can (find_term (fun t -> is_const t && name_of t = "rem")) (rand eq)
    with Failure _ -> false) gl in
  (ARM_SUBROUTINE_SIM_TAC (mlkem_native2_image_mc,exec,off,mc,th) ilist
    (kk+1) THEN
   FIRST_X_ASSUM(fun pth ->
     let c = concl pth in
     if is_imp c && free_in (state_of(kk+1)) c &&
        can (find_term (fun t -> is_const t && name_of t = "nsum")) c
     then MP_TAC pth THEN ANTS_TAC THENL
       [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
        FIRST_ASSUM(fun ith ->
          ACCEPT_TAC(MATCH_MP VAL_LT_OF_REM (MATCH_MP remth ith)));
        DISCH_TAC]
     else NO_TAC)) gl;;

(*** basemul_kK of t (no matrix) by y with its mulcache: the call without
 *** the matrix facts, the bound on the fields of t, and the post
 ***)

let API_BASEMUL_T_CALL_TAC exec k kk gl =
  let ab,a = api_addr_parts(find_read_fact `X1` kk gl)
  and bb,b = api_addr_parts(find_read_fact `X2` kk gl)
  and btb,bt = api_addr_parts(find_read_fact `X3` kk gl) in
  let mc,th,off,pct = api_basemul_th k in
  let fs = flat(map (fun c ->
    [api_fun16_at (ab,a + 512 * c) 256 kk gl;
     api_fun16_at (bb,b + 512 * c) 256 kk gl;
     api_fun16_at (btb,bt + 256 * c) 128 kk gl]) (0--(k-1))) in
  (ARM_SUBROUTINE_SIM_TAC (mlkem_native2_image_mc,exec,off,mc,th)
    ([`read X1 s`; `read X2 s`; `read X3 s`; `read X0 s`] @ fs @
     [pct; `read SP s`; `read X30 s`]) (kk+1) THEN
   API_SIDE_TAC) gl;;

let TT_BOUND = prove
 (`!x. abs(ival(word(x MOD 4096):int16)) <= &2 pow 12`,
  GEN_TAC THEN
  MP_TAC(ARITH_RULE `x MOD 4096 < 4096`) THEN
  SIMP_TAC[IVAL_WORD_SMALL; ARITH_RULE `x < 4096 ==> x < 32768`] THEN
  REWRITE_TAC[INT_ABS_NUM; GSYM INT_OF_NUM_LT] THEN
  CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC);;

let API_BASEMUL_T_POST_TAC v bn k tt yh mc kk (asl,w as gl) =
  let sv = state_of kk in
  let ks = string_of_int k in
  let hasc name c = can (find_term (fun t -> try fst(dest_const t) = name
                                             with Failure _ -> false)) c in
  let pth = find_asm (fun c -> is_imp c && free_in sv c &&
                               hasc ("basemul"^ks^"_even") c) gl in
  let lt a b = mk_binop `(<):num->num->bool` a b in
  let vt = mk_var(v,`:num->int16`) in
  let ap f x = mk_comb(f,x) in
  let iv t = mk_comb(`ival:int16->int`,t) in
  let p = `p:num` in
  let p2 = `2 * p` and p21 = `2 * p + 1` in
  let mul x y = mk_binop `( * ):int->int->int` x y
  and add x y = mk_binop `(+):int->int->int` x y in
  let sum f = end_itlist add (map f (rev(0--(k-1)))) in
  let ev c = add (mul (iv(ap (el c tt) p21)) (iv(ap (el c mc) p)))
                 (mul (iv(ap (el c tt) p2)) (iv(ap (el c yh) p2)))
  and od c = add (mul (iv(ap (el c tt) p21)) (iv(ap (el c yh) p2)))
                 (mul (iv(ap (el c tt) p2)) (iv(ap (el c yh) p21))) in
  let cong x y = vsubst [x,`x:int`; y,`y:int`] `(x:int == y) (mod &3329)` in
  let goal = mk_forall(p,mk_imp(lt p `128`,
    mk_conj(cong (iv(ap vt p2)) (mul `&169:int` (sum ev)),
            cong (iv(ap vt p21)) (mul `&169:int` (sum od))))) in
  let ant = lhand(concl pth) in
  let ivar = fst(dest_forall ant) in
  let fin _ =
    let pmull_th,bdefs = api_basemul_defs k in
    REWRITE_TAC bdefs THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC(pmull_th :: o_THM :: bdefs) THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC[INVERSE_MOD_CONV `inverse_mod 3329 65536`; INT_CONG_RREM] THEN
    SIMP_TAC[] in
  (SUBGOAL_THEN ant (fun ath -> ASSUME_TAC(MP pth ath)) THENL
    [X_GEN_TAC ivar THEN DISCH_TAC THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     ASM_SIMP_TAC[TT_BOUND];
     FIRST_X_ASSUM(fun th -> if concl th = concl pth then ALL_TAC
                             else NO_TAC)] THEN
   API_POST16_TAC v bn 256 kk goal
    [ARITH_RULE `2 * (2 * p) = 4 * p`;
     ARITH_RULE `2 * (2 * p + 1) = 4 * p + 2`] fin) gl;;

(*** The bound of decompressed coefficients, for the NTT ***)

let DECOMPRESS_BOUND = prove
 (`!x n h. 0 < n /\ h <= n
           ==> abs(ival(word((3329 * x MOD n + h) DIV n):int16)) <= &8191`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(3329 * x MOD n + h) DIV n <= 3329` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `a <= 3329 <=> a < 3330`] THEN
    ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
    MP_TAC(SPECL [`x:num`; `n:num`] MOD_LT_EQ) THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
    SPEC_TAC(`x MOD n`,`y:num`) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[IVAL_WORD_SMALL; ARITH_RULE `x <= 3329 ==> x < 32768`] THEN
  REWRITE_TAC[INT_ABS_NUM; INT_OF_NUM_LE] THEN ASM_ARITH_TAC);;

(*** decompress_d of the slice of c at X1 into X0, and its post ***)

let api_decompress_th d =
  api_param_kernel("mlkem_decompress_d" ^ string_of_int d);;

let API_SLICE_FACT_TAC l off len kk gl =
  let sv = state_of kk in
  let a = find_read_fact `X1` kk gl in
  let base,_ = api_addr_parts a in
  let lth = find_asm (fun c ->
    try let l',r = dest_eq c in
        rand r = l && rand l' = sv &&
        fst(dest_pair(rand(rand(rand(rator l'))))) = base
    with Failure _ -> false) gl in
  let lenth = find_asm (fun c ->
    try lhand c = mk_comb(`LENGTH:byte list->num`,l) with Failure _ -> false)
    gl in
  let lem = SPECL [base; l; mk_small_numeral off; mk_small_numeral len; sv]
                  READ_MEMORY_BYTES_SLICE in
  let lem' = REWRITE_RULE[lenth] lem in
  let th = MP lem' (CONJ lth (ARITH_RULE(mk_binop `(<=):num->num->bool`
             (mk_binop `(+):num->num->num` (mk_small_numeral off)
               (mk_small_numeral len)) (rand(concl lenth))))) in
  let th' = if a = base then REWRITE_RULE[WORD_ADD_0] th else th in
  ASSUME_TAC th' gl;;

let API_DECOMPRESS_CALL_TAC exec d c off len kk gl =
  let n = mk_comb(`num_of_bytelist`,
    list_mk_icomb "mlkem_slice"
     [mk_small_numeral off; mk_small_numeral len; c]) in
  let mc,th,lo,pct = api_decompress_th d in
  (API_SLICE_FACT_TAC c off len kk THEN
   ARM_SUBROUTINE_SIM_TAC (mlkem_native2_image_mc,exec,lo,mc,th)
    [`read X0 s`; `read X1 s`; n; pct; `read X30 s`] (kk+1)) gl;;

let API_DECOMPRESS_POST_TAC v bn c d j kk =
  let vt = mk_var(v,`:num->int16`) and n x = mk_small_numeral x in
  let goal0 = vsubst [vt,`v:num->int16`; c,`c:byte list`; n j,`j:num`;
                      n d,`d:num`; n(1 lsl (d-1)),`h:num`; n(1 lsl d),`q:num`]
   `!i. i < 256
        ==> (v:num->int16) i =
            word((3329 * (num_of_bytelist c DIV 2 EXP (d * (256 * j + i)))
                  MOD 2 EXP d + h) DIV q)` in
  let goal = rand(concl(NUM_REDUCE_CONV goal0)) in
  API_POST16_TAC v bn 256 kk goal []
   (fun bth ->
     DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
     MP_TAC(SPECL [c; n(32 * d); n d; n j; `i:num`] FIELD_OF_SLICE_BYTES) THEN
     ASM_REWRITE_TAC[bth] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let API_DECOMPRESS_V_POST_TAC v bn c d off len kk =
  let vt = mk_var(v,`:num->int16`) and n x = mk_small_numeral x in
  let goal0 = vsubst [vt,`v:num->int16`; c,`c:byte list`; n off,`off:num`;
                      n len,`len:num`; n d,`d:num`; n(1 lsl (d-1)),`h:num`;
                      n(1 lsl d),`q:num`]
   `!i. i < 256
        ==> (v:num->int16) i =
            word((3329 * (num_of_bytelist(mlkem_slice off len c) DIV
                          2 EXP (d * i)) MOD 2 EXP d + h) DIV q)` in
  let goal = rand(concl(NUM_REDUCE_CONV goal0)) in
  API_POST16_TAC v bn 256 kk goal []
   (fun _ -> CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

(*** The NTT of a polynomial known as decompressed coefficients ***)

let API_NTT_POST_PLAIN_TAC v bn x kk (asl,w as gl) =
  let sv = state_of kk in
  let isfn c = can (find_term (fun t ->
     try fst(dest_const t) = "forward_ntt" with Failure _ -> false)) c in
  let ispost c = free_in sv c && isfn c && api_has_addr bn c in
  let vt = mk_var(v,`:num->int16`) in
  let goal = vsubst [vt,`v:num->int16`; x,`x:num->int16`]
   `!i. i < 256
        ==> (ival((v:num->int16) i) ==
             forward_ntt (\n. ival((x:num->int16) n)) i) (mod &3329) /\
            abs(ival(v i)) <= &23594` in
  (FIRST_X_ASSUM(fun pth ->
     let c = concl pth in
     if is_imp c && ispost c then
       SUBGOAL_THEN (lhand c) (fun ath -> ASSUME_TAC(MP pth ath)) THENL
        [REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
         CONV_TAC(DEPTH_CONV BETA_CONV) THEN
         ASM_SIMP_TAC[] THEN MATCH_MP_TAC DECOMPRESS_BOUND THEN
         CONV_TAC NUM_REDUCE_CONV;
         ALL_TAC]
     else NO_TAC) THEN
   API_POST16_TAC v bn 256 kk goal []
    (fun _ -> CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[o_DEF] THEN
              CONV_TAC(DEPTH_CONV BETA_CONV) THEN SIMP_TAC[])) gl;;

(*** sub_reduce and tomsg ***)

let API_SUB_REDUCE_CALL_TAC exec k gl =
  let a = find_read_fact `X0` k gl and b = find_read_fact `X1` k gl in
  let f = api_fun16 a 256 k gl and g = api_fun16 b 256 k gl in
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native2_image_mc,exec,
    layout "mlkem_sub_reduce",mlkem_sub_reduce_mc,
    MLKEM_SUB_REDUCE_SUBROUTINE_CORRECT)
   [`read X0 s`; `read X1 s`; f; g; `pc + mlkem_sub_reduce`; `read X30 s`]
   (k+1) gl;;

let API_SUB_REDUCE_POST_TAC v bn x y k =
  let goal = vsubst [mk_var(v,`:num->int16`),`v:num->int16`;
                     x,`x:num->int16`; y,`y:num->int16`]
   `!i. i < 256
        ==> ival((v:num->int16) i) =
            ival(word_sub ((x:num->int16) i) ((y:num->int16) i)) rem &3329` in
  let goal = rand(concl(DEPTH_CONV BETA_CONV goal)) in
  API_POST16_TAC v bn 256 k goal []
   (fun _ -> CONV_TAC(DEPTH_CONV BETA_CONV) THEN SIMP_TAC[]);;

let API_TOMSG_CALL_TAC exec kk gl =
  let a = find_read_fact `X1` kk gl in
  let f = api_fun16 a 256 kk gl in
  let f' = try rand(concl(ETA_CONV f)) with Failure _ -> f in
  let remth = find_asm (fun c ->
    try let iv,body = dest_forall c in
        let _,eq = dest_imp body in
        lhand eq = mk_comb(`ival:int16->int`,mk_comb(f',iv)) &&
        can (find_term (fun t -> is_const t && name_of t = "rem")) (rand eq)
    with Failure _ -> false) gl in
  (ARM_SUBROUTINE_SIM_TAC
    (mlkem_native2_image_mc,exec,layout "mlkem_tomsg",mlkem_tomsg_mc,
     MLKEM_TOMSG_SUBROUTINE_CORRECT)
    [`read X0 s`; `read X1 s`; f'; `pc + mlkem_tomsg`; `read X30 s`]
    (kk+1) THEN
   FIRST_X_ASSUM(fun pth ->
     let c = concl pth in
     if is_imp c && free_in (state_of(kk+1)) c &&
        can (find_term (fun t -> is_const t && name_of t = "nsum")) c
     then MP_TAC pth THEN ANTS_TAC THENL
       [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
        FIRST_ASSUM(fun ith ->
          ACCEPT_TAC(MATCH_MP VAL_LT_OF_REM (MATCH_MP remth ith)));
        DISCH_TAC]
     else NO_TAC)) gl;;

(*** The modulus check of ek as the fields of its first 384 * k bytes ***)

let EK_FIELD_SLICE = prove
 (`!l n i. 12 * i + 12 <= 8 * n /\ n <= LENGTH l
           ==> (num_of_bytelist(mlkem_slice 0 n l) DIV 2 EXP (12 * i)) MOD
               2 EXP 12 =
               (num_of_bytelist l DIV 2 EXP (12 * i)) MOD 2 EXP 12`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLKEM_SLICE_NUM; ADD_CLAUSES] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `a <= b ==> MIN b a = a`]);;

let ek_check_slice k =
  let n x = string_of_int x in
  let par = api_param k in
  let ekth = match k with 2 -> MLKEM_EK_CHECK_512 | 3 -> MLKEM_EK_CHECK_768
                        | _ -> MLKEM_EK_CHECK_1024 in
  let bound = mk_small_numeral(256 * k) in
  prove(parse_term(
   "!ek. LENGTH ek = "^n(kp_pkb k)^" ==> "^
   "((!i. i < "^n(256 * k)^" ==> (num_of_bytelist(mlkem_slice 0 "^n(384 * k)^
   " ek) DIV 2 EXP (12 * i)) MOD 2 EXP 12 < 3329) <=> "^
   "mlkem_ek_check "^par^" ek)"),
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ekth] THEN
   CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
   AP_TERM_TAC THEN ABS_TAC THEN
   ASM_CASES_TAC (mk_binop `(<):num->num->bool` `i:num` bound) THEN
   ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   MATCH_MP_TAC EK_FIELD_SLICE THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(*** A slice fact for l (known at base, with its length) at state kk ***)

let API_SLICE_AT_TAC base l off len kk gl =
  let sv = state_of kk in
  let lth = find_asm (fun c ->
    try let l',r = dest_eq c in
        rand r = l && rand l' = sv &&
        fst(dest_pair(rand(rand(rand(rator l'))))) = base
    with Failure _ -> false) gl in
  let lenth = try find_asm (fun c ->
      try lhand c = mk_comb(`LENGTH:byte list->num`,l) && is_numeral(rand c)
      with Failure _ -> false) gl
    with Failure _ ->
      (REWRITE_CONV[LENGTH_SHA3_512; LENGTH_SHA3_256; LENGTH_APPEND] THENC
       NUM_REDUCE_CONV) (mk_comb(`LENGTH:byte list->num`,l)) in
  let lem = SPECL [base; l; mk_small_numeral off; mk_small_numeral len; sv]
                  READ_MEMORY_BYTES_SLICE in
  let lem' = REWRITE_RULE[lenth] lem in
  let th = MP lem' (CONJ lth (ARITH_RULE(mk_binop `(<=):num->num->bool`
             (mk_binop `(+):num->num->num` (mk_small_numeral off)
               (mk_small_numeral len)) (rand(concl lenth))))) in
  ASSUME_TAC (CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
              (if off = 0 then REWRITE_RULE[WORD_ADD_0] th else th)) gl;;

(*** check_encoding of the k polynomials of ek at X0 ***)

let API_CHECK_ENCODING_CALL_TAC exec k ek kk gl =
  let a = find_read_fact `X0` kk gl in
  let n = mk_comb(`num_of_bytelist`,
            list_mk_icomb "mlkem_slice"
             [`0`; mk_small_numeral(384 * k); ek]) in
  (API_SLICE_AT_TAC a ek 0 (384 * k) kk THEN
   ARM_SUBROUTINE_SIM_TAC
    (mlkem_native2_image_mc,exec,layout "mlkem_check_encoding",
     mlkem_check_encoding_mc,MLKEM_CHECK_ENCODING_K_RULE k)
    [`read X0 s`; n; `pc + mlkem_check_encoding`; `read X30 s`] (kk+1)) gl;;

(*** hash_g of a message m known at X1 (length via lenth) ***)

let API_HASH_G_MSG_CALL_TAC exec m lenth k gl =
  let th = REWRITE_RULE[lenth]
            (SPECL [find_read_fact `X0` k gl; find_read_fact `X1` k gl; m;
                    find_read_fact `X3` k gl; `pc:num`;
                    find_read_fact `SP` k gl; find_read_fact `X30` k gl]
                   MLKEM_HASH_G_SUBROUTINE_CORRECT) in
  (API_RC_TAC k THEN
   ARM_SUBROUTINE_SIM_TAC
    (mlkem_native2_image_mc,exec,0,mlkem_native2_image_mc,th) [] (k+1)) gl;;

(*** 64 bytes from two 32-byte pieces ***)

let READ_MEMORY_BYTES_64_OF_32S = prove
 (`!a (l1:byte list) l2 s:armstate.
     LENGTH l1 = 32 /\
     read (memory :> bytes(a,32)) s = num_of_bytelist l1 /\
     read (memory :> bytes(word_add a (word 32),32)) s = num_of_bytelist l2
     ==> read (memory :> bytes(a,64)) s = num_of_bytelist(APPEND l1 l2)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `64 = 32 + 32`; READ_MEMORY_BYTES_SPLIT] THEN
  ASM_REWRITE_TAC[NUM_OF_BYTELIST_APPEND]);;

(*** A case split on a condition tm of the code's branch, evaluating the
 *** branch in the PC facts
 ***)

let API_BOOL_CASE_TAC tm =
  ASM_CASES_TAC tm THEN
  POP_ASSUM(fun cth ->
    RULE_ASSUM_TAC(fun th ->
      let c = concl th in
      if can (term_match [] `read PC (s:armstate) = (x:int64)`) c &&
         free_in tm c
      then REWRITE_RULE[] (CONV_RULE(DEPTH_CONV WORD_NUM_RED_CONV)
                            (REWRITE_RULE[cth] th))
      else th) THEN
    ASSUME_TAC cth) THEN
  ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* Loops as single steps: the copies of 32-byte blocks, the zeroing of the   *)
(* stack buffers, the comparison of the ciphertexts and the selection of the *)
(* shared secret.                                                            *)
(* ------------------------------------------------------------------------- *)

(*** The copy of n 32-byte blocks from X1 to X0 with ldp/stp q0, q1 and a
 *** count in X2, from the loop at pc + loop to its end
 ***)

let api_copy_tm loop n =
  let ns = mk_small_numeral in
  vsubst [ns loop,`loop:num`; ns n,`n:num`; ns (32 * n),`len:num`;
          ns (loop + 16),`stop:num`]
  `!dst src v pc.
     nonoverlapping (dst,len) (src,len) /\
     nonoverlapping (dst,len) (word pc,mlkem_native2_image_size)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + loop) /\
               read X0 s = dst /\ read X1 s = src /\ read X2 s = word n /\
               read (memory :> bytes(src,len)) s = v)
          (\s. read PC s = word(pc + stop) /\
               read (memory :> bytes(dst,len)) s = v)
          (MAYCHANGE [PC; X0; X1; X2] ,, MAYCHANGE [Q0; Q1] ,,
           MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(dst,len)])`;;

let API_COPY_TAC exec loop n =
  let ns = mk_small_numeral in
  let len = 32 * n in
  let inv = vsubst [ns n,`n:num`; ns len,`len:num`]
   `\i s. read X0 s = word_add dst (word(32 * i)) /\
          read X1 s = word_add src (word(32 * i)) /\
          read X2 s = word(n - i) /\
          read (memory :> bytes(src,len)) s = v /\
          read (memory :> bytes(dst,32 * i)) s = v MOD 2 EXP (256 * i)` in
  let pcp k = mk_binop `(+):num->num->num` `pc:num` (ns k) in
  let ilt = vsubst [ns n,`n:num`] `i < n` in
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN REPEAT STRIP_TAC THEN
  ENSURES_WHILE_UP2_TAC (ns n) (pcp loop) (pcp (loop + 16)) inv THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;
    ARM_SIM_TAC exec [] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0; EXP; MOD_1;
                READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN (vsubst [ns n,`n:num`]
     `val(word(n - (i + 1)):int64) = n - (i + 1)`) ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN (vsubst [ns n,`n:num`]
     `word_sub (word(n - i)) (word 1):int64 = word(n - (i + 1))`)
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [mk_binop `(-):num->num->num` (ns n) `i:num`; `1`]
                    (INST_TYPE [`:64`,`:N`] WORD_SUB)) THEN
      ASM_SIMP_TAC[ARITH_RULE(mk_imp(ilt,
        mk_binop `(<=):num->num->bool` `1`
          (mk_binop `(-):num->num->num` (ns n) `i:num`)))] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    MP_TAC(SPECL [`src:int64`; ns len; `v:num`; `32 * i`; `s0:armstate`]
                 READ_MEMORY_BYTES128_OF_NUM) THEN
    MP_TAC(SPECL [`src:int64`; ns len; `v:num`; `32 * i + 16`; `s0:armstate`]
                 READ_MEMORY_BYTES128_OF_NUM) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    ARM_STEPS_TAC exec (1--4) THEN
    MP_TAC(CONV_RULE NUM_REDUCE_CONV
            (SPECL [`dst:int64`; `i:num`; `v:num`; `s4:armstate`]
                   READ_MEMORY_BYTES_32_STEP)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [COND_CASES_TAC THEN REWRITE_TAC[];
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC];
    ARM_SIM_TAC exec [] THEN
    FIRST_X_ASSUM(MP_TAC o check (can (term_match []
      (vsubst [ns n,`n:num`]
         `read (memory :> bytes (dst,32 * n)) s0 = x`)) o concl)) THEN
    REWRITE_TAC[ARITH_RULE(vsubst [ns n,`n:num`; ns len,`len:num`]
                  `32 * n = len`)] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC MOD_LT THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = vsubst [ns len,`len:num`]
                   `read (memory :> bytes (src,len)) s0 = v`)) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND;
                ARITH_RULE(vsubst [ns n,`n:num`; ns len,`len:num`]
                  `256 * n = 8 * len`)]];;

(*** The zeroing of len bytes at stackpointer + off with stp q0, q0 and a
 *** count in X1, from start (setup instructions before the loop) to stop
 ***)

let api_zero_tm start stop off len =
  let ns = mk_small_numeral in
  vsubst [ns start,`start:num`; ns stop,`stop:num`; ns off,`off:num`;
          ns len,`len:num`]
  `!stackpointer pc.
     nonoverlapping (word_add stackpointer (word off),len)
                    (word pc,mlkem_native2_image_size)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + start) /\
               read SP s = stackpointer)
          (\s. read PC s = word(pc + stop))
          (MAYCHANGE [PC; X0; X1] ,, MAYCHANGE [Q0] ,,
           MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(word_add stackpointer (word off),
                                      len)])`;;

let API_ZERO_TAC exec start setup stop off len =
  let n = len / 32 and ns = mk_small_numeral in
  let inv = vsubst [ns off,`off:num`; ns len,`len:num`]
   `\i s. read X0 s = word_add stackpointer (word(off + 32 * i)) /\
          read X1 s = word(len - 32 * i)` in
  let pcp k = mk_binop `(+):num->num->num` `pc:num` (ns k) in
  let ilt = vsubst [ns n,`n:num`] `i < n` in
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN REPEAT STRIP_TAC THEN
  ENSURES_WHILE_UP2_TAC (ns n) (pcp (start + 4 * setup)) (pcp stop) inv THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;
    ARM_SIM_TAC exec (1--setup) THEN CONV_TAC NUM_REDUCE_CONV THEN
    TRY(CONV_TAC WORD_RULE);
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN (vsubst [ns len,`len:num`]
     `val(word(len - 32 * (i + 1)):int64) = len - 32 * (i + 1)`)
    ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN (vsubst [ns len,`len:num`]
     `word_sub (word(len - 32 * i)) (word 32):int64 =
      word(len - 32 * (i + 1))`) ASSUME_TAC THENL
     [MP_TAC(ISPECL [mk_binop `(-):num->num->num` (ns len) `32 * i`; `32`]
                    (INST_TYPE [`:64`,`:N`] WORD_SUB)) THEN
      ASM_SIMP_TAC[ARITH_RULE(mk_imp(ilt,
        mk_binop `(<=):num->num->bool` `32`
          (mk_binop `(-):num->num->num` (ns len) `32 * i`)))] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ARM_SIM_TAC exec (1--3) THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE(vsubst [ns len,`len:num`; ns n,`n:num`]
        `32 * (i + 1) < len <=> i + 1 < n`)] THEN
      COND_CASES_TAC THEN REWRITE_TAC[];
      CONV_TAC WORD_RULE];
    ARM_SIM_TAC exec []];;

(*** Lemmas for dec: the comparison of the ciphertexts 16 bytes at a
 *** time, and the selection of the shared secret
 ***)

let CMP_MOD_STEP = prove
 (`!n m k. n MOD 2 EXP (128 * (k + 1)) = m MOD 2 EXP (128 * (k + 1)) <=>
           n MOD 2 EXP (128 * k) = m MOD 2 EXP (128 * k) /\
           (n DIV 2 EXP (128 * k)) MOD 2 EXP 128 =
           (m DIV 2 EXP (128 * k)) MOD 2 EXP 128`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `128 * (k + 1) = 128 * k + 128`; EXP_ADD] THEN
  REWRITE_TAC[MOD_MULT_MOD] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) LEXICOGRAPHIC_EQ o lhand o snd) THEN
  REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CONJ_ACI]);;

let CMP_OR_STEP = prove
 (`!q:int128 a b.
        word_or
         (word_xor (word(a MOD 340282366920938463463374607431768211456))
                   (word(b MOD 340282366920938463463374607431768211456)))
         q = word 0 <=>
        q = word 0 /\ b MOD 2 EXP 128 = a MOD 2 EXP 128`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_OR_EQ_0; WORD_XOR_EQ_0] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[VAL_EQ; CONJ_ACI; EQ_SYM_EQ]);;

(*** The comparison of u (n 16-byte words at X0) and v (at X1), ORing the
 *** XORs into Q2, as one step from the loop to its end
 ***)

let api_cmp_inv n =
  vsubst [mk_small_numeral n,`n:num`; mk_small_numeral(16 * n),`len:num`]
   `\i s. read X0 s = word_add ct (word(16 * i)) /\
          read X1 s = word_add ct2 (word(16 * i)) /\
          read X2 s = word(n - i) /\
          read (memory :> bytes(ct,len)) s = u /\
          read (memory :> bytes(ct2,len)) s = v /\
          (read Q2 s = word 0 <=>
           u MOD 2 EXP (128 * i) = v MOD 2 EXP (128 * i))`;;

let api_cmp_tm loop n =
  let ns = mk_small_numeral in
  vsubst [ns loop,`loop:num`; ns n,`n:num`; ns(16 * n),`len:num`;
          ns(loop + 24),`stop:num`]
  `!ct ct2 u v pc.
     ensures arm
      (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
           read PC s = word(pc + loop) /\
           read X0 s = ct /\ read X1 s = ct2 /\ read X2 s = word n /\
           read Q2 s = word 0 /\
           read (memory :> bytes(ct,len)) s = u /\
           read (memory :> bytes(ct2,len)) s = v)
      (\s. read PC s = word(pc + stop) /\
           (read Q2 s = word 0 <=> u = v))
      (MAYCHANGE [PC; X0; X1; X2] ,, MAYCHANGE [Q0; Q1; Q2] ,,
       MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events])`;;

let API_CMP_TAC exec loop n =
  let ns = mk_small_numeral in
  let len = 16 * n in
  let pcp k = mk_binop `(+):num->num->num` `pc:num` (ns k) in
  let ilt = vsubst [ns n,`n:num`] `i < n` in
  REPEAT STRIP_TAC THEN
  ENSURES_WHILE_UP2_TAC (ns n) (pcp loop) (pcp (loop + 24)) (api_cmp_inv n)
  THEN REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;
    ARM_SIM_TAC exec [] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_0; EXP; MOD_1];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN (vsubst [ns n,`n:num`]
     `val(word(n - (i + 1)):int64) = n - (i + 1)`) ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN (vsubst [ns n,`n:num`]
     `word_sub (word(n - i)) (word 1):int64 = word(n - (i + 1))`)
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [mk_binop `(-):num->num->num` (ns n) `i:num`; `1`]
                    (INST_TYPE [`:64`,`:N`] WORD_SUB)) THEN
      ASM_SIMP_TAC[ARITH_RULE(mk_imp(ilt,
        mk_binop `(<=):num->num->bool` `1`
          (mk_binop `(-):num->num->num` (ns n) `i:num`)))] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    GHOST_INTRO_TAC `q:int128` `read Q2` THEN
    ENSURES_INIT_TAC "s0" THEN
    MP_TAC(SPECL [`ct:int64`; ns len; `u:num`; `16 * i`; `s0:armstate`]
                 READ_MEMORY_BYTES128_OF_NUM) THEN
    MP_TAC(SPECL [`ct2:int64`; ns len; `v:num`; `16 * i`; `s0:armstate`]
                 READ_MEMORY_BYTES128_OF_NUM) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    ARM_STEPS_TAC exec (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [COND_CASES_TAC THEN REWRITE_TAC[];
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[CMP_OR_STEP; CMP_MOD_STEP] THEN
      REWRITE_TAC[ARITH_RULE `8 * 16 * i = 128 * i`] THEN
      ASM_REWRITE_TAC[]];
    ARM_SIM_TAC exec [] THEN
    SUBGOAL_THEN (vsubst [ns n,`n:num`]
     `u < 2 EXP (128 * n) /\ v < 2 EXP (128 * n)`) STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
          vsubst [ns len,`len:num`]
           `read (memory :> bytes (ct,len)) s0 = u`));
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
          vsubst [ns len,`len:num`]
           `read (memory :> bytes (ct2,len)) s0 = v`))] THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND;
                  ARITH_RULE(vsubst [ns n,`n:num`; ns len,`len:num`]
                    `128 * n = 8 * len`)];
      ASM_SIMP_TAC[MOD_LT]]];;

(*** UMAXV of the four 32-bit lanes of q, moved to W0 and compared with 0:
 *** zero exactly when q is
 ***)

let WORD_AND_ONES_128 = prove
 (`!x:int128. word_and x (word 340282366920938463463374607431768211455) = x`,
  GEN_TAC THEN BITBLAST_TAC);;

let UMAXV_LANES_EQ_0 = prove
 (`!q:int128.
     MAX (val(word_subword q (0,32):int128))
      (MAX (val(word_subword q (32,32):int128))
       (MAX (val(word_subword q (64,32):int128))
            (val(word_subword q (96,32):int128)))) = 0 <=>
     q = word 0`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `MAX a b = 0 <=> a = 0 /\ b = 0`; VAL_EQ_0] THEN
  BITBLAST_TAC);;

let UMAXV_LANES_BOUND = prove
 (`!q:int128.
     MAX (val(word_subword q (0,32):int128))
      (MAX (val(word_subword q (32,32):int128))
       (MAX (val(word_subword q (64,32):int128))
            (val(word_subword q (96,32):int128)))) < 4294967296`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `MAX a b < n <=> a < n /\ b < n`] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_LT_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let UMAXV_FMOV_EQ_0 = prove
 (`!q:int128.
     val(word_sub (word_zx (word_zx (word_subword
       (word(MAX (val(word_subword q (0,32):int128))
             (MAX (val(word_subword q (32,32):int128))
              (MAX (val(word_subword q (64,32):int128))
                   (val(word_subword q (96,32):int128))))):int128)
       (0,32):int32):int64):int32) (word 0)) = 0 <=>
     q = word 0`,
  GEN_TAC THEN MP_TAC(SPEC `q:int128` UMAXV_LANES_BOUND) THEN
  REWRITE_TAC[GSYM UMAXV_LANES_EQ_0] THEN
  SPEC_TAC(`MAX (val(word_subword (q:int128) (0,32):int128))
             (MAX (val(word_subword q (32,32):int128))
              (MAX (val(word_subword q (64,32):int128))
                   (val(word_subword q (96,32):int128))))`,`m:num`) THEN
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[WORD_SUB_0; VAL_WORD_ZX_GEN; VAL_WORD_SUBWORD; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1] THEN
  SUBGOAL_THEN `m < 340282366920938463463374607431768211456 /\
                m < 18446744073709551616` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[MOD_LT]]);;

(*** The selection, from umaxv at start to the store of the 32 bytes ***)

let API_SEL_TAC exec kr jo =
  let ns = mk_small_numeral in
  let a1 = vsubst [ns kr,`n:num`] `word_add sp (word n):int64`
  and a2 = vsubst [ns jo,`n:num`] `word_add sp (word n):int64` in
  REPEAT STRIP_TAC THEN GHOST_INTRO_TAC `q:int128` `read Q2` THEN
  ENSURES_INIT_TAC "s0" THEN
  API_BYTES128_OF_32_TAC a1 `num_of_bytelist(kk:byte list)` THEN
  API_BYTES128_OF_32_TAC a2 `num_of_bytelist(jj:byte list)` THEN
  ASM_CASES_TAC `b:bool` THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_iff(concl th) &&
    free_in `b:bool` (concl th) && not(is_var(concl th)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ARM_STEPS_TAC exec (1--13) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC READ_MEMORY_BYTES_32_OF_PIECES THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_AND_ONES_128; WORD_AND_0; WORD_OR_0];
    ARM_STEPS_TAC exec (1--13) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[UMAXV_FMOV_EQ_0]) THEN
    MATCH_MP_TAC READ_MEMORY_BYTES_32_OF_PIECES THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
    REWRITE_TAC[WORD_AND_ONES_128; WORD_AND_0; WORD_OR_0]];;

(* ------------------------------------------------------------------------- *)
(* keypair_derand                                                            *)
(* ------------------------------------------------------------------------- *)

(*** The loops: the copy of pk into sk and the two zeroings ***)

let kp_cloop k = layout (api_param k ^ "_keypair_copypk");;
let kp_zero1 k = kp_cloop k + 52;;
let kp_zero2 k = kp_cloop k + 76;;
let kp_zero2_setup k = if 256 + 512 * k * k < 4096 then 3 else 4;;
let kp_zero2_stop k = kp_zero2 k + 4 * kp_zero2_setup k + 12;;

let kp_loops k ex =
  let n = kp_pkb k / 32 in
  let cth = prove(api_copy_tm (kp_cloop k) n,
                  API_COPY_TAC ex (kp_cloop k) n) in
  let z1 = prove(api_zero_tm (kp_zero1 k) (kp_zero2 k) 96 160,
                 API_ZERO_TAC ex (kp_zero1 k) 3 (kp_zero2 k) 96 160) in
  let so = 256 + 512 * k * k and sl = 1280 * k in
  let z2 = prove(api_zero_tm (kp_zero2 k) (kp_zero2_stop k) so sl,
                 API_ZERO_TAC ex (kp_zero2 k) (kp_zero2_setup k)
                   (kp_zero2_stop k) so sl) in
  cth,z1,z2;;

(*** ML-KEM key generation as the K-PKE key pair with H(ek) and z, and the
 *** lengths of the K-PKE keys, for k
 ***)

let kp_keygen_pair k =
  REWRITE_RULE[GSYM(kp_param_def k)]
   (ISPECL (kp_params k) MLKEM_KEYGEN_PAIR);;

let kp_lengths k =
  let nm = api_param k in
  prove(parse_term("!d. LENGTH(FST(kpke_keygen "^nm^" d)) = "^
                   string_of_int(kp_pkb k)^" /\\ "^
                   "LENGTH(SND(kpke_keygen "^nm^" d)) = "^
                   string_of_int(384 * k)),
        REWRITE_TAC[kp_param_def k; KPKE_KEYGEN_LENGTHS] THEN
        CONV_TAC NUM_REDUCE_CONV);;

(*** The seeds (rho, sigma) = G(d || k) and the inputs of the PRF ***)

let kp_rho k = parse_term("FST(mlkem_g(APPEND d [word "^string_of_int k^"]))")
and kp_sigma k =
  parse_term("SND(mlkem_g(APPEND d [word "^string_of_int k^"]))");;

let kp_prf k p =
  let eta = api_eta1 k in
  vsubst [mk_comb(`word:num->byte`,mk_small_numeral p),`x:byte`;
          mk_small_numeral eta,`eta:num`; kp_sigma k,`sigma:byte list`]
   `mlkem_prf eta sigma x`;;

(*** The address of the buffer at offset n ***)

let kp_spn n = mk_comb(mk_comb(`word_add:int64->int64->int64`,
                               `stackpointer:int64`),
                       mk_comb(`word:num->int64`,mk_small_numeral n));;

(*** The steps of keypair_derand for k: the setup, with d and z as 16-byte
 *** words; G(d || k), the matrix and the noise; the NTTs of s and e; the
 *** rows of t_hat; the encodings of t_hat and s_hat; and the copy of pk into
 *** sk with H(pk) and z, and the zeroings
 ***)

let KP_SETUP_TAC k ex =
  MAP_EVERY X_GEN_TAC
   [`pk:int64`; `sk:int64`; `coins:int64`; `d:byte list`; `z:byte list`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC (kp_stack k) THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; PAIRWISE; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
              (mk_const("X"^string_of_int n,[]))) (19--29) THEN
  ENSURES_INIT_TAC "s0" THEN
  API_BYTES128_OF_32_TAC `coins:int64` `num_of_bytelist(d:byte list)` THEN
  API_BYTES128_OF_32_TAC `word_add coins (word 32):int64`
    `num_of_bytelist(z:byte list)` THEN
  ARM_STEPS_TAC ex (1--14) THEN MLKEM_NATIVE_ADRP_TAC;;

let KP_SAMPLE_TAC k ex next gmth =
  let rho = kp_rho k and sigma = kp_sigma k in
  next THEN
  ON_STATE(API_HASH_G_CALL_TAC ex `d:byte list` k) THEN
  ON_STATE(fun kk -> API_G_SPLIT_TAC kk THEN API_CONSTS_TAC) THEN
  next THEN
  (if k = 2 then
     ON_STATE(API_GM_CALL_TAC ex gmth
      (fun r -> [r `X0`; r `X1`; rho; r `X4`; r `X5`; r `X6`; `pc:num`;
                 r `SP`; r `X30`])) THEN
     next THEN ON_STATE(API_GETNOISE_CALL_TAC ex sigma) THEN
     ON_STATE GM_SPLIT_NOISE_TAC
   else
     ON_STATE(API_GM_CALL_TAC ex gmth
      (fun r -> [r `X0`; r `X1`; rho; r `X5`;
                 kp_spn(kp_cstack k + 192); sigma; kp_spn(kp_s k);
                 r `X4`; r `X6`; `pc:num`; r `SP`; r `X30`])) THEN
     ON_STATE GM_SPLIT_NOISE_TAC);;

let KP_NTT_TAC k ex next =
  let eta = api_eta1 k in
  let gv n = mk_var(n,`:num->int16`) in
  MAP_EVERY (fun (v,nn,p) ->
    next THEN ON_STATE(API_NTT_CALL_TAC ex) THEN
    ON_STATE(API_NTT_POST_TAC v (`stackpointer:int64`,nn) eta (kp_prf k p)))
   (map (fun j -> ("SH"^string_of_int j,kp_s k + 512 * j,j)) (0--(k-1)) @
    map (fun j -> ("EH"^string_of_int j,kp_e k + 512 * j,k + j)) (0--(k-1)))
  THEN
  MAP_EVERY (fun j ->
    next THEN ON_STATE(API_MULCACHE_CALL_TAC ex) THEN
    ON_STATE(API_MC_POST_TAC ("MC"^string_of_int j)
              (`stackpointer:int64`,kp_sc k + 256 * j)
              (gv("SH"^string_of_int j))))
   (0--(k-1));;

let KP_ROW_TAC k ex next r =
  let rs = string_of_int r and t = (`stackpointer:int64`,kp_t k + 512 * r) in
  let gv n = mk_var(n,`:num->int16`) in
  let names x = map (fun j -> gv(x^string_of_int j)) (0--(k-1)) in
  next THEN ON_STATE(API_BASEMUL_CALL_TAC ex k r) THEN
  (fun gl ->
    let sred = map (fun c ->
      find_asm (fun tm -> is_forall tm &&
                  can (find_term (fun u -> u = gv("SR"^string_of_int c))) tm &&
                  can (find_term (fun u -> is_const u &&
                                           name_of u = "rem")) tm) gl)
      (if r = 0 then [] else 0--(r-1)) in
    ON_STATE(API_BASEMUL_POST_TAC ("PT"^rs) t k r (names "SH") (names "MC")
               sred) gl) THEN
  next THEN ON_STATE(API_TOMONT_CALL_TAC ex) THEN
  ON_STATE(API_TOMONT_POST_TAC ("PU"^rs) t (gv ("PT"^rs))) THEN
  next THEN ON_STATE(API_ADD_REDUCE_CALL_TAC ex) THEN
  ON_STATE(API_ADD_REDUCE_POST_TAC ("TR"^rs) t (gv ("PU"^rs))
             (gv ("EH"^rs))) THEN
  next THEN ON_STATE(API_REDUCE_CALL_TAC ex) THEN
  ON_STATE(API_REDUCE_POST_TAC ("SR"^rs)
            (`stackpointer:int64`,kp_s k + 512 * r)
             (gv ("SH"^rs)));;

let KP_ENCODE_TAC k ex next kth =
  let rho = kp_rho k and sigma = kp_sigma k in
  REPLICATE_TAC (2 * k) (next THEN ON_STATE(API_TOBYTES_CALL_TAC ex)) THEN
  SUBGOAL_THEN (mk_conj(mk_eq(mk_comb(`LENGTH:byte list->num`,rho),`32`),
                        mk_eq(mk_comb(`LENGTH:byte list->num`,sigma),`32`)))
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[LENGTH_MLKEM_G]; ALL_TAC] THEN
  ON_STATE(API_BYTES128_OF_32_AT_TAC (kp_spn(kp_cstack k + 160))
            (mk_comb(`num_of_bytelist`,rho))) THEN
  ON_STATE(fun kk -> ARM_STEPS_TAC ex ((kk+1)--(kk+4))) THEN
  ON_STATE(API_JOIN32_TAC
    (mk_comb(mk_comb(`word_add:int64->int64->int64`,`pk:int64`),
             mk_comb(`word:num->int64`,mk_small_numeral(384 * k)))) rho) THEN
  ON_STATE(API_KEYGEN_TAC k kth);;

let KP_FINISH_TAC k ex next (cth,z1,z2) =
  let nm = api_param k in
  let ek = parse_term("FST(kpke_keygen "^nm^" d)") in
  let lens = kp_lengths k and pair = kp_keygen_pair k in
  let skb = kp_skb k in
  let wadd a n = mk_comb(mk_comb(`word_add:int64->int64->int64`,a),
                         mk_comb(`word:num->int64`,mk_small_numeral n)) in
  API_TO_PC_TAC ex (kp_cloop k) THEN
  ON_STATE(fun kk gl ->
    API_LEMMA_STEP_TAC ex
     (SPECL [find_read_fact `X0` kk gl; find_read_fact `X1` kk gl;
             mk_comb(`num_of_bytelist`,ek); `pc:num`] cth) kk gl) THEN
  next THEN
  ON_STATE(API_HASH_H_CALL_TAC ex ek (CONJUNCT1(SPEC `d:byte list` lens))) THEN
  ON_STATE(fun kk -> ARM_STEPS_TAC ex ((kk+1)--(kk+4))) THEN
  ON_STATE(API_JOIN32_TAC (wadd `sk:int64` (skb - 32)) `z:byte list`) THEN
  ON_STATE(API_LEMMA_STEP_TAC ex
   (SPECL [kp_spn(kp_cstack k); `pc:num`] z1)) THEN
  ON_STATE(API_LEMMA_STEP_TAC ex
   (SPECL [kp_spn(kp_cstack k); `pc:num`] z2)) THEN
  API_TO_PC_TAC ex (-1) THEN
  ON_STATE(fun kk ->
    SUBGOAL_THEN (vsubst [state_of kk,`s:armstate`;
                          mk_small_numeral skb,`n:num`]
     (parse_term("read (memory :> bytes(sk,n)) s = "^
                 "num_of_bytelist(SND(mlkem_keygen_internal "^nm^" d z))")))
    ASSUME_TAC THENL
     [REWRITE_TAC[pair; mlkem_h; NUM_OF_BYTELIST_APPEND; lens;
                  LENGTH_SHA3_256] THEN
      REWRITE_TAC[ARITH_RULE(parse_term(string_of_int skb^" = "^
        string_of_int(384 * k)^" + "^string_of_int(kp_pkb k)^" + 32 + 32"));
                  READ_MEMORY_BYTES_SPLIT] THEN
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[pair];;

(*** The proof of keypair_derand for k, with the code ex of the function
 *** and the theorem gmth for gen_matrix
 ***)

(*** The termination of SampleNTT for the matrix of the seed rho, entry
 *** (i,j) from rho || j || i if ji, else from rho || i || j, as the API
 *** theorems would assume (MLKEM_SAMPLENTT_TERMINATES_TAC proves it)
 ***)

let api_terminates_tm k rho ji =
  let ks = string_of_int k in
  vsubst [rho,`rho:byte list`]
   (parse_term("!i j. i < "^ks^" /\\ j < "^ks^
               " ==> mlkem_samplentt_terminates (APPEND rho "^
               (if ji then "[word j; word i]" else "[word i; word j]")^")"));;

let MLKEM_NATIVE2_KEYPAIR_DERAND_CORRECT_TAC k ex gmth =
  let nm = api_param k in
  let nx = API_TO_CALL_TAC ex (layout(nm ^ "_keypair_derand"))
                              (layout(nm ^ "_pke_encrypt")) in
  let lps = kp_loops k ex in
  let kth = match k with
      2 -> KPKE_KEYGEN_K2_BLOCKS | 3 -> KPKE_KEYGEN_K3_BLOCKS
    | _ -> KPKE_KEYGEN_K4_BLOCKS in
  MLKEM_SAMPLENTT_TERMINATES_TAC (api_terminates_tm k (kp_rho k) true)
   (KP_SETUP_TAC k ex THEN KP_SAMPLE_TAC k ex nx gmth THEN
    KP_NTT_TAC k ex nx THEN MAP_EVERY (KP_ROW_TAC k ex nx) (0--(k-1)) THEN
    KP_ENCODE_TAC k ex nx kth THEN KP_FINISH_TAC k ex nx lps);;

(* ------------------------------------------------------------------------- *)
(* pke_encrypt                                                               *)
(* ------------------------------------------------------------------------- *)

(*** The K-PKE encryption from the ghosts at state kk: the ciphertext ***)

let PE_FINAL_TAC k bth kk gl =
  let sv = state_of kk in
  let ks = string_of_int k in
  let blk x = api_blk (map (fun j -> x^string_of_int j) (0--(k-1))) in
  let gv n = mk_var(n,`:num->int16`) in
  let e1fun = parse_term("\\j i. iword(mlkem_cbd_coeff 2 (mlkem_prf 2 r "^
                         "(word("^ks^" + j))) i):int16")
  and e2fun = parse_term("\\i. iword(mlkem_cbd_coeff 2 (mlkem_prf 2 r "^
                         "(word "^string_of_int(2 * k)^")) i):int16") in
  let rho = parse_term("mlkem_slice "^string_of_int(384 * k)^" 32 ek") in
  let th = ISPECL [`ek:byte list`; `m:byte list`; `r:byte list`;
                   blk "TT"; blk "YH"; blk "MC"; e1fun; e2fun; gv "MU";
                   blk "U0"; gv "V0"; blk "U1"; gv "V1"; blk "U3"; gv "V2";
                   gv "V4"] bth in
  let du = api_du k and dv = api_dv k in
  let ub = 32 * du and ctb = pe_ctb k in
  let g = parse_term("\\j i. (("^string_of_int(1 lsl (du+1))^" * val(EL j "^
    "["^String.concat "; " (map (fun j -> "U3"^string_of_int j^":num->int16")
                             (0--(k-1)))^"] i) + 3329) DIV 6658) MOD "^
    string_of_int(1 lsl du)) in
  let mth = ISPECL [`ct:int64`; mk_small_numeral ub; mk_small_numeral du;
                    g; sv;
                    mk_small_numeral k] READ_MEMORY_BYTES_NSUM_BLOCKS in
  let ctgoal = vsubst [sv,`s:armstate`; mk_small_numeral ctb,`n:num`]
    (parse_term("read (memory :> bytes(ct,n)) s = "^
                "num_of_bytelist(kpke_encrypt "^api_param k^" ek m r)")) in
  let splitth = ARITH_RULE(mk_eq(mk_small_numeral ctb,
    mk_binop `(+):num->num->num` (mk_small_numeral(ub * k))
      (mk_small_numeral(32 * dv)))) in
  (MP_TAC th THEN ANTS_TAC THENL
    [CONJ_TAC THENL
      [REPEAT STRIP_TAC THEN
       MP_TAC(ISPECL [mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,
                       rho),`[word j; word i]:byte list`); `n:num`]
                API_SAMPLE_NTT_BOUNDS) THEN
       ASM_SIMP_TAC[];
       ALL_TAC] THEN
     REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
     TRY(API_CASES_TAC k) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
     ASM_SIMP_TAC[API_CBD_CONG; ARITH_EQ];
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN DISCH_TAC] THEN
   MP_TAC mth THEN ANTS_TAC THENL
    [CONV_TAC NUM_REDUCE_CONV THEN
     CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
     CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
     ASM_REWRITE_TAC[];
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
     DISCH_TAC] THEN
   SUBGOAL_THEN ctgoal ASSUME_TAC THENL
    [REWRITE_TAC[splitth; READ_MEMORY_BYTES_SPLIT] THEN
     ASM_REWRITE_TAC[] THEN NO_TAC;
     ALL_TAC]) gl;;

(*** The zeroing loops of pke_encrypt ***)

let pe_zero1 k =
  layout(api_param k ^ "_pke_encrypt") +
  (match k with 2 -> 360 | 3 -> 480 | _ -> 652);;

let pe_loops k ex =
  let z1s = pe_zero1 k in
  let z2s = z1s + 24 in
  let z1 = prove(api_zero_tm z1s z2s 96 (256 * k),
                 API_ZERO_TAC ex z1s 3 z2s 96 (256 * k)) in
  let uo = 96 + 768 * k and ul = 512 * k + 1024 in
  let z2 = prove(api_zero_tm z2s (z2s + 24) uo ul,
                 API_ZERO_TAC ex z2s 3 (z2s + 24) uo ul) in
  z1,z2;;

(*** The noise facts with the conditions on the index evaluated ***)

let PE_NOISE_COND_TAC kk =
  let sv = state_of kk in
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if free_in sv c &&
       can (find_term (fun t -> is_const t && name_of t = "mlkem_cbd_coeff")) c
    then REWRITE_RULE[ADD_CLAUSES] (CONV_RULE NUM_REDUCE_CONV th) else th);;

(*** The steps of pke_encrypt for k: the setup; the decoding of t_hat and
 *** of the message, and the NTTs of y with their mulcaches; the products of
 *** A_hat^T and t_hat^T with y_hat, and the inverse NTTs; the additions of
 *** the noise and of the message; and the compressions and the zeroings
 ***)

let PE_SETUP_TAC k ex =
  let ninit = if 1120 + 1280 * k < 4096 then 15 else 16 in
  MAP_EVERY X_GEN_TAC
   [`ct:int64`; `at:int64`; `pk:int64`; `mp:int64`; `noise:int64`;
    `ek:byte list`; `m:byte list`; `r:byte list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC (pe_stack k) THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
              (mk_const("X"^string_of_int n,[]))) (19--29) THEN
  ENSURES_INIT_TAC "s0" THEN
  GM_SPLIT_NOISE_TAC 0 THEN PE_NOISE_COND_TAC 0 THEN
  ARM_STEPS_TAC ex (1--ninit) THEN MLKEM_NATIVE_ADRP_TAC;;

let PE_LOAD_TAC k ex next =
  let sp = `stackpointer:int64` and noise = `noise:int64` in
  let gv n = mk_var(n,`:num->int16`) in
  let eta = api_eta1 k in
  let prf p = vsubst [mk_comb(`word:num->byte`,mk_small_numeral p),`x:byte`;
                      mk_small_numeral eta,`eta:num`] `mlkem_prf eta r x` in
  MAP_EVERY (fun j ->
    next THEN ON_STATE(API_FROMBYTES_CALL_TAC ex `ek:byte list` j) THEN
    ON_STATE(API_FROMBYTES_POST_TAC ("TT"^string_of_int j)
              (sp,pe_t k + 512 * j) `ek:byte list` j)) (0--(k-1)) THEN
  next THEN ON_STATE(API_FROMMSG_CALL_TAC ex `m:byte list`) THEN
  ON_STATE(API_FROMMSG_POST_TAC "MU" (sp,pe_m k) `m:byte list`) THEN
  MAP_EVERY (fun j ->
    next THEN ON_STATE(API_NTT_CALL_TAC ex) THEN
    ON_STATE(API_NTT_POST_TAC ("YH"^string_of_int j) (noise,512 * j) eta
              (prf j)) THEN
    next THEN ON_STATE(API_MULCACHE_CALL_TAC ex) THEN
    ON_STATE(API_MC_POST_TAC ("MC"^string_of_int j) (sp,pe_yc k + 256 * j)
              (gv("YH"^string_of_int j)))) (0--(k-1));;

let PE_MUL_TAC k ex next =
  let sp = `stackpointer:int64` in
  let gv n = mk_var(n,`:num->int16`) in
  let names x = map (fun j -> gv(x^string_of_int j)) (0--(k-1)) in
  MAP_EVERY (fun q ->
    next THEN ON_STATE(API_BASEMUL_CALL_TAC ex k q) THEN
    ON_STATE(API_BASEMUL_POST_TAC ("U0"^string_of_int q) (sp,pe_u k + 512 * q)
              k q (names "YH") (names "MC") [])) (0--(k-1)) THEN
  next THEN ON_STATE(API_BASEMUL_T_CALL_TAC ex k) THEN
  ON_STATE(API_BASEMUL_T_POST_TAC "V0" (sp,pe_v k) k (names "TT")
            (names "YH") (names "MC")) THEN
  MAP_EVERY (fun j ->
    next THEN ON_STATE(API_INTT_CALL_TAC ex) THEN
    ON_STATE(API_INTT_POST_TAC ("U1"^string_of_int j) (sp,pe_u k + 512 * j)
              (gv("U0"^string_of_int j)))) (0--(k-1)) THEN
  next THEN ON_STATE(API_INTT_CALL_TAC ex) THEN
  ON_STATE(API_INTT_POST_TAC "V1" (sp,pe_v k) (gv "V0"));;

let PE_ADD_TAC k ex next =
  let sp = `stackpointer:int64` and noise = `noise:int64` in
  let gv n = mk_var(n,`:num->int16`) in
  MAP_EVERY (fun j ->
    next THEN ON_STATE(API_ADD_REDUCE_CALL_TAC ex) THEN
    ON_STATE(fun kk gl ->
      API_ADD_REDUCE_POST_TAC ("U3"^string_of_int j) (sp,pe_u k + 512 * j)
        (gv("U1"^string_of_int j))
        (api_fun16_at (noise,512 * (k + j)) 256 kk gl) kk gl)) (0--(k-1)) THEN
  next THEN ON_STATE(API_ADD_REDUCE_CALL_TAC ex) THEN
  ON_STATE(fun kk gl ->
    API_ADD_REDUCE_POST_TAC "V2" (sp,pe_v k) (gv "V1")
      (api_fun16_at (noise,1024 * k) 256 kk gl) kk gl) THEN
  next THEN ON_STATE(API_ADD_REDUCE_CALL_TAC ex) THEN
  ON_STATE(API_ADD_REDUCE_POST_TAC "V4" (sp,pe_v k) (gv "V2") (gv "MU"));;

let PE_STORE_TAC k ex next (z1,z2) bth =
  REPLICATE_TAC k (next THEN ON_STATE(API_COMPRESS_CALL_TAC ex (api_du k)))
  THEN
  next THEN ON_STATE(API_COMPRESS_CALL_TAC ex (api_dv k)) THEN
  API_TO_PC_TAC ex (pe_zero1 k) THEN
  ON_STATE(API_LEMMA_STEP_TAC ex
   (SPECL [kp_spn pe_cstack; `pc:num`] z1)) THEN
  ON_STATE(API_LEMMA_STEP_TAC ex
   (SPECL [kp_spn pe_cstack; `pc:num`] z2)) THEN
  API_TO_PC_TAC ex (-1) THEN
  ON_STATE(PE_FINAL_TAC k bth) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(*** The proof of pke_encrypt for k, with the code ex of the function ***)

let MLKEM_NATIVE2_PKE_ENCRYPT_CORRECT_TAC k ex =
  let nm = api_param k in
  let nx = API_TO_CALL_TAC ex (layout(nm ^ "_pke_encrypt"))
                              (layout(nm ^ "_enc_derand")) in
  let lp = pe_loops k ex in
  let bth = match k with
      2 -> KPKE_ENCRYPT_K2_BLOCKS | 3 -> KPKE_ENCRYPT_K3_BLOCKS
    | _ -> KPKE_ENCRYPT_K4_BLOCKS in
  let rho = parse_term("mlkem_slice "^string_of_int(384 * k)^" 32 ek") in
  MLKEM_SAMPLENTT_TERMINATES_TAC (api_terminates_tm k rho false)
   (PE_SETUP_TAC k ex THEN PE_LOAD_TAC k ex nx THEN PE_MUL_TAC k ex nx THEN
    PE_ADD_TAC k ex nx THEN PE_STORE_TAC k ex nx lp bth);;

(* ------------------------------------------------------------------------- *)
(* pke_decrypt                                                               *)
(* ------------------------------------------------------------------------- *)

(*** The K-PKE decryption from the ghosts at state kk: the message ***)

let PD_FINAL_TAC k bth kk gl =
  let sv = state_of kk in
  let blk x = api_blk (map (fun j -> x^string_of_int j) (0--(k-1))) in
  let gv n = mk_var(n,`:num->int16`) in
  let th = ISPECL [`dk:byte list`; `c:byte list`; blk "UD"; gv "VD";
                   blk "SS"; blk "UH"; blk "MC"; gv "WP"; gv "WI"; gv "VR"]
                  bth in
  let mgoal = vsubst [sv,`s:armstate`]
    (parse_term("read (memory :> bytes(mp,32)) s = "^
                "num_of_bytelist(kpke_decrypt "^api_param k^" dk c)")) in
  (MP_TAC th THEN ANTS_TAC THENL
    [REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
     TRY(API_CASES_TAC k) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
     ASM_SIMP_TAC[];
     DISCH_TAC] THEN
   SUBGOAL_THEN mgoal ASSUME_TAC THENL
    [ASM_REWRITE_TAC[] THEN NO_TAC; ALL_TAC]) gl;;

(*** The zeroing loop of pke_decrypt ***)

let pd_zero k =
  layout(api_param k ^ "_pke_decrypt") +
  (match k with 2 -> 244 | 3 -> 320 | _ -> 392);;

let pd_loop k ex =
  let zs = pd_zero k in
  prove(api_zero_tm zs (zs + 24) 96 (1280 * k + 1024),
        API_ZERO_TAC ex zs 3 (zs + 24) 96 (1280 * k + 1024));;

(*** The steps of pke_decrypt for k: the setup; the decompressions of u
 *** and v, the decoding of s_hat, the NTTs of u with their mulcaches, the
 *** product of s_hat^T and u_hat, its inverse NTT, the subtraction, the
 *** encoding of the message and the zeroing
 ***)

let PD_SETUP_TAC k ex =
  let ninit = if 1120 + 1280 * k < 4096 then 13 else 14 in
  MAP_EVERY X_GEN_TAC
   [`mp:int64`; `ct:int64`; `sk:int64`; `c:byte list`; `dk:byte list`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC (pd_stack k) THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
              (mk_const("X"^string_of_int n,[]))) (19--29) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC ex (1--ninit) THEN MLKEM_NATIVE_ADRP_TAC;;

let PD_TAC k ex next zl bth =
  let sp = `stackpointer:int64` in
  let gv n = mk_var(n,`:num->int16`) in
  let names x = map (fun j -> gv(x^string_of_int j)) (0--(k-1)) in
  let du = api_du k and dv = api_dv k in
  MAP_EVERY (fun j ->
    next THEN
    ON_STATE(API_DECOMPRESS_CALL_TAC ex du `c:byte list` (32 * du * j)
              (32 * du)) THEN
    ON_STATE(API_DECOMPRESS_POST_TAC ("UD"^string_of_int j)
              (sp,pd_u k + 512 * j) `c:byte list` du j) THEN
    next THEN ON_STATE(API_FROMBYTES_CALL_TAC ex `dk:byte list` j) THEN
    ON_STATE(API_FROMBYTES_POST_TAC ("SS"^string_of_int j)
              (sp,pd_s k + 512 * j) `dk:byte list` j)) (0--(k-1)) THEN
  next THEN
  ON_STATE(API_DECOMPRESS_CALL_TAC ex dv `c:byte list` (32 * du * k)
            (32 * dv)) THEN
  ON_STATE(API_DECOMPRESS_V_POST_TAC "VD" (sp,pd_v k) `c:byte list` dv
            (32 * du * k) (32 * dv)) THEN
  MAP_EVERY (fun j ->
    next THEN ON_STATE(API_NTT_CALL_TAC ex) THEN
    ON_STATE(API_NTT_POST_PLAIN_TAC ("UH"^string_of_int j)
              (sp,pd_u k + 512 * j) (gv("UD"^string_of_int j)))) (0--(k-1))
  THEN
  MAP_EVERY (fun j ->
    next THEN ON_STATE(API_MULCACHE_CALL_TAC ex) THEN
    ON_STATE(API_MC_POST_TAC ("MC"^string_of_int j) (sp,pd_uc k + 256 * j)
              (gv("UH"^string_of_int j)))) (0--(k-1)) THEN
  next THEN ON_STATE(API_BASEMUL_T_CALL_TAC ex k) THEN
  ON_STATE(API_BASEMUL_T_POST_TAC "WP" (sp,pd_w k) k (names "SS")
            (names "UH") (names "MC")) THEN
  next THEN ON_STATE(API_INTT_CALL_TAC ex) THEN
  ON_STATE(API_INTT_POST_TAC "WI" (sp,pd_w k) (gv "WP")) THEN
  next THEN ON_STATE(API_SUB_REDUCE_CALL_TAC ex) THEN
  ON_STATE(API_SUB_REDUCE_POST_TAC "VR" (sp,pd_v k) (gv "VD") (gv "WI")) THEN
  next THEN ON_STATE(API_TOMSG_CALL_TAC ex) THEN
  API_TO_PC_TAC ex (pd_zero k) THEN
  ON_STATE(API_LEMMA_STEP_TAC ex (SPECL [kp_spn pd_cstack; `pc:num`] zl)) THEN
  API_TO_PC_TAC ex (-1) THEN
  ON_STATE(PD_FINAL_TAC k bth) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(*** The proof of pke_decrypt for k, with the code ex of the function ***)

let MLKEM_NATIVE2_PKE_DECRYPT_CORRECT_TAC k ex =
  let nm = api_param k in
  let nx = API_TO_CALL_TAC ex (layout(nm ^ "_pke_decrypt"))
                              (layout(nm ^ "_dec")) in
  let lp = pd_loop k ex in
  let bth = match k with
      2 -> KPKE_DECRYPT_K2_BLOCKS | 3 -> KPKE_DECRYPT_K3_BLOCKS
    | _ -> KPKE_DECRYPT_K4_BLOCKS in
  PD_SETUP_TAC k ex THEN PD_TAC k ex nx lp bth;;

(* ------------------------------------------------------------------------- *)
(* enc_derand                                                                *)
(* ------------------------------------------------------------------------- *)

(*** The zeroing loop of enc_derand ***)

let en_zero k = layout(api_param k ^ "_enc_derand") +
  (match k with 2 -> 228 | 3 -> 236 | _ -> 244);;

(*** The values of enc_derand: rho in ek, the input of G, K and r ***)

let en_rho k = parse_term("mlkem_slice "^string_of_int(384 * k)^" 32 ek");;
let en_hmsg = `APPEND m (sha3_256 ek)`;;
let en_kk = `mlkem_slice 0 32 (sha3_512 (APPEND m (sha3_256 ek)))`;;
let en_r = `mlkem_slice 32 32 (sha3_512 (APPEND m (sha3_256 ek)))`;;

(*** The setup of enc_derand, with m as two 16-byte words ***)

let EN_SETUP_TAC k ex =
  let ef = 288 + 512 * (2 * k + 1) + 512 * k * k in
  let ninit = 1 + (if ef < 4096 then 1 else 2) + 6 + 4 + 2 in
  MAP_EVERY X_GEN_TAC
   [`ct:int64`; `ss:int64`; `pk:int64`; `coins:int64`; `ek:byte list`;
    `m:byte list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC (en_stack k) THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; PAIRWISE; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
              (mk_const("X"^string_of_int n,[]))) (19--29) THEN
  ENSURES_INIT_TAC "s0" THEN
  API_BYTES128_OF_32_TAC `coins:int64` `num_of_bytelist(m:byte list)` THEN
  ARM_STEPS_TAC ex (1--ninit) THEN MLKEM_NATIVE_ADRP_TAC;;

(*** Encapsulation as K and the K-PKE ciphertext ***)

let en_encaps_pair k =
  REWRITE_RULE[GSYM(kp_param_def k)] (ISPECL (kp_params k) MLKEM_ENCAPS_PAIR);;

(*** The valid path, after the check: m, H(ek), the matrix by gmth,
 *** (K, r), the noise, the ciphertext and the shared secret
 ***)

let EN_VALID_TAC k ex next gmth (pth,zth) =
  let ks = string_of_int k in
  let rho = en_rho k and n = mk_small_numeral in
  let sp x = kp_spn x in
  let lenek = parse_term("LENGTH(ek:byte list) = "^string_of_int(kp_pkb k)) in
  (* past the check, m into GIN *)
  API_TO_PC_TAC ex (layout(api_param k ^ "_enc_derand") + 76) THEN
  ON_STATE(fun kk -> ARM_STEPS_TAC ex ((kk+1)--(kk+3))) THEN
  ON_STATE(API_JOIN32_TAC (sp(en_gin k)) `m:byte list`) THEN
  (* H(ek) and the transposed matrix *)
  SUBGOAL_THEN (parse_term("!i j. i < "^ks^" /\\ j < "^ks^
     " ==> mlkem_samplentt_terminates (APPEND ("^
     string_of_term rho^") [word i; word j])"))
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  (if k = 2 then
     next THEN
     ON_STATE(API_HASH_H_CALL_TAC ex `ek:byte list` (ASSUME lenek)) THEN
     next THEN
     ON_STATE(fun kk gl ->
       (API_SLICE_AT_TAC `pk:int64` `ek:byte list` (384 * k) 32 kk THEN
        API_CONSTS_TAC THEN API_GM_CALL_TAC ex gmth
         (fun r -> [r `X0`; r `X1`; rho; r `X4`; r `X5`; r `X6`; `pc:num`;
                    r `SP`; r `X30`]) kk) gl)
   else
     next THEN
     ON_STATE(fun kk gl ->
       (API_SLICE_AT_TAC `pk:int64` `ek:byte list` (384 * k) 32 kk THEN
        API_CONSTS_TAC THEN API_GM_CALL_TAC ex gmth
         (fun r -> [r `X0`; r `X1`; rho; r `X4`; `word 0:int64`;
                    `word 0:int64`; `word 0:int64`; `pk:int64`;
                    `ek:byte list`; sp(en_gin k + 32); r `X5`; r `X6`;
                    `pc:num`; r `SP`; r `X30`]) kk) gl)) THEN
  (* (K, r) = G(m || H(ek)) *)
  ON_STATE(fun kk gl ->
    (MP_TAC(SPECL [sp(en_gin k); `m:byte list`; `sha3_256 ek`; state_of kk]
                  READ_MEMORY_BYTES_64_OF_32S) THEN
     ANTS_TAC THENL
      [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
       ASM_REWRITE_TAC[] THEN NO_TAC;
       DISCH_TAC]) gl) THEN
  next THEN
  ON_STATE(API_HASH_G_MSG_CALL_TAC ex en_hmsg
            ((REWRITE_CONV[LENGTH_APPEND; LENGTH_SHA3_256;
                           ASSUME `LENGTH(m:byte list) = 32`] THENC
              NUM_REDUCE_CONV)
             (mk_comb(`LENGTH:byte list->num`,en_hmsg)))) THEN
  ON_STATE(fun kk ->
    API_SLICE_AT_TAC (sp(en_kr k)) `sha3_512 (APPEND m (sha3_256 ek))` 0 32 kk
    THEN
    API_SLICE_AT_TAC (sp(en_kr k)) `sha3_512 (APPEND m (sha3_256 ek))` 32 32
      kk) THEN
  (* the noise from r *)
  SUBGOAL_THEN (mk_conj(mk_eq(mk_comb(`LENGTH:byte list->num`,en_r),`32`),
                        mk_eq(mk_comb(`LENGTH:byte list->num`,en_kk),`32`)))
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[LENGTH_MLKEM_SLICE]; ALL_TAC] THEN
  next THEN ON_STATE(API_GETNOISE_CALL_TAC ex en_r) THEN
  ON_STATE(fun kk -> RULE_ASSUM_TAC(fun th ->
    if free_in (state_of kk) (concl th) &&
       can (find_term (fun t -> is_const t && name_of t = "mlkem_prf"))
           (concl th)
    then REWRITE_RULE[ADD_CLAUSES] th else th)) THEN
  (* the ciphertext *)
  next THEN
  ON_STATE(fun kk gl ->
    let r c = find_read_fact c kk gl in
    API_IMAGE_CALL_TAC ex
     (REWRITE_RULE[PAIRWISE; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES]
       (SPECL [r `X0`; r `X1`; r `X2`; r `X3`; r `X4`; `ek:byte list`;
               `m:byte list`; en_r; `pc:num`; r `SP`; r `X30`] pth)) kk gl)
  THEN
  (* the shared secret *)
  ON_STATE(API_BYTES128_OF_32_AT_TAC (sp(en_kr k))
            (mk_comb(`num_of_bytelist`,en_kk))) THEN
  ON_STATE(fun kk -> ARM_STEPS_TAC ex ((kk+1)--(kk+3))) THEN
  ON_STATE(API_JOIN32_TAC `ss:int64` en_kk) THEN
  API_TO_PC_TAC ex (en_zero k) THEN
  ON_STATE(API_LEMMA_STEP_TAC ex
   (SPECL [kp_spn(en_cstack k); `pc:num`] zth)) THEN
  API_TO_PC_TAC ex (-1) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[en_encaps_pair k];;

(*** The invalid path, and the proof for k with the case split on the
 *** modulus check
 ***)

let EN_INVALID_TAC k ex =
  API_TO_PC_TAC ex (-1) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let EN_TAC k ex next gmth (pth,zth) =
  let eks = ek_check_slice k in
  EN_SETUP_TAC k ex THEN
  next THEN ON_STATE(API_CHECK_ENCODING_CALL_TAC ex k `ek:byte list`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP eks
   (ASSUME(parse_term("LENGTH(ek:byte list) = "^string_of_int(kp_pkb k))))])
  THEN
  API_BOOL_CASE_TAC (parse_term("mlkem_ek_check "^api_param k^" ek")) THENL
   [EN_VALID_TAC k ex next gmth (pth,zth); EN_INVALID_TAC k ex];;

(*** The proof of enc_derand for k, with the code ex of the function and
 *** the theorems gmth and pth for gen_matrix and pke_encrypt
 ***)

let MLKEM_NATIVE2_ENC_DERAND_CORRECT_TAC k ex gmth pth =
  let nm = api_param k in
  let nx = API_TO_CALL_TAC ex (layout(nm ^ "_enc_derand"))
                              (layout(nm ^ "_pke_decrypt")) in
  let zl = en_at k - en_gin k in
  let zth = prove(api_zero_tm (en_zero k) (en_zero k + 24) 96 zl,
                  API_ZERO_TAC ex (en_zero k) 3 (en_zero k + 24) 96 zl) in
  MLKEM_SAMPLENTT_TERMINATES_TAC (api_terminates_tm k (en_rho k) true)
   (EN_TAC k ex nx gmth (pth,zth));;

(* ------------------------------------------------------------------------- *)
(* dec                                                                       *)
(* ------------------------------------------------------------------------- *)

(*** The selection of the shared secret after the comparison: K' if
 *** Q2 = 0 (the ciphertexts are equal), else J, stored at X19
 ***)

let api_sel_tm start kr jo =
  let ns = mk_small_numeral in
  vsubst [ns start,`start:num`; ns(start + 52),`stop:num`; ns kr,`kr:num`;
          ns jo,`jo:num`]
  `!ss sp b (kk:byte list) (jj:byte list) pc.
     LENGTH kk = 32 /\ LENGTH jj = 32 /\
     nonoverlapping (ss,32) (word pc,mlkem_native2_image_size)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + start) /\
               read SP s = sp /\ read X19 s = ss /\
               (read Q2 s = word 0 <=> b) /\
               read (memory :> bytes(word_add sp (word kr),32)) s =
               num_of_bytelist kk /\
               read (memory :> bytes(word_add sp (word jo),32)) s =
               num_of_bytelist jj)
          (\s. read PC s = word(pc + stop) /\
               read (memory :> bytes(ss,32)) s =
               num_of_bytelist(if b then kk else jj))
          (MAYCHANGE [PC; X0; X1; X2] ,,
           MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6] ,,
           MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(ss,32)])`;;

(*** The code of dec: the offsets of its loops in the image, and the next
 *** function (where the steps to a callee stop)
 ***)

let de_fn k = layout(api_param k ^ "_dec");;
let de_after k = match k with
    2 -> layout "mlkem768_check_pk" | 3 -> layout "mlkem1024_check_pk"
  | _ -> layout "mlkem_gen_matrix";;
let de_copy k = layout(api_param k ^ "_dec_copyct");;
let de_cmp k = layout(api_param k ^ "_dec_compare");;
let de_sel k = de_cmp k + 24;;
let de_zv k = de_sel k + 52;;
let de_zi k = layout(api_param k ^ "_dec_invalid");;
let de_zlen k = de_at k - de_gin k;;

(*** The loops of dec for k, as lemmas: the copy of c, the comparison of
 *** the ciphertexts, the selection and the two zeroings
 ***)

let de_loops k ex =
  let ctb = pe_ctb k and zl = de_zlen k in
  let cp = prove(api_copy_tm (de_copy k) (ctb / 32),
                 API_COPY_TAC ex (de_copy k) (ctb / 32)) in
  let cm = prove(api_cmp_tm (de_cmp k) (ctb / 16),
                 API_CMP_TAC ex (de_cmp k) (ctb / 16)) in
  let sl = prove(api_sel_tm (de_sel k) 160 256, API_SEL_TAC ex 160 256) in
  let zv = prove(api_zero_tm (de_zv k) (de_zv k + 24) 96 zl,
                 API_ZERO_TAC ex (de_zv k) 3 (de_zv k + 24) 96 zl) in
  let zi = prove(api_zero_tm (de_zi k) (de_zi k + 24) 96 zl,
                 API_ZERO_TAC ex (de_zi k) 3 (de_zi k + 24) 96 zl) in
  cp,cm,sl,zv,zi;;

(*** The values of dec: the parts of dk, m', G(m' || h), K', r', z || c,
 *** J(z || c) and c'
 ***)

let de_slice a n = parse_term("mlkem_slice "^string_of_int a^" "^
                              string_of_int n^" (dk:byte list)");;
let de_dkpke k = de_slice 0 (384 * k);;
let de_ek k = de_slice (384 * k) (384 * k + 32);;
let de_rho k = de_slice (768 * k) 32;;
let de_h k = de_slice (768 * k + 32) 32;;
let de_z k = de_slice (768 * k + 64) 32;;
let de_m k = list_mk_icomb "kpke_decrypt"
  [parse_term(api_param k); de_dkpke k; `c:byte list`];;
let de_hmsg k = list_mk_icomb "APPEND" [de_m k; de_h k];;
let de_g k = mk_comb(`sha3_512`,de_hmsg k);;
let de_kp k = list_mk_icomb "mlkem_slice" [`0`; `32`; de_g k];;
let de_rp k = list_mk_icomb "mlkem_slice" [`32`; `32`; de_g k];;
let de_zcm k = list_mk_icomb "APPEND" [de_z k; `c:byte list`];;
let de_jj k =
  list_mk_icomb "list_of_seq" [mk_comb(`shake256`,de_zcm k); `32`];;
let de_c2 k = list_mk_icomb "kpke_encrypt"
  [parse_term(api_param k); de_ek k; de_m k; de_rp k];;

(*** rho in ek within dk, the hash check, and decapsulation with the hash
 *** functions unfolded, for k
 ***)

let de_rho_eq k =
  let a = 384 * k in
  prove(mk_eq(list_mk_icomb "mlkem_slice"
                [mk_small_numeral a; `32`; de_slice a (a + 32)],
              de_rho k),
        SIMP_TAC[MLKEM_SLICE_SLICE; ARITH]);;

let de_check_th k =
  let n = string_of_int in
  prove(parse_term("!dk c. LENGTH dk = "^n(kp_skb k)^" /\\ LENGTH c = "^
    n(pe_ctb k)^" ==> (mlkem_decaps_check "^api_param k^" dk c <=> "^
    "sha3_256 (mlkem_slice "^n(384 * k)^" "^n(384 * k + 32)^" dk) = "^
    "mlkem_slice "^n(768 * k + 32)^" 32 dk)"),
    REWRITE_TAC[kp_param_def k; mlkem_decaps_check; mlkem_h] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let de_decaps_alt k =
  CONV_RULE(TOP_DEPTH_CONV let_CONV THENC NUM_REDUCE_CONV)
   (REWRITE_RULE[GSYM(kp_param_def k)]
     (ISPECL (kp_params k) MLKEM_DECAPS_ALT));;

(*** Two adjacent byte lists in memory as their concatenation ***)

let READ_MEMORY_BYTES_APPEND = prove
 (`!a (l1:byte list) l2 n1 n2 s:armstate.
     LENGTH l1 = n1 /\
     read (memory :> bytes(a,n1)) s = num_of_bytelist l1 /\
     read (memory :> bytes(word_add a (word n1),n2)) s = num_of_bytelist l2
     ==> read (memory :> bytes(a,n1 + n2)) s = num_of_bytelist(APPEND l1 l2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[READ_MEMORY_BYTES_SPLIT] THEN
  ASM_REWRITE_TAC[NUM_OF_BYTELIST_APPEND]);;

(*** A 32-byte slice of dk copied by ldp/stp q0, q1 to the stack at dst ***)

let DE_COPY32_TAC ex off dst l kk =
  let src = mk_comb(`word_add (sk:int64)`,
                    mk_comb(`word:num->int64`,mk_small_numeral off)) in
  API_SLICE_AT_TAC `sk:int64` `dk:byte list` off 32 kk THEN
  API_BYTES128_OF_32_AT_TAC src (mk_comb(`num_of_bytelist`,l)) kk THEN
  ARM_STEPS_TAC ex ((kk+1)--(kk+4)) THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,l),`32`)) ASSUME_TAC
  THENL [REWRITE_TAC[LENGTH_MLKEM_SLICE]; ALL_TAC] THEN
  API_JOIN32_TAC dst l (kk+4);;

(*** The branch of the hash check at state kk: its condition as the check ***)

let DE_HASH_BRANCH_TAC k kk =
  let sv = state_of kk in
  let chk = MATCH_MP (de_check_th k)
   (CONJ (ASSUME(parse_term("LENGTH(dk:byte list) = "^
                            string_of_int(kp_skb k))))
         (ASSUME(parse_term("LENGTH(c:byte list) = "^
                            string_of_int(pe_ctb k))))) in
  let bnd l =
    let th = ISPEC l NUM_OF_BYTELIST_BOUND in
    CONV_RULE NUM_REDUCE_CONV
     (REWRITE_RULE[LENGTH_SHA3_256; LENGTH_MLKEM_SLICE] th) in
  let hek = mk_comb(`sha3_256`,de_ek k) and h = de_h k in
  let lenth = prove(mk_eq(mk_comb(`LENGTH:byte list->num`,hek),
                          mk_comb(`LENGTH:byte list->num`,h)),
                    REWRITE_TAC[LENGTH_SHA3_256; LENGTH_MLKEM_SLICE]) in
  let inj = MP (ISPECL [hek; h] NUM_OF_BYTELIST_INJ) lenth in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read PC (s:armstate) = (x:int64)`) c &&
       rand(lhand c) = sv
    then
      let vt = find_term (can (term_match [] `val(x:int64) = 0`)) c in
      let eth = PART_MATCH (lhand o rand) WORD_OR_XOR_DIGITS_EQ_0 vt in
      let eth' = MP (CONV_RULE(RATOR_CONV(RAND_CONV NUM_REDUCE_CONV)) eth)
                    (CONJ (bnd hek) (bnd h)) in
      ASSUME_TAC(REWRITE_RULE[GSYM chk] (REWRITE_RULE[eth'; inj] th))
    else NO_TAC);;

(*** The script of dec for k ***)

let de_skoff a = mk_comb(`word_add (sk:int64)`,
                         mk_comb(`word:num->int64`,mk_small_numeral a));;

(*** The setup ***)

let DE_SETUP_TAC k ex =
  MAP_EVERY X_GEN_TAC
   [`ss:int64`; `ct:int64`; `sk:int64`; `dk:byte list`; `c:byte list`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC (de_stack k) THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; PAIRWISE; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
              (mk_const("X"^string_of_int n,[]))) (19--29) THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC ex (1--14) THEN MLKEM_NATIVE_ADRP_TAC;;

(*** m' = K-PKE.Decrypt(dk_pke, c), h after it, and G(m' || h) ***)

let DE_DECRYPT_TAC k ex next pdth =
  let sp x = kp_spn x in
  let lenm = mk_eq(mk_comb(`LENGTH:byte list->num`,de_m k),`32`) in
  next THEN
  ON_STATE(fun kk gl ->
    (API_SLICE_AT_TAC `sk:int64` `dk:byte list` 0 (384 * k) kk THEN
     (fun gl ->
       let r c = find_read_fact c kk gl in
       API_IMAGE_CALL_TAC ex
        (REWRITE_RULE[PAIRWISE; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES;
                      LENGTH_MLKEM_SLICE]
          (SPECL [r `X0`; r `X1`; r `X2`; `c:byte list`; de_dkpke k;
                  `pc:num`; r `SP`; r `X30`] pdth)) kk gl)) gl) THEN
  SUBGOAL_THEN lenm ASSUME_TAC THENL
   [REWRITE_TAC[kp_param_def k; KPKE_DECRYPT_LENGTH]; ALL_TAC] THEN
  ON_STATE(DE_COPY32_TAC ex (768 * k + 32) (sp(de_gin k + 32)) (de_h k)) THEN
  ON_STATE(fun kk gl ->
    (MP_TAC(SPECL [sp(de_gin k); de_m k; de_h k; state_of kk]
                  READ_MEMORY_BYTES_64_OF_32S) THEN
     ANTS_TAC THENL
      [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
       ASM_REWRITE_TAC[] THEN NO_TAC;
       DISCH_TAC]) gl) THEN
  next THEN
  ON_STATE(API_HASH_G_MSG_CALL_TAC ex (de_hmsg k)
    ((REWRITE_CONV[LENGTH_APPEND; LENGTH_MLKEM_SLICE; ASSUME lenm] THENC
      NUM_REDUCE_CONV) (mk_comb(`LENGTH:byte list->num`,de_hmsg k)))) THEN
  ON_STATE(fun kk ->
    API_SLICE_AT_TAC (sp(de_kr k)) (de_g k) 0 32 kk THEN
    API_SLICE_AT_TAC (sp(de_kr k)) (de_g k) 32 32 kk) THEN
  SUBGOAL_THEN (mk_conj(mk_eq(mk_comb(`LENGTH:byte list->num`,de_kp k),`32`),
                        mk_eq(mk_comb(`LENGTH:byte list->num`,de_rp k),`32`)))
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[LENGTH_MLKEM_SLICE]; ALL_TAC];;

(*** z || c on the stack ***)

let DE_ZC_TAC k ex (cp,_,_,_,_) =
  let sp x = kp_spn x and ctb = pe_ctb k in
  ON_STATE(DE_COPY32_TAC ex (768 * k + 64) (sp(de_zc k)) (de_z k)) THEN
  API_TO_PC_TAC ex (de_copy k) THEN
  ON_STATE(API_LEMMA_STEP_TAC ex
   (SPECL [sp(de_zc k + 32); `ct:int64`; `num_of_bytelist(c:byte list)`;
           `pc:num`] cp)) THEN
  ON_STATE(fun kk gl ->
    (MP_TAC(SPECL [sp(de_zc k); de_z k; `c:byte list`; `32`;
                   mk_small_numeral ctb; state_of kk]
                  READ_MEMORY_BYTES_APPEND) THEN
     ANTS_TAC THENL
      [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
       ASM_REWRITE_TAC[LENGTH_MLKEM_SLICE] THEN NO_TAC;
       CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN DISCH_TAC]) gl);;

(*** The matrix with H(ek) and J(z || c), and the noise, by gmth ***)

let DE_GM_TAC k ex next gmth =
  let sp x = kp_spn x and ks = string_of_int k in
  let rho = de_rho k in
  SUBGOAL_THEN (parse_term("!i j. i < "^ks^" /\\ j < "^ks^
     " ==> mlkem_samplentt_terminates (APPEND ("^
     string_of_term rho^") [word i; word j])"))
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`LENGTH:byte list->num`,de_zcm k),
                      mk_small_numeral(32 + pe_ctb k))) ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; LENGTH_MLKEM_SLICE] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  next THEN
  ON_STATE(fun kk gl ->
    (API_SLICE_AT_TAC `sk:int64` `dk:byte list` (768 * k) 32 kk THEN
     API_SLICE_AT_TAC `sk:int64` `dk:byte list` (384 * k) (384 * k + 32) kk
     THEN API_CONSTS_TAC THEN
     API_GM_CALL_TAC ex gmth
      (fun r ->
        [r `X0`; r `X1`; rho; r `X4`; de_skoff(384 * k); de_ek k;
         sp(de_hek k); sp(de_zc k); de_zcm k; sp(de_j k); r `X5`] @
        (if k = 2 then [] else
         [sp(de_kr k + 32); de_rp k; sp(de_noise k)]) @
        [r `X6`; `pc:num`; r `SP`; r `X30`]) kk) gl) THEN
  (if k = 2 then next THEN ON_STATE(API_GETNOISE_CALL_TAC ex (de_rp k))
   else ALL_TAC) THEN
  ON_STATE(fun kk -> RULE_ASSUM_TAC(fun th ->
    if free_in (state_of kk) (concl th) &&
       can (find_term (fun t -> is_const t && name_of t = "mlkem_prf"))
           (concl th)
    then REWRITE_RULE[ADD_CLAUSES] th else th));;

(*** The hash check H(ek) = h, and the case split on it ***)

let DE_CHECK_TAC k ex =
  let sp x = kp_spn x in
  ON_STATE(fun kk ->
    BIGDIGITS_32_TAC (sp(de_hek k))
     (mk_comb(`num_of_bytelist`,mk_comb(`sha3_256`,de_ek k))) (state_of kk)
    THEN
    BIGDIGITS_32_TAC (de_skoff(768 * k + 32))
     (mk_comb(`num_of_bytelist`,de_h k)) (state_of kk) THEN
    ARM_STEPS_TAC ex ((kk+1)--(kk+14))) THEN
  ON_STATE(DE_HASH_BRANCH_TAC k) THEN
  API_BOOL_CASE_TAC (parse_term("mlkem_decaps_check "^api_param k^" dk c"));;

(*** The valid path: c' = K-PKE.Encrypt(ek, m', r'), the comparison, the
 *** selection of ss and the zeroing
 ***)

let DE_VALID_TAC k ex next peth (_,cm,sl,zv,_) =
  let sp x = kp_spn x and ctb = pe_ctb k in
  let lenc2 = mk_eq(mk_comb(`LENGTH:byte list->num`,de_c2 k),
                    mk_small_numeral ctb) in
  next THEN
  ON_STATE(fun kk gl ->
    let r c = find_read_fact c kk gl in
    API_IMAGE_CALL_TAC ex
     (REWRITE_RULE[PAIRWISE; ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES;
                   de_rho_eq k; LENGTH_MLKEM_SLICE]
       (SPECL [r `X0`; r `X1`; r `X2`; r `X3`; r `X4`; de_ek k; de_m k;
               de_rp k; `pc:num`; r `SP`; r `X30`] peth)) kk gl) THEN
  SUBGOAL_THEN lenc2 ASSUME_TAC THENL
   [REWRITE_TAC[kp_param_def k; KPKE_ENCRYPT_LENGTH] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  API_TO_PC_TAC ex (de_cmp k) THEN
  ON_STATE(API_LEMMA_STEP_TAC ex
   (SPECL [`ct:int64`; sp(de_ct2 k); `num_of_bytelist(c:byte list)`;
           mk_comb(`num_of_bytelist`,de_c2 k); `pc:num`] cm)) THEN
  (fun gl ->
    let lenc = ASSUME(mk_eq(`LENGTH(c:byte list)`,mk_small_numeral ctb)) in
    let inj = MP (ISPECL [`c:byte list`; de_c2 k] NUM_OF_BYTELIST_INJ)
                 (TRANS lenc (SYM(ASSUME lenc2))) in
    let inj' = TRANS inj (ISPECL [`c:byte list`; de_c2 k] EQ_SYM_EQ) in
    RULE_ASSUM_TAC(REWRITE_RULE[inj']) gl) THEN
  ON_STATE(API_LEMMA_STEP_TAC ex
   (REWRITE_RULE[LENGTH_MLKEM_SLICE; LENGTH_LIST_OF_SEQ]
     (SPECL [`ss:int64`; kp_spn(de_cstack k);
             mk_eq(de_c2 k,`c:byte list`); de_kp k; de_jj k; `pc:num`] sl)))
  THEN
  ON_STATE(API_LEMMA_STEP_TAC ex (SPECL [kp_spn(de_cstack k); `pc:num`] zv))
  THEN
  API_TO_PC_TAC ex (-1) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[de_decaps_alt k];;

(*** The invalid path, and the proof for k with the case split on the hash
 *** check
 ***)

let DE_INVALID_TAC k ex (_,_,_,_,zi) =
  ON_STATE(API_LEMMA_STEP_TAC ex (SPECL [kp_spn(de_cstack k); `pc:num`] zi))
  THEN
  API_TO_PC_TAC ex (-1) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let DE_TAC k ex next gmth (pdth,peth) lps =
  DE_SETUP_TAC k ex THEN
  DE_DECRYPT_TAC k ex next pdth THEN
  DE_ZC_TAC k ex lps THEN
  DE_GM_TAC k ex next gmth THEN
  DE_CHECK_TAC k ex THENL
   [DE_VALID_TAC k ex next peth lps; DE_INVALID_TAC k ex lps];;

(*** The proof of dec for k, with the code ex of the function and the
 *** theorems gmth, pdth and peth for gen_matrix, pke_decrypt and
 *** pke_encrypt
 ***)

let MLKEM_NATIVE2_DEC_CORRECT_TAC k ex gmth (pdth,peth) =
  let nx = API_TO_CALL_TAC ex (de_fn k) (de_after k) in
  let lps = de_loops k ex in
  MLKEM_SAMPLENTT_TERMINATES_TAC (api_terminates_tm k (de_rho k) true)
   (DE_TAC k ex nx gmth (pdth,peth) lps);;
