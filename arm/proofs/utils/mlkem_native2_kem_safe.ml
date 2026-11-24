(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the constant-time and memory safety proofs of the API functions *)
(* of mlkem_native2 (keypair_derand, enc_derand, dec and the internal        *)
(* pke_encrypt and pke_decrypt): the use of the safety contracts of their    *)
(* callees (the kernels with the frames of their correctness theorems;       *)
(* mlkem_check_encoding and mlkem_hash_g, on whose results the callers'      *)
(* events depend, as correctness and safety in one, "FULL"), the loops as    *)
(* single steps, and the proof of each function for a parameter set, given   *)
(* the contracts of the callees that depend on it.                           *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native2_kem.ml";;
needs "arm/proofs/utils/mlkem_native2_safety.ml";;
needs "arm/proofs/mlkem_native/asm/hash_g_spec.ml";;
needs "arm/proofs/mlkem_native/asm/hash_h_spec.ml";;
needs "arm/proofs/mlkem_native/asm/getnoise_spec.ml";;
needs "arm/proofs/mlkem_native/asm/check_encoding_spec.ml";;
needs "arm/proofs/mlkem_native/asm/keccak_f1600_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The zeroing of a stack buffer as one step, with its events.               *)
(* ------------------------------------------------------------------------- *)

(*** The zeroing of len bytes at stackpointer + off with stp q0, q0 and a
 *** count in X1, from start (setup instructions before the loop) to stop
 ***)

let api_zero_safe_tm start stop off len =
  let ns = mk_small_numeral in
  vsubst [ns start,`start:num`; ns stop,`stop:num`; ns off,`off:num`;
          ns len,`len:num`]
  `exists f_events.
     forall e stackpointer pc.
       nonoverlapping (word_add stackpointer (word off),len)
                      (word pc,mlkem_native2_image_size)
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + start) /\
                 read SP s = stackpointer /\
                 read events s = e)
            (\s. read PC s = word(pc + stop) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events stackpointer pc /\
                    memaccess_inbounds e2
                     [word_add stackpointer (word off),len]
                     [word_add stackpointer (word off),len]))
            (MAYCHANGE [PC; X0; X1] ,, MAYCHANGE [Q0] ,,
             MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bytes(word_add stackpointer (word off),
                                        len)])`;;

let API_ZERO_SAFE_TAC exec start setup stop off len =
  let n = len / 32 and ns = mk_small_numeral in
  let inv = vsubst [ns off,`off:num`; ns len,`len:num`]
   `\i s. read X0 s = word_add stackpointer (word(off + 32 * i)) /\
          read X1 s = word(len - 32 * i)` in
  let pcp k = mk_binop `(+):num->num->num` `pc:num` (ns k) in
  let ilt = vsubst [ns n,`n:num`] `i < n` in
  CONCRETIZE_F_EVENTS_TAC
   (vsubst [ns n,`n:num`]
     `\(stackpointer:int64) (pc:num).
        APPEND (f_ev_epil stackpointer pc)
               (APPEND (ENUMERATEL n (\i. f_ev_loop stackpointer pc i))
                       (f_ev_prol stackpointer pc)) :(uarch_event)list`) THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `pc:num`] THEN
  DISCH_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC (ns n) (pcp (start + 4 * setup)) (pcp stop)
   inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false exec (1--setup) THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN (vsubst [ns len,`len:num`]
     `word_sub (word(len - 32 * i)) (word 32):int64 =
      word(len - 32 * (i + 1)) /\
      val(word(len - 32 * (i + 1)):int64) = len - 32 * (i + 1)`)
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPECL [mk_binop `(-):num->num->num` (ns len)
                         `32 * i`; `32`]
          (INST_TYPE [`:64`,`:N`] WORD_SUB)) THEN
        ASM_SIMP_TAC[ARITH_RULE(mk_imp(ilt,
          vsubst [ns len,`len:num`] `32 <= len - 32 * i`))] THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
        REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        ASM_ARITH_TAC];
      ALL_TAC] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false exec (1--3) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE(vsubst [ns len,`len:num`; ns n,`n:num`]
        `32 * (i + 1) < len <=> i + 1 < n`)] THEN
      COND_CASES_TAC THEN REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false exec [] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

(* ------------------------------------------------------------------------- *)
(* The calls of the kernels by their safety theorems, and the proofs of      *)
(* pke_encrypt and pke_decrypt for k.                                        *)
(* ------------------------------------------------------------------------- *)

(*** The instantiation of a framed safety theorem th of the callee name:
 *** e, the C arguments from the registers, the PC, the stack pointer and
 *** the return address
 ***)

let safe_ilist th name =
  let vs = fst(strip_forall(snd(dest_exists(concl th)))) in
  let ca = find_term (fun t ->
    is_comb t && is_comb(rator t) &&
    (try fst(dest_const(rator(rator t))) = "C_ARGUMENTS"
     with Failure _ -> false)) (concl th) in
  let args = dest_list(rand(rator ca)) in
  map (fun v ->
    let n = name_of v in
    if n = "e" then v
    else if n = "pc" then parse_term("pc + "^name)
    else if n = "stackpointer" then `read SP s`
    else if n = "returnaddress" then `read X30 s`
    else
      let i = index v args in
      parse_term("read X"^string_of_int i^" s")) vs;;

(*** The framed safety theorems of the kernels, with their labels, and
 *** those of the kernels that depend on the parameter set
 ***)

let api_safe_kernels =
  ["mlkem_frombytes","H_FROMBYTES",MLKEM_FROMBYTES_SUBROUTINE_SAFE_FRAMED,
   mlkem_frombytes_mc;
   "mlkem_frommsg","H_FROMMSG",MLKEM_FROMMSG_SUBROUTINE_SAFE_FRAMED,
   mlkem_frommsg_mc;
   "mlkem_ntt_alt","H_NTT",MLKEM_NTT_ALT_SUBROUTINE_SAFE_FRAMED,
   mlkem_ntt_alt_mc;
   "mlkem_intt_alt","H_INTT",MLKEM_INTT_ALT_SUBROUTINE_SAFE_FRAMED,
   mlkem_intt_alt_mc;
   "mlkem_mulcache_compute","H_MULCACHE",
   MLKEM_MULCACHE_COMPUTE_SUBROUTINE_SAFE_FRAMED,mlkem_mulcache_compute_mc;
   "mlkem_tomont","H_TOMONT",MLKEM_TOMONT_SUBROUTINE_SAFE_FRAMED,
   mlkem_tomont_mc;
   "mlkem_reduce","H_REDUCE",MLKEM_REDUCE_SUBROUTINE_SAFE_FRAMED,
   mlkem_reduce_mc;
   "mlkem_add_reduce","H_ADD",MLKEM_ADD_REDUCE_SUBROUTINE_SAFE_FRAMED,
   mlkem_add_reduce_mc;
   "mlkem_sub_reduce","H_SUB",MLKEM_SUB_REDUCE_SUBROUTINE_SAFE_FRAMED,
   mlkem_sub_reduce_mc;
   "mlkem_tobytes_alt","H_TOBYTES",MLKEM_TOBYTES_ALT_SUBROUTINE_SAFE_FRAMED,
   mlkem_tobytes_alt_mc;
   "mlkem_tomsg","H_TOMSG",MLKEM_TOMSG_SUBROUTINE_SAFE_FRAMED,
   mlkem_tomsg_mc;
   "mlkem_basemul_k2_alt","H_BASEMUL2",
   MLKEM_BASEMUL_K2_ALT_SUBROUTINE_SAFE_FRAMED,mlkem_basemul_k2_alt_mc;
   "mlkem_basemul_k3_alt","H_BASEMUL3",
   MLKEM_BASEMUL_K3_ALT_SUBROUTINE_SAFE_FRAMED,mlkem_basemul_k3_alt_mc;
   "mlkem_basemul_k4_alt","H_BASEMUL4",
   MLKEM_BASEMUL_K4_ALT_SUBROUTINE_SAFE_FRAMED,mlkem_basemul_k4_alt_mc;
   "mlkem_compress_d4","H_COMPRESS4",
   MLKEM_COMPRESS_D4_SUBROUTINE_SAFE_FRAMED,mlkem_compress_d4_mc;
   "mlkem_compress_d5","H_COMPRESS5",
   MLKEM_COMPRESS_D5_SUBROUTINE_SAFE_FRAMED,mlkem_compress_d5_mc;
   "mlkem_compress_d10","H_COMPRESS10",
   MLKEM_COMPRESS_D10_SUBROUTINE_SAFE_FRAMED,mlkem_compress_d10_mc;
   "mlkem_compress_d11","H_COMPRESS11",
   MLKEM_COMPRESS_D11_SUBROUTINE_SAFE_FRAMED,mlkem_compress_d11_mc;
   "mlkem_decompress_d4","H_DECOMPRESS4",
   MLKEM_DECOMPRESS_D4_SUBROUTINE_SAFE_FRAMED,mlkem_decompress_d4_mc;
   "mlkem_decompress_d5","H_DECOMPRESS5",
   MLKEM_DECOMPRESS_D5_SUBROUTINE_SAFE_FRAMED,mlkem_decompress_d5_mc;
   "mlkem_decompress_d10","H_DECOMPRESS10",
   MLKEM_DECOMPRESS_D10_SUBROUTINE_SAFE_FRAMED,mlkem_decompress_d10_mc;
   "mlkem_decompress_d11","H_DECOMPRESS11",
   MLKEM_DECOMPRESS_D11_SUBROUTINE_SAFE_FRAMED,mlkem_decompress_d11_mc];;

(*** The assumptions of the safety of the kernels names and of the lemmas
 *** lems (label, theorem), and the calls of them for the run driver, with
 *** the public variables vars
 ***)

let API_SAFE_ASSUME_TAC names lems =
  let ks = filter (fun (n,_,_,_) -> mem n names) api_safe_kernels in
  MAP_EVERY (fun (_,label,th,_) -> ASSUME_CALLEE_TAILED_TAC th label)
    ks THEN
  MAP_EVERY (fun (label,th) -> ASSUME_CALLEE_TAILED_TAC th label) lems;;

let api_safe_calls exec vars names lems =
  let ks = filter (fun (n,_,_,_) -> mem n names) api_safe_kernels in
  map (fun (name,label,th,mc) ->
         layout name,
         NATIVE2_SAFE_THM_TAC exec vars label (layout name,mc) I
           (safe_ilist th name)) ks @
  map (fun (off,label,ilist) ->
         off,
         NATIVE2_SAFE_THM_TAC exec vars label (0,mlkem_native2_image_mc) I
           ilist) lems;;

let MLKEM_NATIVE2_PKE_ENCRYPT_SAFE_TAC k ex =
  let nm = api_param k in
  let names = ["mlkem_frombytes"; "mlkem_frommsg"; "mlkem_ntt_alt";
               "mlkem_mulcache_compute";
               "mlkem_basemul_k"^string_of_int k^"_alt"; "mlkem_intt_alt";
               "mlkem_add_reduce";
               "mlkem_compress_d"^string_of_int(api_du k);
               "mlkem_compress_d"^string_of_int(api_dv k)] in
  let z1s = pe_zero1 k in
  let z2s = z1s + 24 in
  let zl1 = 256 * k and uo = 96 + 768 * k and ul = 512 * k + 1024 in
  let z1 = prove(api_zero_safe_tm z1s z2s 96 zl1,
                 API_ZERO_SAFE_TAC ex z1s 3 z2s 96 zl1)
  and z2 = prove(api_zero_safe_tm z2s (z2s + 24) uo ul,
                 API_ZERO_SAFE_TAC ex z2s 3 (z2s + 24) uo ul) in
  let vars = [`ct:int64`; `at:int64`; `pk:int64`; `mp:int64`;
              `noise:int64`; `pc:num`; `stackpointer:int64`;
              `returnaddress:int64`] in
  let zil = [`e:(uarch_event)list`; `read SP s`; `pc:num`] in
  let calls = api_safe_calls ex vars names
                [z1s,"H_Z1",zil; z2s,"H_Z2",zil] in
  let ninit = if 1120 + 1280 * k < 4096 then 15 else 16 in
  let derive = [layout(nm ^ "_pke_encrypt") + 4 * ninit,
                (fun _ -> MLKEM_NATIVE_ADRP_TAC)] in
  API_SAFE_ASSUME_TAC names ["H_Z1",z1; "H_Z2",z2] THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
              (mk_const("X"^string_of_int n,[]))) (19--29) THEN
  ENSURES_INIT_TAC "s0" THEN
  NATIVE2_SAFE_RUN_TAC ex derive calls 0 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MEMACCESS_NUMERALS_TAC THEN NATIVE2_DISCHARGE_FRESH_TAC;;

let MLKEM_NATIVE2_PKE_DECRYPT_SAFE_TAC k ex =
  let nm = api_param k in
  let names = ["mlkem_decompress_d"^string_of_int(api_du k);
               "mlkem_decompress_d"^string_of_int(api_dv k);
               "mlkem_frombytes"; "mlkem_ntt_alt"; "mlkem_mulcache_compute";
               "mlkem_basemul_k"^string_of_int k^"_alt"; "mlkem_intt_alt";
               "mlkem_sub_reduce"; "mlkem_tomsg"] in
  let zs = pd_zero k and zl = 1280 * k + 1024 in
  let z = prove(api_zero_safe_tm zs (zs + 24) 96 zl,
                API_ZERO_SAFE_TAC ex zs 3 (zs + 24) 96 zl) in
  let vars = [`mp:int64`; `ct:int64`; `sk:int64`; `pc:num`;
              `stackpointer:int64`; `returnaddress:int64`] in
  let zil = [`e:(uarch_event)list`; `read SP s`; `pc:num`] in
  let calls = api_safe_calls ex vars names [zs,"H_Z",zil] in
  let ninit = if 1120 + 1280 * k < 4096 then 13 else 14 in
  let derive = [layout(nm ^ "_pke_decrypt") + 4 * ninit,
                (fun _ -> MLKEM_NATIVE_ADRP_TAC)] in
  API_SAFE_ASSUME_TAC names ["H_Z",z] THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
              (mk_const("X"^string_of_int n,[]))) (19--29) THEN
  ENSURES_INIT_TAC "s0" THEN
  NATIVE2_SAFE_RUN_TAC ex derive calls 0 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MEMACCESS_NUMERALS_TAC THEN NATIVE2_DISCHARGE_FRESH_TAC;;

(* ------------------------------------------------------------------------- *)
(* keypair_derand: G(d || k) by its FULL theorem, rho as a variable for the  *)
(* events, the matrix and the noise, the NTT domain and the encodings, the   *)
(* copy into sk with H(pk) and z, and rho in pk.                             *)
(* ------------------------------------------------------------------------- *)

(*** rho = FST(mlkem_g(d || k)) as a variable (an abbreviation), so that
 *** the events are a function of it: the assumptions rewritten with it
 ***)

let KP_RHO_ABBREV_TAC (asl,w as gl) =
  let ab = find_asm (fun c ->
    is_eq c && is_var(rand c) && name_of(rand c) = "rho" &&
    can (find_term (fun t -> try fst(dest_const t) = "mlkem_g"
                             with Failure _ -> false)) (lhand c)) gl in
  RULE_ASSUM_TAC(fun th -> if concl th = concl ab then th
                           else REWRITE_RULE[ab] th) gl;;

(*** A call of a function of the image by its theorem with the label, all
 *** the variables but e_tail given (args), the lengths of slices and of the
 *** outputs of G rewritten
 ***)

let API_SAFE_SIM_TAC exec vars label args k =
  NATIVE2_SAFE_IMAGE_TAC exec vars [LENGTH_MLKEM_G; LENGTH_MLKEM_SLICE]
    label args k;;

(*** G = SHA3-512 on d || k by the FULL theorem, then rho and sigma, the
 *** constants for gen_matrix and rho as two 16-byte words
 ***)

let KP_HG_SAFE_CALL_TAC exec vars k kk gl =
  let d = `d:byte list` in
  let a = find_read_fact `X1` kk gl and sv = state_of kk in
  let m = mk_comb(mk_comb(`APPEND:byte list->byte list->byte list`,d),
                  mk_list([mk_comb(`word:num->byte`,mk_small_numeral k)],
                          `:byte`)) in
  let gin = SPECL [a; d; mk_comb(`word:num->byte`,mk_small_numeral k); sv]
              READ_MEMORY_BYTES_33_OF_PIECES in
  let ldth = find_asm (fun c ->
    c = mk_eq(mk_comb(`LENGTH:byte list->num`,d),`32`)) gl in
  let lenth = (REWRITE_CONV[LENGTH_APPEND; LENGTH; ldth] THENC
               NUM_REDUCE_CONV) (mk_comb(`LENGTH:byte list->num`,m)) in
  let r c = find_read_fact c kk gl in
  (MP_TAC gin THEN ANTS_TAC THENL
    [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
     CONV_TAC(DEPTH_CONV NUM_EXP_CONV) THEN ASM_REWRITE_TAC[] THEN NO_TAC;
     DISCH_TAC] THEN
   ASSUME_TAC lenth THEN
   FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[WORD_ADD] o
     MATCH_MP MLKEM_NATIVE2_ROUND_CONSTANTS o
     check (can (term_match [] `aligned_bytes_loaded s (word pc) mc`) o
            concl)) THEN
   API_SAFE_SIM_TAC exec vars "H_HG"
    [r `X0`; a; m; `33`; r `X3`; `pc:num`; r `SP`; r `X30`] kk THEN
   API_G_SPLIT_TAC (kk+1) THEN API_CONSTS_TAC THEN
   ASSUME_TAC(CONJUNCT1(ISPEC m LENGTH_MLKEM_G)) THEN
   KP_RHO_ABBREV_TAC THEN
   API_BYTES128_OF_32_AT_TAC (kp_spn(kp_cstack k + 160))
     `num_of_bytelist(rho:byte list)` (kk+1)) gl;;

(*** gen_matrix by its safety theorem: k = 2 without noise, else with the
 *** noise of s and e
 ***)

let KP_GM_SAFE_CALL_TAC exec vars k kk gl =
  let r c = find_read_fact c kk gl in
  let args =
    if k = 2 then
      [r `X0`; r `X1`; `rho:byte list`; r `X4`; r `X5`; r `X6`; `pc:num`;
       r `SP`; r `X30`]
    else
      [r `X0`; r `X1`; `rho:byte list`; r `X5`; kp_spn(kp_cstack k + 192);
       kp_spn(kp_s k); r `X4`; r `X6`; `pc:num`; r `SP`; r `X30`] in
  API_SAFE_SIM_TAC exec vars "H_GM" args kk gl;;

(*** mlkem_getnoise and mlkem_hash_h by their safety theorems ***)

let API_GETNOISE_SAFE_CALL_TAC exec vars kk gl =
  let v reg = mk_small_numeral(dest_small_numeral
                (rand(find_read_fact reg kk gl))) in
  let vs = vars @ fev_vars gl in
  REMOVE_THEN "H_GETNOISE" (fun th ->
    let th1 = SPECL [`e:(uarch_event)list`; find_read_fact `X0` kk gl;
                     find_read_fact `X1` kk gl; v `X2`; v `X3`; v `X4`;
                     v `X5`; find_read_fact `X6` kk gl; `pc:num`;
                     find_read_fact `SP` kk gl; find_read_fact `X30` kk gl]
                    th in
    let th2 = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
               (REWRITE_RULE[ARITH_EQ] th1) in
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
     (mlkem_native2_image_mc,exec,0,mlkem_native2_image_mc,
      FRESH_TAIL_RULE th2) [] (kk+1)
    THENL [EXISTS_E2_TAC (ref vs); LABEL_TAC "H_GETNOISE" th]) gl;;

let API_HASH_H_SAFE_CALL_TAC exec vars kk gl =
  let r c = find_read_fact c kk gl in
  let len = mk_small_numeral(dest_small_numeral(rand(r `X2`))) in
  API_SAFE_SIM_TAC exec vars "H_HH"
   [r `X0`; r `X1`; len; r `X3`; `pc:num`; r `SP`; r `X30`] kk gl;;

(*** The proof of the safety of keypair_derand for k: the setup, the run
 *** and the end, as parts for debugging
 ***)

let kp_safe_parts k ex gmth =
  let nm = api_param k in
  let names = ["mlkem_ntt_alt"; "mlkem_mulcache_compute";
               "mlkem_basemul_k"^string_of_int k^"_alt"; "mlkem_tomont";
               "mlkem_add_reduce"; "mlkem_reduce"; "mlkem_tobytes_alt"] in
  let so = 256 + 512 * k * k and sl = 1280 * k in
  let z1 = prove(api_zero_safe_tm (kp_zero1 k) (kp_zero2 k) 96 160,
                 API_ZERO_SAFE_TAC ex (kp_zero1 k) 3 (kp_zero2 k) 96 160)
  and z2 = prove(api_zero_safe_tm (kp_zero2 k) (kp_zero2_stop k) so sl,
                 API_ZERO_SAFE_TAC ex (kp_zero2 k) (kp_zero2_setup k)
                   (kp_zero2_stop k) so sl) in
  let vars = [`pk:int64`; `sk:int64`; `coins:int64`; `pc:num`;
              `stackpointer:int64`; `returnaddress:int64`; `rho:byte list`] in
  let zil = [`e:(uarch_event)list`; `read SP s`; `pc:num`] in
  let calls =
    api_safe_calls ex vars names [kp_zero1 k,"H_Z1",zil; kp_zero2 k,"H_Z2",zil]
    @ [layout "mlkem_hash_g", KP_HG_SAFE_CALL_TAC ex vars k;
       layout "mlkem_gen_matrix", KP_GM_SAFE_CALL_TAC ex vars k;
       layout "mlkem_getnoise", API_GETNOISE_SAFE_CALL_TAC ex vars;
       layout "mlkem_hash_h", API_HASH_H_SAFE_CALL_TAC ex vars] in
  let derive = [layout(nm ^ "_keypair_derand") + 4 * 14,
                (fun _ -> MLKEM_NATIVE_ADRP_TAC)] in
  let setup =
    API_SAFE_ASSUME_TAC names ["H_Z1",z1; "H_Z2",z2] THEN
    ASSUME_CALLEE_TAILED_TAC MLKEM_NATIVE_HASH_G_SHORT_ASM_IMAGE_SUBROUTINE_FULL "H_HG" THEN
    ASSUME_CALLEE_TAILED_TAC gmth "H_GM" THEN
    ASSUME_CALLEE_TAILED_TAC MLKEM_NATIVE_GETNOISE_ASM_IMAGE_SUBROUTINE_SAFE "H_GETNOISE" THEN
    ASSUME_CALLEE_TAILED_TAC MLKEM_NATIVE_HASH_H_ASM_IMAGE_SUBROUTINE_SAFE "H_HH" THEN
    META_EXISTS_TAC THEN
    MAP_EVERY X_GEN_TAC
     [`e:(uarch_event)list`; `pk:int64`; `sk:int64`; `coins:int64`;
      `d:byte list`; `pc:num`] THEN
    WORD_FORALL_OFFSET_TAC (kp_stack k) THEN
    MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
                C_RETURN; ALL; PAIRWISE; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
    REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    ABBREV_TAC(mk_eq(`rho:byte list`,kp_rho k)) THEN KP_RHO_ABBREV_TAC THEN
    ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
    ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
    MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
                (mk_const("X"^string_of_int n,[]))) (19--29) THEN
    ENSURES_INIT_TAC "s0" THEN
    API_BYTES128_OF_32_TAC `coins:int64` `num_of_bytelist(d:byte list)`
  and finish =
    ON_STATE(API_JOIN32_TAC
      (mk_comb(mk_comb(`word_add:int64->int64->int64`,`pk:int64`),
               mk_comb(`word:num->int64`,mk_small_numeral(384 * k))))
      `rho:byte list`) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MEMACCESS_NUMERALS_TAC THEN NATIVE2_DISCHARGE_FRESH_TAC in
  setup,derive,calls,finish;;

let MLKEM_NATIVE2_KEYPAIR_DERAND_SAFE_TAC k ex gmth =
  let setup,derive,calls,finish = kp_safe_parts k ex gmth in
  MLKEM_SAMPLENTT_TERMINATES_TAC (api_terminates_tm k (kp_rho k) true)
   (setup THEN NATIVE2_SAFE_RUN_TAC ex derive calls 0 THEN finish);;

(* ------------------------------------------------------------------------- *)
(* enc_derand: the modulus check by its FULL theorem and the case split on   *)
(* it; then H(pk), the matrix, G, the noise and K-PKE.Encrypt.               *)
(* ------------------------------------------------------------------------- *)

(*** The modulus check of ek at X0 by the FULL theorem, the result as
 *** mlkem_ek_check
 ***)

let API_CHECK_ENCODING_FULL_CALL_TAC exec vars k ek kk gl =
  let a = find_read_fact `X0` kk gl in
  let n = mk_comb(`num_of_bytelist`,
            list_mk_icomb "mlkem_slice"
             [`0`; mk_small_numeral(384 * k); ek]) in
  let vs = vars @ fev_vars gl in
  let eks = ek_check_slice k in
  let lenth = find_asm (fun c ->
    c = mk_eq(mk_comb(`LENGTH:byte list->num`,ek),
              mk_small_numeral(kp_pkb k))) gl in
  (API_SLICE_AT_TAC a ek 0 (384 * k) kk THEN
   REMOVE_THEN "H_CE" (fun th ->
     let th1 = SPECL [`e:(uarch_event)list`; a;
                      mk_comb(`word:num->int64`,mk_small_numeral k); n;
                      `pc + mlkem_check_encoding`;
                      find_read_fact `X30` kk gl] th in
     let th2 = REWRITE_RULE[ARITH_RULE `2 < 2 EXP 61 /\ 3 < 2 EXP 61 /\
                                        4 < 2 EXP 61`;
                            ARITH_RULE `4096 = 2 EXP 12`]
                (CONV_RULE(ONCE_DEPTH_CONV WORD_NUM_RED_CONV THENC
                           ONCE_DEPTH_CONV NUM_MULT_CONV) th1) in
     ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native2_image_mc,exec,layout "mlkem_check_encoding",
       mlkem_check_encoding_mc,FRESH_TAIL_RULE th2) [] (kk+1)
     THENL [EXISTS_E2_TAC (ref vs); LABEL_TAC "H_CE" th]) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP eks lenth])) gl;;

(*** gen_matrix by its safety theorem, with rho from ek ***)

let EN_GM_SAFE_CALL_TAC exec vars k kk gl =
  let r c = find_read_fact c kk gl in
  let rho = en_rho k in
  let args =
    if k = 2 then
      [r `X0`; r `X1`; rho; r `X4`; r `X5`; r `X6`; `pc:num`; r `SP`;
       r `X30`]
    else
      [r `X0`; r `X1`; rho; r `X4`; `word 0:int64`; `word 0:int64`;
       `word 0:int64`; `pk:int64`; kp_spn(en_gin k + 32); r `X5`; r `X6`;
       `pc:num`; r `SP`; r `X30`] in
  (API_SLICE_AT_TAC `pk:int64` `ek:byte list` (384 * k) 32 kk THEN
   API_CONSTS_TAC THEN
   API_SAFE_SIM_TAC exec vars "H_GM" args kk) gl;;

(*** hash_g of 64 bytes by its safety theorem, and pke_encrypt ***)

let API_HASH_G_SAFE_CALL_TAC exec vars kk gl =
  let r c = find_read_fact c kk gl in
  let len = mk_small_numeral(dest_small_numeral(rand(r `X2`))) in
  API_SAFE_SIM_TAC exec vars "H_HGS"
   [r `X0`; r `X1`; len; r `X3`; `pc:num`; r `SP`; r `X30`] kk gl;;

let API_PKE_SAFE_CALL_TAC exec vars label regs kk gl =
  let r c = find_read_fact c kk gl in
  API_SAFE_SIM_TAC exec vars label
   (map r regs @ [`pc:num`; r `SP`; r `X30`]) kk gl;;

(*** The proof of the safety of enc_derand for k, with the safety theorem
 *** peth of pke_encrypt, as parts for debugging
 ***)

let en_safe_parts k ex gmth peth =
  let nm = api_param k in
  let zl = en_at k - en_gin k in
  let zth = prove(api_zero_safe_tm (en_zero k) (en_zero k + 24) 96 zl,
                  API_ZERO_SAFE_TAC ex (en_zero k) 3 (en_zero k + 24) 96 zl) in
  let vars = [`ct:int64`; `ss:int64`; `pk:int64`; `coins:int64`; `pc:num`;
              `stackpointer:int64`; `returnaddress:int64`; `ek:byte list`] in
  let zil = [`e:(uarch_event)list`; `read SP s`; `pc:num`] in
  let calls =
    api_safe_calls ex vars [] [en_zero k,"H_Z",zil] @
    [layout "mlkem_check_encoding",
       API_CHECK_ENCODING_FULL_CALL_TAC ex vars k `ek:byte list`;
     layout "mlkem_hash_h", API_HASH_H_SAFE_CALL_TAC ex vars;
     layout "mlkem_gen_matrix", EN_GM_SAFE_CALL_TAC ex vars k;
     layout "mlkem_hash_g", API_HASH_G_SAFE_CALL_TAC ex vars;
     layout "mlkem_getnoise", API_GETNOISE_SAFE_CALL_TAC ex vars;
     layout (nm ^ "_pke_encrypt"),
       API_PKE_SAFE_CALL_TAC ex vars "H_PE" [`X0`; `X1`; `X2`; `X3`; `X4`]] in
  let ef = 288 + 512 * (2 * k + 1) + 512 * k * k in
  let ninit = 1 + (if ef < 4096 then 1 else 2) + 6 + 4 + 2 in
  let derive = [layout(nm ^ "_enc_derand") + 4 * ninit,
                (fun _ -> MLKEM_NATIVE_ADRP_TAC)] in
  let setup =
    API_SAFE_ASSUME_TAC [] ["H_Z",zth] THEN
    ASSUME_CALLEE_TAILED_TAC MLKEM_CHECK_ENCODING_SUBROUTINE_FULL "H_CE" THEN
    ASSUME_CALLEE_TAILED_TAC MLKEM_NATIVE_HASH_H_ASM_IMAGE_SUBROUTINE_SAFE "H_HH" THEN
    ASSUME_CALLEE_TAILED_TAC gmth "H_GM" THEN
    ASSUME_CALLEE_TAILED_TAC MLKEM_NATIVE_HASH_G_ASM_IMAGE_SUBROUTINE_SAFE "H_HGS" THEN
    ASSUME_CALLEE_TAILED_TAC MLKEM_NATIVE_GETNOISE_ASM_IMAGE_SUBROUTINE_SAFE "H_GETNOISE" THEN
    ASSUME_CALLEE_TAILED_TAC peth "H_PE" THEN
    CONCRETIZE_F_EVENTS_TAC (parse_term(
     "\\(ct:int64) (ss:int64) (pk:int64) (coins:int64) (pc:num) "^
     "  (stackpointer:int64) (returnaddress:int64) (ek:byte list). "^
     "  if mlkem_ek_check "^nm^" ek "^
     "  then f_ev_ok ct ss pk coins pc stackpointer returnaddress ek "^
     "  else f_ev_bad ct ss pk coins pc stackpointer returnaddress ek "^
     "  :(uarch_event)list")) THEN
    REPEAT META_EXISTS_TAC THEN
    MAP_EVERY X_GEN_TAC
     [`e:(uarch_event)list`; `ct:int64`; `ss:int64`; `pk:int64`;
      `coins:int64`; `ek:byte list`; `pc:num`] THEN
    WORD_FORALL_OFFSET_TAC (en_stack k) THEN
    MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
                C_RETURN; ALL; PAIRWISE; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
    REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    SUBGOAL_THEN (parse_term("!i j. i < "^string_of_int k^" /\\ j < "^
       string_of_int k^" ==> mlkem_samplentt_terminates (APPEND ("^
       string_of_term(en_rho k)^") [word i; word j])"))
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
    ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
    MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
                (mk_const("X"^string_of_int n,[]))) (19--29) THEN
    ENSURES_INIT_TAC "s0"
  and finish =
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MEMACCESS_NUMERALS_TAC THEN NATIVE2_DISCHARGE_FRESH_TAC in
  setup,derive,calls,finish;;

let MLKEM_NATIVE2_ENC_DERAND_SAFE_TAC k ex gmth peth =
  let setup,derive,calls,finish = en_safe_parts k ex gmth peth in
  MLKEM_SAMPLENTT_TERMINATES_TAC (api_terminates_tm k (en_rho k) true)
   (setup THEN NATIVE2_SAFE_RUN_TAC ex derive calls 0 THEN
    API_BOOL_CASE_TAC (parse_term("mlkem_ek_check "^api_param k^" ek")) THEN
    ON_STATE(NATIVE2_SAFE_RUN_TAC ex derive calls) THEN finish);;

(* ------------------------------------------------------------------------- *)
(* dec: K-PKE.Decrypt, G, the matrix with H(ek) as a result, ek and h as     *)
(* variables for the events, the hash check and the case split on it; then   *)
(* K-PKE.Encrypt, the comparison and the selection.                          *)
(* ------------------------------------------------------------------------- *)

(*** Abbreviations: the assumptions t = v with v a variable named in names
 *** used to rewrite the others, so that the events are functions of v
 ***)

let ABBREVS_TAC names (asl,w as gl) =
  let abs = filter (fun (_,th) ->
    let c = concl th in
    is_eq c && is_var(rand c) && mem (name_of(rand c)) names &&
    not(is_var(lhand c))) asl in
  let ths = map snd abs in
  RULE_ASSUM_TAC(fun th -> if mem (concl th) (map concl ths) then th
                           else REWRITE_RULE ths th) gl;;

(*** rho as the slice of ek in dk, so that the events are those of ek ***)

let de_rho_ek k =
  list_mk_icomb "mlkem_slice"
   [mk_small_numeral(384 * k); `32`; `ek:byte list`];;

(*** gen_matrix by its theorem with H(ek) as a result: rho, ek at
 *** sk + 384 * k and the termination for the transposed matrix
 ***)

let DE_GM_SAFE_CALL_TAC exec vars k kk gl =
  let sp x = kp_spn x in
  let r c = find_read_fact c kk gl in
  let args =
    [r `X0`; r `X1`; de_rho_ek k; r `X4`; de_skoff(384 * k); `ek:byte list`;
     sp(de_hek k); sp(de_zc k); sp(de_j k); r `X5`] @
    (if k = 2 then [] else [sp(de_kr k + 32); sp(de_noise k)]) @
    [r `X6`; `pc:num`; r `SP`; r `X30`] in
  (API_SLICE_AT_TAC `sk:int64` `dk:byte list` (768 * k) 32 kk THEN
   API_SLICE_AT_TAC `sk:int64` `dk:byte list` (384 * k) (384 * k + 32) kk THEN
   RULE_ASSUM_TAC(REWRITE_RULE[GSYM(de_rho_eq k)]) THEN
   ABBREVS_TAC ["ek"; "h"] THEN
   API_CONSTS_TAC THEN
   API_SAFE_SIM_TAC exec vars "H_GM" args kk) gl;;

(*** The hash check at state kk: the digest and h as 64-bit words, the
 *** code, and the branch as H(ek) = h
 ***)

let DE_HASH_SAFE_BRANCH_TAC k kk =
  let sv = state_of kk in
  let bnd l =
    let th = ISPEC l NUM_OF_BYTELIST_BOUND in
    CONV_RULE NUM_REDUCE_CONV
     (REWRITE_RULE[LENGTH_SHA3_256; ASSUME `LENGTH(h:byte list) = 32`] th) in
  let hek = `sha3_256 ek` and h = `h:byte list` in
  let lenth = TRANS (ISPEC `ek:byte list` LENGTH_SHA3_256)
                    (SYM(ASSUME `LENGTH(h:byte list) = 32`)) in
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
      ASSUME_TAC(REWRITE_RULE[eth'; inj] th)
    else NO_TAC);;

let DE_DIGITS_TAC k kk =
  let sp x = kp_spn x in
  BIGDIGITS_32_TAC (sp(de_hek k)) `num_of_bytelist(sha3_256 ek)`
   (state_of kk) THEN
  API_SLICE_AT_TAC `sk:int64` `dk:byte list` (768 * k + 32) 32 kk THEN
  ABBREVS_TAC ["ek"; "h"] THEN
  BIGDIGITS_32_TAC (de_skoff(768 * k + 32)) `num_of_bytelist(h:byte list)`
   (state_of kk);;

(*** The proof of the safety of dec for k, with the safety theorems pdth
 *** and peth of pke_decrypt and pke_encrypt, as parts for debugging
 ***)

let de_safe_parts k ex gmth (pdth,peth) =
  let nm = api_param k and zl = de_zlen k in
  let zv = prove(api_zero_safe_tm (de_zv k) (de_zv k + 24) 96 zl,
                 API_ZERO_SAFE_TAC ex (de_zv k) 3 (de_zv k + 24) 96 zl)
  and zi = prove(api_zero_safe_tm (de_zi k) (de_zi k + 24) 96 zl,
                 API_ZERO_SAFE_TAC ex (de_zi k) 3 (de_zi k + 24) 96 zl) in
  let vars = [`ss:int64`; `ct:int64`; `sk:int64`; `pc:num`;
              `stackpointer:int64`; `returnaddress:int64`;
              `ek:byte list`; `h:byte list`] in
  let zil = [`e:(uarch_event)list`; `read SP s`; `pc:num`] in
  let calls =
    api_safe_calls ex vars [] [de_zv k,"H_ZV",zil; de_zi k,"H_ZI",zil] @
    [layout (nm ^ "_pke_decrypt"),
       API_PKE_SAFE_CALL_TAC ex vars "H_PD" [`X0`; `X1`; `X2`];
     layout "mlkem_hash_g", API_HASH_G_SAFE_CALL_TAC ex vars;
     layout "mlkem_gen_matrix",
       (fun kk -> DE_GM_SAFE_CALL_TAC ex vars k kk THEN
                  (if k = 2 then ALL_TAC else DE_DIGITS_TAC k (kk+1)));
     layout "mlkem_getnoise",
       (fun kk -> API_GETNOISE_SAFE_CALL_TAC ex vars kk THEN
                  DE_DIGITS_TAC k (kk+1));
     layout (nm ^ "_pke_encrypt"),
       API_PKE_SAFE_CALL_TAC ex vars "H_PE" [`X0`; `X1`; `X2`; `X3`; `X4`]]
  in
  let derive = [layout(nm ^ "_dec") + 4 * 14,
                (fun _ -> MLKEM_NATIVE_ADRP_TAC)] in
  let setup =
    API_SAFE_ASSUME_TAC [] ["H_ZV",zv; "H_ZI",zi] THEN
    ASSUME_CALLEE_TAILED_TAC pdth "H_PD" THEN
    ASSUME_CALLEE_TAILED_TAC MLKEM_NATIVE_HASH_G_ASM_IMAGE_SUBROUTINE_SAFE "H_HGS" THEN
    ASSUME_CALLEE_TAILED_TAC gmth "H_GM" THEN
    ASSUME_CALLEE_TAILED_TAC MLKEM_NATIVE_GETNOISE_ASM_IMAGE_SUBROUTINE_SAFE "H_GETNOISE" THEN
    ASSUME_CALLEE_TAILED_TAC peth "H_PE" THEN
    CONCRETIZE_F_EVENTS_TAC
     `\(ss:int64) (ct:int64) (sk:int64) (pc:num) (stackpointer:int64)
       (returnaddress:int64) (ek:byte list) (h:byte list).
        if sha3_256 ek = h
        then f_ev_ok ss ct sk pc stackpointer returnaddress ek h
        else f_ev_bad ss ct sk pc stackpointer returnaddress ek h
        :(uarch_event)list` THEN
    REPEAT META_EXISTS_TAC THEN
    MAP_EVERY X_GEN_TAC
     [`e:(uarch_event)list`; `ss:int64`; `ct:int64`; `sk:int64`;
      `dk:byte list`; `pc:num`] THEN
    WORD_FORALL_OFFSET_TAC (de_stack k) THEN
    MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
                C_RETURN; ALL; PAIRWISE; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
    REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
    SUBGOAL_THEN (parse_term("!i j. i < "^string_of_int k^" /\\ j < "^
       string_of_int k^" ==> mlkem_samplentt_terminates (APPEND ("^
       string_of_term(vsubst [de_ek k,`ek:byte list`] (de_rho_ek k))^
       ") [word i; word j])"))
    ASSUME_TAC THENL
     [REWRITE_TAC[de_rho_eq k] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ASSUME_TAC(ISPECL [mk_small_numeral(384 * k);
                       mk_small_numeral(384 * k + 32); `dk:byte list`]
                      LENGTH_MLKEM_SLICE) THEN
    ASSUME_TAC(ISPECL [mk_small_numeral(768 * k + 32); `32`; `dk:byte list`]
                      LENGTH_MLKEM_SLICE) THEN
    ABBREV_TAC(mk_eq(`ek:byte list`,de_ek k)) THEN
    ABBREV_TAC(mk_eq(`h:byte list`,de_h k)) THEN
    ABBREVS_TAC ["ek"; "h"] THEN
    ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
    ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
    MAP_EVERY (fun n -> ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
                (mk_const("X"^string_of_int n,[]))) (19--29) THEN
    ENSURES_INIT_TAC "s0"
  and finish =
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MEMACCESS_NUMERALS_TAC THEN NATIVE2_DISCHARGE_FRESH_TAC in
  setup,derive,calls,finish;;

let MLKEM_NATIVE2_DEC_SAFE_TAC k ex gmth (pdth,peth) =
  let setup,derive,calls,finish = de_safe_parts k ex gmth (pdth,peth) in
  MLKEM_SAMPLENTT_TERMINATES_TAC (api_terminates_tm k (de_rho k) true)
   (setup THEN NATIVE2_SAFE_RUN_TAC ex derive calls 0 THEN
    ON_STATE(DE_HASH_SAFE_BRANCH_TAC k) THEN
    API_BOOL_CASE_TAC `sha3_256 ek = h` THEN
    ON_STATE(NATIVE2_SAFE_RUN_TAC ex derive calls) THEN finish);;
