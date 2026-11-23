(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The noise sampling of ML-KEM, SamplePolyCBD_eta(PRF_eta(sigma, b)) of     *)
(* FIPS 203 for n consecutive nonces b, in the lanes of the x4 Keccak        *)
(* permutation, in the image of the AVX-512 version of the x86               *)
(* mlkem_native2, for the configurations used by the API functions. A copy   *)
(* of mlkem_getnoise.ml for the AVX2 version.                                *)
(* ========================================================================= *)

needs "x86/proofs/utils/mlkem_native2_avx512_noise.ml";;

(**** The function's code is that of x86/mlkem_native/asm/mlkem_getnoise.S, as
 **** x86/mlkem_native/asm_avx512/mlkem_getnoise_avx512.S assembles it. Its
 **** frame of 1672 bytes below the six saved registers has the four 200-byte
 **** lanes at the stack pointer, the four 192-byte buffers at + 800, the
 **** index and block count of each lane's polynomial at + 1568 and + 1600,
 **** and the arguments nonce0, n, n1 and eta1 at + 1632; the constants
 **** block is the seventh argument, above the return address. The call of
 **** sha3_keccak4_f1600_avx512 puts its return address below the frame, and
 **** its theorems used here allow it the 0x31f bytes below that which
 **** sha3_keccak4_f1600_alt uses in the AVX2 version (it uses none), so the
 **** stack used is within the 2527 bytes below the return address. In the
 **** proofs stackpointer is the lowest address of that, so that the lanes
 **** are at stackpointer + 807 + 200 * l and the buffers at stackpointer +
 **** 1607 + 192 * l.
 ****)

let MLKEM_GETNOISE_AVX512_EXEC =
  MLKEM_NATIVE2_AVX512_IMAGE_EXEC ["mlkem_getnoise_avx512"];;

let pc_plus name off =
  parse_term (Printf.sprintf "pc + %d" (layout name + off));;

(*** The end of the zeroing of the lanes and buffers, before vzeroupper ***)

install_layout ["mlkem_getnoise_zerodone",layout "mlkem_getnoise_end" + 46];;

(* ------------------------------------------------------------------------- *)
(* The zeroing of the lanes and buffers before the return, as one step.      *)
(* ------------------------------------------------------------------------- *)

let MLKEM_GETNOISE_AVX512_ZERO_COUNTER = prove
 (`!i. i < 12
       ==> ((~(val(word_zx(word(12 - i):int64):int32) = val(word 1:int32)) <=>
             i + 1 < 12) /\
            word_zx(word_sub (word_zx(word(12 - i):int64):int32) (word 1))
            :int64 = word(12 - (i + 1)))`,
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV)));;

let MLKEM_GETNOISE_AVX512_ZERO = prove
 (`!stackpointer pc.
     nonoverlapping (stackpointer,1568)
                    (word pc,mlkem_native2_avx512_image_size)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_native2_avx512_image_mc /\
               read RIP s = word(pc + mlkem_getnoise_end) /\
               read RSP s = stackpointer)
          (\s. read RIP s = word(pc + mlkem_getnoise_zerodone))
          (MAYCHANGE [RIP; RDI; RCX] ,, MAYCHANGE [ZMM0] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(stackpointer,1568)])`,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  ENSURES_WHILE_UP2_TAC `12` `pc + mlkem_getnoise_zero`
   (pc_plus "mlkem_getnoise_zero" 30)
   `\i s. read RDI s = word_add stackpointer (word(128 * i)) /\
          read RCX s = word(12 - i)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    X86_SIM_TAC MLKEM_GETNOISE_AVX512_EXEC (1--3) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    X86_SIM_TAC MLKEM_GETNOISE_AVX512_EXEC (1--7) THEN
    ASM_SIMP_TAC[MLKEM_GETNOISE_AVX512_ZERO_COUNTER] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; CONV_TAC WORD_RULE];
    X86_SIM_TAC MLKEM_GETNOISE_AVX512_EXEC [1]]);;

let MLKEM_GETNOISE_AVX512_ZERO_SAFE = time prove
 (`exists f_events.
     forall e stackpointer pc.
       nonoverlapping (stackpointer,1568)
                      (word pc,mlkem_native2_avx512_image_size)
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_avx512_image_mc /\
                 read RIP s = word(pc + mlkem_getnoise_end) /\
                 read RSP s = stackpointer /\
                 read events s = e)
            (\s. read RIP s = word(pc + mlkem_getnoise_zerodone) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events stackpointer pc /\
                    memaccess_inbounds e2
                     [stackpointer,1568] [stackpointer,1568]))
            (MAYCHANGE [RIP; RDI; RCX] ,, MAYCHANGE [ZMM0] ,,
             MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
             MAYCHANGE [memory :> bytes(stackpointer,1568)])`,
  REWRITE_TAC[SOME_FLAGS] THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(stackpointer:int64) (pc:num).
      APPEND (f_ev_epil stackpointer pc)
             (APPEND (ENUMERATEL 12 (\i. f_ev_loop stackpointer pc i))
                     (f_ev_prol stackpointer pc)) :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `pc:num`] THEN
  DISCH_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `12` `pc + mlkem_getnoise_zero`
   (pc_plus "mlkem_getnoise_zero" 30)
   `\i s. read RDI s = word_add stackpointer (word(128 * i)) /\
          read RCX s = word(12 - i)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_GETNOISE_AVX512_EXEC (1--3) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_GETNOISE_AVX512_EXEC (1--7) THEN
    ASM_SIMP_TAC[MLKEM_GETNOISE_AVX512_ZERO_COUNTER] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_GETNOISE_AVX512_EXEC [1] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The facts added on the way, by the offset of RIP where they are needed:   *)
(*                                                                           *)
(*  - before the store of the final bit 0x80 at byte 135 of the lane at      *)
(*    RDX, its zero bytes before it as pieces that the store does not        *)
(*    overlap, and after it the state of the lane,                           *)
(*    mlkem_noise_state seed (word(nonce0 + i)), as bytes;                   *)
(*                                                                           *)
(*  - the selection of eta for the polynomial, which is 2 either way when    *)
(*    eta1 = 2 (and n1 is not known);                                        *)
(*                                                                           *)
(*  - for eta = 3, the words of the lane at RSI before it is copied to the   *)
(*    buffer at RDX, 136 bytes after the first permutation and 56 after the  *)
(*    second, and the buffer as the PRF output after each copy.              *)
(* ------------------------------------------------------------------------- *)

let LANE_ZERO_SPLIT_TAC k gl =
  let a = find_read_fact `RDX` k gl in
  let sv = state_of k in
  let x = addr_plus a 104 in
  let th0 = asm_with_lhs (vsubst [x,`x:int64`; sv,`s:x86state`]
              `read (memory :> bytes256 x) s`) gl in
  let split th = CONJ_PAIR(CONV_RULE(READ_MEMORY_SPLIT_CONV 1 THENC
                                     DEPTH_CONV WORD_RED_CONV) th) in
  let l1,h1 = split th0 in
  let l2,h2 = split h1 in
  let l3,h3 = split h2 in
  let l4,h4 = split h3 in
  let l5,_ = split h4 in
  MAP_EVERY ASSUME_TAC [l1;l2;l3;l4;l5] gl;;

let LANE_INIT_TAC k gl =
  let a = find_read_fact `RDX` k gl in
  let sv = state_of k in
  let q = rand(concl(asm_with_lhs
            (vsubst [addr_plus a 32,`x:int64`; sv,`s:x86state`]
                    `read (memory :> bytes64 x) s`) gl)) in
  let _,ins,_ = term_match []
   `word_zx(word_or (word_zx(word_zx(word_zx (b:byte):int32):int64):int32)
                    (word 7936):int32):int64` q in
  let b = rev_assoc `b:byte` ins in
  (MP_TAC(SPECL [a; `seed:byte list`; b; sv] MLKEM_NOISE_LANE_X86) THEN
   ANTS_TAC THENL
    [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
     CONV_TAC(DEPTH_CONV NUM_EXP_CONV) THEN ASM_REWRITE_TAC[];
     REWRITE_TAC[GSYM WORD_ADD; BYTE_OF_WORD64; READ_MEMORY_WBYTES_1600] THEN
     DISCH_TAC]) gl;;

let LANE_LOAD_TAC offs256 offs128 offs64 k gl =
  let a = find_read_fact `RSI` k gl in
  let sv = state_of k in
  let th200 = bytes_fact a 200 k gl in
  let x = rand(concl th200) in
  let mk lemma len off =
    let th = SPECL [a; `200`; x; mk_small_numeral off; sv] lemma in
    let th' = MP th (CONJ th200 (ARITH_RULE(mk_binop `(<=):num->num->bool`
               (mk_binop `(+):num->num->num` (mk_small_numeral off)
                 (mk_small_numeral len)) `200`))) in
    CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THENC
              RAND_CONV(NUM_REDUCE_CONV)) (REWRITE_RULE[WORD_ADD_0] th') in
  let ths = map (mk READ_MEMORY_BYTES256_OF_NUM 32) offs256 @
            map (mk READ_MEMORY_BYTES128_OF_NUM 16) offs128 @
            map (mk READ_MEMORY_BYTES64_OF_NUM 8) offs64 in
  MAP_EVERY (ASSUME_TAC o REWRITE_RULE[DIV_1]) ths gl;;

let BUF1_TAC k gl =
  let buf = find_read_fact `RDX` k gl in
  let x = rand(concl(bytes_fact (find_read_fact `RSI` k gl) 200 k gl)) in
  let sv = state_of k in
  (MP_TAC(SPECL [buf; x; sv] READ_MEMORY_BYTES_136_OF_PIECES_X86) THEN
   ANTS_TAC THENL
    [CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
     CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
     REWRITE_TAC[DIV_1; WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
     CONV_TAC NUM_REDUCE_CONV;
     DISCH_TAC]) gl;;

(*** The facts in state k about memory at addresses based at a, with their
 *** numerals reduced, as rewrites
 ***)

let MEM_FACTS_REDUCED_TAC a k (asl,w) =
  let sv = state_of k in
  let ok th = let c = concl th in
    is_eq c && is_comb(lhand c) && rand(lhand c) = sv &&
    can (find_term ((=) a)) (lhand c) in
  REWRITE_TAC (map (CONV_RULE NUM_REDUCE_CONV o snd)
                   (filter (ok o snd) asl)) (asl,w);;

let BUF2_TAC k gl =
  let buf = find_read_fact `RDX` k gl in
  let sv = state_of k in
  let b = rand(rand(rand(lhand(rand(concl(bytes_fact buf 136 k gl)))))) in
  (MP_TAC(SPECL [buf; `seed:byte list`; b; sv]
     READ_MEMORY_BYTES_192_PRF_3_X86) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     REWRITE_TAC[WORD_ZX_128_256] THEN
     MEM_FACTS_REDUCED_TAC `stackpointer:int64` k THEN
     REWRITE_TAC[WORD_ZX_128_256];
     DISCH_TAC]) gl;;

let getnoise_derive =
  [layout "mlkem_getnoise_assigned" - 10, LANE_ZERO_SPLIT_TAC;
   layout "mlkem_getnoise_assigned" - 3, LANE_INIT_TAC;
   layout "mlkem_getnoise_postloop" + 39, SIMP_REG_TAC `RCX` [COND_ID];
   layout "mlkem_getnoise_eta3" + 26, LANE_LOAD_TAC [0;32;64;96] [] [128];
   layout "mlkem_getnoise_eta3" + 78, BUF1_TAC;
   layout "mlkem_getnoise_eta3_second", LANE_LOAD_TAC [0] [32] [48];
   layout "mlkem_getnoise_eta3_second" + 36, BUF2_TAC];;

let getnoise_calls =
  [layout "sha3_keccak4_f1600_avx512",
   KECCAK4_CALL_TAC MLKEM_GETNOISE_AVX512_EXEC;
   layout "sha3_keccak_f1600_avx512",
   KECCAK1_CALL_TAC MLKEM_GETNOISE_AVX512_EXEC;
   layout "mlkem_cbd2", CBD2_CALL_TAC MLKEM_GETNOISE_AVX512_EXEC;
   layout "mlkem_cbd3", CBD3_CALL_TAC MLKEM_GETNOISE_AVX512_EXEC;
   layout "mlkem_getnoise_end",
   (fun k -> X86_SUBROUTINE_SIM_TAC
     (mlkem_native2_avx512_image_mc,MLKEM_GETNOISE_AVX512_EXEC,0,
      mlkem_native2_avx512_image_mc,
      MLKEM_GETNOISE_AVX512_ZERO)
     [`word_add (read RSP s) (word 0)`; `pc:num`] (k+1))];;

(* ------------------------------------------------------------------------- *)
(* Correctness for the configurations (n,n1,eta1) used: eta1 = 2 for n = 4,  *)
(* 7, 8 or 9 polynomials (any n1, eta being 2 for all), and eta1 = 3 for n = *)
(* 4 with n1 = 4 or n = 5 with n1 = 2. The result is the coefficients of     *)
(* SamplePolyCBD_eta(PRF_eta(seed, word(nonce0 + i))) with eta = eta1 for i  *)
(* < n1 and 2 otherwise. The constants block c is the seventh argument, on   *)
(* the stack; it must not overlap the code of sha3_keccak4_f1600_avx512, as  *)
(* that function's correctness theorem requires, which holds when it is the  *)
(* constants block of the image.                                             *)
(* ------------------------------------------------------------------------- *)

let MLKEM_GETNOISE_AVX512_INSTANCE_TAC =
  REWRITE_TAC[COND_ID] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL;
              NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[WORDLIST_FROM_MEMORY_ROUND_CONSTANTS;
              WORDLIST_FROM_MEMORY_RHO8; WORDLIST_FROM_MEMORY_RHO56] THEN
  REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  MAP_EVERY (fun r -> ENSURES_PRESERVED_TAC
                (String.lowercase_ascii(fst(dest_const r))^"_init") r)
   [`RBX`; `RBP`; `R12`; `R13`; `R14`; `R15`] THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`sigma:int64`; `32`; `num_of_bytelist(seed:byte list)`; `0`;
                `s0:x86state`] READ_MEMORY_BYTES256_OF_NUM) THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 + 32 <= 32`; WORD_ADD_0; MULT_CLAUSES; EXP;
                  DIV_1] THEN
  DISCH_TAC THEN
  NATIVE2_RUN_TAC MLKEM_GETNOISE_AVX512_EXEC
    getnoise_derive getnoise_calls 0 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;;

let MLKEM_GETNOISE_AVX512_SUBROUTINE_CORRECT = time prove
 (`!r sigma (seed:byte list) nonce0 n n1 eta1 c pc stackpointer returnaddress.
     (eta1 = 2 /\ n = 4 \/ eta1 = 2 /\ n = 7 \/ eta1 = 2 /\ n = 8 \/
      eta1 = 2 /\ n = 9 \/ eta1 = 3 /\ n = 4 /\ n1 = 4 \/
      eta1 = 3 /\ n = 5 /\ n1 = 2) /\
     LENGTH seed = 32 /\
     ALL (nonoverlapping (word_sub stackpointer (word 2527),2543))
         [(word pc,mlkem_native2_avx512_image_size); (sigma,32); (c,256)] /\
     ALL (nonoverlapping (r,512 * n))
         [(word pc,mlkem_native2_avx512_image_size); (sigma,32); (c,256);
          (word_sub stackpointer (word 2527),2543)] /\
     nonoverlapping (c,256)
       (word(pc + sha3_keccak4_f1600_avx512),sha3_keccak4_f1600_avx512_size)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_native2_avx512_image_mc /\
               read RIP s = word(pc + mlkem_getnoise_avx512) /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [r; sigma; word nonce0; word n; word n1;
                            word eta1] s /\
               read (memory :> bytes64 (word_add stackpointer (word 8))) s =
               c /\
               read (memory :> bytes(sigma,32)) s = num_of_bytelist seed /\
               wordlist_from_memory(c,24) s = round_constants /\
               wordlist_from_memory(word_add c (word 192),4) s =
               rho8_constant /\
               wordlist_from_memory(word_add c (word 224),4) s =
               rho56_constant)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               !i j. i < n /\ j < 256
                     ==> read(memory :> bytes16(word_add r
                                                  (word(512 * i + 2 * j)))) s =
                         iword(mlkem_cbd_coeff (if i < n1 then eta1 else 2)
                                (mlkem_prf (if i < n1 then eta1 else 2) seed
                                           (word(nonce0 + i))) j))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE
            [memory :> bytes(r,512 * n);
             memory :> bytes(word_sub stackpointer (word 2527),2527)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `sigma:int64`; `seed:byte list`; `nonce0:num`; `n:num`;
    `n1:num`; `eta1:num`; `c:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 2527 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[IMP_CONJ] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN
    SUBST1_TAC)) THEN
  MLKEM_GETNOISE_AVX512_INSTANCE_TAC);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety, for the same configurations: the events  *)
(* depend only on the addresses and on n and eta1.                           *)
(* ------------------------------------------------------------------------- *)

let getnoise_safe_vars =
  [`r:int64`; `sigma:int64`; `c:int64`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`];;

(*** A call by the image-level theorem with the given label, of the x1
 *** permutation or the zeroing (offset 0 in the image)
 ***)

let IMAGE_SAFE_CALL_TAC label ilist k =
  REMOVE_THEN label (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native2_avx512_image_mc,MLKEM_GETNOISE_AVX512_EXEC,0,
       mlkem_native2_avx512_image_mc,th)
      ilist (k+1) THENL
     [EXISTS_E2_TAC (ref getnoise_safe_vars); LABEL_TAC label th]);;

let getnoise_safe_calls =
  let call = NATIVE2_SAFE_CALL_TAC mlkem_native2_avx512_image_mc
               MLKEM_GETNOISE_AVX512_EXEC getnoise_safe_vars in
  [layout "sha3_keccak4_f1600_avx512",
   call "H_K4"
    (layout "sha3_keccak4_f1600_avx512",sha3_keccak4_f1600_avx512_mc)
    [`read RSI s`; `read RDI s`; `read RDX s`; `read RCX s`];
   layout "sha3_keccak_f1600_avx512",
   IMAGE_SAFE_CALL_TAC "H_K1"
    ([`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `pc:num`] @
     return_args);
   layout "mlkem_cbd2",
   call "H_CBD2" (layout "mlkem_cbd2",mlkem_cbd2_mc)
    [`read RDI s`; `read RSI s`];
   layout "mlkem_cbd3",
   call "H_CBD3" (layout "mlkem_cbd3",mlkem_cbd3_mc)
    [`read RDI s`; `read RSI s`];
   layout "mlkem_getnoise_end",
   IMAGE_SAFE_CALL_TAC "H_ZERO"
    [`e:(uarch_event)list`; `word_add (read RSP s) (word 0)`; `pc:num`]];;

let MLKEM_GETNOISE_AVX512_INSTANCE_SAFE_TAC =
  REWRITE_TAC[COND_ID; ARITH_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL;
              NONOVERLAPPING_CLAUSES] THEN
  REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  MAP_EVERY (fun r -> ENSURES_PRESERVED_TAC
                (String.lowercase_ascii(fst(dest_const r))^"_init") r)
   [`RBX`; `RBP`; `R12`; `R13`; `R14`; `R15`] THEN
  ENSURES_INIT_TAC "s0" THEN
  NATIVE2_SAFE_RUN_TAC MLKEM_GETNOISE_AVX512_EXEC
   [layout "mlkem_getnoise_postloop" + 39, SIMP_REG_TAC `RCX` [COND_ID]]
   getnoise_safe_calls 0 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MEMACCESS_NUMERALS_TAC THEN NATIVE2_DISCHARGE_SAFETY_TAC;;

let MLKEM_GETNOISE_AVX512_SUBROUTINE_SAFE = time prove
 (`exists f_events.
     forall e r sigma nonce0 n n1 eta1 c pc stackpointer returnaddress.
       (eta1 = 2 /\ n = 4 \/ eta1 = 2 /\ n = 7 \/ eta1 = 2 /\ n = 8 \/
        eta1 = 2 /\ n = 9 \/ eta1 = 3 /\ n = 4 /\ n1 = 4 \/
        eta1 = 3 /\ n = 5 /\ n1 = 2) /\
       ALL (nonoverlapping (word_sub stackpointer (word 2527),2543))
           [(word pc,mlkem_native2_avx512_image_size); (sigma,32); (c,256)] /\
       ALL (nonoverlapping (r,512 * n))
           [(word pc,mlkem_native2_avx512_image_size); (sigma,32); (c,256);
            (word_sub stackpointer (word 2527),2543)] /\
       nonoverlapping (c,256)
         (word(pc + sha3_keccak4_f1600_avx512),sha3_keccak4_f1600_avx512_size)
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_avx512_image_mc /\
                 read RIP s = word(pc + mlkem_getnoise_avx512) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [r; sigma; word nonce0; word n; word n1;
                              word eta1] s /\
                 read (memory :> bytes64 (word_add stackpointer (word 8))) s =
                 c /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events r sigma n eta1 c pc
                                  (word_sub stackpointer (word 2527))
                                  returnaddress /\
                    memaccess_inbounds e2
                     [r,512 * n; sigma,32; c,256;
                      word_sub stackpointer (word 2527),2543]
                     [r,512 * n; word_sub stackpointer (word 2527),2527]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(r,512 * n);
                        memory :> bytes(word_sub stackpointer (word 2527),
                                        2527)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
     SHA3_KECCAK4_F1600_AVX512_SUBROUTINE_SAFE_ALTFORM "H_K4" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
     SHA3_KECCAK_F1600_AVX512_IMAGE_SAFE "H_K1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
     MLKEM_CBD2_SUBROUTINE_SAFE_FRAMED "H_CBD2" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
     MLKEM_CBD3_SUBROUTINE_SAFE_FRAMED "H_CBD3" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC MLKEM_GETNOISE_AVX512_ZERO_SAFE "H_ZERO" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(r:int64) (sigma:int64) (n:num) (eta1:num) (c:int64) (pc:num)
     (stackpointer:int64) (returnaddress:int64).
      if eta1 = 2 then
        if n = 4 then f_ev_24 r sigma c pc stackpointer returnaddress
        else if n = 7 then f_ev_27 r sigma c pc stackpointer returnaddress
        else if n = 8 then f_ev_28 r sigma c pc stackpointer returnaddress
        else f_ev_29 r sigma c pc stackpointer returnaddress
      else if n = 4 then f_ev_34 r sigma c pc stackpointer returnaddress
      else f_ev_35 r sigma c pc stackpointer returnaddress
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `r:int64`; `sigma:int64`; `nonce0:num`; `n:num`;
    `n1:num`; `eta1:num`; `c:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 2527 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[IMP_CONJ] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (REPEAT_TCL CONJUNCTS_THEN
    SUBST1_TAC)) THEN
  MLKEM_GETNOISE_AVX512_INSTANCE_SAFE_TAC);;
