(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of key generation, encapsulation and decapsulation   *)
(* in the x86 mlkem_native2 (x86/proofs/mlkem512.ml, mlkem768.ml and         *)
(* mlkem1024.ml): the order of the coefficients of the x86 NTT domain, the   *)
(* frames of the functions, the kernels and the tables of the constants      *)
(* block in the forms the callers take them, tactics for the steps of the    *)
(* functions in the image (the calls of the kernels as single steps with     *)
(* their results as ghost functions for the coefficients, and the loops as   *)
(* lemmas), and the proofs for a parameter set from the results of K-PKE in  *)
(* utils/mlkem_native2_kpke.ml. As arm/proofs/utils/mlkem_native2_kem.ml     *)
(* for AArch64.                                                              *)
(* ========================================================================= *)

needs "x86/proofs/utils/mlkem_native2_kpke.ml";;
needs "x86/proofs/utils/mlkem_native2_api.ml";;
needs "x86/proofs/utils/mlkem_bytes.ml";;
needs "x86/proofs/mlkem_hash_g.ml";;
needs "x86/proofs/mlkem_gen_matrix.ml";;
needs "x86/proofs/mlkem_ntt.ml";;
needs "x86/proofs/mlkem_intt.ml";;
needs "x86/proofs/mlkem_mulcache_compute.ml";;
needs "x86/proofs/mlkem_basemul_k2.ml";;
needs "x86/proofs/mlkem_basemul_k3.ml";;
needs "x86/proofs/mlkem_basemul_k4.ml";;
needs "x86/proofs/mlkem_tomont.ml";;
needs "x86/proofs/mlkem_reduce.ml";;
needs "x86/proofs/mlkem_add_reduce.ml";;
needs "x86/proofs/mlkem_sub_reduce.ml";;
needs "x86/proofs/mlkem_tobytes.ml";;
needs "x86/proofs/mlkem_frombytes.ml";;
needs "x86/proofs/mlkem_frommsg.ml";;
needs "x86/proofs/mlkem_tomsg.ml";;
needs "x86/proofs/mlkem_compress_d4_x86.ml";;
needs "x86/proofs/mlkem_compress_d5_x86.ml";;
needs "x86/proofs/mlkem_compress_d10_x86.ml";;
needs "x86/proofs/mlkem_compress_d11_x86.ml";;
needs "x86/proofs/mlkem_decompress_d4_x86.ml";;
needs "x86/proofs/mlkem_decompress_d5_x86.ml";;
needs "x86/proofs/mlkem_decompress_d10_x86.ml";;
needs "x86/proofs/mlkem_decompress_d11_x86.ml";;

(* ------------------------------------------------------------------------- *)
(* The order of the coefficients in the NTT domain of the x86 kernels:       *)
(* coefficient k in memory is coefficient avx_unorder k of FIPS 203's        *)
(* order, so FIPS coefficient i is at avx_order i, for the NTT (forward and  *)
(* inverse), the matrix from mlkem_gen_matrix (mlkem_unpack), and the codecs *)
(* mlkem_frombytes and mlkem_tobytes.                                        *)
(* ------------------------------------------------------------------------- *)

let AVX_ORDER_UNORDER = prove
 (`!i. i < 256
       ==> avx_unorder(avx_order i) = i /\ avx_order(avx_unorder i) = i /\
           avx_order i < 256 /\ avx_unorder i < 256`,
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[avx_order; avx_unorder] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

let AVX2_FORWARD_NTT_UNORDER = prove
 (`!f k. k < 256 ==> avx2_forward_ntt f k = forward_ntt f (avx_unorder k)`,
  GEN_TAC THEN CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[avx2_forward_ntt; forward_ntt; avx_unorder] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[AVX2_NTT_ORDER_CLAUSES; BITREVERSE7_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let AVX_ORDER_INVERSE_INDEX = prove
 (`!j b. j < 128 /\ b < 2
         ==> avx_order(2 * bitreverse7 j + b) =
             avx2_ntt_order' j DIV 16 * 32 + b * 16 +
             avx2_ntt_order' j MOD 16`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `b = 0 \/ b = 1` MP_TAC THENL
   [ASM_ARITH_TAC; DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC)] THEN
  UNDISCH_TAC `j < 128` THEN SPEC_TAC(`j:num`,`j:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[AVX2_NTT_ORDER_CLAUSES'; BITREVERSE7_CLAUSES] THEN
  REWRITE_TAC[avx_order] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let AVX2_INVERSE_NTT_ORDER = prove
 (`!f k. avx2_inverse_ntt f k = inverse_ntt (\i. f(avx_order i)) k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[avx2_inverse_ntt; inverse_ntt] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `j:num` THEN
  REWRITE_TAC[IN_NUMSEG] THEN DISCH_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC AVX_ORDER_INVERSE_INDEX THEN
  ASM_REWRITE_TAC[ARITH_RULE `j < 128 <=> j <= 127`] THEN ARITH_TAC);;

(*** The mulcache of the x86 kernels: for pair p of FIPS 203's order (the
 *** coefficients 2p and 2p + 1, X^2 - zeta^(2 bitreverse7 p + 1)), entry
 *** mcix p of mlkem_mulcache_compute_x86 has the coefficient 2p + 1 times
 *** the zeta of the even pair p - p MOD 2, so minus that of p when p is odd
 *** (the basemul subtracts it then)
 ***)

let avx2_mcix = new_definition
 `avx2_mcix p = 64 * (p DIV 64) + 16 * (p MOD 4) + (p MOD 64) DIV 4`;;

let INT_REM_MUL_CONG = prove
 (`!x a c. (a == c) (mod &3329) ==> ((x * a) rem &3329 == x * c) (mod &3329)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INT_CONG_LREM] THEN
  ASM_SIMP_TAC[INT_CONG_LMUL]);;

let AVX2_MULCACHE_PAIR = prove
 (`!f p. p < 128
         ==> (avx2_mulcache f (avx2_mcix p) ==
              f(avx_order(2 * p + 1)) *
              ((if EVEN p then &1 else -- &1) *
               &17 pow (2 * bitreverse7 p + 1))) (mod &3329)`,
  GEN_TAC THEN CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[avx2_mulcache; avx2_mcix; avx_order] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[BITREVERSE7_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[COND_CLAUSES] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC INT_REM_MUL_CONG THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The frames of the API functions (the enter macro): push rbp; mov rbp,rsp; *)
(* push rbx, r12-r15; sub rsp,size; and rsp,-32. With the stack region of    *)
(* the statement at stackpointer, N bytes, below the return address, the     *)
(* frame base fb is stackpointer + d, 32-byte aligned, for some d with       *)
(* d <= m <= d + 31 where m = N - 48 - size.                                 *)
(* ------------------------------------------------------------------------- *)

let WORD_AND_NOT31 = WORD_BLAST
 `word_and (x:int64) (word 18446744073709551584) =
  word_sub x (word_and x (word 31))`;;

let ALIGNED_WORD_AND_NOT31 = prove
 (`!x:int64. aligned 32 (word_and x (word 18446744073709551584))`,
  GEN_TAC THEN REWRITE_TAC[aligned; DIMINDEX_64; DIVIDES_MOD] THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`word_and x (word 18446744073709551584):int64`; `5`]
    VAL_WORD_AND_MASK_WORD) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[VAL_EQ_0] THEN CONV_TAC WORD_BLAST);;

let API_ALIGN_FRAME = prove
 (`!stk:int64 m.
        31 <= m
        ==> ?d. word_and (word_add stk (word m)) (word 18446744073709551584) =
                word_add stk (word d) /\
                d <= m /\ m <= d + 31 /\
                aligned 32 (word_add stk (word d))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `x:int64 = word_add stk (word m)` THEN
  EXISTS_TAC `m - val(word_and x (word 31):int64)` THEN
  MP_TAC(ISPECL [`x:int64`; `31`] (CONJUNCT1 VAL_WORD_AND_WORD_LE)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `word_add stk (word(m - val(word_and x (word 31):int64))):int64 =
    word_and x (word 18446744073709551584)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[WORD_SUB; ARITH_RULE `r <= 31 /\ 31 <= m ==> r <= m`] THEN
    REWRITE_TAC[WORD_VAL; WORD_AND_NOT31] THEN EXPAND_TAC "x" THEN
    CONV_TAC WORD_RULE;
    REWRITE_TAC[ALIGNED_WORD_AND_NOT31] THEN ASM_ARITH_TAC]);;

(*** The frame and the callees' stack, cs bytes below fb, are in the stack
 *** region away from the six saved registers and the return address
 ***)

let API_FRAME_NONOVERLAPPING = prove
 (`!stk d cs size N (r:int64) n.
        cs <= d /\ d + size + 48 <= N /\
        nonoverlapping (stk,N + 8) (r,n)
        ==> nonoverlapping
             (word_sub (word_add stk (word d)) (word cs),cs + size) (r,n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NONOVERLAPPING_SUBREGIONS THEN
  MAP_EVERY EXISTS_TAC [`stk:int64`; `N + 8`; `r:int64`; `n:num`] THEN
  ASM_REWRITE_TAC[CONTAINED] THEN
  CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THENL
   [EXISTS_TAC `(d - cs) + i` THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[WORD_ADD; WORD_SUB] THEN CONV_TAC WORD_RULE;
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]]);;

let API_FRAME_SAVED_NONOVERLAPPING = prove
 (`!(stk:int64) d cs size N.
        cs <= d /\ d + size + 48 <= N /\ N < 2 EXP 63
        ==> nonoverlapping
             (word_sub (word_add stk (word d)) (word cs),cs + size)
             (word_add stk (word(N - 48)),56)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_sub (word_add stk (word d)) (word cs):int64 =
                word_add stk (word(d - cs))` SUBST1_TAC THENL
   [ASM_SIMP_TAC[WORD_SUB] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; nonoverlapping; DIMINDEX_64] THEN
  MATCH_MP_TAC NONOVERLAPPING_MODULO_64_OFFSET_BOTH THEN
  DISJ1_TAC THEN UNDISCH_TAC `N < 2 EXP 63` THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The kernels in the forms the API proofs use: for the codecs the inputs    *)
(* and outputs as numbers and coefficient functions (not word lists), and    *)
(* for the NTT kernels the tables as bytes, which the simulation keeps.      *)
(* ------------------------------------------------------------------------- *)

let ENSURES_PREPOST_RULE = prove
 (`!P P' (C:A->A->bool) Q Q'.
     ensures step P Q C
     ==> (!s. P' s ==> P s) /\ (!s. Q s ==> Q' s) ==> ensures step P' Q' C`,
  MESON_TAC[ENSURES_PREPOSTCONDITION_THM]);;

let READ_BYTES_EQ_BOUND = prove
 (`!a k n s:x86state.
        read (memory :> bytes(a,k)) s = n ==> n < 2 EXP (8 * k)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND]);;

let READ_BYTES16_OF_WORDLIST = prove
 (`!r (l:int16 list) s:x86state.
     read (memory :> bytes(r,2 * LENGTH l)) s = num_of_wordlist l
     ==> !i. i < LENGTH l
             ==> read (memory :> bytes16(word_add r (word(2 * i)))) s =
                 EL i l`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC WORDLIST_FROM_MEMORY_BYTES16 THEN
  MP_TAC(ISPECL [`r:int64`; `LENGTH(l:int16 list)`;
                 `2 * LENGTH(l:int16 list)`; `l:int16 list`; `s:x86state`]
    WORDLIST_FROM_MEMORY_EQ_ALT) THEN
  REWRITE_TAC[DIMINDEX_16] THEN ANTS_TAC THENL [ARITH_TAC; ASM_SIMP_TAC[]]);;

(*** decompress_d: the 32 * d bytes at a as the number n, the 256 results
 *** as the FIPS 203 formula
 ***)

let api_decompress_tm d tlen =
  let n = string_of_int in
  parse_term(Printf.sprintf
   "!r a data n pc stackpointer returnaddress.
      aligned 32 r /\\ aligned 32 data /\\
      ALL (nonoverlapping (r, 512))
          [(word pc, LENGTH mlkem_decompress_d%d_x86_mc); (a, %d);
           (data, %d); (stackpointer, 8)]
      ==> ensures x86
           (\\s. bytes_loaded s (word pc) mlkem_decompress_d%d_x86_mc /\\
                read RIP s = word pc /\\
                read RSP s = stackpointer /\\
                read (memory :> bytes64 stackpointer) s = returnaddress /\\
                C_ARGUMENTS [r; a; data] s /\\
                read (memory :> bytes(data, %d)) s =
                num_of_wordlist ((MAP iword decompress_d%d_data):byte list) /\\
                read (memory :> bytes(a, %d)) s = n)
           (\\s. read RIP s = returnaddress /\\
                read RSP s = word_add stackpointer (word 8) /\\
                !i. i < 256
                    ==> read (memory :> bytes16(word_add r (word(2 * i)))) s =
                        word((3329 * (n DIV 2 EXP (%d * i)) MOD 2 EXP %d + %s)
                             DIV %s))
           (MAYCHANGE [RSP] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(r, 512)])"
   d (32 * d) tlen d tlen d (32 * d) d d (n(1 lsl (d - 1))) (n(1 lsl d)));;

let API_DECOMPRESS_TAC d th =
  let l = parse_term(Printf.sprintf "wordlist_of_num 256 n:(%d word)list" d)
  and ml = parse_term(Printf.sprintf
             "MAP decompress_d%d (wordlist_of_num 256 n:(%d word)list)" d d) in
  let defn = match d with
      4 -> decompress_d4 | 5 -> decompress_d5
    | 10 -> decompress_d10 | _ -> decompress_d11 in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`r:int64`; `a:int64`; `data:int64`; l; `pc:num`;
                `stackpointer:int64`; `returnaddress:int64`] th) THEN
  ASM_REWRITE_TAC[LENGTH_WORDLIST_OF_NUM] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_RULE) THEN
  CONJ_TAC THEN X_GEN_TAC `s:x86state` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP READ_BYTES_EQ_BOUND o
                check (fun th -> rand(concl th) = `n:num`)) THEN
    DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC NUM_OF_WORDLIST_OF_NUM_EQ_SELF THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
    POP_ASSUM MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    MP_TAC(ISPECL [`r:int64`; ml; `s:x86state`] READ_BYTES16_OF_WORDLIST) THEN
    REWRITE_TAC[LENGTH_MAP; LENGTH_WORDLIST_OF_NUM] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[th; EL_MAP; LENGTH_WORDLIST_OF_NUM;
                   EL_WORDLIST_OF_NUM]) THEN
    REWRITE_TAC[defn; VAL_WORD] THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN REWRITE_TAC[MULT_SYM]];;

let API_DECOMPRESS_D4 = prove
 (api_decompress_tm 4 32,
  API_DECOMPRESS_TAC 4 MLKEM_DECOMPRESS_D4_X86_SUBROUTINE_CORRECT);;

let API_DECOMPRESS_D5 = prove
 (api_decompress_tm 5 96,
  API_DECOMPRESS_TAC 5 MLKEM_DECOMPRESS_D5_X86_SUBROUTINE_CORRECT);;

let API_DECOMPRESS_D10 = prove
 (api_decompress_tm 10 32,
  API_DECOMPRESS_TAC 10 MLKEM_DECOMPRESS_D10_X86_SUBROUTINE_CORRECT);;

let API_DECOMPRESS_D11 = prove
 (api_decompress_tm 11 128,
  API_DECOMPRESS_TAC 11 MLKEM_DECOMPRESS_D11_X86_SUBROUTINE_CORRECT);;

(*** frombytes: the 384 bytes at a as the number n, coefficient i of the
 *** result its 12-bit field avx_unorder i
 ***)

let LENGTH_UNPERMUTE_LIST = prove
 (`!l:(N word)list. LENGTH(unpermute_list l) = 256`,
  REWRITE_TAC[unpermute_list; LENGTH_LIST_OF_SEQ]);;

let API_FROMBYTES = prove
 (`!r a n pc stackpointer returnaddress.
        aligned 32 r /\
        nonoverlapping (word pc, LENGTH mlkem_frombytes_mc) (a, 384) /\
        nonoverlapping (word pc, LENGTH mlkem_frombytes_mc) (r, 512) /\
        nonoverlapping (a, 384) (r, 512) /\
        nonoverlapping (stackpointer, 8) (r, 512)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_frombytes_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a, 384)) s = n)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((n DIV 2 EXP (12 * avx_unorder i)) MOD
                               2 EXP 12))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [RSP] ,, MAYCHANGE [memory :> bytes(r, 512)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`r:int64`; `a:int64`; `wordlist_of_num 256 n:(12 word)list`;
                `pc:num`] MLKEM_FROMBYTES_SUBROUTINE_CORRECT) THEN
  ASM_REWRITE_TAC[LENGTH_WORDLIST_OF_NUM] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_RULE) THEN
  CONJ_TAC THEN X_GEN_TAC `s:x86state` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP READ_BYTES_EQ_BOUND o
                check (fun th -> rand(concl th) = `n:num`)) THEN
    DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC NUM_OF_WORDLIST_OF_NUM_EQ_SELF THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
    POP_ASSUM MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    MP_TAC(ISPECL [`r:int64`;
     `MAP word_zx (unpermute_list (wordlist_of_num 256 n:(12 word)list))
      :int16 list`; `s:x86state`] READ_BYTES16_OF_WORDLIST) THEN
    REWRITE_TAC[LENGTH_MAP; LENGTH_UNPERMUTE_LIST] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[th; EL_MAP; LENGTH_UNPERMUTE_LIST]) THEN
    ASM_SIMP_TAC[unpermute_list; EL_LIST_OF_SEQ] THEN
    ASM_SIMP_TAC[EL_WORDLIST_OF_NUM; AVX_ORDER_UNORDER] THEN
    REWRITE_TAC[word_zx; VAL_WORD] THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN REWRITE_TAC[]]);;

(*** tobytes: the coefficients x of the polynomial at a (all < q), encoded
 *** in the order of FIPS 203: coefficient i is x(avx_order i)
 ***)

let API_TOBYTES = prove
 (`!r a (x:num->int16) pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc, LENGTH mlkem_tobytes_mc) (a, 512) /\
        nonoverlapping (word pc, LENGTH mlkem_tobytes_mc) (r, 384) /\
        nonoverlapping (a, 512) (r, 384) /\
        nonoverlapping (stackpointer, 8) (r, 512)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_tobytes_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r, 384)) s =
                       num_of_wordlist
                        (MAP (word_zx:int16->12 word)
                             (list_of_seq (\i. x(avx_order i)) 256))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r, 384)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`r:int64`; `a:int64`; `list_of_seq (x:num->int16) 256`;
                `pc:num`] MLKEM_TOBYTES_SUBROUTINE_CORRECT) THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_RULE) THEN
  CONJ_TAC THEN X_GEN_TAC `s:x86state` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP READ_MEMORY_BYTES16_LIST_OF_SEQ) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[];
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[EL_LIST_OF_SEQ; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[permute_list] THEN MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC EL_LIST_OF_SEQ THEN ASM_SIMP_TAC[AVX_ORDER_UNORDER]]);;

(*** The NTT kernels with the table qdata as bytes ***)

let WORDLIST_FROM_MEMORY_QDATA = prove
 (`!c s:x86state.
        wordlist_from_memory(c,624) s = MAP (iword:int->int16) qdata_full <=>
        read (memory :> bytes(c,1248)) s =
        num_of_wordlist(MAP (iword:int->int16) qdata_full)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`c:int64`; `624`; `1248`;
                 `MAP (iword:int->int16) qdata_full`; `s:x86state`]
    WORDLIST_FROM_MEMORY_EQ_ALT) THEN
  REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[LENGTH_MAP; qdata_full; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let API_NTT = REWRITE_RULE[WORDLIST_FROM_MEMORY_QDATA]
  MLKEM_NTT_SUBROUTINE_CORRECT;;

let API_INTT = REWRITE_RULE[WORDLIST_FROM_MEMORY_QDATA]
  MLKEM_INTT_SUBROUTINE_CORRECT;;

let API_MULCACHE = REWRITE_RULE[WORDLIST_FROM_MEMORY_QDATA]
  MLKEM_MULCACHE_COMPUTE_SUBROUTINE_CORRECT;;

let MLKEM_NATIVE2_QDATA = prove
 (`!s pc. bytes_loaded s (word pc) mlkem_native2_image_mc
          ==> read (memory :> bytes(word(pc + 62208),1248)) s =
              num_of_wordlist(MAP (iword:int->int16) qdata_full)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP MLKEM_NATIVE2_QDATA_TABLE) THEN
  REWRITE_TAC[MLKEM_NATIVE2_QDATA_TABLE_VALUE]);;

(*** compress_d: the coefficients x of the polynomial at a, all < q, as the
 *** 32 * d bytes at r of their d-bit compressions, as in FIPS 203
 ***)

let DIV_2_ODD = prove
 (`!a b. (2 * a + 1) DIV (2 * b) = a DIV b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM DIV_DIV] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let IVAL_LT_3329 = prove
 (`!x:int16. val x < 3329 ==> &0 <= ival x /\ ival x <= &3328`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) IVAL_EQ_VAL o
    find_term (fun t -> try fst(dest_const(rator t)) = "ival"
                        with Failure _ -> false) o snd) THEN
  REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC]) THEN
  REWRITE_TAC[INT_POS; INT_OF_NUM_LE] THEN ASM_ARITH_TAC);;

let api_compress_tm d tlen =
  Printf.sprintf
   "!r a (x:num->int16) data pc stackpointer returnaddress.
      aligned 32 a /\\ aligned 32 data /\\
      (!i. i < 256 ==> val(x i) < 3329) /\\
      ALL (nonoverlapping (r, %d))
          [(word pc, LENGTH mlkem_compress_d%d_x86_mc); (a, 512);
           (data, %d); (stackpointer, 8)]
      ==> ensures x86
           (\\s. bytes_loaded s (word pc) mlkem_compress_d%d_x86_mc /\\
                read RIP s = word pc /\\
                read RSP s = stackpointer /\\
                read (memory :> bytes64 stackpointer) s = returnaddress /\\
                C_ARGUMENTS [r; a; data] s /\\
                read (memory :> bytes(data, %d)) s =
                num_of_wordlist ((MAP iword compress_d%d_data):byte list) /\\
                !i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i)
           (\\s. read RIP s = returnaddress /\\
                read RSP s = word_add stackpointer (word 8) /\\
                read (memory :> bytes(r, %d)) s =
                nsum {i | i < 256}
                     (\\i. ((%d * val(x i) + 3329) DIV 6658) MOD %d *
                          2 EXP (%d * i)))
           (MAYCHANGE [RSP] ,,
            MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(r, %d)])"
   (32 * d) d tlen d tlen d (32 * d) (1 lsl (d + 1)) (1 lsl d) d (32 * d)
  |> parse_term;;

let api_compress_round d =
  let tm = parse_term(Printf.sprintf
    "!v. (%d * v + 3329) DIV 6658 = (v * %d + 1664) DIV 3329"
    (1 lsl (d + 1)) (1 lsl d))
  and ath = ARITH_RULE(parse_term(Printf.sprintf
    "%d * v + 3329 = 2 * (v * %d + 1664) + 1 /\\ 6658 = 2 * 3329"
    (1 lsl (d + 1)) (1 lsl d))) in
  prove(tm, REWRITE_TAC[ath; DIV_2_ODD]);;

let API_COMPRESS_TAC d th =
  let defn = match d with
      4 -> compress_d4 | 5 -> compress_d5
    | 10 -> compress_d10 | _ -> compress_d11 in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`r:int64`; `a:int64`; `data:int64`;
                `list_of_seq (x:num->int16) 256`; `pc:num`;
                `stackpointer:int64`; `returnaddress:int64`] th) THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_RULE) THEN
  CONJ_TAC THEN X_GEN_TAC `s:x86state` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP READ_MEMORY_BYTES16_LIST_OF_SEQ) THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[];
      ASM_SIMP_TAC[EL_LIST_OF_SEQ; IVAL_LT_3329]];
    REWRITE_TAC[MAP_LIST_OF_SEQ; NUM_OF_WORDLIST_LIST_OF_SEQ] THEN
    MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[IN_ELIM_THM; o_THM; defn; VAL_WORD] THEN DISCH_TAC THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
    REWRITE_TAC[api_compress_round d] THEN CONV_TAC NUM_REDUCE_CONV];;

let API_COMPRESS_D4 = prove
 (api_compress_tm 4 32,
  API_COMPRESS_TAC 4 MLKEM_COMPRESS_D4_X86_SUBROUTINE_CORRECT);;

let API_COMPRESS_D5 = prove
 (api_compress_tm 5 32,
  API_COMPRESS_TAC 5 MLKEM_COMPRESS_D5_X86_SUBROUTINE_CORRECT);;

let API_COMPRESS_D10 = prove
 (api_compress_tm 10 32,
  API_COMPRESS_TAC 10 MLKEM_COMPRESS_D10_X86_SUBROUTINE_CORRECT);;

let API_COMPRESS_D11 = prove
 (api_compress_tm 11 64,
  API_COMPRESS_TAC 11 MLKEM_COMPRESS_D11_X86_SUBROUTINE_CORRECT);;

(*** basemul_kK: the K polynomials at src1 (x_c, bounded by 2^12) times
 *** those at src2 (y_c) with their mulcaches at src2t (z_c), for pair p of
 *** FIPS 203 (coefficients avx_order(2p) and avx_order(2p+1) in memory,
 *** mulcache entry avx2_mcix p, with zeta negated for odd p)
 ***)

let READ16_BLOCKS = prove
 (`!a off (f:num->int16) s:x86state.
     (!i. i < 256
          ==> read(memory :> bytes16(word_add a (word(off + 2 * i)))) s =
              f i)
     ==> (!i. i < 16
              ==> !j. j < 8
                      ==> read(memory :> bytes16
                            (word_add a (word(off + 64 * j + 2 * i)))) s =
                          f(32 * j + i)) /\
         (!i. i < 16
              ==> !j. j < 8
                      ==> read(memory :> bytes16
                            (word_add a (word(off + 64 * j + 32 + 2 * i)))) s =
                          f(32 * j + 16 + i))`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(fun th ->
    W(fun (_,w) -> MP_TAC(SPEC (rand(rand w)) th))) THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)]) THEN
  REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN ARITH_TAC);;

let READ16_MC_BLOCKS = prove
 (`!a off (f:num->int16) s:x86state.
     (!i. i < 128
          ==> read(memory :> bytes16(word_add a (word(off + 2 * i)))) s =
              f i)
     ==> (!i. i < 16
              ==> !j. j < 8
                      ==> read(memory :> bytes16
                            (word_add a (word(off + 32 * j + 2 * i)))) s =
                          f(16 * j + i))`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(fun th ->
    W(fun (_,w) -> MP_TAC(SPEC (rand(rand w)) th))) THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)]) THEN
  REPEAT(AP_TERM_TAC ORELSE AP_THM_TAC) THEN ARITH_TAC);;

let AVX_PAIR_INDEX = prove
 (`!p. p < 128
       ==> (p MOD 64) DIV 4 < 16 /\ 4 * (p DIV 64) + p MOD 4 < 8 /\
           avx_order(2 * p) =
           32 * (4 * (p DIV 64) + p MOD 4) + (p MOD 64) DIV 4 /\
           avx_order(2 * p + 1) =
           32 * (4 * (p DIV 64) + p MOD 4) + 16 + (p MOD 64) DIV 4 /\
           avx2_mcix p = 16 * (4 * (p DIV 64) + p MOD 4) + (p MOD 64) DIV 4 /\
           (EVEN(4 * (p DIV 64) + p MOD 4) <=> EVEN p)`,
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[avx_order; avx2_mcix] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let AVX_PAIR_REINDEX = prove
 (`!P. (!i j. i < 16 /\ j < 8
              ==> P (32 * j + i) (32 * j + 16 + i) (16 * j + i) (EVEN j))
       ==> !p. p < 128
               ==> P (avx_order(2 * p)) (avx_order(2 * p + 1)) (avx2_mcix p)
                     (EVEN p)`,
  GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `p:num` THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP AVX_PAIR_INDEX) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(p MOD 64) DIV 4`;
                                `4 * (p DIV 64) + p MOD 4`]) THEN
  ASM_REWRITE_TAC[]);;

let READ16_BLOCKS0 = prove
 (`!a (f:num->int16) s:x86state.
     (!i. i < 256
          ==> read(memory :> bytes16(word_add a (word(2 * i)))) s = f i)
     ==> (!i. i < 16
              ==> !j. j < 8
                      ==> read(memory :> bytes16
                            (word_add a (word(64 * j + 2 * i)))) s =
                          f(32 * j + i)) /\
         (!i. i < 16
              ==> !j. j < 8
                      ==> read(memory :> bytes16
                            (word_add a (word(64 * j + 32 + 2 * i)))) s =
                          f(32 * j + 16 + i))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`a:int64`; `0`; `f:num->int16`; `s:x86state`]
    READ16_BLOCKS) THEN
  REWRITE_TAC[ADD_CLAUSES]);;

let READ16_MC_BLOCKS0 = prove
 (`!a (f:num->int16) s:x86state.
     (!i. i < 128
          ==> read(memory :> bytes16(word_add a (word(2 * i)))) s = f i)
     ==> (!i. i < 16
              ==> !j. j < 8
                      ==> read(memory :> bytes16
                            (word_add a (word(32 * j + 2 * i)))) s =
                          f(16 * j + i))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`a:int64`; `0`; `f:num->int16`; `s:x86state`]
    READ16_MC_BLOCKS) THEN
  REWRITE_TAC[ADD_CLAUSES]);;

let api_basemul_tm k =
  let cs = 0--(k-1) and n = string_of_int in
  let v nm c = nm ^ n c in
  let fvars = String.concat " "
    (map (fun c -> Printf.sprintf
                     "(%s:num->int16) (%s:num->int16) (%s:num->int16)"
                     (v "x" c) (v "y" c) (v "z" c)) cs) in
  let off m c =
    if c = 0 then "2 * i" else Printf.sprintf "%d + 2 * i" (m * c) in
  let rd a m c f lim = Printf.sprintf
    "(!i. i < %d ==> read(memory :> bytes16(word_add %s (word(%s)))) s = %s i)"
    lim a (off m c) f in
  let pres = String.concat " /\\\n" (flat (map (fun c ->
    [rd "src1" 512 c (v "x" c) 256; rd "src2" 512 c (v "y" c) 256;
     rd "src2t" 256 c (v "z" c) 128]) cs)) in
  let bnds = String.concat " /\\\n" (map (fun c -> Printf.sprintf
    "(!i. i < 256 ==> abs(ival(%s i)) <= &2 pow 12)" (v "x" c)) cs) in
  let sum f = String.concat " + " (map f (rev cs)) in
  let ev c = Printf.sprintf
    ("(ival(%s(avx_order(2 * p + 1))) * "^^
     "(if EVEN p then ival(%s(avx2_mcix p)) else --ival(%s(avx2_mcix p))) + "^^
     "ival(%s(avx_order(2 * p))) * ival(%s(avx_order(2 * p))))")
    (v "x" c) (v "z" c) (v "z" c) (v "x" c) (v "y" c)
  and od c = Printf.sprintf
    ("(ival(%s(avx_order(2 * p + 1))) * ival(%s(avx_order(2 * p))) + "^^
     "ival(%s(avx_order(2 * p))) * ival(%s(avx_order(2 * p + 1))))")
    (v "x" c) (v "y" c) (v "x" c) (v "y" c) in
  parse_term(Printf.sprintf
   "!src1 src2 src2t dst %s pc stackpointer returnaddress.
      aligned 32 src1 /\\ aligned 32 src2 /\\ aligned 32 src2t /\\
      aligned 32 dst /\\
      ALL (nonoverlapping (dst, 512))
          [(src1, %d); (src2, %d); (src2t, %d)] /\\
      nonoverlapping (dst, 512) (word pc, LENGTH mlkem_basemul_k%d_mc) /\\
      nonoverlapping (dst, 512) (stackpointer, 8) /\\
      %s
      ==> ensures x86
           (\\s. bytes_loaded s (word pc) mlkem_basemul_k%d_mc /\\
                read RIP s = word pc /\\
                read RSP s = stackpointer /\\
                read (memory :> bytes64 stackpointer) s = returnaddress /\\
                C_ARGUMENTS [dst; src1; src2; src2t] s /\\
                %s)
           (\\s. read RIP s = returnaddress /\\
                read RSP s = word_add stackpointer (word 8) /\\
                !p. p < 128
                    ==> (ival(read(memory :> bytes16(word_add dst
                                (word(2 * avx_order(2 * p))))) s) ==
                         &169 * (%s)) (mod &3329) /\\
                        (ival(read(memory :> bytes16(word_add dst
                                (word(2 * avx_order(2 * p + 1))))) s) ==
                         &169 * (%s)) (mod &3329))
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(dst, 512)])"
   fvars (512 * k) (512 * k) (256 * k) k bnds k pres (sum ev) (sum od));;

let API_BASEMUL_TAC k th defs =
  let cs = 0--(k-1) in
  let mk nm c = mk_var(nm ^ string_of_int c,`:num->int16`) in
  let lam f t = vsubst [f,`f:num->int16`] t in
  let args = flat (map (fun c ->
    let x = mk "x" c and y = mk "y" c and z = mk "z" c in
    [lam x `\i j. (f:num->int16)(32 * j + i)`;
     lam x `\i j. (f:num->int16)(32 * j + 16 + i)`;
     lam y `\i j. (f:num->int16)(32 * j + i)`;
     lam y `\i j. (f:num->int16)(32 * j + 16 + i)`;
     lam z `\i j. (f:num->int16)(16 * j + i)`]) cs) in
  let sth = BETA_RULE(SPECL
    ([`src1:int64`; `src2:int64`; `src2t:int64`; `dst:int64`] @ args @
     [`pc:num`; `stackpointer:int64`; `returnaddress:int64`]) th) in
  let blocks th =
    tryfind (fun l -> MATCH_MP l th)
      [READ16_BLOCKS; READ16_BLOCKS0; READ16_MC_BLOCKS; READ16_MC_BLOCKS0] in
  let ks = string_of_int k in
  let sfx = if k = 2 then "" else "_k"^ks in
  let c0 = "pmulaccred0"^sfx and c0o = "pmulaccred0_odd"^sfx
  and c1 = "pmulaccred1"^sfx in
  let hasc nm t = can (find_term (fun u -> try fst(dest_const u) = nm
                                         with Failure _ -> false)) t in
  let post_at nm jv let_form =
    FIRST_ASSUM(fun th -> if is_forall(concl th) && hasc nm (concl th)
                          then MP_TAC(SPEC `i:num` th) else NO_TAC) THEN
    (ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(MP_TAC o SPEC jv)]) THEN
    (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    (if let_form then CONV_TAC(TOP_DEPTH_CONV let_CONV) else ALL_TAC) THEN
    (ANTS_TAC THENL
      [REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
       ALL_TAC]) in
  let fin =
    REWRITE_TAC defs THEN
    REWRITE_TAC[INVERSE_MOD_CONV `inverse_mod 3329 65536`; INT_CONG_RREM] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `y:int = z ==> (x == y) (mod n) ==> (x == z) (mod n)`) THEN
    INT_ARITH_TAC in
  REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC sth THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_RULE) THEN
  CONJ_TAC THEN X_GEN_TAC `s:x86state` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THENL
   [(fun (asl,w) ->
      MAP_EVERY (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))
        (mapfilter (blocks o snd) asl) (asl,w)) THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
    W(fun (_,w) ->
      let body = rand(snd(dest_forall w)) in
      let ve = genvar `:num` and vo = genvar `:num` and vq = genvar `:num`
      and vb = genvar `:bool` in
      let body' = subst [ve,`avx_order(2 * p)`; vo,`avx_order(2 * p + 1)`;
                         vq,`avx2_mcix p`; vb,`EVEN p`] body in
      MATCH_MP_TAC(BETA_RULE(SPEC (list_mk_abs([ve;vo;vq;vb],body'))
                                  AVX_PAIR_REINDEX))) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[ARITH_RULE `2 * (32 * j + i) = 64 * j + 2 * i`;
                ARITH_RULE `2 * (32 * j + 16 + i) = 64 * j + 32 + 2 * i`] THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `EVEN j` THEN
      POP_ASSUM(fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THENL
       [FIRST_X_ASSUM(X_CHOOSE_THEN `j0:num` SUBST_ALL_TAC o
          REWRITE_RULE[EVEN_EXISTS] o
          check (fun th -> concl th = `EVEN j`)) THEN
        post_at c0 `j0:num` true THEN fin;
        FIRST_X_ASSUM(X_CHOOSE_THEN `j0:num` SUBST_ALL_TAC o
          REWRITE_RULE[NOT_EVEN; ODD_EXISTS; ADD1] o
          check (fun th -> concl th = `~EVEN j`)) THEN
        post_at c0o `j0:num` true THEN fin];
      post_at c1 `j:num` false THEN fin]];;

let pmul_defs2 = [pmulaccred0; pmulaccred0_odd; pmulaccred1; pmulacc0;
                  pmulacc0_odd; pmulacc1; pmul0; pmul0_odd; pmul1];;

let API_BASEMUL_K2 = time prove
 (api_basemul_tm 2,
  API_BASEMUL_TAC 2 MLKEM_BASEMUL_K2_SUBROUTINE_CORRECT pmul_defs2);;

let pmul_defs3 = [pmulaccred0_k3; pmulaccred0_odd_k3; pmulaccred1_k3;
                  pmulacc0_k3; pmulacc0_odd_k3; pmulacc1_k3;
                  pmul0; pmul0_odd; pmul1];;

let API_BASEMUL_K3 = time prove
 (api_basemul_tm 3,
  API_BASEMUL_TAC 3 MLKEM_BASEMUL_K3_SUBROUTINE_CORRECT pmul_defs3);;

let pmul_defs4 = [pmulaccred0_k4; pmulaccred0_odd_k4; pmulaccred1_k4;
                  pmulacc0_k4; pmulacc0_odd_k4; pmulacc1_k4;
                  pmul0; pmul0_odd; pmul1];;

let API_BASEMUL_K4 = time prove
 (api_basemul_tm 4,
  API_BASEMUL_TAC 4 MLKEM_BASEMUL_K4_SUBROUTINE_CORRECT pmul_defs4);;

(* ------------------------------------------------------------------------- *)
(* K-PKE from the x86 kernels: the blocked statements of                     *)
(* utils/mlkem_native2_kpke.ml with the coefficients in the NTT domain in    *)
(* the order of the kernels in memory, and the mulcaches and products as     *)
(* those kernels give them (see API_BASEMUL_K2 etc.), from the FIPS 203      *)
(* views: coefficient i of a polynomial in memory order f is f(avx_order i). *)
(* ------------------------------------------------------------------------- *)

(*** The mulcache view: entry p of FIPS 203 from that of the kernel ***)

let api_mc_view = `\(CM:num->num->int16) j p.
   iword(if EVEN p then ival(CM j (avx2_mcix p))
         else --ival(CM j (avx2_mcix p))):int16`;;

let IVAL_MC_VIEW = prove
 (`!(CM:num->num->int16) j p.
        abs(ival(CM j (avx2_mcix p))) <= &3328
        ==> ival((iword(if EVEN p then ival(CM j (avx2_mcix p))
                        else --ival(CM j (avx2_mcix p)))):int16) =
            if EVEN p then ival(CM j (avx2_mcix p))
            else --ival(CM j (avx2_mcix p))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC INT_REDUCE_CONV THEN COND_CASES_TAC THEN ASM_INT_ARITH_TAC);;

let AVX2_MCIX_LT = prove
 (`!p. p < 128 ==> avx2_mcix p < 128`,
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[avx2_mcix] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(*** The blocked statement of decryption with the x86 kernels ***)

let x86_kpke_decrypt_tm k =
  let ks = string_of_int k and n x = string_of_int x in
  let du = api_du k and dv = api_dv k in
  let sum f = String.concat " + " (map f (rev(0--(k-1)))) in
  let ev c = let cs = n c in
    "(ival((SM:num->num->int16) "^cs^" (avx_order(2 * p + 1))) * "^
    "(if EVEN p then ival(CM "^cs^" (avx2_mcix p)) "^
    "else --ival(CM "^cs^" (avx2_mcix p))) + "^
    "ival(SM "^cs^" (avx_order(2 * p))) * ival(UM "^cs^" (avx_order(2 * p))))"
  and od c = let cs = n c in
    "(ival((SM:num->num->int16) "^cs^" (avx_order(2 * p + 1))) * "^
    "ival(UM "^cs^" (avx_order(2 * p))) + "^
    "ival(SM "^cs^" (avx_order(2 * p))) * "^
    "ival(UM "^cs^" (avx_order(2 * p + 1))))" in
  parse_term(
   "!dk ct (UD:num->num->int16) (VD:num->int16) (SM:num->num->int16) "^
   "(UM:num->num->int16) (CM:num->num->int16) (WM:num->int16) "^
   "(WI:num->int16) (VR:num->int16). "^
   "(!j i. j < "^ks^" /\\ i < 256 ==> UD j i = "^
   "  word((3329 * (num_of_bytelist ct DIV 2 EXP ("^n du^
   " * (256 * j + i))) MOD 2 EXP "^n du^" + "^n(1 lsl (du-1))^") DIV "^
   n(1 lsl du)^")) /\\ "^
   "(!i. i < 256 ==> VD i = "^
   "  word((3329 * (num_of_bytelist(mlkem_slice "^n(32 * du * k)^" "^
   n(32 * dv)^" ct) DIV 2 EXP ("^n dv^" * i)) MOD 2 EXP "^n dv^" + "^
   n(1 lsl (dv-1))^") DIV "^n(1 lsl dv)^")) /\\ "^
   "(!j i. j < "^ks^" /\\ i < 256 ==> "^
   "  SM j i = word((num_of_bytelist dk DIV "^
   "    2 EXP (12 * (256 * j + avx_unorder i))) MOD 2 EXP 12)) /\\ "^
   "(!j i. j < "^ks^" /\\ i < 256 ==> "^
   "  (ival(UM j i) == avx2_forward_ntt (ival o UD j) i) (mod &3329) /\\ "^
   "  abs(ival(UM j i)) <= &23594) /\\ "^
   "(!j p. j < "^ks^" /\\ p < 128 ==> "^
   "  (ival(CM j p) == avx2_mulcache (ival o UM j) p) (mod &3329) /\\ "^
   "  abs(ival(CM j p)) <= &3328) /\\ "^
   "(!p. p < 128 ==> "^
   "  (ival(WM(avx_order(2 * p))) == &169 * ("^sum ev^")) (mod &3329) /\\ "^
   "  (ival(WM(avx_order(2 * p + 1))) == &169 * ("^sum od^")) "^
   "  (mod &3329)) /\\ "^
   "(!i. i < 256 ==> (ival(WI i) == avx2_inverse_ntt (ival o WM) i) "^
   "  (mod &3329) /\\ abs(ival(WI i)) <= &26631) /\\ "^
   "(!i. i < 256 ==> ival(VR i) = ival(word_sub (VD i) (WI i)) rem &3329) "^
   "==> nsum {i | i < 256} "^
   "      (\\i. ((4 * val(VR i) + 3329) DIV 6658) MOD 2 * 2 EXP i) = "^
   "    num_of_bytelist(kpke_decrypt "^api_param k^" dk ct)");;


let MC_SIGN_CONG_T = INTEGER_RULE
 `!c m u z n:int. (c == m) (mod n) ==> (m == u * &1 * z) (mod n)
                  ==> (c == u * z) (mod n)`;;

let MC_SIGN_CONG_F = INTEGER_RULE
 `!c m u z n:int. (c == m) (mod n) ==> (m == u * -- &1 * z) (mod n)
                  ==> (--c == u * z) (mod n)`;;

let MC_SIGN_CONG = prove
 (`!b (c:int) m u z n.
        (c == m) (mod n)
        ==> (m == u * (if b then &1 else -- &1) * z) (mod n)
        ==> ((if b then c else --c) == u * z) (mod n)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[MC_SIGN_CONG_T; MC_SIGN_CONG_F]);;

let hascon nm t = can (find_term (fun u -> try fst(dest_const u) = nm
                                         with Failure _ -> false)) t;;

let X86_KPKE_DECRYPT_TAC k bth =
  let kn = mk_small_numeral k in
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC bth THEN
  MAP_EVERY EXISTS_TAC
   [`UD:num->num->int16`; `VD:num->int16`;
    `\j i. (SM:num->num->int16) j (avx_order i)`;
    `\j i. (UM:num->num->int16) j (avx_order i)`;
    mk_comb(api_mc_view,`CM:num->num->int16`);
    `\n. (WM:num->int16)(avx_order n)`; `WI:num->int16`] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [ASM_SIMP_TAC[AVX_ORDER_UNORDER];
    FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `avx_order i`] o
      check (hascon "avx2_forward_ntt" o concl)) THEN
    ASM_SIMP_TAC[AVX_ORDER_UNORDER; AVX2_FORWARD_NTT_UNORDER; o_DEF];
    FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `avx2_mcix p`] o
      check (hascon "avx2_mulcache" o concl)) THEN
    ASM_SIMP_TAC[AVX2_MCIX_LT] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[IVAL_MC_VIEW] THEN
    MP_TAC(ISPECL [`ival o (UM:num->num->int16) j`; `p:num`]
      AVX2_MULCACHE_PAIR) THEN
    ASM_REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      hascon "avx2_mulcache" (concl th) && not(is_forall(concl th)))) THEN
    REWRITE_TAC[MC_SIGN_CONG];
    SUBGOAL_THEN
     (vsubst [kn,`k:num`]
       `!c. c < k
            ==> abs(ival((CM:num->num->int16) c (avx2_mcix p))) <= &3328`)
    ASSUME_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[AVX2_MCIX_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[IVAL_MC_VIEW; ARITH_RULE `0 < 4 /\ 1 < 4 /\ 2 < 4 /\ 3 < 4 /\
                                          0 < 3 /\ 1 < 3 /\ 2 < 3 /\
                                          0 < 2 /\ 1 < 2`];
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o
      check (hascon "avx2_inverse_ntt" o concl)) THEN
    ASM_REWRITE_TAC[AVX2_INVERSE_NTT_ORDER; o_THM]];;

let X86_KPKE_DECRYPT_K2 = time prove
 (x86_kpke_decrypt_tm 2, X86_KPKE_DECRYPT_TAC 2 KPKE_DECRYPT_K2_BLOCKS);;

let X86_KPKE_DECRYPT_K3 = time prove
 (x86_kpke_decrypt_tm 3, X86_KPKE_DECRYPT_TAC 3 KPKE_DECRYPT_K3_BLOCKS);;

let X86_KPKE_DECRYPT_K4 = time prove
 (x86_kpke_decrypt_tm 4, X86_KPKE_DECRYPT_TAC 4 KPKE_DECRYPT_K4_BLOCKS);;

(* ------------------------------------------------------------------------- *)
(* The tables of the constants block as the callees take them, at the        *)
(* addresses word(pc + N) of the image.                                      *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE2_DECOMPRESS_D4_TABLE_VALUE = time prove
 (`num_of_bytelist mlkem_native2_decompress_d4_table =
   num_of_wordlist((MAP iword decompress_d4_data):byte list)`,
  API_TABLE_VALUE_TAC[mlkem_native2_decompress_d4_table; decompress_d4_data]);;

let MLKEM_NATIVE2_DECOMPRESS_D5_TABLE_VALUE = time prove
 (`num_of_bytelist mlkem_native2_decompress_d5_table =
   num_of_wordlist((MAP iword decompress_d5_data):byte list)`,
  API_TABLE_VALUE_TAC[mlkem_native2_decompress_d5_table; decompress_d5_data]);;

let MLKEM_NATIVE2_DECOMPRESS_D10_TABLE_VALUE = time prove
 (`num_of_bytelist mlkem_native2_decompress_d10_table =
   num_of_wordlist((MAP iword decompress_d10_data):byte list)`,
  API_TABLE_VALUE_TAC[mlkem_native2_decompress_d10_table;
                      decompress_d10_data]);;

let MLKEM_NATIVE2_DECOMPRESS_D11_TABLE_VALUE = time prove
 (`num_of_bytelist mlkem_native2_decompress_d11_table =
   num_of_wordlist((MAP iword decompress_d11_data):byte list)`,
  API_TABLE_VALUE_TAC[mlkem_native2_decompress_d11_table;
                      decompress_d11_data]);;

let MLKEM_NATIVE2_COMPRESS_D5_TABLE_VALUE = time prove
 (`num_of_bytelist mlkem_native2_compress_d5_table =
   num_of_wordlist((MAP iword compress_d5_data):byte list)`,
  API_TABLE_VALUE_TAC[mlkem_native2_compress_d5_table; compress_d5_data]);;

let MLKEM_NATIVE2_COMPRESS_D10_TABLE_VALUE = time prove
 (`num_of_bytelist mlkem_native2_compress_d10_table =
   num_of_wordlist((MAP iword compress_d10_data):byte list)`,
  API_TABLE_VALUE_TAC[mlkem_native2_compress_d10_table; compress_d10_data]);;

let MLKEM_NATIVE2_COMPRESS_D11_TABLE_VALUE = time prove
 (`num_of_bytelist mlkem_native2_compress_d11_table =
   num_of_wordlist((MAP iword compress_d11_data):byte list)`,
  API_TABLE_VALUE_TAC[mlkem_native2_compress_d11_table; compress_d11_data]);;

(*** The facts at a state with the image loaded ***)

let api_table_fact tab value =
  GEN_ALL(DISCH_ALL(REWRITE_RULE[value] (UNDISCH(SPEC_ALL tab))));;

let MLKEM_NATIVE2_TABLE_FACTS =
  [MLKEM_NATIVE2_QDATA;
   api_table_fact MLKEM_NATIVE2_DECOMPRESS_D4_TABLE
     MLKEM_NATIVE2_DECOMPRESS_D4_TABLE_VALUE;
   api_table_fact MLKEM_NATIVE2_DECOMPRESS_D5_TABLE
     MLKEM_NATIVE2_DECOMPRESS_D5_TABLE_VALUE;
   api_table_fact MLKEM_NATIVE2_DECOMPRESS_D10_TABLE
     MLKEM_NATIVE2_DECOMPRESS_D10_TABLE_VALUE;
   api_table_fact MLKEM_NATIVE2_DECOMPRESS_D11_TABLE
     MLKEM_NATIVE2_DECOMPRESS_D11_TABLE_VALUE;
   api_table_fact MLKEM_NATIVE2_COMPRESS_D4_TABLE
     MLKEM_NATIVE2_COMPRESS_D4_TABLE_VALUE;
   api_table_fact MLKEM_NATIVE2_COMPRESS_D5_TABLE
     MLKEM_NATIVE2_COMPRESS_D5_TABLE_VALUE;
   api_table_fact MLKEM_NATIVE2_COMPRESS_D10_TABLE
     MLKEM_NATIVE2_COMPRESS_D10_TABLE_VALUE;
   api_table_fact MLKEM_NATIVE2_COMPRESS_D11_TABLE
     MLKEM_NATIVE2_COMPRESS_D11_TABLE_VALUE];;

(* ------------------------------------------------------------------------- *)
(* The entry of an API function, for the statement with the stack region of  *)
(* n bytes below the return address (n + 8 with it) and the frame of size    *)
(* bytes, with the callees' stack cs = n - 79 - size bytes below the frame:  *)
(* the goal from its variables vars (those before stackpointer), with the    *)
(* stack region at stackpointer, the steps of enter (with the callee-saved   *)
(* registers preserved), the facts about the tables of the image, and the    *)
(* frame base fb with its facts: aligned, the frame and the callees' stack   *)
(* away from each other region of the statement and from the saved           *)
(* registers and the return address, and fb = stackpointer + delta.          *)
(* ------------------------------------------------------------------------- *)

let API_PCADD_CONV =
  REWR_CONV(GSYM WORD_ADD) THENC
  RAND_CONV(REWR_CONV(GSYM ADD_ASSOC) THENC RAND_CONV NUM_ADD_CONV);;

let ALIGNED_PC_OFFSET = prove
 (`!pc n. aligned 32 (word pc:int64) /\ 32 divides n
          ==> aligned 32 (word(pc + n):int64)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_ADD] THEN
  MATCH_MP_TAC ALIGNED_WORD_ADD THEN ASM_REWRITE_TAC[ALIGNED_WORD] THEN
  REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC(RAND_CONV NUM_REDUCE_CONV THENC DIVIDES_CONV));;

(*** aligned 32 (word(pc + N)) for the address of each table ***)

let MLKEM_NATIVE2_TABLE_ALIGNED =
  let addrs = map (fun th ->
    let c = snd(dest_imp(snd(strip_forall(concl th)))) in
    lhand(rand(rand(lhand(lhand c))))) MLKEM_NATIVE2_TABLE_FACTS in
  map (fun a ->
    let n = rand(rand a) in
    let th = SPECL [`pc:num`; n] ALIGNED_PC_OFFSET in
    let dth = EQT_ELIM(DIVIDES_CONV(rand(lhand(concl th)))) in
    GEN `pc:num` (REWRITE_RULE[dth] th)) addrs;;

let API_IMAGE_TABLES_TAC k =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `bytes_loaded s (word pc) mc`) c &&
       rand(rator(rator c)) = state_of k
    then MAP_EVERY (fun lem -> ASSUME_TAC(MATCH_MP lem th))
          MLKEM_NATIVE2_TABLE_FACTS
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (word pc:int64)`
    then MAP_EVERY (fun lem -> ASSUME_TAC(MATCH_MP lem th))
          MLKEM_NATIVE2_TABLE_ALIGNED
    else NO_TAC);;

let dest_nonoverlapping tm =
  match strip_comb tm with
    Const("nonoverlapping",_),[l;r] -> l,r
  | _ -> failwith "dest_nonoverlapping";;

let API_ENTRY_TAC exec vars n size =
  let m = n - 48 - size in
  let cs = m - 31 in
  let nn = mk_small_numeral n and mm = mk_small_numeral m
  and csn = mk_small_numeral cs and sizen = mk_small_numeral size in
  let fth = CONV_RULE NUM_REDUCE_CONV
   (REWRITE_RULE[IMP_CONJ]
     (SPEC_ALL(SPECL [`stackpointer:int64`; `delta:num`; csn; sizen; nn]
                     API_FRAME_NONOVERLAPPING)))
  and sth = REWRITE_RULE[] (CONV_RULE NUM_REDUCE_CONV
   (REWRITE_RULE[IMP_CONJ]
     (SPECL [`stackpointer:int64`; `delta:num`; csn; sizen; nn]
            API_FRAME_SAVED_NONOVERLAPPING))) in
  let dlo = lhand(concl fth) and dhi = lhand(rand(concl fth)) in
  let stk = mk_pair(`stackpointer:int64`,mk_small_numeral(n + 8)) in
  let frame_fact th =
    let c = concl th in
    let l,r = dest_nonoverlapping c in
    let th' = if l = stk then th
              else if r = stk then ONCE_REWRITE_RULE[NONOVERLAPPING_SYM] th
              else failwith "frame_fact" in
    MATCH_MP (GEN_ALL(MP (MP fth (ASSUME dlo)) (ASSUME dhi))) th' in
  MAP_EVERY X_GEN_TAC vars THEN
  WORD_FORALL_OFFSET_TAC n THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; ALLPAIRS] THEN
  REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  MAP_EVERY (fun r -> ENSURES_PRESERVED_TAC
                (String.lowercase_ascii(fst(dest_const r))^"_init") r)
   [`RBX`; `RBP`; `R12`; `R13`; `R14`; `R15`] THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC exec (1--11) THEN API_RIPREL_TAC THEN
  API_IMAGE_TABLES_TAC 11 THEN
  MP_TAC(SPECL [`stackpointer:int64`; mm] API_ALIGN_FRAME) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:num`
   (CONJUNCTS_THEN2 (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
                    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN (mk_conj(dlo,dhi)) STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  (fun (asl,w as gl) ->
     MAP_EVERY (ASSUME_TAC o frame_fact o snd)
       (filter (fun (_,th) -> can frame_fact th) asl) gl) THEN
  ASSUME_TAC(MP (MP sth (ASSUME dlo)) (ASSUME dhi)) THEN
  ABBREV_TAC `fb:int64 = word_add stackpointer (word delta)`;;

(*** The state number k of the goal (eventually x86 P sk) ***)

let api_state_of_goal (asl,w) =
  let sv = rand w in
  let nm = fst(dest_var sv) in
  int_of_string(String.sub nm 1 (String.length nm - 1));;

let ON_STATE f gl = f (api_state_of_goal gl) gl;;

(*** Steps while RIP is in the function at [lo,hi) of the image ***)

let API_TO_CALL_TAC exec lo hi =
  let rec tac k gl =
    let off = get_pc_offset k gl in
    if off < lo || off >= hi then ALL_TAC gl
    else (X86_STEPS_TAC exec [k+1] THEN tac (k+1)) gl in
  ON_STATE tac;;

(*** The register value fact of reg at state k with its RIP-relative
 *** address word_add (word(pc + a)) (word b) as word(pc + (a + b))
 ***)

let API_REG_PCADD_TAC reg k =
  let lhs = mk_comb(mk_comb(`read:(x86state,int64)component->x86state->int64`,
                            reg),state_of k) in
  FIRST_X_ASSUM(fun th ->
    if try lhand(concl th) = lhs with Failure _ -> false
    then ASSUME_TAC(CONV_RULE(RAND_CONV(TRY_CONV API_PCADD_CONV)) th)
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Buffers and ghosts (as for AArch64): addresses base + N, the facts        *)
(* !i. i < n ==> read(bytes16(base + N + 2 * i)) s = F i about them, and     *)
(* ghost functions for what the callees write.                               *)
(* ------------------------------------------------------------------------- *)

let api_addr_parts a =
  match a with
    Comb(Comb(Const("word_add",_),b),Comb(Const("word",_),n))
      when is_numeral n -> b,dest_small_numeral n
  | _ -> a,0;;

let api_rd16 b nn i s =
  let off = if nn = 0 then mk_binop `( * ):num->num->num` `2` i
            else mk_binop `(+):num->num->num` (mk_small_numeral nn)
                   (mk_binop `( * ):num->num->num` `2` i) in
  vsubst [b,`b:int64`; off,`off:num`; s,`s:x86state`]
   `read (memory :> bytes16 (word_add b (word off))) s`;;

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

let API_GHOST16_TAC v (b,nn) n k =
  let vt = mk_var(v,`:num->int16`) and sv = state_of k in
  let rd i = api_rd16 b nn i sv in
  let fact = mk_forall(`i:num`,
    mk_imp(mk_binop `(<):num->num->bool` `i:num` (mk_small_numeral n),
           mk_eq(rd `i:num`,mk_comb(vt,`i:num`)))) in
  SUBGOAL_THEN (mk_exists(vt,fact)) (X_CHOOSE_TAC vt) THENL
   [EXISTS_TAC (mk_abs(`i:num`,rd `i:num`)) THEN REWRITE_TAC[]; ALL_TAC];;

let READ16_REBASE = prove
 (`!a b off n (x:num->int16) s:x86state.
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

let API_PRE16_TAC a n k gl =
  let b,nn = api_addr_parts a in
  let th = api_buf_fact (b,nn) n k gl in
  if nn = 0 then ASSUME_TAC th gl else
  ASSUME_TAC(BETA_RULE(MATCH_MP READ16_REBASE (CONJ (REFL a) th))) gl;;

let api_pre16_fun a k gl =
  let sv = state_of k in
  let ok c =
    try let iv,body = dest_forall c in
        let _,eq = dest_imp body in
        lhand eq = vsubst [iv,`i:num`; a,`a:int64`; sv,`s:x86state`]
          `read (memory :> bytes16 (word_add a (word(2 * i)))) s`
    with Failure _ -> false in
  let c = concl(find_asm ok gl) in
  let iv,body = dest_forall c in
  mk_abs(iv,rand(rand body));;

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

(*** aligned 32 (word_add b (word n)) for the register values at state k
 *** of that form with aligned 32 b among the assumptions and 32 | n
 ***)

let ALIGNED_BASE_OFFSET = prove
 (`!x n. aligned 32 (x:int64) /\ 32 divides n
         ==> aligned 32 (word_add x (word n))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ALIGNED_WORD_ADD THEN
  ASM_REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
  CONV_TAC(RAND_CONV NUM_REDUCE_CONV THENC DIVIDES_CONV));;

let API_ALIGNED_TAC k (asl,w as gl) =
  let sv = state_of k in
  let vals = mapfilter (fun (_,th) ->
    let c = concl th in
    let l,r = dest_eq c in
    if rand l = sv && type_of r = `:int64` &&
       (try fst(dest_const(rator(rator l))) = "read" with Failure _ -> false)
    then r else failwith "") asl in
  let cands = setify(mapfilter (fun a ->
    let b,n = api_addr_parts a in
    if n > 0 && n mod 32 = 0 then (b,n) else failwith "") vals) in
  let mk (b,n) =
    let ath = find_asm (fun c -> c = mk_comb(`aligned 32:int64->bool`,b)) gl in
    let dth = EQT_ELIM(DIVIDES_CONV(mk_binop `(divides):num->num->bool`
                         `32` (mk_small_numeral n))) in
    MATCH_MP ALIGNED_BASE_OFFSET (CONJ ath dth) in
  MAP_EVERY (fun bn -> try ASSUME_TAC(mk bn) with Failure _ -> ALL_TAC)
            cands gl;;

(* ------------------------------------------------------------------------- *)
(* The kernel calls (at the state kk at the callee's entry) and their posts  *)
(* as ghosts v for the buffer bn = (base,N) with the facts the K-PKE         *)
(* statements take.                                                          *)
(* ------------------------------------------------------------------------- *)

let api_decompress_th d =
  match d with
    4 -> layout "mlkem_decompress_d4_x86",mlkem_decompress_d4_x86_mc,
         API_DECOMPRESS_D4
  | 5 -> layout "mlkem_decompress_d5_x86",mlkem_decompress_d5_x86_mc,
         API_DECOMPRESS_D5
  | 10 -> layout "mlkem_decompress_d10_x86",mlkem_decompress_d10_x86_mc,
          API_DECOMPRESS_D10
  | _ -> layout "mlkem_decompress_d11_x86",mlkem_decompress_d11_x86_mc,
         API_DECOMPRESS_D11;;

let API_DECOMPRESS_CALL_TAC exec d c off len kk gl =
  let n = mk_comb(`num_of_bytelist`,
    list_mk_icomb "mlkem_slice"
     [mk_small_numeral off; mk_small_numeral len; c]) in
  let base,_ = api_addr_parts(find_read_fact `RSI` kk gl) in
  let lo,mc,th = api_decompress_th d in
  (API_SLICE_AT_TAC base c off len kk THEN API_REG_PCADD_TAC `RDX` kk THEN
   API_ALIGNED_TAC kk THEN
   NATIVE2_CALL_TAC mlkem_native2_image_mc exec (lo,mc,th)
    [`read RDI s`; `read RSI s`; `read RDX s`; n] kk) gl;;

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

(*** After a call: RSP as fb again ***)

let API_WORD_SUB_ADD = WORD_RULE `!x y:int64. word_add (word_sub x y) y = x`;;

let API_RSP_TAC = RULE_ASSUM_TAC(REWRITE_RULE[API_WORD_SUB_ADD]);;

(*** frombytes of polynomial j of ek (at RSI) ***)

let API_FROMBYTES_CALL_TAC exec ek j kk gl =
  let n = mk_comb(`num_of_bytelist`,
    list_mk_icomb "mlkem_slice" [mk_small_numeral(384 * j); `384`; ek]) in
  let base,_ = api_addr_parts(find_read_fact `RSI` kk gl) in
  (API_SLICE_AT_TAC base ek (384 * j) 384 kk THEN
   API_ALIGNED_TAC kk THEN
   NATIVE2_CALL_TAC mlkem_native2_image_mc exec
    (layout "mlkem_frombytes",mlkem_frombytes_mc,API_FROMBYTES)
    [`read RDI s`; `read RSI s`; n] kk) gl;;

let API_FROMBYTES_POST_TAC v bn ek j kk =
  let vt = mk_var(v,`:num->int16`) in
  let goal0 = vsubst [vt,`v:num->int16`; ek,`ek:byte list`;
                      mk_small_numeral j,`j:num`]
   `!i. i < 256
        ==> (v:num->int16) i =
            word((num_of_bytelist ek DIV
                  2 EXP (12 * (256 * j + avx_unorder i))) MOD 2 EXP 12)` in
  let goal = rand(concl(NUM_REDUCE_CONV goal0)) in
  API_POST16_TAC v bn 256 kk goal []
   (fun bth ->
     DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
     MP_TAC(SPECL [ek; `384`; `12`; mk_small_numeral j; `avx_unorder i`]
              FIELD_OF_SLICE_BYTES) THEN
     ASM_SIMP_TAC[bth; AVX_ORDER_UNORDER] THEN
     CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

(*** Bounds for the NTT and basemul inputs from the ghost facts ***)

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

let FIELD12_BOUND = prove
 (`!x. abs(ival(word(x MOD 4096):int16)) <= &2 pow 12`,
  GEN_TAC THEN MP_TAC(SPECL [`x:num`; `4096`] MOD_LT_EQ) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[IVAL_WORD_SMALL; ARITH_RULE `x < 4096 ==> x < 32768`] THEN
  REWRITE_TAC[INT_ABS_NUM; GSYM INT_OF_NUM_LT] THEN
  CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC);;

(*** The bound !i. i < 256 ==> abs(ival(f i)) <= b of a ghost f from its
 *** defining fact, by the lemma lem
 ***)

let API_GHOST_BOUND_TAC f b lem =
  let goal = vsubst [f,`f:num->int16`; b,`b:int`]
   `!i. i < 256 ==> abs(ival((f:num->int16) i)) <= b` in
  SUBGOAL_THEN goal ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th ->
      let c = concl th in
      if is_forall c &&
         (try let _,e = dest_imp(snd(dest_forall c)) in
              lhand e = mk_comb(f,fst(dest_forall c))
          with Failure _ -> false)
      then REWRITE_TAC[MP (SPEC `i:num` th) (ASSUME `i < 256`)]
      else NO_TAC) THEN
    TRY(fun g -> (MATCH_MP_TAC lem THEN CONV_TAC NUM_REDUCE_CONV THEN
                  NO_TAC) g) THEN
    REWRITE_TAC[lem];
    ALL_TAC];;

(*** The NTT of the polynomial at RDI ***)

let API_NTT_CALL_TAC exec k gl =
  let a = find_read_fact `RDI` k gl in
  (API_PRE16_TAC a 256 k THEN API_REG_PCADD_TAC `RSI` k THEN
   API_ALIGNED_TAC k THEN
   (fun gl ->
     let f = api_pre16_fun a k gl in
     let f' = try rand(concl(ETA_CONV f)) with Failure _ -> f in
     NATIVE2_CALL_TAC mlkem_native2_image_mc exec
      (layout "mlkem_ntt_x86",mlkem_ntt_mc,API_NTT)
      [`read RDI s`; `read RSI s`; f'] k gl)) gl;;

let API_NTT_POST_TAC v bn x kk =
  let goal = vsubst [mk_var(v,`:num->int16`),`v:num->int16`;
                     x,`x:num->int16`]
   `!i. i < 256
        ==> (ival((v:num->int16) i) ==
             avx2_forward_ntt (ival o (x:num->int16)) i)
            (mod &3329) /\
            abs(ival(v i)) <= &23594` in
  API_POST16_TAC v bn 256 kk goal []
   (fun _ -> CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP_TAC[]);;

(*** The mulcache of the polynomial at RSI into RDI ***)

let API_MULCACHE_CALL_TAC exec k gl =
  let a = find_read_fact `RSI` k gl in
  (API_PRE16_TAC a 256 k THEN API_REG_PCADD_TAC `RDX` k THEN
   API_ALIGNED_TAC k THEN
   (fun gl ->
     let f = api_pre16_fun a k gl in
     let f' = try rand(concl(ETA_CONV f)) with Failure _ -> f in
     NATIVE2_CALL_TAC mlkem_native2_image_mc exec
      (layout "mlkem_mulcache_compute_x86",mlkem_mulcache_compute_mc,
       API_MULCACHE)
      [`read RDI s`; `read RSI s`; `read RDX s`; f'] k gl)) gl;;

let API_MC_POST_TAC v bn x kk =
  let goal = vsubst [mk_var(v,`:num->int16`),`v:num->int16`;
                     x,`x:num->int16`]
   `!p. p < 128
        ==> (ival((v:num->int16) p) ==
             avx2_mulcache (ival o (x:num->int16)) p)
            (mod &3329) /\
            abs(ival(v p)) <= &3328` in
  API_POST16_TAC v bn 128 kk goal []
   (fun _ -> CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP_TAC[]);;

(*** basemul_kK of the k polynomials at RSI by those at RDX with their
 *** mulcaches at RCX, into RDI
 ***)

(*** The side goals of a call left by the simulation: the quantified facts
 *** of the precondition with addresses N + m + 2 * i
 ***)

let API_SIDE_TAC (asl,w as gl) =
  if (try fst(dest_const(fst(strip_comb w))) = "eventually"
      with Failure _ -> false)
  then ALL_TAC gl
  else (REWRITE_TAC[ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
        ASM_REWRITE_TAC[] THEN NO_TAC) gl;;

let api_basemul_th k =
  match k with
    2 -> layout "mlkem_basemul_k2",mlkem_basemul_k2_mc,API_BASEMUL_K2
  | 3 -> layout "mlkem_basemul_k3",mlkem_basemul_k3_mc,API_BASEMUL_K3
  | _ -> layout "mlkem_basemul_k4",mlkem_basemul_k4_mc,API_BASEMUL_K4;;

let API_BASEMUL_CALL_TAC exec k kk gl =
  let ab,a = api_addr_parts(find_read_fact `RSI` kk gl)
  and bb,b = api_addr_parts(find_read_fact `RDX` kk gl)
  and tb,t = api_addr_parts(find_read_fact `RCX` kk gl) in
  let eta f = try rand(concl(ETA_CONV f)) with Failure _ -> f in
  let fs = flat(map (fun c ->
    [eta(api_fun16_at (ab,a + 512 * c) 256 kk gl);
     eta(api_fun16_at (bb,b + 512 * c) 256 kk gl);
     eta(api_fun16_at (tb,t + 256 * c) 128 kk gl)]) (0--(k-1))) in
  let xs = map (fun c -> el (3 * c) fs) (0--(k-1)) in
  let lo,mc,th = api_basemul_th k in
  (MAP_EVERY (fun x -> API_GHOST_BOUND_TAC x `(&2 pow 12):int` FIELD12_BOUND)
             xs THEN
   API_ALIGNED_TAC kk THEN
   NATIVE2_CALL_TAC mlkem_native2_image_mc exec (lo,mc,th)
    ([`read RSI s`; `read RDX s`; `read RCX s`; `read RDI s`] @ fs) kk THEN
   API_SIDE_TAC) gl;;

(*** The post of basemul as ghost v for the buffer bn ***)

let API_BASEMUL_POST_TAC v bn kk (asl,w as gl) =
  let sv = state_of kk in
  let vt = mk_var(v,`:num->int16`) in
  let ispost c = is_forall c && free_in sv c && hascon "avx_order" c &&
                 api_has_addr bn c in
  let pth = find_asm ispost gl in
  let pv,pb = dest_forall(concl pth) in
  let rds = setify(find_terms (fun t ->
    try fst(dest_const(rator(rator t))) = "read" && rand t = sv
    with Failure _ -> false) pb) in
  let idx t = (* the index i of read(bytes16(base + N + 2 * i)) *)
    let x = rand(rand(rand(rand(lhand t)))) in
    if is_binary "+" x then rand(rand x) else rand x in
  let goal = mk_forall(pv,subst (map (fun t -> mk_comb(vt,idx t),t) rds) pb) in
  let isghost c =
    is_forall c && free_in sv c &&
    (try rator(rand(snd(dest_imp(snd(dest_forall c))))) = vt
     with Failure _ -> false) in
  let b0 = `avx_order(2 * p) < 256` and b1 = `avx_order(2 * p + 1) < 256` in
  (API_GHOST16_TAC v bn 256 kk THEN
   SUBGOAL_THEN goal ASSUME_TAC THENL
    [X_GEN_TAC `p:num` THEN DISCH_TAC THEN
     SUBGOAL_THEN (mk_conj(b0,b1)) STRIP_ASSUME_TAC THENL
      [ASM_SIMP_TAC[AVX_ORDER_UNORDER;
                    ARITH_RULE `p < 128 ==> 2 * p < 256 /\ 2 * p + 1 < 256`];
       ALL_TAC] THEN
     FIRST_ASSUM(fun gth ->
       if isghost(concl gth)
       then SIMP_TAC[GSYM gth; ASSUME b0; ASSUME b1] else NO_TAC) THEN
     FIRST_ASSUM(MATCH_MP_TAC o check (ispost o concl)) THEN
     ASM_REWRITE_TAC[];
     FIRST_X_ASSUM(fun th -> if ispost(concl th) then ALL_TAC else NO_TAC)])
  gl;;

(*** The inverse NTT of the polynomial at RDI ***)

let API_INTT_CALL_TAC exec k gl =
  let a = find_read_fact `RDI` k gl in
  (API_PRE16_TAC a 256 k THEN API_REG_PCADD_TAC `RSI` k THEN
   API_ALIGNED_TAC k THEN
   (fun gl ->
     let f = api_pre16_fun a k gl in
     let f' = try rand(concl(ETA_CONV f)) with Failure _ -> f in
     NATIVE2_CALL_TAC mlkem_native2_image_mc exec
      (layout "mlkem_intt_x86",mlkem_intt_mc,API_INTT)
      [`read RDI s`; `read RSI s`; f'] k gl)) gl;;

let API_INTT_POST_TAC v bn x kk =
  let goal = vsubst [mk_var(v,`:num->int16`),`v:num->int16`;
                     x,`x:num->int16`]
   `!i. i < 256
        ==> (ival((v:num->int16) i) ==
             avx2_inverse_ntt (ival o (x:num->int16)) i)
            (mod &3329) /\
            abs(ival(v i)) <= &26631` in
  API_POST16_TAC v bn 256 kk goal []
   (fun _ -> CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN SIMP_TAC[]);;

(*** sub_reduce and tomsg ***)

let API_SUB_REDUCE_CALL_TAC exec k gl =
  let a = find_read_fact `RDI` k gl and b = find_read_fact `RSI` k gl in
  let eta f = try rand(concl(ETA_CONV f)) with Failure _ -> f in
  let f = eta(api_fun16 a 256 k gl) and g = eta(api_fun16 b 256 k gl) in
  NATIVE2_CALL_TAC mlkem_native2_image_mc exec
   (layout "mlkem_sub_reduce",mlkem_sub_reduce_mc,
    MLKEM_SUB_REDUCE_SUBROUTINE_CORRECT)
   [`read RDI s`; `read RSI s`; f; g] k gl;;

let API_SUB_REDUCE_POST_TAC v bn x y k =
  let goal = vsubst [mk_var(v,`:num->int16`),`v:num->int16`;
                     x,`x:num->int16`; y,`y:num->int16`]
   `!i. i < 256
        ==> ival((v:num->int16) i) =
            ival(word_sub ((x:num->int16) i) ((y:num->int16) i)) rem &3329` in
  API_POST16_TAC v bn 256 k goal []
   (fun _ -> SIMP_TAC[]);;

let API_TOMSG_CALL_TAC exec kk gl =
  let a = find_read_fact `RSI` kk gl in
  let f = api_fun16 a 256 kk gl in
  let f' = try rand(concl(ETA_CONV f)) with Failure _ -> f in
  let remth = find_asm (fun c ->
    try let iv,body = dest_forall c in
        let _,eq = dest_imp body in
        lhand eq = mk_comb(`ival:int16->int`,mk_comb(f',iv)) &&
        can (find_term (fun t -> is_const t && name_of t = "rem")) (rand eq)
    with Failure _ -> false) gl in
  (NATIVE2_CALL_TAC mlkem_native2_image_mc exec
    (layout "mlkem_tomsg",mlkem_tomsg_mc,MLKEM_TOMSG_SUBROUTINE_CORRECT)
    [`read RDI s`; `read RSI s`; f'] kk THEN
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

(* ------------------------------------------------------------------------- *)
(* The zeroing loops of the frames (the zero macro with len >= 128): from    *)
(* the mov ecx,n at pc + lo - 5 before the loop at pc + lo, with RDI = a, to *)
(* the end of the loop, zeroing 128 * n bytes at a. The loops of a function  *)
(* are found in the image by their code.                                     *)
(* ------------------------------------------------------------------------- *)

let api_image_bytes =
  let l = dest_list(rand(concl mlkem_native2_image_mc)) in
  Array.of_list(map (fun t -> dest_small_numeral(rand t)) l);;

let api_zero_loops fname =
  let lo = layout fname and hi = layout fname + layout (fname^"_size") in
  let pat = [0xc5;0xfe;0x7f;0x07; 0xc5;0xfe;0x7f;0x47;0x20;
             0xc5;0xfe;0x7f;0x47;0x40; 0xc5;0xfe;0x7f;0x47;0x60;
             0x48;0x81;0xc7;0x80;0x00;0x00;0x00; 0xff;0xc9; 0x75;0xe2] in
  let at i = let rec ok j l = match l with
      [] -> true | x::t -> api_image_bytes.(i+j) = x && ok (j+1) t in
    ok 0 pat in
  let res = ref [] in
  for i = lo to hi - 30 do
    if at i && api_image_bytes.(i-5) = 0xb9 then
      let n = api_image_bytes.(i-4) + 256 * api_image_bytes.(i-3) in
      res := (i,n) :: !res
  done;
  rev !res;;

let api_zero_tm lo n =
  parse_term(Printf.sprintf
   "!a pc. nonoverlapping (a,%d) (word pc,mlkem_native2_image_size)
           ==> ensures x86
                (\\s. bytes_loaded s (word pc) mlkem_native2_image_mc /\\
                     read RIP s = word(pc + %d) /\\ read RDI s = a)
                (\\s. read RIP s = word(pc + %d) /\\
                     read RDI s = word_add a (word %d))
                (MAYCHANGE [RIP; RDI; RCX] ,, MAYCHANGE SOME_FLAGS ,,
                 MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,%d)])"
   (128 * n) (lo - 5) (lo + 30) (128 * n) (128 * n));;

let api_zero_counter n =
  let nn = mk_small_numeral n in
  prove(vsubst [nn,`n:num`]
   `!i. i < n
        ==> ((~(val(word_zx(word(n - i):int64):int32) = val(word 1:int32)) <=>
              i + 1 < n) /\
             word_zx(word_sub (word_zx(word(n - i):int64):int32) (word 1))
             :int64 = word(n - (i + 1)))`,
   CONV_TAC EXPAND_CASES_CONV THEN
   CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV)));;

let API_ZERO_LOOP exec (lo,n) =
  let cth = api_zero_counter n in
  let nn = mk_small_numeral n in
  prove(api_zero_tm lo n,
    REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
    ENSURES_WHILE_UP2_TAC nn (mk_binop `(+):num->num->num` `pc:num`
                                (mk_small_numeral lo))
     (mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral(lo + 30)))
     (vsubst [nn,`n:num`]
       `\i s. read RDI s = word_add a (word(128 * i)) /\
              read RCX s = word(n - i)`) THEN
    REPEAT CONJ_TAC THENL
     [ARITH_TAC;
      X86_SIM_TAC exec (1--1) THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[WORD_ADD_0];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      X86_SIM_TAC exec (1--7) THEN
      ASM_SIMP_TAC[cth] THEN
      CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; CONV_TAC WORD_RULE];
      X86_SIM_TAC exec [] THEN CONV_TAC NUM_REDUCE_CONV]);;

(*** Steps to RIP = pc + target (target < 0: until RIP is not in the image,
 *** after the return)
 ***)

let API_TO_PC_TAC exec target =
  let rec tac k gl =
    let off = get_pc_offset k gl in
    if off = target || off < 0 then ALL_TAC gl
    else (X86_STEPS_TAC exec [k+1] THEN tac (k+1)) gl in
  ON_STATE tac;;

(*** A zeroing loop at state k by its lemma zth ***)

let API_ZERO_STEP_TAC exec zth k =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native2_image_mc,exec,0,mlkem_native2_image_mc,zth)
   [`read RDI s`; `pc:num`] (k+1);;

(*** At the end: the frame base in the MAYCHANGE assumption as
 *** stackpointer + delta, with its offsets combined
 ***)

let WORD_SUB_SUB_NUM = prove
 (`!x a b. word_sub (word_sub x (word a)) (word b):int64 =
           word_sub x (word(a + b))`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let API_FB_SUB = prove
 (`!stk d c. c <= d
             ==> word_sub (word_add stk (word d)) (word c):int64 =
                 word_add stk (word(d - c))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WORD_SUB] THEN CONV_TAC WORD_RULE);;

let API_EXPAND_FB_TAC (asl,w as gl) =
  let eth = find_asm (fun c ->
    c = `word_add stackpointer (word delta) = fb:int64`) gl in
  let dlo = find_asm (fun c -> is_binary "<=" c && rand c = `delta:num` &&
                               is_numeral(lhand c)) gl in
  let fbsub tm =
    let c = rand(rand tm) in
    let cth = MP (ARITH_RULE(mk_imp(concl dlo,
                mk_binop `(<=):num->num->bool` c `delta:num`))) dlo in
    MP (SPECL [`stackpointer:int64`; `delta:num`; c] API_FB_SUB) cth in
  let pat = `word_sub (word_add stackpointer (word delta)) (word c):int64` in
  RULE_ASSUM_TAC(fun th ->
    if maychange_term(concl th) then
      let th1 = REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]
                 (REWRITE_RULE[SYM eth]
                   (CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
                     (REWRITE_RULE[WORD_SUB_SUB_NUM] th))) in
      let subs = setify(find_terms (fun t -> can (term_match [] pat) t &&
                                             is_numeral(rand(rand t)))
                          (concl th1)) in
      REWRITE_RULE (map fbsub subs) th1
    else th) gl;;

(*** The block function \j. EL j [X0; ...] of the ghosts X0, ... ***)

let api_blk names =
  let lst = mk_list(map (fun n -> mk_var(n,`:num->int16`)) names,
                    `:num->int16`) in
  mk_abs(`j:num`,list_mk_icomb "EL" [`j:num`; lst]);;

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

(*** The end of pke_decrypt: the message from the blocked K-PKE theorem
 *** bth, then the final state
 ***)

let PD_FINAL_TAC k bth kk gl =
  let sv = state_of kk in
  let blk x = api_blk (map (fun j -> x^string_of_int j) (0--(k-1))) in
  let gv n = mk_var(n,`:num->int16`) in
  let th = ISPECL [`dk:byte list`; `c:byte list`; blk "UD"; gv "VD";
                   blk "SM"; blk "UM"; blk "CM"; gv "WM"; gv "WI"; gv "VR"]
                  bth in
  let mgoal = vsubst [sv,`s:x86state`]
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

(* ------------------------------------------------------------------------- *)
(* pke_decrypt for k: the frame (u, its mulcaches, v, s, w), the entry, the  *)
(* calls with their posts, the zeroing, the message from the K-PKE theorem.  *)
(* ------------------------------------------------------------------------- *)

let pd_u k = 0;;
let pd_uc k = 512 * k;;
let pd_v k = pd_uc k + 256 * k;;
let pd_s k = pd_v k + 512;;
let pd_w k = pd_s k + 512 * k;;
let pd_frame k = pd_w k + 512;;
let pd_stack k = pd_frame k + 87;;

let MLKEM_NATIVE2_PKE_DECRYPT_CORRECT_TAC k ex =
  let nm = api_param k in
  let lo = layout(nm ^ "_pke_decrypt") and hi = layout(nm ^ "_dec") in
  let next = API_TO_CALL_TAC ex lo hi in
  let zs = api_zero_loops (nm ^ "_pke_decrypt") in
  let zl = API_ZERO_LOOP ex (hd zs) in
  let bth = match k with
      2 -> X86_KPKE_DECRYPT_K2 | 3 -> X86_KPKE_DECRYPT_K3
    | _ -> X86_KPKE_DECRYPT_K4 in
  let fb = `fb:int64` and gv n = mk_var(n,`:num->int16`) in
  let du = api_du k and dv = api_dv k in
  let cv = `c:byte list` and dkv = `dk:byte list` in
  let ns x j = x ^ string_of_int j in
  API_ENTRY_TAC ex
   [`mp:int64`; `ct:int64`; `sk:int64`; `c:byte list`; `dk:byte list`;
    `pc:num`] (pd_stack k) (pd_frame k) THEN
  MAP_EVERY (fun j ->
    next THEN
    ON_STATE(API_DECOMPRESS_CALL_TAC ex du cv (32 * du * j) (32 * du)) THEN
    API_RSP_TAC THEN
    ON_STATE(API_DECOMPRESS_POST_TAC (ns "UD" j) (fb,512 * j) cv du j) THEN
    next THEN ON_STATE(API_FROMBYTES_CALL_TAC ex dkv j) THEN API_RSP_TAC THEN
    ON_STATE(API_FROMBYTES_POST_TAC (ns "SM" j) (fb,pd_s k + 512 * j) dkv j))
   (0--(k-1)) THEN
  next THEN
  ON_STATE(API_DECOMPRESS_CALL_TAC ex dv cv (32 * du * k) (32 * dv)) THEN
  API_RSP_TAC THEN
  ON_STATE(API_DECOMPRESS_V_POST_TAC "VD" (fb,pd_v k) cv dv
            (32 * du * k) (32 * dv)) THEN
  MAP_EVERY (fun j ->
    next THEN
    API_GHOST_BOUND_TAC (gv(ns "UD" j)) `&8191:int` DECOMPRESS_BOUND THEN
    ON_STATE(API_NTT_CALL_TAC ex) THEN API_RSP_TAC THEN
    ON_STATE(API_NTT_POST_TAC (ns "UM" j) (fb,512 * j) (gv(ns "UD" j))))
   (0--(k-1)) THEN
  MAP_EVERY (fun j ->
    next THEN ON_STATE(API_MULCACHE_CALL_TAC ex) THEN API_RSP_TAC THEN
    ON_STATE(API_MC_POST_TAC (ns "CM" j) (fb,pd_uc k + 256 * j)
              (gv(ns "UM" j))))
   (0--(k-1)) THEN
  next THEN ON_STATE(API_BASEMUL_CALL_TAC ex k) THEN API_RSP_TAC THEN
  ON_STATE(API_BASEMUL_POST_TAC "WM" (fb,pd_w k)) THEN
  next THEN ON_STATE(API_INTT_CALL_TAC ex) THEN API_RSP_TAC THEN
  ON_STATE(API_INTT_POST_TAC "WI" (fb,pd_w k) (gv "WM")) THEN
  next THEN ON_STATE(API_SUB_REDUCE_CALL_TAC ex) THEN API_RSP_TAC THEN
  ON_STATE(API_SUB_REDUCE_POST_TAC "VR" (fb,pd_v k) (gv "VD") (gv "WI")) THEN
  next THEN ON_STATE(API_TOMSG_CALL_TAC ex) THEN API_RSP_TAC THEN
  API_TO_PC_TAC ex (fst(hd zs) - 5) THEN ON_STATE(API_ZERO_STEP_TAC ex zl) THEN
  API_TO_PC_TAC ex (-1) THEN
  ON_STATE(PD_FINAL_TAC k bth) THEN
  API_EXPAND_FB_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* K-PKE encryption and key generation from the x86 kernels, as for          *)
(* decryption above.                                                        *)
(* ------------------------------------------------------------------------- *)

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

(*** The coefficients of SampleNTT from a 32-byte seed and two bytes ***)

let API_SAMPLE_SEED = prove
 (`!rho (x:byte) (y:byte) n.
        LENGTH rho = 32 /\ n < 256
        ==> ival(iword(mlkem_sample_ntt (APPEND rho [x; y]) n):int16) =
            mlkem_sample_ntt (APPEND rho [x; y]) n /\
            mlkem_sample_ntt (APPEND rho [x; y]) n < &3329`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`APPEND rho [x:byte; y]`; `n:num`] API_SAMPLE_NTT_BOUNDS) THEN
  ASM_SIMP_TAC[MLKEM_SAMPLENTT_TERMINATES_SEED]);;

(*** The blocked statement of encryption with the x86 kernels ***)

let x86_kpke_encrypt_tm k =
  let ks = string_of_int k and es = string_of_int(api_eta1 k) in
  let n x = string_of_int x in
  let rho = "(mlkem_slice "^n(384 * k)^" 32 ek)" in
  let a c t = "ival(iword(mlkem_sample_ntt (APPEND "^rho^
              " [word q; word "^n c^"]) (avx_unorder("^t^"))):int16)" in
  let pm c = "(if EVEN p then ival((CM:num->num->int16) "^n c^
             " (avx2_mcix p)) else --ival(CM "^n c^" (avx2_mcix p)))" in
  let o1 = "avx_order(2 * p + 1)" and o0 = "avx_order(2 * p)" in
  let ev c = "("^a c o1^" * "^pm c^" + "^a c o0^
             " * ival((YM:num->num->int16) "^n c^" ("^o0^")))"
  and od c = "("^a c o1^" * ival((YM:num->num->int16) "^n c^" ("^o0^")) + "^
             a c o0^" * ival(YM "^n c^" ("^o1^")))"
  and tev c = "(ival((TM:num->num->int16) "^n c^" ("^o1^")) * "^pm c^
              " + ival(TM "^n c^" ("^o0^")) * ival(YM "^n c^" ("^o0^")))"
  and tod c = "(ival((TM:num->num->int16) "^n c^" ("^o1^")) * "^
              "ival(YM "^n c^" ("^o0^")) + "^
              "ival(TM "^n c^" ("^o0^")) * ival(YM "^n c^" ("^o1^")))" in
  let sum f = String.concat " + " (map f (rev(0--(k-1)))) in
  let du = api_du k and dv = api_dv k in
  let p2 x = n(1 lsl x) in
  parse_term(
   "!ek m r (TM:num->num->int16) (YM:num->num->int16) "^
   "(CM:num->num->int16) (MU:num->int16) (UM:num->num->int16) "^
   "(VM:num->int16) (U1:num->num->int16) (V1:num->int16) "^
   "(U3:num->num->int16) (V2:num->int16) (V4:num->int16). "^
   "(!j i. j < "^ks^" /\\ i < 256 ==> "^
   "  TM j i = word((num_of_bytelist ek DIV "^
   "    2 EXP (12 * (256 * j + avx_unorder i))) MOD 2 EXP 12)) /\\ "^
   "(!j i. j < "^ks^" /\\ i < 256 ==> "^
   "  (ival(YM j i) == avx2_forward_ntt (\\n. ival(iword(mlkem_cbd_coeff "^
   es^" (mlkem_prf "^es^" r (word j)) n):int16)) i) (mod &3329) /\\ "^
   "  abs(ival(YM j i)) <= &23594) /\\ "^
   "(!j p. j < "^ks^" /\\ p < 128 ==> "^
   "  (ival(CM j p) == avx2_mulcache (ival o YM j) p) (mod &3329) /\\ "^
   "  abs(ival(CM j p)) <= &3328) /\\ "^
   "(!i. i < 256 ==> "^
   "  MU i = word((3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1) "^
   "             DIV 2)) /\\ "^
   "(!q p. q < "^ks^" /\\ p < 128 ==> "^
   "  (ival(UM q ("^o0^")) == &169 * ("^sum ev^")) (mod &3329) /\\ "^
   "  (ival(UM q ("^o1^")) == &169 * ("^sum od^")) (mod &3329)) /\\ "^
   "(!p. p < 128 ==> "^
   "  (ival(VM("^o0^")) == &169 * ("^sum tev^")) (mod &3329) /\\ "^
   "  (ival(VM("^o1^")) == &169 * ("^sum tod^")) (mod &3329)) /\\ "^
   "(!j i. j < "^ks^" /\\ i < 256 ==> "^
   "  (ival(U1 j i) == avx2_inverse_ntt (ival o UM j) i) (mod &3329) /\\ "^
   "  abs(ival(U1 j i)) <= &26631) /\\ "^
   "(!i. i < 256 ==> (ival(V1 i) == avx2_inverse_ntt (ival o VM) i) "^
   "  (mod &3329) /\\ abs(ival(V1 i)) <= &26631) /\\ "^
   "(!j i. j < "^ks^" /\\ i < 256 ==> "^
   "  ival(U3 j i) = ival(word_add (U1 j i) (iword(mlkem_cbd_coeff 2 "^
   "   (mlkem_prf 2 r (word("^ks^" + j))) i))) rem &3329) /\\ "^
   "(!i. i < 256 ==> "^
   "  ival(V2 i) = ival(word_add (V1 i) (iword(mlkem_cbd_coeff 2 "^
   "   (mlkem_prf 2 r (word "^n(2 * k)^")) i))) rem &3329) /\\ "^
   "(!i. i < 256 ==> ival(V4 i) = ival(word_add (V2 i) (MU i)) rem &3329) "^
   "==> nsum {i | i < "^n(256 * k)^"} "^
   "      (\\i. (("^p2(du+1)^" * val(U3 (i DIV 256) (i MOD 256)) + 3329) "^
   "           DIV 6658) MOD "^p2 du^" * 2 EXP ("^n du^" * i)) + "^
   "    2 EXP (8 * "^n(32 * du * k)^") * "^
   "    nsum {i | i < 256} "^
   "      (\\i. (("^p2(dv+1)^" * val(V4 i) + 3329) DIV 6658) MOD "^p2 dv^
   "           * 2 EXP ("^n dv^" * i)) = "^
   "    num_of_bytelist(kpke_encrypt "^api_param k^" ek m r)");;

let API_SAMPLE_SEED_LT = prove
 (`!rho (x:byte) (y:byte) n.
        LENGTH rho = 32 /\ n < 256
        ==> mlkem_sample_ntt (APPEND rho [x; y]) n < &3329`,
  SIMP_TAC[API_SAMPLE_SEED]);;

let API_IVAL_SAMPLE = prove
 (`!l (x:byte) (y:byte) a n.
        n < 256
        ==> ival(iword(mlkem_sample_ntt
                        (APPEND (mlkem_slice a 32 l) [x; y]) n):int16) =
            mlkem_sample_ntt (APPEND (mlkem_slice a 32 l) [x; y]) n`,
  SIMP_TAC[API_SAMPLE_SEED; LENGTH_MLKEM_SLICE]);;

let X86_KPKE_ENCRYPT_TAC k bth =
  let kn = mk_small_numeral k and ks = string_of_int k in
  let e1 = parse_term("\\j i. iword(mlkem_cbd_coeff 2 (mlkem_prf 2 r "^
                      "(word("^ks^" + j))) i):int16")
  and e2 = parse_term("\\i. iword(mlkem_cbd_coeff 2 (mlkem_prf 2 r "^
                      "(word "^string_of_int(2 * k)^")) i):int16") in
  let mcbound =
    SUBGOAL_THEN
     (vsubst [kn,`k:num`]
       `!c. c < k
            ==> abs(ival((CM:num->num->int16) c (avx2_mcix p))) <= &3328`)
    ASSUME_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[AVX2_MCIX_LT]; ALL_TAC] in
  let small = ARITH_RULE `0 < 4 /\ 1 < 4 /\ 2 < 4 /\ 3 < 4 /\
                          0 < 3 /\ 1 < 3 /\ 2 < 3 /\ 0 < 2 /\ 1 < 2` in
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC bth THEN
  MAP_EVERY EXISTS_TAC
   [`\j i. (TM:num->num->int16) j (avx_order i)`;
    `\j i. (YM:num->num->int16) j (avx_order i)`;
    mk_comb(api_mc_view,`CM:num->num->int16`); e1; e2; `MU:num->int16`;
    `\j n. (UM:num->num->int16) j (avx_order n)`;
    `\n. (VM:num->int16)(avx_order n)`; `U1:num->num->int16`;
    `V1:num->int16`; `V2:num->int16`] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [MATCH_MP_TAC API_SAMPLE_SEED_LT THEN ASM_REWRITE_TAC[LENGTH_MLKEM_SLICE];
    ASM_SIMP_TAC[AVX_ORDER_UNORDER];
    FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `avx_order i`] o
      check (hascon "avx2_forward_ntt" o concl)) THEN
    ASM_SIMP_TAC[AVX_ORDER_UNORDER; AVX2_FORWARD_NTT_UNORDER] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MLKEM_NATIVE_NTT_CONG THEN
    EXISTS_TAC (mk_abs(`n:num`,vsubst [mk_small_numeral(api_eta1 k),`eta:num`]
      `iword(mlkem_cbd_coeff eta (mlkem_prf eta r (word j)) n):int16`)) THEN
    ASM_REWRITE_TAC[MLKEM_CBD_IN_RQ] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(SPECL [mk_small_numeral(api_eta1 k);
                  vsubst [mk_small_numeral(api_eta1 k),`eta:num`]
                    `mlkem_prf eta r (word j)`; `n:num`] API_CBD_CONG) THEN
    ASM_REWRITE_TAC[ARITH_EQ] THEN SIMP_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `avx2_mcix p`] o
      check (hascon "avx2_mulcache" o concl)) THEN
    ASM_SIMP_TAC[AVX2_MCIX_LT] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[IVAL_MC_VIEW] THEN
    MP_TAC(ISPECL [`ival o (YM:num->num->int16) j`; `p:num`]
      AVX2_MULCACHE_PAIR) THEN
    ASM_REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      hascon "avx2_mulcache" (concl th) && not(is_forall(concl th)))) THEN
    REWRITE_TAC[MC_SIGN_CONG];
    MATCH_MP_TAC API_CBD_CONG THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC API_CBD_CONG THEN ASM_REWRITE_TAC[];
    mcbound THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`q:num`; `p:num`] o
      check (hascon "mlkem_sample_ntt" o concl)) THEN
    ASM_SIMP_TAC[IVAL_MC_VIEW; small; AVX_ORDER_UNORDER; API_IVAL_SAMPLE;
                 ARITH_RULE `p < 128 ==> 2 * p < 256 /\ 2 * p + 1 < 256`];
    mcbound THEN ASM_SIMP_TAC[IVAL_MC_VIEW; small];
    FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `i:num`] o
      check (fun th -> hascon "avx2_inverse_ntt" (concl th) &&
                       length(fst(strip_forall(concl th))) = 2)) THEN
    ASM_REWRITE_TAC[AVX2_INVERSE_NTT_ORDER; o_THM];
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o
      check (fun th -> hascon "avx2_inverse_ntt" (concl th) &&
                       length(fst(strip_forall(concl th))) = 1)) THEN
    ASM_REWRITE_TAC[AVX2_INVERSE_NTT_ORDER; o_THM]];;

let X86_KPKE_ENCRYPT_K2 = time prove
 (x86_kpke_encrypt_tm 2, X86_KPKE_ENCRYPT_TAC 2 KPKE_ENCRYPT_K2_BLOCKS);;

let X86_KPKE_ENCRYPT_K3 = time prove
 (x86_kpke_encrypt_tm 3, X86_KPKE_ENCRYPT_TAC 3 KPKE_ENCRYPT_K3_BLOCKS);;

let X86_KPKE_ENCRYPT_K4 = time prove
 (x86_kpke_encrypt_tm 4, X86_KPKE_ENCRYPT_TAC 4 KPKE_ENCRYPT_K4_BLOCKS);;

(*** The blocked statement of key generation with the x86 kernels ***)

let x86_kpke_keygen_tm k =
  let ks = string_of_int k and es = string_of_int(api_eta1 k) in
  let n x = string_of_int x in
  let a c t = "ival(iword(mlkem_sample_ntt (APPEND rho [word "^n c^
              "; word r]) (avx_unorder("^t^"))):int16)" in
  let pm c = "(if EVEN p then ival((CM:num->num->int16) "^n c^
             " (avx2_mcix p)) else --ival(CM "^n c^" (avx2_mcix p)))" in
  let o1 = "avx_order(2 * p + 1)" and o0 = "avx_order(2 * p)" in
  let ev c = "("^a c o1^" * "^pm c^" + "^a c o0^
             " * ival((SM:num->num->int16) "^n c^" ("^o0^")))"
  and od c = "("^a c o1^" * ival((SM:num->num->int16) "^n c^" ("^o0^")) + "^
             a c o0^" * ival(SM "^n c^" ("^o1^")))" in
  let sum f = String.concat " + " (map f (rev(0--(k-1)))) in
  let noise v off =
   "(!j i. j < "^ks^" /\\ i < 256 ==> "^
   "  (ival("^v^" j i) == avx2_forward_ntt (\\n. ival(iword(mlkem_cbd_coeff "^
   es^" (mlkem_prf "^es^" sigma (word("^off^"j))) n):int16)) i) "^
   "  (mod &3329) /\\ abs(ival("^v^" j i)) <= &23594) /\\ " in
  parse_term(
   "!d rho sigma (SM:num->num->int16) (EM:num->num->int16) "^
   "(CM:num->num->int16) (PM:num->num->int16) (PU:num->num->int16) "^
   "(TR:num->num->int16) (SR:num->num->int16). "^
   "mlkem_g(APPEND d [word "^ks^"]) = rho,sigma /\\ "^
   noise "SM" "" ^ noise "EM" (ks^" + ") ^
   "(!j p. j < "^ks^" /\\ p < 128 ==> "^
   "  (ival(CM j p) == avx2_mulcache (ival o SM j) p) (mod &3329) /\\ "^
   "  abs(ival(CM j p)) <= &3328) /\\ "^
   "(!r p. r < "^ks^" /\\ p < 128 ==> "^
   "  (ival(PM r ("^o0^")) == &169 * ("^sum ev^")) (mod &3329) /\\ "^
   "  (ival(PM r ("^o1^")) == &169 * ("^sum od^")) (mod &3329)) /\\ "^
   "(!r i. r < "^ks^" /\\ i < 256 ==> "^
   "  (ival(PU r i) == &65536 * ival(PM r i)) (mod &3329) /\\ "^
   "  abs(ival(PU r i)) <= &3328) /\\ "^
   "(!r i. r < "^ks^" /\\ i < 256 ==> "^
   "  ival(TR r i) = ival(word_add (PU r i) (EM r i)) rem &3329) /\\ "^
   "(!r i. r < "^ks^" /\\ i < 256 ==> ival(SR r i) = ival(SM r i) rem &3329) "^
   "==> num_of_wordlist(MAP (word_zx:int16->12 word) "^
   "      (list_of_seq (\\i. TR (i DIV 256) (avx_order(i MOD 256))) "^
   n(256 * k)^")) + "^
   "    2 EXP (8 * "^n(384 * k)^") * num_of_bytelist rho = "^
   "    num_of_bytelist(FST(kpke_keygen "^api_param k^" d)) /\\ "^
   "    num_of_wordlist(MAP (word_zx:int16->12 word) "^
   "      (list_of_seq (\\i. SR (i DIV 256) (avx_order(i MOD 256))) "^
   n(256 * k)^")) = "^
   "    num_of_bytelist(SND(kpke_keygen "^api_param k^" d))");;

let API_IVAL_SAMPLE_RHO = prove
 (`!rho (x:byte) (y:byte) n.
        LENGTH rho = 32 /\ n < 256
        ==> ival(iword(mlkem_sample_ntt (APPEND rho [x; y]) n):int16) =
            mlkem_sample_ntt (APPEND rho [x; y]) n`,
  SIMP_TAC[API_SAMPLE_SEED]);;

let X86_KPKE_KEYGEN_TAC k bth =
  let kn = mk_small_numeral k in
  let es = mk_small_numeral(api_eta1 k) in
  let mcbound =
    SUBGOAL_THEN
     (vsubst [kn,`k:num`]
       `!c. c < k
            ==> abs(ival((CM:num->num->int16) c (avx2_mcix p))) <= &3328`)
    ASSUME_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[AVX2_MCIX_LT]; ALL_TAC] in
  let small = ARITH_RULE `0 < 4 /\ 1 < 4 /\ 2 < 4 /\ 3 < 4 /\
                          0 < 3 /\ 1 < 3 /\ 2 < 3 /\ 0 < 2 /\ 1 < 2` in
  let ntt_tac v off =
    FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `avx_order i`] o
      check (fun th -> hascon "avx2_forward_ntt" (concl th) &&
                       can (find_term ((=) v)) (concl th))) THEN
    ASM_SIMP_TAC[AVX_ORDER_UNORDER; AVX2_FORWARD_NTT_UNORDER] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MLKEM_NATIVE_NTT_CONG THEN
    EXISTS_TAC (mk_abs(`n:num`,vsubst [es,`eta:num`; off,`x:num`]
      `iword(mlkem_cbd_coeff eta (mlkem_prf eta sigma (word x)) n)
       :int16`)) THEN
    ASM_REWRITE_TAC[MLKEM_CBD_IN_RQ] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(SPECL [es; vsubst [es,`eta:num`; off,`x:num`]
                    `mlkem_prf eta sigma (word x)`; `n:num`] API_CBD_CONG) THEN
    ASM_REWRITE_TAC[ARITH_EQ] THEN SIMP_TAC[] in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH(rho:byte list) = 32` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o AP_TERM `\x:byte list#byte list. LENGTH(FST x)` o
      check (hascon "mlkem_g" o concl)) THEN
    REWRITE_TAC[LENGTH_MLKEM_G] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d:byte list`; `rho:byte list`; `sigma:byte list`;
    `\j i. (SM:num->num->int16) j (avx_order i)`;
    `\j i. (EM:num->num->int16) j (avx_order i)`;
    mk_comb(api_mc_view,`CM:num->num->int16`);
    `\j n. (PM:num->num->int16) j (avx_order n)`;
    `\j n. (PU:num->num->int16) j (avx_order n)`;
    `\j n. (TR:num->num->int16) j (avx_order n)`;
    `\j n. (SR:num->num->int16) j (avx_order n)`] bth) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
    STRIP_TAC THENL
     [MATCH_MP_TAC API_SAMPLE_SEED_LT THEN ASM_REWRITE_TAC[];
      ntt_tac `SM:num->num->int16` `j:num`;
      ntt_tac `EM:num->num->int16` (mk_binop `(+):num->num->num` kn `j:num`);
      FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `avx2_mcix p`] o
        check (hascon "avx2_mulcache" o concl)) THEN
      ASM_SIMP_TAC[AVX2_MCIX_LT] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[IVAL_MC_VIEW] THEN
      MP_TAC(ISPECL [`ival o (SM:num->num->int16) j`; `p:num`]
        AVX2_MULCACHE_PAIR) THEN
      ASM_REWRITE_TAC[o_THM] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th ->
        hascon "avx2_mulcache" (concl th) && not(is_forall(concl th)))) THEN
      REWRITE_TAC[MC_SIGN_CONG];
      mcbound THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`r:num`; `p:num`] o
        check (hascon "mlkem_sample_ntt" o concl)) THEN
      ASM_SIMP_TAC[IVAL_MC_VIEW; small; AVX_ORDER_UNORDER; API_IVAL_SAMPLE_RHO;
                   ARITH_RULE `p < 128 ==> 2 * p < 256 /\ 2 * p + 1 < 256`];
      ASM_SIMP_TAC[AVX_ORDER_UNORDER];
      ASM_SIMP_TAC[AVX_ORDER_UNORDER];
      ASM_SIMP_TAC[AVX_ORDER_UNORDER]];
    SIMP_TAC[]];;

let X86_KPKE_KEYGEN_K2 = time prove
 (x86_kpke_keygen_tm 2, X86_KPKE_KEYGEN_TAC 2 KPKE_KEYGEN_K2_BLOCKS);;

let X86_KPKE_KEYGEN_K3 = time prove
 (x86_kpke_keygen_tm 3, X86_KPKE_KEYGEN_TAC 3 KPKE_KEYGEN_K3_BLOCKS);;

let X86_KPKE_KEYGEN_K4 = time prove
 (x86_kpke_keygen_tm 4, X86_KPKE_KEYGEN_TAC 4 KPKE_KEYGEN_K4_BLOCKS);;

(* ------------------------------------------------------------------------- *)
(* pke_encrypt: vectors stored polynomial by polynomial, the noise and the   *)
(* matrix as facts per polynomial, and the tactics for its calls.            *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES_MAP_BLOCKS = prove
 (`!a m (g:int16->N word) (f:num->num->int16) s:x86state k.
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

let READ_MEMORY_BYTES_NSUM_BLOCKS = prove
 (`!a m d (g:num->num->num) s:x86state k.
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

(*** The noise as facts per polynomial at state k ***)

let API_SPLIT_NOISE_TAC k =
  let sv = state_of k in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_forall c && free_in sv c && length(fst(strip_forall c)) = 2 &&
       hascon "mlkem_cbd_coeff" c
    then
      let th1 = CONV_RULE EXPAND_CASES_CONV
                 (REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM] th) in
      let th2 = REWRITE_RULE[ADD_CLAUSES]
                 (CONV_RULE(DEPTH_CONV NUM_RED_CONV)
                   (REWRITE_RULE[ADD_ASSOC]
                     (CONV_RULE(DEPTH_CONV NUM_RED_CONV) th1))) in
      MAP_EVERY ASSUME_TAC (CONJUNCTS th2)
    else NO_TAC);;

(*** The polynomial (r,c) of the matrix at state k as a buffer fact ***)

let API_MATRIX_POLY_TAC r c k gl =
  let sv = state_of k in
  let ismat c = is_forall c && free_in sv c &&
    length(fst(strip_forall c)) = 3 && hascon "mlkem_sample_ntt" c in
  let th = find_asm ismat gl in
  let th1 = SPECL [mk_small_numeral r; mk_small_numeral c] th in
  let th2 = CONV_RULE NUM_REDUCE_CONV th1 in
  let th3 = REWRITE_RULE[ADD_CLAUSES]
              (CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD_ASSOC] th2)) in
  ASSUME_TAC th3 gl;;

(*** Bounds for the inputs of the NTT (noise) and basemul (matrix) ***)

let API_CBD_NTT_BOUND = prove
 (`!eta b i. (eta = 2 \/ eta = 3) /\ i < 256
             ==> abs(ival(iword(mlkem_cbd_coeff eta b i):int16)) <= &8191`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`eta:num`; `b:byte list`; `i:num`] API_CBD_CONG) THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN INT_ARITH_TAC);;

let API_SAMPLE_ABS_BOUND = prove
 (`!rho (x:byte) (y:byte) t.
        LENGTH rho = 32 /\ t < 256
        ==> abs(ival(iword(mlkem_sample_ntt (APPEND rho [x; y])
                                            (avx_unorder t)):int16))
            <= &2 pow 12`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`APPEND rho [x:byte; y]`; `avx_unorder t`]
    API_SAMPLE_NTT_BOUNDS) THEN
  ASM_SIMP_TAC[MLKEM_SAMPLENTT_TERMINATES_SEED; AVX_ORDER_UNORDER] THEN
  INT_ARITH_TAC);;

(*** The bound !i. i < 256 ==> abs(ival(f i)) <= b, f a lambda or a
 *** ghost, by the tactic tac after beta-reduction
 ***)

let api_beta t = try rand(concl(BETA_CONV t)) with Failure _ -> t;;

let API_FUN_BOUND_TAC f b tac =
  let iv = `i:num` in
  let body = mk_binop `(<=):int->int->bool`
    (mk_comb(`abs:int->int`,
             mk_comb(`ival:int16->int`,api_beta(mk_comb(f,iv)))))
    b in
  let goal = mk_forall(iv,mk_imp(`i < 256`,body)) in
  SUBGOAL_THEN goal ASSUME_TAC THENL
   [X_GEN_TAC iv THEN DISCH_TAC THEN tac; ALL_TAC];;

let API_NOISE_BOUND_TAC f =
  API_FUN_BOUND_TAC f `&8191:int`
   (MATCH_MP_TAC API_CBD_NTT_BOUND THEN ASM_REWRITE_TAC[ARITH_EQ]);;

let API_MATRIX_BOUND_TAC f =
  API_FUN_BOUND_TAC f `(&2 pow 12):int`
   (MATCH_MP_TAC API_SAMPLE_ABS_BOUND THEN
    ASM_REWRITE_TAC[LENGTH_MLKEM_SLICE]);;

(*** frommsg of the message (32 bytes known as num_of_bytelist m) at RSI ***)

let API_FROMMSG_CALL_TAC exec m kk gl =
  let n = mk_comb(`num_of_bytelist`,m) in
  (API_ALIGNED_TAC kk THEN
   NATIVE2_CALL_TAC mlkem_native2_image_mc exec
    (layout "mlkem_frommsg",mlkem_frommsg_mc,MLKEM_FROMMSG_SUBROUTINE_CORRECT)
    [`read RDI s`; `read RSI s`; n] kk) gl;;

let API_FROMMSG_POST_TAC v bn m kk =
  let vt = mk_var(v,`:num->int16`) in
  let goal = vsubst [vt,`v:num->int16`; m,`m:byte list`]
   `!i. i < 256
        ==> (v:num->int16) i =
            word((3329 * (num_of_bytelist m DIV 2 EXP i) MOD 2 + 1) DIV 2)` in
  API_POST16_TAC v bn 256 kk goal [] (fun _ -> SIMP_TAC[]);;

(*** The NTT post for the noise (input a lambda) ***)

let API_NTT_POST_LAM_TAC v bn x kk =
  let vt = mk_var(v,`:num->int16`) in
  let f = mk_abs(`n:num`,
    mk_comb(`ival:int16->int`,api_beta(mk_comb(x,`n:num`)))) in
  let goal = vsubst [vt,`v:num->int16`; f,`f:num->int`]
   `!i. i < 256
        ==> (ival((v:num->int16) i) == avx2_forward_ntt f i) (mod &3329) /\
            abs(ival(v i)) <= &23594` in
  API_POST16_TAC v bn 256 kk goal []
   (fun _ -> CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[o_DEF] THEN
             CONV_TAC(DEPTH_CONV BETA_CONV) THEN SIMP_TAC[]);;

(*** add_reduce of the polynomials at RDI and RSI, in place at RDI ***)

let API_ADD_REDUCE_CALL_TAC exec k gl =
  let a = find_read_fact `RDI` k gl and b = find_read_fact `RSI` k gl in
  let eta f = try rand(concl(ETA_CONV f)) with Failure _ -> f in
  let f = eta(api_fun16 a 256 k gl) and g = eta(api_fun16 b 256 k gl) in
  NATIVE2_CALL_TAC mlkem_native2_image_mc exec
   (layout "mlkem_add_reduce",mlkem_add_reduce_mc,
    MLKEM_ADD_REDUCE_SUBROUTINE_CORRECT)
   [`read RDI s`; `read RSI s`; f; g] k gl;;

let API_ADD_REDUCE_POST_TAC v bn x y k =
  let goal = vsubst [mk_var(v,`:num->int16`),`v:num->int16`;
                     x,`x:num->int16`; y,`y:num->int16`]
   `!i. i < 256
        ==> ival((v:num->int16) i) =
            ival(word_add ((x:num->int16) i) ((y:num->int16) i)) rem &3329` in
  let goal = rand(concl(DEPTH_CONV BETA_CONV goal)) in
  API_POST16_TAC v bn 256 k goal []
   (fun _ -> CONV_TAC(DEPTH_CONV BETA_CONV) THEN SIMP_TAC[]);;

(*** compress_d of the polynomial at RSI (all < q, from its reduction) into
 *** RDI, the table at RDX
 ***)

let api_compress_th d =
  match d with
    4 -> layout "mlkem_compress_d4_x86",mlkem_compress_d4_x86_mc,
         API_COMPRESS_D4
  | 5 -> layout "mlkem_compress_d5_x86",mlkem_compress_d5_x86_mc,
         API_COMPRESS_D5
  | 10 -> layout "mlkem_compress_d10_x86",mlkem_compress_d10_x86_mc,
          API_COMPRESS_D10
  | _ -> layout "mlkem_compress_d11_x86",mlkem_compress_d11_x86_mc,
         API_COMPRESS_D11;;

let API_COMPRESS_CALL_TAC exec d kk gl =
  let a = find_read_fact `RSI` kk gl in
  let f = api_fun16 a 256 kk gl in
  let f' = try rand(concl(ETA_CONV f)) with Failure _ -> f in
  let remth = find_asm (fun c ->
    try let iv,body = dest_forall c in
        let _,eq = dest_imp body in
        lhand eq = mk_comb(`ival:int16->int`,mk_comb(f',iv)) &&
        can (find_term (fun t -> is_const t && name_of t = "rem")) (rand eq)
    with Failure _ -> false) gl in
  let bth = GEN `i:num` (DISCH `i < 256`
              (MATCH_MP VAL_LT_OF_REM (UNDISCH(SPEC `i:num` remth)))) in
  let lo,mc,th = api_compress_th d in
  (ASSUME_TAC bth THEN API_REG_PCADD_TAC `RDX` kk THEN API_ALIGNED_TAC kk THEN
   NATIVE2_CALL_TAC mlkem_native2_image_mc exec (lo,mc,th)
    [`read RDI s`; `read RSI s`; f'; `read RDX s`] kk) gl;;

(*** basemul_kK with the bounds of the polynomials at RSI by btac ***)

let API_BASEMUL_GEN_CALL_TAC exec k btac kk gl =
  let ab,a = api_addr_parts(find_read_fact `RSI` kk gl)
  and bb,b = api_addr_parts(find_read_fact `RDX` kk gl)
  and tb,t = api_addr_parts(find_read_fact `RCX` kk gl) in
  let eta f = try rand(concl(ETA_CONV f)) with Failure _ -> f in
  let fs = flat(map (fun c ->
    [eta(api_fun16_at (ab,a + 512 * c) 256 kk gl);
     eta(api_fun16_at (bb,b + 512 * c) 256 kk gl);
     eta(api_fun16_at (tb,t + 256 * c) 128 kk gl)]) (0--(k-1))) in
  let xs = map (fun c -> el (3 * c) fs) (0--(k-1)) in
  let lo,mc,th = api_basemul_th k in
  (MAP_EVERY btac xs THEN API_ALIGNED_TAC kk THEN
   NATIVE2_CALL_TAC mlkem_native2_image_mc exec (lo,mc,th)
    ([`read RSI s`; `read RDX s`; `read RCX s`; `read RDI s`] @ fs) kk THEN
   API_SIDE_TAC) gl;;

let API_GHOST12_BOUND_TAC x =
  API_GHOST_BOUND_TAC x `(&2 pow 12):int` FIELD12_BOUND;;

(* ------------------------------------------------------------------------- *)
(* pke_encrypt for k: the frame (the mulcache of y, t, u, v, m), the noise   *)
(* y, e1, e2 in place at noise.                                              *)
(* ------------------------------------------------------------------------- *)

let pe_yc k = 0;;
let pe_t k = 256 * k;;
let pe_u k = pe_t k + 512 * k;;
let pe_v k = pe_u k + 512 * k;;
let pe_m k = pe_v k + 512;;
let pe_frame k = pe_m k + 512;;
let pe_stack k = pe_frame k + 87;;
let pe_ctb k = 32 * (api_du k * k + api_dv k);;
let pe_nb k = 512 * (2 * k + 1);;

let PE_FINAL_TAC k bth kk gl =
  let sv = state_of kk in
  let blk x = api_blk (map (fun j -> x^string_of_int j) (0--(k-1))) in
  let gv n = mk_var(n,`:num->int16`) in
  let th = ISPECL [`ek:byte list`; `m:byte list`; `r:byte list`;
                   blk "TM"; blk "YM"; blk "CM"; gv "MU"; blk "UM"; gv "VM";
                   blk "U1"; gv "V1"; blk "U3"; gv "V2"; gv "V4"] bth in
  let du = api_du k and dv = api_dv k in
  let ub = 32 * du and ctb = pe_ctb k in
  let g = parse_term("\\j i. (("^string_of_int(1 lsl (du+1))^" * val(EL j "^
    "["^String.concat "; " (map (fun j -> "U3"^string_of_int j^":num->int16")
                             (0--(k-1)))^"] i) + 3329) DIV 6658) MOD "^
    string_of_int(1 lsl du)) in
  let mth = ISPECL [`ct:int64`; mk_small_numeral ub; mk_small_numeral du;
                    g; sv; mk_small_numeral k] READ_MEMORY_BYTES_NSUM_BLOCKS in
  let ctgoal = vsubst [sv,`s:x86state`; mk_small_numeral ctb,`n:num`]
    (parse_term("read (memory :> bytes(ct,n)) s = "^
                "num_of_bytelist(kpke_encrypt "^api_param k^" ek m r)")) in
  let splitth = ARITH_RULE(mk_eq(mk_small_numeral ctb,
    mk_binop `(+):num->num->num` (mk_small_numeral(ub * k))
      (mk_small_numeral(32 * dv)))) in
  (MP_TAC th THEN ANTS_TAC THENL
    [REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
     TRY(API_CASES_TAC k) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
     ASM_SIMP_TAC[];
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

let MLKEM_NATIVE2_PKE_ENCRYPT_CORRECT_TAC k ex =
  let nm = api_param k in
  let lo = layout(nm ^ "_pke_encrypt") and hi = layout(nm ^ "_enc_derand") in
  let next = API_TO_CALL_TAC ex lo hi in
  let zs = api_zero_loops (nm ^ "_pke_encrypt") in
  let zls = map (API_ZERO_LOOP ex) zs in
  let bth = match k with
      2 -> X86_KPKE_ENCRYPT_K2 | 3 -> X86_KPKE_ENCRYPT_K3
    | _ -> X86_KPKE_ENCRYPT_K4 in
  let fb = `fb:int64` and noise = `noise:int64`
  and gv n = mk_var(n,`:num->int16`) in
  let du = api_du k and dv = api_dv k in
  let ns x j = x ^ string_of_int j in
  let ekv = `ek:byte list` and mv = `m:byte list` in
  API_ENTRY_TAC ex
   [`ct:int64`; `at:int64`; `pk:int64`; `mp:int64`; `noise:int64`;
    `ek:byte list`; `m:byte list`; `r:byte list`; `pc:num`]
   (pe_stack k) (pe_frame k) THEN
  ON_STATE API_SPLIT_NOISE_TAC THEN
  next THEN ON_STATE(API_FROMMSG_CALL_TAC ex mv) THEN API_RSP_TAC THEN
  ON_STATE(API_FROMMSG_POST_TAC "MU" (fb,pe_m k) mv) THEN
  MAP_EVERY (fun j ->
    next THEN ON_STATE(API_FROMBYTES_CALL_TAC ex ekv j) THEN API_RSP_TAC THEN
    ON_STATE(API_FROMBYTES_POST_TAC (ns "TM" j) (fb,pe_t k + 512 * j) ekv j))
   (0--(k-1)) THEN
  MAP_EVERY (fun j ->
    next THEN
    ON_STATE(fun kk gl ->
      let x = api_fun16_at (noise,512 * j) 256 kk gl in
      (API_NOISE_BOUND_TAC x THEN API_NTT_CALL_TAC ex kk THEN API_RSP_TAC THEN
       ON_STATE(API_NTT_POST_LAM_TAC (ns "YM" j) (noise,512 * j) x)) gl))
   (0--(k-1)) THEN
  MAP_EVERY (fun j ->
    next THEN ON_STATE(API_MULCACHE_CALL_TAC ex) THEN API_RSP_TAC THEN
    ON_STATE(API_MC_POST_TAC (ns "CM" j) (fb,pe_yc k + 256 * j)
              (gv(ns "YM" j))))
   (0--(k-1)) THEN
  MAP_EVERY (fun q ->
    next THEN
    MAP_EVERY (fun c -> ON_STATE(API_MATRIX_POLY_TAC q c)) (0--(k-1)) THEN
    ON_STATE(API_BASEMUL_GEN_CALL_TAC ex k API_MATRIX_BOUND_TAC) THEN
    API_RSP_TAC THEN
    ON_STATE(API_BASEMUL_POST_TAC (ns "UM" q) (fb,pe_u k + 512 * q)))
   (0--(k-1)) THEN
  next THEN ON_STATE(API_BASEMUL_GEN_CALL_TAC ex k API_GHOST12_BOUND_TAC) THEN
  API_RSP_TAC THEN ON_STATE(API_BASEMUL_POST_TAC "VM" (fb,pe_v k)) THEN
  MAP_EVERY (fun j ->
    next THEN ON_STATE(API_INTT_CALL_TAC ex) THEN API_RSP_TAC THEN
    ON_STATE(API_INTT_POST_TAC (ns "U1" j) (fb,pe_u k + 512 * j)
              (gv(ns "UM" j))))
   (0--(k-1)) THEN
  next THEN ON_STATE(API_INTT_CALL_TAC ex) THEN API_RSP_TAC THEN
  ON_STATE(API_INTT_POST_TAC "V1" (fb,pe_v k) (gv "VM")) THEN
  MAP_EVERY (fun j ->
    next THEN ON_STATE(API_ADD_REDUCE_CALL_TAC ex) THEN API_RSP_TAC THEN
    ON_STATE(fun kk gl ->
      API_ADD_REDUCE_POST_TAC (ns "U3" j) (fb,pe_u k + 512 * j)
        (gv(ns "U1" j)) (api_fun16_at (noise,512 * (k + j)) 256 kk gl) kk gl))
   (0--(k-1)) THEN
  next THEN ON_STATE(API_ADD_REDUCE_CALL_TAC ex) THEN API_RSP_TAC THEN
  ON_STATE(fun kk gl ->
    API_ADD_REDUCE_POST_TAC "V2" (fb,pe_v k) (gv "V1")
      (api_fun16_at (noise,1024 * k) 256 kk gl) kk gl) THEN
  next THEN ON_STATE(API_ADD_REDUCE_CALL_TAC ex) THEN API_RSP_TAC THEN
  ON_STATE(API_ADD_REDUCE_POST_TAC "V4" (fb,pe_v k) (gv "V2") (gv "MU")) THEN
  REPLICATE_TAC k (next THEN ON_STATE(API_COMPRESS_CALL_TAC ex du) THEN
                   API_RSP_TAC) THEN
  next THEN ON_STATE(API_COMPRESS_CALL_TAC ex dv) THEN API_RSP_TAC THEN
  MAP_EVERY (fun ((lo,_),zl) ->
    API_TO_PC_TAC ex (lo - 5) THEN ON_STATE(API_ZERO_STEP_TAC ex zl))
   (zip zs zls) THEN
  API_TO_PC_TAC ex (-1) THEN
  ON_STATE(PE_FINAL_TAC k bth) THEN
  API_EXPAND_FB_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* keypair_derand, enc_derand and dec: the calls of the middle layer         *)
(* (hash_g, hash_h, gen_matrix, getnoise) with the facts about the constants *)
(* block they take, and the copies of 32-byte blocks.                        *)
(* ------------------------------------------------------------------------- *)

(*** The constants block c = word(pc + 61952) and its tables, as the callees
 *** take them: at word_add c (word off), and the word list forms
 ***)

let API_C_ADDR = prove
 (`!pc a b. word(pc + a + b):int64 = word_add (word(pc + a)) (word b)`,
  REWRITE_TAC[GSYM WORD_ADD; ADD_ASSOC]);;

let api_c_off th off =
  let c = layout "mlkem_native2_constants" in
  let th1 = SPECL [`pc:num`; mk_small_numeral c; mk_small_numeral off]
              API_C_ADDR in
  let th2 = CONV_RULE(LAND_CONV(RAND_CONV(RAND_CONV NUM_ADD_CONV))) th1 in
  REWRITE_RULE[th2] th;;

let MLKEM_NATIVE2_RC_WORDS = prove
 (`!s pc. bytes_loaded s (word pc) mlkem_native2_image_mc
          ==> wordlist_from_memory(word(pc + 61952),24) s = round_constants`,
  REWRITE_TAC[MLKEM_NATIVE2_ROUND_CONSTANTS]);;

let MLKEM_NATIVE2_RHO8_WORDS = prove
 (`!s pc. bytes_loaded s (word pc) mlkem_native2_image_mc
          ==> wordlist_from_memory(word_add (word(pc + 61952)) (word 192),4)
                s = rho8_constant`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP MLKEM_NATIVE2_RHO8_TABLE) THEN
  REWRITE_TAC[GSYM WORD_ADD; GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORDLIST_FROM_MEMORY_RHO8; MLKEM_NATIVE2_RHO8_TABLE_VALUE]);;

let MLKEM_NATIVE2_RHO56_WORDS = prove
 (`!s pc. bytes_loaded s (word pc) mlkem_native2_image_mc
          ==> wordlist_from_memory(word_add (word(pc + 61952)) (word 224),4)
                s = rho56_constant`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP MLKEM_NATIVE2_RHO56_TABLE) THEN
  REWRITE_TAC[GSYM WORD_ADD; GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORDLIST_FROM_MEMORY_RHO56; MLKEM_NATIVE2_RHO56_TABLE_VALUE]);;

let MLKEM_NATIVE2_REJ_BYTES = prove
 (`!s pc. bytes_loaded s (word pc) mlkem_native2_image_mc
          ==> read (memory :> bytes(word_add (word(pc + 61952)) (word 1952),
                                    4096)) s =
              num_of_wordlist mlkem_rej_uniform_table`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP MLKEM_NATIVE2_REJ_TABLE) THEN
  REWRITE_TAC[GSYM WORD_ADD; GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MLKEM_NATIVE2_REJ_TABLE_VALUE]);;

(*** The facts for the Keccak-based callees at the current state k (the
 *** simulation does not keep wordlist_from_memory facts)
 ***)

let API_CONSTS_TAC k =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `bytes_loaded s (word pc) mc`) c &&
       rand(rator(rator c)) = state_of k
    then MAP_EVERY (fun lem -> ASSUME_TAC(MATCH_MP lem th))
          [MLKEM_NATIVE2_RC_WORDS; MLKEM_NATIVE2_RHO8_WORDS;
           MLKEM_NATIVE2_RHO56_WORDS; MLKEM_NATIVE2_REJ_BYTES]
    else NO_TAC);;

(*** A call of a function of the image as one step, by its theorem fully
 *** specialized, with the addresses normalized, and the side goals for the
 *** arguments on the stack
 ***)

let API_STACK_SIDE_TAC (asl,w as gl) =
  if (try fst(dest_const(fst(strip_comb w))) = "eventually"
      with Failure _ -> false)
  then ALL_TAC gl
  else (REWRITE_TAC[API_WORD_SUB_ADD] THEN ASM_REWRITE_TAC[] THEN NO_TAC) gl;;

let API_IMAGE_CALL_TAC exec th k =
  let th' = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th in
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native2_image_mc,exec,0,mlkem_native2_image_mc,th') [] (k+1) THEN
  API_STACK_SIDE_TAC;;

(*** The bytes of 32-byte blocks: from a number, and back ***)

let READ_MEMORY_BYTES_OF_256S_MOD = prove
 (`!a n N s:x86state.
     (!i. i < n
          ==> read (memory :> bytes256(word_add a (word(32 * i)))) s =
              word((N DIV 2 EXP (8 * (32 * i))) MOD 2 EXP 256))
     ==> read (memory :> bytes(a,32 * n)) s = N MOD 2 EXP (8 * (32 * n))`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; READ_COMPONENT_COMPOSE;
                READ_BYTES_TRIVIAL];
    REPEAT STRIP_TAC] THEN
  REWRITE_TAC[ARITH_RULE `32 * SUC n = 32 * n + 32`] THEN
  REWRITE_TAC[READ_MEMORY_BYTES_SPLIT; READ_MEMORY_BYTES_32] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`N:num`; `s:x86state`] o
    check (fun th -> length(fst(strip_forall(concl th))) = 2)) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  REWRITE_TAC[ARITH_RULE `n < SUC n`] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_256; MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `8 * (32 * n + 32) = 8 * 32 * n + 256`] THEN
  REWRITE_TAC[EXP_ADD; MOD_MULT_MOD] THEN ARITH_TAC);;

let READ_MEMORY_BYTES_OF_256S = prove
 (`!a n (l:byte list) s:x86state.
     LENGTH l = 32 * n /\
     (!i. i < n
          ==> read (memory :> bytes256(word_add a (word(32 * i)))) s =
              word((num_of_bytelist l DIV 2 EXP (8 * (32 * i))) MOD
                   2 EXP 256))
     ==> read (memory :> bytes(a,32 * n)) s = num_of_bytelist l`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP READ_MEMORY_BYTES_OF_256S_MOD) THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPEC `l:byte list` NUM_OF_BYTELIST_BOUND) THEN
  ASM_REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; GSYM EXP_EXP]);;

(*** The view as 32 bytes of 32 bytes at a known as a number ***)

let API_BYTES256_OF_TAC a n len off k =
  let sv = state_of k in
  let th0 = SPECL [a; mk_small_numeral len; n; mk_small_numeral off; sv]
              READ_MEMORY_BYTES256_OF_NUM in
  MP_TAC th0 THEN ANTS_TAC THENL
   [CONV_TAC(RAND_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN NO_TAC;
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
    CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0; EXP; DIV_1] THEN
    CONV_TAC(LAND_CONV(DEPTH_CONV NUM_RED_CONV)) THEN DISCH_TAC];;

(*** The input of G: 32 bytes of d (as a 256-bit word) and a byte ***)

let READ_MEMORY_BYTES_33_OF_256 = prove
 (`!a (d:byte list) c s:x86state.
     LENGTH d = 32 /\
     read (memory :> bytes256 a) s = word(num_of_bytelist d MOD 2 EXP 256) /\
     read (memory :> bytes8 (word_add a (word 32))) s = c
     ==> read (memory :> bytes(a,33)) s = num_of_bytelist(APPEND d [c])`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `33 = 32 + 1`; READ_MEMORY_BYTES_SPLIT] THEN
  ASM_REWRITE_TAC[READ_MEMORY_BYTES_32; READ_MEMORY_BYTES_1] THEN
  ASM_REWRITE_TAC[NUM_OF_BYTELIST_APPEND; num_of_bytelist; VAL_WORD;
                  DIMINDEX_256; MOD_MOD_REFL] THEN
  MP_TAC(ISPEC `d:byte list` NUM_OF_BYTELIST_BOUND) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[MOD_LT] THEN ARITH_TAC);;

(*** hash_g of m (with LENGTH m from lenth) at RSI, at RDI ***)

let API_HASH_G_CALL_TAC exec m lenth k gl =
  let th = REWRITE_RULE[lenth]
            (SPECL [find_read_fact `RDI` k gl; find_read_fact `RSI` k gl; m;
                    find_read_fact `RCX` k gl; `pc:num`;
                    find_read_fact `RSP` k gl;
                    rand(concl(bytes64_fact (find_read_fact `RSP` k gl) k gl))]
                   MLKEM_HASH_G_SUBROUTINE_CORRECT) in
  (API_CONSTS_TAC k THEN API_IMAGE_CALL_TAC exec th k) gl;;

let API_HASH_H_CALL_TAC exec m lenth k gl =
  let th = REWRITE_RULE[lenth]
            (SPECL [find_read_fact `RDI` k gl; find_read_fact `RSI` k gl; m;
                    find_read_fact `RCX` k gl; `pc:num`;
                    find_read_fact `RSP` k gl;
                    rand(concl(bytes64_fact (find_read_fact `RSP` k gl) k gl))]
                   MLKEM_HASH_H_SUBROUTINE_CORRECT) in
  (API_CONSTS_TAC k THEN API_IMAGE_CALL_TAC exec th k) gl;;

(*** G's output: rho and sigma from the 64 bytes of SHA3-512 ***)

let API_G_SPLIT_TAC k =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read (memory :> bytes(a,64)) s =
                            num_of_bytelist(sha3_512 m)`) c &&
       rand(lhand c) = state_of k
    then MAP_EVERY ASSUME_TAC
          (CONJUNCTS(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                       (MATCH_MP MLKEM_G_BYTES th)))
    else NO_TAC);;

(*** The calls of gen_matrix and getnoise with their theorems specialized
 *** (args from the registers r, the stack pointer and the return address)
 ***)

let api_ret k gl = rand(concl(bytes64_fact (find_read_fact `RSP` k gl) k gl));;

let API_GM_CALL_TAC exec gmth args k gl =
  let r c = find_read_fact c k gl in
  let th = REWRITE_RULE[PAIRWISE; ALLPAIRS; ALL; LENGTH_MLKEM_G;
                        LENGTH_MLKEM_SLICE]
            (SPECL (args r @ [`pc:num`; r `RSP`; api_ret k gl]) gmth) in
  (API_CONSTS_TAC k THEN API_ALIGNED_TAC k THEN
   API_IMAGE_CALL_TAC exec th k) gl;;

let api_getnoise_th seed k gl =
  let v reg = dest_small_numeral(rand(find_read_fact reg k gl)) in
  let ns = mk_small_numeral in
  let sp = find_read_fact `RSP` k gl in
  let c = find_read_fact `R15` k gl in
  let th = SPECL [find_read_fact `RDI` k gl; find_read_fact `RSI` k gl; seed;
                  ns(v `RDX`); ns(v `RCX`); ns(v `R8`); ns(v `R9`);
                  c; `pc:num`; sp; api_ret k gl]
                 MLKEM_GETNOISE_SUBROUTINE_CORRECT in
  let th' = CONV_RULE(LAND_CONV(LAND_CONV(REWRITE_CONV[ARITH_EQ]))) th in
  REWRITE_RULE[COND_ID; LENGTH_MLKEM_G; ALL]
   (CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) (REWRITE_RULE[] th'));;

let API_GETNOISE_CALL_TAC exec seed k gl =
  (API_CONSTS_TAC k THEN API_ALIGNED_TAC k THEN
   API_IMAGE_CALL_TAC exec (api_getnoise_th seed k gl) k) gl;;

(*** Dropping the facts about 32-byte blocks of memory at addresses based
 *** at b (for a copy from there by blocks of a value known as a whole)
 ***)

let API_DROP256_TAC b =
  let isb t = (fst(api_addr_parts t) = b) in
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c &&
       (try let comp = lhand(lhand c) in
            let bv = rand comp in
            fst(dest_const(rator bv)) = "bytes256" && isb(rand bv)
        with Failure _ -> false)
    then ALL_TAC else NO_TAC));;

(*** A copy of n 32-byte blocks: the blocks of the source known as the
 *** number N (bytes(base,len) s = N at offset off) as 256-bit words, at
 *** state k
 ***)

let API_BLOCKS256_TAC base len nn off n k =
  MAP_EVERY (fun i -> API_BYTES256_OF_TAC base nn len (off + 32 * i) k)
            (0--(n-1));;

(*** The bytes at dst (n blocks) as N, from the blocks stored at state k,
 *** given N < 2 EXP (256 * n)
 ***)

let API_JOIN256_TAC dst l n k (asl,w as gl) =
  let sv = state_of k in
  let th = SPECL [dst; mk_small_numeral n; l; sv] READ_MEMORY_BYTES_OF_256S in
  (MP_TAC th THEN ANTS_TAC THENL
    [CONJ_TAC THENL
      [CONV_TAC(RAND_CONV NUM_REDUCE_CONV) THEN
       REWRITE_TAC[LENGTH_MLKEM_G; LENGTH_SHA3_256; LENGTH_SHA3_512;
                   LENGTH_MLKEM_SLICE] THEN
       ASM_REWRITE_TAC[] THEN NO_TAC;
       CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
       CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
       REWRITE_TAC[WORD_ADD_0; EXP; DIV_1] THEN
       CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN ASM_REWRITE_TAC[] THEN NO_TAC];
     CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN DISCH_TAC]) gl;;

(* ------------------------------------------------------------------------- *)
(* keypair_derand for k                                                      *)
(* ------------------------------------------------------------------------- *)

let kp_gin = 32 and kp_g = 96 and kp_njob = 160;;
let kp_a k = 256;;
let kp_s k = kp_a k + 512 * k * k;;
let kp_e k = kp_s k + 512 * k;;
let kp_sc k = kp_e k + 512 * k;;
let kp_t k = kp_sc k + 256 * k;;
let kp_frame k = kp_t k + 512 * k;;
let kp_cs k = if k = 4 then 5639 else 3895;;
let kp_stack k = 48 + kp_frame k + 31 + kp_cs k;;
let kp_pkb k = 384 * k + 32;;
let kp_skb k = 768 * k + 96;;

let kp_rho k = parse_term("FST(mlkem_g(APPEND d [word "^string_of_int k^"]))")
and kp_sigma k =
  parse_term("SND(mlkem_g(APPEND d [word "^string_of_int k^"]))");;

let kp_keygen_pair k =
  REWRITE_RULE[GSYM(match k with
                      2 -> mlkem512 | 3 -> mlkem768 | _ -> mlkem1024)]
   (ISPECL (match k with
      2 -> [`2`; `3`; `2`; `10`; `4`] | 3 -> [`3`; `2`; `2`; `10`; `4`]
    | _ -> [`4`; `2`; `2`; `11`; `5`]) MLKEM_KEYGEN_PAIR);;

let kp_lengths k =
  let nm = api_param k in
  let def = match k with 2 -> mlkem512 | 3 -> mlkem768 | _ -> mlkem1024 in
  prove(parse_term("!d. LENGTH(FST(kpke_keygen "^nm^" d)) = "^
                   string_of_int(kp_pkb k)^" /\\ "^
                   "LENGTH(SND(kpke_keygen "^nm^" d)) = "^
                   string_of_int(384 * k)),
        REWRITE_TAC[def; KPKE_KEYGEN_LENGTHS] THEN
        CONV_TAC NUM_REDUCE_CONV);;

(*** tobytes with the slot of the return address apart from the 384 bytes of
 *** the output (the library theorems have 512 there)
 ***)

let MLKEM_TOBYTES_NOIBT_SUBROUTINE_CORRECT_384 = prove
(`!r a (l:int16 list) pc.
        aligned 32 a /\
        nonoverlapping (word pc, LENGTH mlkem_tobytes_tmc) (a, 512) /\
        nonoverlapping (word pc, LENGTH mlkem_tobytes_tmc) (r, 384) /\
        nonoverlapping (a, 512) (r, 384) /\
        nonoverlapping (stackpointer, 8) (r, 384)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_tobytes_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a, 512)) s = num_of_wordlist l)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (LENGTH l = 256
                   ==> (!i. i < LENGTH l ==> val(EL i l) < 3329)
                   ==> read(memory :> bytes(r, 384)) s =
                       num_of_wordlist
                        (MAP word_zx (permute_list l):(12 word)list)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
               MAYCHANGE [memory :> bytes(r, 384)])`,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_tobytes_tmc MLKEM_TOBYTES_CORRECT);;

let MLKEM_TOBYTES_SUBROUTINE_CORRECT_384 =
  ADD_IBT_RULE MLKEM_TOBYTES_NOIBT_SUBROUTINE_CORRECT_384;;

let API_TOBYTES_384 = prove
 (`!r a (x:num->int16) pc stackpointer returnaddress.
        aligned 32 a /\
        nonoverlapping (word pc, LENGTH mlkem_tobytes_mc) (a, 512) /\
        nonoverlapping (word pc, LENGTH mlkem_tobytes_mc) (r, 384) /\
        nonoverlapping (a, 512) (r, 384) /\
        nonoverlapping (stackpointer, 8) (r, 384)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mlkem_tobytes_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r, 384)) s =
                       num_of_wordlist
                        (MAP (word_zx:int16->12 word)
                             (list_of_seq (\i. x(avx_order i)) 256))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r, 384)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`r:int64`; `a:int64`; `list_of_seq (x:num->int16) 256`;
                `pc:num`] MLKEM_TOBYTES_SUBROUTINE_CORRECT_384) THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_RULE) THEN
  CONJ_TAC THEN X_GEN_TAC `s:x86state` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP READ_MEMORY_BYTES16_LIST_OF_SEQ) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN REWRITE_TAC[];
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[EL_LIST_OF_SEQ; LENGTH_LIST_OF_SEQ]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[permute_list] THEN MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC EL_LIST_OF_SEQ THEN ASM_SIMP_TAC[AVX_ORDER_UNORDER]]);;

(*** tomont and reduce in place at RDI ***)

let API_TOMONT_CALL_TAC exec k gl =
  let a = find_read_fact `RDI` k gl in
  let f = api_fun16 a 256 k gl in
  let f' = try rand(concl(ETA_CONV f)) with Failure _ -> f in
  (API_ALIGNED_TAC k THEN
   NATIVE2_CALL_TAC mlkem_native2_image_mc exec
    (layout "mlkem_tomont",mlkem_tomont_mc,MLKEM_TOMONT_SUBROUTINE_CORRECT)
    [`read RDI s`; f'] k) gl;;

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

let API_REDUCE_CALL_TAC exec k gl =
  let a = find_read_fact `RDI` k gl in
  let f = api_fun16 a 256 k gl in
  let f' = try rand(concl(ETA_CONV f)) with Failure _ -> f in
  (API_ALIGNED_TAC k THEN
   NATIVE2_CALL_TAC mlkem_native2_image_mc exec
    (layout "mlkem_reduce",mlkem_reduce_mc,MLKEM_REDUCE_SUBROUTINE_CORRECT)
    [`read RDI s`; f'] k) gl;;

let API_REDUCE_POST_TAC v bn x k =
  let goal = vsubst [mk_var(v,`:num->int16`),`v:num->int16`;
                     x,`x:num->int16`]
   `!i. i < 256
        ==> ival((v:num->int16) i) = ival((x:num->int16) i) rem &3329` in
  API_POST16_TAC v bn 256 k goal [] (fun _ -> SIMP_TAC[]);;

(*** tobytes of the polynomial at RSI (all < q, from its reduction) into
 *** RDI, with its post discharged
 ***)

let API_TOBYTES_CALL_TAC exec kk gl =
  let a = find_read_fact `RSI` kk gl in
  let f = api_fun16 a 256 kk gl in
  let f' = try rand(concl(ETA_CONV f)) with Failure _ -> f in
  let remth = find_asm (fun c ->
    try let iv,body = dest_forall c in
        let _,eq = dest_imp body in
        lhand eq = mk_comb(`ival:int16->int`,mk_comb(f',iv)) &&
        can (find_term (fun t -> is_const t && name_of t = "rem")) (rand eq)
    with Failure _ -> false) gl in
  (API_ALIGNED_TAC kk THEN
   NATIVE2_CALL_TAC mlkem_native2_image_mc exec
    (layout "mlkem_tobytes",mlkem_tobytes_mc,API_TOBYTES_384)
    [`read RDI s`; `read RSI s`; f'] kk THEN
   FIRST_X_ASSUM(fun pth ->
     let c = concl pth in
     if is_imp c && free_in (state_of(kk+1)) c && hascon "avx_order" c
     then MP_TAC pth THEN ANTS_TAC THENL
       [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
        FIRST_ASSUM(fun ith ->
          ACCEPT_TAC(MATCH_MP VAL_LT_OF_REM (MATCH_MP remth ith)));
        DISCH_TAC]
     else NO_TAC)) gl;;

(*** The products of row r of A with s (reduced in place before, for the
 *** polynomials c < r) as those with s in the NTT domain: the facts of v
 *** (the ghost of row r) with ival(SR_c x) replaced by ival(SM_c x)
 ***)

let API_ROW_FIX_TAC v r kk (asl,w as gl) =
  if r = 0 then ALL_TAC gl else
  let vt = mk_var(v,`:num->int16`) and gv n = mk_var(n,`:num->int16`) in
  let isrow c = is_forall c && hascon "avx_order" c &&
                can (find_term ((=) vt)) c && hascon "avx2_mcix" c in
  let th = find_asm isrow gl in
  let srs = map (fun c ->
    find_asm (fun tm -> is_forall tm &&
                can (find_term ((=) (gv("SR"^string_of_int c)))) tm &&
                hascon "rem" tm) gl) (0--(r-1)) in
  let pairs = map (fun c -> gv("SR"^string_of_int c),gv("SM"^string_of_int c))
                  (0--(r-1)) in
  let goal = subst (map (fun (a,b) -> b,a) pairs) (concl th) in
  (SUBGOAL_THEN goal ASSUME_TAC THENL
    [X_GEN_TAC `p:num` THEN DISCH_TAC THEN
     SUBGOAL_THEN `avx_order(2 * p) < 256 /\ avx_order(2 * p + 1) < 256`
     STRIP_ASSUME_TAC THENL
      [ASM_SIMP_TAC[AVX_ORDER_UNORDER;
                    ARITH_RULE `p < 128 ==> 2 * p < 256 /\ 2 * p + 1 < 256`];
       ALL_TAC] THEN
     MP_TAC(SIMP_RULE (srs @ [ASSUME `avx_order(2 * p) < 256`;
                              ASSUME `avx_order(2 * p + 1) < 256`])
             (MP (SPEC `p:num` th) (ASSUME `p < 128`))) THEN
     REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
     REWRITE_TAC[];
     ALL_TAC]) gl;;

(*** The final facts of keypair_derand: pk and sk from the K-PKE keys ***)

let KP_KEYGEN_TAC k bth kk gl =
  let sv = state_of kk in
  let blk x = api_blk (map (fun j -> x^string_of_int j) (0--(k-1))) in
  let rho = kp_rho k and sigma = kp_sigma k in
  let th = ISPECL [`d:byte list`; rho; sigma;
                   blk "SM"; blk "EM"; blk "CM"; blk "PM"; blk "PU";
                   blk "TR"; blk "SR"] bth in
  let mapth x = ISPECL
    [(if x = "TR" then `pk:int64` else `sk:int64`); `384`;
     `word_zx:int16->12 word`;
     mk_abs(`j:num`,mk_abs(`i:num`,
       mk_comb(mk_comb(blk x,`j:num`),`avx_order i`)));
     sv; mk_small_numeral k] READ_MEMORY_BYTES_MAP_BLOCKS in
  let tgoal = vsubst [sv,`s:x86state`]
   (parse_term("read (memory :> bytes(pk,"^string_of_int(384 * k)^")) s = "^
     "num_of_wordlist(MAP (word_zx:int16->12 word) "^
     "(list_of_seq (\\i. ("^string_of_term(blk "TR")^") (i DIV 256) "^
     "(avx_order(i MOD 256))) "^string_of_int(256 * k)^"))")) in
  ignore tgoal;
  (MP_TAC th THEN ANTS_TAC THENL
    [REWRITE_TAC[PAIR] THEN
     REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
     TRY(API_CASES_TAC k) THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
     ASM_SIMP_TAC[];
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN STRIP_TAC] THEN
   MAP_EVERY (fun x ->
     MP_TAC(mapth x) THEN ANTS_TAC THENL
      [CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
       CONV_TAC NUM_REDUCE_CONV THEN
       CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
       CONV_TAC(DEPTH_CONV BETA_CONV) THEN
       CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
       CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
       ASM_REWRITE_TAC[] THEN NO_TAC;
       CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
       DISCH_TAC]) ["TR"; "SR"]) gl;;


let API_MATRIX_BOUND_G_TAC f =
  API_FUN_BOUND_TAC f `(&2 pow 12):int`
   (MATCH_MP_TAC API_SAMPLE_ABS_BOUND THEN
    ASM_REWRITE_TAC[LENGTH_MLKEM_SLICE; LENGTH_MLKEM_G]);;

let MLKEM_NATIVE2_KEYPAIR_DERAND_CORRECT_TAC k ex gmth =
  let nm = api_param k in
  let lo = layout(nm ^ "_keypair_derand")
  and hi = layout(nm ^ "_pke_encrypt") in
  let next = API_TO_CALL_TAC ex lo hi in
  let zs = api_zero_loops (nm ^ "_keypair_derand") in
  let zls = map (API_ZERO_LOOP ex) zs in
  let bth = match k with
      2 -> X86_KPKE_KEYGEN_K2 | 3 -> X86_KPKE_KEYGEN_K3
    | _ -> X86_KPKE_KEYGEN_K4 in
  let fb = `fb:int64` and gv n = mk_var(n,`:num->int16`) in
  let ns x j = x ^ string_of_int j in
  let rho = kp_rho k and sigma = kp_sigma k in
  let ek = parse_term("FST(kpke_keygen "^nm^" d)") in
  let pkb = kp_pkb k and skb = kp_skb k in
  let klen = kp_lengths k and pair = kp_keygen_pair k in
  let wadd a n = mk_comb(mk_comb(`word_add:int64->int64->int64`,a),
                         mk_comb(`word:num->int64`,mk_small_numeral n)) in
  let m = parse_term("APPEND d [word "^string_of_int k^":byte]") in
  let gin_lenth = (REWRITE_CONV[LENGTH_APPEND; LENGTH;
                                ASSUME `LENGTH(d:byte list) = 32`] THENC
                   NUM_REDUCE_CONV) (mk_comb(`LENGTH:byte list->num`,m)) in
  let row r =
    let rs = string_of_int r and t = (fb,kp_t k + 512 * r) in
    next THEN
    MAP_EVERY (fun c -> ON_STATE(API_MATRIX_POLY_TAC r c)) (0--(k-1)) THEN
    ON_STATE(API_BASEMUL_GEN_CALL_TAC ex k API_MATRIX_BOUND_G_TAC) THEN
    API_RSP_TAC THEN
    ON_STATE(API_BASEMUL_POST_TAC ("PM"^rs) t) THEN
    ON_STATE(API_ROW_FIX_TAC ("PM"^rs) r) THEN
    next THEN ON_STATE(API_TOMONT_CALL_TAC ex) THEN API_RSP_TAC THEN
    ON_STATE(API_TOMONT_POST_TAC ("PU"^rs) t (gv ("PM"^rs))) THEN
    next THEN ON_STATE(API_ADD_REDUCE_CALL_TAC ex) THEN API_RSP_TAC THEN
    ON_STATE(API_ADD_REDUCE_POST_TAC ("TR"^rs) t (gv ("PU"^rs))
               (gv ("EM"^rs))) THEN
    next THEN ON_STATE(API_REDUCE_CALL_TAC ex) THEN API_RSP_TAC THEN
    ON_STATE(API_REDUCE_POST_TAC ("SR"^rs) (fb,kp_s k + 512 * r)
               (gv ("SM"^rs))) in
  let gm_call =
    if k = 2 then
      ON_STATE(API_GM_CALL_TAC ex gmth
        (fun r -> [r `RDI`; r `RSI`; rho; r `R8`; r `R9`;
                   `word(pc + 61952):int64`])) THEN API_RSP_TAC THEN
      next THEN ON_STATE(API_GETNOISE_CALL_TAC ex sigma) THEN API_RSP_TAC
    else
      ON_STATE(API_GM_CALL_TAC ex gmth
        (fun r -> [r `RDI`; r `RSI`; rho; r `R9`;
                   wadd fb (kp_g + 32); sigma; wadd fb (kp_s k);
                   r `R8`; `word(pc + 61952):int64`])) THEN API_RSP_TAC in
  API_ENTRY_TAC ex
   [`pk:int64`; `sk:int64`; `coins:int64`; `d:byte list`; `z:byte list`;
    `pc:num`] (kp_stack k) (kp_frame k) THEN
  ON_STATE(API_BYTES256_OF_TAC `coins:int64` `num_of_bytelist(d:byte list)`
            32 0) THEN
  next THEN
  ON_STATE(fun kk gl ->
    let sv = state_of kk in
    (MP_TAC(SPECL [wadd fb kp_gin; `d:byte list`;
                   mk_comb(`word:num->byte`,mk_small_numeral k); sv]
       READ_MEMORY_BYTES_33_OF_256) THEN ANTS_TAC THENL
      [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
       CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
       ASM_REWRITE_TAC[] THEN NO_TAC;
       DISCH_TAC]) gl) THEN
  ON_STATE(API_HASH_G_CALL_TAC ex m gin_lenth) THEN API_RSP_TAC THEN
  ON_STATE API_G_SPLIT_TAC THEN
  next THEN gm_call THEN ON_STATE API_SPLIT_NOISE_TAC THEN
  MAP_EVERY (fun (v,off) ->
    next THEN
    ON_STATE(fun kk gl ->
      let x = api_fun16_at (fb,off) 256 kk gl in
      (API_NOISE_BOUND_TAC x THEN API_NTT_CALL_TAC ex kk THEN API_RSP_TAC THEN
       ON_STATE(API_NTT_POST_LAM_TAC v (fb,off) x)) gl))
   (map (fun j -> (ns "SM" j,kp_s k + 512 * j)) (0--(k-1)) @
    map (fun j -> (ns "EM" j,kp_e k + 512 * j)) (0--(k-1))) THEN
  MAP_EVERY (fun j ->
    next THEN ON_STATE(API_MULCACHE_CALL_TAC ex) THEN API_RSP_TAC THEN
    ON_STATE(API_MC_POST_TAC (ns "CM" j) (fb,kp_sc k + 256 * j)
              (gv(ns "SM" j))))
   (0--(k-1)) THEN
  MAP_EVERY row (0--(k-1)) THEN
  REPLICATE_TAC (2 * k)
   (next THEN ON_STATE(API_TOBYTES_CALL_TAC ex) THEN API_RSP_TAC) THEN
  ON_STATE(API_BYTES256_OF_TAC (wadd fb kp_g) (mk_comb(`num_of_bytelist`,rho))
            32 0) THEN
  ON_STATE(fun kk -> X86_STEPS_TAC ex ((kk+1)--(kk+2))) THEN
  ON_STATE(API_JOIN256_TAC (wadd `pk:int64` (384 * k)) rho 1) THEN
  ON_STATE(KP_KEYGEN_TAC k bth) THEN
  ON_STATE(fun kk ->
    SUBGOAL_THEN (vsubst [state_of kk,`s:x86state`;
                          mk_small_numeral pkb,`n:num`; ek,`ek:byte list`]
                   `read (memory :> bytes(pk,n)) s = num_of_bytelist ek`)
    ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE(mk_eq(mk_small_numeral pkb,
        mk_binop `(+):num->num->num` (mk_small_numeral(384 * k)) `32`));
        READ_MEMORY_BYTES_SPLIT] THEN
      ASM_REWRITE_TAC[] THEN NO_TAC;
      ALL_TAC]) THEN
  API_DROP256_TAC `pk:int64` THEN
  ON_STATE(API_BLOCKS256_TAC `pk:int64` pkb (mk_comb(`num_of_bytelist`,ek)) 0
            (pkb / 32)) THEN
  ON_STATE(fun kk -> X86_STEPS_TAC ex ((kk+1)--(kk + 2 * (pkb / 32)))) THEN
  ASSUME_TAC(CONJUNCT1(SPEC `d:byte list` klen)) THEN
  ON_STATE(API_JOIN256_TAC (wadd `sk:int64` (384 * k)) ek (pkb / 32)) THEN
  next THEN
  ON_STATE(API_HASH_H_CALL_TAC ex ek (CONJUNCT1(SPEC `d:byte list` klen))) THEN
  API_RSP_TAC THEN
  ON_STATE(API_BYTES256_OF_TAC (wadd `coins:int64` 32)
            `num_of_bytelist(z:byte list)` 32 0) THEN
  ON_STATE(fun kk -> X86_STEPS_TAC ex ((kk+1)--(kk+2))) THEN
  ON_STATE(API_JOIN256_TAC (wadd `sk:int64` (skb - 32)) `z:byte list` 1) THEN
  MAP_EVERY (fun ((lo,_),zl) ->
    API_TO_PC_TAC ex (lo - 5) THEN ON_STATE(API_ZERO_STEP_TAC ex zl))
   (zip zs zls) THEN
  API_TO_PC_TAC ex (-1) THEN
  ON_STATE(fun kk ->
    SUBGOAL_THEN (vsubst [state_of kk,`s:x86state`;
                          mk_small_numeral skb,`n:num`]
     (parse_term("read (memory :> bytes(sk,n)) s = "^
                 "num_of_bytelist(SND(mlkem_keygen "^nm^" d z))")))
    ASSUME_TAC THENL
     [REWRITE_TAC[pair; mlkem_h; NUM_OF_BYTELIST_APPEND; klen;
                  LENGTH_SHA3_256] THEN
      REWRITE_TAC[ARITH_RULE(parse_term(string_of_int skb^" = "^
        string_of_int(384 * k)^" + "^string_of_int pkb^" + 32 + 32"));
                  READ_MEMORY_BYTES_SPLIT] THEN
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC]) THEN
  API_EXPAND_FB_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[pair];;

(* ------------------------------------------------------------------------- *)
(* enc_derand and dec: the key checks, the 64-byte input of G, and the       *)
(* calls of pke_encrypt and pke_decrypt.                                     *)
(* ------------------------------------------------------------------------- *)

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

(*** check_encoding of the k polynomials of ek at RDI ***)

let API_CHECK_ENCODING_CALL_TAC exec k ek kk gl =
  let a = find_read_fact `RDI` kk gl in
  let n = mk_comb(`num_of_bytelist`,
            list_mk_icomb "mlkem_slice"
             [`0`; mk_small_numeral(384 * k); ek]) in
  (API_SLICE_AT_TAC a ek 0 (384 * k) kk THEN
   NATIVE2_CALL_TAC mlkem_native2_image_mc exec
    (layout "mlkem_check_encoding",mlkem_check_encoding_mc,
     MLKEM_CHECK_ENCODING_K_RULE k)
    [`read RDI s`; n] kk) gl;;

(*** The 64 bytes of l1 (32 bytes, as a 256-bit word) and l2 (32 bytes) ***)

let READ_MEMORY_BYTES_64_OF_256_32 = prove
 (`!a (l1:byte list) (l2:byte list) s:x86state.
     LENGTH l1 = 32 /\
     read (memory :> bytes256 a) s =
     word(num_of_bytelist l1 MOD 2 EXP 256) /\
     read (memory :> bytes(word_add a (word 32),32)) s = num_of_bytelist l2
     ==> read (memory :> bytes(a,64)) s = num_of_bytelist(APPEND l1 l2)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `64 = 32 + 32`; READ_MEMORY_BYTES_SPLIT] THEN
  ASM_REWRITE_TAC[READ_MEMORY_BYTES_32] THEN
  ASM_REWRITE_TAC[NUM_OF_BYTELIST_APPEND; VAL_WORD; DIMINDEX_256;
                  MOD_MOD_REFL] THEN
  MP_TAC(ISPEC `l1:byte list` NUM_OF_BYTELIST_BOUND) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT]);;

(*** A case split on the boolean b, rewriting it in the assumptions ***)

let API_BOOL_CASE_TAC tm =
  ASM_CASES_TAC tm THEN
  POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th);;

(* ------------------------------------------------------------------------- *)
(* enc_derand for k                                                          *)
(* ------------------------------------------------------------------------- *)

let en_gin = 32 and en_kr = 96 and en_jobs = 160 and en_noise = 224;;
let en_at k = en_noise + 512 * (2 * k + 1);;
let en_frame k = en_at k + 512 * k * k;;
let en_cs k = match k with 2 -> 3895 | 3 -> 4959 | _ -> 6239;;
let en_stack k = 48 + en_frame k + 31 + en_cs k;;

(*** The noise from getnoise in the form pke_encrypt takes (nonce 0 + i) ***)

let API_NOISE_FORM_TAC k =
  let sv = state_of k in
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_forall c && free_in sv c && hascon "mlkem_cbd_coeff" c
    then REWRITE_RULE[ADD_CLAUSES; COND_ID] th else th);;

let en_pair k =
  let par = api_param k in
  let def = match k with 2 -> mlkem512 | 3 -> mlkem768 | _ -> mlkem1024 in
  prove(parse_term("!ek m. mlkem_encaps_internal "^par^" ek m = "^
    "FST(mlkem_g(APPEND m (sha3_256 ek))),"^
    "kpke_encrypt "^par^" ek m (SND(mlkem_g(APPEND m (sha3_256 ek))))"),
   REWRITE_TAC[def; MLKEM_ENCAPS_PAIR; mlkem_g]);;

let MLKEM_NATIVE2_ENC_DERAND_CORRECT_TAC k ex gmth peth =
  let nm = api_param k in
  let lo = layout(nm ^ "_enc_derand") and hi = layout(nm ^ "_pke_decrypt") in
  let next = API_TO_CALL_TAC ex lo hi in
  let zs = api_zero_loops (nm ^ "_enc_derand") in
  let zls = map (API_ZERO_LOOP ex) zs in
  let fb = `fb:int64` in
  let wadd a n = mk_comb(mk_comb(`word_add:int64->int64->int64`,a),
                         mk_comb(`word:num->int64`,mk_small_numeral n)) in
  let ek = `ek:byte list` and mv = `m:byte list` in
  let pkb = kp_pkb k in
  let rho_ek = parse_term("mlkem_slice "^string_of_int(384 * k)^" 32 ek") in
  let hmsg = `APPEND m (sha3_256 ek)` in
  let kk_t = `FST(mlkem_g(APPEND m (sha3_256 ek)))`
  and rr_t = `SND(mlkem_g(APPEND m (sha3_256 ek)))` in
  let hlen = (REWRITE_CONV[LENGTH_APPEND; LENGTH_SHA3_256;
                           ASSUME `LENGTH(m:byte list) = 32`] THENC
              NUM_REDUCE_CONV) (mk_comb(`LENGTH:byte list->num`,hmsg)) in
  let check = parse_term("mlkem_ek_check "^nm^" ek") in
  let valid =
    ON_STATE(API_BYTES256_OF_TAC `coins:int64` `num_of_bytelist(m:byte list)`
              32 0) THEN
    next THEN
    ON_STATE(fun kk -> API_SLICE_AT_TAC `pk:int64` ek (384 * k) 32 kk) THEN
    ON_STATE(API_GM_CALL_TAC ex gmth
      (fun r -> [r `RDI`; r `RSI`; rho_ek; r `R8`; `word 0:int64`;
                 `word 0:int64`; `word 0:int64`; `pk:int64`; ek;
                 wadd fb (en_gin + 32); r `R9`;
                 `word(pc + 61952):int64`])) THEN
    API_RSP_TAC THEN
    next THEN
    ON_STATE(fun kk gl ->
      (MP_TAC(SPECL [wadd fb en_gin; mv; `sha3_256 ek`; state_of kk]
         READ_MEMORY_BYTES_64_OF_256_32) THEN ANTS_TAC THENL
        [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
         CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
         ASM_REWRITE_TAC[] THEN NO_TAC;
         DISCH_TAC]) gl) THEN
    ON_STATE(API_HASH_G_CALL_TAC ex hmsg hlen) THEN API_RSP_TAC THEN
    ON_STATE API_G_SPLIT_TAC THEN
    next THEN ON_STATE(API_GETNOISE_CALL_TAC ex rr_t) THEN API_RSP_TAC THEN
    ON_STATE API_NOISE_FORM_TAC THEN
    ON_STATE(API_JOIN256_TAC (wadd fb en_gin) mv 1) THEN
    next THEN
    ON_STATE(fun kk gl ->
      let r c = find_read_fact c kk gl in
      let th = REWRITE_RULE[PAIRWISE; ALLPAIRS; ALL]
        (SPECL [r `RDI`; r `RSI`; r `RDX`; r `RCX`; r `R8`; ek; mv; rr_t;
                `pc:num`; r `RSP`; api_ret kk gl] peth) in
      (API_ALIGNED_TAC kk THEN API_IMAGE_CALL_TAC ex th kk) gl) THEN
    API_RSP_TAC THEN
    ON_STATE(API_BYTES256_OF_TAC (wadd fb en_kr)
              (mk_comb(`num_of_bytelist`,kk_t)) 32 0) THEN
    ON_STATE(fun kk -> X86_STEPS_TAC ex ((kk+1)--(kk+2))) THEN
    ON_STATE(API_JOIN256_TAC `ss:int64` kk_t 1) THEN
    MAP_EVERY (fun ((lo,_),zl) ->
      API_TO_PC_TAC ex (lo - 5) THEN ON_STATE(API_ZERO_STEP_TAC ex zl))
     (zip zs zls) THEN
    API_TO_PC_TAC ex (-1) THEN
    API_EXPAND_FB_TAC THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[en_pair k] in
  let invalid =
    API_TO_PC_TAC ex (-1) THEN
    API_EXPAND_FB_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] in
  API_ENTRY_TAC ex
   [`ct:int64`; `ss:int64`; `pk:int64`; `coins:int64`; `ek:byte list`;
    `m:byte list`; `pc:num`] (en_stack k) (en_frame k) THEN
  next THEN ON_STATE(API_CHECK_ENCODING_CALL_TAC ex k ek) THEN API_RSP_TAC THEN
  MP_TAC(SPEC ek (ek_check_slice k)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
  API_BOOL_CASE_TAC check THENL [valid; invalid];;

(* ------------------------------------------------------------------------- *)
(* dec for k                                                                 *)
(* ------------------------------------------------------------------------- *)

let de_gin = 32 and de_kr = 96 and de_hek = 160 and de_j = 192
and de_jobs = 224 and de_njob = 288 and de_zc = 320;;
let de_ct2 k = de_zc + 32 + pe_ctb k;;
let de_noise k = de_ct2 k + pe_ctb k;;
let de_at k = de_noise k + 512 * (2 * k + 1);;
let de_frame k = de_at k + 512 * k * k;;
let de_cs k = match k with 2 -> 3895 | 3 -> 5639 | _ -> 6239;;
let de_stack k = 48 + de_frame k + 31 + de_cs k;;

(*** The 64 bytes of l1 (32 bytes) and l2 (32 bytes, as a 256-bit word) ***)

let READ_MEMORY_BYTES_64_OF_32_256 = prove
 (`!a (l1:byte list) (l2:byte list) s:x86state.
     LENGTH l1 = 32 /\ LENGTH l2 = 32 /\
     read (memory :> bytes(a,32)) s = num_of_bytelist l1 /\
     read (memory :> bytes256 (word_add a (word 32))) s =
     word(num_of_bytelist l2 MOD 2 EXP 256)
     ==> read (memory :> bytes(a,64)) s = num_of_bytelist(APPEND l1 l2)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `64 = 32 + 32`; READ_MEMORY_BYTES_SPLIT] THEN
  ASM_REWRITE_TAC[READ_MEMORY_BYTES_32] THEN
  ASM_REWRITE_TAC[NUM_OF_BYTELIST_APPEND; VAL_WORD; DIMINDEX_256;
                  MOD_MOD_REFL] THEN
  MP_TAC(ISPEC `l2:byte list` NUM_OF_BYTELIST_BOUND) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT]);;

let pd_len k =
  let def = match k with 2 -> mlkem512 | 3 -> mlkem768 | _ -> mlkem1024 in
  prove(parse_term("!dk c. LENGTH(kpke_decrypt "^api_param k^" dk c) = 32"),
        REWRITE_TAC[def; KPKE_DECRYPT_LENGTH]);;

let pe_len k =
  let def = match k with 2 -> mlkem512 | 3 -> mlkem768 | _ -> mlkem1024 in
  prove(parse_term("!ek m r. LENGTH(kpke_encrypt "^api_param k^" ek m r) = "^
                   string_of_int(pe_ctb k)),
        REWRITE_TAC[def; KPKE_ENCRYPT_LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

(*** The hash check of dk as the equality of the numbers of H(ek) and h ***)

let de_check_th k =
  let n = string_of_int in
  let par = api_param k in
  let def = match k with 2 -> mlkem512 | 3 -> mlkem768 | _ -> mlkem1024 in
  let pkb = kp_pkb k in
  prove(parse_term(
   "!dk c. LENGTH dk = "^n(kp_skb k)^" /\\ LENGTH c = "^n(pe_ctb k)^
   " ==> (num_of_bytelist(sha3_256(mlkem_slice "^n(384 * k)^" "^n pkb^
   " dk)) = num_of_bytelist(mlkem_slice "^n(768 * k + 32)^" 32 dk) <=> "^
   "mlkem_decaps_check "^par^" dk c)"),
   REPEAT STRIP_TAC THEN REWRITE_TAC[def; mlkem_decaps_check; mlkem_h] THEN
   CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC NUM_OF_BYTELIST_INJ THEN
   REWRITE_TAC[LENGTH_SHA3_256; LENGTH_MLKEM_SLICE]);;

(*** The RIP of the branch on the hash check at state k, as the check ***)

let API_HASH_CHECK_TAC k dkv cv hek ht kk =
  let sv = state_of kk in
  let lth = SPECL [dkv; cv] (de_check_th k) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && lhand c = mk_comb(`read RIP`,sv) then
      MP_TAC th THEN
      W(fun (_,w) ->
        MP_TAC(PART_MATCH (lhand o rand) WORD_OR_XOR_DIGITS_EQ_0
                (find_term (can (term_match [] `val(x:int64) = 0`)) w))) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [MP_TAC(ISPEC hek NUM_OF_BYTELIST_BOUND) THEN
          REWRITE_TAC[LENGTH_SHA3_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
          SIMP_TAC[];
          MP_TAC(ISPEC ht NUM_OF_BYTELIST_BOUND) THEN
          REWRITE_TAC[LENGTH_MLKEM_SLICE] THEN CONV_TAC NUM_REDUCE_CONV THEN
          SIMP_TAC[]];
        DISCH_THEN SUBST1_TAC] THEN
      MP_TAC lth THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN DISCH_TAC
    else NO_TAC);;

(*** Numbers equal iff their 256-bit chunks are ***)

let NUM_EQ_CHUNKS256 = prove
 (`!x y n. x < 2 EXP (256 * n) /\ y < 2 EXP (256 * n)
           ==> (x = y <=>
                !i. i < n ==> (x DIV 2 EXP (256 * i)) MOD 2 EXP 256 =
                              (y DIV 2 EXP (256 * i)) MOD 2 EXP 256)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [SIMP_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `!m. m <= n ==> x MOD 2 EXP (256 * m) = y MOD 2 EXP (256 * m)`
   (MP_TAC o SPEC `n:num`) THENL
   [INDUCT_TAC THENL [REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1]; ALL_TAC] THEN
    DISCH_TAC THEN
    REWRITE_TAC[ARITH_RULE `256 * SUC m = 256 * m + 256`; EXP_ADD;
                MOD_MULT_MOD] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
    ASM_SIMP_TAC[MOD_LT; LE_REFL]]);;

(*** The comparison of c (at ct) with c' (n 32-byte blocks): the ZF fact at
 *** state k as c' = c
 ***)

let API_CMP_TAC c cp n kk (asl,w as gl) =
  let sv = state_of kk in
  let zf = mk_comb(`read ZF`,sv) in
  let th = find_asm (fun t -> is_iff t && lhand t = zf) gl in
  let nc = mk_comb(`num_of_bytelist`,c)
  and ncp = mk_comb(`num_of_bytelist`,cp) in
  let lc = find_asm (fun t -> t = mk_eq(mk_comb(`LENGTH:byte list->num`,c),
                                        mk_small_numeral(32 * n))) gl in
  let lcp = (REWRITE_CONV(map pe_len [2;3;4]) THENC NUM_REDUCE_CONV)
              (mk_comb(`LENGTH:byte list->num`,cp)) in
  let bnd l lth =
    let b0 = ISPEC l NUM_OF_BYTELIST_BOUND in
    let b1 = REWRITE_RULE[lth] b0 in
    let b2 = CONV_RULE(RAND_CONV NUM_REDUCE_CONV) b1 in
    let tgt = mk_binop `(<):num->num->bool` (mk_comb(`num_of_bytelist`,l))
               (mk_binop `EXP` `2` (mk_binop `( * ):num->num->num` `256`
                  (mk_small_numeral n))) in
    let eqn = NUM_REDUCE_CONV (rand tgt) in
    EQ_MP (SYM(AP_TERM (rator tgt) eqn)) b2 in
  let goal = mk_iff(zf,mk_eq(cp,c)) in
  (SUBGOAL_THEN goal ASSUME_TAC THENL
    [REWRITE_TAC[th; VAL_EQ_0; WORD_AND_REFL; WORD_OR_EQ_0; WORD_XOR_EQ_0] THEN
     REWRITE_TAC[WORD_EQ; DIMINDEX_256; CONG] THEN
     CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
     REWRITE_TAC[MOD_MOD_REFL] THEN
     MP_TAC(MP (SPECL [nc; ncp; mk_small_numeral n] NUM_EQ_CHUNKS256)
               (CONJ (bnd c lc) (bnd cp lcp))) THEN
     CONV_TAC(LAND_CONV(RAND_CONV(EXPAND_CASES_CONV THENC
       ONCE_DEPTH_CONV NUM_REDUCE_CONV))) THEN
     REWRITE_TAC[DIV_1] THEN DISCH_TAC THEN
     FIRST_X_ASSUM(fun lth ->
       let c2 = rand(concl lth) in
       W(fun (_,w) ->
         let c1 = lhand w in
         let eq12 = CONJ_ACI_RULE(mk_eq(c1,c2)) in
         REWRITE_TAC[eq12; GSYM lth])) THEN
     MP_TAC(ISPECL [c; cp] NUM_OF_BYTELIST_INJ) THEN
     REWRITE_TAC[lcp; lc] THEN DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC[EQ_SYM_EQ];
     FIRST_X_ASSUM(fun t -> if concl t = concl th then ALL_TAC else NO_TAC)])
  gl;;

(*** The selected 32 bytes at ss: the byte-wise blend of a 256-bit word y
 *** (all its bytes) is y, and the bytes as the number of the list l
 ***)

let API_BLEND_TAC l kk (asl,w as gl) =
  let sv = state_of kk in
  let lhs0 = vsubst [sv,`s:x86state`]
    `read (memory :> bytes256 ss) s` in
  let th = find_asm (fun t -> is_eq t && lhand t = lhs0) gl in
  let rhs0 = rand(concl th) in
  let ys = setify(find_terms (fun t ->
     try fst(dest_const(rator(rator t))) = "word_subword" &&
         type_of(rand(rator t)) = `:256 word`
     with Failure _ -> false) rhs0) in
  let y = rand(rator(hd ys)) in
  let yv = mk_var("y",`:256 word`) in
  let gen = subst [yv,y] rhs0 in
  let eqth = WORD_BLAST(mk_eq(gen,yv)) in
  let eqth' = INST [y,yv] eqth in
  let nl = mk_comb(`num_of_bytelist`,l) in
  let lenl = (REWRITE_CONV[LENGTH_MLKEM_G; LENGTH_SHA3_256; LENGTH_SHA3_512;
                           LENGTH_MLKEM_SLICE; LENGTH_LIST_OF_SEQ] THENC
              NUM_REDUCE_CONV) (mk_comb(`LENGTH:byte list->num`,l)) in
  let bth = CONV_RULE(RAND_CONV NUM_REDUCE_CONV)
              (REWRITE_RULE[lenl] (ISPEC l NUM_OF_BYTELIST_BOUND)) in
  let goal = vsubst [sv,`s:x86state`; nl,`n:num`]
    `read (memory :> bytes(ss,32)) s = n` in
  (SUBGOAL_THEN goal ASSUME_TAC THENL
    [REWRITE_TAC[READ_MEMORY_BYTES_32; REWRITE_RULE[eqth'] th] THEN
     REWRITE_TAC[VAL_WORD; DIMINDEX_256] THEN
     CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
     REWRITE_TAC[MOD_MOD_REFL] THEN MATCH_MP_TAC MOD_LT THEN
     ACCEPT_TAC bth;
     ALL_TAC]) gl;;

(*** Decapsulation with the slices of dk and the G and J outputs ***)

let de_decaps_alt k =
  let def = match k with 2 -> mlkem512 | 3 -> mlkem768 | _ -> mlkem1024 in
  let ps = match k with
      2 -> [`2`; `3`; `2`; `10`; `4`] | 3 -> [`3`; `2`; `2`; `10`; `4`]
    | _ -> [`4`; `2`; `2`; `11`; `5`] in
  let th = ISPECL ps MLKEM_DECAPS_ALT in
  let th1 = CONV_RULE(TOP_DEPTH_CONV let_CONV) th in
  let th2 = CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV) th1 in
  REWRITE_RULE[GSYM def] th2;;

(* ------------------------------------------------------------------------- *)
(* The proof of dec for k with the theorems gmth of gen_matrix (with the H   *)
(* and J jobs, and for k = 3, 4 the noise too) and pdth, peth of the K-PKE   *)
(* functions.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE2_DEC_CORRECT_TAC k ex gmth (pdth,peth) =
  let nm = api_param k in
  let lo = layout(nm ^ "_dec") in
  let hi = lo + layout(nm ^ "_dec_size") in
  let next = API_TO_CALL_TAC ex lo hi in
  let zs = zip (api_zero_loops (nm ^ "_dec"))
               (map (API_ZERO_LOOP ex) (api_zero_loops (nm ^ "_dec"))) in
  let zv = el 0 zs and zi = el 1 zs in
  let fb = `fb:int64` in
  let wadd a n = mk_comb(mk_comb(`word_add:int64->int64->int64`,a),
                         mk_comb(`word:num->int64`,mk_small_numeral n)) in
  let dkv = `dk:byte list` and cv = `c:byte list` in
  let skb = kp_skb k and ctb = pe_ctb k and pkb = kp_pkb k in
  let sl a n = parse_term("mlkem_slice "^string_of_int a^" "^
                          string_of_int n^" dk") in
  let dkpke = sl 0 (384 * k) and ekt = sl (384 * k) pkb
  and ht = sl (768 * k + 32) 32 and zt = sl (768 * k + 64) 32
  and rho_dk = sl (768 * k) 32 in
  let mprime = list_mk_icomb "kpke_decrypt" [mk_const(nm,[]); dkpke; cv] in
  let gmsg = list_mk_icomb "APPEND" [mprime; ht] in
  let glen = (REWRITE_CONV[LENGTH_APPEND; pd_len k; LENGTH_MLKEM_SLICE] THENC
              NUM_REDUCE_CONV) (mk_comb(`LENGTH:byte list->num`,gmsg)) in
  let nc = mk_comb(`num_of_bytelist`,cv) in
  let zc = list_mk_icomb "APPEND" [zt; cv] in
  let lc = ASSUME(mk_eq(mk_comb(`LENGTH:byte list->num`,cv),
                        mk_small_numeral ctb)) in
  let rr_t = list_mk_icomb "SND" [list_mk_icomb "mlkem_g" [gmsg]]
  and kk_t = list_mk_icomb "FST" [list_mk_icomb "mlkem_g" [gmsg]] in
  let hek = list_mk_icomb "sha3_256" [ekt] in
  let dcheck = parse_term("mlkem_decaps_check "^nm^" dk c") in
  let cprime = list_mk_icomb "kpke_encrypt"
                 [mk_const(nm,[]); ekt; mprime; rr_t] in
  let ncp = mk_comb(`num_of_bytelist`,cprime) in
  let ceq = mk_eq(cprime,cv) in
  let jt = list_mk_icomb "list_of_seq" [mk_comb(`shake256`,zc); `32`] in
  let dalt = de_decaps_alt k in
  let gm_args r =
    [r `RDI`; r `RSI`; rho_dk; r `R8`; wadd `sk:int64` (384 * k); ekt;
     wadd fb de_hek; wadd fb de_zc; zc; wadd fb de_j; r `R9`] @
    (if k = 2 then []
     else [wadd fb (de_kr + 32); rr_t; wadd fb (de_noise k)]) @
    [`word(pc + 61952):int64`] in
  let final =
    API_EXPAND_FB_TAC THEN ENSURES_FINAL_STATE_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[mlkem_g]) THEN
    ASM_REWRITE_TAC[dalt; mlkem_g] in
  let valid =
    next THEN
    ON_STATE(fun kk gl ->
      let r c = find_read_fact c kk gl in
      let th = REWRITE_RULE[PAIRWISE; ALLPAIRS; ALL; LENGTH_MLKEM_SLICE;
                            pd_len k]
        (SPECL [r `RDI`; r `RSI`; r `RDX`; r `RCX`; r `R8`; ekt; mprime; rr_t;
                `pc:num`; r `RSP`; api_ret kk gl] peth) in
      let th' = CONV_RULE(DEPTH_CONV NUM_ADD_CONV)
                 (SIMP_RULE[MLKEM_SLICE_SLICE; ARITH_RULE(parse_term(
                   string_of_int(384 * k)^" + 32 <= "^string_of_int pkb))]
                  th) in
      (API_ALIGNED_TAC kk THEN API_IMAGE_CALL_TAC ex th' kk) gl) THEN
    API_RSP_TAC THEN
    API_DROP256_TAC `ct:int64` THEN
    ON_STATE(API_BLOCKS256_TAC `ct:int64` ctb nc 0 (ctb / 32)) THEN
    ON_STATE(API_BLOCKS256_TAC (wadd fb (de_ct2 k)) ctb ncp 0 (ctb / 32)) THEN
    ON_STATE(fun kk -> X86_STEPS_TAC ex ((kk+1)--(kk + 3 + 3 * (ctb / 32))))
    THEN
    ON_STATE(API_CMP_TAC cv cprime (ctb / 32)) THEN
    API_BOOL_CASE_TAC ceq THEN
    ON_STATE(API_BYTES256_OF_TAC (wadd fb de_j) (mk_comb(`num_of_bytelist`,jt))
              32 0) THEN
    ON_STATE(API_BYTES256_OF_TAC (wadd fb de_kr)
              (mk_comb(`num_of_bytelist`,kk_t)) 32 0) THEN
    ON_STATE(fun kk -> X86_STEPS_TAC ex ((kk+1)--(kk+8))) THENL
     [ON_STATE(API_BLEND_TAC kk_t); ON_STATE(API_BLEND_TAC jt)] THEN
    API_TO_PC_TAC ex (fst(fst zv) - 5) THEN
    ON_STATE(API_ZERO_STEP_TAC ex (snd zv)) THEN
    API_TO_PC_TAC ex (-1) THEN final in
  let invalid =
    API_TO_PC_TAC ex (fst(fst zi) - 5) THEN
    ON_STATE(API_ZERO_STEP_TAC ex (snd zi)) THEN
    API_TO_PC_TAC ex (-1) THEN final in
  API_ENTRY_TAC ex
   [`ss:int64`; `ct:int64`; `sk:int64`; `dk:byte list`; `c:byte list`;
    `pc:num`] (de_stack k) (de_frame k) THEN

  (*** m' = K-PKE.Decrypt(dk, c) ***)

  next THEN ON_STATE(fun kk -> API_SLICE_AT_TAC `sk:int64` dkv 0 (384 * k) kk)
  THEN
  ON_STATE(fun kk gl ->
    let r c = find_read_fact c kk gl in
    let th = REWRITE_RULE[PAIRWISE; ALLPAIRS; ALL; LENGTH_MLKEM_SLICE]
      (SPECL [r `RDI`; r `RSI`; r `RDX`; cv; dkpke; `pc:num`; r `RSP`;
              api_ret kk gl] pdth) in
    (API_ALIGNED_TAC kk THEN API_IMAGE_CALL_TAC ex th kk) gl) THEN
  API_RSP_TAC THEN

  (*** (K', r') = G(m' || h) ***)

  ON_STATE(fun kk -> API_SLICE_AT_TAC `sk:int64` dkv (skb - 64) 32 kk) THEN
  ON_STATE(API_BYTES256_OF_TAC (wadd `sk:int64` (skb - 64))
            (mk_comb(`num_of_bytelist`,ht)) 32 0) THEN
  next THEN
  ON_STATE(fun kk gl ->
    (MP_TAC(SPECL [wadd fb de_gin; mprime; ht; state_of kk]
       READ_MEMORY_BYTES_64_OF_32_256) THEN ANTS_TAC THENL
      [REWRITE_TAC[pd_len k; LENGTH_MLKEM_SLICE] THEN
       CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
       CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
       ASM_REWRITE_TAC[] THEN NO_TAC;
       DISCH_TAC]) gl) THEN
  ON_STATE(API_HASH_G_CALL_TAC ex gmsg glen) THEN API_RSP_TAC THEN
  ON_STATE API_G_SPLIT_TAC THEN

  (*** z || c ***)

  ON_STATE(fun kk -> API_SLICE_AT_TAC `sk:int64` dkv (skb - 32) 32 kk) THEN
  ON_STATE(API_BYTES256_OF_TAC (wadd `sk:int64` (skb - 32))
            (mk_comb(`num_of_bytelist`,zt)) 32 0) THEN
  ON_STATE(API_BLOCKS256_TAC `ct:int64` ctb nc 0 (ctb / 32)) THEN
  ON_STATE(fun kk -> X86_STEPS_TAC ex ((kk+1)--(kk + 2 + 2 * (ctb / 32))))
  THEN
  ON_STATE(API_JOIN256_TAC (wadd fb de_zc) zt 1) THEN
  ON_STATE(API_JOIN256_TAC (wadd fb (de_zc + 32)) cv (ctb / 32)) THEN
  ON_STATE(fun kk ->
    SUBGOAL_THEN (vsubst [state_of kk,`s:x86state`;
                          mk_small_numeral(32 + ctb),`n:num`;
                          zc,`l:byte list`; wadd fb de_zc,`a:int64`]
      `read (memory :> bytes(a,n)) s = num_of_bytelist l`) ASSUME_TAC THENL
     [REWRITE_TAC[NUM_OF_BYTELIST_APPEND; LENGTH_MLKEM_SLICE] THEN
      REWRITE_TAC[ARITH_RULE(mk_eq(mk_small_numeral(32 + ctb),
        mk_binop `(+):num->num->num` `32` (mk_small_numeral ctb)));
        READ_MEMORY_BYTES_SPLIT] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      ASM_REWRITE_TAC[] THEN NO_TAC;
      ALL_TAC]) THEN

  (*** The matrix with H(ek) and J(z || c), and the noise ***)

  next THEN
  ON_STATE(fun kk -> API_SLICE_AT_TAC `sk:int64` dkv (768 * k) 32 kk) THEN
  ON_STATE(fun kk -> API_SLICE_AT_TAC `sk:int64` dkv (384 * k) pkb kk) THEN
  ON_STATE(fun kk gl ->
    let r c = find_read_fact c kk gl in
    let th = REWRITE_RULE[PAIRWISE; ALLPAIRS; ALL; LENGTH_MLKEM_G;
                          LENGTH_APPEND; LENGTH_MLKEM_SLICE; lc]
      (SPECL (gm_args r @ [`pc:num`; r `RSP`; api_ret kk gl]) gmth) in
    let th' = CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV) th in
    (API_CONSTS_TAC kk THEN API_ALIGNED_TAC kk THEN
     API_IMAGE_CALL_TAC ex th' kk) gl) THEN
  API_RSP_TAC THEN
  (if k = 2 then
     next THEN ON_STATE(API_GETNOISE_CALL_TAC ex rr_t) THEN API_RSP_TAC
   else ALL_TAC) THEN
  ON_STATE API_NOISE_FORM_TAC THEN

  (*** The hash check of dk ***)

  ON_STATE(fun kk -> API_SLICE_AT_TAC `sk:int64` dkv (skb - 64) 32 kk) THEN
  ON_STATE(fun kk -> BIGDIGITS_32_TAC (wadd fb de_hek)
            (mk_comb(`num_of_bytelist`,hek)) (state_of kk)) THEN
  ON_STATE(fun kk -> BIGDIGITS_32_TAC (wadd `sk:int64` (skb - 64))
            (mk_comb(`num_of_bytelist`,ht)) (state_of kk)) THEN
  ON_STATE(fun kk -> X86_STEPS_TAC ex ((kk+1)--(kk+12))) THEN
  ON_STATE(API_HASH_CHECK_TAC k dkv cv hek ht) THEN
  API_BOOL_CASE_TAC dcheck THENL [valid; invalid];;
