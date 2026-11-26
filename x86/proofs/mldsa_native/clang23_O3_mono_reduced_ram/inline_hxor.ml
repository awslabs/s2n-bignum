(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The loops that clang 23 makes of mld_keccakf1600_xor_bytes when it        *)
(* inlines the absorbing of a message of any length into a SHAKE256 state    *)
(* (in mld_H44, mld_H65 and mld_H87): they XOR chunks of 32, 4 or 1 bytes of *)
(* the data at m into the state at a, from byte off of the state. As in the  *)
(* proof of keccakf1600_xor_bytes of the gcc12_O2_reduced_ram build, the     *)
(* state is a 1600-bit word S and the len bytes of data a number Tm; after  *)
(* c bytes, the state is word_xor S (word(2 EXP (8 * off) * Tm MOD 2 EXP (8 *)
(* * c))). The invariant of a loop gives the bytes of the state one by one,  *)
(* and the facts for the bytes that an iteration does not write are          *)
(* restricted so that the simulator keeps them over its stores. This file    *)
(* has the arithmetic, and a generator of the lemma for one loop, from its   *)
(* head to its exit, with the registers as parameters.                       *)
(* ========================================================================= *)

(* inline_sign.ml and inline_sponge_*.ml (under inline_sponge_region.ml)     *)
(* use mldsa_native_top.ml, mldsa_native_verify.ml, mldsa_native_signing.ml  *)
(* and the permutation theorem without loading them                          *)
needs "x86/proofs/utils/mldsa_native_top.ml";;
needs "x86/proofs/utils/mldsa_native_verify.ml";;
needs "x86/proofs/utils/mldsa_native_signing.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/keccakf1600_permute_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sponge_region.ml";;

let hx_add a b = mk_binop `(+):num->num->num` a b;;
let hx_lt a b = mk_binop `(<):num->num->bool` a b;;
let hx_le a b = mk_binop `(<=):num->num->bool` a b;;

(* ------------------------------------------------------------------------- *)
(* One byte and a chunk of w bytes, at offset off + c of the state.          *)
(* ------------------------------------------------------------------------- *)

let HX_BYTE_STEP = prove
 (`!(S:1600 word) m off i j.
        off + i < 200 /\ j < 200
        ==> word_subword
             (word_xor S (word(2 EXP (8 * off) *
                               m MOD 2 EXP (8 * (i + 1)))))
             (8 * j,8):byte =
            if j = off + i
            then word_xor
                  (word_subword
                    (word_xor S (word(2 EXP (8 * off) * m MOD 2 EXP (8 * i))))
                    (8 * j,8))
                  (word((m DIV 2 EXP (8 * i)) MOD 256))
            else word_subword
                  (word_xor S (word(2 EXP (8 * off) * m MOD 2 EXP (8 * i))))
                  (8 * j,8)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  SUBGOAL_THEN
   `2 EXP (8 * off) * m MOD 2 EXP (8 * (i + 1)) =
    2 EXP (8 * off) * m MOD 2 EXP (8 * i) +
    2 EXP (8 * (off + i)) * (m DIV 2 EXP (8 * i)) MOD 256`
  SUBST1_TAC THENL
   [REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; MULT_CLAUSES;
                ARITH_RULE `2 EXP 8 = 256`; MOD_MULT_MOD] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[WORD_SUBWORD_WORD; DIMINDEX_CONV `dimindex(:1600)`;
               DIMINDEX_8; ARITH_RULE `j < 200 ==> 8 * j + 8 <= 1600`] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SPONGE_BYTE_UPDATE o
    rand o rand o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ; ARITH_EQ] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; LT_MULT_LCANCEL] THEN
    REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ];
    DISCH_THEN SUBST1_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  SUBGOAL_THEN `2 EXP (8 * off) * m MOD 2 EXP (8 * i) < 2 EXP (8 * (off + i))`
   (fun th -> SIMP_TAC[th; DIV_LT; MOD_0; WORD_XOR_0]) THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; LT_MULT_LCANCEL] THEN
  REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ]);;

let HX_CHUNK_STEP = prove
 (`!(S:1600 word) m off c w j.
        off + c + w <= 200 /\ j < 200
        ==> word_subword
             (word_xor S (word(2 EXP (8 * off) * m MOD 2 EXP (8 * (c + w)))))
             (8 * j,8):byte =
            if off + c <= j /\ j < off + c + w
            then word_xor
                  (word_subword
                    (word_xor S (word(2 EXP (8 * off) * m MOD 2 EXP (8 * c))))
                    (8 * j,8))
                  (word((m DIV 2 EXP (8 * (j - off))) MOD 256))
            else word_subword
                  (word_xor S (word(2 EXP (8 * off) * m MOD 2 EXP (8 * c))))
                  (8 * j,8)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `c + SUC w = (c + w) + 1`] THEN
  MP_TAC(SPECL [`S:1600 word`; `m:num`; `off:num`; `c + w`; `j:num`]
         HX_BYTE_STEP) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_CASES_TAC `j = off + c + w` THENL
   [SUBGOAL_THEN `j - off = c + w` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[ADD_ASSOC; ARITH_RULE `~(x < x)`;
                    ARITH_RULE `off + c <= (off + c) + w`;
                    ARITH_RULE `x < x + SUC 0`; ADD1;
                    ARITH_RULE `x < (x + 1)`];
    SUBGOAL_THEN `~(j = off + c + w)` (fun th -> REWRITE_TAC[th; GSYM ADD_ASSOC]) THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(off + c <= j /\ j < off + c + w + 1) <=>
                  (off + c <= j /\ j < off + c + w)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[]]]);;

let HX_CHUNK_STEP0 = prove
 (`!(S:1600 word) m c w j.
        c + w <= 200 /\ j < 200
        ==> word_subword (word_xor S (word(m MOD 2 EXP (8 * (c + w))))) (8 * j,8):byte =
            if c <= j /\ j < c + w
            then word_xor (word_subword (word_xor S (word(m MOD 2 EXP (8 * c)))) (8 * j,8))
                          (word((m DIV 2 EXP (8 * j)) MOD 256))
            else word_subword (word_xor S (word(m MOD 2 EXP (8 * c)))) (8 * j,8)`,
  REPEAT GEN_TAC THEN MP_TAC(SPECL [`S:1600 word`; `m:num`; `0`; `c:num`; `w:num`; `j:num`] HX_CHUNK_STEP) THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES; SUB_0]);;

(* ------------------------------------------------------------------------- *)
(* Chunks of N bits at any byte offset k of the state and of the data.       *)
(* ------------------------------------------------------------------------- *)

let HX_NUM_CHUNK n =
  let sub = subst_tokens ["@N@",string_of_int n; "@NB@",string_of_int (n/8);
                          "@P@",(match n with 32 -> "4294967296" | 64 -> "18446744073709551616" | _ -> "340282366920938463463374607431768211456");
                          "@BN@",Printf.sprintf "bytes%d" n] in
  let wth = (match n with 32 -> BYTES32_WBYTES
             | 64 -> BYTES64_WBYTES | _ -> BYTES128_WBYTES) in
  prove(parse_term(sub
   "!(a:int64) l x k (s:x86state).
        read (memory :> bytes(a,l)) s = x /\\ k + @NB@ <= l
        ==> read (memory :> @BN@ (word_add a (word k))) s =
            word((x DIV 2 EXP (8 * k)) MOD 2 EXP @N@)"),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[wth; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) then SUBST1_TAC(SYM th)
                        else NO_TAC) THEN
  REWRITE_TAC[ARITH_RULE(parse_term(sub "@P@ = 2 EXP (8 * @NB@)"))] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD;
              MOD_MOD_REFL] THEN
  SUBGOAL_THEN(parse_term(sub "MIN (l - k) @NB@ = @NB@")) SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[]);;

let HX_NUM_CHUNK32 = HX_NUM_CHUNK 32;;
let HX_NUM_CHUNK128 = HX_NUM_CHUNK 128;;

let HX_WBYTES_CHUNK n =
  let sub = subst_tokens ["@N@",string_of_int n; "@NB@",string_of_int (n/8);
                          "@BN@",Printf.sprintf "bytes%d" n] in
  let nth = HX_NUM_CHUNK n in
  prove(parse_term(sub
   "!(a:int64) (X:1600 word) k (s:x86state).
        read (memory :> wbytes a) s = X /\\ k + @NB@ <= 200
        ==> read (memory :> @BN@ (word_add a (word k))) s =
            word_subword X (8 * k,@N@)"),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `200`; `val(X:1600 word)`; `k:num`; `s:x86state`] nth) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
      CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE];
      ASM_ARITH_TAC];
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[word_subword] THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MOD_MOD_REFL]]);;

let HX_WBYTES_CHUNK32 = HX_WBYTES_CHUNK 32;;
let HX_WBYTES_CHUNK128 = HX_WBYTES_CHUNK 128;;

(* A byte of a chunk of the state XORed with a chunk of the data *)

let HX_CHUNK_BYTE n =
  let sub = subst_tokens ["@N@",string_of_int n; "@NB@",string_of_int (n/8)] in
  prove(parse_term(sub
 "!(Y:1600 word) Tm k i t. t < @NB@ /\\ 8 * k + @N@ <= 1600
     ==> word_subword (word_xor (word_subword Y (8 * k,@N@):(@N@)word)
                                (word((Tm DIV 2 EXP (8 * i)) MOD 2 EXP @N@))) (8 * t,8):byte =
         word_xor (word_subword Y (8 * (k + t),8))
                  (word((Tm DIV 2 EXP (8 * (i + t))) MOD 256))"),
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_SUBWORD_XOR] THEN
  MATCH_MP_TAC(MESON[] `a = a' /\ b = b' ==> word_xor a b:byte = word_xor a' b'`) THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`Y:1600 word`; `8 * k`; parse_term(sub "@N@"); `8 * t`; `8`]
      (INST_TYPE [parse_type(sub "(@N@)"),`:N`; `:1600`,`:M`; `:8`,`:P`] WORD_SUBWORD_SUBWORD)) THEN
    REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`; DIMINDEX_32; DIMINDEX_128; DIMINDEX_8] THEN
    CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN (parse_term(sub "MIN 8 (@N@ - 8 * t) = 8")) SUBST1_TAC THENL
     [UNDISCH_TAC (parse_term(sub "t < @NB@")) THEN ARITH_TAC;
      REWRITE_TAC[LEFT_ADD_DISTRIB]];
    ASM_SIMP_TAC[WORD_SUBWORD_WORD; DIMINDEX_32; DIMINDEX_128; DIMINDEX_8;
                 ARITH_RULE(parse_term(sub "t < @NB@ ==> 8 * t + 8 <= @N@"))] THEN
    REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2 EXP 8 = 256`] THEN
    AP_TERM_TAC THEN
    MP_TAC(SPECL [parse_term(sub "Tm DIV 2 EXP (8 * i)"); parse_term(sub "@N@"); `t:num`] SPONGE_MODDIV_BYTE) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`; DIV_DIV; GSYM EXP_ADD] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LEFT_ADD_DISTRIB]]);;

let HX_CHUNK_BYTE32 = HX_CHUNK_BYTE 32;;
let HX_CHUNK_BYTE128 = HX_CHUNK_BYTE 128;;

(* ------------------------------------------------------------------------- *)
(* The facts !j. j < 200 ==> read (bytes8 ..) s = .. restricted to the bytes *)
(* other than t, or to those below p and from p + w on, so that the          *)
(* simulator keeps them over a store to byte t or to bytes p .. p + w - 1.   *)
(* ------------------------------------------------------------------------- *)

let HX_RESTRICT_NEQ t th =
  let j,bod = dest_forall(concl th) in
  let p,q = dest_imp bod in
  let p' = mk_conj(p,mk_neg(mk_eq(j,t))) in
  GEN j (DISCH p' (MP (SPEC j th) (CONJUNCT1(ASSUME p'))));;

let HX_RESTRICT_RANGE p w th =
  let j,bod = dest_forall(concl th) in
  let pr,q = dest_imp bod in
  let jl = mk_comb(mk_comb(`(<):num->num->bool`,j),p) in
  let jh = mk_comb(mk_comb(`(<=):num->num->bool`,mk_binop `(+):num->num->num` p w),j) in
  let mk c = let pr' = mk_conj(pr,c) in GEN j (DISCH pr' (MP (SPEC j th) (CONJUNCT1(ASSUME pr')))) in
  [mk jl; mk jh];;

(* ------------------------------------------------------------------------- *)
(* The bytes of a stored chunk of the state XORed with a chunk of the data.  *)
(* ------------------------------------------------------------------------- *)

let HX_STORED n =
  let sub = subst_tokens ["@N@",string_of_int n; "@NB@",string_of_int (n/8);
                          "@BN@",Printf.sprintf "bytes%d" n] in
  let cth = if n = 32 then SPONGE_BYTES8_OF_CHUNK32 else SPONGE_BYTES8_OF_CHUNK128 in
  let bth = HX_CHUNK_BYTE n in
  prove(parse_term(sub
   "!(a:int64) (X:1600 word) Tm k i (s:x86state).
      read (memory :> @BN@ (word_add a (word k))) s =
        word_xor (word_subword X (8 * k,@N@))
                 (word((Tm DIV 2 EXP (8 * i)) MOD 2 EXP @N@)) /\\
      k + @NB@ <= 200
      ==> !t. t < @NB@
              ==> read (memory :> bytes8 (word_add a (word (k + t)))) s =
                  word_xor (word_subword X (8 * (k + t),8))
                           (word((Tm DIV 2 EXP (8 * (i + t))) MOD 256))"),
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`word_add a (word k):int64`; parse_term(sub "word_xor (word_subword (X:1600 word) (8 * k,@N@)) (word((Tm DIV 2 EXP (8 * i)) MOD 2 EXP @N@)):(@N@)word"); `t:num`; `s:x86state`] cth) THEN
  ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC bth THEN ASM_ARITH_TAC);;

let HX_STORED32 = HX_STORED 32;;
let HX_STORED128 = HX_STORED 128;;

(* ------------------------------------------------------------------------- *)
(* The loop tests: a bound register compared with the index, and a counter.  *)
(* ------------------------------------------------------------------------- *)

let HX_TEST_BOUND_W w = prove
 (subst [mk_small_numeral w,`w:num`]
   `!c0 n i. i < n /\ c0 + w * n < 2 EXP 64
        ==> (~(val(word_sub (word (c0 + w * n)) (word_add (word (c0 + w * i)) (word w)):int64) = 0)
             <=> i + 1 < n)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; GSYM WORD_ADD] THEN
  SUBGOAL_THEN (subst [mk_small_numeral w,`w:num`] `(c0 + w * i) + w < 2 EXP 64`) ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[WORD_EQ; DIMINDEX_64; CONG; MOD_LT] THEN ASM_ARITH_TAC);;

let HX_TEST_BOUND1 = HX_TEST_BOUND_W 1;;
let HX_TEST_BOUND4 = HX_TEST_BOUND_W 4;;
let HX_TEST_BOUND32 = HX_TEST_BOUND_W 32;;

let HX_TEST_COUNT = prove
 (`!n i. i < n /\ n < 2 EXP 64
        ==> (~(val(word_sub (word (n - i)) (word 1):int64) = 0) <=> i + 1 < n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_sub (word (n - i)) (word 1):int64 = word (n - (i + 1))` SUBST1_TAC THENL
   [SUBGOAL_THEN `1 <= n - i` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[WORD_SUB2] THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `n - (i + 1) < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A loop that XORs chunks of the data into the state. hx_kind is "b" (one   *)
(* byte: movzx; xor byte), "d" (4 bytes: mov; xor dword), "va" (32 bytes:    *)
(* movups data; xorps with the state in memory; movaps) or "vu" (32 bytes:   *)
(* movups data; movups state; xorps; movups). The state is addressed through *)
(* hx_dst, which holds the address of byte off + hx_bias of the state at a   *)
(* (or, for hx_dst = "RSP", the state is at rsp0 + hx_bias and off = 0); the *)
(* data through hx_src; the index hx_idx counts the bytes from c0; the loop  *)
(* ends when hx_idx reaches hx_ctl (or, if hx_count, when the counter hx_ctl *)
(* reaches 0), after n iterations.                                           *)
(* ------------------------------------------------------------------------- *)

type hx_loop =
 { hx_fn : string; hx_head : int; hx_exit : int; hx_kind : string;
   hx_dst : string; hx_bias : int; hx_src : string; hx_idx : string;
   hx_ctl : string; hx_count : bool; hx_keep : (string * string) list };;

let hx_w l = match l.hx_kind with "b" -> 1 | "d" -> 4 | _ -> 32;;
let hx_nsteps l = match l.hx_kind with "b" | "d" -> 5 | "va" -> 9 | _ -> 11;;
let hx_rsp l = (l.hx_dst = "RSP");;
let hx_a l = if hx_rsp l then (if l.hx_bias = 0 then "rsp0" else Printf.sprintf "word_add rsp0 (word %d)" l.hx_bias) else "a";;
let hx_off l = if hx_rsp l then "0" else "off";;
let hx_dv l = if hx_rsp l then "rsp0" else if l.hx_bias = 0 then "word_add a (word off)"
              else Printf.sprintf "word_add a (word (off + %d))" l.hx_bias;;

let hx_tok l extra s =
  subst_tokens (extra @
   ["@CPRE@",(if l.hx_count then "word n" else "word (c0 + @W@ * n)");
    "@CPOST@",(if l.hx_count then "word 0" else "word (c0 + @W@ * n)");
    "@CINV@",(if l.hx_count then "word (n - i)" else "word (c0 + @W@ * n)");
    "@OFFP@",(if hx_rsp l then "" else "off + ");
    "@SC@",(if hx_rsp l then "" else "2 EXP (8 * off) * ");
    "@A@",hx_a l; "@OFF@",hx_off l; "@DV@",hx_dv l; "@D@",l.hx_dst;
    "@M@",l.hx_src; "@I@",l.hx_idx; "@C@",l.hx_ctl;
    "@W@",string_of_int (hx_w l);
    "@HEAD@",string_of_int (layout l.hx_fn + l.hx_head);
    "@EXIT@",string_of_int (layout l.hx_fn + l.hx_exit);
    "@VARS@",(if hx_rsp l then "rsp0" else "a off");
    "@KEEP@",String.concat "" (map (fun (r,v) -> Printf.sprintf "read %s s = %s /\\ " r v) l.hx_keep);
    "@ALIGN@",(if l.hx_kind = "va" then "aligned 16 rsp0 /\\ 16 divides c0 /\\" else "")]) s;;

let HX_EXEC l = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
  [(layout l.hx_fn + l.hx_head, layout l.hx_fn + l.hx_exit)];;

let HX_STMT l = parse_term(hx_tok l []
 "exists f_events. forall e @VARS@ m len c0 n (S:1600 word) Tm pc.
   @OFFP@len <= 200 /\\ c0 + @W@ * n <= len /\\ 0 < n /\\ @ALIGN@
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   nonoverlapping (m,len) (@A@,200) /\\
   nonoverlapping (word pc,libmldsa_size) (@A@,200)
   ==> ensures x86
    (\\s. bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
         read RIP s = word (pc + @HEAD@) /\\
         read @D@ s = @DV@ /\\ read @M@ s = m /\\ read @I@ s = word c0 /\\
         read @C@ s = @CPRE@ /\\ @KEEP@
         read (memory :> bytes(m,len)) s = Tm /\\
         read (memory :> wbytes (@A@)) s =
           word_xor S (word(@SC@Tm MOD 2 EXP (8 * c0))) /\\
         read events s = e)
    (\\s. read RIP s = word (pc + @EXIT@) /\\
         read @D@ s = @DV@ /\\ read @M@ s = m /\\ read @I@ s = word (c0 + @W@ * n) /\\
         read @C@ s = @CPOST@ /\\ @KEEP@
         read (memory :> bytes(m,len)) s = Tm /\\
         read (memory :> wbytes (@A@)) s =
           word_xor S (word(@SC@Tm MOD 2 EXP (8 * (c0 + @W@ * n)))) /\\
         (exists e2. read events s = APPEND e2 e /\\ e2 = f_events @VARS@ m len c0 n pc /\\
            memaccess_inbounds e2 [m,len; @A@,200] [@A@,200]))
    (MAYCHANGE [RIP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(@A@,200)])");;

let HX_INV l = parse_term(hx_tok l []
 "\\i s. read @D@ s = @DV@ /\\ read @M@ s = m /\\ read @I@ s = word (c0 + @W@ * i) /\\
        read @C@ s = @CINV@ /\\ @KEEP@
        read (memory :> bytes(m,len)) s = Tm /\\
        !j. j < 200
            ==> read (memory :> bytes8 (word_add (@A@) (word j))) s =
                word_subword
                 (word_xor (S:1600 word) (word(@SC@Tm MOD 2 EXP (8 * (c0 + @W@ * i)))))
                 (8 * j,8)");;

(* ------------------------------------------------------------------------- *)
(* The proof of a loop lemma.                                                *)
(* ------------------------------------------------------------------------- *)

(*** A word equation whose atoms (chunks of the 1600-bit state, words of  ***)
(*** numbers) are generalized, by bit-blasting                            ***)

let hx_is_atom t =
  is_comb t &&
  let f,args = strip_comb t in
  is_const f &&
  ((fst(dest_const f) = "word_subword" &&
    (match args with [x;_] -> type_of x = `:1600 word` | _ -> false)) ||
   (fst(dest_const f) = "word" &&
    (match args with [n] -> not (is_numeral n) && not (can (find_term (fun t -> try fst(dest_const t) = "val" with _ -> false)) n) | _ -> false)));;

let rec hx_size t = match t with Comb(a,b) -> hx_size a + hx_size b | Abs(_,b) -> 1 + hx_size b | _ -> 1;;

let HX_GEN_BLAST_TAC =
  REPEAT(W(fun (asl,w) ->
    let ats = find_terms hx_is_atom w in
    if ats = [] then NO_TAC else
    let t = itlist (fun a b -> if hx_size a >= hx_size b then a else b) ats (hd ats) in
    SPEC_TAC(t,genvar(type_of t)))) THEN
  REPEAT GEN_TAC THEN BITBLAST_TAC;;

(*** The address of an access [reg + idx + d] as the simulator writes it ***)

let hx_disp_tm d =
  if d >= 0 then mk_small_numeral d
  else mk_numeral(Num.sub_num (Num.power_num (Num.num_of_int 2) (Num.num_of_int 64)) (Num.num_of_int (-d)));;

(* for straight-line chunks at constant offsets (hx_const_x = Some x), the  *)
(* index is the numeral x and the accesses are [reg + x + d]                *)
let hx_const_x = par_local_ref (fun () -> (None:term option));;

let hx_sim_addr_m cmode base x d =
  if cmode <> None then
    let k = dest_small_numeral x + d in
    (if k = 0 then base
     else mk_comb(mk_comb(`word_add:int64->int64->int64`,base),mk_comb(`word:num->int64`,mk_small_numeral k)))
  else
  let one_x = mk_binop `( * ):num->num->num` `1` x in
  let off = if d = 0 then one_x else mk_binop `(+):num->num->num` one_x (hx_disp_tm d) in
  mk_comb(mk_comb(`word_add:int64->int64->int64`,base),mk_comb(`word:num->int64`,off));;

let hx_sim_addr base x d = hx_sim_addr_m !(hx_const_x ()) base x d;;

(*** A fact about memory at address t1 restated at the address t2 ***)

let HX_MOD64_ADD = prove
 (`!a. (a + 18446744073709551616) MOD 18446744073709551616 = a MOD 18446744073709551616`,
  GEN_TAC THEN ONCE_REWRITE_TAC[ARITH_RULE `a + n = 1 * n + a`] THEN REWRITE_TAC[MOD_MULT_ADD]);;

(* equality of addresses word_add b (word n): by WORD_RULE, or modulo 2^64 *)
(* for a displacement written as 2^64 - d                                   *)
let HX_ADDR_EQ_TAC =
  CONV_TAC WORD_RULE ORELSE
  (REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN AP_TERM_TAC THEN
   REWRITE_TAC[WORD_EQ; DIMINDEX_64; CONG] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
   W(fun (_,g) ->
     let l = lhand(lhand g) and r = lhand(rand g) in
     let n64 = `18446744073709551616` in
     (SUBGOAL_THEN (mk_eq(r,hx_add l n64)) SUBST1_TAC THENL [ARITH_TAC; REWRITE_TAC[HX_MOD64_ADD]]) ORELSE
     (SUBGOAL_THEN (mk_eq(l,hx_add r n64)) SUBST1_TAC THENL [ARITH_TAC; REWRITE_TAC[HX_MOD64_ADD]])));;

let HX_RETARGET th t2 =
  let t1 = rand(rand(lhand(lhand(concl th)))) in
  if t1 = t2 then th else
  let eq = prove(mk_eq(t1,t2),HX_ADDR_EQ_TAC) in
  GEN_REWRITE_RULE (LAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV) [eq] th;;

(*** The terms of a loop ***)



let hx_terms l =
  let w = mk_small_numeral (hx_w l) in
  let at = parse_term("(" ^ hx_a l ^ "):int64") and offt = parse_term("(" ^ hx_off l ^ "):num") in
  let x = match !(hx_const_x ()) with Some t -> t
          | None -> mk_binop `(+):num->num->num` `c0:num` (mk_binop `( * ):num->num->num` w `i:num`) in
  let k0 = if hx_rsp l then x else mk_binop `(+):num->num->num` offt x in
  w,at,offt,x,k0;;

let hx_hi l = let w,at,offt,x,k0 = hx_terms l in
  if hx_rsp l then hx_add x w else hx_add offt (hx_add x w);;
let hx_suboff l t = if hx_rsp l then t else mk_binop `(-):num->num->num` t `off:num`;;

(* the base register value of the state accesses and their displacements *)
let hx_dst_base l =
  if hx_rsp l then `rsp0:int64`,l.hx_bias else parse_term("(" ^ hx_dv l ^ "):int64"),(- l.hx_bias);;

let hx_chunks l = match l.hx_kind with "b" -> [0,8] | "d" -> [0,32] | _ -> [0,128; 16,128];;

let HX_A16 = prove
 (`!c0 i d. 16 divides c0 /\ 16 divides d ==> aligned 16 (word (1 * (c0 + 32 * i) + d):int64)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[divides] THEN STRIP_TAC THEN CONJ_TAC THENL
   [EXISTS_TAC `1152921504606846976` THEN ARITH_TAC;
    EXISTS_TAC `x + 2 * i + x'` THEN ASM_ARITH_TAC]);;

let HX_A16_0 = prove
 (`!c0 i. 16 divides c0 ==> aligned 16 (word (1 * (c0 + 32 * i)):int64)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`c0:num`; `i:num`; `0`] HX_A16) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; DIVIDES_0]);;

(* the alignment of the SSE accesses [rsp + idx + d] of a "va" loop *)
let HX_ALIGN_TAC l =
  if l.hx_kind <> "va" then ALL_TAC else
  let w,at,offt,x,k0 = hx_terms l in
  let ra = ASSUME `aligned 16 (rsp0:int64)` and dc = ASSUME `16 divides c0` in
  let one d =
    let dd = l.hx_bias + d in
    let ath = if dd = 0 then MP (SPECL [`c0:num`; `i:num`] HX_A16_0) dc
              else MP (SPECL [`c0:num`; `i:num`; mk_small_numeral dd] HX_A16)
                      (CONJ dc (EQT_ELIM(NUM_DIVIDES_CONV (mk_binop `divides` `16` (mk_small_numeral dd))))) in
    let th = MATCH_MP ALIGNED_WORD_ADD (CONJ ra ath) in
    let sa = hx_sim_addr `rsp0:int64` x dd in
    let na = try rhs(concl(NORMALIZE_RELATIVE_ADDRESS_CONV sa)) with _ -> sa in
    ASSUME_TAC th THEN
    (if na = sa then ALL_TAC else ASSUME_TAC(REWRITE_RULE[NORMALIZE_RELATIVE_ADDRESS_CONV sa] th)) in
  one 0 THEN one 16;;

let HX_ARITH_FROM c h = MP (ARITH_RULE (mk_imp(h,c))) (ASSUME h);;

let HX_LOAD_FACTS_TAC l =
  let w,at,offt,x,k0 = hx_terms l in
  let cmode = !(hx_const_x ()) in
  let hx_sim_addr = hx_sim_addr_m cmode in
  let db,dd = hx_dst_base l in
  let addk k d = if d = 0 then k else mk_binop `(+):num->num->num` k (mk_small_numeral d) in
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && free_in `bytes8` (concl th) then
      let wth = MATCH_MP SPONGE_WBYTES_OF_ALL_BYTES th in
      let state_fact (d,nb) =
        let k = addk k0 d in
        let sth =
          if nb = 8 then
            MATCH_MP SPONGE_BYTES8_OF_WBYTES (CONJ wth (HX_ARITH_FROM (mk_binop `(<):num->num->bool` k `200`) (mk_binop `(<=):num->num->bool` (mk_binop `(+):num->num->num` k0 w) `200`)))
          else
            let cth = if nb = 32 then HX_WBYTES_CHUNK32 else HX_WBYTES_CHUNK128 in
            let bnd = mk_binop `(<=):num->num->bool` (mk_binop `(+):num->num->num` k (mk_small_numeral (nb/8))) `200` in
            MATCH_MP cth (CONJ wth (HX_ARITH_FROM (bnd) (mk_binop `(<=):num->num->bool` (mk_binop `(+):num->num->num` k0 w) `200`))) in
        let sa = hx_sim_addr db x (dd + d) in
        if dd + d < 0 then
          (* an alias of the address with the negative displacement, which the *)
          (* simulator rewrites with, and the fact at the canonical address   *)
          let ca = rand(rand(lhand(lhand(concl sth)))) in
          let na = try rhs(concl(NORMALIZE_RELATIVE_ADDRESS_CONV ca)) with _ -> ca in
          ASSUME_TAC (prove(mk_eq(sa,ca),HX_ADDR_EQ_TAC)) THEN
          ASSUME_TAC sth THEN
          (if na = ca then ALL_TAC else ASSUME_TAC (HX_RETARGET sth na))
        else
        let na = try rhs(concl(NORMALIZE_RELATIVE_ADDRESS_CONV sa)) with _ -> sa in
        ASSUME_TAC (HX_RETARGET sth sa) THEN
        (if na = sa then ALL_TAC else ASSUME_TAC (HX_RETARGET sth na)) in
      MAP_EVERY ASSUME_TAC (HX_RESTRICT_RANGE k0 w th) THEN
      MAP_EVERY state_fact (hx_chunks l)
    else NO_TAC) THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [`m:int64`; `len:num`; `Tm:num`] `read (memory :> bytes (m,len)) s0 = Tm`) (concl th) then
      let data_fact (d,nb) =
        let k = addk x d in
        let dth =
          if nb = 8 then
            MATCH_MP READ_MEMORY_BYTES8_OF_NUM (CONJ th (HX_ARITH_FROM (mk_binop `(<):num->num->bool` k `len:num`) (mk_binop `(<=):num->num->bool` (mk_binop `(+):num->num->num` x w) `len:num`)))
          else
            let cth = if nb = 32 then HX_NUM_CHUNK32 else HX_NUM_CHUNK128 in
            let bnd = mk_binop `(<=):num->num->bool` (mk_binop `(+):num->num->num` k (mk_small_numeral (nb/8))) `len:num` in
            MATCH_MP cth (CONJ th (HX_ARITH_FROM (bnd) (mk_binop `(<=):num->num->bool` (mk_binop `(+):num->num->num` x w) `len:num`))) in
        let sa = hx_sim_addr `m:int64` x d in
        let na = try rhs(concl(NORMALIZE_RELATIVE_ADDRESS_CONV sa)) with _ -> sa in
        ASSUME_TAC (HX_RETARGET dth sa) THEN
        (if na = sa then ALL_TAC else ASSUME_TAC (HX_RETARGET dth na)) in
      MAP_EVERY data_fact (hx_chunks l)
    else NO_TAC);;

(*** The bytes of the state after the iteration ***)


let hx_x_state l =
  let w,at,offt,x,k0 = hx_terms l in
  let e8 = mk_binop `( * ):num->num->num` `8` in
  let p2 t = mk_binop `EXP` `2` t in
  let tm0 = mk_binop `MOD` `Tm:num` (p2 (e8 x)) in
  let tm = if hx_rsp l then tm0 else mk_binop `( * ):num->num->num` (p2 (e8 offt)) tm0 in
  mk_binop `word_xor:1600 word->1600 word->1600 word` `S:1600 word` (mk_comb(`word:num->1600 word`,tm));;

(* the stored chunk at byte k of the state, from its fact in the simulated   *)
(* form, as the XOR of the chunks of the state and the data                  *)
let HX_CANON_TAC (asl,w) =
  let lhs_w = lhand w in
  let comp = rand(lhand lhs_w) and sv = rand lhs_w in
  let ca = rand comp in
  let cand (_,th) =
    let c = concl th in
    is_eq c && is_comb(lhs c) &&
    (try rand(lhs c) = sv && rator(rand(lhand(lhs c))) = rator comp with _ -> false) &&
    (let a2 = rand(rand(lhand(lhs c))) in
     a2 = ca || can (fun () -> prove(mk_eq(ca,a2),HX_ADDR_EQ_TAC)) ()) in
  let _,th = find cand asl in
  let a2 = rand(rand(lhand(lhs(concl th)))) in
  let eq = if a2 = ca then REFL ca else prove(mk_eq(ca,a2),HX_ADDR_EQ_TAC) in
  (GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV) [eq] THEN
   REWRITE_TAC[th; WORD_VAL_MOD_256] THEN CONV_TAC NUM_REDUCE_CONV THEN HX_GEN_BLAST_TAC) (asl,w);;

let HX_INRANGE_TAC l =
  let w,at,offt,x,k0 = hx_terms l in
  let hi = hx_hi l in
  let xs = hx_x_state l in
  let addk k d = if d = 0 then k else hx_add k (mk_small_numeral d) in
  let chunk_tac (d,nb) =
    W(fun (asl,g) ->
      let st = rand(lhand g) in
      let k = addk k0 d and xd = addk x d in
      let nbt = mk_small_numeral (nb/8) in
      let tmpl = match nb with
          8 -> `read (memory :> bytes8 (word_add AA (word kk))) ss =
                word_xor (word_subword (XS:1600 word) (8 * kk,8)) (word((Tm DIV 2 EXP (8 * xx)) MOD 256))`
        | 32 -> `read (memory :> bytes32 (word_add AA (word kk))) ss =
                 word_xor (word_subword (XS:1600 word) (8 * kk,32)) (word((Tm DIV 2 EXP (8 * xx)) MOD 2 EXP 32))`
        | _ -> `read (memory :> bytes128 (word_add AA (word kk))) ss =
                word_xor (word_subword (XS:1600 word) (8 * kk,128)) (word((Tm DIV 2 EXP (8 * xx)) MOD 2 EXP 128))` in
      let canon = subst [k,`kk:num`; xd,`xx:num`; xs,`XS:1600 word`; at,`AA:int64`; st,`ss:x86state`] tmpl in
      SUBGOAL_THEN canon ASSUME_TAC THENL [HX_CANON_TAC; ALL_TAC] THEN
      (if nb = 8 then
         SUBGOAL_THEN (mk_eq(`j:num`,k)) SUBST1_TAC THENL
          [MAP_EVERY UNDISCH_TAC [mk_conj(hx_le k0 `j:num`, hx_lt `j:num` hi)] THEN ARITH_TAC;
           ALL_TAC] THEN
         (if hx_rsp l then ALL_TAC else
          SUBGOAL_THEN (mk_eq(hx_suboff l k, xd)) SUBST1_TAC THENL [ARITH_TAC; ALL_TAC]) THEN
         FIRST_ASSUM ACCEPT_TAC
       else
         let sth = if nb = 32 then HX_STORED32 else HX_STORED128 in
         FIRST_X_ASSUM(fun th -> if concl th = canon then
             MP_TAC(SPEC (mk_binop `(-):num->num->num` `j:num` k)
               (MATCH_MP sth (CONJ th (HX_ARITH_FROM (hx_le (hx_add k nbt) `200`) (hx_le (hx_add k0 w) `200`)))))
           else NO_TAC) THEN
         ANTS_TAC THENL
          [MAP_EVERY UNDISCH_TAC [mk_conj(hx_le k0 `j:num`, hx_lt `j:num` hi)] THEN
           (if d = 0 && nb < 8 * hx_w l then UNDISCH_TAC (hx_lt `j:num` (hx_add k0 `16`)) else
            if d > 0 then UNDISCH_TAC (mk_neg(hx_lt `j:num` (hx_add k0 `16`))) else ALL_TAC) THEN
           ARITH_TAC;
           ALL_TAC] THEN
         SUBGOAL_THEN (mk_conj(mk_eq(hx_add k (mk_binop `(-):num->num->num` `j:num` k),`j:num`),
                               mk_eq(hx_add xd (mk_binop `(-):num->num->num` `j:num` k),
                                     hx_suboff l `j:num`)))
           MP_TAC THENL
          [MAP_EVERY UNDISCH_TAC [mk_conj(hx_le k0 `j:num`, hx_lt `j:num` hi)] THEN
           (if d > 0 then UNDISCH_TAC (mk_neg(hx_lt `j:num` (hx_add k0 `16`))) else ALL_TAC) THEN
           ARITH_TAC;
           ALL_TAC] THEN
         DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN TRY(DISCH_THEN ACCEPT_TAC))) in
  match hx_chunks l with
    [c] -> chunk_tac c
  | [c0;c1] -> ASM_CASES_TAC (hx_lt `j:num` (hx_add k0 `16`)) THENL [chunk_tac c0; chunk_tac c1]
  | _ -> failwith "HX_INRANGE_TAC";;

let HX_OUTRANGE_TAC l =
  let w,at,offt,x,k0 = hx_terms l in
  let hi = hx_hi l in
  let is_restr p th =
    try let v,b = dest_forall(concl th) in
        let ant = lhand b in
        p v (rand ant)
    with _ -> false in
  ASM_CASES_TAC (hx_lt `j:num` k0) THENL
   [FIRST_X_ASSUM(fun th -> if is_restr (fun v c -> c = hx_lt v k0) th then MATCH_MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(fun th -> if is_restr (fun v c -> c = hx_le (hx_add k0 w) v) th then MATCH_MP_TAC th else NO_TAC) THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [mk_neg(mk_conj(hx_le k0 `j:num`, hx_lt `j:num` hi));
                           mk_neg(hx_lt `j:num` k0)] THEN
    ARITH_TAC];;

let HX_BYTES_TAC l =
  let w,at,offt,x,k0 = hx_terms l in
  let x1 = if !(hx_const_x ()) <> None then hx_add x w else hx_add `c0:num` (mk_binop `( * ):num->num->num` w `i + 1`) in
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  (if x1 = hx_add x w then ALL_TAC else
   SUBGOAL_THEN (mk_eq(x1,hx_add x w)) SUBST1_TAC THENL [ARITH_TAC; ALL_TAC]) THEN
  MP_TAC(if hx_rsp l then SPECL [`S:1600 word`; `Tm:num`; x; w; `j:num`] HX_CHUNK_STEP0
         else SPECL [`S:1600 word`; `Tm:num`; offt; x; w; `j:num`] HX_CHUNK_STEP) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC (hx_le (hx_add k0 w) `200`) THEN ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  COND_CASES_TAC THENL [HX_INRANGE_TAC l; HX_OUTRANGE_TAC l];;

let HX_COUNT_EQ = prove
 (`!n i. i < n ==> word_sub (word (n - i)) (word 1):int64 = word (n - (i + 1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= n - i` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[WORD_SUB2] THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let HX_FINAL_TAC l =
  let w,at,offt,x,k0 = hx_terms l in
  let bnd = if l.hx_count then `n < 2 EXP 64`
            else mk_binop `(<):num->num->bool` (hx_add `c0:num` (mk_binop `( * ):num->num->num` w `n:num`)) `2 EXP 64` in
  let tth = if l.hx_count then HX_TEST_COUNT
            else (match hx_w l with 1 -> HX_TEST_BOUND1 | 4 -> HX_TEST_BOUND4 | _ -> HX_TEST_BOUND32) in
  SUBGOAL_THEN bnd ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [parse_term(hx_tok l [] "c0 + @W@ * n <= len"); parse_term(hx_tok l [] "@OFFP@len <= 200")] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(MATCH_MP tth (CONJ (ASSUME `i < n`) (ASSUME bnd))) THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(fun a ->
    if can (term_match [] `read RIP s = x`) (concl a) || can (term_match [] `read events s = x`) (concl a)
    then REWRITE_RULE[th] a else a)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  W(fun (_,g) ->
    if is_forall g then HX_BYTES_TAC l
    else if is_exists g then DISCHARGE_SAFETY_PROPERTY_TAC
    else if is_cond(rand g) || is_cond(lhand g) then (COND_CASES_TAC THEN REWRITE_TAC[])
    else if l.hx_count && can (find_term (fun t -> t = `n - i`)) g then
      MATCH_MP_TAC HX_COUNT_EQ THEN FIRST_ASSUM ACCEPT_TAC
    else CONV_TAC WORD_RULE);;

let HX_BODY_TAC l exec =
  let w,at,offt,x,k0 = hx_terms l in
  let xw = hx_add x w and k0w = hx_add k0 w in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN (hx_le xw `len:num`) ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`i < n`; parse_term(hx_tok l [] "c0 + @W@ * n <= len")] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (hx_le k0w `200`) ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [hx_le xw `len:num`; parse_term(hx_tok l [] "@OFFP@len <= 200")] THEN ARITH_TAC;
    ALL_TAC] THEN
  FULL_INIT_TAC THEN VAL_INT64_TAC x THEN
  HX_LOAD_FACTS_TAC l THEN HX_ALIGN_TAC l THEN
  (if hx_w l = 32 then YMM_GHOST_TAC `s0:x86state` ["YMM0","y0"; "YMM1","y1"; "YMM2","y2"] else ALL_TAC) THEN
  X86_STEPS_TAC exec (1--hx_nsteps l) THEN
  HX_FINAL_TAC l;;

let HX_INTRO_TAC l =
  let exec = HX_EXEC l in
  let tvars = if hx_rsp l then "(rsp0:int64)" else "(a:int64) (off:num)" in
  let vars = if hx_rsp l then [`rsp0:int64`] else [`a:int64`; `off:num`] in
  let tmpl = parse_term(hx_tok l ["@TVARS@",tvars]
   "\\@TVARS@ (m:int64) (len:num) (c0:num) (n:num) (pc:num).
      APPEND (f_ev_epil @VARS@ m len c0 n pc)
       (APPEND (ENUMERATEL n (\\i. f_ev_loop @VARS@ m len c0 n pc i)) (f_ev_prol @VARS@ m len c0 n pc))
    :(uarch_event)list") in
  let hd = mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral (layout l.hx_fn + l.hx_head))
  and ex = mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral (layout l.hx_fn + l.hx_exit)) in
  CONCRETIZE_F_EVENTS_TAC tmpl THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC ([`e:(uarch_event)list`] @ vars @
    [`m:int64`; `len:num`; `c0:num`; `n:num`; `S:1600 word`; `Tm:num`; `pc:num`]) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `n:num` hd ex (HX_INV l) THEN
  REPEAT CONJ_TAC;;

let HX_INIT_TAC l =
  let w,_,_,_,_ = hx_terms l in
  FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[ARITH_RULE(mk_eq(hx_add `c0:num` (mk_binop `( * ):num->num->num` w `0`),`c0:num`)); SUB_0] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_ASSUM(fun th -> if can (term_match [] `read (memory :> wbytes a) s0 = X`) (concl th)
                          then ACCEPT_TAC(MATCH_MP SPONGE_ALL_BYTES_OF_WBYTES th) else NO_TAC);
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let HX_EXIT_TAC l =
  FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[SUB_REFL] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_forall(concl th) && free_in `bytes8` (concl th)
                            then ACCEPT_TAC(MATCH_MP SPONGE_WBYTES_OF_ALL_BYTES th) else NO_TAC);
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let HX_TAC l =
  HX_INTRO_TAC l THENL
   [UNDISCH_TAC `0 < n` THEN ARITH_TAC; HX_INIT_TAC l; HX_BODY_TAC l (HX_EXEC l); HX_EXIT_TAC l];;

let HX_PROVE l = prove(HX_STMT l, HX_TAC l);;

(* ------------------------------------------------------------------------- *)
(* The run-time test for an overlap of the data and the r bytes of the state *)
(* that a tail XORs (TG_ALIAS of inline_sponge_tail_glue.ml for a region of  *)
(* r bytes instead of the 200 bytes of the state): as they do not overlap,   *)
(* the code takes the vector path.                                           *)
(* ------------------------------------------------------------------------- *)

let HX_ALIAS = prove(`!m s r. m < 2 EXP 64 /\ s < 2 EXP 64 /\ r < 136 /\ nonoverlapping_modulo (2 EXP 64) (m,r) (s,r)
         ==> ~(s < (m + r) MOD 2 EXP 64 /\ m < (s + r) MOD 2 EXP 64)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match [] `nonoverlapping_modulo n (a,b) (c,d)`) (concl th))) THEN
  REWRITE_TAC[nonoverlapping_modulo; NOT_EXISTS_THM] THEN DISCH_TAC THEN
  ASM_CASES_TAC `m + r < 2 EXP 64` THEN ASM_CASES_TAC `s + r < 2 EXP 64` THENL
   [(* no wraps *)
    SUBGOAL_THEN `s < m + r /\ m < s + r` STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[MOD_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `s <= m` THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `m - s`]) THEN
      SUBGOAL_THEN `m + 0 = s + (m - s)` (fun th -> REWRITE_TAC[th; CONG_REFL]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPECL [`s - m`; `0`]) THEN
      SUBGOAL_THEN `m + (s - m) = s + 0` (fun th -> REWRITE_TAC[th; CONG_REFL]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_ARITH_TAC];
    (* s + r wraps *)
    SUBGOAL_THEN `m < (s + r) - 2 EXP 64` ASSUME_TAC THENL
     [SUBGOAL_THEN `(s + r) MOD 2 EXP 64 = (s + r) - 2 EXP 64` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [MATCH_MP_TAC TG_MOD1 THEN ASM_ARITH_TAC; ALL_TAC] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `m + 2 EXP 64 - s`]) THEN
    SUBGOAL_THEN `(m + 0 == s + (m + 2 EXP 64 - s)) (mod (2 EXP 64))` (fun th -> REWRITE_TAC[th]) THENL
     [SUBGOAL_THEN `s + (m + 2 EXP 64 - s) = m + 2 EXP 64` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ADD_CLAUSES; TG_CONG1; CONG_SYM] THEN ONCE_REWRITE_TAC[CONG_SYM] THEN REWRITE_TAC[TG_CONG1]; ALL_TAC] THEN
    ASM_ARITH_TAC;
    (* m + r wraps *)
    SUBGOAL_THEN `s < (m + r) - 2 EXP 64` ASSUME_TAC THENL
     [SUBGOAL_THEN `(m + r) MOD 2 EXP 64 = (m + r) - 2 EXP 64` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [MATCH_MP_TAC TG_MOD1 THEN ASM_ARITH_TAC; ALL_TAC] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s + 2 EXP 64 - m`; `0`]) THEN
    SUBGOAL_THEN `(m + (s + 2 EXP 64 - m) == s + 0) (mod (2 EXP 64))` (fun th -> REWRITE_TAC[th]) THENL
     [SUBGOAL_THEN `m + (s + 2 EXP 64 - m) = s + 2 EXP 64` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ADD_CLAUSES; TG_CONG1]; ALL_TAC] THEN
    ASM_ARITH_TAC;
    (* both wrap *)
    SUBGOAL_THEN `s < (m + r) - 2 EXP 64 /\ m < (s + r) - 2 EXP 64` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(m + r) MOD 2 EXP 64 = (m + r) - 2 EXP 64 /\ (s + r) MOD 2 EXP 64 = (s + r) - 2 EXP 64` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC TG_MOD1 THEN ASM_ARITH_TAC; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[]) THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `s <= m` THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `m - s`]) THEN
      SUBGOAL_THEN `m + 0 = s + (m - s)` (fun th -> REWRITE_TAC[th; CONG_REFL]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPECL [`s - m`; `0`]) THEN
      SUBGOAL_THEN `m + (s - m) = s + 0` (fun th -> REWRITE_TAC[th; CONG_REFL]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_ARITH_TAC]]);;

let HX_ALIAS_W = prove(`!(mp:int64) (st:int64) r. r < 136 /\ nonoverlapping_modulo (2 EXP 64) (val mp,r) (val st,r)
    ==> ~(val st < val (word_add mp (word r)) /\ val mp < val (word_add st (word r)))`,
  REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  ASSUME_TAC(REWRITE_RULE[DIMINDEX_64] (ISPEC `mp:int64` VAL_BOUND)) THEN
  ASSUME_TAC(REWRITE_RULE[DIMINDEX_64] (ISPEC `st:int64` VAL_BOUND)) THEN
  MP_TAC(SPECL [`val (mp:int64)`; `val (st:int64)`; `r:num`] HX_ALIAS) THEN
  ASM_REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `r MOD 2 EXP 64 = r` SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A driver for the code between the loops: step one instruction at a time, *)
(* resolving the conditional branches with the rewrites ths, until RIP is    *)
(* pc + stop (an offset in the image).                                       *)
(* ------------------------------------------------------------------------- *)

let hx_rip_fact asl =
  let fs = filter (fun (_,th) -> can (term_match [] `read RIP s = x`) (concl th)) asl in
  match fs with
    [_,th] -> th
  | _ -> failwith "hx_rip_fact: no unique RIP fact";;

let hx_state_num asl =
  let s = rand(lhand(concl(hx_rip_fact asl))) in
  let n = name_of s in
  int_of_string (String.sub n 1 (String.length n - 1));;

let hx_is_regfact th =
  let c = concl th in
  is_eq c && (let l = lhs c in is_comb l && is_comb(rator l) &&
    (try fst(dest_const(rator(rator l))) = "read" with _ -> false) &&
    is_const(rand(rator l)) && type_of l <> bool_ty);;

let HX_RES ths =
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read RIP s = x`) (concl th) || can (term_match [] `read events s = x`) (concl th) ||
       hx_is_regfact th
    then CONV_RULE (RAND_CONV(REWRITE_CONV (WORD_ZX_ZX_32_64_32 :: ths) THENC NUM_REDUCE_CONV)) th else th);;

let hx_drive_debug = ref false;;

let HX_DRIVE_TAC exec ths stop =
  let target = mk_comb(`word:num->int64`,mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral stop)) in
  let rec go cnt (asl,w) =
    if cnt > 100 then failwith "HX_DRIVE_TAC: more than 100 steps" else
    let rth = hx_rip_fact asl in
    if rand(concl rth) = target then ALL_TAC (asl,w) else
    if is_cond(rand(concl rth)) then
      failwith ("HX_DRIVE_TAC: unresolved branch " ^ string_of_term (rand(concl rth))) else
    let k = hx_state_num asl in
    if !hx_drive_debug then print_string ("HX_DRIVE at " ^ string_of_term (rand(concl rth)) ^ "\n") else ();
    (X86_STEPS_TAC exec [k+1] THEN HX_RES ths THEN go (cnt+1)) (asl,w) in
  go 0;;

(* ------------------------------------------------------------------------- *)
(* The blocks of the stream 2^(8 * pos) * M of an absorb at position pos     *)
(* (from the proof of shake256_absorb of the gcc12_O2_reduced_ram build):    *)
(* block k is r - p bytes of M from offset c, at position p of the state,    *)
(* with p = pos and c = 0 for k = 0 and p = 0 and c = r * k - pos after      *)
(* that, and the rest of M after the n = (pos + inlen) DIV r blocks is the   *)
(* last, partial, block.                                                     *)
(* ------------------------------------------------------------------------- *)

let HX_ABSORB_CHUNK = prove
 (`!M pos r k.
        pos <= r
        ==> 2 EXP (8 * (if k = 0 then pos else 0)) *
            (M DIV 2 EXP (8 * (if k = 0 then 0 else r * k - pos))) MOD
            2 EXP (8 * (r - (if k = 0 then pos else 0))) =
            (2 EXP (8 * pos) * M) DIV 2 EXP (8 * r * k) MOD 2 EXP (8 * r)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1] THEN
    SUBGOAL_THEN `2 EXP (8 * r) = 2 EXP (8 * pos) * 2 EXP (8 * (r - pos))`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      SIMP_TAC[MOD_MULT2; EXP_EQ_0; ARITH_EQ]];
    REWRITE_TAC[MULT_CLAUSES; EXP; SUB_0] THEN
    SUBGOAL_THEN
     `2 EXP (8 * r * k) = 2 EXP (8 * pos) * 2 EXP (8 * (r * k - pos))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `r <= r * k` MP_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `r = r * 1`] THEN
        REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
      SIMP_TAC[DIV_MULT2; EXP_EQ_0; ARITH_EQ]]]);;

let HX_ABSORB_TAIL = prove
 (`!M inlen pos r.
        0 < r /\ pos <= r /\ M < 2 EXP (8 * inlen)
        ==> let n = (pos + inlen) DIV r in
            let p = if n = 0 then pos else 0
            and c = if n = 0 then 0 else r * n - pos in
            2 EXP (8 * p) * (M DIV 2 EXP (8 * c)) MOD 2 EXP (8 * (inlen - c)) =
            (2 EXP (8 * pos) * M) DIV 2 EXP (8 * r * n) MOD 2 EXP (8 * r) /\
            p + (inlen - c) = (pos + inlen) MOD r /\
            c <= inlen`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(SPECL [`pos + inlen`; `r:num`] DIVISION) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
  ABBREV_TAC `n = (pos + inlen) DIV r` THEN
  ABBREV_TAC `t = (pos + inlen) MOD r` THEN STRIP_TAC THEN
  SUBGOAL_THEN `r <= r * n \/ n = 0` ASSUME_TAC THENL
   [ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `r = r * 1`] THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(if n = 0 then 0 else r * n - pos) <= inlen /\
                inlen - (if n = 0 then 0 else r * n - pos) +
                (if n = 0 then pos else 0) = t`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pos + inlen = n * r + t` THEN
    UNDISCH_TAC `r <= r * n \/ n = 0` THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  SUBGOAL_THEN `(2 EXP (8 * pos) * M) DIV 2 EXP (8 * r * n) =
                2 EXP (8 * (if n = 0 then pos else 0)) *
                M DIV 2 EXP (8 * (if n = 0 then 0 else r * n - pos))`
  SUBST1_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1] THEN
    SUBGOAL_THEN
     `2 EXP (8 * r * n) = 2 EXP (8 * pos) * 2 EXP (8 * (r * n - pos))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN
      UNDISCH_TAC `r <= r * n \/ n = 0` THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      SIMP_TAC[DIV_MULT2; EXP_EQ_0; ARITH_EQ]];
    ALL_TAC] THEN
  ABBREV_TAC `c = if n = 0 then 0 else r * n - pos` THEN
  ABBREV_TAC `p = if n = 0 then pos else 0` THEN
  SUBGOAL_THEN `M DIV 2 EXP (8 * c) < 2 EXP (8 * (inlen - c))` ASSUME_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[GSYM EXP_ADD; GSYM LEFT_ADD_DISTRIB] THEN
    ASM_SIMP_TAC[ARITH_RULE `c <= inlen ==> c + inlen - c = inlen`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  TRANS_TAC LTE_TRANS `2 EXP (8 * p) * 2 EXP (8 * (inlen - c))` THEN
  ASM_SIMP_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD; LE_EXP] THEN
  ASM_ARITH_TAC);;

let HX_ABSORB_LOOP_TEST = prove
 (`!pos inlen i.
        pos <= 136 /\ 136 * (i + 1) <= pos + inlen
        ==> (~(inlen - (136 * (i + 1) - pos) < 135 \/
               inlen - (136 * (i + 1) - pos) = 135) <=>
             i + 1 < (pos + inlen) DIV 136)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `i + 1 < q <=> i + 2 <= q`] THEN
  SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN ASM_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* The zeroing of the state at rsp0 + so with one MOVUPS of its last 16      *)
(* bytes and the position (at rsp0 + so + 188) and 12 MOVAPS, as            *)
(* SPONGE_ZERO of inline_sponge_region.ml (which is for so = 32), from the   *)
(* XORPS at offset z0 of the function to offset z1 (14 instructions).        *)
(* ------------------------------------------------------------------------- *)

let HX_ZERO_STMT fn so z0 z1 =
  let sa = if so = 0 then "rsp0" else Printf.sprintf "word_add rsp0 (word %d)" so in
  parse_term(subst_tokens ["@SA@",sa; "@Z0@",string_of_int (layout fn + z0); "@Z1@",string_of_int (layout fn + z1)]
 "exists f_events. forall e rsp0 pc.
   aligned 16 rsp0 /\\ aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   nonoverlapping (word pc,libmldsa_size) (@SA@,204)
   ==> ensures x86
     (\\s. bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
          read RIP s = word (pc + @Z0@) /\\
          read RSP s = rsp0 /\\ read events s = e)
     (\\s. read RIP s = word (pc + @Z1@) /\\
          read RSP s = rsp0 /\\
          read (memory :> wbytes (@SA@)) s = (word 0:1600 word) /\\
          (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 pc /\\
             memaccess_inbounds e2 [@SA@,204] [@SA@,204]))
     (MAYCHANGE [RIP] ,, MAYCHANGE [ZMM0] ,, MAYCHANGE [events] ,,
      MAYCHANGE [memory :> bytes(@SA@,204)])");;

let HX_ZERO_TAC fn so z0 z1 =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
               [(layout fn + z0, layout fn + z1)] in
  let pat = parse_term(Printf.sprintf "read (memory :> bytes128 (word_add (rsp0:int64) (word %d))) s2 = (x:int128)" (so + 188)) in
  let sa = if so = 0 then `rsp0:int64` else mk_comb(`word_add (rsp0:int64)`,mk_comb(`word:num->int64`,mk_small_numeral so)) in
  CONCRETIZE_F_EVENTS_TAC `\(rsp0:int64) (pc:num). f_ev_z rsp0 pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  YMM_GHOST_TAC `s0:x86state` ["YMM0","y0"] THEN
  FIRST_ASSUM(fun ra -> if concl ra = `aligned 16 (rsp0:int64)` then
    MAP_EVERY (fun k -> ASSUME_TAC (MATCH_MP ALIGNED_WORD_ADD (CONJ ra (SPONGE_A16 k))))
      (filter (fun k -> k > 0) (map (fun j -> so + 16 * j) (0--12))) else NO_TAC) THEN
  X86_STEPS_TAC exec (1--2) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPONGE_XMM0_ZERO]) THEN
  FIRST_ASSUM(fun th -> if can (term_match [] pat) (concl th) then
    MAP_EVERY (fun k ->
      let f = MATCH_MP SPONGE_BYTES8_OF_CHUNK128 (CONJ th (ARITH_RULE(mk_binop `(<):num->num->bool` (mk_small_numeral k) `16`))) in
      let f' = CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC DEPTH_CONV NUM_ADD_CONV) f in
      ASSUME_TAC(REWRITE_RULE[WORD_SUBWORD_0] f')) (4--11)
    else NO_TAC) THEN
  X86_STEPS_TAC exec (3--14) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPONGE_XMM0_ZERO]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SPONGE_WBYTES_OF_ALL_BYTES THEN
    REWRITE_TAC[WORD_SUBWORD_0] THEN
    MATCH_MP_TAC SPONGE_ZERO_BYTES THEN CONJ_TAC THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    TRY(GEN_REWRITE_TAC (ONCE_DEPTH_CONV) [WORD_ADD_0]) THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[WORD_ADD_0];
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let HX_ZERO_PROVE fn so z0 z1 = prove(HX_ZERO_STMT fn so z0 z1, HX_ZERO_TAC fn so z0 z1);;

(* ------------------------------------------------------------------------- *)
(* Tools for the glue between the loops: the current state, restating a     *)
(* fact about it, and a call of a loop lemma at the current state.           *)
(* ------------------------------------------------------------------------- *)

let hx_cur_state asl = rand(lhand(concl(hx_rip_fact asl)));;

(* replace the fact read c s = v (s the current state) by read c s = v',     *)
(* with v = v' proved by tac                                                 *)
let HX_RESTATE_TAC (c:term) (v':term) (tac:tactic) =
  W(fun (asl,w) ->
    let s = hx_cur_state asl in
    FIRST_X_ASSUM(fun th ->
      let cth = concl th in
      if is_eq cth && is_comb(lhs cth) && rand(lhs cth) = s && rand(rator(lhs cth)) = c then
        SUBGOAL_THEN (mk_eq(rhs cth,v')) (fun e -> ASSUME_TAC(TRANS th e)) THENL
         [(tac THEN NO_TAC) ORELSE
          (fun g -> print_goal g; failwith ("HX_RESTATE_TAC: unproved for " ^ string_of_term c));
          ALL_TAC]
      else NO_TAC));;

(* the callee's precondition on the events, and the equations of addresses  *)
(* that the normalization of its precondition leaves (by WORD_RULE)         *)
let HX_E2_ANY vars =
  REPEAT CONJ_TAC THEN
  W(fun (_,g) ->
    if can (find_term (fun t -> try type_of t = `:(uarch_event)list` with _ -> false)) g
    then FULL_EXISTS_E2_TAC (ref vars)
    else FIRST [CONV_TAC WORD_RULE THEN NO_TAC; ASM_REWRITE_TAC[] THEN NO_TAC;
                HX_ADDR_EQ_TAC THEN NO_TAC]);;

let HX_LCALL_TAC exec name ilist vars =
  W(fun (asl,w) ->
    let k = hx_state_num asl in
    REMOVE_THEN name (fun th ->
      X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
        (mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,exec,0x0,mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc,th)
        (`e:(uarch_event)list`::ilist) (k+1) THENL
       [HX_E2_ANY vars; LABEL_TAC name th] THEN
      (* the callee's events by their definition *)
      ASSUM_LIST(fun ths ->
        let defs = filter (fun th ->
          let c = concl th in
          is_eq c && is_var(lhs c) && type_of(lhs c) = `:(uarch_event)list` &&
          String.length(name_of(lhs c)) >= 2 && String.sub (name_of(lhs c)) 0 2 = "e2" &&
          (try let h = fst(strip_comb(rhs c)) in
               is_var h && String.length(name_of h) >= 15 && String.sub (name_of h) 0 15 = "f_events_callee"
           with _ -> false)) ths in
        if defs = [] then ALL_TAC else
        RULE_ASSUM_TAC(fun a -> if can (term_match [] `read events s = x`) (concl a)
                                then REWRITE_RULE defs a else a))));;

(* ------------------------------------------------------------------------- *)
(* A region that XORs r bytes of the data at m (in register rg_src) into the *)
(* state from byte off (in register rg_dst as for a loop, rg_dst = "RSP" for *)
(* the state at rsp0 + rg_bias), with the length in rg_len, from offset      *)
(* rg_entry to rg_exit of the function, through the loops rg_v32, rg_v4 and  *)
(* rg_v1. The statement is that of mldsa_keccakf1600_xor_bytes.              *)
(* ------------------------------------------------------------------------- *)

type hx_region =
 { rg_fn : string; rg_entry : int; rg_exit : int;
   rg_dst : string; rg_bias : int; rg_src : string; rg_len : string;
   rg_v32 : hx_loop; rg_v4 : hx_loop; rg_v1 : hx_loop };;

let rg_loop g = { g.rg_v1 with hx_dst = g.rg_dst; hx_bias = g.rg_bias; hx_src = g.rg_src; hx_kind = (if g.rg_dst = "RSP" then "va" else "vu") };;

let rg_tok g extra s =
  hx_tok (rg_loop g) (extra @
   ["@ALIGN@",(if g.rg_dst = "RSP" then "aligned 16 rsp0 /\\" else "")] @
   ["@ENTRY@",string_of_int (layout g.rg_fn + g.rg_entry);
    "@REXIT@",string_of_int (layout g.rg_fn + g.rg_exit);
    "@L@",g.rg_len]) s;;

(* xpre: extra facts in the precondition (registers that the code uses,   *)
(* e.g. a second pointer into the state), "" for none                      *)
let HXR_STMT_X strict g xpre = parse_term(rg_tok g ["@RLE@",(if strict then "<" else "<="); "@XPRE@",xpre]
 "exists f_events. forall e @VARS@ m r Tm (S:1600 word) pc.
   0 < r /\\ @OFFP@r @RLE@ 136 /\\ @ALIGN@
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   nonoverlapping (m,r) (@A@,200) /\\
   nonoverlapping (word pc,libmldsa_size) (@A@,200)
   ==> ensures x86
    (\\s. bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
         read RIP s = word (pc + @ENTRY@) /\\
         read @D@ s = @DV@ /\\ read @M@ s = m /\\ read @L@ s = word r /\\ @XPRE@
         read (memory :> bytes(m,r)) s = Tm /\\
         read (memory :> wbytes (@A@)) s = S /\\
         read events s = e)
    (\\s. read RIP s = word (pc + @REXIT@) /\\
         read @D@ s = @DV@ /\\ read @M@ s = m /\\ read @L@ s = word r /\\
         read (memory :> wbytes (@A@)) s = word_xor S (word(@SC@Tm)) /\\
         (exists e2. read events s = APPEND e2 e /\\ e2 = f_events @VARS@ m r pc /\\
            memaccess_inbounds e2 [m,r; @A@,200] [@A@,200]))
    (MAYCHANGE [RIP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(@A@,200)])");;

(* without extra facts *)
let HXR_STMT strict g = HXR_STMT_X strict g "";;

(* ------------------------------------------------------------------------- *)
(* Arithmetic of a length r < 136 (or <= 136), by cases.                     *)
(* ------------------------------------------------------------------------- *)

let HX_RCASES b tm =
  prove(mk_forall(`r:num`,mk_imp(mk_binop `(<):num->num->bool` `r:num` (mk_small_numeral b),tm)),
        CONV_TAC EXPAND_CASES_CONV THEN REPEAT(CHANGED_TAC(CONV_TAC(NUM_REDUCE_CONV THENC WORD_REDUCE_CONV))) THEN REWRITE_TAC[]);;

let HX_R_DIVS = HX_RCASES 137
 `4 * (r DIV 4) + r MOD 4 = r /\ 32 * (r DIV 32) + r MOD 32 = r /\
  32 * (r DIV 32) + 4 * ((r MOD 32) DIV 4) = 4 * (r DIV 4) /\
  (r MOD 32 < 4 ==> 32 * (r DIV 32) = 4 * (r DIV 4) /\ r MOD 32 = r MOD 4) /\
  4 * (r DIV 4) <= r /\ 32 * (r DIV 32) <= r /\
  (4 <= r ==> 0 < r DIV 4) /\ (32 <= r ==> 0 < r DIV 32) /\
  (~(r MOD 32 < 4) ==> 0 < (r MOD 32) DIV 4) /\
  (~(r MOD 4 = 0) ==> 0 < r MOD 4) /\
  (~(r MOD 4 = 0) ==> 4 * (r DIV 4) < r /\ r < 4 * (r DIV 4) + 4) /\
  (~(r MOD 32 = 0) /\ r MOD 32 < 4 ==> 32 * (r DIV 32) < r /\ r < 32 * (r DIV 32) + 4) /\
  (r MOD 4 = 0 ==> 4 * (r DIV 4) = r) /\ (r MOD 32 = 0 ==> 32 * (r DIV 32) = r) /\
  (r < 4 ==> r DIV 4 = 0 /\ r MOD 4 = r) /\ (r < 32 ==> r DIV 32 = 0 /\ r MOD 32 = r)`;;

let HX_R_WORDS = HX_RCASES 137
 `(word r:int64) && word 3 = word (r MOD 4) /\
  (word r:int64) && word 18446744073709551612 = word (4 * (r DIV 4)) /\
  (word r:int64) && word 18446744073709551584 = word (32 * (r DIV 32)) /\
  word_zx((word_zx (word r:int64):int32) && word 252):int64 = word (4 * (r DIV 4)) /\
  word_zx((word_zx (word r:int64):int32) && word 224):int64 = word (32 * (r DIV 32)) /\
  word_zx((word_zx (word r:int64):int32) && word 4294967292):int64 = word (4 * (r DIV 4)) /\
  word_zx((word_zx (word r:int64):int32) && word 4294967264):int64 = word (32 * (r DIV 32)) /\
  val(word r:int64) = r /\ val(word (r MOD 4):int64) = r MOD 4 /\
  val(word (r MOD 32):int64) = r MOD 32 /\
  val(word_sub (word r) (word (4 * (r DIV 4))):int64) = r MOD 4 /\
  val(word_sub (word r) (word (32 * (r DIV 32))):int64) = r MOD 32 /\
  (val((word (r MOD 256):byte) && word 28) = 0 <=> r MOD 32 < 4)`;;

(* ------------------------------------------------------------------------- *)
(* The unrolled 32-byte chunks of the XOR of len >= 32 bytes into the state  *)
(* (n = len DIV 32 <= 4 chunks, each followed by a CMP of the bound in RDX   *)
(* and a JE to the end), from j10 to j11, by the cases of n; each chunk is   *)
(* simulated as the body of a "vu" loop at a constant index.                 *)
(* ------------------------------------------------------------------------- *)

let HXU_STMT fn j10 j11 = parse_term(subst_tokens
  ["@J10@",string_of_int (layout fn + j10); "@J11@",string_of_int (layout fn + j11)]
 "exists f_events. forall e a off m len n (S:1600 word) Tm pc.
   off + len <= 136 /\\ len DIV 32 = n /\\ 0 < n /\\
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   nonoverlapping (m,len) (a,200) /\\
   nonoverlapping (word pc,libmldsa_size) (a,200)
   ==> ensures x86
    (\\s. bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
         read RIP s = word (pc + @J10@) /\\
         read RCX s = word_add a (word off) /\\ read R13 s = m /\\ read RAX s = word len /\\
         read (memory :> bytes(m,len)) s = Tm /\\
         read (memory :> wbytes a) s = S /\\
         read events s = e)
    (\\s. read RIP s = word (pc + @J11@) /\\
         read RCX s = word_add a (word off) /\\ read R13 s = m /\\ read RAX s = word len /\\
         read RDX s = word (32 * n) /\\
         read (memory :> bytes(m,len)) s = Tm /\\
         read (memory :> wbytes a) s =
           word_xor S (word(2 EXP (8 * off) * Tm MOD 2 EXP (8 * (32 * n)))) /\\
         (exists e2. read events s = APPEND e2 e /\\ e2 = f_events a off m len n pc /\\
            memaccess_inbounds e2 [m,len; a,200] [a,200]))
    (MAYCHANGE [RIP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(a,200)])");;

let HXU_CHUNK_LOOP fn = { hx_fn = fn; hx_head = 0; hx_exit = 0; hx_kind = "vu"; hx_dst = "RCX"; hx_bias = 0;
  hx_src = "R13"; hx_idx = "RCX"; hx_ctl = "RDX"; hx_count = false; hx_keep = [] };;

let hx_with_const x f =
  hx_const_x () := Some x;
  let r = (try f () with e -> (hx_const_x () := None; raise e)) in
  hx_const_x () := None; r;;

let HX_DROP_RESTRICTED_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && free_in `bytes8` (concl th) &&
       (try is_conj(lhand(snd(dest_forall(concl th)))) with _ -> false)
    then ALL_TAC else NO_TAC));;

let hxu_state_tm s x = subst [s,`s:x86state`; x,`xx:num`]
  `!j. j < 200 ==> read (memory :> bytes8 (word_add a (word j))) s =
                   word_subword (word_xor (S:1600 word) (word(2 EXP (8 * off) * Tm MOD 2 EXP (8 * xx)))) (8 * j,8)`;;

let HX_REDUCE_CONV = REPEATC(CHANGED_CONV(NUM_REDUCE_CONV THENC WORD_REDUCE_CONV));;
let HXU_RES ths =
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read RIP s = x`) (concl th) || can (term_match [] `read events s = x`) (concl th) ||
       hx_is_regfact th
    then CONV_RULE (RAND_CONV(REWRITE_CONV (WORD_ZX_ZX_32_64_32 :: ths) THENC HX_REDUCE_CONV)) th else th);;

(* one chunk at byte x = 32 c of the data: the facts, 8 steps, the bytes *)
let HXU_CHUNK_TAC exec fn c =
  let l = HXU_CHUNK_LOOP fn in
  let x = mk_small_numeral (32 * c) in
  let load = hx_with_const x (fun () -> HX_LOAD_FACTS_TAC l) in
  let bytes = hx_with_const x (fun () -> HX_BYTES_TAC l) in
  let w = `32` in
  let offt = `off:num` in
  let k0 = hx_add offt x in
  W(fun (asl,gl) ->
    let k = hx_state_num asl and s = hx_cur_state asl in
    SUBGOAL_THEN (hx_le (hx_add x w) `len:num`) ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if can (term_match [] `(k:num) <= len`) (concl th) && is_numeral(lhand(concl th))
                            then MP_TAC th else NO_TAC) THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN (hx_le (hx_add k0 w) `200`) ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [hx_le (hx_add x w) `len:num`; `off + len <= 136`] THEN ARITH_TAC; ALL_TAC] THEN
    load THEN YMM_GHOST_TAC s (map (fun r -> Printf.sprintf "YMM%d" r, Printf.sprintf "yu%d_%d" r c) [0;1;2]) THEN
    X86_STEPS_TAC exec ((k+1)--(k+8)) THEN
    W(fun (asl',gl') ->
      let s' = hx_cur_state asl' in
      let tm = hxu_state_tm s' (hx_add x w) in
      SUBGOAL_THEN tm (ASSUME_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_ADD_CONV)) THENL
       [bytes; HX_DROP_RESTRICTED_TAC]));;

let HXU_TAC fn j10 j11 =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc [(layout fn + j10, layout fn + j11)] in
  let case q =
    let qt = mk_small_numeral q in
    let wds = CONJUNCTS (MP (SPEC `len:num` HX_R_WORDS) (ASSUME `len < 137`)) in
    FIRST_X_ASSUM(fun th -> if concl th = mk_eq(`n:num`,qt) then SUBST_ALL_TAC th else NO_TAC) THEN
    RULE_ASSUM_TAC(fun th -> let c = concl th in
      if can (term_match [] `(x:num) <= y`) c || can (term_match [] `(x:num) < y`) c
      then CONV_RULE NUM_REDUCE_CONV th else th) THEN REWRITE_TAC[ARITH_EQ] THEN
    FULL_INIT_TAC THEN
    X86_STEPS_TAC exec (1--2) THEN HXU_RES (wds @ [ASSUME (mk_eq(`len DIV 32`,qt))]) THEN
    W(fun (asl,gl) -> let s = hx_cur_state asl in
      SUBGOAL_THEN (hxu_state_tm s `0`) ASSUME_TAC THENL
       [SUBGOAL_THEN `word_xor (S:1600 word) (word(2 EXP (8 * off) * Tm MOD 2 EXP (8 * 0))) = S` SUBST1_TAC THENL
         [REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; WORD_XOR_0]; ALL_TAC] THEN
        MATCH_MP_TAC SPONGE_ALL_BYTES_OF_WBYTES THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC]) THEN
    EVERY (map (fun c ->
      HXU_CHUNK_TAC exec fn c THEN
      W(fun (asl,gl) -> let k = hx_state_num asl in
        X86_STEPS_TAC exec ((k+1)--(k+2)) THEN HXU_RES (wds @ [ASSUME (mk_eq(`len DIV 32`,qt))]))) (0--(q-1))) THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) && free_in `bytes8` (concl th)
                            then ASSUME_TAC(CONV_RULE NUM_REDUCE_CONV (MATCH_MP SPONGE_WBYTES_OF_ALL_BYTES th)) else NO_TAC) THEN
    ENSURES_FINAL_STATE_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_SPINE_TAC in
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (off:num) (m:int64) (len:num) (n:num) (pc:num).
      if n = 1 then f_ev_u1 a off m len n pc else if n = 2 then f_ev_u2 a off m len n pc
      else if n = 3 then f_ev_u3 a off m len n pc else f_ev_u4 a off m len n pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `off:num`; `m:int64`; `len:num`; `n:num`; `S:1600 word`; `Tm:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `len < 137` ASSUME_TAC THENL [UNDISCH_TAC `off + len <= 136` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `32 * n <= len /\ n < 5` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`len:num`; `32`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
    UNDISCH_TAC `len < 137` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `n = 1 \/ n = 2 \/ n = 3 \/ n = 4` MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`0 < n`; `n < 5`] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   [case 1; case 2; case 3; case 4];;

let HXU_PROVE fn j10 j11 = prove(HXU_STMT fn j10 j11, HXU_TAC fn j10 j11);;

(* ------------------------------------------------------------------------- *)
(* The tail regions (the XOR of the last r < 136 - off bytes), with the      *)
(* run-time overlap test of the data and the state before the vector loops: *)
(* r < 4: v1 from 0; 4 <= r < 32: v4 from 0, then v1 if r MOD 4 > 0;       *)
(* r >= 32: v32 from 0, then v1 if 0 < r MOD 32 < 4, v4 and v1 otherwise.    *)
(* ------------------------------------------------------------------------- *)

let HXR_TEMPLATE g =
  let tv = if g.rg_dst = "RSP" then "(rsp0:int64)" else "(a:int64) (off:num)" in
  let vs = if g.rg_dst = "RSP" then "rsp0" else "a off" in
  parse_term(subst_tokens ["@TV@",tv; "@V@",vs]
   "\\@TV@ (m:int64) (r:num) (pc:num).
      if r < 4 then f_ev_1 @V@ m r pc
      else if r < 32 then (if r MOD 4 = 0 then f_ev_2 @V@ m r pc else f_ev_3 @V@ m r pc)
      else if r MOD 32 = 0 then f_ev_4 @V@ m r pc
      else if r MOD 32 < 4 then f_ev_5 @V@ m r pc
      else if r MOD 4 = 0 then f_ev_6 @V@ m r pc else f_ev_7 @V@ m r pc :(uarch_event)list");;

let hxr_vars g = if g.rg_dst = "RSP" then [`rsp0:int64`] else [`a:int64`; `off:num`];;
let hxr_a g = parse_term("(" ^ hx_a (rg_loop g) ^ "):int64");;
let hxr_off g = parse_term("(" ^ hx_off (rg_loop g) ^ "):num");;

(* the state fact: S XORed with the data up to byte c *)
let hxr_state g c =
  let tm0 = mk_binop `MOD` `Tm:num` (mk_binop `EXP` `2` (mk_binop `( * ):num->num->num` `8` c)) in
  let tm = if g.rg_dst = "RSP" then tm0 else
           mk_binop `( * ):num->num->num` (mk_binop `EXP` `2` (mk_binop `( * ):num->num->num` `8` `off:num`)) tm0 in
  mk_binop `word_xor:1600 word->1600 word->1600 word` `S:1600 word` (mk_comb(`word:num->1600 word`,tm));;

let hxr_wcomp g = parse_term("(memory :> wbytes (" ^ string_of_term (hxr_a g) ^ ")):(x86state,1600 word)component");;

let HXR_STATE_AT g c tac = HX_RESTATE_TAC (hxr_wcomp g) (hxr_state g c) tac;;

(* the truth value of a condition on r < 137 under the case hypotheses hs  *)
(* (assumptions), as atom <=> T or atom <=> F                              *)
let hx_decide_cache = ref ([]:((term list*term)*(bool*thm)) list);;
let HX_DECIDE (hs:term list) (atom:term) =
  let hyp = if hs = [] then `T` else list_mk_conj hs in
  let pos,gth =
    try assoc (hs,atom) !hx_decide_cache with Failure _ ->
    let r = try true,HX_RCASES 137 (mk_imp(hyp,atom))
            with Failure _ -> false,HX_RCASES 137 (mk_imp(hyp,mk_neg atom)) in
    hx_decide_cache := ((hs,atom),r) :: !hx_decide_cache; r in
  let th1 = MP (SPEC `r:num` gth) (ASSUME `r < 137`) in
  let th2 = MP th1 (if hs = [] then TRUTH else end_itlist CONJ (map ASSUME hs)) in
  if pos then EQT_INTRO th2 else EQF_INTRO th2;;

let HX_ATOMS = [`r < 4`; `r < 32`; `r MOD 4 = 0`; `r MOD 32 = 0`; `r MOD 32 < 4`;
                `4 <= r`; `32 <= r`; `4 <= r MOD 32`];;
let HX_DECISIONS hs = mapfilter (HX_DECIDE hs) HX_ATOMS;;

(* The overlap test of the data (m,r) and the r bytes of the state at dv    *)
(* (two SETBs, TEST, JE), whose conditions c1, c2 are as the simulation      *)
(* writes them: the fact ~(c1 /\ c2) and the rewrites for the branch.        *)

let HX_NOV_DST = prove
 (`!(m:int64) (a:int64) off r.
     nonoverlapping_modulo (2 EXP 64) (val m,r) (val a,200) /\ off + r <= 200
     ==> nonoverlapping_modulo (2 EXP 64) (val m,r) (val (word_add a (word off)),r)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN
  MATCH_MP_TAC SPONGE_NOV_OFFSET THEN EXISTS_TAC `200` THEN
  ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN ASM_REWRITE_TAC[]);;

let hxr_setb_conds g =
  let dv = if g.rg_dst = "RSP" then failwith "hxr_setb_conds" else parse_term("(" ^ hx_dv (rg_loop g) ^ "):int64") in
  let c1 = subst [dv,`dv:int64`] `val (dv:int64) < val (word_add (word r:int64) (word (1 * val (m:int64))))`
  and c2 = subst [dv,`dv:int64`] `val (m:int64) < val (word_add (word r:int64) (word (1 * val (dv:int64))))` in
  dv,c1,c2;;

let HXR_ALIAS_SETB_TAC g =
  let dv,c1,c2 = hxr_setb_conds g in
  let eq1 = ISPECL [`word r:int64`; `m:int64`] WORD_ADD_SYM and eq2 = ISPECL [`word r:int64`; dv] WORD_ADD_SYM in
  SUBGOAL_THEN (mk_neg(mk_conj(c1,c2))) ASSUME_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; WORD_VAL] THEN REWRITE_TAC[eq1; eq2] THEN
    MATCH_MP_TAC HX_ALIAS_W THEN CONJ_TAC THENL
     [UNDISCH_TAC `off + r < 136` THEN ARITH_TAC;
      MATCH_MP_TAC HX_NOV_DST THEN ASM_REWRITE_TAC[]];
    ALL_TAC];;

let hxr_setb_ths g =
  let dv,c1,c2 = hxr_setb_conds g in
  [TG_SETB; MP (SPECL [c1; c2] TG_COND_AND) (ASSUME (mk_neg(mk_conj(c1,c2))))];;

(* ------------------------------------------------------------------------- *)
(* The overlap test with two JAEs (the third absorb of mld_H): from e0, with *)
(* dst = a + off, the data m and the length r in registers, the code jumps   *)
(* to e1 if dst >= m + r, and otherwise tests m >= dst + r and jumps to e1,  *)
(* which the nonoverlap of the data with the state guarantees. The events    *)
(* depend on the first test (a function of the addresses).                   *)
(* ------------------------------------------------------------------------- *)

let HXA_STMT fn e0 e1 d m l = parse_term(subst_tokens
  ["@E0@",string_of_int (layout fn + e0); "@E1@",string_of_int (layout fn + e1);
   "@D@",d; "@M@",m; "@L@",l]
 "exists f_events. forall e a off m r pc.
   off + r < 136 /\\
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   nonoverlapping (m,r) (a,200)
   ==> ensures x86
    (\\s. bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
         read RIP s = word (pc + @E0@) /\\
         read @D@ s = word_add a (word off) /\\ read @M@ s = m /\\ read @L@ s = word r /\\
         read events s = e)
    (\\s. read RIP s = word (pc + @E1@) /\\
         read @D@ s = word_add a (word off) /\\ read @M@ s = m /\\ read @L@ s = word r /\\
         (exists e2. read events s = APPEND e2 e /\\ e2 = f_events a off m r pc /\\
            memaccess_inbounds e2 [m,r; a,200] [a,200]))
    (MAYCHANGE [RIP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [events])");;

(* mfirst: the code computes the end of the data as m + r (lea rax,[m+r]),   *)
(* not as r + m                                                              *)
let HXA_TAC fn mfirst =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc [layout_range fn] in
  let c1 = if mfirst then `val (word_add a (word off):int64) < val (word_add (m:int64) (word (1 * val (word r:int64))))`
           else `val (word_add a (word off):int64) < val (word_add (word r) (word (1 * val (m:int64))):int64)` in
  let c2 = `val (m:int64) < val (word_add (word_add a (word off)) (word (1 * val (word r:int64))):int64)` in
  CONCRETIZE_F_EVENTS_TAC
   (list_mk_abs([`a:int64`; `off:num`; `m:int64`; `r:num`; `pc:num`],
     mk_cond(c1, `f_ev_2 (a:int64) (off:num) (m:int64) (r:num) (pc:num) :(uarch_event)list`,
                 `f_ev_1 (a:int64) (off:num) (m:int64) (r:num) (pc:num) :(uarch_event)list`))) THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `off:num`; `m:int64`; `r:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN (mk_neg(mk_conj(c1,c2))) ASSUME_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; WORD_VAL] THEN
    REWRITE_TAC[ISPECL [`word r:int64`; `m:int64`] WORD_ADD_SYM] THEN
    MATCH_MP_TAC HX_ALIAS_W THEN CONJ_TAC THENL
     [UNDISCH_TAC `off + r < 136` THEN ARITH_TAC;
      MATCH_MP_TAC HX_NOV_DST THEN ASM_REWRITE_TAC[] THEN UNDISCH_TAC `off + r < 136` THEN ARITH_TAC];
    ALL_TAC] THEN
  FULL_INIT_TAC THEN
  X86_STEPS_TAC exec (1--3) THEN
  (* the JAEs jump if not CF: the conditions are y <= x for c = x < y *)
  ASM_CASES_TAC c1 THENL
   [HX_RES [GSYM NOT_LT; EQT_INTRO(ASSUME c1)] THEN
    X86_STEPS_TAC exec (4--6) THEN
    HX_RES [GSYM NOT_LT;
            EQF_INTRO(MP (MP (INST [c1,`x1:bool`; c2,`x2:bool`] (TAUT `~(x1 /\ x2) ==> x1 ==> ~x2`))
                             (ASSUME (mk_neg(mk_conj(c1,c2))))) (ASSUME c1))];
    HX_RES [GSYM NOT_LT; EQF_INTRO(ASSUME (mk_neg c1))]] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_SPINE_TAC;;

let HXA_PROVE_G fn e0 e1 d m l mfirst = prove(HXA_STMT fn e0 e1 d m l, HXA_TAC fn mfirst);;
let HXA_PROVE fn e0 e1 d m l = HXA_PROVE_G fn e0 e1 d m l false;;

(* ------------------------------------------------------------------------- *)
(* The overlap test with two SETBs for a state on the stack (the first      *)
(* absorb of mld_H): from e0 (after the test of r < 4) to its target e1 for *)
(* data that does not overlap the state at rsp0 + so, in nsteps steps. The  *)
(* conditions of the SETBs are taken from the simulation and shown to be    *)
(* those of HX_ALIAS_W by WORD_RULE.                                        *)
(* ------------------------------------------------------------------------- *)

let HXA1_STMT fn e0 e1 so m l = parse_term(subst_tokens
  ["@E0@",string_of_int (layout fn + e0); "@E1@",string_of_int (layout fn + e1);
   "@A@",(if so = 0 then "rsp0" else Printf.sprintf "word_add rsp0 (word %d)" so); "@M@",m; "@L@",l]
 "exists f_events. forall e rsp0 m r pc.
   r < 136 /\\
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   nonoverlapping (m,r) (@A@,200)
   ==> ensures x86
    (\\s. bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
         read RIP s = word (pc + @E0@) /\\
         read RSP s = rsp0 /\\ read @M@ s = m /\\ read @L@ s = word r /\\
         read events s = e)
    (\\s. read RIP s = word (pc + @E1@) /\\
         read RSP s = rsp0 /\\ read @M@ s = m /\\ read @L@ s = word r /\\
         (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rsp0 m r pc /\\
            memaccess_inbounds e2 [m,r; @A@,200] [@A@,200]))
    (MAYCHANGE [RIP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [events])");;

let HXA1_TAC fn so nsteps =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc [layout_range fn] in
  let st = if so = 0 then `rsp0:int64` else mk_comb(`word_add (rsp0:int64)`,mk_comb(`word:num->int64`,mk_small_numeral so)) in
  let c1 = subst [st,`st:int64`] `val (st:int64) < val (word_add m (word r):int64)`
  and c2 = subst [st,`st:int64`] `val (m:int64) < val (word_add st (word r):int64)` in
  let norm = REWRITE_TAC[MULT_CLAUSES; WORD_VAL; ASSUME `val(word r:int64) = r`] THEN CONV_TAC WORD_RULE in
  let lt_eq x c = (* |- x <=> c for x = val A < val B, c = val A' < val B' *)
    let a,b = dest_binop `(<):num->num->bool` x and a',b' = dest_binop `(<):num->num->bool` c in
    let tha = prove(mk_eq(rand a,rand a'),norm) and thb = prove(mk_eq(rand b,rand b'),norm) in
    MK_COMB(AP_TERM `(<):num->num->bool` (AP_TERM (rator a) tha),AP_TERM (rator b) thb) in
  CONCRETIZE_F_EVENTS_TAC `\(rsp0:int64) (m:int64) (r:num) (pc:num). f_ev_a rsp0 m r pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rsp0:int64`; `m:int64`; `r:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `val(word r:int64) = r` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN UNDISCH_TAC `r < 136` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (mk_neg(mk_conj(c1,c2))) ASSUME_TAC THENL
   [MATCH_MP_TAC HX_ALIAS_W THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN MATCH_MP_TAC TG_NOV_MONO THEN
    EXISTS_TAC `200` THEN ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `r < 136` THEN ARITH_TAC; ALL_TAC] THEN
  FULL_INIT_TAC THEN
  X86_STEPS_TAC exec (1--nsteps) THEN
  HX_RES [TG_SETB] THEN
  W(fun (asl,w) ->
    let rth = hx_rip_fact asl in
    let cnd,_ = dest_cond(rand(concl rth)) in
    let x1,x2 = match term_match [] `val ((if x1 then word 1 else word 0:byte) && (if x2 then word 1 else word 0)) = 0` cnd with
       (_,i,_) -> (rev_assoc `x1:bool` i, rev_assoc `x2:bool` i) in
    let th1 = lt_eq x1 c1 and th2 = lt_eq x2 c2 in
    (* not by rewriting: the free variables of th1 and th2 would be matched *)
    let nth = EQ_MP (SYM(AP_TERM `(~)` (MK_COMB(AP_TERM `(/\)` th1,th2))))
                    (ASSUME (mk_neg(mk_conj(c1,c2)))) in
    HX_RES [MP (SPECL [x1; x2] TG_COND_AND) nth]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_SPINE_TAC;;

let HXA1_PROVE fn e0 e1 so m l nsteps = prove(HXA1_STMT fn e0 e1 so m l, HXA1_TAC fn so nsteps);;

(* The common tactic of the tail and fill regions, with the options:       *)
(*  - ho_strict: off + r < 136 (tails) or off + r <= 136 (fills);           *)
(*  - ho_pre: run first (to assume more region lemmas);                     *)
(*  - ho_alias: for r >= 4, before the vector code (the overlap test);      *)
(*  - ho_aliasths: rewrites for the branches of the overlap test;           *)
(*  - ho_unrolled: the 32-byte chunks are unrolled (HXU), not a loop;       *)
(*  - ho_v32pre: before the call of the 32-byte loop (restate its dst).     *)
(* The 1-byte loop counts down (hx_count) in the tails, and runs to a bound *)
(* with an index from the start in the fills.                               *)

type hxr_opts =
 { ho_strict : bool; ho_pre : tactic; ho_alias : tactic; ho_aliasths : thm list;
   ho_unrolled : bool; ho_v32pre : tactic };;

let HXR_GEN_TAC ho g th32 th4 th1 =
  let aliasths = ho.ho_aliasths in
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
               [layout_range g.rg_fn] in
  let rsp = (g.rg_dst = "RSP") in
  let gvars = hxr_vars g in
  let vars = gvars @ [`m:int64`; `r:num`; `pc:num`] in
  let fn = g.rg_fn in
  let hd l = layout fn + l.hx_head and ex = layout fn + g.rg_exit in
  let wds = CONJUNCTS (MP (SPEC `r:num` HX_R_WORDS) (ASSUME `r < 137`)) in
  let dvs = CONJUNCTS (MP (SPEC `r:num` HX_R_DIVS) (ASSUME `r < 137`)) in
  let fact hs t = EQT_ELIM(HX_DECIDE (`0 < r` :: hs) t) in
  let decs hs = HX_DECISIONS (`0 < r` :: hs) in
  let drive hs extra stop = HX_DRIVE_TAC exec (wds @ decs hs @ extra) stop in
  let arith_tac hs = SIMP_TAC(dvs @ decs hs @ [ADD_CLAUSES; MULT_CLAUSES]) in
  let setreg hs reg v = HX_RESTATE_TAC (mk_const(reg,[])) v (AP_TERM_TAC THEN arith_tac hs) in
  let state_at hs c = HXR_STATE_AT g c
    (AP_TERM_TAC THEN AP_TERM_TAC THEN (if rsp then ALL_TAC else AP_TERM_TAC) THEN
     AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN arith_tac hs) in
  let state0 = HXR_STATE_AT g `0` (REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; WORD_XOR_0]) in
  let call hs name c0 n w =
    let wt = mk_small_numeral w in
    let bnd = hx_le (hx_add c0 (mk_binop `( * ):num->num->num` wt n)) `r:num` in
    ASSUME_TAC(fact hs bnd) THEN ASSUME_TAC(fact hs (hx_lt `0` n)) THEN
    (if w = 32 && rsp then ASSUME_TAC(SPEC `16` DIVIDES_0) else ALL_TAC) THEN
    HX_LCALL_TAC exec name (gvars @ [`m:int64`; `r:num`; c0; n; `S:1600 word`; `Tm:num`; `pc:num`]) vars in
  let ja hs c = MP (SPECL [c; `r:num`] TG_JA) (CONJ (fact hs (hx_lt c `r:num`)) (fact hs (hx_lt `r:num` (hx_add c `4`)))) in
  let fin hs =
    HX_RESTATE_TAC (hxr_wcomp g)
      (mk_binop `word_xor:1600 word->1600 word->1600 word` `S:1600 word`
         (mk_comb(`word:num->1600 word`, if rsp then `Tm:num` else `2 EXP (8 * off) * Tm`)))
      (AP_TERM_TAC THEN AP_TERM_TAC THEN (if rsp then ALL_TAC else AP_TERM_TAC) THEN
       MATCH_MP_TAC MOD_LT THEN
       W(fun (_,gl) -> let e = rand(rand(rand gl)) in
         SUBGOAL_THEN (mk_eq(e,`r:num`)) SUBST1_TAC THENL [arith_tac hs; FIRST_ASSUM ACCEPT_TAC])) THEN
    TRY(setreg hs g.rg_len `word r:int64`) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_SPINE_TAC in
  let v1 = g.rg_v1 and v4 = g.rg_v4 and v32 = g.rg_v32 in
  let d4 = `4 * (r DIV 4)` and d32 = `32 * (r DIV 32)` in
  let path1 =
    let hs = [`r < 4`] in
    drive hs [] (hd v1) THEN
    (if v1.hx_count then setreg hs v1.hx_ctl `word r:int64`
     else setreg hs v1.hx_ctl `word (0 + 1 * r):int64` THEN setreg hs v1.hx_idx `word 0:int64`) THEN
    state0 THEN call hs "H_V1" `0` `r:num` 1 THEN drive hs [ja hs `0`] ex THEN fin hs in
  let bytes_after hs c =
    (* from the exit of v4/v32 with the state up to c, through v1 *)
    drive hs aliasths (hd v1) THEN
    (if v1.hx_count then setreg hs v1.hx_ctl `word (r MOD 4):int64`
     else setreg hs v1.hx_ctl (mk_comb(`word:num->int64`,hx_add c `1 * r MOD 4`))) THEN
    setreg hs v1.hx_idx (mk_comb(`word:num->int64`,c)) THEN state_at hs c THEN
    call hs "H_V1" c `r MOD 4` 1 THEN drive hs [ja hs c] ex THEN fin hs in
  let words_from hs c n =
    (* v4 from byte c, n words *)
    setreg hs v4.hx_ctl (mk_comb(`word:num->int64`,hx_add c (mk_binop `( * ):num->num->num` `4` n))) THEN
    setreg hs v4.hx_idx (mk_comb(`word:num->int64`,c)) THEN (if c = `0` then state0 else state_at hs c) THEN
    call hs "H_V4" c n 4 THEN setreg hs v4.hx_ctl (mk_comb(`word:num->int64`,d4)) in
  let path23 hs =
    drive hs aliasths (hd v4) THEN words_from hs `0` `r DIV 4` THEN
    ASM_CASES_TAC `r MOD 4 = 0` THENL
     [drive (hs @ [`r MOD 4 = 0`]) aliasths ex THEN fin (hs @ [`r MOD 4 = 0`]);
      bytes_after (hs @ [`~(r MOD 4 = 0)`]) d4] in
  let v32_call hs =
    if ho.ho_unrolled then
      ASSUME_TAC(REFL `r DIV 32`) THEN ASSUME_TAC(fact hs `0 < r DIV 32`) THEN
      ASSUME_TAC(fact hs `r <= 136`) THEN
      HX_LCALL_TAC exec "H_V32" (gvars @ [`m:int64`; `r:num`; `r DIV 32`; `S:1600 word`; `Tm:num`; `pc:num`]) vars
    else
      ho.ho_v32pre THEN
      setreg hs v32.hx_ctl `word (0 + 32 * (r DIV 32)):int64` THEN setreg hs v32.hx_idx `word 0:int64` THEN
      state0 THEN call hs "H_V32" `0` `r DIV 32` 32 THEN setreg hs v32.hx_ctl (mk_comb(`word:num->int64`,d32)) in
  let path4567 hs =
    drive hs aliasths (hd v32) THEN v32_call hs THEN
    let hs4 = hs @ [`r MOD 32 = 0`]
    and hs5 = hs @ [`~(r MOD 32 = 0)`; `r MOD 32 < 4`]
    and hs6 = hs @ [`~(r MOD 32 = 0)`; `~(r MOD 32 < 4)`] in
    ASM_CASES_TAC `r MOD 32 = 0` THENL
     [drive hs4 aliasths ex THEN fin hs4;
      ASM_CASES_TAC `r MOD 32 < 4` THENL
       [bytes_after hs5 d32;
        drive hs6 aliasths (hd v4) THEN words_from hs6 d32 `(r MOD 32) DIV 4` THEN
        ASM_CASES_TAC `r MOD 4 = 0` THENL
         [drive (hs6 @ [`r MOD 4 = 0`]) aliasths ex THEN fin (hs6 @ [`r MOD 4 = 0`]);
          bytes_after (hs6 @ [`~(r MOD 4 = 0)`]) d4]]] in
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 th32) "H_V32" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 th4) "H_V4" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 th1) "H_V1" THEN
  ho.ho_pre THEN
  CONCRETIZE_F_EVENTS_TAC (HXR_TEMPLATE g) THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC ([`e:(uarch_event)list`] @ gvars @ [`m:int64`; `r:num`; `Tm:num`; `S:1600 word`; `pc:num`]) THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  SUBGOAL_THEN `Tm < 2 EXP (8 * r)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if can (term_match [`m:int64`; `r:num`; `Tm:num`] `read (memory :> bytes (m,r)) s0 = Tm`) (concl th)
                          then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND]; ALL_TAC] THEN
  let rel = if ho.ho_strict then `(<):num->num->bool` else `(<=):num->num->bool` in
  let rhyp = mk_binop rel (if rsp then `r:num` else `off + r`) `136` in
  SUBGOAL_THEN `r < 137` ASSUME_TAC THENL [UNDISCH_TAC rhyp THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (mk_binop `(<=):num->num->bool` (if rsp then `r:num` else `off + r`) `200`) ASSUME_TAC THENL
   [UNDISCH_TAC rhyp THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `r < 4` THENL
   [path1;
    ho.ho_alias THEN
    ASM_CASES_TAC `r < 32` THENL
     [path23 [`~(r < 4)`; `r < 32`];
      path4567 [`~(r < 4)`; `~(r < 32)`]]];;

(* The tails with the SETB overlap test (aliasths = [] for the default).   *)
let HXR_TAIL_TAC (aliasths:thm list) g th32 th4 th1 =
  let aliasths = if aliasths = [] then (try hxr_setb_ths g with Failure _ -> []) else aliasths in
  HXR_GEN_TAC { ho_strict = true; ho_pre = ALL_TAC; ho_alias = HXR_ALIAS_SETB_TAC g; ho_aliasths = aliasths;
                ho_unrolled = false; ho_v32pre = ALL_TAC } g th32 th4 th1;;

(* ------------------------------------------------------------------------- *)
(* The fill regions (the XOR of r <= 136 - off bytes from the start of a    *)
(* block), as the tails but without the overlap test and with the unrolled  *)
(* 32-byte chunks (HXU) instead of the 32-byte loop.                        *)
(* ------------------------------------------------------------------------- *)

let HXR_FILL_TAC g thu th4 th1 =
  HXR_GEN_TAC { ho_strict = false; ho_pre = ALL_TAC; ho_alias = ALL_TAC; ho_aliasths = [];
                ho_unrolled = true; ho_v32pre = ALL_TAC } g thu th4 th1;;

(* The tails with the overlap test as a lemma alth from e0 (HXA_PROVE for  *)
(* the JAEs, HXA1_PROVE for the SETBs of a state on the stack), called      *)
(* after the test of r < 4.                                                 *)
let HXR_TAIL_ALIAS_TAC e0 alth g th32 th4 th1 =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
               [layout_range g.rg_fn] in
  let wds = CONJUNCTS (MP (SPEC `r:num` HX_R_WORDS) (ASSUME `r < 137`)) in
  let vars = hxr_vars g @ [`m:int64`; `r:num`; `pc:num`] in
  HXR_GEN_TAC { ho_strict = true;
    ho_pre = ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 alth) "H_AL";
    ho_alias = HX_DRIVE_TAC exec (wds @ [EQF_INTRO(ASSUME `~(r < 4)`)]) (layout g.rg_fn + e0) THEN
               HX_LCALL_TAC exec "H_AL" vars vars;
    ho_aliasths = []; ho_unrolled = false; ho_v32pre = ALL_TAC } g th32 th4 th1;;

(* The fills with a 32-byte loop (not unrolled) whose dst is the register   *)
(* d16 = state + off + 16 (statement HXR_STMT_X with the facts of d16).     *)
let HXR_FILLV_TAC d16 g th32 th4 th1 =
  HXR_GEN_TAC { ho_strict = false; ho_pre = ALL_TAC; ho_alias = ALL_TAC; ho_aliasths = [];
    ho_unrolled = false;
    ho_v32pre = HX_RESTATE_TAC (mk_const(d16,[])) `word_add a (word (off + 16)):int64` HX_ADDR_EQ_TAC }
    g th32 th4 th1;;
