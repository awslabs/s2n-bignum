(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Evaluation of the ML-KEM functions of common/fips203.ml on concrete       *)
(* inputs by proof, used to check the specification against NIST test        *)
(* vectors. The K-PKE functions are evaluated via their NTT-domain forms     *)
(* KPKE_*_FIPS of common/fips203_theory.ml.                                  *)
(* ========================================================================= *)

needs "common/fips203_theory.ml";;
needs "tests/mlkem/keccak_bridge.ml";;

(* ------------------------------------------------------------------------- *)
(* Lemmas used only for evaluation.                                          *)
(* ------------------------------------------------------------------------- *)

let NUM_OF_BYTELIST_BIT = prove
 (`!l n. n < 8 * LENGTH l
         ==> (num_of_bytelist l DIV 2 EXP n) MOD 2 =
             bitval(bit (n MOD 8) (EL (n DIV 8) l))`,
  REWRITE_TAC[BIT_VAL; BITVAL_ODD] THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; MULT_CLAUSES; LT; num_of_bytelist] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `n < 8` THENL
   [ASM_SIMP_TAC[DIV_LT; MOD_LT; EL; HD] THEN
    SUBGOAL_THEN
     `!N. 256 * N = 2 EXP n * (2 * 2 EXP (7 - n) * N)`
     (fun th -> REWRITE_TAC[th])
    THENL
     [UNDISCH_TAC `n < 8` THEN SPEC_TAC(`n:num`,`n:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
      SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ; MOD_MULT_ADD]];
    FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC o
      REWRITE_RULE[NOT_LT; LE_EXISTS]) THEN
    REWRITE_TAC[ARITH_RULE `(8 + m) DIV 8 = SUC(m DIV 8)`; EL; TL] THEN
    SUBGOAL_THEN `(8 + m) MOD 8 = m MOD 8` SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[ADD_SYM] THEN
      REWRITE_TAC[ARITH_RULE `m + 8 = m + 1 * 8`; MOD_MULT_ADD];
      ALL_TAC] THEN
    REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
    SUBGOAL_THEN
     `(val(h:byte) + 256 * num_of_bytelist t) DIV 2 EXP 8 =
      num_of_bytelist t`
    SUBST1_TAC THENL
     [MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN
      REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
      SIMP_TAC[DIV_MULT_ADD; ARITH_EQ; DIV_LT; ADD_CLAUSES];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

let MLKEM_ZETA_POW_MOD = prove
 (`!n. &17 pow n rem &3329 = &17 pow (n MOD 256) rem &3329 /\
       &1175 pow n rem &3329 = &1175 pow (n MOD 256) rem &3329`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `!x:int. x pow n = (x pow 256) pow (n DIV 256) * x pow (n MOD 256)`
   (fun th -> ONCE_REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN REWRITE_TAC[INT_POW_POW; GSYM INT_POW_ADD] THEN
    AP_TERM_TAC THEN MP_TAC(SPECL [`n:num`; `256`] DIVISION) THEN ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM INT_MUL_REM] THEN
  ONCE_REWRITE_TAC[GSYM INT_POW_REM] THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_REDUCE_CONV) THEN REWRITE_TAC[INT_POW_ONE] THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_REDUCE_CONV) THEN
  REWRITE_TAC[INT_MUL_LID; INT_REM_REM]);;

let MLKEM_NTT_FORWARD_REM = prove
 (`!f k. f IN ring_carrier mlkem_rq
         ==> mlkem_ntt f k =
             isum (0..127)
              (\j. coeff (2 * j + k MOD 2) f *
                   &17 pow (((2 * bitreverse7 (k DIV 2) + 1) * j) MOD 256)
                   rem &3329) rem &3329`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLKEM_NTT_FORWARD; INT_REM_EQ] THEN
  MATCH_MP_TAC INT_CONG_ISUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM MLKEM_ZETA_POW_MOD] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!c x y n:int. (x == y) (mod n) ==> (c * x == c * y) (mod n)`) THEN
  REWRITE_TAC[INT_CONG_RREM; INTEGER_RULE `(x:int == x) (mod n)`]);;

let MLKEM_NTT_INV_COEFF_REM = prove
 (`!a k. (!i. i < 256 ==> &0 <= a i /\ a i < &3329) /\ k < 256
         ==> coeff k (mlkem_ntt_inv a) =
             (&3303 *
              isum (0..127)
               (\j. a(2 * bitreverse7 j + k MOD 2) *
                    &1175 pow (((2 * j + 1) * k DIV 2) MOD 256) rem &3329))
             rem &3329`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLKEM_NTT_INV_COEFF; INT_REM_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!c x y n:int. (x == y) (mod n) ==> (c * x == c * y) (mod n)`) THEN
  MATCH_MP_TAC INT_CONG_ISUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM MLKEM_ZETA_POW_MOD] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!c x y n:int. (x == y) (mod n) ==> (c * x == c * y) (mod n)`) THEN
  REWRITE_TAC[INT_CONG_RREM; INTEGER_RULE `(x:int == x) (mod n)`]);;

let MLKEM_ZQ_RING_SUM_BOUNDS = prove
 (`!s (f:K->int).
        &0 <= ring_sum mlkem_zq s f /\ ring_sum mlkem_zq s f < &3329`,
  REWRITE_TAC[GSYM IN_MLKEM_ZQ; RING_SUM]);;

let CARD_LT_SUC = prove
 (`!P n. CARD {j | j < SUC n /\ P j} =
         CARD {j | j < n /\ P j} + (if P n then 1 else 0)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `FINITE {j | j < n /\ P j}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j:num | j < n}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `{j | j < SUC n /\ P j} = n INSERT {j | j < n /\ P j}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM; LT] THEN
      ASM_MESON_TAC[];
      ASM_SIMP_TAC[CARD_CLAUSES; IN_ELIM_THM; LT_REFL; ADD1]];
    REWRITE_TAC[ADD_CLAUSES] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; LT] THEN ASM_MESON_TAC[]]);;

let MLKEM_SELECT_FIELD = prove
 (`!c:num->num i j.
        c j < 3329 /\ CARD {j' | j' < j /\ c j' < 3329} = i
        ==> (@j. c j < 3329 /\ CARD {j' | j' < j /\ c j' < 3329} = i) = j`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `y:num` THEN EQ_TAC THENL
   [ALL_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b. a < b /\ c a < 3329
          ==> CARD {j' | j' < a /\ c j' < 3329} <
              CARD {j' | j' < b /\ c j' < 3329}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_PSUBSET THEN CONJ_TAC THENL
     [REWRITE_TAC[PSUBSET; SUBSET; EXTENSION; IN_ELIM_THM] THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[LT_TRANS];
        DISCH_THEN(MP_TAC o SPEC `a:num`) THEN ASM_REWRITE_TAC[LT_REFL]];
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j:num | j < b}` THEN
      REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  ASM_MESON_TAC[LT_CASES; LT_REFL]);;

(* ------------------------------------------------------------------------- *)
(* An evaluator for closed terms built from the ML-KEM functions.            *)
(* MLKEM_EVAL_CONV evaluates arguments first, except for let-terms and       *)
(* conditionals, and then applies a handler for the head constant, if any.   *)
(* It does not look inside abstractions, which are only evaluated once they  *)
(* are applied (handlers for sums etc. apply them to explicit numerals).     *)
(* ------------------------------------------------------------------------- *)

(* Progress messages for long evaluations.                                   *)

let mlkem_eval_verbose = ref true;;

let mlkem_report s =
  if !mlkem_eval_verbose then
    Printf.printf "[mlkem_eval %.1f] %s\n%!" (Sys.time()) s;;

(* Frequently used terms, so that they are not parsed again on every call.   *)

let ev_T = `T` and ev_F = `F`
and ev_zq = `mlkem_zq` and ev_rq = `mlkem_rq`
and ev_q = `&3329:int` and ev_17 = `&17:int` and ev_1175 = `&1175:int`
and ev_0 = `0` and ev_2 = `2` and ev_8 = `8` and ev_256 = `256`
and ev_3329 = `3329` and ev_bytenil = `[]:byte list`
and ev_conj = `(/\)` and ev_nlt = `(<):num->num->bool`
and ev_nmul = `( * ):num->num->num` and ev_length = `LENGTH:byte list->num`
and ev_el = `EL:num->byte list->byte`
and ev_coeff = `coeff:num->((1->num)->int)->int`
and ev_rem = `(rem):int->int->int` and ev_ipow = `(pow):int->num->int`
and ev_n = `n:num` and ev_k = `k:num` and ev_j = `j:num`
and ev_ile = `int_le` and ev_ilt = `int_lt` and ev_i0 = `&0:int`
and ev_klt256 = `k < 256`
and ev_ntt = `mlkem_ntt` and ev_xof = `mlkem_xof`
and ev_xof_field = `mlkem_xof_field` and ev_bitreverse7 = `bitreverse7`
and ev_in_rq = `(IN):((1->num)->int)->(((1->num)->int)->bool)->bool`
and ev_carrier_rq = `ring_carrier mlkem_rq`;;

let EV_F_AND = TAUT `F /\ p <=> F` and EV_T_AND = TAUT `T /\ p <=> p`;;

let mlkem_handlers = Hashtbl.create 100;;

let add_mlkem_handler name (conv:conv) =
  Hashtbl.replace mlkem_handlers name conv;;

let is_byte_literal tm =
  match tm with
    Comb(Const("word",_),n) -> is_numeral n
  | _ -> false;;

let is_mlkem_literal tm =
  is_numeral tm || is_intconst tm || tm = ev_T || tm = ev_F ||
  is_byte_literal tm ||
  (is_list tm && forall is_byte_literal (dest_list tm));;

(* Tables of values of functions g at numerals 0, 1, ..., registered by the  *)
(* handlers that need them repeatedly (the inverse NTT).                     *)

let beta_tables = ref ([]:(term * thm array) list);;

let rec find_beta_table g l =
  match l with
    [] -> raise Not_found
  | (g',t)::r -> if g == g' || g = g' then t else find_beta_table g r;;

(* Conversions tried before evaluating arguments; they must fail fast.       *)

let mlkem_pre_convs = ref ([]:conv list);;

let rec MLKEM_EVAL_CONV tm =
  if is_mlkem_literal tm then REFL tm else
  try tryfind (fun c -> c tm) (!mlkem_pre_convs) with Failure _ ->
  if is_let tm then
    (RAND_CONV MLKEM_EVAL_CONV THENC let_CONV THENC MLKEM_EVAL_CONV) tm
  else if is_cond tm then
    (RATOR_CONV(RATOR_CONV(RAND_CONV MLKEM_EVAL_CONV)) THENC
     GEN_REWRITE_CONV I [COND_CLAUSES] THENC MLKEM_EVAL_CONV) tm
  else match tm with
    Comb(f,x) ->
      if is_abs f then
        let th1 = AP_TERM f (MLKEM_EVAL_CONV x) in
        TRANS th1 (BETA_EVAL_CONV (rand(concl th1)))
      else
        let th1 = COMB_CONV MLKEM_EVAL_CONV tm in
        let tm1 = rand(concl th1) in
        if is_abs(rator tm1) || is_var(rator tm1)
        then TRANS th1 (BETA_EVAL_CONV tm1)
        else TRANS th1 (TRY_CONV MLKEM_HANDLE_CONV tm1)
  | _ -> REFL tm

and BETA_EVAL_CONV tm =
  let fallback tm =
    if is_abs(rator tm) then (BETA_CONV THENC MLKEM_EVAL_CONV) tm
    else REFL tm in
  match tm with
    Comb(g,n) when !beta_tables <> [] && is_numeral n ->
      (try let t = find_beta_table g (!beta_tables) in
           let i = Num.int_of_num(dest_numeral n) in
           if i < Array.length t then t.(i) else failwith "BETA_EVAL_CONV"
       with Not_found | Failure _ -> fallback tm)
  | _ -> fallback tm

and MLKEM_HANDLE_CONV tm =
  let h,args = strip_comb tm in
  match h with
    Const(name,_) ->
      (try Hashtbl.find mlkem_handlers name
       with Not_found -> failwith "MLKEM_HANDLE_CONV") tm
  | _ -> failwith "MLKEM_HANDLE_CONV";;

(* Arithmetic on literals. *)

let ARITH_LITERAL_CONV =
  let pth = prove(`!n. num_of_int(&n) = n`, REWRITE_TAC[NUM_OF_INT_OF_NUM]) in
  fun tm ->
    let _,args = strip_comb tm in
    if not(forall is_mlkem_literal args) then failwith "ARITH_LITERAL_CONV"
    else (NUM_RED_CONV ORELSEC INT_RED_CONV ORELSEC REWR_CONV pth) tm;;

do_list (fun s -> add_mlkem_handler s ARITH_LITERAL_CONV)
 ["+"; "-"; "*"; "DIV"; "MOD"; "EXP"; "SUC"; "<"; "<="; ">"; ">=";
  "EVEN"; "ODD"; "int_add"; "int_sub"; "int_mul"; "int_neg"; "int_pow";
  "div"; "rem"; "int_lt"; "int_le"; "int_gt"; "int_ge"; "num_of_int";
  "int_abs"];;

(* Equality of literals, including byte lists. *)

let LITERAL_EQ_CONV =
  let pth_cons = prove
   (`!h t h' t'. (CONS (h:byte) t = CONS h' t') <=> h = h' /\ t = t'`,
    REWRITE_TAC[CONS_11])
  and pth_nil1 = prove
   (`!h t. (CONS (h:byte) t = []) <=> F`, REWRITE_TAC[NOT_CONS_NIL])
  and pth_nil2 = prove
   (`!h t. ([] = CONS (h:byte) t) <=> F`, REWRITE_TAC[NOT_CONS_NIL]) in
  let rec conv tm =
    let l,r = dest_eq tm in
    if l = r then EQT_INTRO(REFL l)
    else if is_list l then
      if l = ev_bytenil || r = ev_bytenil then
        (REWR_CONV pth_nil1 ORELSEC REWR_CONV pth_nil2) tm
      else
        let th1 = REWR_CONV pth_cons tm in
        let a,b = dest_conj(rand(concl th1)) in
        let tha = conv a in
        if rand(concl tha) = ev_F then
          TRANS th1 (CONV_RULE(RAND_CONV(REWR_CONV EV_F_AND))
                       (AP_THM (AP_TERM ev_conj tha) b))
        else
          TRANS th1 (CONV_RULE(RAND_CONV(REWR_CONV EV_T_AND))
                       (MK_COMB(AP_TERM ev_conj tha,conv b)))
    else (NUM_RED_CONV ORELSEC INT_RED_CONV ORELSEC WORD_RED_CONV) tm in
  fun tm ->
    let l,r = dest_eq tm in
    if is_mlkem_literal l && is_mlkem_literal r then conv tm
    else failwith "LITERAL_EQ_CONV";;

add_mlkem_handler "=" LITERAL_EQ_CONV;;

(* Propositional connectives and bitval on T and F. *)

let BOOL_LITERAL_CONV tm =
  let _,args = strip_comb tm in
  if forall (fun t -> t = ev_T || t = ev_F) args
  then REWRITE_CONV[BITVAL_CLAUSES] tm
  else failwith "BOOL_LITERAL_CONV";;

do_list (fun s -> add_mlkem_handler s BOOL_LITERAL_CONV)
 ["~"; "/\\"; "\\/"; "==>"; "bitval"];;

(* Bits of bytes, and list operations on explicit lists. *)

add_mlkem_handler "bit"
 (fun tm -> if forall is_mlkem_literal (snd(strip_comb tm))
            then WORD_RED_CONV tm else failwith "bit");;

add_mlkem_handler "APPEND"
 (fun tm -> if forall is_mlkem_literal (snd(strip_comb tm))
            then REWRITE_CONV[APPEND] tm else failwith "APPEND");;

add_mlkem_handler "LENGTH"
 (fun tm -> if is_mlkem_literal(rand tm) then LENGTH_CONV tm
            else failwith "LENGTH");;

add_mlkem_handler "EL"
 (fun tm -> if forall is_mlkem_literal (snd(strip_comb tm)) then EL_CONV tm
            else failwith "EL");;

add_mlkem_handler "FST" (REWR_CONV FST);;
add_mlkem_handler "SND" (REWR_CONV SND);;

(* ------------------------------------------------------------------------- *)
(* Hashing (cached, since the same values are needed several times).         *)
(* ------------------------------------------------------------------------- *)

let CACHED_CONV (conv:conv) =
  let cache = Hashtbl.create 20 in
  fun tm -> try Hashtbl.find cache tm with Not_found ->
            let th = conv tm in Hashtbl.add cache tm th; th;;

let REPORTING_CONV name (conv:conv) tm =
  mlkem_report name; let th = conv tm in mlkem_report (name^" done"); th;;

let SHA3_512_EVAL_CONV =
  CACHED_CONV (REPORTING_CONV "SHA3-512" SHA3_512_CONV);;

let SHA3_256_EVAL_CONV =
  CACHED_CONV (REPORTING_CONV "SHA3-256" SHA3_256_CONV);;

let SHAKE_OUTPUT_EVAL_CONV =
  CACHED_CONV (REPORTING_CONV "SHAKE"
   (RATOR_CONV(RAND_CONV(REWR_CONV shake128 ORELSEC REWR_CONV shake256))
    THENC KECCAK_OUTPUT_CONV));;

add_mlkem_handler "sha3_512"
 (fun tm -> if is_mlkem_literal(rand tm) then SHA3_512_EVAL_CONV tm
            else failwith "sha3_512");;

add_mlkem_handler "sha3_256"
 (fun tm -> if is_mlkem_literal(rand tm) then SHA3_256_EVAL_CONV tm
            else failwith "sha3_256");;

add_mlkem_handler "list_of_seq"
 (fun tm ->
    match tm with
      Comb(Comb(Const("list_of_seq",_),
                Comb(Const(("shake128"|"shake256"),_),m)),n)
        when is_mlkem_literal m && is_numeral n -> SHAKE_OUTPUT_EVAL_CONV tm
    | _ -> failwith "list_of_seq");;

let LITERAL_ARGS_CONV name (conv:conv) =
  let cconv = CACHED_CONV conv in
  fun tm -> if forall is_mlkem_literal (snd(strip_comb tm)) then cconv tm
            else failwith name;;

do_list (fun (s,th) ->
  add_mlkem_handler s
   (LITERAL_ARGS_CONV s (REWR_CONV th THENC MLKEM_EVAL_CONV)))
 ["mlkem_g",mlkem_g; "mlkem_h",mlkem_h; "mlkem_j",mlkem_j;
  "mlkem_prf",mlkem_prf];;

add_mlkem_handler "mlkem_slice"
 (LITERAL_ARGS_CONV "mlkem_slice"
   (REWR_CONV mlkem_slice THENC LIST_OF_SEQ_CONV THENC MLKEM_EVAL_CONV));;

(* ------------------------------------------------------------------------- *)
(* SampleNTT: evaluate the 12-bit fields of the XOF stream, count the ones   *)
(* < q, and use MLKEM_SELECT_FIELD to identify the i-th one.                 *)
(* ------------------------------------------------------------------------- *)

let SAMPLE_NTT_TABLE =
  let cache = Hashtbl.create 10 in
  let xof_field_conv =
    REWR_CONV mlkem_xof_field THENC
    RATOR_CONV(RAND_CONV(REWR_CONV NUMSEG_LT THENC
                         RATOR_CONV(LAND_CONV NUM_EQ_CONV) THENC
                         REWRITE_CONV[] THENC NUM_REDUCE_CONV)) THENC
    EXPAND_NSUM_CONV THENC NUM_REDUCE_CONV in
  let card0 = prove
   (`!P. CARD {j | j < 0 /\ P j} = 0`,
    REWRITE_TAC[LT; EMPTY_GSPEC; CARD_CLAUSES]) in
  fun b ->
    try Hashtbl.find cache b with Not_found ->
    mlkem_report "SampleNTT";
    let xth = (REWR_CONV mlkem_xof THENC REWR_CONV shake128 THENC KECCAK_CONV)
              (mk_comb(`mlkem_xof`,b)) in
    let xtm = lhs(concl xth) in
    let bytes = Hashtbl.create 600 in
    let byte_conv tm =
      match tm with
        Comb(s,n) when s = xtm && is_numeral n ->
          let i = Num.int_of_num(dest_numeral n) in
          (try Hashtbl.find bytes i with Not_found ->
           let th = CONV_RULE(RAND_CONV
                      (BETA_CONV THENC NUM_REDUCE_CONV THENC
                       ONCE_DEPTH_CONV KECCAK_SQUEEZE_CONV THENC
                       WORD_REDUCE_CONV)) (AP_THM xth n) in
           Hashtbl.add bytes i th; th)
      | _ -> failwith "byte_conv" in
    let ctm = mk_comb(`mlkem_xof_field`,xtm) in
    let field j =
      (xof_field_conv THENC ONCE_DEPTH_CONV byte_conv THENC
       WORD_REDUCE_CONV THENC REWRITE_CONV[BITVAL_CLAUSES] THENC
       NUM_REDUCE_CONV) (mk_comb(ctm,mk_small_numeral j)) in
    let ptm = mk_abs(`j:num`,mk_binop `(<):num->num->bool`
                       (mk_comb(ctm,`j:num`)) `3329`) in
    let suc_th = BETA_RULE(ISPEC ptm CARD_LT_SUC)
    and sel_th = ISPEC ctm MLKEM_SELECT_FIELD
    and def_th = CONV_RULE(RAND_CONV let_CONV) (SPEC b mlkem_sample_ntt) in
    let result = Array.make 256 TRUTH in
    let rec loop j cth found =
      if found = 256 then () else
      let fth = field j in
      let good = dest_numeral(rand(concl fth)) </ num 3329 in
      (if good then
         let i = rand(concl cth) in
         let gth = EQT_ELIM((LAND_CONV(REWR_CONV fth) THENC NUM_LT_CONV)
                     (mk_binop ev_nlt (lhs(concl fth)) ev_3329)) in
         let sth = MP (SPECL [i; mk_small_numeral j] sel_th) (CONJ gth cth) in
         let th = CONV_RULE(RAND_CONV(BETA_CONV THENC
                    ONCE_DEPTH_CONV(REWR_CONV sth) THENC
                    ONCE_DEPTH_CONV(REWR_CONV fth))) (AP_THM def_th i) in
         result.(Num.int_of_num(dest_numeral i)) <- th);
      let th1 = SPEC (mk_small_numeral j) suc_th in
      let th2 = CONV_RULE(RAND_CONV(PURE_ONCE_REWRITE_CONV[cth] THENC
                  PURE_ONCE_REWRITE_CONV[fth] THENC NUM_REDUCE_CONV)) th1 in
      let cth' = CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV NUM_SUC_CONV)) th2 in
      loop (j + 1) cth' (if good then found + 1 else found) in
    loop 0 (BETA_RULE(SPEC ptm card0)) 0;
    mlkem_report "SampleNTT done";
    Hashtbl.add cache b result; result;;

add_mlkem_handler "mlkem_sample_ntt"
 (fun tm ->
    match tm with
      Comb(Comb(Const("mlkem_sample_ntt",_),b),n)
        when is_mlkem_literal b && is_numeral n &&
             dest_numeral n </ num 256 ->
        (SAMPLE_NTT_TABLE b).(Num.int_of_num(dest_numeral n))
    | _ -> failwith "mlkem_sample_ntt");;

(* ------------------------------------------------------------------------- *)
(* Sums, Z_q arithmetic, bitreverse7 and the powers of zeta mod q.           *)
(* ------------------------------------------------------------------------- *)

let NUMSEG_LT_CONV =
  REWR_CONV NUMSEG_LT THENC RATOR_CONV(LAND_CONV NUM_EQ_CONV) THENC
  GEN_REWRITE_CONV I [COND_CLAUSES] THENC RAND_CONV NUM_SUB_CONV;;

add_mlkem_handler "nsum"
 (fun tm ->
    match tm with
      Comb(Comb(Const("nsum",_),s),f) ->
        if is_numeral(rand s) && is_comb(rator s) &&
           fst(dest_const(rator(rator s))) = ".."
        then (EXPAND_NSUM_CONV THENC MLKEM_EVAL_CONV) tm
        else (RATOR_CONV(RAND_CONV NUMSEG_LT_CONV) THENC EXPAND_NSUM_CONV THENC
              MLKEM_EVAL_CONV) tm
    | _ -> failwith "nsum");;

add_mlkem_handler "isum"
 (fun tm -> (EXPAND_ISUM_CONV THENC MLKEM_EVAL_CONV) tm);;

let MLKEM_ZQ_CLAUSES = prove
 (`ring_0 mlkem_zq = &0 /\ ring_1 mlkem_zq = &1 /\
   (!x. ring_neg mlkem_zq x = --x rem &3329) /\
   (!x y. ring_add mlkem_zq x y = (x + y) rem &3329) /\
   (!x y. ring_sub mlkem_zq x y = (x - y) rem &3329) /\
   (!x y. ring_mul mlkem_zq x y = (x * y) rem &3329) /\
   (!x n. ring_pow mlkem_zq x n = x pow n rem &3329) /\
   (!x. x IN ring_carrier mlkem_zq <=> &0 <= x /\ x < &3329)`,
  REWRITE_TAC[MLKEM_ZQ; IN_ELIM_THM]);;

let ZQ_CONV = GEN_REWRITE_CONV I [MLKEM_ZQ_CLAUSES] THENC MLKEM_EVAL_CONV;;

do_list (fun (s,n) ->
  add_mlkem_handler s
   (fun tm -> let _,args = strip_comb tm in
              if length args = n && hd args = ev_zq then ZQ_CONV tm
              else failwith s))
 ["ring_0",1; "ring_1",1; "ring_neg",2; "ring_add",3; "ring_sub",3;
  "ring_mul",3; "ring_pow",3];;

add_mlkem_handler "IN"
 (fun tm -> match tm with
              Comb(Comb(Const("IN",_),x),Comb(Const("ring_carrier",_),r))
                when r = ev_zq && is_mlkem_literal x -> ZQ_CONV tm
            | _ -> failwith "IN");;

let RING_SUM_NUMSEG_CONV =
  let pth0,pth1 = CONJ_PAIR RING_SUM_CLAUSES_NUMSEG in
  fun tm ->
    match tm with
      Comb(Comb(Comb(Const("ring_sum",_),r),
                Comb(Comb(Const("..",_),m),n)),f) ->
        if n = ev_0 then (REWR_CONV pth0 THENC MLKEM_EVAL_CONV) tm else
        (RATOR_CONV(RAND_CONV(RAND_CONV num_CONV)) THENC REWR_CONV pth1 THENC
         MLKEM_EVAL_CONV) tm
    | _ -> failwith "RING_SUM_NUMSEG_CONV";;

add_mlkem_handler "ring_sum"
 (fun tm ->
    match tm with
      Comb(Comb(Comb(Const("ring_sum",_),r),s),f) when r = ev_zq ->
        if is_comb s && is_comb(rator s) && is_const(rator(rator s)) &&
           fst(dest_const(rator(rator s))) = ".."
        then RING_SUM_NUMSEG_CONV tm
        else (RATOR_CONV(RAND_CONV NUMSEG_LT_CONV) THENC
              RING_SUM_NUMSEG_CONV) tm
    | _ -> failwith "ring_sum");;

let BITREVERSE7_CONV =
  let tab = Array.init 128 (fun i ->
    (REWR_CONV bitreverse7 THENC WORD_REDUCE_CONV)
    (mk_comb(`bitreverse7`,mk_small_numeral i))) in
  fun tm ->
    match tm with
      Comb(Const("bitreverse7",_),n) when is_numeral n &&
                                         dest_numeral n </ num 128 ->
        tab.(Num.int_of_num(dest_numeral n))
    | _ -> failwith "BITREVERSE7_CONV";;

add_mlkem_handler "bitreverse7" BITREVERSE7_CONV;;

(* (&17 pow e) rem &3329 and (&1175 pow e) rem &3329, via e MOD 256.         *)

let ZETA_REM_CONV =
  let pth17,pth1175 = CONJ_PAIR(SPEC_ALL MLKEM_ZETA_POW_MOD) in
  let tab17 = Array.make 256 TRUTH and tab1175 = Array.make 256 TRUTH in
  let get tab x i =
    if concl tab.(i) <> ev_T then tab.(i) else
    let th = INT_REDUCE_CONV
      (mk_binop ev_rem (mk_binop ev_ipow x (mk_small_numeral i)) ev_q) in
    tab.(i) <- th; th in
  fun tm ->
    match tm with
      Comb(Comb(Const("rem",_),Comb(Comb(Const("int_pow",_),x),e)),q)
        when q = ev_q && (x = ev_17 || x = ev_1175) ->
        let th1 = LAND_CONV(RAND_CONV MLKEM_EVAL_CONV) tm in
        let e' = rand(lhand(rand(concl th1))) in
        let tab,pth = if x = ev_17 then tab17,pth17 else tab1175,pth1175 in
        let n = Num.int_of_num(dest_numeral e') in
        let th2 =
          if n < 256 then get tab x n else
          let th3 = INST [e',ev_n] pth in
          let th4 = CONV_RULE(RAND_CONV(LAND_CONV(RAND_CONV NUM_REDUCE_CONV)))
                      th3 in
          TRANS th4 (get tab x (n mod 256)) in
        TRANS th1 th2
    | _ -> failwith "ZETA_REM_CONV";;

(* ------------------------------------------------------------------------- *)
(* Byte strings and their numeric values, encoding, decoding, compression.   *)
(* ------------------------------------------------------------------------- *)

let NUM_OF_BYTELIST_EVAL_CONV = CACHED_CONV NUM_OF_BYTELIST_CONV;;

add_mlkem_handler "num_of_bytelist"
 (fun tm -> if is_mlkem_literal(rand tm) then NUM_OF_BYTELIST_EVAL_CONV tm
            else failwith "num_of_bytelist");;

let BYTELIST_OF_NUM_CONV =
  let pth0,pth1 = CONJ_PAIR bytelist_of_num in
  let rec conv tm =
    match tm with
      Comb(Comb(Const("bytelist_of_num",_),k),n) ->
        if k = ev_0 then REWR_CONV pth0 tm else
        (RATOR_CONV(RAND_CONV num_CONV) THENC REWR_CONV pth1 THENC
         RATOR_CONV(RAND_CONV(RAND_CONV NUM_REDUCE_CONV)) THENC
         RAND_CONV(RAND_CONV NUM_REDUCE_CONV THENC conv)) tm
    | _ -> failwith "BYTELIST_OF_NUM_CONV" in
  conv;;

add_mlkem_handler "bytelist_of_num"
 (fun tm -> if forall is_numeral (snd(strip_comb tm))
            then BYTELIST_OF_NUM_CONV tm else failwith "bytelist_of_num");;

let SPEC_HANDLER name th =
  let n = length(snd(strip_comb(lhs(snd(strip_forall(concl th)))))) in
  add_mlkem_handler name
   (fun tm -> let _,args = strip_comb tm in
              if length args = n then
                (REWR_CONV th THENC MLKEM_EVAL_CONV) tm
              else failwith name);;

SPEC_HANDLER "mlkem_decode" mlkem_decode;;
add_mlkem_handler "mlkem_encode"
 (fun tm -> match strip_comb tm with
              _,[d;n;f] when is_numeral d && is_numeral n ->
                mlkem_report("encode "^string_of_term d^" "^string_of_term n);
                let th = (REWR_CONV mlkem_encode THENC MLKEM_EVAL_CONV) tm in
                mlkem_report "encode done"; th
            | _ -> failwith "mlkem_encode");;
SPEC_HANDLER "mlkem_compress" mlkem_compress;;
SPEC_HANDLER "mlkem_decompress" mlkem_decompress;;
add_mlkem_handler "mlkem_round" (REWR_CONV mlkem_round THENC MLKEM_EVAL_CONV);;
SPEC_HANDLER "fips203_multiply_ntts" fips203_multiply_ntts;;

(* ------------------------------------------------------------------------- *)
(* R_q elements: membership in the carrier, coefficients and the NTT.        *)
(* ------------------------------------------------------------------------- *)

let NTT_VALID f =
  let tm = mk_forall(ev_k,
    mk_imp(ev_klt256,
      mk_conj(mk_binop ev_ile ev_i0 (mk_comb(f,ev_k)),
              mk_binop ev_ilt (mk_comb(f,ev_k)) ev_q))) in
  prove(tm, GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[] THEN
            REWRITE_TAC[MLKEM_ZQ_RING_SUM_BOUNDS; MLKEM_DECODE_12_BOUNDS] THEN
            REWRITE_TAC[GSYM IN_MLKEM_ZQ] THEN
            REPEAT(FIRST[MATCH_ACCEPT_TAC RING_SUM;
                         MATCH_MP_TAC RING_ADD THEN CONJ_TAC;
                         MATCH_MP_TAC RING_SUB THEN CONJ_TAC;
                         MATCH_MP_TAC RING_MUL THEN CONJ_TAC]));;

let rec RQ_CARRIER tm =
  match strip_comb tm with
    Const("mlkem_poly",_),[f] -> ISPEC f MLKEM_POLY_IN_RQ
  | Const("mlkem_cbd",_),[eta;l] -> ISPECL [eta;l] MLKEM_CBD_IN_RQ
  | Const("mlkem_dot",_),[k;u;v] -> ISPECL [k;u;v] MLKEM_DOT_IN_RQ
  | Const("ring_add",_),[r;p;q] when r = ev_rq ->
      MATCH_MP (ISPEC r RING_ADD) (CONJ (RQ_CARRIER p) (RQ_CARRIER q))
  | Const("ring_sub",_),[r;p;q] when r = ev_rq ->
      MATCH_MP (ISPEC r RING_SUB) (CONJ (RQ_CARRIER p) (RQ_CARRIER q))
  | Const("mlkem_ntt_inv",_),[f] ->
      CONJUNCT1(MATCH_MP MLKEM_NTT_INV (NTT_VALID f))
  | _ -> failwith "RQ_CARRIER";;

let rq_tables = ref ([]:(term * thm array) list);;

let rq_table key (mk:unit->thm array) =
  try assoc key (!rq_tables) with Failure _ ->
  let a = mk() in rq_tables := (key,a)::(!rq_tables); a;;

(* Evaluate with a large term t replaced by a variable v, under the          *)
(* hypothesis v = t, and then remove the hypothesis again.                   *)

let abbrev_hyp t =
  let v = genvar(type_of t) in
  v,ASSUME(mk_eq(v,t));;

let unabbrev_hyp t v th = PROVE_HYP (REFL t) (INST [t,v] th);;

(* Bits of byte strings, via NUM_OF_BYTELIST_BIT and a table of EL values.   *)

let EL_TABLE =
  let cache = ref [] in
  fun l ->
    try assoc l (!cache) with Failure _ ->
    let n = length(dest_list l) in
    let t = Array.init n
              (fun i -> EL_CONV(mk_binop ev_el (mk_small_numeral i) l)) in
    cache := (l,t)::(!cache); t;;

let LENGTH_CACHED_CONV = CACHED_CONV LENGTH_CONV;;

let BYTELIST_BIT_CONV tm =
  match tm with
    Comb(Comb(Const("MOD",_),
      Comb(Comb(Const("DIV",_),Comb(Const("num_of_bytelist",_),l)),
           Comb(Comb(Const("EXP",_),two),n))),two') when
      two = ev_2 && two' = ev_2 && is_mlkem_literal l ->
      let th1 = LAND_CONV(RAND_CONV(RAND_CONV MLKEM_EVAL_CONV)) tm in
      let n' = rand(rand(lhand(rand(concl th1)))) in
      let lth = EQT_ELIM((RAND_CONV(RAND_CONV LENGTH_CACHED_CONV THENC
                                    NUM_MULT_CONV)
                          THENC NUM_LT_CONV)
                 (mk_binop ev_nlt n'
                    (mk_binop ev_nmul ev_8 (mk_comb(ev_length,l))))) in
      let th2 = MP (ISPECL [l;n'] NUM_OF_BYTELIST_BIT) lth in
      let th3 = CONV_RULE(RAND_CONV(RAND_CONV(LAND_CONV NUM_RED_CONV THENC
                  RAND_CONV(LAND_CONV NUM_RED_CONV)))) th2 in
      let i = Num.int_of_num
                (dest_numeral(lhand(rand(rand(rand(concl th3)))))) in
      let th4 = CONV_RULE(RAND_CONV(RAND_CONV(RAND_CONV
                  (REWR_CONV (EL_TABLE l).(i))))) th3 in
      TRANS th1 (CONV_RULE(RAND_CONV(RAND_CONV WORD_RED_CONV THENC
                                     REWRITE_CONV[BITVAL_CLAUSES])) th4)
  | _ -> failwith "BYTELIST_BIT_CONV";;

(* coeff k p for k < 256, computing all 256 at once *)

let COEFF_TABLE p =
  rq_table p
   (fun () ->
    (if not(is_var p) then
       mlkem_report("coefficients of "^fst(dest_const(fst(strip_comb p)))));
    match strip_comb p with
      Const("mlkem_poly",_),[f] ->
        let th = ISPEC f COEFF_MLKEM_POLY in
        Array.init 256 (fun k ->
          CONV_RULE(RAND_CONV MLKEM_EVAL_CONV) (SPEC (mk_small_numeral k) th))
    | Const("mlkem_cbd",_),[eta;l] ->
        let th0 = CONV_RULE(RAND_CONV let_CONV) (ISPECL [eta;l] mlkem_cbd) in
        let f = rand(rand(concl th0)) in
        let th = ISPEC f COEFF_MLKEM_POLY in
        Array.init 256 (fun k ->
          let k = mk_small_numeral k in
          let th1 = AP_TERM (mk_comb(ev_coeff,k)) th0 in
          TRANS th1 (CONV_RULE(RAND_CONV MLKEM_EVAL_CONV) (SPEC k th)))
    | Const(("ring_add"|"ring_sub") as op,_),[r;p1;p2] when r = ev_rq ->
        let th = MATCH_MP (if op = "ring_add" then MLKEM_RQ_COEFF_ADD
                           else MLKEM_RQ_COEFF_SUB)
                          (CONJ (RQ_CARRIER p1) (RQ_CARRIER p2)) in
        Array.init 256 (fun k ->
          CONV_RULE(RAND_CONV MLKEM_EVAL_CONV) (SPEC (mk_small_numeral k) th))
    | Const("mlkem_ntt_inv",_),[f] ->
        let vth = NTT_VALID f in
        let ftab = Array.init 256
                     (fun i ->
                        MLKEM_EVAL_CONV(mk_comb(f,mk_small_numeral i))) in
        let fv,hth = abbrev_hyp f in
        let ftab' = Array.map
          (fun th -> TRANS (AP_THM hth (rand(lhs(concl th)))) th) ftab in
        beta_tables := (fv,ftab')::(!beta_tables);
        let vth' = SUBS [SYM hth] vth in
        let th = SPEC fv MLKEM_NTT_INV_COEFF_REM in
        let res = Array.init 256 (fun k ->
          let k = mk_small_numeral k in
          let kth = EQT_ELIM(NUM_LT_CONV(mk_binop ev_nlt k ev_256)) in
          unabbrev_hyp f fv
           (CONV_RULE(RAND_CONV MLKEM_EVAL_CONV)
              (MP (SPEC k th) (CONJ vth' kth)))) in
        beta_tables := tl(!beta_tables); res
    | _ -> failwith "COEFF_TABLE");;

add_mlkem_handler "coeff"
 (fun tm ->
    match tm with
      Comb(Comb(Const("coeff",_),k),p) when is_numeral k &&
                                         dest_numeral k </ num 256 ->
        (COEFF_TABLE p).(Num.int_of_num(dest_numeral k))
    | _ -> failwith "coeff");;

(* mlkem_ntt p n for n < 256, computing all 256 at once *)

let NTT_TABLE p =
  rq_table (mk_comb(ev_ntt,p))
   (fun () ->
      let ctab = COEFF_TABLE p in
      mlkem_report "NTT";
      let pv,hth = abbrev_hyp p in
      let ctab' = Array.map
        (fun th -> TRANS (AP_TERM (rator(lhs(concl th))) hth) th) ctab in
      rq_tables := (pv,ctab')::(!rq_tables);
      let cth = EQ_MP (SYM(AP_THM (AP_TERM ev_in_rq hth) ev_carrier_rq))
                      (RQ_CARRIER p) in
      let fth = MATCH_MP MLKEM_NTT_FORWARD_REM cth in
      let res = Array.init 256 (fun n ->
        unabbrev_hyp p pv
         (CONV_RULE(RAND_CONV MLKEM_EVAL_CONV)
            (SPEC (mk_small_numeral n) fth))) in
      rq_tables := tl(!rq_tables); res);;

add_mlkem_handler "mlkem_ntt"
 (fun tm ->
    match tm with
      Comb(Comb(Const("mlkem_ntt",_),p),n) when is_numeral n &&
                                              dest_numeral n </ num 256 ->
        (NTT_TABLE p).(Num.int_of_num(dest_numeral n))
    | _ -> failwith "mlkem_ntt");;

mlkem_pre_convs := [ZETA_REM_CONV; BYTELIST_BIT_CONV];;

(* ------------------------------------------------------------------------- *)
(* The top-level functions, via the NTT-domain forms KPKE_*_FIPS. The        *)
(* hypotheses about SampleNTT are discharged by evaluation.                  *)
(* ------------------------------------------------------------------------- *)

let SAMPLE_HYP_CONV =
  let closed_conv tm =
    if frees tm = [] && not(is_mlkem_literal tm) && type_of tm <> bool_ty
    then CHANGED_CONV MLKEM_EVAL_CONV tm else failwith "closed_conv" in
  ONCE_DEPTH_CONV closed_conv THENC
  REWRITE_CONV[GSYM IMP_IMP; RIGHT_FORALL_IMP_THM] THENC
  TOP_DEPTH_CONV EXPAND_CASES_CONV THENC MLKEM_EVAL_CONV;;

let FIPS_EVAL_CONV fips_th tm =
  let th1 =
    if is_imp(snd(strip_forall(concl fips_th)))
    then PART_MATCH (lhand o rand) fips_th tm
    else PART_MATCH lhs fips_th tm in
  let th2 = if is_imp(concl th1) then
              MP th1 (EQT_ELIM(SAMPLE_HYP_CONV(lhand(concl th1))))
            else th1 in
  CONV_RULE(RAND_CONV MLKEM_EVAL_CONV) th2;;

add_mlkem_handler "kpke_keygen" (FIPS_EVAL_CONV KPKE_KEYGEN_FIPS);;
add_mlkem_handler "kpke_encrypt" (FIPS_EVAL_CONV KPKE_ENCRYPT_FIPS);;
add_mlkem_handler "kpke_decrypt" (FIPS_EVAL_CONV KPKE_DECRYPT_FIPS);;

SPEC_HANDLER "mlkem_keygen_internal" mlkem_keygen_internal;;
SPEC_HANDLER "mlkem_encaps_internal" mlkem_encaps_internal;;
SPEC_HANDLER "mlkem_decaps_internal" mlkem_decaps_internal;;

let MLKEM_TOP_EVAL_CONV =
  REWRITE_CONV[mlkem512; mlkem768; mlkem1024] THENC MLKEM_EVAL_CONV;;
