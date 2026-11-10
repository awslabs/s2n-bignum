(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Evaluation of the ML-DSA functions of common/fips204.ml on concrete       *)
(* inputs by proof, used to check the specification against NIST test        *)
(* vectors. Key generation, one signing attempt and verification are         *)
(* evaluated via their NTT-domain forms MLDSA_*_FIPS of                      *)
(* common/fips204_theory.ml, with the NTT computed by a proved fast          *)
(* (Cooley-Tukey) evaluation and the inverse NTT checked through the NTT.    *)
(* SHAKE is evaluated on states kept as lists of 25 lanes, each an explicit  *)
(* chain of 64 bits, so that no large numerals are ever built.               *)
(* ========================================================================= *)

needs "common/fips204_theory.ml";;
needs "tests/mlkem/keccak_bridge.ml";;
needs "tests/mlkem/mlkem_eval.ml";;

(* ------------------------------------------------------------------------- *)
(* Two facts about congruences of Library/integer.ml, which this file does   *)
(* not load.                                                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_EV_INT_CONG_REFL = prove
 (`!x n:int. (x == x) (mod n)`,
  INTEGER_TAC);;

let MLDSA_EV_INT_CONG_TRANS = prove
 (`!x y z n:int. (x == y) (mod n) /\ (y == z) (mod n) ==> (x == z) (mod n)`,
  INTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Numbers as explicit chains of bits, keccak_ev_bit b0 (keccak_ev_bit b1    *)
(* (... 0)) with the least significant bit outermost, and the bitwise        *)
(* operations xor and "and not" on numbers, with their effect on chains and  *)
(* on words.                                                                 *)
(* ------------------------------------------------------------------------- *)

let keccak_ev_bit = new_definition
 `keccak_ev_bit b n = bitval b + 2 * n`;;

let keccak_ev_xor = new_definition
 `keccak_ev_xor m n =
    nsum ((bits_of_num m DIFF bits_of_num n) UNION
          (bits_of_num n DIFF bits_of_num m)) (\i. 2 EXP i)`;;

let keccak_ev_andn = new_definition
 `keccak_ev_andn m n = nsum (bits_of_num n DIFF bits_of_num m) (\i. 2 EXP i)`;;

let KECCAK_EV_NUM_EQ = prove
 (`!m n. m = n <=> !i. ODD(m DIV 2 EXP i) <=> ODD(n DIV 2 EXP i)`,
  REWRITE_TAC[GSYM IN_BITS_OF_NUM; GSYM EXTENSION; BITS_OF_NUM_EQ]);;

let KECCAK_EV_XOR_BITS = prove
 (`!m n i. ODD(keccak_ev_xor m n DIV 2 EXP i) <=>
           ~(ODD(m DIV 2 EXP i) <=> ODD(n DIV 2 EXP i))`,
  REWRITE_TAC[GSYM IN_BITS_OF_NUM; keccak_ev_xor] THEN
  SIMP_TAC[BITS_OF_NUM_NSUM; FINITE_UNION; FINITE_DIFF; FINITE_BITS_OF_NUM] THEN
  REWRITE_TAC[IN_UNION; IN_DIFF] THEN CONV_TAC TAUT);;

let KECCAK_EV_ANDN_BITS = prove
 (`!m n i. ODD(keccak_ev_andn m n DIV 2 EXP i) <=>
           ~ODD(m DIV 2 EXP i) /\ ODD(n DIV 2 EXP i)`,
  REWRITE_TAC[GSYM IN_BITS_OF_NUM; keccak_ev_andn] THEN
  SIMP_TAC[BITS_OF_NUM_NSUM; FINITE_DIFF; FINITE_BITS_OF_NUM] THEN
  REWRITE_TAC[IN_DIFF] THEN CONV_TAC TAUT);;

let KECCAK_EV_BIT_DIV2 = prove
 (`!b n. keccak_ev_bit b n DIV 2 = n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[keccak_ev_bit] THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `bitval b` THEN
  BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[BITVAL_CLAUSES] THEN ARITH_TAC);;

let KECCAK_EV_BIT_BITS = prove
 (`(!b n. ODD(keccak_ev_bit b n DIV 2 EXP 0) <=> b) /\
   (!b n i. ODD(keccak_ev_bit b n DIV 2 EXP SUC i) <=> ODD(n DIV 2 EXP i))`,
  REWRITE_TAC[EXP; DIV_1; GSYM DIV_DIV; KECCAK_EV_BIT_DIV2] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[keccak_ev_bit] THEN
  BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[BITVAL_CLAUSES; ODD_ADD; ODD_MULT; ARITH]);;

let KECCAK_EV_XOR_CLAUSES = prove
 (`keccak_ev_xor 0 0 = 0 /\
   (!a b m n. keccak_ev_xor (keccak_ev_bit a m) (keccak_ev_bit b n) =
              keccak_ev_bit (~(a <=> b)) (keccak_ev_xor m n))`,
  ONCE_REWRITE_TAC[KECCAK_EV_NUM_EQ] THEN
  REWRITE_TAC[KECCAK_EV_XOR_BITS; DIV_0; ARITH] THEN
  MAP_EVERY X_GEN_TAC [`a:bool`; `b:bool`; `m:num`; `n:num`] THEN
  INDUCT_TAC THEN REWRITE_TAC[KECCAK_EV_BIT_BITS; KECCAK_EV_XOR_BITS]);;

let KECCAK_EV_ANDN_CLAUSES = prove
 (`keccak_ev_andn 0 0 = 0 /\
   (!a b m n. keccak_ev_andn (keccak_ev_bit a m) (keccak_ev_bit b n) =
              keccak_ev_bit (~a /\ b) (keccak_ev_andn m n))`,
  ONCE_REWRITE_TAC[KECCAK_EV_NUM_EQ] THEN
  REWRITE_TAC[KECCAK_EV_ANDN_BITS; DIV_0; ARITH] THEN
  MAP_EVERY X_GEN_TAC [`a:bool`; `b:bool`; `m:num`; `n:num`] THEN
  INDUCT_TAC THEN REWRITE_TAC[KECCAK_EV_BIT_BITS; KECCAK_EV_ANDN_BITS]);;

let KECCAK_EV_WORD_XOR = prove
 (`!m n. word_xor (word m:N word) (word n) = word(keccak_ev_xor m n)`,
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_XOR; BIT_WORD; KECCAK_EV_XOR_BITS] THEN
  CONV_TAC TAUT);;

let KECCAK_EV_WORD_ANDN = prove
 (`!m n. word_and (word_not(word m):N word) (word n) =
         word(keccak_ev_andn m n)`,
  REWRITE_TAC[WORD_EQ_BITS; BIT_WORD_AND; BIT_WORD_NOT; BIT_WORD;
              KECCAK_EV_ANDN_BITS] THEN
  CONV_TAC TAUT);;

(* ------------------------------------------------------------------------- *)
(* Chains as terms, and conversions for xor and "and not" of chains of the   *)
(* same length (a multiple of 4), four bits at a time by tables.             *)
(* ------------------------------------------------------------------------- *)

let kev_T = `T` and kev_F = `F` and kev_0 = `0`;;
let kev_bitT = `keccak_ev_bit T` and kev_bitF = `keccak_ev_bit F`;;
let kev_x = `x:num` and kev_y = `y:num`;;
let kev_m = `m:num` and kev_n = `n:num`;;

let rec kev_chain_onto bits tl =
  match bits with
    [] -> tl
  | b::t -> mk_comb((if b then kev_bitT else kev_bitF),kev_chain_onto t tl);;

let kev_chain bits = kev_chain_onto bits kev_0;;

let rec kev_chain_vars vs tl =
  match vs with
    [] -> tl
  | v::t -> mk_comb(mk_comb(`keccak_ev_bit`,v),kev_chain_vars t tl);;

let rec kev_dest_chain tm =
  match tm with
    Comb(Comb(Const("keccak_ev_bit",_),b),t) -> b::kev_dest_chain t
  | _ -> [];;

let kev_chain_value tm =
  itlist (fun b n -> 2 * n + (if b = kev_T then 1 else 0))
         (kev_dest_chain tm) 0;;

let kev_bits n k = map (fun i -> (n lsr i) land 1 = 1) (0--(k-1));;

let KECCAK_EV_BINOP_CONV clauses =
  let base,step = CONJ_PAIR clauses in
  let fn = rator(rator(lhs(concl base))) in
  let tab = Array.init 256 (fun ab ->
    let tm = mk_comb(mk_comb(fn,kev_chain_onto (kev_bits (ab / 16) 4) kev_x),
                     kev_chain_onto (kev_bits (ab mod 16) 4) kev_y) in
    (PURE_REWRITE_CONV[step] THENC REWRITE_CONV[]) tm) in
  let res = Array.map (fun th -> kev_chain_value(rand(concl th))) tab in
  let bitc = [|kev_bitF; kev_bitT|] in
  let ctx c th =
    let b i = bitc.((c lsr i) land 1) in
    AP_TERM (b 0) (AP_TERM (b 1) (AP_TERM (b 2) (AP_TERM (b 3) th))) in
  let bv b = if b = kev_T then 1 else 0 in
  let peel4 tm =
    match tm with
      Comb(Comb(_,b0),Comb(Comb(_,b1),Comb(Comb(_,b2),Comb(Comb(_,b3),r)))) ->
        bv b0 + 2 * bv b1 + 4 * bv b2 + 8 * bv b3,r
    | _ -> failwith "KECCAK_EV_BINOP_CONV" in
  let rec conv m n =
    if m = kev_0 && n = kev_0 then base else
    let a,m' = peel4 m and b,n' = peel4 n in
    let i = 16 * a + b in
    TRANS (INST [m',kev_x; n',kev_y] tab.(i)) (ctx res.(i) (conv m' n')) in
  fun tm ->
    match tm with
      Comb(Comb(f,m),n) when f = fn -> conv m n
    | _ -> failwith "KECCAK_EV_BINOP_CONV";;

let KECCAK_EV_XOR_CONV = KECCAK_EV_BINOP_CONV KECCAK_EV_XOR_CLAUSES;;
let KECCAK_EV_ANDN_CONV = KECCAK_EV_BINOP_CONV KECCAK_EV_ANDN_CLAUSES;;

(* ------------------------------------------------------------------------- *)
(* Rotations of 64-bit words, and their bytes, as instances of theorems in   *)
(* 64 boolean variables b0, ..., b63 for the bits of a chain.                *)
(* ------------------------------------------------------------------------- *)

let KECCAK_EV_CHAIN_BIT_CONV =
  let th0,thS = CONJ_PAIR KECCAK_EV_BIT_BITS in
  let rec conv tm =
    match tm with
      Comb(Const("ODD",_),Comb(Comb(Const("DIV",_),c),
                               Comb(Comb(Const("EXP",_),_),n))) ->
        if n = kev_0 then REWR_CONV th0 tm
        else (RAND_CONV(RAND_CONV(RAND_CONV num_CONV)) THENC
              REWR_CONV thS THENC conv) tm
    | _ -> failwith "KECCAK_EV_CHAIN_BIT_CONV" in
  conv;;

let KECCAK_EV_ARITH_CONV =
  DEPTH_CONV(fun tm ->
    match tm with
      Comb(Comb(Const("EXP",_),_),_) -> failwith "KECCAK_EV_ARITH_CONV"
    | _ -> NUM_RED_CONV tm);;

let KECCAK_EV_BITS_TAC n =
  REWRITE_TAC[WORD_EQ_BITS] THEN X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC (mk_binop `(<):num->num->bool` `i:num` (mk_small_numeral n))
  THENL
   [POP_ASSUM MP_TAC THEN SPEC_TAC(`i:num`,`i:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC[BIT_WORD_ROL; BIT_WORD_SUBWORD; BIT_WORD; DIMINDEX_64;
                DIMINDEX_8] THEN
    CONV_TAC KECCAK_EV_ARITH_CONV THEN REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV KECCAK_EV_CHAIN_BIT_CONV) THEN REWRITE_TAC[];
    ASM_SIMP_TAC[BIT_TRIVIAL; DIMINDEX_64; DIMINDEX_8; GSYM NOT_LT]];;

let kev_vars = map (fun i -> mk_var("b"^string_of_int i,bool_ty)) (0--63);;

let KECCAK_EV_ROL_THM =
  let cache = Hashtbl.create 64 in
  fun k ->
    try Hashtbl.find cache k with Not_found ->
    let rot = map (fun i -> el ((i + 64 - k) mod 64) kev_vars) (0--63) in
    let lhs = mk_comb(mk_comb(`word_rol:int64->num->int64`,
                       mk_comb(`word:num->int64`,
                               kev_chain_vars kev_vars kev_0)),
                      mk_small_numeral k) in
    let rhs = mk_comb(`word:num->int64`,kev_chain_vars rot kev_0) in
    let th = prove(mk_eq(lhs,rhs),KECCAK_EV_BITS_TAC 64) in
    Hashtbl.add cache k th; th;;

let KECCAK_EV_BYTE_THMS =
  Array.init 8 (fun j ->
    let bs = map (fun i -> el (8 * j + i) kev_vars) (0--7) in
    let lhs = mk_comb(mk_comb(`word_subword:int64->num#num->byte`,
                       mk_comb(`word:num->int64`,
                               kev_chain_vars kev_vars kev_0)),
                      mk_pair(mk_binop `( * ):num->num->num` `8`
                                (mk_small_numeral j),`8`)) in
    let rhs = mk_comb(`word:num->byte`,kev_chain_vars bs kev_0) in
    prove(mk_eq(lhs,rhs),KECCAK_EV_BITS_TAC 8));;

let KECCAK_EV_INST_CHAIN th c = INST (zip (kev_dest_chain c) kev_vars) th;;

(* ------------------------------------------------------------------------- *)
(* Lane expressions (xor, "and not" and rotations of chains), and one round  *)
(* as an implication: if the variables C0, ..., B44 of the definition of     *)
(* keccak_round, and E0, ..., E24 for the resulting lanes, have the values   *)
(* that the definition gives them, the round gives [E0; ...; E24]. Its       *)
(* instances are found without any substitution under binders.               *)
(* ------------------------------------------------------------------------- *)

let KECCAK_EV_WORD_XOR_64 =
  SPEC_ALL(INST_TYPE [`:64`,`:N`] KECCAK_EV_WORD_XOR);;
let KECCAK_EV_WORD_ANDN_64 =
  SPEC_ALL(INST_TYPE [`:64`,`:N`] KECCAK_EV_WORD_ANDN);;

let rec KECCAK_EV_LANE_CONV tm =
  match tm with
    Comb(Comb(Const("word_xor",_),p),q) ->
      let th1 = MK_COMB(AP_TERM (rator(rator tm)) (KECCAK_EV_LANE_CONV p),
                        KECCAK_EV_LANE_CONV q) in
      let m = rand(lhand(rand(concl th1)))
      and n = rand(rand(rand(concl th1))) in
      let th2 = INST [m,kev_m; n,kev_n] KECCAK_EV_WORD_XOR_64 in
      TRANS th1 (TRANS th2 (AP_TERM (rator(rand(concl th2)))
                              (KECCAK_EV_XOR_CONV (rand(rand(concl th2))))))
  | Comb(Comb(Const("word_and",_),Comb(Const("word_not",_),p)),q) ->
      let th1 = MK_COMB(AP_TERM (rator(rator tm))
                         (AP_TERM (rator(lhand tm)) (KECCAK_EV_LANE_CONV p)),
                        KECCAK_EV_LANE_CONV q) in
      let m = rand(rand(lhand(rand(concl th1))))
      and n = rand(rand(rand(concl th1))) in
      let th2 = INST [m,kev_m; n,kev_n] KECCAK_EV_WORD_ANDN_64 in
      TRANS th1 (TRANS th2 (AP_TERM (rator(rand(concl th2)))
                              (KECCAK_EV_ANDN_CONV (rand(rand(concl th2))))))
  | Comb(Comb(Const("word_rol",_),p),k) ->
      let th1 = AP_THM (AP_TERM (rator(rator tm)) (KECCAK_EV_LANE_CONV p)) k in
      let c = rand(lhand(rand(concl th1))) in
      TRANS th1 (KECCAK_EV_INST_CHAIN
                  (KECCAK_EV_ROL_THM (Num.int_of_num(dest_numeral k))) c)
  | _ -> REFL tm;;

let kev_lane_vars =
  map (fun i -> mk_var("v"^string_of_int i,`:int64`)) (0--24);;
let kev_rc = `rc:int64`;;

let KECCAK_EV_ROUND_BINDINGS,KECCAK_EV_ROUND_THM =
  let tm = mk_comb(mk_comb(`keccak_round`,kev_rc),
                   mk_list(kev_lane_vars,`:int64`)) in
  let th1 = REWR_CONV keccak_round tm in
  let rec args n = if n = 0 then ALL_CONV
                   else RAND_CONV EL_CONV THENC RATOR_CONV(args(n - 1)) in
  let bs,_ = dest_let(rand(concl th1)) in
  let th2 = CONV_RULE(RAND_CONV(args (length bs) THENC let_CONV)) th1 in
  let rec levels tm =
    if is_let tm then let bs,body = dest_let tm in bs @ levels body
    else
      let es = dest_list tm in
      let evs = map (fun i -> mk_var("E"^string_of_int i,`:int64`))
                    (0--(length es - 1)) in
      zip evs es in
  let binds = levels (rand(concl th2)) in
  let res = mk_list(map fst (snd(chop_list (length binds - 25) binds)),
                    `:int64`) in
  let hyps = list_mk_conj(map (fun (v,e) -> mk_eq(v,e)) binds) in
  binds,
  prove(mk_imp(hyps,mk_eq(tm,res)),
    DISCH_TAC THEN REWRITE_TAC[th2] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC(CONJUNCTS th)));;

let KECCAK_EV_ROUND_CONV tm =
  match tm with
    Comb(Comb(Const("keccak_round",_),rc),l) ->
      let sub0 = (rc,kev_rc)::zip (dest_list l) kev_lane_vars in
      let sub,ths = itlist
        (fun (v,e) (sub,ths) ->
           let th = KECCAK_EV_LANE_CONV (vsubst sub e) in
           ((rand(concl th),v)::sub),(SYM th)::ths)
        (rev KECCAK_EV_ROUND_BINDINGS) (sub0,[]) in
      MP (INST sub KECCAK_EV_ROUND_THM) (end_itlist CONJ (rev ths))
  | _ -> failwith "KECCAK_EV_ROUND_CONV";;

(* |- n = chain of k bits, for a numeral n < 2 EXP k, and the round          *)
(* constants as chains.                                                      *)

let kev_num_bits n k =
  let rec bits n k =
    if k = 0 then [] else
    (mod_num n (Num.num_of_int 2) =/ Num.num_of_int 1)::
    bits (quo_num n (Num.num_of_int 2)) (k - 1) in
  bits n k;;

let KECCAK_EV_NUM_CHAIN_CONV k tm =
  let c = kev_chain (kev_num_bits (dest_numeral tm) k) in
  SYM((REWRITE_CONV[keccak_ev_bit; BITVAL_CLAUSES] THENC NUM_REDUCE_CONV) c);;

let KECCAK_EV_RC_THMS =
  Array.init 24 (fun i ->
    let tm = mk_comb(mk_comb(`EL:num->int64 list->int64`,mk_small_numeral i),
                     `round_constants`) in
    let th = (RAND_CONV(REWR_CONV round_constants) THENC EL_CONV) tm in
    let w = rand(concl th) in
    TRANS th (AP_TERM (rator w) (KECCAK_EV_NUM_CHAIN_CONV 64 (rand w))));;

let KECCAK_EV_LIST_CONV =
  let [pth0;pth1] = CONJUNCTS keccak in
  let kc = `keccak` and one = `1` in
  let sucs = Array.init 24 (fun k ->
    SYM(NUM_ADD_CONV(mk_binary "+" (mk_small_numeral k,one)))) in
  fun tm ->
    match tm with
      Comb(Comb(Const("keccak",_),n),l) ->
        let rec iter k th =
          if k = Num.int_of_num(dest_numeral n) then th else
          let tm' = mk_comb(mk_comb(kc,mk_small_numeral(k + 1)),l) in
          let th1 = (RATOR_CONV(RAND_CONV(K sucs.(k))) THENC REWR_CONV pth1)
                    tm' in
          let th2 = CONV_RULE(RAND_CONV(RAND_CONV(K th))) th1 in
          let th3 = CONV_RULE(RAND_CONV(LAND_CONV(K KECCAK_EV_RC_THMS.(k))))
                      th2 in
          iter (k + 1) (CONV_RULE(RAND_CONV KECCAK_EV_ROUND_CONV) th3) in
        iter 0 (INST [l,`l:int64 list`] (SPEC_ALL pth0))
    | _ -> failwith "KECCAK_EV_LIST_CONV";;

(* ------------------------------------------------------------------------- *)
(* The sponge on states keccak_state (keccak_table l) for explicit lists l   *)
(* of 25 chains: absorbing a block of bytes, applying the permutation, and   *)
(* reading the bytes of the rate.                                            *)
(* ------------------------------------------------------------------------- *)

let KECCAK_EV_NUM_OF_BYTELIST_APPEND = prove
 (`!l1 l2:byte list.
        num_of_bytelist (APPEND l1 l2) =
        num_of_bytelist l1 + 2 EXP (8 * LENGTH l1) * num_of_bytelist l2`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; num_of_bytelist; LENGTH] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `8 * SUC n = 8 + 8 * n`; EXP_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let KECCAK_EV_NUM_OF_BYTELIST_BOUND = prove
 (`!l:byte list. num_of_bytelist l < 2 EXP (8 * LENGTH l)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[num_of_bytelist; LENGTH; ARITH_RULE `8 * SUC n = 8 + 8 * n`;
              EXP_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN POP_ASSUM MP_TAC THEN ARITH_TAC);;

let KECCAK_EV_LANE8 = prove
 (`!c t:byte list.
        LENGTH c = 8
        ==> num_of_bytelist (APPEND c t) =
            val(word(num_of_bytelist c):int64) + 2 EXP 64 * num_of_bytelist t`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[KECCAK_EV_NUM_OF_BYTELIST_APPEND; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPEC `c:byte list` KECCAK_EV_NUM_OF_BYTELIST_BOUND) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let KECCAK_EV_BLOCK = prove
 (`!l1 l2 l3:byte list.
        (num_of_bytelist (APPEND l1 (APPEND l2 l3)) DIV 2 EXP (8 * LENGTH l1))
        MOD 2 EXP (8 * LENGTH l2) =
        num_of_bytelist l2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[KECCAK_EV_NUM_OF_BYTELIST_APPEND] THEN
  MP_TAC(ISPEC `l1:byte list` KECCAK_EV_NUM_OF_BYTELIST_BOUND) THEN
  MP_TAC(ISPEC `l2:byte list` KECCAK_EV_NUM_OF_BYTELIST_BOUND) THEN
  SPEC_TAC(`2 EXP (8 * LENGTH(l1:byte list))`,`p:num`) THEN
  SPEC_TAC(`2 EXP (8 * LENGTH(l2:byte list))`,`q:num`) THEN
  SPEC_TAC(`num_of_bytelist l1`,`a:num`) THEN
  SPEC_TAC(`num_of_bytelist l2`,`b:num`) THEN
  SPEC_TAC(`num_of_bytelist l3`,`c:num`) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a + p * (b + q * c)) DIV p = b + q * c` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `a:num` THEN ASM_ARITH_TAC;
    ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT]]);;

let kev_w_vars = map (fun i -> mk_var("w"^string_of_int i,`:int64`)) (0--24);;

let KECCAK_EV_STATE_HORNER =
  let horner = itlist (fun w t ->
     mk_binop `(+):num->num->num` (mk_comb(`val:int64->num`,w))
       (mk_binop `( * ):num->num->num` `2 EXP 64` t)) kev_w_vars `0` in
  let tm = mk_eq(mk_comb(`keccak_state`,
                    mk_comb(`keccak_table`,mk_list(kev_w_vars,`:int64`))),
                 mk_comb(`word:num->1600 word`,horner)) in
  prove(tm,
    REWRITE_TAC[keccak_state; keccak_table; GSYM EXP_EXP] THEN
    AP_TERM_TAC THEN SPEC_TAC(`2 EXP 64`,`p:num`) THEN GEN_TAC THEN
    CONV_TAC(LAND_CONV(EXPAND_NSUM_CONV THENC NUM_REDUCE_CONV THENC
                       ONCE_DEPTH_CONV EL_CONV)) THEN
    CONV_TAC NUM_RING);;

let KECCAK_EV_DIV5 = prove
 (`!j. j MOD 5 + 5 * (j DIV 5) = j`,
  GEN_TAC THEN MP_TAC(SPECL [`j:num`; `5`] DIVISION) THEN ARITH_TAC);;

let KECCAK_EV_SUBWORD_STATE = prove
 (`!a j. j < 25
         ==> word_subword (keccak_state a) (64 * j,64):int64 =
             a (j MOD 5) (j DIV 5)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:num->num->int64`; `j MOD 5`; `j DIV 5`]
               KECCAK_LANES_STATE) THEN
  ANTS_TAC THENL [REWRITE_TAC[MOD_LT_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[keccak_lanes; KECCAK_EV_DIV5] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC);;

let KECCAK_EV_STATE_BYTE = prove
 (`!l j b. j < 25 /\ b < 8
           ==> word_subword (keccak_state (keccak_table l)) (8 * (8 * j + b),8)
               :byte =
               word_subword (EL j l:int64) (8 * b,8)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`keccak_table l`; `j:num`] KECCAK_EV_SUBWORD_STATE) THEN
  ASM_REWRITE_TAC[keccak_table; KECCAK_EV_DIV5] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_SUBWORD o rand o snd) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN BINOP_TAC THEN ASM_ARITH_TAC);;

let KECCAK_EV_STATE_XOR = prove
 (`!l m. LENGTH l = 25 /\ LENGTH m = 25
         ==> word_xor (keccak_state (keccak_table l))
                      (keccak_state (keccak_table m)) =
             keccak_state (keccak_table (MAP2 word_xor l m))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM KECCAK_STATE_LANES] THEN
  MATCH_MP_TAC KECCAK_STATE_EQ THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[keccak_lanes; WORD_SUBWORD_XOR] THEN
  SUBGOAL_THEN `!a. word_subword (keccak_state a) (64 * (x + 5 * y),64):int64 =
                    a x y`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN MP_TAC(SPECL [`a:num->num->int64`; `x + 5 * y`]
                              KECCAK_EV_SUBWORD_STATE) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    BINOP_TAC THENL
     [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `y:num` THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    REWRITE_TAC[keccak_table] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC EL_MAP2 THEN ASM_ARITH_TAC]);;

(* Byte tables: |- val(word n:byte) = n, |- !x. n + 256 * x = chain onto x   *)
(* of the 8 bits of n, and |- chain of the 8 bits of n = n, for n < 256.     *)

let KECCAK_EV_VAL_BYTE = Array.init 256 (fun n ->
  WORD_RED_CONV (mk_comb(`val:byte->num`,
                         mk_comb(`word:num->byte`,mk_small_numeral n))));;

let KECCAK_EV_BYTE_ONTO = Array.init 256 (fun n ->
  let c = kev_chain_onto (kev_bits n 8) kev_x in
  let tm = mk_eq(mk_binop `(+):num->num->num` (mk_small_numeral n)
                   (mk_binop `( * ):num->num->num` `256` kev_x),c) in
  prove(tm,REWRITE_TAC[keccak_ev_bit; BITVAL_CLAUSES] THEN ARITH_TAC));;

let KECCAK_EV_CHAIN_BYTE = Array.init 256 (fun n ->
  let c = kev_chain (kev_bits n 8) in
  (REWRITE_CONV[keccak_ev_bit; BITVAL_CLAUSES] THENC NUM_REDUCE_CONV) c);;

let kev_byte_value tm =
  match tm with
    Comb(Const("word",_),n) -> Num.int_of_num(dest_numeral n)
  | _ -> failwith "kev_byte_value";;

(* |- num_of_bytelist l = chain, for an explicit list l of bytes.            *)

let KECCAK_EV_BYTES_CHAIN_CONV =
  let nil_th,cons_th = CONJ_PAIR num_of_bytelist in
  let cons_th = SPEC_ALL cons_th in
  let plus = `(+):num->num->num` and times256 = `( * ) 256` in
  let rec conv tm =
    match tm with
      Comb(_,Const("NIL",_)) -> nil_th
    | Comb(_,Comb(Comb(Const("CONS",_),h),t)) ->
        let th1 = REWR_CONV cons_th tm in
        let n = kev_byte_value h in
        let th2 = conv (rand(rand(rand(concl th1)))) in
        let th3 = MK_COMB(AP_TERM plus KECCAK_EV_VAL_BYTE.(n),
                          AP_TERM times256 th2) in
        TRANS th1 (TRANS th3 (INST [rand(concl th2),kev_x]
                                   KECCAK_EV_BYTE_ONTO.(n)))
    | _ -> failwith "KECCAK_EV_BYTES_CHAIN_CONV" in
  conv;;

(* APPEND [x0; ...; x(k-1)] t = CONS x0 (... (CONS x(k-1) t)) without        *)
(* looking into t, and |- APPEND [x0; ...; x(k-1)] t = l, splitting an       *)
(* explicit list l after k elements.                                         *)

let KECCAK_EV_APPEND_CONV =
  let nil_th,cons_th = CONJ_PAIR APPEND in
  let cache = ref [] in
  let get ty =
    try assoc ty (!cache) with Failure _ ->
    let n = SPEC_ALL(INST_TYPE [ty,aty] nil_th)
    and c = SPEC_ALL(INST_TYPE [ty,aty] cons_th) in
    let tv = rand(lhand(lhand(concl c))) and hv = lhand(lhand(lhand(concl c)))
    and lv = rand(lhand(concl c)) and nv = rand(lhand(concl n)) in
    let r = (n,nv),(c,hv,tv,lv) in cache := (ty,r)::(!cache); r in
  let rec conv ((n,nv),(c,hv,tv,lv) as ths) tm =
    match tm with
      Comb(Comb(_,Const("NIL",_)),l) -> INST [l,nv] n
    | Comb(Comb(_,Comb(Comb(_,h),t)),l) ->
        let th = INST [h,hv; t,tv; l,lv] c in
        TRANS th (AP_TERM (rator(rand(concl th)))
                   (conv ths (rand(rand(concl th)))))
    | _ -> failwith "KECCAK_EV_APPEND_CONV" in
  fun tm -> conv (get (hd(snd(dest_type(type_of tm))))) tm;;

let KECCAK_EV_SPLIT_LIST k l =
  let ety = hd(snd(dest_type(type_of l))) in
  let rec take k l = if k = 0 then [],l
                     else let h,t = take (k - 1) (rand l) in lhand l::h,t in
  let c,t = take k l in
  KECCAK_EV_APPEND_CONV
   (mk_comb(mk_comb(mk_const("APPEND",[ety,aty]),mk_list(c,ety)),t));;

(* |- 0 = val(word 0) + 2 EXP 64 * (... + 2 EXP 64 * 0) with k zero lanes,   *)
(* and |- num_of_bytelist l = val w0 + 2 EXP 64 * (... + 2 EXP 64 * 0) with  *)
(* k lanes for a list of 8 * m bytes, m <= k.                                *)

let kev_zero_lane = `word 0:int64`;;
let KECCAK_EV_CHAIN0_LANE =
  let c = kev_chain (replicate false 64) in
  AP_TERM `word:num->int64`
   (SYM((REWRITE_CONV[keccak_ev_bit; BITVAL_CLAUSES] THENC NUM_REDUCE_CONV)
        c));;

let KECCAK_EV_ZPAD =
  let z1 = prove(`0 = val(word 0:int64) + 2 EXP 64 * 0`,
                 REWRITE_TAC[VAL_WORD_0] THEN ARITH_TAC) in
  let a = Array.make 26 (REFL `0`) in
  for k = 1 to 25 do
    a.(k) <- TRANS z1 (AP_TERM (rator(rand(concl z1)))
                        (AP_TERM (rator(rand(rand(concl z1)))) a.(k - 1)))
  done; a;;

let kev_byte_vars = map (fun i -> mk_var("b"^string_of_int i,`:byte`)) (0--7);;
let kev_t = `t:byte list`;;

let KECCAK_EV_LANE8_CONS =
  let c = mk_list(kev_byte_vars,`:byte`) in
  let th = MP (INST [c,`c:byte list`] (SPEC_ALL KECCAK_EV_LANE8))
              (LENGTH_CONV(mk_comb(`LENGTH:byte list->num`,c))) in
  CONV_RULE(LAND_CONV(RAND_CONV KECCAK_EV_APPEND_CONV)) th;;

let KECCAK_EV_LANES_CONV =
  let nil_th = CONJUNCT1 num_of_bytelist in
  let rec conv k tm =
    match tm with
      Comb(_,Const("NIL",_)) -> TRANS nil_th KECCAK_EV_ZPAD.(k)
    | Comb(nb,l) ->
        let rec take k l = if k = 0 then [],l
                           else let h,t = take (k - 1) (rand l) in
                                lhand l::h,t in
        let bs,tl = take 8 l in
        let th1 = INST ((tl,kev_t)::zip bs kev_byte_vars)
                       KECCAK_EV_LANE8_CONS in
        let th2 = conv (k - 1) (mk_comb(nb,tl)) in
        TRANS th1 (AP_TERM (rator(rand(concl th1)))
                    (AP_TERM (rator(rand(rand(concl th1)))) th2))
    | _ -> failwith "KECCAK_EV_LANES_CONV" in
  conv;;

(* |- word(num_of_bytelist l):1600 word = keccak_state (keccak_table L) for  *)
(* a block l of at most 200 bytes (a multiple of 8), with L 25 chains.       *)

let KECCAK_EV_BLOCK_CONV tm =
  match tm with
    Comb(w,nbl) ->
      let th1 = AP_TERM w (KECCAK_EV_LANES_CONV 25 nbl) in
      let rec lanes h =
        match h with
          Comb(Comb(Const("+",_),Comb(_,wd)),Comb(_,r)) -> wd::lanes r
        | _ -> [] in
      let ls = lanes (rand(rand(concl th1))) in
      let th2 = TRANS th1 (SYM(INST (zip ls kev_w_vars)
                                   KECCAK_EV_STATE_HORNER)) in
      let lane_conv l =
        if l = kev_zero_lane then KECCAK_EV_CHAIN0_LANE
        else AP_TERM (rator l) (KECCAK_EV_BYTES_CHAIN_CONV (rand l)) in
      CONV_RULE(RAND_CONV(RAND_CONV(RAND_CONV(LIST_CONV lane_conv)))) th2
  | _ -> failwith "KECCAK_EV_BLOCK_CONV";;

let KECCAK_EV_STATE_ZERO =
  let th = KECCAK_EV_BLOCK_CONV `word(num_of_bytelist []):1600 word` in
  CONV_RULE(LAND_CONV(RAND_CONV(REWR_CONV(CONJUNCT1 num_of_bytelist)))) th;;

(* MAP2 word_xor on explicit lists of chains, and the permutation.           *)

let KECCAK_EV_MAP2_XOR_CONV =
  let nil_th,cons_th = CONJ_PAIR MAP2 in
  let rec conv tm =
    match tm with
      Comb(Comb(Comb(_,_),Const("NIL",_)),_) -> REWR_CONV nil_th tm
    | _ -> (REWR_CONV cons_th THENC
            COMB2_CONV (RAND_CONV KECCAK_EV_LANE_CONV) conv) tm in
  conv;;

let kev_lenw = `LENGTH:int64 list->num` and kev_lenb = `LENGTH:byte list->num`;;
let kev_l = `l:int64 list` and kev_ml = `m:int64 list`;;

let KECCAK_EV_F1600_STATE_CONV tm =
  match tm with
    Comb(Const("keccak_f1600",_),Comb(_,Comb(_,l))) ->
      let lth = LENGTH_CONV(mk_comb(kev_lenw,l)) in
      let th = MP (SPEC l KECCAK_F1600_BRIDGE) lth in
      CONV_RULE(RAND_CONV(RAND_CONV(RAND_CONV KECCAK_EV_LIST_CONV))) th
  | _ -> failwith "KECCAK_EV_F1600_STATE_CONV";;

(* ------------------------------------------------------------------------- *)
(* The sponge keccak_sponge c d m for an explicit message m: the absorbed    *)
(* state and the squeezed states as lane lists, and a table of the bytes     *)
(* |- keccak_sponge c d m i = word n, filled on demand. The padded message   *)
(* is split block by block, keeping |- APPEND A T = P and |- LENGTH A = r j  *)
(* for the prefix A (as a nested APPEND) and the explicit rest T.            *)
(* ------------------------------------------------------------------------- *)

let keccak_ev_report = ref (fun (s:string) -> ());;

let KECCAK_EV_SPONGE =
  let abs0,abs1 = CONJ_PAIR keccak_absorb
  and sq0,sq1 = CONJ_PAIR keccak_squeeze in
  let app_nil = CONJUNCT1 APPEND in
  let rv = `r:num` and pv = `p:num` and jv = `j:num`
  and sv = `s:1600 word` and tv = `t:num` and sucv = `SUC`
  and bv = `b:num` and lt = `(<):num->num->bool` and n25 = `25` and n8 = `8`
  and spongec = `keccak_sponge` and elc = `EL:num->int64 list->int64`
  and plus = `(+):num->num->num` and times = `( * ):num->num->num`
  and nilb = `[]:byte list` in
  let lt25 = Array.init 25 (fun j ->
    EQT_ELIM(NUM_LT_CONV(mk_binop lt (mk_small_numeral j) n25)))
  and lt8 = Array.init 8 (fun j ->
    EQT_ELIM(NUM_LT_CONV(mk_binop lt (mk_small_numeral j) n8))) in
  let offs = Array.init 200 (fun k ->
    SYM(NUM_REDUCE_CONV(mk_binop plus
      (mk_binop times n8 (mk_small_numeral(k / 8)))
      (mk_small_numeral(k mod 8))))) in
  let state_byte = SPEC_ALL KECCAK_EV_STATE_BYTE
  and state_xor = SPEC_ALL KECCAK_EV_STATE_XOR in
  let padconv =
    REWRITE_CONV[keccak_pad] THENC NUM_REDUCE_CONV THENC
    ONCE_DEPTH_CONV REPLICATE_CONV THENC REWRITE_CONV[APPEND] in
  fun c d m ->
    let tm = list_mk_comb(spongec,[c; d; m]) in
    let th1 = REWR_CONV keccak_sponge tm in
    let th2 = CONV_RULE(RAND_CONV(RAND_CONV NUM_REDUCE_CONV THENC let_CONV))
                th1 in
    let th3 = CONV_RULE(RAND_CONV(RAND_CONV
                (RAND_CONV(RAND_CONV LENGTH_CONV THENC padconv) THENC
                 KECCAK_EV_APPEND_CONV) THENC let_CONV)) th2 in
    let th4 = CONV_RULE(RAND_CONV(RAND_CONV(RAND_CONV
                (LAND_CONV LENGTH_CONV THENC NUM_DIV_CONV)) THENC let_CONV))
                th3 in
    let s0 = rand(lhand(body(rand(concl th4)))) in
    let rtm = lhand(rator s0) and ptm = rand(rator s0) and ntm = rand s0 in
    let r = Num.int_of_num(dest_numeral rtm)
    and n = Num.int_of_num(dest_numeral ntm) in
    let ab0 = INST [rtm,rv; ptm,pv] abs0
    and ab1 = INST [rtm,rv; ptm,pv] abs1 in
    let rec absorb j th sth lth =
      if j = n then th else
      let a = lhand(lhand(concl sth)) and t = rand(lhand(concl sth)) in
      let bsth = KECCAK_EV_SPLIT_LIST r t in
      let b = lhand(lhand(concl bsth)) and t' = rand(lhand(concl bsth)) in
      let blen = LENGTH_CONV(mk_comb(kev_lenb,b)) in
      let bth0 = SPECL [a; b; t'] KECCAK_EV_BLOCK in
      let bth1 = CONV_RULE(LAND_CONV(LAND_CONV(LAND_CONV(RAND_CONV
                   (RAND_CONV(K bsth) THENC K sth))))) bth0 in
      let bth2 = CONV_RULE(LAND_CONV(BINOP2_CONV
                   (RAND_CONV(RAND_CONV(RAND_CONV(K lth) THENC
                                        NUM_MULT_CONV)))
                   (RAND_CONV(RAND_CONV(K blen) THENC
                              NUM_MULT_CONV)))) bth1 in
      let jtm = mk_small_numeral j in
      let st1 = INST [jtm,jv] ab1 in
      let st2 = CONV_RULE(LAND_CONV(RAND_CONV(K(NUM_SUC_CONV
                  (mk_comb(sucv,jtm)))))) st1 in
      let st3 = CONV_RULE(RAND_CONV(RAND_CONV(BINOP2_CONV (K th)
                  (RAND_CONV(BINOP2_CONV
                    (RAND_CONV(RAND_CONV NUM_REDUCE_CONV))
                    (RAND_CONV NUM_REDUCE_CONV) THENC K bth2) THENC
                   KECCAK_EV_BLOCK_CONV)))) st2 in
      let x = rand(rand(concl st3)) in
      let l = rand(rand(lhand x)) and l' = rand(rand(rand x)) in
      let xth = MP (INST [l,kev_l; l',kev_ml] state_xor)
                   (CONJ (LENGTH_CONV(mk_comb(kev_lenw,l)))
                         (LENGTH_CONV(mk_comb(kev_lenw,l')))) in
      let st4 = CONV_RULE(RAND_CONV(RAND_CONV(K xth THENC
                  RAND_CONV(RAND_CONV KECCAK_EV_MAP2_XOR_CONV)))) st3 in
      let st5 = CONV_RULE(RAND_CONV KECCAK_EV_F1600_STATE_CONV) st4 in
      let sth' = TRANS (TRANS (SYM(ISPECL [a;b;t'] APPEND_ASSOC))
                              (AP_TERM (rator(lhand(concl sth))) bsth)) sth in
      let lth' = CONV_RULE(RAND_CONV(LAND_CONV(K lth) THENC
                            RAND_CONV(K blen) THENC NUM_ADD_CONV))
                   (ISPECL [a;b] LENGTH_APPEND) in
      absorb (j + 1) st5 sth' lth' in
    let sth0 = ISPEC (rand ptm) app_nil in
    let lth0 = LENGTH_CONV(mk_comb(kev_lenb,nilb)) in
    (!keccak_ev_report) (Printf.sprintf "Keccak: absorbing %d blocks" n);
    let absth = absorb 0 (TRANS ab0 KECCAK_EV_STATE_ZERO) sth0 lth0 in
    let sq0' = INST [s0,sv] sq0 and sq1' = INST [s0,sv] sq1 in
    let states = Hashtbl.create 10 in
    Hashtbl.add states 0 (TRANS sq0' absth);
    let rec state t =
      try Hashtbl.find states t with Not_found ->
      let th = state (t - 1) in
      let ttm = mk_small_numeral(t - 1) in
      let th1 = CONV_RULE(LAND_CONV(LAND_CONV(K(NUM_SUC_CONV
                  (mk_comb(sucv,ttm)))))) (INST [ttm,tv] sq1') in
      let th2 = CONV_RULE(RAND_CONV(RAND_CONV(K th) THENC
                                    KECCAK_EV_F1600_STATE_CONV)) th1 in
      Hashtbl.add states t th2; th2 in
    let eltabs = Hashtbl.create 10 in
    let eltab t =
      try Hashtbl.find eltabs t with Not_found ->
      let l = rand(rand(rand(concl(state t)))) in
      let a = Array.init 25 (fun j ->
        EL_CONV(mk_comb(mk_comb(elc,mk_small_numeral j),l))) in
      Hashtbl.add eltabs t a; a in
    let bytes = Hashtbl.create 1000 in
    fun i ->
      try Hashtbl.find bytes i with Not_found ->
      let t = i / r and off = i mod r in
      let j = off / 8 and b = off mod 8 in
      let th1 = CONV_RULE(RAND_CONV BETA_CONV)
                  (AP_THM th4 (mk_small_numeral i)) in
      let th2 = CONV_RULE(RAND_CONV(BINOP2_CONV
                  (LAND_CONV NUM_DIV_CONV THENC K(state t))
                  (LAND_CONV(RAND_CONV(NUM_MOD_CONV THENC K offs.(off))))))
                  th1 in
      let l = rand(rand(lhand(rand(concl th2)))) in
      let sb = MP (INST [l,kev_l; mk_small_numeral j,jv;
                         mk_small_numeral b,bv] state_byte)
                  (CONJ lt25.(j) lt8.(b)) in
      let th3 = CONV_RULE(RAND_CONV(LAND_CONV(K (eltab t).(j))))
                  (TRANS th2 sb) in
      let ch = rand(lhand(rand(concl th3))) in
      let th4 = TRANS th3 (KECCAK_EV_INST_CHAIN KECCAK_EV_BYTE_THMS.(b) ch) in
      let c8 = rand(rand(concl th4)) in
      let th5 = CONV_RULE(RAND_CONV(RAND_CONV(K
                  KECCAK_EV_CHAIN_BYTE.(kev_chain_value c8)))) th4 in
      Hashtbl.add bytes i th5; th5;;

(* Hash tables keyed by terms, with a hash of the whole term (the generic    *)
(* hash only looks at a bounded part, so that for example all the samples    *)
(* from the same seed with different nonces would collide), and caching of   *)
(* conversions with them.                                                    *)

let mev_term_hash tm =
  let rec h acc n tm =
    if n <= 0 then acc,n else
    match tm with
      Var(s,_) | Const(s,_) ->
        (acc * 65599 + Hashtbl.hash s) land 0x3FFFFFFF,n - 1
    | Comb(f,x) -> let a,n' = h ((acc * 31 + 7) land 0x3FFFFFFF) (n - 1) f in
                   h a n' x
    | Abs(v,b) -> let a,n' = h ((acc * 31 + 11) land 0x3FFFFFFF) (n - 1) v in
                  h a n' b in
  fst(h 0 20000 tm);;

let mev_tbl_create n = (Hashtbl.create n:(int*term,'a)Hashtbl.t);;
let mev_tbl_find tbl tm = Hashtbl.find tbl (mev_term_hash tm,tm);;
let mev_tbl_add tbl tm v = Hashtbl.add tbl (mev_term_hash tm,tm) v;;

let MEV_CACHED_CONV (conv:conv) =
  let cache = mev_tbl_create 100 in
  fun tm -> try mev_tbl_find cache tm with Not_found ->
            let th = conv tm in mev_tbl_add cache tm th; th;;

(* Streams of SHAKE128 and SHAKE256 outputs, cached by message:              *)
(* KECCAK_EV_SHAKE_BYTE f m i gives |- f m i = word n for f = shake128 or    *)
(* f = shake256.                                                             *)

let KECCAK_EV_SHAKE_BYTE =
  let streams = mev_tbl_create 100 in
  fun f m ->
    let key = mk_comb(f,m) in
    let th0,sp =
      try mev_tbl_find streams key with Not_found ->
      let th0 = (match f with
                   Const("shake128",_) -> REWR_CONV shake128
                 | Const("shake256",_) -> REWR_CONV shake256
                 | _ -> failwith "KECCAK_EV_SHAKE_BYTE") (mk_comb(f,m)) in
      let c,d,m' = match strip_comb(rand(concl th0)) with
                     _,[c;d;m'] -> c,d,m' | _ -> failwith "shake" in
      let r = th0,KECCAK_EV_SPONGE c d m' in
      mev_tbl_add streams key r; r in
    fun i -> TRANS (AP_THM th0 (mk_small_numeral i)) (sp i);;

(* ------------------------------------------------------------------------- *)
(* The NTT by the Cooley-Tukey splitting. A polynomial is the list of its    *)
(* coefficients (mldsa_ev_peval gives its value in Horner form); for x with  *)
(* x^m == s (mod q), its value at x is that of the half-size polynomial with *)
(* coefficients a(j) + s * a(j + m) mod q. NTT(f)[k] is the value of f at    *)
(* zeta^(2 * BitRev8(k) + 1), whose powers x^m, m = 128, 64, ..., 1, are     *)
(* known, so 8 halvings give it, sharing the work between the 256 roots.     *)
(* ------------------------------------------------------------------------- *)

let mldsa_ev_peval = define
 `mldsa_ev_peval [] (x:int) = &0 /\
  mldsa_ev_peval (CONS c l) x = c + x * mldsa_ev_peval l x`;;

let MLDSA_EV_PEVAL_APPEND = prove
 (`!l1 l2 x. mldsa_ev_peval (APPEND l1 l2) x =
             mldsa_ev_peval l1 x + x pow (LENGTH l1) * mldsa_ev_peval l2 x`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; mldsa_ev_peval; LENGTH; INT_POW] THEN
  CONV_TAC INT_RING);;

let MLDSA_EV_PEVAL_LIST_OF_SEQ = prove
 (`!a x n. mldsa_ev_peval (list_of_seq a (SUC n)) x =
           isum (0..n) (\j. a j * x pow j)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ONCE_REWRITE_TAC[list_of_seq] THEN
  ASM_REWRITE_TAC[MLDSA_EV_PEVAL_APPEND; ISUM_CLAUSES_NUMSEG; LE_0;
                  LENGTH_LIST_OF_SEQ; list_of_seq; APPEND; mldsa_ev_peval] THEN
  CONV_TAC INT_RING);;

let MLDSA_EV_NTT_PEVAL = prove
 (`!f k. f IN ring_carrier mldsa_rq
         ==> mldsa_ntt f k =
             mldsa_ev_peval (list_of_seq (\j. coeff j f) 256)
                            (&1753 pow (2 * bitreverse8 k + 1)) rem &8380417`,
  SIMP_TAC[MLDSA_NTT_FORWARD; ARITH_RULE `256 = SUC 255`;
           MLDSA_EV_PEVAL_LIST_OF_SEQ; INT_POW_POW]);;

let MLDSA_EV_ZETA_POW = prove
 (`!n. &1753 pow n rem &8380417 = &1753 pow (n MOD 512) rem &8380417`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `!x:int. x pow n = (x pow 512) pow (n DIV 512) * x pow (n MOD 512)`
   (fun th -> ONCE_REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN REWRITE_TAC[INT_POW_POW; GSYM INT_POW_ADD] THEN
    AP_TERM_TAC THEN MP_TAC(SPECL [`n:num`; `512`] DIVISION) THEN ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM INT_MUL_REM] THEN
  ONCE_REWRITE_TAC[GSYM INT_POW_REM] THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_REDUCE_CONV) THEN REWRITE_TAC[INT_POW_ONE] THEN
  CONV_TAC(ONCE_DEPTH_CONV INT_REDUCE_CONV) THEN
  REWRITE_TAC[INT_MUL_LID; INT_REM_REM]);;

(* Powers of zeta = 1753 mod q, and the congruences (x^m == s) (mod q) for   *)
(* the roots x = zeta^(2 * BitRev8(k) + 1).                                  *)

let mev_q = `&8380417:int` and mev_x = `x:int` and mev_s = `s:int`
and mev_qv = `q:int` and mev_ipow = `(pow):int->num->int`
and mev_il1 = `l1:int list` and mev_il2 = `l2:int list`
and mev_lenint = `LENGTH:int list->num`;;

let mldsa_q_num = Num.num_of_int 8380417;;

let mev_int n =
  if n < 0 then mk_comb(`int_neg`,mk_comb(`int_of_num`,mk_small_numeral(-n)))
  else mk_comb(`int_of_num`,mk_small_numeral n);;

let mev_dest_int tm = Num.int_of_num(dest_intconst tm);;

(* |- &1753 pow e rem &8380417 = &v for e < 512, and bitreverse8 values.     *)

let MLDSA_EV_ZETA_TABLE =
  let th0 = INT_REDUCE_CONV `&1753 pow 0 rem &8380417` in
  let a = Array.make 512 th0 in
  let step = prove
   (`!e v. &1753 pow e rem &8380417 = v
           ==> &1753 pow (SUC e) rem &8380417 = (&1753 * v) rem &8380417`,
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[INT_POW] THEN CONV_TAC INT_REM_DOWN_CONV THEN REFL_TAC) in
  for e = 1 to 511 do
    let th1 = MP (SPECL [mk_small_numeral(e - 1); rand(concl a.(e - 1))] step)
                 a.(e - 1) in
    let th2 = CONV_RULE(LAND_CONV(LAND_CONV(RAND_CONV NUM_SUC_CONV)) THENC
                        RAND_CONV INT_REDUCE_CONV) th1 in
    a.(e) <- th2
  done; a;;

let MLDSA_EV_BITREVERSE8 =
  Array.init 256 (fun i ->
    (REWR_CONV bitreverse8 THENC WORD_REDUCE_CONV)
    (mk_comb(`bitreverse8`,mk_small_numeral i)));;

let mldsa_br8 i =
  let rec go i k =
    if k = 0 then 0 else (i land 1) lsl (k - 1) lor go (i lsr 1) (k - 1) in
  go i 8;;

(* |- ((&1753 pow (2 * bitreverse8 k + 1)) pow m == &s) (mod &8380417).      *)

let MLDSA_EV_ROOT_POW =
  let cache = Hashtbl.create 3000 in
  let pth = prove
   (`!k m e s. (2 * k + 1) * m = e /\
               &1753 pow (e MOD 512) rem &8380417 = &s /\ s < 8380417
               ==> (((&1753:int) pow (2 * k + 1)) pow m == &s) (mod &8380417)`,
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[INT_POW_POW; GSYM INT_REM_EQ] THEN
    ONCE_REWRITE_TAC[MLDSA_EV_ZETA_POW] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_REM_LT THEN
    ASM_REWRITE_TAC[INT_OF_NUM_LT; INT_POS]) in
  fun k m ->
    try Hashtbl.find cache (k,m) with Not_found ->
    let b = mldsa_br8 k in
    let e = (2 * b + 1) * m in
    let zt = MLDSA_EV_ZETA_TABLE.(e mod 512) in
    let s = rand(rand(concl zt)) in
    let th1 = SPECL [mk_comb(`bitreverse8`,mk_small_numeral k);
                     mk_small_numeral m; mk_small_numeral e; s] pth in
    let ante = lhand(concl th1) in
    let ath = EQT_ELIM((REWRITE_CONV[MLDSA_EV_BITREVERSE8.(k)] THENC
                        NUM_REDUCE_CONV THENC REWRITE_CONV[zt]) ante) in
    let th = MP th1 ath in
    Hashtbl.add cache (k,m) th; th;;

let MLDSA_EV_PEVAL_SING = prove
 (`!c x. mldsa_ev_peval [c] x = c`,
  REWRITE_TAC[mldsa_ev_peval; INT_MUL_RZERO; INT_ADD_RID]);;

let MLDSA_EV_CONG_REM = prove
 (`!a c. (a == &c) (mod &8380417) /\ c < 8380417
         ==> a rem &8380417 = &c`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[INT_REM_UNIQUE] THEN
  ASM_REWRITE_TAC[INT_POS; INT_OF_NUM_LT] THEN
  CONV_TAC INT_REDUCE_CONV THEN ASM_REWRITE_TAC[INT_OF_NUM_LT]);;


(* One halving computes the products t = s * b once for both halves, which   *)
(* are a + t (for x^m == s) and a - t (for x^m == -s).                       *)

let MLDSA_EV_PEVAL_MAP = prove
 (`!l x s q. (mldsa_ev_peval (MAP (\b. (s * b) rem q) l) x ==
              s * mldsa_ev_peval l x) (mod q)`,
  let lemma = INTEGER_RULE
   `!r m b s x p q:int.
        (r == s * b) (mod q) /\ (m == s * p) (mod q)
        ==> (r + x * m == s * (b + x * p)) (mod q)` in
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; mldsa_ev_peval] THEN
  REWRITE_TAC[INT_MUL_RZERO; MLDSA_EV_INT_CONG_REFL] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC lemma THEN
  ASM_REWRITE_TAC[INT_REM_MOD_SELF]);;

let MLDSA_EV_PEVAL_MAP2_ADD = prove
 (`!l1 l2 x q.
        LENGTH l1 = LENGTH l2
        ==> (mldsa_ev_peval (MAP2 (\a t. (a + t) rem q) l1 l2) x ==
             mldsa_ev_peval l1 x + mldsa_ev_peval l2 x) (mod q)`,
  let lemma = INTEGER_RULE
   `!r m a b x p1 p2 q:int.
        (r == a + b) (mod q) /\ (m == p1 + p2) (mod q)
        ==> (r + x * m == (a + x * p1) + (b + x * p2)) (mod q)` in
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; MAP2; mldsa_ev_peval] THEN
  REWRITE_TAC[INT_MUL_RZERO; INT_ADD_RID; MLDSA_EV_INT_CONG_REFL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma THEN
  REWRITE_TAC[INT_REM_MOD_SELF] THEN ASM_SIMP_TAC[]);;

let MLDSA_EV_PEVAL_MAP2_SUB = prove
 (`!l1 l2 x q.
        LENGTH l1 = LENGTH l2
        ==> (mldsa_ev_peval (MAP2 (\a t. (a - t) rem q) l1 l2) x ==
             mldsa_ev_peval l1 x - mldsa_ev_peval l2 x) (mod q)`,
  let lemma = INTEGER_RULE
   `!r m a b x p1 p2 q:int.
        (r == a - b) (mod q) /\ (m == p1 - p2) (mod q)
        ==> (r + x * m == (a + x * p1) - (b + x * p2)) (mod q)` in
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; NOT_SUC; GSYM NOT_SUC; SUC_INJ; MAP2; mldsa_ev_peval] THEN
  REWRITE_TAC[INT_MUL_RZERO; INT_ADD_RID; INT_SUB_RZERO;
              MLDSA_EV_INT_CONG_REFL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma THEN
  REWRITE_TAC[INT_REM_MOD_SELF] THEN ASM_SIMP_TAC[]);;

let MLDSA_EV_CONG_ADD_TRANS = INTEGER_RULE
 `!c p1 d e q:int. (c == p1 + d) (mod q) /\ (d == e) (mod q)
                   ==> (c == p1 + e) (mod q)`;;

let MLDSA_EV_CONG_SUB_TRANS = INTEGER_RULE
 `!c p1 d e q:int. (c == p1 - d) (mod q) /\ (d == e) (mod q)
                   ==> (c == p1 - e) (mod q)`;;

let MLDSA_EV_SPLIT_PLUS = prove
 (`!l1 l2 x s q m.
        LENGTH l1 = m /\ LENGTH l2 = m /\ (x pow m == s) (mod q)
        ==> (mldsa_ev_peval (APPEND l1 l2) x ==
             mldsa_ev_peval (MAP2 (\a t. (a + t) rem q) l1
                                  (MAP (\b. (s * b) rem q) l2)) x) (mod q)`,
  let lemma = INTEGER_RULE
   `!a b c s t q:int.
        (t == s) (mod q) /\ (c == a + s * b) (mod q)
        ==> (a + t * b == c) (mod q)` in
  REPEAT STRIP_TAC THEN REWRITE_TAC[MLDSA_EV_PEVAL_APPEND] THEN
  MATCH_MP_TAC lemma THEN EXISTS_TAC `s:int` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MLDSA_EV_CONG_ADD_TRANS THEN
  EXISTS_TAC `mldsa_ev_peval (MAP (\b. (s * b) rem q) l2) x` THEN
  REWRITE_TAC[MLDSA_EV_PEVAL_MAP] THEN
  MATCH_MP_TAC MLDSA_EV_PEVAL_MAP2_ADD THEN ASM_REWRITE_TAC[LENGTH_MAP]);;

let MLDSA_EV_SPLIT_MINUS = prove
 (`!l1 l2 x s s' q m.
        LENGTH l1 = m /\ LENGTH l2 = m /\ (x pow m == s') (mod q) /\
        (s + s' == &0) (mod q)
        ==> (mldsa_ev_peval (APPEND l1 l2) x ==
             mldsa_ev_peval (MAP2 (\a t. (a - t) rem q) l1
                                  (MAP (\b. (s * b) rem q) l2)) x) (mod q)`,
  let lemma = INTEGER_RULE
   `!a b c s s' t q:int.
        (t == s') (mod q) /\ (s + s' == &0) (mod q) /\
        (c == a - s * b) (mod q)
        ==> (a + t * b == c) (mod q)` in
  REPEAT STRIP_TAC THEN REWRITE_TAC[MLDSA_EV_PEVAL_APPEND] THEN
  MATCH_MP_TAC lemma THEN MAP_EVERY EXISTS_TAC [`s:int`; `s':int`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MLDSA_EV_CONG_SUB_TRANS THEN
  EXISTS_TAC `mldsa_ev_peval (MAP (\b. (s * b) rem q) l2) x` THEN
  REWRITE_TAC[MLDSA_EV_PEVAL_MAP] THEN
  MATCH_MP_TAC MLDSA_EV_PEVAL_MAP2_SUB THEN ASM_REWRITE_TAC[LENGTH_MAP]);;

(* Fast (a + t) rem q and (a - t) rem q for a, t in [0,q).                   *)

let MLDSA_EV_ADDREM_LT = prove
 (`!a t. a + t < 8380417 ==> (&a + &t) rem &8380417 = &(a + t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_REM_UNIQ THEN
  EXISTS_TAC `&0:int` THEN
  REWRITE_TAC[INT_ABS_NUM; INT_MUL_LZERO; INT_ADD_LID; INT_OF_NUM_ADD;
              INT_POS; INT_OF_NUM_LT] THEN
  ASM_ARITH_TAC);;

let MLDSA_EV_ADDREM_GE = prove
 (`!a t. 8380417 <= a + t /\ a + t < 16760834
         ==> (&a + &t) rem &8380417 = &((a + t) - 8380417)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_REM_UNIQ THEN
  EXISTS_TAC `&1:int` THEN
  ASM_SIMP_TAC[INT_ABS_NUM; GSYM INT_OF_NUM_SUB; INT_OF_NUM_LT; INT_POS] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
  CONJ_TAC THENL [INT_ARITH_TAC; ASM_ARITH_TAC]);;

let MLDSA_EV_SUBREM_LE = prove
 (`!a t. t <= a /\ a < 8380417 ==> (&a - &t) rem &8380417 = &(a - t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_REM_UNIQ THEN
  EXISTS_TAC `&0:int` THEN
  ASM_SIMP_TAC[INT_ABS_NUM; GSYM INT_OF_NUM_SUB; INT_OF_NUM_LT; INT_POS] THEN
  CONJ_TAC THENL [INT_ARITH_TAC; ASM_ARITH_TAC]);;

let MLDSA_EV_SUBREM_GT = prove
 (`!a t. a < t /\ t < 8380417
         ==> (&a - &t) rem &8380417 = &((a + 8380417) - t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t <= a + 8380417` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC INT_REM_UNIQ THEN EXISTS_TAC `-- &1:int` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP INT_OF_NUM_SUB th)]) THEN
  REWRITE_TAC[INT_ABS_NUM; GSYM INT_OF_NUM_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_OF_NUM_LT]) THEN
  ASM_INT_ARITH_TAC);;

let mldsa_zeta_pow =
  let a = Array.make 512 0 in
  let r = ref 1 in
  for e = 0 to 511 do a.(e) <- !r; r := (!r * 1753) mod 8380417 done;
  fun e -> a.(e mod 512);;

let MLDSA_EV_ADDZERO = prove
 (`!s s'. s + s' = 8380417 ==> (&s + &s' == &0:int) (mod &8380417)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[INT_OF_NUM_ADD] THEN
  SPEC_TAC(`&8380417:int`,`n:int`) THEN CONV_TAC INTEGER_RULE);;

(* (&a + &t) rem q, (&a - &t) rem q and (&s * &b) rem q for literals a, t,   *)
(* s, b in [0,q).                                                            *)

let MLDSA_EV_ADDREM_CONV,MLDSA_EV_SUBREM_CONV,MLDSA_EV_MULREM_CONV =
  let lt = `(<):num->num->bool` and le = `(<=):num->num->bool`
  and plus = `(+):num->num->num` and q = `8380417` and q2 = `16760834` in
  let num_of tm = Num.int_of_num(dest_numeral(rand tm)) in
  let lt_th a b = EQT_ELIM(NUM_LT_CONV(mk_binop lt a b)) in
  let le_th a b = EQT_ELIM(NUM_LE_CONV(mk_binop le a b)) in
  let addc tm =
    let a = rand(lhand(lhand tm)) and t = rand(rand(lhand tm)) in
    let s = num_of(lhand(lhand tm)) + num_of(rand(lhand tm)) in
    let sth = NUM_ADD_CONV(mk_binop plus a t) in
    let sv = rand(concl sth) in
    if s < 8380417 then
      let th = MP (SPECL [a; t] MLDSA_EV_ADDREM_LT)
                  (EQ_MP (SYM(AP_THM (AP_TERM lt sth) q)) (lt_th sv q)) in
      CONV_RULE(RAND_CONV(RAND_CONV(K sth))) th
    else
      let th = MP (SPECL [a; t] MLDSA_EV_ADDREM_GE)
                  (CONJ (EQ_MP (SYM(AP_TERM (mk_comb(le,q)) sth)) (le_th q sv))
                        (EQ_MP (SYM(AP_THM (AP_TERM lt sth) q2))
                               (lt_th sv q2))) in
      CONV_RULE(RAND_CONV(RAND_CONV(LAND_CONV(K sth) THENC NUM_SUB_CONV))) th
  and subc tm =
    let a = rand(lhand(lhand tm)) and t = rand(rand(lhand tm)) in
    let av = num_of(lhand(lhand tm)) and tv = num_of(rand(lhand tm)) in
    if tv <= av then
      let th = MP (SPECL [a; t] MLDSA_EV_SUBREM_LE)
                  (CONJ (le_th t a) (lt_th a q)) in
      CONV_RULE(RAND_CONV(RAND_CONV NUM_SUB_CONV)) th
    else
      let th = MP (SPECL [a; t] MLDSA_EV_SUBREM_GT)
                  (CONJ (lt_th a t) (lt_th t q)) in
      CONV_RULE(RAND_CONV(RAND_CONV NUM_REDUCE_CONV)) th
  and mulc = INT_REDUCE_CONV in
  addc,subc,mulc;;

(* MAP and MAP2 of the butterflies on explicit lists of literals.            *)

let MLDSA_EV_MAP_CONV,MLDSA_EV_MAP2_ADD_CONV,MLDSA_EV_MAP2_SUB_CONV =
  let ity = `:int` in
  let mnil,mcons = CONJ_PAIR(INST_TYPE [ity,aty; ity,bty] MAP) in
  let tyin = [ity,aty; ity,bty; ity,`:C`] in
  let nil2,cons2 = CONJ_PAIR(INST_TYPE tyin MAP2) in
  let mnil = SPEC_ALL mnil and mcons = SPEC_ALL mcons in
  let mapc =
    let arith = BETA_CONV THENC MLDSA_EV_MULREM_CONV in
    let rec conv tm =
      match tm with
        Comb(_,Const("NIL",_)) -> REWR_CONV mnil tm
      | _ -> (REWR_CONV mcons THENC COMB2_CONV (RAND_CONV arith) conv) tm in
    conv in
  let map2c ar =
    let arith = RATOR_CONV BETA_CONV THENC BETA_CONV THENC ar in
    let rec conv tm =
      match tm with
        Comb(Comb(Comb(_,_),Const("NIL",_)),_) -> REWR_CONV nil2 tm
      | _ -> (REWR_CONV cons2 THENC COMB2_CONV (RAND_CONV arith) conv) tm in
    conv in
  mapc,map2c MLDSA_EV_ADDREM_CONV,map2c MLDSA_EV_SUBREM_CONV;;

(* The splitting tree for an explicit list l0 of 256 integers: for each      *)
(* leaf, A |- (mldsa_ev_peval l0 x == &c) (mod &8380417), where A are the    *)
(* hypotheses (x pow m == &s) (mod &8380417) satisfied by the root x of      *)
(* index k; the leaves are indexed by bitreverse8 k.                         *)

let MLDSA_EV_FFT_LEAVES =
  let peval = `mldsa_ev_peval` and x = mev_x and q = mev_q in
  let pow = mev_ipow in
  let plus_th = SPEC_ALL MLDSA_EV_SPLIT_PLUS
  and minus_th = SPEC_ALL MLDSA_EV_SPLIT_MINUS in
  let sm = `m:num` and sv' = `s':int` and nplus = `(+):num->num->num` in
  let maptm = `MAP:(int->int)->int list->int list`
  and bv = `b:int` and mul = `( * ):int->int->int`
  and remc = `(rem):int->int->int` in
  let trans_th = SPEC_ALL MLDSA_EV_INT_CONG_TRANS in
  let tx = `x:int` and ty = `y:int` and tz = `z:int` and tn = `n:int` in
  let sing = SPEC_ALL MLDSA_EV_PEVAL_SING and cv = `c:int` in
  let congc,mods =
    match strip_comb(concl(SPECL [x; q] MLDSA_EV_INT_CONG_REFL)) with
      c,[_;_;m] -> c,m | _ -> failwith "congc" in
  fun l0 ->
    let res = Array.make 256 TRUTH in
    let p0 = mk_comb(mk_comb(peval,l0),x) in
    let root = SPECL [p0; q] MLDSA_EV_INT_CONG_REFL in
    let rec go t rho th l =
      if t = 8 then
        let c = hd(dest_list l) in
        res.(rho) <- CONV_RULE(LAND_CONV(K(INST [c,cv] sing))) th
      else
        let m = 1 lsl (7 - t) in
        let mtm = mk_small_numeral m in
        let sth = KECCAK_EV_SPLIT_LIST m l in
        let l1 = lhand(lhand(concl sth)) and l2 = rand(lhand(concl sth)) in
        let len1 = LENGTH_CONV(mk_comb(mev_lenint,l1))
        and len2 = LENGTH_CONV(mk_comb(mev_lenint,l2)) in
        let s = mldsa_zeta_pow (m * (2 * rho + 1)) in
        let s' = 8380417 - s in
        let stm = mev_int s and stm' = mev_int s' in
        let f = mk_abs(bv,mk_binop remc (mk_binop mul stm bv) q) in
        let mth = MLDSA_EV_MAP_CONV(mk_comb(mk_comb(maptm,f),l2)) in
        let hyp v = ASSUME(list_mk_comb(congc,[mk_binop pow x mtm; v; mods])) in
        let child1 =
          let sp = MP (INST [l1,mev_il1; l2,mev_il2; stm,mev_s; q,mev_qv;
                             mtm,sm] plus_th)
                      (CONJ len1 (CONJ len2 (hyp stm))) in
          CONV_RULE(RATOR_CONV(LAND_CONV(LAND_CONV(K sth)) THENC
            RAND_CONV(LAND_CONV(RAND_CONV(K mth) THENC
                                MLDSA_EV_MAP2_ADD_CONV)))) sp
        and child2 =
          let zth = MP (SPECL [rand stm; rand stm'] MLDSA_EV_ADDZERO)
                       (NUM_ADD_CONV(mk_binop nplus (rand stm) (rand stm'))) in
          let sp = MP (INST [l1,mev_il1; l2,mev_il2; stm,mev_s; stm',sv';
                             q,mev_qv; mtm,sm] minus_th)
                      (CONJ len1 (CONJ len2 (CONJ (hyp stm') zth))) in
          CONV_RULE(RATOR_CONV(LAND_CONV(LAND_CONV(K sth)) THENC
            RAND_CONV(LAND_CONV(RAND_CONV(K mth) THENC
                                MLDSA_EV_MAP2_SUB_CONV)))) sp in
        let next rho' sp =
          let a = lhand(rator(concl th)) and b = rand(rator(concl th))
          and c = rand(rator(concl sp)) in
          let th' = MP (INST [a,tx; b,ty; c,tz; q,tn] trans_th) (CONJ th sp) in
          go (t + 1) rho' th' (lhand c) in
        next rho child1; next (rho + (1 lsl t)) child2 in
    go 0 0 root l0; res;;


(* ------------------------------------------------------------------------- *)
(* Bounded quantifiers: !i. i < n ==> P i, proved from the instances or      *)
(* refuted by one of them.                                                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_EV_BOUNDED_STEP = prove
 (`!P n. (!i. i < n ==> P i) /\ P n ==> !i. i < SUC n ==> P i`,
  REWRITE_TAC[LT] THEN MESON_TAC[]);;

let MLDSA_EV_BOUNDED_0 = prove
 (`!P. !i. i < 0 ==> P i`,
  REWRITE_TAC[LT]);;

(* ------------------------------------------------------------------------- *)
(* An evaluator for closed terms built from the ML-DSA functions, in the     *)
(* style of MLKEM_EVAL_CONV: arguments are evaluated first, except for       *)
(* let-terms, conditionals, the connectives (which are short-circuited) and  *)
(* bounded quantifiers, and then a handler for the head constant is applied. *)
(* Abstractions are only evaluated when applied.                             *)
(* ------------------------------------------------------------------------- *)

let mldsa_eval_verbose = ref true;;

let mldsa_report s =
  if !mldsa_eval_verbose then
    Printf.printf "[mldsa_eval %.1f] %s\n%!" (Sys.time()) s;;

let mev_T = `T` and mev_F = `F`;;

let mldsa_handlers = Hashtbl.create 200;;

let add_mldsa_handler name (conv:conv) =
  Hashtbl.replace mldsa_handlers name conv;;

let is_mev_byte tm =
  match tm with
    Comb(Const("word",_),n) -> is_numeral n
  | _ -> false;;

(* Explicit lists of bytes or integer literals; long lists already checked   *)
(* are remembered by physical identity.                                      *)

let is_mev_elt_list elt =
  let mev_list_memo = (Hashtbl.create 1000:(term,unit)Hashtbl.t) in
  let rec walk n tm =
    match tm with
      Const("NIL",_) -> true
    | Comb(Comb(Const("CONS",_),h),t) ->
        if n = 64 && Hashtbl.mem mev_list_memo tm then true
        else elt h && walk (n + 1) t
    | _ -> false in
  fun tm ->
    if Hashtbl.mem mev_list_memo tm then true
    else if walk 0 tm then
      (if length(dest_list tm) > 64 then Hashtbl.add mev_list_memo tm (); true)
    else false;;

let is_mev_bytelist = is_mev_elt_list is_mev_byte;;
let is_mev_intlist = is_mev_elt_list is_intconst;;

let is_mldsa_literal tm =
  is_numeral tm || is_intconst tm || tm = mev_T || tm = mev_F ||
  is_mev_byte tm || is_mev_bytelist tm || is_mev_intlist tm;;

let mldsa_pre_convs = ref ([]:conv list);;

let MEV_CONJ_F = TAUT `F /\ p <=> F` and MEV_CONJ_T = TAUT `T /\ p <=> p`
and MEV_DISJ_T = TAUT `T \/ p <=> T` and MEV_DISJ_F = TAUT `F \/ p <=> p`
and MEV_IMP_F = TAUT `(F ==> p) <=> T` and MEV_IMP_T = TAUT `(T ==> p) <=> p`
and MEV_NOT_T = TAUT `~T <=> F` and MEV_NOT_F = TAUT `~F <=> T`;;

let mev_nlt = `(<):num->num->bool`;;

let rec MLDSA_EVAL_CONV tm =
  if is_mldsa_literal tm then REFL tm else
  try tryfind (fun c -> c tm) (!mldsa_pre_convs) with Failure _ ->
  match tm with
    Comb(Comb(Const("/\\",_),p),q) ->
      MEV_BINCONN MEV_CONJ_F MEV_CONJ_T mev_F mev_T tm
  | Comb(Comb(Const("\\/",_),p),q) ->
      MEV_BINCONN MEV_DISJ_T MEV_DISJ_F mev_T mev_F tm
  | Comb(Comb(Const("==>",_),p),q) ->
      MEV_BINCONN MEV_IMP_F MEV_IMP_T mev_F mev_T tm
  | Comb(Const("~",_),p) ->
      (RAND_CONV MLDSA_EVAL_CONV THENC
       TRY_CONV(REWR_CONV MEV_NOT_T ORELSEC REWR_CONV MEV_NOT_F)) tm
  | Comb(Const("!",_),Abs(_,_)) -> MLDSA_FORALL_CONV tm
  | _ ->
  if is_let tm then
    let bs,_ = dest_let tm in
    let rec args n = if n = 0 then ALL_CONV
                     else RAND_CONV MLDSA_EVAL_CONV THENC
                          RATOR_CONV(args(n - 1)) in
    (args (length bs) THENC let_CONV THENC MLDSA_EVAL_CONV) tm
  else if is_cond tm then
    (RATOR_CONV(RATOR_CONV(RAND_CONV MLDSA_EVAL_CONV)) THENC
     GEN_REWRITE_CONV I [COND_CLAUSES] THENC MLDSA_EVAL_CONV) tm
  else
    let h,args = strip_comb tm in
    if args = [] then REFL tm else
    let th1 = MEV_ARGS_CONV tm in
    let tm1 = rand(concl th1) in
    if is_abs h then
      TRANS th1 ((funpow (length args - 1) RATOR_CONV BETA_CONV THENC
                  MLDSA_EVAL_CONV) tm1)
    else TRANS th1 (TRY_CONV MLDSA_HANDLE_CONV tm1)

and MEV_ARGS_CONV tm =
  match tm with
    Comb(f,x) -> MK_COMB(MEV_ARGS_CONV f,MLDSA_EVAL_CONV x)
  | _ -> REFL tm

(* p /\ q, p \/ q and p ==> q: evaluate p, and q only if needed.             *)

and MEV_BINCONN th_short th_long v_short v_long tm =
  let th = LAND_CONV MLDSA_EVAL_CONV tm in
  let r = rand(concl th) in
  let p = lhand r in
  if p = v_short then TRANS th (REWR_CONV th_short r)
  else if p = v_long then TRANS th ((REWR_CONV th_long THENC MLDSA_EVAL_CONV) r)
  else TRANS th (RAND_CONV MLDSA_EVAL_CONV r)

and MLDSA_HANDLE_CONV tm =
  let h,args = strip_comb tm in
  match h with
    Const(name,_) ->
      (try Hashtbl.find mldsa_handlers name
       with Not_found -> failwith "MLDSA_HANDLE_CONV") tm
  | _ -> failwith "MLDSA_HANDLE_CONV"

(* !i. i < n ==> P[i] for a numeral n: evaluate P[0], P[1], ... and stop at  *)
(* the first false one; !i j. i < m /\ j < n ==> P[i,j] is rewritten into    *)
(* this form first.                                                          *)

(* Evaluate the maximal closed subterms (once, before the instances).        *)

and MEV_HOIST_CONV tm =
  let ev t =
    if is_abs t || is_mldsa_literal t || not(frees t = []) then
      failwith "MEV_HOIST_CONV"
    else MLDSA_EVAL_CONV t in
  ONCE_DEPTH_CONV ev tm

and MLDSA_FORALL_CONV tm =
  let i,bod = dest_forall tm in
  match bod with
    Comb(Comb(Const("==>",_),Comb(Comb(Const("<",_),i'),n)),p)
      when i' = i && not(is_numeral n) && frees n = [] ->
      let eth = MLDSA_EVAL_CONV n in
      if not(is_numeral(rand(concl eth))) then failwith "MLDSA_FORALL_CONV" else
      let th = BINDER_CONV(LAND_CONV(RAND_CONV(K eth))) tm in
      TRANS th (MLDSA_FORALL_CONV(rand(concl th)))
  | Comb(Comb(Const("==>",_),Comb(Comb(Const("<",_),i'),n)),p)
      when i' = i && is_numeral n ->
      let hth = BINDER_CONV(RAND_CONV(MEV_HOIST_CONV)) tm in
      if not(rand(concl hth) = tm) then
        TRANS hth (MLDSA_FORALL_CONV(rand(concl hth))) else
      let nv = Num.int_of_num(dest_numeral n) in
      let lam = mk_abs(i,p) in
      let rec loop k th =
        if k = nv then
          EQT_INTRO(CONV_RULE(BINDER_CONV(RAND_CONV BETA_CONV)) th)
        else
          let ktm = mk_small_numeral k in
          let pk = vsubst [ktm,i] p in
          let eth = MLDSA_EVAL_CONV pk in
          if rand(concl eth) = mev_F then
            let sth = MP (SPEC ktm (ASSUME tm))
                        (EQT_ELIM(NUM_LT_CONV(mk_binop mev_nlt ktm n))) in
            EQF_INTRO(NOT_INTRO(DISCH tm (EQ_MP eth sth)))
          else
            let pth = EQ_MP (SYM(BETA_CONV(mk_comb(lam,ktm))))
                            (EQT_ELIM eth) in
            let th1 = MP (SPECL [lam; ktm] MLDSA_EV_BOUNDED_STEP)
                         (CONJ th pth) in
            loop (k + 1)
                 (CONV_RULE(BINDER_CONV(LAND_CONV(RAND_CONV NUM_SUC_CONV)))
                           th1) in
      loop 0 (SPEC lam MLDSA_EV_BOUNDED_0)
  | _ ->
      let th = if is_forall bod then
                 (REWRITE_CONV[GSYM IMP_IMP; RIGHT_FORALL_IMP_THM]) tm
               else MEV_BOUND_FIRST_CONV tm in
      if rand(concl th) = tm then failwith "MLDSA_FORALL_CONV"
      else TRANS th (MLDSA_EVAL_CONV(rand(concl th)))

(* Put an antecedent x < e (x not free in e) first, for !x. A1 ==> ... ==> P *)
(* and for ?x. C1 /\ ... /\ Cn, so that the bounded forms apply.             *)

and MEV_BOUND_FIRST_CONV tm =
  let x,bod = if is_forall tm then dest_forall tm else dest_exists tm in
  let isb t = match t with
                Comb(Comb(Const("<",_),x'),e) -> x' = x && not(vfree_in x e)
              | _ -> false in
  if is_forall tm then
    let ants,c = splitlist dest_imp bod in
    let ants = if length ants = 1 && is_conj(hd ants)
               then conjuncts(hd ants) else ants in
    let b = find isb ants in
    let rest = filter (fun t -> not(t = b)) ants in
    let bod' = mk_imp(b,itlist (curry mk_imp) rest c) in
    if bod' = bod then failwith "MEV_BOUND_FIRST_CONV" else
    BINDER_CONV(K(TAUT(mk_eq(bod,bod')))) tm
  else
    let cs = conjuncts bod in
    let b = find isb cs in
    let rest = filter (fun t -> not(t = b)) cs in
    if rest = [] then failwith "MEV_BOUND_FIRST_CONV" else
    let bod' = mk_conj(b,list_mk_conj rest) in
    if bod' = bod then failwith "MEV_BOUND_FIRST_CONV" else
    BINDER_CONV(K(CONJ_ACI_RULE(mk_eq(bod,bod')))) tm;;

(* ------------------------------------------------------------------------- *)
(* Handlers: arithmetic and equality of literals, booleans, words.           *)
(* ------------------------------------------------------------------------- *)

let MEV_ARITH_CONV =
  let pth = prove(`!n. num_of_int(&n) = n`, REWRITE_TAC[NUM_OF_INT_OF_NUM]) in
  fun tm ->
    let _,args = strip_comb tm in
    if not(forall is_mldsa_literal args) then failwith "MEV_ARITH_CONV"
    else (NUM_RED_CONV ORELSEC INT_RED_CONV ORELSEC REWR_CONV pth) tm;;

do_list (fun s -> add_mldsa_handler s MEV_ARITH_CONV)
 ["+"; "-"; "*"; "DIV"; "MOD"; "EXP"; "SUC"; "<"; "<="; ">"; ">=";
  "EVEN"; "ODD"; "int_add"; "int_sub"; "int_mul"; "int_neg"; "int_pow";
  "div"; "rem"; "int_lt"; "int_le"; "int_gt"; "int_ge"; "num_of_int";
  "int_abs"; "MIN"; "MAX"];;

add_mldsa_handler "="
 (fun tm -> let l,r = dest_eq tm in
            if is_mldsa_literal l && is_mldsa_literal r then LITERAL_EQ_CONV tm
            else failwith "=");;

add_mldsa_handler "bitval"
 (fun tm -> if rand tm = mev_T || rand tm = mev_F
            then REWRITE_CONV[BITVAL_CLAUSES] tm else failwith "bitval");;

let MEV_WORD_CONV tm =
  if forall is_mldsa_literal (snd(strip_comb tm)) then WORD_RED_CONV tm
  else failwith "MEV_WORD_CONV";;

add_mldsa_handler "word"
 (fun tm -> match tm with
              Comb(_,n) when is_numeral n -> CHANGED_CONV WORD_RED_CONV tm
            | _ -> failwith "word");;

add_mldsa_handler "val"
 (fun tm -> match tm with
              Comb(Const("val",Tyapp(_,[Tyapp(_,[n]);_])),
                   Comb(Const("word",_),k))
                when n = `:8` && is_numeral k &&
                     dest_numeral k </ Num.num_of_int 256 ->
                KECCAK_EV_VAL_BYTE.(Num.int_of_num(dest_numeral k))
            | _ -> MEV_WORD_CONV tm);;

do_list (fun s -> add_mldsa_handler s MEV_WORD_CONV) ["bit"];;

add_mldsa_handler "FST" (REWR_CONV FST);;
add_mldsa_handler "SND" (REWR_CONV SND);;

(* ------------------------------------------------------------------------- *)
(* Explicit lists: APPEND, LENGTH, EL (with tables built in linear time),    *)
(* list_of_seq, REPLICATE and slices.                                        *)
(* ------------------------------------------------------------------------- *)

let is_mev_list tm = is_mev_bytelist tm || is_mev_intlist tm;;

add_mldsa_handler "APPEND"
 (let conv = MEV_CACHED_CONV KECCAK_EV_APPEND_CONV in
  fun tm -> match tm with
              Comb(Comb(_,l),m) when is_mev_list l && is_mev_list m -> conv tm
            | _ -> failwith "APPEND");;

let MEV_LENGTH_CONV = MEV_CACHED_CONV LENGTH_CONV;;

add_mldsa_handler "LENGTH"
 (fun tm -> if is_mev_list(rand tm) then MEV_LENGTH_CONV tm
            else failwith "LENGTH");;

(* |- !n. EL (n + j) l = EL n tj for the tails tj of l, giving all the       *)
(* |- EL j l = xj in linear time.                                            *)

let MEV_EL_TABLE =
  let cache = mev_tbl_create 50 in
  let pth = prove
   (`!h:A t l j. (!n. EL (n + j) l = EL n (CONS h t))
                 ==> (!n. EL (n + (j + 1)) l = EL n t)`,
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n + 1`) THEN
    REWRITE_TAC[GSYM ADD1; EL; TL; ADD_CLAUSES])
  and pth0 = prove(`!l:A list. !n. EL (n + 0) l = EL n l`,
                   REWRITE_TAC[ADD_CLAUSES])
  and el0 = prove(`!h:A t. EL 0 (CONS h t) = h`, REWRITE_TAC[EL; HD])
  and zero = `0` and add0 = CONJUNCT1 ADD_CLAUSES in
  fun l ->
    try mev_tbl_find cache l with Not_found ->
    let ety = hd(snd(dest_type(type_of l))) in
    let pth = INST_TYPE [ety,aty] pth and pth0 = INST_TYPE [ety,aty] pth0
    and el0 = INST_TYPE [ety,aty] el0 in
    let len = length(dest_list l) in
    let res = Array.make len TRUTH in
    let rec loop j th t =
      if j < len then
        let h = lhand t and t' = rand t in
        let e = CONV_RULE(LAND_CONV(LAND_CONV(REWR_CONV add0)))
                  (SPEC zero th) in
        res.(j) <- TRANS e (SPECL [h;t'] el0);
        let th' = MP (SPECL [h;t';l;mk_small_numeral j] pth) th in
        let th'' = CONV_RULE(BINDER_CONV(LAND_CONV(LAND_CONV(RAND_CONV
                     NUM_ADD_CONV)))) th' in
        loop (j + 1) th'' t' in
    loop 0 (SPEC l pth0) l;
    mev_tbl_add cache l res; res;;

add_mldsa_handler "EL"
 (fun tm -> match tm with
              Comb(Comb(_,n),l) when is_numeral n && is_mev_list l ->
                let t = MEV_EL_TABLE l in
                let i = Num.int_of_num(dest_numeral n) in
                if i < Array.length t then t.(i) else failwith "EL"
            | _ -> failwith "EL");;

add_mldsa_handler "REPLICATE"
 (fun tm -> if forall is_mldsa_literal (snd(strip_comb tm))
            then REPLICATE_CONV tm else failwith "REPLICATE");;

(* list_of_seq f n: expand, then evaluate the elements. For f = shake128 m   *)
(* or shake256 m the elements are bytes of the stream.                       *)

add_mldsa_handler "list_of_seq"
 (fun tm -> match tm with
              Comb(Comb(_,f),n) when is_numeral n ->
                (LIST_OF_SEQ_CONV THENC LIST_CONV MLDSA_EVAL_CONV) tm
            | _ -> failwith "list_of_seq");;

do_list (fun s ->
  add_mldsa_handler s
   (fun tm -> match tm with
                Comb(Comb(f,m),i) when is_mev_bytelist m && is_numeral i ->
                  KECCAK_EV_SHAKE_BYTE f m (Num.int_of_num(dest_numeral i))
              | _ -> failwith s))
 ["shake128"; "shake256"];;

add_mldsa_handler "mldsa_h"
 (MEV_CACHED_CONV(REWR_CONV mldsa_h THENC MLDSA_EVAL_CONV));;

add_mldsa_handler "mldsa_slice"
 (let conv = MEV_CACHED_CONV(REWR_CONV mldsa_slice THENC MLDSA_EVAL_CONV) in
  fun tm -> match strip_comb tm with
              _,[a;n;l] when is_numeral a && is_numeral n && is_mev_list l ->
                conv tm
            | _ -> failwith "mldsa_slice");;

add_mldsa_handler "num_of_bytelist"
 (fun tm -> if is_mev_bytelist(rand tm) then NUM_OF_BYTELIST_CONV tm
            else failwith "num_of_bytelist");;

add_mldsa_handler "bytelist_of_num"
 (fun tm -> if forall is_numeral (snd(strip_comb tm))
            then BYTELIST_OF_NUM_CONV tm else failwith "bytelist_of_num");;

add_mldsa_handler "mldsa_bitlen" MLDSA_BITLEN_CONV;;

(* ------------------------------------------------------------------------- *)
(* The rounding functions and Z_q, by their definitions.                     *)
(* ------------------------------------------------------------------------- *)

let MEV_DEF_HANDLER name def =
  let n = length(snd(strip_comb(lhs(snd(strip_forall(concl def)))))) in
  let conv = MEV_CACHED_CONV(REWR_CONV def THENC MLDSA_EVAL_CONV) in
  add_mldsa_handler name
   (fun tm -> let _,args = strip_comb tm in
              if length args = n && forall is_mldsa_literal args then conv tm
              else failwith name);;

MEV_DEF_HANDLER "mldsa_modpm" mldsa_modpm;;
MEV_DEF_HANDLER "mldsa_power2round" mldsa_power2round;;
MEV_DEF_HANDLER "mldsa_decompose" mldsa_decompose;;
MEV_DEF_HANDLER "mldsa_highbits" mldsa_highbits;;
MEV_DEF_HANDLER "mldsa_lowbits" mldsa_lowbits;;
MEV_DEF_HANDLER "mldsa_makehint" mldsa_makehint;;
MEV_DEF_HANDLER "mldsa_usehint" mldsa_usehint;;

let MLDSA_EV_ZQ_CLAUSES = prove
 (`ring_0 mldsa_zq = &0 /\ ring_1 mldsa_zq = &1 /\
   (!x. ring_neg mldsa_zq x = --x rem &8380417) /\
   (!x y. ring_add mldsa_zq x y = (x + y) rem &8380417) /\
   (!x y. ring_sub mldsa_zq x y = (x - y) rem &8380417) /\
   (!x y. ring_mul mldsa_zq x y = (x * y) rem &8380417) /\
   (!x n. ring_pow mldsa_zq x n = x pow n rem &8380417) /\
   (!x. x IN ring_carrier mldsa_zq <=> &0 <= x /\ x < &8380417)`,
  REWRITE_TAC[MLDSA_ZQ; IN_ELIM_THM]);;

let mev_zq = `mldsa_zq` and mev_rq = `mldsa_rq`;;

let MEV_ZQ_CONV =
  GEN_REWRITE_CONV I [MLDSA_EV_ZQ_CLAUSES] THENC MLDSA_EVAL_CONV;;

do_list (fun (s,n) ->
  add_mldsa_handler s
   (fun tm -> let _,args = strip_comb tm in
              if length args = n && hd args = mev_zq &&
                 forall is_mldsa_literal (tl args)
              then MEV_ZQ_CONV tm else failwith s))
 ["ring_0",1; "ring_1",1; "ring_neg",2; "ring_add",3; "ring_sub",3;
  "ring_mul",3; "ring_pow",3];;

(* ring_sum mldsa_zq {j | j < n} f and ring_sum mldsa_zq (m..n) f.           *)

let MEV_RING_SUM_CONV =
  let pth0,pth1 = CONJ_PAIR RING_SUM_CLAUSES_NUMSEG in
  let rec conv tm =
    match tm with
      Comb(Comb(Comb(Const("ring_sum",_),r),Comb(Comb(Const("..",_),m),n)),f) ->
        if n = kev_0 then (REWR_CONV pth0 THENC MLDSA_EVAL_CONV) tm else
        (RATOR_CONV(RAND_CONV(RAND_CONV num_CONV)) THENC REWR_CONV pth1 THENC
         MLDSA_EVAL_CONV) tm
    | _ -> failwith "MEV_RING_SUM_CONV" in
  conv;;

let MLDSA_EV_ZQ_DOT = prove
 (`!n x y. ring_sum mldsa_zq {j | j < n} (\j. ring_mul mldsa_zq (x j) (y j)) =
           isum {j | j < n} (\j. x j * y j) rem &8380417`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MLDSA_ZQ] THEN
  SIMP_TAC[MLDSA_ZQ_RING_SUM; FINITE_NUMSEG_LT]);;

add_mldsa_handler "isum"
 (fun tm ->
    match tm with
      Comb(Comb(Const("isum",_),s),f) ->
        if is_comb s && is_comb(rator s) && is_const(rator(rator s)) &&
           fst(dest_const(rator(rator s))) = ".."
        then (EXPAND_ISUM_CONV THENC MLDSA_EVAL_CONV) tm
        else (RATOR_CONV(RAND_CONV NUMSEG_LT_CONV) THENC EXPAND_ISUM_CONV THENC
              MLDSA_EVAL_CONV) tm
    | _ -> failwith "isum");;

add_mldsa_handler "ring_sum"
 (fun tm ->
    try (PART_MATCH lhs MLDSA_EV_ZQ_DOT THENC MLDSA_EVAL_CONV) tm
    with Failure _ ->
    match tm with
      Comb(Comb(Comb(Const("ring_sum",_),r),s),f) when r = mev_zq ->
        if is_comb s && is_comb(rator s) && is_const(rator(rator s)) &&
           fst(dest_const(rator(rator s))) = ".."
        then MEV_RING_SUM_CONV tm
        else (RATOR_CONV(RAND_CONV NUMSEG_LT_CONV) THENC MEV_RING_SUM_CONV) tm
    | _ -> failwith "ring_sum");;

let mldsa_rq_carrier_ref = ref (fun (tm:term) -> (failwith "RQ_CARRIER":thm));;


add_mldsa_handler "IN"
 (fun tm ->
    match tm with
      Comb(Comb(Const("IN",_),x),Comb(Const("ring_carrier",_),r))
        when r = mev_zq && is_mldsa_literal x -> MEV_ZQ_CONV tm
    | Comb(Comb(Const("IN",_),p),Comb(Const("ring_carrier",_),r))
        when r = mev_rq -> EQT_INTRO(!mldsa_rq_carrier_ref p)
    | _ -> failwith "IN");;

(* ------------------------------------------------------------------------- *)
(* The rejection samplers with their candidate values as named functions,    *)
(* and the i-th accepted candidate of a predicate.                           *)
(* ------------------------------------------------------------------------- *)

let mldsa_ev_rej_coeff = new_definition
 `mldsa_ev_rej_coeff rho j =
    val(shake128 rho (3 * j)) + 256 * val(shake128 rho (3 * j + 1)) +
    65536 * (val(shake128 rho (3 * j + 2)) MOD 128)`;;

let mldsa_ev_nib = new_definition
 `mldsa_ev_nib rho t =
    (val(shake256 rho (t DIV 2)) DIV 16 EXP (t MOD 2)) MOD 16`;;

let mldsa_ev_bok = new_definition
 `mldsa_ev_bok eta rho t <=>
    if eta = 2 then mldsa_ev_nib rho t < 15 else mldsa_ev_nib rho t < 9`;;

let mldsa_ev_bval = new_definition
 `mldsa_ev_bval eta rho t =
    if eta = 2 then &2 - &(mldsa_ev_nib rho t MOD 5)
    else &4 - &(mldsa_ev_nib rho t):int`;;

let MLDSA_EV_REJ_NTT_POLY = prove
 (`!rho. mldsa_rej_ntt_poly rho =
         \i. &(mldsa_ev_rej_coeff rho
                (@j. mldsa_ev_rej_coeff rho j < 8380417 /\
                     CARD {j' | j' < j /\ mldsa_ev_rej_coeff rho j' < 8380417} =
                     i))`,
  REWRITE_TAC[mldsa_rej_ntt_poly; mldsa_ev_rej_coeff] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

let MLDSA_EV_REJ_BOUNDED_POLY = prove
 (`!eta rho.
        mldsa_rej_bounded_poly eta rho =
        mldsa_poly
         (\i. mldsa_ev_bval eta rho
               (@t. mldsa_ev_bok eta rho t /\
                    CARD {t' | t' < t /\ mldsa_ev_bok eta rho t'} = i))`,
  REWRITE_TAC[mldsa_rej_bounded_poly; mldsa_ev_bval; mldsa_ev_bok;
              mldsa_ev_nib] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

let MLDSA_EV_SELECT = prove
 (`!P:num->bool i j.
        P j /\ CARD {j' | j' < j /\ P j'} = i
        ==> (@j. P j /\ CARD {j' | j' < j /\ P j'} = i) = j`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `y:num` THEN EQ_TAC THENL
   [ALL_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b. a < b /\ P a
          ==> CARD {j' | j' < a /\ P j'} < CARD {j' | j' < b /\ P j'}`
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

(* The hint positions: the p < N with h p and t hints before is unique.      *)

let MLDSA_EV_HINT_SELECT = prove
 (`!h N t p.
        p < N /\ h p /\ mldsa_hint_count h p = t
        ==> (@p. p < N /\ h p /\ mldsa_hint_count h p = t) = p`,
  REWRITE_TAC[mldsa_hint_count] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `y:num` THEN EQ_TAC THENL
   [ALL_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b. a < b /\ h a
          ==> CARD {j' | j' < a /\ h j'} < CARD {j' | j' < b /\ h j'}`
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

let MLDSA_EV_HINT_NONE = prove
 (`!h N t. mldsa_hint_count h N <= t
           ==> ~(?p. p < N /\ h p /\ mldsa_hint_count h p = t)`,
  REWRITE_TAC[mldsa_hint_count] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `CARD {j' | j' < p /\ h j'} < CARD {j' | j' < N /\ h j'}`
  MP_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  MATCH_MP_TAC CARD_PSUBSET THEN CONJ_TAC THENL
   [REWRITE_TAC[PSUBSET; SUBSET; EXTENSION; IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[LT_TRANS];
      DISCH_THEN(MP_TAC o SPEC `p:num`) THEN ASM_REWRITE_TAC[LT_REFL]];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j:num | j < N}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]]);;

(* The signing loop, from the first attempt that is not rejected.            *)

let MLDSA_EV_SIGN_LOOP = prove
 (`!att:num->A option n x.
        att n = SOME x /\ (!m. m < n ==> att m = NONE)
        ==> (if ?n. ~(att n = NONE) then att(minimal n. ~(att n = NONE))
             else NONE) = SOME x`,
  let sn = prove(`!x:A. ~(SOME x = NONE)`,
                 ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
                 REWRITE_TAC[option_DISTINCT]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(minimal n. ~((att:num->A option) n = NONE)) = n`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MINIMAL_UNIQUE THEN ASM_SIMP_TAC[sn];
    SUBGOAL_THEN `?n. ~((att:num->A option) n = NONE)`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
    EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[sn]]);;

let MLDSA_EV_FIELD_GROUP = prove
 (`!c l1 l2:byte list i.
        LENGTH l1 = c
        ==> mldsa_field c (APPEND l1 l2) (i + 8) = mldsa_field c l2 i`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[mldsa_field; KECCAK_EV_NUM_OF_BYTELIST_APPEND] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `c * (i + 8) = 8 * c + c * i`; EXP_ADD;
              GSYM DIV_DIV] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPEC `l1:byte list` KECCAK_EV_NUM_OF_BYTELIST_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`2 EXP (8 * c)`,`p:num`) THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `num_of_bytelist l1` THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let MLDSA_EV_FIELD_FIRST = prove
 (`!c l1 l2:byte list i.
        LENGTH l1 = c /\ i < 8
        ==> mldsa_field c (APPEND l1 l2) i = mldsa_field c l1 i`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[mldsa_field; KECCAK_EV_NUM_OF_BYTELIST_APPEND] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `2 EXP (8 * c) = 2 EXP (c * i) * 2 EXP c * 2 EXP (c * (7 - i))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; GSYM(CONJUNCT2 MULT_CLAUSES)] THEN
    REWRITE_TAC[ARITH_RULE `8 * c = c * 8`] THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MULT_ASSOC] THEN
  SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ;
           ONCE_REWRITE_RULE[ADD_SYM] DIV_MULT_ADD] THEN
  MATCH_ACCEPT_TAC(MESON[ADD_SYM; MULT_SYM; MOD_MULT_ADD]
   `!a n x. (a + n * x) MOD n = a MOD n`));;

(* ------------------------------------------------------------------------- *)
(* |- !i. i < n ==> P[i] from the instances |- P[k] for k < n, where lam is  *)
(* \i. P[i] and inst k gives |- P[k].                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_EV_BOUNDED_RULE lam n (inst:int->thm) =
  let rec loop k th =
    if k = n then CONV_RULE(BINDER_CONV(RAND_CONV BETA_CONV)) th else
    let ktm = mk_small_numeral k in
    let pth = EQ_MP (SYM(BETA_CONV(mk_comb(lam,ktm)))) (inst k) in
    let th1 = MP (SPECL [lam; ktm] MLDSA_EV_BOUNDED_STEP) (CONJ th pth) in
    loop (k + 1)
     (CONV_RULE(BINDER_CONV(LAND_CONV(RAND_CONV NUM_SUC_CONV))) th1) in
  loop 0 (SPEC lam MLDSA_EV_BOUNDED_0);;

let MEV_INT_LITERAL_EQ th = rand(concl th);;

(* ------------------------------------------------------------------------- *)
(* Fields: |- mldsa_field c b i = &v for all i < 8 * LENGTH b DIV c, for an  *)
(* explicit byte list b, a group of 8 fields (c bytes) at a time.            *)
(* ------------------------------------------------------------------------- *)

let MLDSA_EV_FIELD_TABLE =
  let cache = mev_tbl_create 100 and fld = `mldsa_field` in
  let th0 = prove(`!c b i. mldsa_field c b (i + 0) = mldsa_field c b i`,
                  REWRITE_TAC[ADD_CLAUSES]) in
  let grp = SPEC_ALL MLDSA_EV_FIELD_GROUP
  and fst = SPEC_ALL MLDSA_EV_FIELD_FIRST in
  let cv = `c:num` and l1v = `l1:byte list` and l2v = `l2:byte list`
  and iv = `i:num` and n8 = `8` and plus = `(+):num->num->num`
  and lt = `(<):num->num->bool` in
  let lt8 = Array.init 8 (fun r ->
    EQT_ELIM(NUM_LT_CONV(mk_binop lt (mk_small_numeral r) n8))) in
  fun c b ->
    let ctm = mk_small_numeral c in
    let key = mk_comb(mk_comb(fld,ctm),b) in
    try mev_tbl_find cache key with Not_found ->
    let len = length(dest_list b) in
    let ng = len / c in
    let res = Array.make (8 * ng) TRUTH in
    let rec loop g th t =
      (* th : |- !i. mldsa_field c b (i + N) = mldsa_field c t i, N = 8g *)
      if g < ng then
        let sth = KECCAK_EV_SPLIT_LIST c t in
        let chunk = lhand(lhand(concl sth)) and t' = rand(lhand(concl sth)) in
        let lth = LENGTH_CONV(mk_comb(kev_lenb,chunk)) in
        let nth = NUM_OF_BYTELIST_CONV(mk_comb(`num_of_bytelist`,chunk)) in
        let fth = MP (INST [ctm,cv; chunk,l1v; t',l2v] (SPEC_ALL grp)) lth in
        for r = 0 to 7 do
          let rtm = mk_small_numeral r in
          let e1 = CONV_RULE(LAND_CONV(RAND_CONV NUM_ADD_CONV)) (SPEC rtm th) in
          let e2 = CONV_RULE(RAND_CONV(LAND_CONV(K(SYM sth))))
                     (REFL(rand(concl e1))) in
          let e2' = TRANS e2 (MP (INST [ctm,cv; chunk,l1v; t',l2v; rtm,iv] fst)
                                 (CONJ lth lt8.(r))) in
          let e3 = (REWR_CONV mldsa_field THENC
                    RAND_CONV(LAND_CONV(LAND_CONV(K nth))) THENC
                    RAND_CONV NUM_REDUCE_CONV) (rand(concl e2')) in
          res.(8 * g + r) <- TRANS e1 (TRANS e2' e3)
        done;
        let th1 = SPEC (mk_binop plus iv n8) th in
        let th2 = CONV_RULE(RAND_CONV(LAND_CONV(K(SYM sth)) THENC K fth)) th1 in
        let th3 = CONV_RULE(LAND_CONV(RAND_CONV(REWR_CONV(GSYM ADD_ASSOC) THENC
                    RAND_CONV NUM_ADD_CONV))) th2 in
        loop (g + 1) (GEN iv th3) t'
      in
    loop 0 (SPECL [ctm; b] th0) b;
    mev_tbl_add cache key res; res;;

add_mldsa_handler "mldsa_field"
 (fun tm -> match strip_comb tm with
              _,[c;b;i] when is_numeral c && is_mev_bytelist b &&
                             is_numeral i ->
                let t =
                  MLDSA_EV_FIELD_TABLE (Num.int_of_num(dest_numeral c)) b in
                let k = Num.int_of_num(dest_numeral i) in
                if k < Array.length t then t.(k) else failwith "mldsa_field"
            | _ -> failwith "mldsa_field");;

(* ------------------------------------------------------------------------- *)
(* Encoding: compute the bytes, and prove them through their fields.         *)
(* ------------------------------------------------------------------------- *)

let mev_bytes_of_num len n =
  let rec go k n =
    if k = 0 then [] else
    let b = mod_num n (Num.num_of_int 256) in
    mk_comb(`word:num->byte`,mk_numeral b)::
    go (k - 1) (quo_num n (Num.num_of_int 256)) in
  mk_list(go len n,`:byte`);;

let MLDSA_EV_ENCODE_CONV =
  let eqrem = SPEC_ALL MLDSA_ENCODE_EQ_REM
  and efield = SPEC_ALL MLDSA_ENCODE_FIELD in
  let cv = `c:num` and nv = `n:num` and fv = `f:num->int` and gv = `g:num->int`
  and bv = `b:byte list` and iv = `i:num` and fld = `mldsa_field`
  and remc = `(rem):int->int->int` and powc = `(pow):int->num->int`
  and two = `&2:int` and divc = `(divides):num->num->bool` and n8 = `8`
  and mulc = `( * ):num->num->num` and divn = `DIV` in
  fun tm ->
    match strip_comb tm with
      _,[c;n;f] when is_numeral c && is_numeral n ->
        let ci = Num.int_of_num(dest_numeral c)
        and ni = Num.int_of_num(dest_numeral n) in
        mldsa_report(Printf.sprintf "encode %d x %d" ci ni);
        let vals = Array.init ni (fun i ->
          MLDSA_EVAL_CONV(mk_comb(f,mk_small_numeral i))) in
        let p2 = power_num (Num.num_of_int 2) (Num.num_of_int ci) in
        let total = ref (Num.num_of_int 0) in
        for i = ni - 1 downto 0 do
          let v = dest_intconst(rand(concl vals.(i))) in
          let w = mod_num (add_num (mod_num v p2) p2) p2 in
          total := add_num (mult_num !total p2) w
        done;
        let b = mev_bytes_of_num ((ci * ni) / 8) !total in
        let ft = MLDSA_EV_FIELD_TABLE ci b in
        let g = mk_comb(mk_comb(fld,c),b) in
        let pc = mk_binop powc two c in
        let lam = mk_abs(iv,mk_eq(mk_binop remc (mk_comb(f,iv)) pc,
                                  mk_binop remc (mk_comb(g,iv)) pc)) in
        let inst k =
          let tm = rand(concl(BETA_CONV(mk_comb(lam,mk_small_numeral k)))) in
          let l = (LAND_CONV(K vals.(k)) THENC INT_REDUCE_CONV) (lhs tm) in
          let r = (LAND_CONV(K ft.(k)) THENC INT_REDUCE_CONV) (rhs tm) in
          TRANS l (SYM r) in
        let ath = MLDSA_EV_BOUNDED_RULE lam ni inst in
        let th1 = MP (INST [c,cv; n,nv; f,fv; g,gv] eqrem) ath in
        let cn = mk_binop mulc c n in
        let dth = EQT_ELIM((RAND_CONV NUM_MULT_CONV THENC DIVIDES_CONV)
                    (mk_comb(mk_comb(divc,n8),cn))) in
        let lth = TRANS (LENGTH_CONV(mk_comb(kev_lenb,b)))
                        (SYM(NUM_REDUCE_CONV(mk_binop divn cn n8))) in
        let th2 = MP (INST [c,cv; n,nv; b,bv] efield) (CONJ dth lth) in
        mldsa_report "encode done";
        TRANS th1 th2
    | _ -> failwith "MLDSA_EV_ENCODE_CONV";;

add_mldsa_handler "mldsa_encode" MLDSA_EV_ENCODE_CONV;;

(* ------------------------------------------------------------------------- *)
(* Selection of the i-th accepted candidate, counting, minimal and exists.   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_EV_CARD_STEP = prove
 (`!P n m. n + 1 = m
           ==> CARD {j | j < m /\ P j} =
               CARD {j | j < n /\ P j} + (if P n then 1 else 0)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM ADD1; CARD_LT_SUC]);;

let MLDSA_EV_CARD_0 = prove
 (`!P. CARD {j | j < 0 /\ P j} = 0`,
  REWRITE_TAC[LT; EMPTY_GSPEC; CARD_CLAUSES]);;

(* Counting tables for a predicate p (a lambda or a function term): for      *)
(* k = 0, 1, ..., |- CARD {j | j < k /\ P j} = c with P j in the form given  *)
(* by beta (if p is a lambda pj) or as p j, and |- P k <=> T or F.           *)

let mev_count_tables = mev_tbl_create 100;;
let mev_count_tables_beta = mev_tbl_create 100;;

(* With isbeta, p is \j. P[j] and the sets have the body P[j]; otherwise     *)
(* they have p j itself (which may be a beta-redex).                         *)

let MLDSA_EV_COUNT =
  let plus = `(+):num->num->num` and one = `1` in
  fun isbeta p ->
    let tbl = if isbeta then mev_count_tables_beta else mev_count_tables in
    try mev_tbl_find tbl p with Not_found ->
    let beta = if isbeta then BETA_RULE else I in
    let step = beta(ISPEC p MLDSA_EV_CARD_STEP)
    and th0 = beta(ISPEC p MLDSA_EV_CARD_0) in
    let pinst k = if isbeta then vsubst [k,bndvar p] (body p)
                  else mk_comb(p,k) in
    let counts = ref [|th0|] and preds = ref [||] in
    let rec get k =
      (* ensure counts up to k *)
      let n = Array.length !counts in
      if k < n then () else
      let ktm = mk_small_numeral (n - 1) in
      let pth = MLDSA_EVAL_CONV(pinst ktm) in
      let cth = (!counts).(n - 1) in
      let k1 = NUM_ADD_CONV(mk_binop plus ktm one) in
      let th1 = MP (SPECL [ktm; rand(concl k1)] step) k1 in
      let th2 = CONV_RULE(RAND_CONV(LAND_CONV(K cth) THENC
                  RAND_CONV(RATOR_CONV(LAND_CONV(K pth)) THENC
                            GEN_REWRITE_CONV I [COND_CLAUSES]) THENC
                  NUM_ADD_CONV)) th1 in
      counts := Array.append !counts [|th2|];
      preds := Array.append !preds [|pth|];
      get k in
    let r = (get,counts,preds) in
    mev_tbl_add tbl p r; r;;

(* @j. P j /\ CARD {j' | j' < j /\ P j'} = i, for the i-th accepted j.       *)

let MLDSA_EV_SELECT_CONV =
  let tables = mev_tbl_create 100 in
  fun tm ->
    match tm with
      Comb(Const("@",_),Abs(j,Comb(Comb(Const("/\\",_),pj),
                                   Comb(Comb(Const("=",_),card),itm))))
        when is_numeral itm ->
        let p = mk_abs(j,pj) in
        let i = Num.int_of_num(dest_numeral itm) in
        let get,counts,preds = MLDSA_EV_COUNT true p in
        let sel = BETA_RULE(ISPEC p MLDSA_EV_SELECT) in
        let found =
          try mev_tbl_find tables p with Not_found ->
          let f = Hashtbl.create 300 in mev_tbl_add tables p f; f in
        let rec scan k =
          if Hashtbl.mem found i then Hashtbl.find found i else
          if k > 100000 then failwith "MLDSA_EV_SELECT_CONV: too far" else
          (get (k + 1);
           let pth = (!preds).(k) and cth = (!counts).(k) in
           (if rand(concl pth) = mev_T then
              let c = rand(concl cth) in
              let ci = Num.int_of_num(dest_numeral c) in
              if not(Hashtbl.mem found ci) then
                Hashtbl.add found ci
                 (MP (SPECL [c; mk_small_numeral k] sel)
                     (CONJ (EQT_ELIM pth) cth)));
           scan (k + 1)) in
        let th = scan 0 in
        if lhand(concl th) = tm then th
        else TRANS (ALPHA tm (lhand(concl th))) th
    | _ -> failwith "MLDSA_EV_SELECT_CONV";;

(* @p. p < N /\ h p /\ mldsa_hint_count h p = t, the position of the hint    *)
(* number t, from the counting table of h.                                   *)

let MLDSA_EV_HINT_SELECT_CONV =
  let lt = `(<):num->num->bool` and hcount = `mldsa_hint_count` in
  fun tm ->
    match tm with
      Comb(Const("@",_),Abs(p,Comb(Comb(Const("/\\",_),
            Comb(Comb(Const("<",_),p1),n)),
          Comb(Comb(Const("/\\",_),Comb(h,p2)),
            Comb(Comb(Const("=",_),
              Comb(Comb(Const("mldsa_hint_count",_),h'),p3)),t)))))
        when p1 = p && p2 = p && p3 = p && h = h' && is_numeral t &&
             not(vfree_in p h) ->
        let get,counts,preds = MLDSA_EV_COUNT false h in
        let nv = Num.int_of_num(dest_numeral(rand(concl(MLDSA_EVAL_CONV n)))) in
        get nv;
        let ti = Num.int_of_num(dest_numeral t) in
        let rec find k =
          if k >= nv then failwith "MLDSA_EV_HINT_SELECT_CONV" else
          if rand(concl (!preds).(k)) = mev_T &&
             Num.int_of_num(dest_numeral(rand(concl (!counts).(k)))) = ti
          then k else find (k + 1) in
        let k = find 0 in
        let ktm = mk_small_numeral k in
        let lth = EQT_ELIM(MLDSA_EVAL_CONV(mk_binop lt ktm n)) in
        let hth = EQT_ELIM (!preds).(k) in
        let c1 = REWR_CONV mldsa_hint_count (list_mk_comb(hcount,[h; ktm])) in
        let cth = (!counts).(k) in
        let cth' = TRANS c1
                    (if lhand(concl cth) = rand(concl c1) then cth
                     else TRANS (ALPHA (rand(concl c1)) (lhand(concl cth)))
                                cth) in
        let th = MP (SPECL [h; n; t; ktm] MLDSA_EV_HINT_SELECT)
                    (CONJ lth (CONJ hth cth')) in
        if lhand(concl th) = tm then th
        else TRANS (ALPHA tm (lhand(concl th))) th
    | _ -> failwith "MLDSA_EV_HINT_SELECT_CONV";;

add_mldsa_handler "@"
 (fun tm -> try MLDSA_EV_SELECT_CONV tm with Failure _ ->
            try MLDSA_EV_HINT_SELECT_CONV tm with Failure s ->
            (mldsa_report("select not evaluated: "^s); failwith s));;

(* CARD {j | j < n /\ P j} by the counting tables.                           *)

let mev_dest_bounded_set tm =
  match tm with
    Comb(Const("GSPEC",_),Abs(x,Comb(Const("?",_),
      Abs(v,Comb(Comb(Comb(Const("SETSPEC",_),x'),cnd),v'))))) when
      x' = x && v' = v ->
      (match cnd with
         Comb(Comb(Const("/\\",_),Comb(Comb(Const("<",_),v1),n)),q)
           when v1 = v -> v,n,q
       | _ -> failwith "mev_dest_bounded_set")
  | _ -> failwith "mev_dest_bounded_set";;

add_mldsa_handler "CARD"
 (fun tm ->
    let v,n,q = mev_dest_bounded_set (rand tm) in
    if not(is_numeral n) then failwith "CARD" else
    let isbeta,p = match q with
                     Comb(h,v2) when v2 = v && not(vfree_in v h) -> false,h
                   | _ -> true,mk_abs(v,q) in
    let get,counts,_ = MLDSA_EV_COUNT isbeta p in
    let k = Num.int_of_num(dest_numeral n) in
    get k;
    let th = (!counts).(k) in
    if lhand(concl th) = tm then th
    else TRANS (ALPHA tm (lhand(concl th))) th);;

(* (minimal) P = n for the least n with P n.                                 *)

add_mldsa_handler "minimal"
 (fun tm ->
    match tm with
      Comb(Const("minimal",_),p) ->
        let rec search k acc =
          if k > 100000 then failwith "minimal: too far" else
          let ktm = mk_small_numeral k in
          let pk = MLDSA_EVAL_CONV(mk_comb(p,ktm)) in
          if rand(concl pk) = mev_T then k,pk,rev acc
          else if rand(concl pk) = mev_F then search (k + 1) (pk::acc)
          else failwith "minimal: not evaluated" in
        let n,pn,nots = search 0 [] in
        let nots = Array.of_list nots in
        let m = genvar `:num` in
        let lam = mk_abs(m,mk_neg(mk_comb(p,m))) in
        let ath = MLDSA_EV_BOUNDED_RULE lam n (fun k -> EQF_ELIM nots.(k)) in
        MP (ISPECL [p; mk_small_numeral n] MINIMAL_UNIQUE)
           (CONJ (EQT_ELIM pn) ath)
    | _ -> failwith "minimal");;

(* ?x. P x: a witness by search; ?x. x < e /\ R x is refuted if there is     *)
(* none below e.                                                             *)

let MLDSA_EV_NOT_EXISTS_BOUNDED = prove
 (`!R n. (!x. x < n ==> ~R x) ==> ((?x. x < n /\ R x) <=> F)`,
  MESON_TAC[]);;

let rec MEV_EXISTS_CONV hoisted tm =
  match tm with
    Comb(Const("?",_),Abs(x,bod)) ->
      (match bod with
         Comb(Comb(Const("/\\",_),Comb(Comb(Const("<",_),x'),e)),r)
           when x' = x && not(vfree_in x e) ->
           if not hoisted then
             let hth = BINDER_CONV(RAND_CONV MEV_HOIST_CONV) tm in
             TRANS hth (MEV_EXISTS_CONV true (rand(concl hth)))
           else
           let eth = MLDSA_EVAL_CONV e in
           let nv = Num.int_of_num(dest_numeral(rand(concl eth))) in
           let rec search k acc =
             if k = nv then None,rev acc else
             let ktm = mk_small_numeral k in
             let rk = MLDSA_EVAL_CONV(vsubst [ktm,x] r) in
             if rand(concl rk) = mev_T then Some(ktm,rk),[]
             else if rand(concl rk) = mev_F then search (k + 1) (rk::acc)
             else failwith "?: not evaluated" in
           (match search 0 [] with
              Some(ktm,rk),_ ->
                let lt =
                  EQT_ELIM(MLDSA_EVAL_CONV(vsubst [ktm,x] (lhand bod))) in
                EQT_INTRO(EXISTS (tm,ktm) (CONJ lt (EQT_ELIM rk)))
            | None,nots ->
                let nots = Array.of_list nots in
                let rl = mk_abs(x,r) in
                let lam = mk_abs(x,mk_neg(mk_comb(rl,x))) in
                let ath = MLDSA_EV_BOUNDED_RULE lam nv
                  (fun k -> EQF_ELIM(TRANS (BETA_CONV(mk_comb(rl,
                                                 mk_small_numeral k)))
                                           nots.(k))) in
                let th1 = MP (ISPECL [rl; rand(concl eth)]
                                     MLDSA_EV_NOT_EXISTS_BOUNDED) ath in
                let th2 = CONV_RULE(LAND_CONV(BINDER_CONV
                            (LAND_CONV(RAND_CONV(K(SYM eth))) THENC
                             RAND_CONV BETA_CONV))) th1 in
                if lhand(concl th2) = tm then th2
                else TRANS (ALPHA tm (lhand(concl th2))) th2)
       | _ ->
           try let th = MEV_BOUND_FIRST_CONV tm in
               TRANS th (MEV_EXISTS_CONV false (rand(concl th)))
           with Failure _ ->
           let rec search k =
             if k > 1000 then failwith "?: no witness" else
             let ktm = mk_small_numeral k in
             let bk = MLDSA_EVAL_CONV(vsubst [ktm,x] bod) in
             if rand(concl bk) = mev_T then
               EQT_INTRO(EXISTS (tm,ktm) (EQT_ELIM bk))
             else if rand(concl bk) = mev_F then search (k + 1)
             else failwith "?: not evaluated" in
           search 0)
  | _ -> failwith "MEV_EXISTS_CONV";;

add_mldsa_handler "?" (MEV_EXISTS_CONV false);;

(* ------------------------------------------------------------------------- *)
(* Polynomials: for an element p of R_q given by a term, the carrier         *)
(* theorem and the 256 coefficients |- coeff k p = &c (0 <= c < q), and the  *)
(* NTT |- mldsa_ntt p k = &c computed by the FFT. mldsa_ntt_inv a is found   *)
(* by computing the result and checking its NTT (MLDSA_NTT_INV_UNIQUE).      *)
(* ------------------------------------------------------------------------- *)

let mev_in_rq = `(IN):((1->num)->int)->(((1->num)->int)->bool)->bool`
and mev_carrier_rq = `ring_carrier mldsa_rq`
and mev_mldsa_poly = `mldsa_poly`
and mev_el_int = `EL:num->int list->int`
and mev_coeff = `coeff:num->((1->num)->int)->int`
and mev_list_of_seq_int = `list_of_seq:(num->int)->num->int list`
and mev_n256 = `256`;;

let mldsa_inv_ntt_ocaml v =
  Array.init 256 (fun j ->
    let s = ref 0 in
    for k = 0 to 255 do
      let e = ((2 * mldsa_br8 k + 1) * j) mod 512 in
      let z = mldsa_zeta_pow ((512 - e) mod 512) in
      s := (!s + v.(k) * z) mod 8380417
    done;
    (!s * 8347681) mod 8380417);;

let mev_poly_tables = mev_tbl_create 300;;
let mev_ntt_tables = mev_tbl_create 300;;

let rec MLDSA_EV_POLY p =
  try mev_tbl_find mev_poly_tables p with Not_found ->
  let r =
    match strip_comb p with
      Const("mldsa_poly",_),[f] ->
        let cth = ISPEC f MLDSA_POLY_IN_RQ in
        let base = ISPEC f COEFF_MLDSA_POLY in
        cth,Array.init 256 (fun k ->
          CONV_RULE(RAND_CONV MLDSA_EVAL_CONV) (SPEC (mk_small_numeral k) base))
    | Const("mldsa_rej_bounded_poly",_),[eta;rho] ->
        MEV_POLY_TRANSFER (SPECL [eta;rho] MLDSA_EV_REJ_BOUNDED_POLY)
    | Const("mldsa_expand_mask",_),[_;_;_;_] ->
        MEV_POLY_TRANSFER
         ((REWR_CONV mldsa_expand_mask THENC MLDSA_EVAL_CONV) p)
    | Const("mldsa_sample_in_ball",_),[_;_] ->
        MEV_POLY_TRANSFER (REWR_CONV mldsa_sample_in_ball p)
    | Const("mldsa_ntt_inv",_),[a] -> MEV_POLY_TRANSFER (MLDSA_EV_NTT_INV a)
    | Const(("ring_add"|"ring_sub") as op,_),[r;p1;p2] when r = mev_rq ->
        let c1,t1 = MLDSA_EV_POLY p1 and c2,t2 = MLDSA_EV_POLY p2 in
        let add = op = "ring_add" in
        let cth = MATCH_MP (ISPEC r (if add then RING_ADD else RING_SUB))
                           (CONJ c1 c2) in
        let th = MATCH_MP
                  (if add then MLDSA_RQ_COEFF_ADD else MLDSA_RQ_COEFF_SUB)
                  (CONJ c1 c2) in
        let ar = if add then MLDSA_EV_ADDREM_CONV else MLDSA_EV_SUBREM_CONV in
        cth,Array.init 256 (fun k ->
          CONV_RULE(RAND_CONV(LAND_CONV(BINOP_CONV(fun tm ->
              if rand tm = p1 then t1.(k) else t2.(k))) THENC ar))
            (SPEC (mk_small_numeral k) th))
    | _ -> failwith "MLDSA_EV_POLY" in
  mev_tbl_add mev_poly_tables p r; r

and MEV_POLY_TRANSFER th =
  let c',t' = MLDSA_EV_POLY (rand(concl th)) in
  EQ_MP (SYM(AP_THM (AP_TERM mev_in_rq th) mev_carrier_rq)) c',
  Array.map (fun t -> TRANS (AP_TERM (rator(lhs(concl t))) th) t) t'

and MLDSA_EV_NTT_TABLE p =
  try mev_tbl_find mev_ntt_tables p with Not_found ->
  let cth,ctab = MLDSA_EV_POLY p in
  mldsa_report "NTT";
  let l0 =
    mk_list(map (fun th -> rand(concl th)) (Array.to_list ctab),`:int`) in
  let j = `j:num` in
  let ls = mk_comb(mk_comb(mev_list_of_seq_int,
                           mk_abs(j,mk_comb(mk_comb(mev_coeff,j),p))),
                   mev_n256) in
  let lth = (LIST_OF_SEQ_CONV THENC
             LIST_CONV(fun tm -> ctab.(Num.int_of_num(dest_numeral(lhand tm)))))
            ls in
  let base = MATCH_MP MLDSA_EV_NTT_PEVAL cth in
  let leaves = MLDSA_EV_FFT_LEAVES l0 in
  let res = Array.init 256 (fun k ->
    let b = CONV_RULE(RAND_CONV(LAND_CONV(LAND_CONV(K lth))))
              (SPEC (mk_small_numeral k) base) in
    let xk = rand(lhand(rand(concl b))) in
    let leaf = INST [xk,mev_x] leaves.(mldsa_br8 k) in
    let leaf' = itlist (fun t th ->
      PROVE_HYP (MLDSA_EV_ROOT_POW k (1 lsl (7 - t))) th) (0--7) leaf in
    let c = rand(rand(rator(concl leaf'))) in
    let lt = EQT_ELIM(NUM_LT_CONV(mk_binop mev_nlt c `8380417`)) in
    TRANS b (MP (SPECL [lhand(rator(concl leaf')); c] MLDSA_EV_CONG_REM)
                (CONJ leaf' lt))) in
  mldsa_report "NTT done";
  mev_tbl_add mev_ntt_tables p res; res

and MLDSA_EV_NTT_INV a =
  mldsa_report "inverse NTT";
  let vals = Array.init 256 (fun n ->
    MLDSA_EVAL_CONV(mk_comb(a,mk_small_numeral n))) in
  let v = Array.map (fun th -> mev_dest_int(rand(concl th))) vals in
  let f = mldsa_inv_ntt_ocaml v in
  let l = mk_list(map mev_int (Array.to_list f),`:int`) in
  let i = `i:num` in
  let pf = mk_comb(mev_mldsa_poly,mk_abs(i,mk_comb(mk_comb(mev_el_int,i),l))) in
  let cpf,_ = MLDSA_EV_POLY pf in
  let ntt = MLDSA_EV_NTT_TABLE pf in
  let k = `k:num` in
  let lam = mk_abs(k,mk_eq(mk_comb(mk_comb(`mldsa_ntt`,pf),k),mk_comb(a,k))) in
  let ath = MLDSA_EV_BOUNDED_RULE lam 256
              (fun k -> TRANS ntt.(k) (SYM vals.(k))) in
  mldsa_report "inverse NTT done";
  MP (ISPECL [pf; a] MLDSA_NTT_INV_UNIQUE) (CONJ cpf ath);;

mldsa_rq_carrier_ref := (fun p -> fst(MLDSA_EV_POLY p));;

add_mldsa_handler "coeff"
 (fun tm -> match tm with
              Comb(Comb(_,k),p) when is_numeral k &&
                                     dest_numeral k </ Num.num_of_int 256 ->
                (snd(MLDSA_EV_POLY p)).(Num.int_of_num(dest_numeral k))
            | _ -> failwith "coeff");;

add_mldsa_handler "mldsa_ntt"
 (fun tm -> match tm with
              Comb(Comb(_,p),k) when is_numeral k &&
                                     dest_numeral k </ Num.num_of_int 256 ->
                (MLDSA_EV_NTT_TABLE p).(Num.int_of_num(dest_numeral k))
            | _ -> failwith "mldsa_ntt");;

(* ------------------------------------------------------------------------- *)
(* The samplers and the remaining definitions.                               *)
(* ------------------------------------------------------------------------- *)

add_mldsa_handler "mldsa_rej_ntt_poly"
 (let conv = MEV_CACHED_CONV(fun tm ->
    let th = AP_THM (SPEC (lhand tm) MLDSA_EV_REJ_NTT_POLY) (rand tm) in
    CONV_RULE(RAND_CONV(BETA_CONV THENC MLDSA_EVAL_CONV)) th) in
  fun tm -> match tm with
              Comb(Comb(_,rho),i) when is_mev_bytelist rho && is_numeral i ->
                conv tm
            | _ -> failwith "mldsa_rej_ntt_poly");;

MEV_DEF_HANDLER "mldsa_ev_rej_coeff" mldsa_ev_rej_coeff;;
MEV_DEF_HANDLER "mldsa_ev_nib" mldsa_ev_nib;;
MEV_DEF_HANDLER "mldsa_ev_bok" mldsa_ev_bok;;
MEV_DEF_HANDLER "mldsa_ev_bval" mldsa_ev_bval;;

let MEV_CLAUSES_HANDLER name th =
  let th0,th1 = CONJ_PAIR th in
  let th0 = SPEC_ALL th0 and th1 = SPEC_ALL th1 in
  let conv = MEV_CACHED_CONV(fun tm ->
    let k = match name with
              "mldsa_ball_pos" -> rand tm | _ -> rand(rator tm) in
    if k = kev_0 then (REWR_CONV th0 THENC MLDSA_EVAL_CONV) tm
    else
      let c = if name = "mldsa_ball_pos" then RAND_CONV num_CONV
              else RATOR_CONV(RAND_CONV num_CONV) in
      (c THENC REWR_CONV th1 THENC MLDSA_EVAL_CONV) tm) in
  add_mldsa_handler name conv;;

MEV_CLAUSES_HANDLER "mldsa_ball_pos" mldsa_ball_pos;;
MEV_CLAUSES_HANDLER "mldsa_ball_coeffs" mldsa_ball_coeffs;;

let MEV_UNFOLD_HANDLER name def =
  add_mldsa_handler name (REWR_CONV def THENC MLDSA_EVAL_CONV);;

do_list (fun (s,d) -> MEV_UNFOLD_HANDLER s d)
 ["mldsa_vec_norm_lt",mldsa_vec_norm_lt; "mldsa_norm_lt",mldsa_norm_lt;
  "mldsa_hint_count",mldsa_hint_count; "mldsa_hintbitpack",mldsa_hintbitpack;
  "mldsa_hint_start",mldsa_hint_start; "mldsa_hint_ok",mldsa_hint_ok;
  "mldsa_hintbitunpack",mldsa_hintbitunpack;
  "mldsa_sign_mu",mldsa_sign_mu; "mldsa_sign_internal",mldsa_sign_internal;
  "mldsa_verify_internal",mldsa_verify_internal];;

(* Options: NONE and SOME of a literal are literals, with equality.          *)

let is_mev_option tm =
  match tm with
    Const("NONE",_) -> true
  | Comb(Const("SOME",_),x) -> is_mldsa_literal x
  | _ -> false;;

let MLDSA_EV_SOME_NOT_NONE = prove
 (`!x:A. ~(SOME x = NONE)`,
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN REWRITE_TAC[option_DISTINCT]);;

let MEV_OPTION_EQ_CONV =
  let dist = option_DISTINCT and inj = option_INJ in
  fun tm ->
    let l,r = dest_eq tm in
    match l,r with
      Const("NONE",_),Const("NONE",_) -> EQT_INTRO(REFL l)
    | Const("NONE",_),Comb(Const("SOME",_),x) -> EQF_INTRO(ISPEC x dist)
    | Comb(Const("SOME",_),x),Const("NONE",_) ->
        EQF_INTRO(ISPEC x MLDSA_EV_SOME_NOT_NONE)
    | Comb(Const("SOME",_),x),Comb(Const("SOME",_),y) ->
        TRANS (ISPECL [x;y] inj) (LITERAL_EQ_CONV(mk_eq(x,y)))
    | _ -> failwith "MEV_OPTION_EQ_CONV";;

add_mldsa_handler "="
 (fun tm -> let l,r = dest_eq tm in
            if is_mev_option l && is_mev_option r then MEV_OPTION_EQ_CONV tm
            else if is_mldsa_literal l && is_mldsa_literal r
            then LITERAL_EQ_CONV tm
            else failwith "=");;

(* Match on an evaluated option.                                             *)

add_mldsa_handler "_MATCH"
 (fun tm -> match tm with
              Comb(Comb(_,e),_) when
                (match e with
                   Const("NONE",_) -> true
                 | Comb(Const("SOME",_),_) -> true
                 | _ -> false) -> (MATCH_CONV THENC MLDSA_EVAL_CONV) tm
            | _ -> failwith "_MATCH");;

(* ------------------------------------------------------------------------- *)
(* The top-level functions, via MLDSA_KEYGEN_INTERNAL_FIPS,                  *)
(* MLDSA_SIGN_ATTEMPT_FIPS and MLDSA_VERIFY_MU_FIPS, whose hypotheses are    *)
(* discharged by evaluation.                                                 *)
(* ------------------------------------------------------------------------- *)

let rec MLDSA_FIPS_CONV fips_th tm =
  try MLDSA_FIPS_CONV_RAW fips_th tm with Failure s ->
    (mldsa_report("evaluation failed: "^s); failwith s)

and MLDSA_FIPS_CONV_RAW fips_th tm =
  let th1 = PART_MATCH (lhand o rand) fips_th tm in
  mldsa_report "checking the hypotheses";
  let hth = EQT_ELIM(MLDSA_EVAL_CONV(lhand(concl th1))) in
  mldsa_report "hypotheses done";
  CONV_RULE(RAND_CONV MLDSA_EVAL_CONV) (MP th1 hth);;

add_mldsa_handler "mldsa_keygen_internal"
 (MLDSA_FIPS_CONV MLDSA_KEYGEN_INTERNAL_FIPS);;

let mev_none_sig = `NONE:(byte list)option`;;

add_mldsa_handler "mldsa_sign_attempt"
 (MEV_CACHED_CONV(fun tm ->
    mldsa_report("signing attempt, kappa = "^string_of_term(rand tm));
    let th = MLDSA_FIPS_CONV MLDSA_SIGN_ATTEMPT_FIPS tm in
    mldsa_report("attempt done: "^
                 (if rand(concl th) = mev_none_sig then "rejected"
                  else "accepted"));
    th));;

add_mldsa_handler "mldsa_verify_mu" (MLDSA_FIPS_CONV MLDSA_VERIFY_MU_FIPS);;

let MLDSA_TOP_EVAL_CONV =
  REWRITE_CONV[mldsa44; mldsa65; mldsa87] THENC MLDSA_EVAL_CONV;;
