(* ========================================================================= *)
(* The HOL Light prelude of the HOL Light backend of the FIPS compiler       *)
(* (theory FIPS_HOL_Light_Export of proofs/isabelle/spec).                   *)
(*                                                                           *)
(* The generated files code/hol_light/NAME.ml print Isabelle/HOL definitions *)
(* in HOL Light. Most Isabelle library constants have a HOL Light           *)
(* counterpart with the same meaning (CONS, LENGTH, MAP, int_add, ...).     *)
(* This file defines, by Isabelle's equations, the few whose HOL Light      *)
(* counterpart differs or does not exist:                                    *)
(*                                                                           *)
(*   isa_take, isa_drop, isa_upt, isa_list_update,                           *)
(*   isa_concat                                     (List.take, ...)         *)
(*   isa_case_option, isa_map_option                (Option)                  *)
(*   isa_nat                                        (Int.nat: 0 below 0)      *)
(*   isa_int_div, isa_int_mod                       (floor division on int)   *)
(*   isa_literal, isa_literal_nil, isa_literal_cons (String.literal)          *)
(*                                                                           *)
(* and the tactics that prove the obligations of the generated files         *)
(* NAME_obligations.ml: Isabelle theorems that characterize each primitive, *)
(* stated for its HOL Light term. It also defines fips_phantom_theorems,     *)
(* which proves the datatype theorems of a type with phantom parameters.     *)
(* ========================================================================= *)

needs "Library/words.ml";;

(* ------------------------------------------------------------------------- *)
(* Lists, by Isabelle's recursion equations.                                 *)
(* ------------------------------------------------------------------------- *)

let isa_take = define
 `(!n. isa_take n ([]:A list) = []) /\
  (!n (x:A) xs. isa_take n (CONS x xs) =
                if n = 0 then [] else CONS x (isa_take (n - 1) xs))`;;

let isa_drop = define
 `(!n. isa_drop n ([]:A list) = []) /\
  (!n (x:A) xs. isa_drop n (CONS x xs) =
                if n = 0 then CONS x xs else isa_drop (n - 1) xs)`;;

let isa_upt = define
 `(!i. isa_upt i 0 = []) /\
  (!i j. isa_upt i (SUC j) = if i <= j then APPEND (isa_upt i j) [j] else [])`;;

let isa_list_update = define
 `(!i (v:A). isa_list_update [] i v = []) /\
  (!(x:A) xs i v. isa_list_update (CONS x xs) i v =
                  if i = 0 then CONS v xs
                  else CONS x (isa_list_update xs (i - 1) v))`;;

let isa_concat = define
 `(isa_concat ([]:(A list) list) = []) /\
  (!(x:A list) xs. isa_concat (CONS x xs) = APPEND x (isa_concat xs))`;;

(* ------------------------------------------------------------------------- *)
(* Options.                                                                  *)
(* ------------------------------------------------------------------------- *)

let isa_case_option = define
 `(!(e:B) (f:A->B). isa_case_option e f NONE = e) /\
  (!(e:B) (f:A->B) x. isa_case_option e f (SOME x) = f x)`;;

let isa_map_option = define
 `(!f:A->B. isa_map_option f NONE = NONE) /\
  (!(f:A->B) x. isa_map_option f (SOME x) = SOME (f x))`;;

(* ------------------------------------------------------------------------- *)
(* Integers: Int.nat is 0 on negative integers (num_of_int is unspecified    *)
(* there); div and mod on int round towards minus infinity, while HOL        *)
(* Light's div and rem leave a nonnegative remainder. They agree for a       *)
(* positive divisor. Both divide by 0 to 0 with the dividend as remainder.   *)
(* ------------------------------------------------------------------------- *)

let isa_nat = new_definition
 `isa_nat (x:int) = if &0 <= x then num_of_int x else 0`;;

let isa_int_div = new_definition
 `isa_int_div (a:int) (b:int) = if b < &0 then (--a) div (--b) else a div b`;;

let isa_int_mod = new_definition
 `isa_int_mod (a:int) (b:int) = if b < &0 then --((--a) rem (--b)) else a rem b`;;

let ISA_NAT = prove
 (`(!x. &0 <= x ==> &(isa_nat x) = x) /\ (!x. x < &0 ==> isa_nat x = 0)`,
  REWRITE_TAC[isa_nat] THEN CONJ_TAC THEN GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT] THEN ASM_INT_ARITH_TAC);;

let ISA_INT_DIV_MOD = prove
 (`!a b. isa_int_div a b * b + isa_int_mod a b = a /\
         (&0 < b ==> &0 <= isa_int_mod a b /\ isa_int_mod a b < b) /\
         (b < &0 ==> isa_int_mod a b <= &0 /\ b < isa_int_mod a b) /\
         isa_int_div a (&0) = &0 /\ isa_int_mod a (&0) = a`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[isa_int_div; isa_int_mod; INT_LT_REFL; INT_DIV_0; INT_REM_0] THEN
  ASM_CASES_TAC `b:int < &0` THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(SPECL [`--a:int`; `--b:int`] INT_DIVISION) THEN
    ANTS_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[INT_ARITH `b:int < &0 ==> abs(--b) = --b`] THEN
    REPEAT STRIP_TAC THEN ASM_INT_ARITH_TAC;
    ASM_CASES_TAC `b:int = &0` THEN ASM_REWRITE_TAC[INT_DIV_0; INT_REM_0] THENL
     [INT_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`a:int`; `b:int`] INT_DIVISION) THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN ASM_INT_ARITH_TAC]);;

(* Natural division: Isabelle and HOL Light agree, including division by 0.  *)

let ISA_NAT_DIV_MOD = prove
 (`!m n. m DIV n * n + m MOD n = m /\ (0 < n ==> m MOD n < n) /\
         m DIV 0 = 0 /\ m MOD 0 = m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DIV_ZERO; MOD_ZERO] THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[DIV_ZERO; MOD_ZERO; MULT_CLAUSES; ADD_CLAUSES; LT_REFL];
    ASM_MESON_TAC[DIVISION]]);;

(* ------------------------------------------------------------------------- *)
(* Words: val identifies the words of length n with the naturals below 2^n.  *)
(* ------------------------------------------------------------------------- *)

let ISA_VAL_ONTO = prove
 (`!n. n < 2 EXP dimindex(:N) ==> ?w:N word. val w = n`,
  MESON_TAC[VAL_WORD_EQ]);;

let ISA_VAL_IWORD = prove
 (`!x. val(iword x:N word) = isa_nat (isa_int_mod x (&2 pow dimindex(:N)))`,
  GEN_TAC THEN
  SUBGOAL_THEN `&0:int < (&2:int) pow dimindex(:N)` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_POW_LT THEN INT_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[iword; isa_int_mod; isa_nat] THEN
  ASM_SIMP_TAC[INT_ARITH `&0:int < x ==> ~(x < &0)`] THEN
  MP_TAC(SPECL [`x:int`; `(&2:int) pow dimindex(:N)`] INT_DIVISION) THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[VAL_WORD] THEN
  MATCH_MP_TAC MOD_LT THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_POW] THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT] THEN ASM_INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Isabelle's String.literal: the strings of 7-bit characters.               *)
(* ------------------------------------------------------------------------- *)

let isa_literal_TYBIJ = new_type_definition "isa_literal"
  ("mk_isa_literal", "dest_isa_literal")
  (prove(`?s. ALL (\c. ?b0 b1 b2 b3 b4 b5 b6. c = ASCII b0 b1 b2 b3 b4 b5 b6 F) s`,
         EXISTS_TAC `[]:char list` THEN REWRITE_TAC[ALL]));;

(* The empty literal and the literal of a 7-bit character and a literal, as  *)
(* Isabelle's String.Literal builds them. A literal names an unspecified     *)
(* function, such as the pre-hash oracle of FIPS 204.                        *)

let isa_literal_nil = new_definition
 `isa_literal_nil = mk_isa_literal []`;;

let isa_literal_cons = new_definition
 `isa_literal_cons b0 b1 b2 b3 b4 b5 b6 s =
    mk_isa_literal (CONS (ASCII b0 b1 b2 b3 b4 b5 b6 F) (dest_isa_literal s))`;;

(* ------------------------------------------------------------------------- *)
(* The tactics of the obligations.                                           *)
(* ------------------------------------------------------------------------- *)

let ISA_NAT_TAC = MESON_TAC[ISA_NAT];;

let ISA_INT_DIV_MOD_TAC = MESON_TAC[ISA_INT_DIV_MOD];;

let ISA_NAT_DIV_MOD_TAC = MESON_TAC[ISA_NAT_DIV_MOD];;

let ISA_WORD_TAC =
  MESON_TAC[VAL_BOUND; VAL_EQ; ISA_VAL_ONTO; VAL_WORD_0; ISA_VAL_IWORD];;

(* ------------------------------------------------------------------------- *)
(* A one-constructor datatype whose type parameters do not all occur in its  *)
(* field (phantom parameters, such as the modulus of a residue) is a type    *)
(* definition over the constant functions from the phantom parameters to the *)
(* field type:                                                               *)
(*                                                                           *)
(*   tybij:  (!a. mk (dest a) = a) /\                                        *)
(*           (!f. (!p q. f p = f q) <=> dest (mk f) = f)                     *)
(*   C_DEF:  !x. C x = mk (\p. x)                                            *)
(*   S_DEF:  !r. S r = dest r ARB                                            *)
(*                                                                           *)
(* fips_phantom_theorems proves the theorems of Isabelle's datatype:          *)
(*   !x. S (C x) = x,   !r. C (S r) = r,   !x y. C x = C y <=> x = y.        *)
(* ------------------------------------------------------------------------- *)

let fips_phantom_theorems tybij ctr_def sel_def =
  let x, ctr_eq = dest_forall (concl ctr_def) in
  let ctr_x, mk_lam = dest_eq ctr_eq in
  let ctr = rator ctr_x in
  let r, sel_eq = dest_forall (concl sel_def) in
  let sel_r, dest_app = dest_eq sel_eq in
  let sel = rator sel_r in
  let dest = rator (rator dest_app) in
  let rep_abs =
    prove(mk_forall(x, mk_eq(mk_comb(dest, mk_lam), rand mk_lam)),
          REWRITE_TAC[GSYM (CONJUNCT2 tybij)]) in
  let sel_ctr =
    prove(mk_forall(x, mk_eq(mk_comb(sel, mk_comb(ctr, x)), x)),
          REWRITE_TAC[ctr_def; sel_def; rep_abs]) in
  let pty = fst(dest_fun_ty(type_of(mk_comb(dest, r)))) in
  let p = mk_var("p", pty) and q = mk_var("q", pty) in
  let constant =
    prove(list_mk_forall([r; p; q],
            mk_eq(mk_comb(mk_comb(dest, r), p), mk_comb(mk_comb(dest, r), q))),
          MESON_TAC[tybij]) in
  let ctr_sel =
    prove(mk_forall(r, mk_eq(mk_comb(ctr, mk_comb(sel, r)), r)),
          GEN_TAC THEN REWRITE_TAC[ctr_def; sel_def] THEN
          GEN_REWRITE_TAC RAND_CONV [GSYM (CONJUNCT1 tybij)] THEN AP_TERM_TAC THEN
          REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[constant]) in
  let y = variant [x] x in
  let inject =
    prove(list_mk_forall([x; y],
            mk_eq(mk_eq(mk_comb(ctr, x), mk_comb(ctr, y)), mk_eq(x, y))),
          MESON_TAC[sel_ctr]) in
  sel_ctr, ctr_sel, inject;;

(* ------------------------------------------------------------------------- *)
(* A record is a type definition over the tuple of its fields:               *)
(*                                                                           *)
(*   tybij:  (!a. mk (dest a) = a) /\ (!r. T <=> dest (mk r) = r)            *)
(*   EXT_DEF: !x1 ... xk. EXT x1 ... xk = mk (x1, ..., xk)                   *)
(*                                                                           *)
(* and its selectors and updates are definitions over the tuple.             *)
(* FIPS_RECORD_TAC proves their equations on EXT x1 ... xk, and              *)
(* FIPS_RECORD_INJECT_TAC that EXT is injective.                             *)
(* ------------------------------------------------------------------------- *)

let fips_record_rep_abs tybij = REWRITE_RULE[] (CONJUNCT2 tybij);;

let FIPS_RECORD_TAC tybij defs =
  REWRITE_TAC (defs @ [fips_record_rep_abs tybij; FST; SND]);;

let FIPS_RECORD_INJECT_TAC tybij ext_def =
  let rep_abs = fips_record_rep_abs tybij in
  let dest = rator (lhs (snd (dest_forall (concl rep_abs)))) in
  REPEAT GEN_TAC THEN REWRITE_TAC[ext_def] THEN EQ_TAC THENL
   [DISCH_THEN (MP_TAC o AP_TERM dest) THEN REWRITE_TAC[rep_abs; PAIR_EQ];
    STRIP_TAC THEN ASM_REWRITE_TAC[]];;

(* ------------------------------------------------------------------------- *)
(* HOL Light reads a variable that is named like a constant as the constant  *)
(* (unless it is bound without a type). A generated file first checks that  *)
(* none of its variables is a constant of the context it is loaded in.       *)
(* ------------------------------------------------------------------------- *)

let fips_check_variables names =
  match filter (fun v -> can get_const_type v) names with
    [] -> ()
  | clashes ->
      failwith ("fips_check_variables: these variables of the generated file " ^
                "are HOL Light constants of this context: " ^
                String.concat ", " clashes);;

let fips_hol_prelude_loaded = true;;
