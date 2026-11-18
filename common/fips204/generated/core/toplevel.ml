(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Top level of the equivalence proof: ML-DSA key generation, signing and    *)
(* verification (internal, from mu, external and HashML-DSA), and their      *)
(* checked and public wrappers, for ML-DSA-44, -65 and -87.                  *)
(*                                                                           *)
(* Load from the repository root after base.ml and common.ml.          *)
(*                                                                           *)
(* The statements are built from templates (STMT_*, with @P@ for the         *)
(* parameter set); check.ml prints every final statement in full. The        *)
(* wrapper theorems EQ_ML_DSA_*_P etc. below carry the structure theorems    *)
(* of the internal families (keygen.ml, sign.ml, verify.ml)   *)
(* as hypotheses; equivalence.ml discharges them and rebinds the names to    *)
(* theorems without hypotheses.                                              *)
(* ========================================================================= *)

needs "common/fips204/generated/core/core.ml";;
needs "common/fips204/generated/core/ball.ml";;

(* ------------------------------------------------------------------------- *)
(* Instantiating a statement for a parameter set. In the template strings    *)
(* below, @P@ is the generated name of the parameter set (MLDSA44), @HW@     *)
(* the handwritten tuple (mldsa44), and @PK@, @SK@, @SIG@ the byte lengths   *)
(* of the public key, the secret key and the signature.                      *)
(* ------------------------------------------------------------------------- *)

let top_subst (subs:(string*string) list) (s:string) =
  let repl s (a,b) =
    let la = String.length a and ls = String.length s in
    let buf = Buffer.create ls in
    let rec go i =
      if i > ls - la then Buffer.add_string buf (String.sub s i (ls - i))
      else if String.sub s i la = a then (Buffer.add_string buf b; go (i + la))
      else (Buffer.add_char buf (String.get s i); go (i + 1)) in
    (go 0; Buffer.contents buf) in
  List.fold_left repl s subs;;

let top_params p =
  match p with
    "44" -> ["@P@","MLDSA44"; "@HW@","mldsa44"; "@PK@","1312";
             "@SK@","2560"; "@SIG@","2420"; "@K@","4"; "@L@","4";
             "@ALLOWED@","{&1, &2, &3, &6, &8, &9, &10, &11, &12}"]
  | "65" -> ["@P@","MLDSA65"; "@HW@","mldsa65"; "@PK@","1952";
             "@SK@","4032"; "@SIG@","3309"; "@K@","6"; "@L@","5";
             "@ALLOWED@","{&2, &3, &9, &10, &12}"]
  | "87" -> ["@P@","MLDSA87"; "@HW@","mldsa87"; "@PK@","2592";
             "@SK@","4896"; "@SIG@","4627"; "@K@","8"; "@L@","7";
             "@ALLOWED@","{&3, &10, &12}"]
  | _ -> failwith "top_params";;

let top_tm p s = parse_term (top_subst (top_params p) s);;

let top_sets = ["44"; "65"; "87"];;

(* ------------------------------------------------------------------------- *)
(* Basic facts about the generated monad (local versions; see core.ml).      *)
(* ------------------------------------------------------------------------- *)


let TOP_INT_TO_BIT = prove
 (`typed_hol_int_to_bit (&0) = Value F /\ typed_hol_int_to_bit (&1) = Value T`,
  REWRITE_TAC[typed_hol_int_to_bit_DEF] THEN CONV_TAC INT_REDUCE_CONV);;

let TOP_BIT_VALUE = prove
 (`(!b. native_bind (typed_hol_bit_value b) typed_hol_int_to_bit = Value b) /\
   (!b (f:int->(A)native_result).
      native_bind (typed_hol_bit_value b) f = f (if b then &1 else &0))`,
  CONJ_TAC THEN GEN_TAC THEN
  REWRITE_TAC[typed_hol_bit_value_DEF; NATIVE_BIND] THEN
  COND_CASES_TAC THEN REWRITE_TAC[TOP_INT_TO_BIT]);;

let TOP_CASE_CLAUSES = prove
 (`(!f1 (f2:A->B). case_native_bottom f1 f2 Native_Bottom = f1) /\
   (!f1 (f2:A->B) x. case_native_bottom f1 f2 (Native_Value x) = f2 x) /\
   (!(i:int). typed_hol_bottom_index (Native_Bottom:(A list)native_bottom) i =
              NONE) /\
   (!(xs:A list) i. typed_hol_bottom_index (Native_Value xs) i =
                    native_list_index xs i) /\
   (!(e:B) (f:A->B). isa_case_option e f NONE = e) /\
   (!(e:B) (f:A->B) x. isa_case_option e f (SOME x) = f x)`,
  REWRITE_TAC[case_native_bottom_DEF; typed_hol_bottom_index_DEF;
              isa_case_option]);;

(* The basic simplification of a generated definition.                       *)

let TOP_MONAD_RULES =
  [NATIVE_BIND; TYPED_HOL_READ; NATIVE_FINISH; ISA_NAT_NUM;
   TOP_INT_TO_BIT; TOP_BIT_VALUE; TYPED_HOL_EMPTY_SLICE; TOP_CASE_CLAUSES;
   case_native_result_DEF; case_statement_outcome_DEF; LET_DEF; LET_END_DEF] @
  CONJUNCTS lift_sign_result @ CONJUNCTS lift_sign_internal_result @
  CONJUNCTS lift_verify_result @ CONJUNCTS lift_verify_bool;;

(* IntegerToBytes(x,1) for a byte value x (local version; see encode.ml).    *)


let TOP_CTX_TOO_LONG = prove
 (`!n. (&0:int) < &n - &255 <=> 255 < n`,
  REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC);;

(* Evaluation of the generated bitlen on numerals.                           *)

let TOP_BITLEN_CONV =
  let th0 = prove
   (`bitlen 0 = 0`,
    GEN_REWRITE_TAC LAND_CONV [bitlen_DEF] THEN REWRITE_TAC[])
  and thS = prove
   (`!n. ~(n = 0) ==> bitlen n = SUC(bitlen(n DIV 2))`,
    GEN_TAC THEN DISCH_TAC THEN GEN_REWRITE_TAC LAND_CONV [bitlen_DEF] THEN
    ASM_REWRITE_TAC[]) in
  let rec conv tm =
    match tm with
      Comb(Const("bitlen",_),ntm) when is_numeral ntm ->
        if dest_numeral ntm =/ num 0 then th0 else
        let th1 = MP (SPEC ntm thS)
                     (EQF_ELIM(NUM_EQ_CONV(mk_eq(ntm,`0`)))) in
        CONV_RULE(RAND_CONV(RAND_CONV(RAND_CONV NUM_DIV_CONV THENC conv) THENC
                            NUM_SUC_CONV)) th1
    | _ -> failwith "TOP_BITLEN_CONV" in
  conv;;

(* Integer arithmetic on literals in the generated code.                     *)

let TOP_ARITH_RULES =
  [typed_hol_int_arithmetic_DEF; bitlen_semantic_DEF; arith_faults_DEF;
   distinctness "aop"; int_op_DEF; case_aop_DEF; isa_int_div; isa_int_mod];;

let TOP_ARITH_TAC =
  REWRITE_TAC(ISA_NAT_NUM :: TOP_ARITH_RULES) THEN
  CONV_TAC(DEPTH_CONV TOP_BITLEN_CONV) THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC TOP_MONAD_RULES THEN CONV_TAC INT_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* MLDSAVerifyLengthCheck.                                                   *)
(* ------------------------------------------------------------------------- *)

let TOP_LENGTHCHECK_TEMPLATE =
 "!pk sg. MLDSAVerifyLengthCheck_@P@_Configuration_hol pk sg =
          Value (LENGTH pk = @PK@ /\\ LENGTH sg = @SIG@)";;

let EQ_MLDSAVERIFYLENGTHCHECK_MLDSA44,
    EQ_MLDSAVERIFYLENGTHCHECK_MLDSA65,
    EQ_MLDSAVERIFYLENGTHCHECK_MLDSA87 =
  let f p =
    let def = assoc p
     ["44",MLDSAVerifyLengthCheck_MLDSA44_Configuration_hol_DEF;
      "65",MLDSAVerifyLengthCheck_MLDSA65_Configuration_hol_DEF;
      "87",MLDSAVerifyLengthCheck_MLDSA87_Configuration_hol_DEF] in
    prove(top_tm p TOP_LENGTHCHECK_TEMPLATE,
      REPEAT GEN_TAC THEN REWRITE_TAC(def :: TOP_MONAD_RULES) THEN
      TOP_ARITH_TAC THEN
      REWRITE_TAC[INT_OF_NUM_EQ] THEN
      REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[]) in
  f "44", f "65", f "87";;

(* The lengths of FIPS 204 Section 3.6.2, as the handwritten verification    *)
(* checks them.                                                              *)

let TOP_VERIFY_MU_LENGTHS_TEMPLATE =
 "!pk mu sg. mldsa_verify_mu_accepts @HW@ pk mu sg
             ==> LENGTH pk = @PK@ /\\ LENGTH sg = @SIG@";;

let TOP_VERIFY_MU_LENGTHS_MLDSA44,
    TOP_VERIFY_MU_LENGTHS_MLDSA65,
    TOP_VERIFY_MU_LENGTHS_MLDSA87 =
  let f p =
    prove(top_tm p TOP_VERIFY_MU_LENGTHS_TEMPLATE,
      REWRITE_TAC[mldsa44; mldsa65; mldsa87; mldsa_verify_mu_accepts;
                  LET_DEF; LET_END_DEF] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV MLDSA_BITLEN_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]) in
  f "44", f "65", f "87";;

(* A signature or key of the wrong length is rejected.                       *)

let TOP_VERIFY_MU_INVALID_MLDSA44,
    TOP_VERIFY_MU_INVALID_MLDSA65,
    TOP_VERIFY_MU_INVALID_MLDSA87 =
  let f p th =
    prove(top_tm p
     "!pk mu sg. ~(LENGTH pk = @PK@ /\\ LENGTH sg = @SIG@)
                 ==> mldsa_verify_mu @HW@ pk mu sg =
                     MLDSA_Verify_Error_InvalidSignature",
     REWRITE_TAC[mldsa_verify_mu; mldsa_verify_of_bool] THEN
     REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_MESON_TAC[th]) in
  f "44" TOP_VERIFY_MU_LENGTHS_MLDSA44,
  f "65" TOP_VERIFY_MU_LENGTHS_MLDSA65,
  f "87" TOP_VERIFY_MU_LENGTHS_MLDSA87;;

(* ------------------------------------------------------------------------- *)
(* The statements of the main theorems, for each parameter set.              *)
(* ------------------------------------------------------------------------- *)

let STMT_KEYGEN_INTERNAL =
 "!xi. xof_ok /\\ LENGTH xi = 32
       ==> ML_DSA_KeyGen_internal_@P@_Configuration_hol xi =
           Value (mldsa_keygen_internal @HW@ xi)";;

let STMT_SIGN_INTERNAL_MU =
 "!sk mu rnd.
     xof_ok /\\ LENGTH sk = @SK@
     ==> ML_DSA_Sign_internal_mu_@P@_Configuration_hol sk mu rnd =
         lift_sign_internal_result (mldsa_sign_mu @HW@ NONE sk mu rnd)";;

let STMT_SIGN_INTERNAL =
 "!sk m rnd.
     xof_ok /\\ LENGTH sk = @SK@
     ==> ML_DSA_Sign_internal_@P@_Configuration_hol sk (bits_of_bytes m) rnd =
         lift_sign_internal_result (mldsa_sign_internal @HW@ NONE sk m rnd)";;

let STMT_VERIFY_INTERNAL_MU =
 "!pk mu sg.
     xof_ok /\\ LENGTH pk = @PK@ /\\ LENGTH sg = @SIG@
     ==> ML_DSA_Verify_internal_mu_@P@_Configuration_hol pk mu sg =
         lift_verify_bool (mldsa_verify_mu @HW@ pk mu sg)";;

let STMT_VERIFY_INTERNAL =
 "!pk m sg.
     xof_ok /\\ LENGTH pk = @PK@ /\\ LENGTH sg = @SIG@
     ==> ML_DSA_Verify_internal_@P@_Configuration_hol pk (bits_of_bytes m) sg =
         lift_verify_bool (mldsa_verify_internal @HW@ pk m sg)";;

let STMT_SIGN_MU_CHECKED =
 "!sk mu rnd.
     xof_ok /\\ LENGTH sk = @SK@
     ==> MLDSASignMuChecked_@P@_Configuration_hol sk mu rnd =
         if LENGTH mu = 64
         then lift_sign_result (mldsa_sign_mu @HW@ NONE sk mu rnd)
         else Value Native_Bottom";;

let STMT_VERIFY_MU_CHECKED =
 "!pk mu sg.
     xof_ok
     ==> MLDSAVerifyMuChecked_@P@_Configuration_hol pk mu sg =
         if LENGTH mu = 64
         then lift_verify_bool (mldsa_verify_mu @HW@ pk mu sg)
         else Value F";;

let STMT_VERIFY_INTERNAL_CHECKED =
 "!pk m sg.
     xof_ok
     ==> MLDSAVerifyInternalChecked_@P@_Configuration_hol
          pk (bits_of_bytes m) sg =
         lift_verify_bool (mldsa_verify_internal @HW@ pk m sg)";;

let STMT_KEYGEN =
 "!ent xi.
     xof_ok /\\ ent 0 = SOME xi /\\ LENGTH xi = 32
     ==> ML_DSA_KeyGen_@P@_Configuration_hol ent =
         Value (Native_Value (mldsa_keygen @HW@ xi))";;

let STMT_SIGN =
 "!ent sk m ctx rnd.
     xof_ok /\\ LENGTH sk = @SK@ /\\ ent 0 = SOME rnd
     ==> ML_DSA_Sign_@P@_Configuration_hol ent sk (bits_of_bytes m) ctx =
         lift_sign_result (mldsa_sign @HW@ NONE sk m ctx rnd)";;

let STMT_VERIFY =
 "!pk m sg ctx.
     xof_ok /\\ LENGTH pk = @PK@ /\\ LENGTH sg = @SIG@
     ==> ML_DSA_Verify_@P@_Configuration_hol pk (bits_of_bytes m) sg ctx =
         lift_verify_result (mldsa_verify @HW@ pk m sg ctx)";;

let STMT_VERIFY_PUBLIC =
 "!pk m sg ctx.
     xof_ok
     ==> MLDSAVerifyPublic_@P@_Configuration_hol pk (bits_of_bytes m) sg ctx =
         lift_verify_result (mldsa_verify @HW@ pk m sg ctx)";;

(* Hypotheses on components used by the wrappers (discharged in              *)
(* equivalence.ml).                                                          *)

let HYP_BYTESTOBITSSTRING =
 `!z. BytesToBitsString_hol z = Value (bits_of_bytes z)`;;

(* ------------------------------------------------------------------------- *)
(* Proving a statement from hypotheses, which stay as assumptions of the     *)
(* theorem until PROVE_HYP discharges them.                                  *)
(* ------------------------------------------------------------------------- *)

let top_prove hyps stmt tac =
  let th = prove(itlist (curry mk_imp) hyps stmt, REPEAT DISCH_TAC THEN tac) in
  funpow (length hyps) UNDISCH th;;

let top_def p l = assoc p l;;

(* Splitting on the context-length check and evaluating the encoding of the  *)
(* domain separator and the context length.                                  *)

let TOP_CTX_TAC =
  REWRITE_TAC[TOP_CTX_TOO_LONG] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC TOP_MONAD_RULES THEN
  SUBGOAL_THEN `LENGTH(ctx:byte list) < 256` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC(INTEGER_TO_BYTES_1_NUM :: ARITH_RULE `0 < 256 /\ 1 < 256` ::
               TOP_MONAD_RULES) THEN
  REWRITE_TAC[APPEND; GSYM BITS_OF_BYTES_APPEND];;

(* The handwritten internal functions take no context and never give        *)
(* BadContext. The generated internal functions have no native_bottom, so    *)
(* the wrappers can use lift_sign_internal_result and lift_verify_bool       *)
(* under a bind only for such results.                                       *)

let TOP_SIGN_OF_OPTION_NOT_BAD = prove
 (`!x. ~(mldsa_sign_of_option x = MLDSA_Sign_Error_BadContext)`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `x:(byte list)option` (cases "option")) THEN
  REWRITE_TAC[mldsa_sign_of_option; distinctness "mldsa_sign_result"]);;

let TOP_SIGN_MU_NOT_BAD = prove
 (`!p b sk mu rnd. ~(mldsa_sign_mu p b sk mu rnd = MLDSA_Sign_Error_BadContext)`,
  REWRITE_TAC[FORALL_PAIR_THM; mldsa_sign_mu] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[TOP_SIGN_OF_OPTION_NOT_BAD]);;

let TOP_SIGN_INTERNAL_NOT_BAD = prove
 (`!p b sk m rnd.
     ~(mldsa_sign_internal p b sk m rnd = MLDSA_Sign_Error_BadContext)`,
  REWRITE_TAC[mldsa_sign_internal; TOP_SIGN_MU_NOT_BAD]);;

let TOP_BIND_SIGN = prove
 (`!r. ~(r = MLDSA_Sign_Error_BadContext)
       ==> native_bind (lift_sign_internal_result r)
                       (\v. Value (Native_Value v)) = lift_sign_result r`,
  GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `r:mldsa_sign_result` (cases "mldsa_sign_result")) THEN
  REWRITE_TAC[distinctness "mldsa_sign_result"; lift_sign_internal_result;
              lift_sign_result; NATIVE_BIND]);;

(* The verification functions give a bool for the accepted signatures; the   *)
(* lift to a generated value is Value of that bool.                          *)

let TOP_LIFT_VERIFY_MU = prove
 (`!p pk mu sg. lift_verify_bool (mldsa_verify_mu p pk mu sg) =
                Value (mldsa_verify_mu_accepts p pk mu sg)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mldsa_verify_mu; mldsa_verify_of_bool] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[lift_verify_bool]);;

let TOP_VERIFY_MU_NOT_BAD = prove
 (`!p pk mu sg.
     ~(mldsa_verify_mu p pk mu sg = MLDSA_Verify_Error_BadContext)`,
  REWRITE_TAC[mldsa_verify_mu; mldsa_verify_of_bool] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[distinctness "mldsa_verify_result"]);;

let TOP_VERIFY_INTERNAL_NOT_BAD = prove
 (`!p pk m sg.
     ~(mldsa_verify_internal p pk m sg = MLDSA_Verify_Error_BadContext)`,
  REWRITE_TAC[mldsa_verify_internal; TOP_VERIFY_MU_NOT_BAD]);;

let TOP_BIND_VERIFY = prove
 (`!r. ~(r = MLDSA_Verify_Error_BadContext)
       ==> native_bind (lift_verify_bool r) (\v. Value (Native_Value v)) =
           lift_verify_result r`,
  GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `r:mldsa_verify_result`
                     (cases "mldsa_verify_result")) THEN
  REWRITE_TAC[distinctness "mldsa_verify_result"; lift_verify_bool;
              lift_verify_result; NATIVE_BIND]);;

(* ------------------------------------------------------------------------- *)
(* ML_DSA_Verify (FIPS 204 Algorithm 3).                                     *)
(* ------------------------------------------------------------------------- *)

let EQ_ML_DSA_VERIFY_MLDSA44,
    EQ_ML_DSA_VERIFY_MLDSA65,
    EQ_ML_DSA_VERIFY_MLDSA87 =
  let f p =
    let def = top_def p
     ["44",ML_DSA_Verify_MLDSA44_Configuration_hol_DEF;
      "65",ML_DSA_Verify_MLDSA65_Configuration_hol_DEF;
      "87",ML_DSA_Verify_MLDSA87_Configuration_hol_DEF] in
    top_prove [HYP_BYTESTOBITSSTRING; top_tm p STMT_VERIFY_INTERNAL]
     (top_tm p STMT_VERIFY)
     (REPEAT STRIP_TAC THEN REWRITE_TAC(def :: TOP_MONAD_RULES) THEN
      REWRITE_TAC[mldsa_verify] THEN TOP_CTX_TAC THEN
      ASM_SIMP_TAC(TOP_BIND_VERIFY :: TOP_VERIFY_INTERNAL_NOT_BAD ::
                   TOP_MONAD_RULES)) in
  f "44", f "65", f "87";;

let TOP_OPTION_CASES_TAC tm =
  STRUCT_CASES_TAC(ISPEC tm (cases "option")) THEN
  ASM_REWRITE_TAC TOP_MONAD_RULES;;

(* ------------------------------------------------------------------------- *)
(* ML_DSA_Sign (FIPS 204 Algorithm 2).                                       *)
(* ------------------------------------------------------------------------- *)

let EQ_ML_DSA_SIGN_MLDSA44,
    EQ_ML_DSA_SIGN_MLDSA65,
    EQ_ML_DSA_SIGN_MLDSA87 =
  let f p =
    let def = top_def p
     ["44",ML_DSA_Sign_MLDSA44_Configuration_hol_DEF;
      "65",ML_DSA_Sign_MLDSA65_Configuration_hol_DEF;
      "87",ML_DSA_Sign_MLDSA87_Configuration_hol_DEF] in
    top_prove [HYP_BYTESTOBITSSTRING; top_tm p STMT_SIGN_INTERNAL]
     (top_tm p STMT_SIGN)
     (REPEAT STRIP_TAC THEN REWRITE_TAC(def :: TOP_MONAD_RULES) THEN
      REWRITE_TAC[mldsa_sign] THEN TOP_CTX_TAC THEN
      ASM_SIMP_TAC(INTEGER_TO_BYTES_1_NUM ::
                   ARITH_RULE `0 < 256 /\ 1 < 256` :: TOP_MONAD_RULES) THEN
      REWRITE_TAC[APPEND; GSYM BITS_OF_BYTES_APPEND] THEN
      ASM_SIMP_TAC(TOP_BIND_SIGN :: TOP_SIGN_INTERNAL_NOT_BAD ::
                   TOP_MONAD_RULES)) in
  f "44", f "65", f "87";;

(* ------------------------------------------------------------------------- *)
(* ML_DSA_KeyGen (FIPS 204 Algorithm 1).                                     *)
(* ------------------------------------------------------------------------- *)

let EQ_ML_DSA_KEYGEN_MLDSA44,
    EQ_ML_DSA_KEYGEN_MLDSA65,
    EQ_ML_DSA_KEYGEN_MLDSA87 =
  let f p =
    let def = top_def p
     ["44",ML_DSA_KeyGen_MLDSA44_Configuration_hol_DEF;
      "65",ML_DSA_KeyGen_MLDSA65_Configuration_hol_DEF;
      "87",ML_DSA_KeyGen_MLDSA87_Configuration_hol_DEF] in
    top_prove [top_tm p STMT_KEYGEN_INTERNAL]
     (top_tm p STMT_KEYGEN)
     (REPEAT STRIP_TAC THEN
      REWRITE_TAC(def :: mldsa_keygen :: TOP_MONAD_RULES) THEN
      ASM_SIMP_TAC TOP_MONAD_RULES) in
  f "44", f "65", f "87";;

(* ------------------------------------------------------------------------- *)
(* The checked wrappers.                                                     *)
(* ------------------------------------------------------------------------- *)

let TOP_INT_EQ_TAC =
  REWRITE_TAC[INT_OF_NUM_EQ; INT_ARITH `(if b then &1 else &0:int) = &0 <=> ~b`];;

let EQ_MLDSASIGNMUCHECKED_MLDSA44,
    EQ_MLDSASIGNMUCHECKED_MLDSA65,
    EQ_MLDSASIGNMUCHECKED_MLDSA87 =
  let f p =
    let def = top_def p
     ["44",MLDSASignMuChecked_MLDSA44_Configuration_hol_DEF;
      "65",MLDSASignMuChecked_MLDSA65_Configuration_hol_DEF;
      "87",MLDSASignMuChecked_MLDSA87_Configuration_hol_DEF] in
    top_prove [top_tm p STMT_SIGN_INTERNAL_MU]
     (top_tm p STMT_SIGN_MU_CHECKED)
     (REPEAT STRIP_TAC THEN REWRITE_TAC(def :: TOP_MONAD_RULES) THEN
      TOP_INT_EQ_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC(TOP_BIND_SIGN :: TOP_SIGN_MU_NOT_BAD ::
                   TOP_MONAD_RULES)) in
  f "44", f "65", f "87";;

let EQ_MLDSAVERIFYMUCHECKED_MLDSA44,
    EQ_MLDSAVERIFYMUCHECKED_MLDSA65,
    EQ_MLDSAVERIFYMUCHECKED_MLDSA87 =
  let f p =
    let def = top_def p
     ["44",MLDSAVerifyMuChecked_MLDSA44_Configuration_hol_DEF;
      "65",MLDSAVerifyMuChecked_MLDSA65_Configuration_hol_DEF;
      "87",MLDSAVerifyMuChecked_MLDSA87_Configuration_hol_DEF]
    and lc = top_def p
     ["44",EQ_MLDSAVERIFYLENGTHCHECK_MLDSA44;
      "65",EQ_MLDSAVERIFYLENGTHCHECK_MLDSA65;
      "87",EQ_MLDSAVERIFYLENGTHCHECK_MLDSA87]
    and len = top_def p
     ["44",TOP_VERIFY_MU_INVALID_MLDSA44;
      "65",TOP_VERIFY_MU_INVALID_MLDSA65;
      "87",TOP_VERIFY_MU_INVALID_MLDSA87] in
    top_prove [top_tm p STMT_VERIFY_INTERNAL_MU]
     (top_tm p STMT_VERIFY_MU_CHECKED)
     (REPEAT STRIP_TAC THEN REWRITE_TAC(def :: lc :: TOP_MONAD_RULES) THEN
      TOP_INT_EQ_TAC THEN ASM_CASES_TAC `LENGTH(mu:byte list) = 64` THEN
      ASM_REWRITE_TAC TOP_MONAD_RULES THEN
      ASM_CASES_TAC (top_tm p
        "LENGTH(pk:byte list) = @PK@ /\\ LENGTH(sg:byte list) = @SIG@") THEN
      ASM_SIMP_TAC TOP_MONAD_RULES THEN
      ASM_SIMP_TAC(len :: TOP_MONAD_RULES)) in
  f "44", f "65", f "87";;

let TOP_VERIFY_INTERNAL_LENGTHS_MLDSA44,
    TOP_VERIFY_INTERNAL_LENGTHS_MLDSA65,
    TOP_VERIFY_INTERNAL_LENGTHS_MLDSA87 =
  let f p th =
    prove(top_tm p
     "!pk m sg. ~(LENGTH pk = @PK@ /\\ LENGTH sg = @SIG@)
                ==> mldsa_verify_internal @HW@ pk m sg =
                    MLDSA_Verify_Error_InvalidSignature",
     REWRITE_TAC[mldsa_verify_internal] THEN MESON_TAC[th]) in
  f "44" TOP_VERIFY_MU_INVALID_MLDSA44,
  f "65" TOP_VERIFY_MU_INVALID_MLDSA65,
  f "87" TOP_VERIFY_MU_INVALID_MLDSA87;;

let EQ_MLDSAVERIFYINTERNALCHECKED_MLDSA44,
    EQ_MLDSAVERIFYINTERNALCHECKED_MLDSA65,
    EQ_MLDSAVERIFYINTERNALCHECKED_MLDSA87 =
  let f p =
    let def = top_def p
     ["44",MLDSAVerifyInternalChecked_MLDSA44_Configuration_hol_DEF;
      "65",MLDSAVerifyInternalChecked_MLDSA65_Configuration_hol_DEF;
      "87",MLDSAVerifyInternalChecked_MLDSA87_Configuration_hol_DEF]
    and lc = top_def p
     ["44",EQ_MLDSAVERIFYLENGTHCHECK_MLDSA44;
      "65",EQ_MLDSAVERIFYLENGTHCHECK_MLDSA65;
      "87",EQ_MLDSAVERIFYLENGTHCHECK_MLDSA87]
    and len = top_def p
     ["44",TOP_VERIFY_INTERNAL_LENGTHS_MLDSA44;
      "65",TOP_VERIFY_INTERNAL_LENGTHS_MLDSA65;
      "87",TOP_VERIFY_INTERNAL_LENGTHS_MLDSA87] in
    top_prove [top_tm p STMT_VERIFY_INTERNAL]
     (top_tm p STMT_VERIFY_INTERNAL_CHECKED)
     (REPEAT STRIP_TAC THEN REWRITE_TAC(def :: lc :: TOP_MONAD_RULES) THEN
      TOP_INT_EQ_TAC THEN
      ASM_CASES_TAC (top_tm p
        "LENGTH(pk:byte list) = @PK@ /\\ LENGTH(sg:byte list) = @SIG@") THEN
      ASM_SIMP_TAC TOP_MONAD_RULES THEN
      ASM_SIMP_TAC(len :: injectivity "native_result" :: TOP_MONAD_RULES)) in
  f "44", f "65", f "87";;

(* ------------------------------------------------------------------------- *)
(* MLDSAVerifyPublic: ML_DSA_Verify behind the length checks.                *)
(* ------------------------------------------------------------------------- *)

let EQ_MLDSAVERIFYPUBLIC_MLDSA44,
    EQ_MLDSAVERIFYPUBLIC_MLDSA65,
    EQ_MLDSAVERIFYPUBLIC_MLDSA87 =
  let f p =
    let def = top_def p
     ["44",MLDSAVerifyPublic_MLDSA44_Configuration_hol_DEF;
      "65",MLDSAVerifyPublic_MLDSA65_Configuration_hol_DEF;
      "87",MLDSAVerifyPublic_MLDSA87_Configuration_hol_DEF]
    and lc = top_def p
     ["44",EQ_MLDSAVERIFYLENGTHCHECK_MLDSA44;
      "65",EQ_MLDSAVERIFYLENGTHCHECK_MLDSA65;
      "87",EQ_MLDSAVERIFYLENGTHCHECK_MLDSA87]
    and len = top_def p
     ["44",TOP_VERIFY_INTERNAL_LENGTHS_MLDSA44;
      "65",TOP_VERIFY_INTERNAL_LENGTHS_MLDSA65;
      "87",TOP_VERIFY_INTERNAL_LENGTHS_MLDSA87]
    and ver = top_def p
     ["44",EQ_ML_DSA_VERIFY_MLDSA44;
      "65",EQ_ML_DSA_VERIFY_MLDSA65;
      "87",EQ_ML_DSA_VERIFY_MLDSA87] in
    PROVE_HYP ver
    (top_prove [top_tm p STMT_VERIFY]
     (top_tm p STMT_VERIFY_PUBLIC)
     (REPEAT STRIP_TAC THEN REWRITE_TAC(def :: lc :: TOP_MONAD_RULES) THEN
      REWRITE_TAC[TOP_CTX_TOO_LONG; mldsa_verify] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC TOP_MONAD_RULES THEN TOP_INT_EQ_TAC THEN
      ASM_CASES_TAC (top_tm p
        "LENGTH(pk:byte list) = @PK@ /\\ LENGTH(sg:byte list) = @SIG@") THEN
      ASM_SIMP_TAC(mldsa_verify :: TOP_MONAD_RULES) THEN
      ASM_SIMP_TAC(len :: injectivity "native_result" :: TOP_MONAD_RULES))) in
  f "44", f "65", f "87";;

(* ------------------------------------------------------------------------- *)
(* The pre-hash functions of HashML-DSA: OIDBytes, PreHash, PreHashAllowed.  *)
(* ------------------------------------------------------------------------- *)

let TOP_REPLICATE_CONV =
  let th0,th1 = CONJ_PAIR REPLICATE in
  let rec conv tm =
    match tm with
      Comb(Comb(Const("REPLICATE",_),n),_) when is_numeral n ->
        if dest_numeral n =/ num 0 then REWR_CONV th0 tm else
        (LAND_CONV num_CONV THENC REWR_CONV th1 THENC RAND_CONV conv) tm
    | _ -> failwith "TOP_REPLICATE_CONV" in
  conv;;

let TOP_EVAL_TAC rules =
  REPEAT(CHANGED_TAC(REWRITE_TAC rules THEN CONV_TAC INT_REDUCE_CONV THEN
                     CONV_TAC NUM_REDUCE_CONV));;

let EQ_OIDBYTES = prove
 (`!n. OIDBytes_hol (&n) = Value (mldsa_oid n)`,
  GEN_TAC THEN REWRITE_TAC(OIDBytes_hol_DEF :: TOP_MONAD_RULES) THEN
  CONV_TAC(ONCE_DEPTH_CONV TOP_REPLICATE_CONV) THEN
  REWRITE_TAC[typed_hol_int_to_byte_DEF; isa_int_mod; INT_OF_NUM_REM] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[INT_OF_NUM_LT; INT_POS; MOD_LT_EQ; ARITH_RULE `~(256 = 0)`] THEN
  TOP_EVAL_TAC(native_list_update_DEF :: LENGTH :: isa_list_update ::
               TOP_MONAD_RULES) THEN
  REWRITE_TAC[mldsa_oid; GSYM WORD_IWORD; injectivity "native_result";
              CONS_11] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[WORD_EQ; DIMINDEX_8; CONG] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_REFL]);;

(* The digest PH(M) of FIPS 204 Algorithm 4, line 11, for the pre-hash       *)
(* function number n of the generated PreHash: the uninterpreted SHA-2 and   *)
(* SHA-3 hashes of the generated specification, and its SHAKE128/SHAKE256    *)
(* with 256 and 512 bits of output.                                          *)

let top_prehash = new_definition
 `top_prehash n (M:bool list) =
    if n = 1 then SHA256 M else if n = 2 then SHA384 M
    else if n = 3 then SHA512 M else if n = 4 then SHA224 M
    else if n = 5 then SHA512t224 M else if n = 6 then SHA512t256 M
    else if n = 7 then SHA3x224 M else if n = 8 then SHA3x256 M
    else if n = 9 then SHA3x384 M else if n = 10 then SHA3x512 M
    else if n = 11 then SHAKE128 M 256 else SHAKE256 M 512`;;
let TOP_PREHASH_IN = prove
 (`!n M. 1 <= n /\ n <= 12
         ==> PreHash_hol (&n) M = Value (Native_Value (mldsa_oid n, top_prehash n M))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE `1 <= n /\ n <= 12 ==> n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/ n = 11 \/ n = 12`)) THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC(PreHash_hol_DEF :: top_prehash :: TOP_MONAD_RULES) THEN
  CONV_TAC INT_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC(EQ_OIDBYTES :: TOP_MONAD_RULES) THEN
  REWRITE_TAC[mldsa_oid; typed_hol_list_slice_DEF; LENGTH] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC(ISA_NAT_NUM :: TOP_MONAD_RULES) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  TOP_EVAL_TAC(isa_take :: isa_drop :: TOP_MONAD_RULES) THEN
  REWRITE_TAC[SHA256_semantic_DEF; SHA384_semantic_DEF; SHA512_semantic_DEF;
     SHA224_semantic_DEF; SHA512t224_semantic_DEF; SHA512t256_semantic_DEF;
     SHA3x224_semantic_DEF; SHA3x256_semantic_DEF; SHA3x384_semantic_DEF;
     SHA3x512_semantic_DEF; SHAKE128_semantic_DEF; SHAKE256_semantic_DEF;
     UNCURRY_DEF] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC(ISA_NAT_NUM :: TOP_MONAD_RULES));;
let TOP_PREHASH_OUT = prove
 (`!PH M. ~(&1 <= PH /\ PH <= &12) ==> PreHash_hol PH M = Value Native_Bottom`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(PH = &1) /\ ~(PH = &2) /\ ~(PH = &3) /\ ~(PH = &4) /\
                ~(PH = &5) /\ ~(PH = &6) /\ ~(PH = &7) /\ ~(PH = &8) /\
                ~(PH = &9) /\ ~(PH = &10) /\ ~(PH = &11) /\ ~(PH:int = &12)`
  STRIP_ASSUME_TAC THENL [POP_ASSUM MP_TAC THEN INT_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC(PreHash_hol_DEF :: TOP_MONAD_RULES));;
let EQ_PREHASH = prove
 (`!PH M. PreHash_hol PH M =
          if &1 <= PH /\ PH <= &12
          then Value (Native_Value (mldsa_oid (num_of_int PH),
                                    top_prehash (num_of_int PH) M))
          else Value Native_Bottom`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[TOP_PREHASH_OUT] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (INT_ARITH `&1 <= x:int /\ x <= &12 ==> &0 <= x`)) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EXISTS] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[INT_OF_NUM_LE]) THEN
  ASM_SIMP_TAC[NUM_OF_INT_OF_NUM; TOP_PREHASH_IN]);;

(* The pre-hash functions that each parameter set allows (with a collision   *)
(* strength of at least lambda bits).                                        *)

let STMT_PREHASHALLOWED =
 "!PH. PreHashAllowed_@P@_Configuration_hol PH = Value (PH IN @ALLOWED@)";;

let EQ_PREHASHALLOWED_MLDSA44,
    EQ_PREHASHALLOWED_MLDSA65,
    EQ_PREHASHALLOWED_MLDSA87 =
  let f p =
    let def = top_def p
     ["44",PreHashAllowed_MLDSA44_Configuration_hol_DEF;
      "65",PreHashAllowed_MLDSA65_Configuration_hol_DEF;
      "87",PreHashAllowed_MLDSA87_Configuration_hol_DEF] in
    prove(top_tm p STMT_PREHASHALLOWED,
      GEN_TAC THEN REWRITE_TAC(def :: TOP_MONAD_RULES) THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; GSYM COND_RAND;
                  injectivity "native_result"] THEN
      CONV_TAC TAUT) in
  f "44", f "65", f "87";;

let TOP_PREHASHALLOWED_RANGE = prove
 (`!PH:int. PH IN {&1, &2, &3, &6, &8, &9, &10, &11, &12} \/
        PH IN {&2, &3, &9, &10, &12} \/ PH IN {&3, &10, &12}
        ==> ?n. PH = &n /\ 1 <= n /\ n <= 12`,
  GEN_TAC THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(fun th -> EXISTS_TAC `num_of_int PH` THEN MP_TAC th) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* HashML-DSA (FIPS 204 Algorithms 4 and 5).                                 *)
(* ------------------------------------------------------------------------- *)

let STMT_HASH_SIGN =
 "!ent sk M ctx n rnd.
     xof_ok /\\ LENGTH sk = @SK@ /\\ 1 <= n /\\ n <= 12 /\\ ent 0 = SOME rnd
     ==> HashML_DSA_Sign_@P@_Configuration_hol ent sk M ctx (&n) =
         lift_sign_result
          (hash_mldsa_sign @HW@ NONE sk (mldsa_oid n) (top_prehash n M)
                           ctx rnd)";;

let STMT_HASH_VERIFY =
 "!pk M sg ctx n.
     xof_ok /\\ LENGTH pk = @PK@ /\\ LENGTH sg = @SIG@ /\\ 1 <= n /\\ n <= 12
     ==> HashML_DSA_Verify_@P@_Configuration_hol pk M sg ctx (&n) =
         lift_verify_bool
          (hash_mldsa_verify @HW@ pk (mldsa_oid n) (top_prehash n M) sg ctx)";;

let STMT_HASH_SIGN_PUBLIC =
 "!ent sk M ctx PH rnd.
     xof_ok /\\ LENGTH sk = @SK@ /\\ ent 0 = SOME rnd
     ==> HashMLDSASignPublic_@P@_Configuration_hol ent sk M ctx PH =
         if PH IN @ALLOWED@
         then lift_sign_result
               (hash_mldsa_sign @HW@ NONE sk (mldsa_oid (num_of_int PH))
                 (top_prehash (num_of_int PH) M) ctx rnd)
         else Value Native_Bottom";;

let STMT_HASH_VERIFY_PUBLIC =
 "!pk M sg ctx PH.
     xof_ok
     ==> HashMLDSAVerifyPublic_@P@_Configuration_hol pk M sg ctx PH =
         if PH IN @ALLOWED@
         then lift_verify_bool
               (hash_mldsa_verify @HW@ pk (mldsa_oid (num_of_int PH))
                 (top_prehash (num_of_int PH) M) sg ctx)
         else Value F";;

let EQ_HASHML_DSA_SIGN_MLDSA44,
    EQ_HASHML_DSA_SIGN_MLDSA65,
    EQ_HASHML_DSA_SIGN_MLDSA87 =
  let f p =
    let def = top_def p
     ["44",HashML_DSA_Sign_MLDSA44_Configuration_hol_DEF;
      "65",HashML_DSA_Sign_MLDSA65_Configuration_hol_DEF;
      "87",HashML_DSA_Sign_MLDSA87_Configuration_hol_DEF] in
    top_prove [HYP_BYTESTOBITSSTRING; top_tm p STMT_SIGN_INTERNAL]
     (top_tm p STMT_HASH_SIGN)
     (REPEAT STRIP_TAC THEN REWRITE_TAC(def :: TOP_MONAD_RULES) THEN
      REWRITE_TAC[hash_mldsa_sign] THEN TOP_CTX_TAC THEN
      ASM_SIMP_TAC(TOP_PREHASH_IN :: INTEGER_TO_BYTES_1_NUM ::
                   ARITH_RULE `0 < 256 /\ 1 < 256` :: TOP_MONAD_RULES) THEN
      REWRITE_TAC[APPEND; GSYM APPEND_ASSOC] THEN
      ASM_SIMP_TAC(TOP_BIND_SIGN :: TOP_SIGN_INTERNAL_NOT_BAD ::
                   TOP_MONAD_RULES)) in
  f "44", f "65", f "87";;

let EQ_HASHML_DSA_VERIFY_MLDSA44,
    EQ_HASHML_DSA_VERIFY_MLDSA65,
    EQ_HASHML_DSA_VERIFY_MLDSA87 =
  let f p =
    let def = top_def p
     ["44",HashML_DSA_Verify_MLDSA44_Configuration_hol_DEF;
      "65",HashML_DSA_Verify_MLDSA65_Configuration_hol_DEF;
      "87",HashML_DSA_Verify_MLDSA87_Configuration_hol_DEF] in
    top_prove [HYP_BYTESTOBITSSTRING; top_tm p STMT_VERIFY_INTERNAL]
     (top_tm p STMT_HASH_VERIFY)
     (REPEAT STRIP_TAC THEN REWRITE_TAC(def :: TOP_MONAD_RULES) THEN
      REWRITE_TAC[hash_mldsa_verify; GSYM NOT_LT] THEN TOP_CTX_TAC THEN
      ASM_SIMP_TAC(TOP_PREHASH_IN :: INTEGER_TO_BYTES_1_NUM ::
                   ARITH_RULE `0 < 256 /\ 1 < 256` :: TOP_MONAD_RULES) THEN
      REWRITE_TAC[APPEND; GSYM APPEND_ASSOC] THEN
      ASM_SIMP_TAC TOP_MONAD_RULES) in
  f "44", f "65", f "87";;

let TOP_ALLOWED_TAC p =
  ASM_CASES_TAC (top_tm p "(PH:int) IN @ALLOWED@") THEN
  ASM_REWRITE_TAC TOP_MONAD_RULES THEN
  SUBGOAL_THEN `?n. (PH:int) = &n /\ 1 <= n /\ n <= 12` MP_TAC THENL
   [MATCH_MP_TAC TOP_PREHASHALLOWED_RANGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[NUM_OF_INT_OF_NUM];;

let EQ_HASHMLDSASIGNPUBLIC_MLDSA44,
    EQ_HASHMLDSASIGNPUBLIC_MLDSA65,
    EQ_HASHMLDSASIGNPUBLIC_MLDSA87 =
  let f p =
    let def = top_def p
     ["44",HashMLDSASignPublic_MLDSA44_Configuration_hol_DEF;
      "65",HashMLDSASignPublic_MLDSA65_Configuration_hol_DEF;
      "87",HashMLDSASignPublic_MLDSA87_Configuration_hol_DEF]
    and al = top_def p
     ["44",EQ_PREHASHALLOWED_MLDSA44;
      "65",EQ_PREHASHALLOWED_MLDSA65;
      "87",EQ_PREHASHALLOWED_MLDSA87]
    and hs = top_def p
     ["44",EQ_HASHML_DSA_SIGN_MLDSA44;
      "65",EQ_HASHML_DSA_SIGN_MLDSA65;
      "87",EQ_HASHML_DSA_SIGN_MLDSA87] in
    PROVE_HYP hs
    (top_prove [top_tm p STMT_HASH_SIGN]
     (top_tm p STMT_HASH_SIGN_PUBLIC)
     (REPEAT STRIP_TAC THEN REWRITE_TAC(def :: al :: TOP_MONAD_RULES) THEN
      TOP_INT_EQ_TAC THEN TOP_ALLOWED_TAC p THEN
      ASM_SIMP_TAC TOP_MONAD_RULES)) in
  f "44", f "65", f "87";;

let EQ_HASHMLDSAVERIFYPUBLIC_MLDSA44,
    EQ_HASHMLDSAVERIFYPUBLIC_MLDSA65,
    EQ_HASHMLDSAVERIFYPUBLIC_MLDSA87 =
  let f p =
    let def = top_def p
     ["44",HashMLDSAVerifyPublic_MLDSA44_Configuration_hol_DEF;
      "65",HashMLDSAVerifyPublic_MLDSA65_Configuration_hol_DEF;
      "87",HashMLDSAVerifyPublic_MLDSA87_Configuration_hol_DEF]
    and al = top_def p
     ["44",EQ_PREHASHALLOWED_MLDSA44;
      "65",EQ_PREHASHALLOWED_MLDSA65;
      "87",EQ_PREHASHALLOWED_MLDSA87]
    and lc = top_def p
     ["44",EQ_MLDSAVERIFYLENGTHCHECK_MLDSA44;
      "65",EQ_MLDSAVERIFYLENGTHCHECK_MLDSA65;
      "87",EQ_MLDSAVERIFYLENGTHCHECK_MLDSA87]
    and len = top_def p
     ["44",TOP_VERIFY_INTERNAL_LENGTHS_MLDSA44;
      "65",TOP_VERIFY_INTERNAL_LENGTHS_MLDSA65;
      "87",TOP_VERIFY_INTERNAL_LENGTHS_MLDSA87]
    and hv = top_def p
     ["44",EQ_HASHML_DSA_VERIFY_MLDSA44;
      "65",EQ_HASHML_DSA_VERIFY_MLDSA65;
      "87",EQ_HASHML_DSA_VERIFY_MLDSA87] in
    PROVE_HYP hv
    (top_prove [top_tm p STMT_HASH_VERIFY]
     (top_tm p STMT_HASH_VERIFY_PUBLIC)
     (REPEAT STRIP_TAC THEN REWRITE_TAC(def :: al :: lc :: TOP_MONAD_RULES) THEN
      TOP_INT_EQ_TAC THEN TOP_ALLOWED_TAC p THEN
      REWRITE_TAC[TOP_CTX_TOO_LONG; hash_mldsa_verify; GSYM NOT_LT] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC TOP_MONAD_RULES THEN
      ASM_CASES_TAC (top_tm p
        "LENGTH(pk:byte list) = @PK@ /\\ LENGTH(sg:byte list) = @SIG@") THEN
      ASM_SIMP_TAC(hash_mldsa_verify :: GSYM NOT_LT :: TOP_MONAD_RULES) THEN
      ASM_SIMP_TAC(len :: injectivity "native_result" :: TOP_MONAD_RULES))) in
  f "44", f "65", f "87";;
let TOP_NATIVE_WHILE_ACCEPT = prove
 (`!(test:S->(bool)native_result)
    (body:S->((S,R)statement_outcome)native_result)
    (wi:num->S->bool) (rej:num->bool) (Q:num->S->bool).
    (!n s. wi n s ==> test s = Value T) /\
    (!n s. wi n s
           ==> ?s'. body s = Value (Continue s') /\
                    (if rej n then wi (n + 1) s'
                     else test s' = Value F /\ Q n s'))
    ==> !d n s. wi n s /\ ~rej (n + d) /\ (!e. e < d ==> rej (n + e))
                ==> ?s'. native_while (\s. Value (Continue s)) test body s =
                         Value (Continue s') /\ Q (n + d) s'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "T") (LABEL_TAC "B")) THEN
  INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV o LAND_CONV) [NATIVE_WHILE] THEN
  USE_THEN "T" (fun th -> ASSUME_TAC(MATCH_MP th
    (ASSUME `(wi:num->S->bool) n s`))) THEN
  USE_THEN "B" (fun th -> MP_TAC(MATCH_MP th
    (ASSUME `(wi:num->S->bool) n s`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:S` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[NATIVE_BIND; NATIVE_CONTINUE_BIND] THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
    UNDISCH_TAC `if (rej:num->bool) n then wi (n + 1) (t:S)
                 else test t = Value F /\ Q n t` THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
    EXISTS_TAC `t:S` THEN ASM_SIMP_TAC[NATIVE_WHILE_EXIT];
    SUBGOAL_THEN `(rej:num->bool) n` ASSUME_TAC THENL
     [MP_TAC(SPEC `0` (ASSUME `!e. e < SUC d ==> (rej:num->bool) (n + e)`)) THEN
      REWRITE_TAC[ADD_CLAUSES] THEN
      DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `if (rej:num->bool) n then wi (n + 1) (t:S)
                 else test t = Value F /\ Q n t` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`n + 1`; `t:S`] o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "native_while"))
          (concl th))) THEN
    ASM_REWRITE_TAC[ARITH_RULE `(n + 1) + d = n + SUC d`] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `e:num` THEN DISCH_TAC THEN
    MP_TAC(SPEC `SUC e` (ASSUME `!e. e < SUC d ==> (rej:num->bool) (n + e)`)) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[LT_SUC]]);;

let TOP_NATIVE_WHILE = prove
 (`!(test:S->(bool)native_result)
    (body:S->((S,R)statement_outcome)native_result)
    (wi:num->S->bool) (rej:num->bool) (Q:num->S->bool) s0.
    wi 0 s0 /\
    (!n s. wi n s ==> test s = Value T) /\
    (!n s. wi n s
           ==> ?s'. body s = Value (Continue s') /\
                    (if rej n then wi (n + 1) s'
                     else test s' = Value F /\ Q n s'))
    ==> ((!n. rej n)
         ==> native_while (\s. Value (Continue s)) test body s0 =
             Nontermination) /\
        (~(!n. rej n)
         ==> ?s. native_while (\s. Value (Continue s)) test body s0 =
                 Value (Continue s) /\ Q (minimal n. ~rej n) s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "T")
    (LABEL_TAC "B"))) THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`s0:S`; `\(x:S) (n:num). @s'. (body:S->((S,R)statement_outcome)native_result) x = Value (Continue s') /\
                                     (wi:num->S->bool) (n + 1) s'`]
                  num_RECURSION) THEN
    REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `st:num->S` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `!k. (wi:num->S->bool) k (st k)` ASSUME_TAC THENL
     [INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "B" (fun th -> MP_TAC(SELECT_RULE(REWRITE_RULE
        [ASSUME `!n. (rej:num->bool) n`]
        (MATCH_MP th (ASSUME `(wi:num->S->bool) k (st k)`))))) THEN
      SIMP_TAC[ADD1];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
    MATCH_MP_TAC NATIVE_WHILE_DIVERGE THEN GEN_TAC THEN CONJ_TAC THENL
     [USE_THEN "T" MATCH_MP_TAC THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "B" (fun th -> MP_TAC(SELECT_RULE(REWRITE_RULE
        [ASSUME `!n. (rej:num->bool) n`]
        (MATCH_MP th (SPEC `k:num`
          (ASSUME `!k. (wi:num->S->bool) k (st k)`)))))) THEN
    MESON_TAC[];
    MP_TAC(ISPECL [`test:S->(bool)native_result`;
                   `body:S->((S,R)statement_outcome)native_result`;
                   `wi:num->S->bool`; `rej:num->bool`; `Q:num->S->bool`]
                  TOP_NATIVE_WHILE_ACCEPT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`minimal n. ~(rej:num->bool) n`; `0`; `s0:S`]) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPEC `\n. ~(rej:num->bool) n` MINIMAL) THEN
    ASM_REWRITE_TAC[GSYM NOT_FORALL_THM] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* H on byte strings, through BytesToBitsString.                             *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* ML_DSA_Verify_internal is ML_DSA_Verify_internal_mu with mu = H(tr || M). *)
(* The two generated definitions have their own copies (callables) of the    *)
(* local helpers, with the same bodies.                                      *)
(* ------------------------------------------------------------------------- *)

let TOP_CALLABLE_EQ defs tm =
  prove(tm, REPEAT GEN_TAC THEN REWRITE_TAC defs);;

let TOP_VERIFY_INTERNAL_VIA_MU_MLDSA44 =
  let ceq k args =
    let c s = "ML_DSA_Verify_internal_"^s^"MLDSA44_Configuration_callable_"^k^"_call" in
    parse_term("!"^args^". "^c ""^" "^args^" = "^c "mu_"^" "^args) in
  let eqs =
   [TOP_CALLABLE_EQ
     [ML_DSA_Verify_internal_MLDSA44_Configuration_callable_2_0_call_DEF;
      ML_DSA_Verify_internal_mu_MLDSA44_Configuration_callable_2_0_call_DEF]
     (ceq "2_0" "x");
    TOP_CALLABLE_EQ
     [ML_DSA_Verify_internal_MLDSA44_Configuration_callable_1_0_call_DEF;
      ML_DSA_Verify_internal_mu_MLDSA44_Configuration_callable_1_0_call_DEF]
     (ceq "1_0" "x y");
    TOP_CALLABLE_EQ
     [ML_DSA_Verify_internal_MLDSA44_Configuration_callable_0_0_call_DEF;
      ML_DSA_Verify_internal_mu_MLDSA44_Configuration_callable_0_0_call_DEF]
     (ceq "0_0" "x y")] in
  top_prove [HYP_BYTESTOBITSSTRING]
   `!pk m sg. xof_ok
              ==> ML_DSA_Verify_internal_MLDSA44_Configuration_hol
                    pk (bits_of_bytes m) sg =
                  ML_DSA_Verify_internal_mu_MLDSA44_Configuration_hol pk
                    (mldsa_h (APPEND (mldsa_h pk 64) m) 64) sg`
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC([ML_DSA_Verify_internal_MLDSA44_Configuration_hol_DEF;
                 ML_DSA_Verify_internal_mu_MLDSA44_Configuration_hol_DEF] @ eqs) THEN
    REWRITE_TAC TOP_MONAD_RULES THEN
    ASM_SIMP_TAC(BALL_HBYTESSTRING :: TOP_MONAD_RULES) THEN
    REWRITE_TAC[GSYM BITS_OF_BYTES_APPEND] THEN
    ASM_SIMP_TAC(EQ_H_HOL :: TOP_MONAD_RULES));;

let TOP_VERIFY_INTERNAL_VIA_MU_MLDSA65 =
  let ceq k args =
    let c s = "ML_DSA_Verify_internal_"^s^"MLDSA65_Configuration_callable_"^k^"_call" in
    parse_term("!"^args^". "^c ""^" "^args^" = "^c "mu_"^" "^args) in
  let eqs =
   [TOP_CALLABLE_EQ
     [ML_DSA_Verify_internal_MLDSA65_Configuration_callable_2_0_call_DEF;
      ML_DSA_Verify_internal_mu_MLDSA65_Configuration_callable_2_0_call_DEF]
     (ceq "2_0" "x");
    TOP_CALLABLE_EQ
     [ML_DSA_Verify_internal_MLDSA65_Configuration_callable_1_0_call_DEF;
      ML_DSA_Verify_internal_mu_MLDSA65_Configuration_callable_1_0_call_DEF]
     (ceq "1_0" "x y");
    TOP_CALLABLE_EQ
     [ML_DSA_Verify_internal_MLDSA65_Configuration_callable_0_0_call_DEF;
      ML_DSA_Verify_internal_mu_MLDSA65_Configuration_callable_0_0_call_DEF]
     (ceq "0_0" "x y")] in
  top_prove [HYP_BYTESTOBITSSTRING]
   `!pk m sg. xof_ok
              ==> ML_DSA_Verify_internal_MLDSA65_Configuration_hol
                    pk (bits_of_bytes m) sg =
                  ML_DSA_Verify_internal_mu_MLDSA65_Configuration_hol pk
                    (mldsa_h (APPEND (mldsa_h pk 64) m) 64) sg`
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC([ML_DSA_Verify_internal_MLDSA65_Configuration_hol_DEF;
                 ML_DSA_Verify_internal_mu_MLDSA65_Configuration_hol_DEF] @ eqs) THEN
    REWRITE_TAC TOP_MONAD_RULES THEN
    ASM_SIMP_TAC(BALL_HBYTESSTRING :: TOP_MONAD_RULES) THEN
    REWRITE_TAC[GSYM BITS_OF_BYTES_APPEND] THEN
    ASM_SIMP_TAC(EQ_H_HOL :: TOP_MONAD_RULES));;

let TOP_VERIFY_INTERNAL_VIA_MU_MLDSA87 =
  let ceq k args =
    let c s = "ML_DSA_Verify_internal_"^s^"MLDSA87_Configuration_callable_"^k^"_call" in
    parse_term("!"^args^". "^c ""^" "^args^" = "^c "mu_"^" "^args) in
  let eqs =
   [TOP_CALLABLE_EQ
     [ML_DSA_Verify_internal_MLDSA87_Configuration_callable_2_0_call_DEF;
      ML_DSA_Verify_internal_mu_MLDSA87_Configuration_callable_2_0_call_DEF]
     (ceq "2_0" "x");
    TOP_CALLABLE_EQ
     [ML_DSA_Verify_internal_MLDSA87_Configuration_callable_1_0_call_DEF;
      ML_DSA_Verify_internal_mu_MLDSA87_Configuration_callable_1_0_call_DEF]
     (ceq "1_0" "x y");
    TOP_CALLABLE_EQ
     [ML_DSA_Verify_internal_MLDSA87_Configuration_callable_0_0_call_DEF;
      ML_DSA_Verify_internal_mu_MLDSA87_Configuration_callable_0_0_call_DEF]
     (ceq "0_0" "x y")] in
  top_prove [HYP_BYTESTOBITSSTRING]
   `!pk m sg. xof_ok
              ==> ML_DSA_Verify_internal_MLDSA87_Configuration_hol
                    pk (bits_of_bytes m) sg =
                  ML_DSA_Verify_internal_mu_MLDSA87_Configuration_hol pk
                    (mldsa_h (APPEND (mldsa_h pk 64) m) 64) sg`
   (REPEAT STRIP_TAC THEN
    REWRITE_TAC([ML_DSA_Verify_internal_MLDSA87_Configuration_hol_DEF;
                 ML_DSA_Verify_internal_mu_MLDSA87_Configuration_hol_DEF] @ eqs) THEN
    REWRITE_TAC TOP_MONAD_RULES THEN
    ASM_SIMP_TAC(BALL_HBYTESSTRING :: TOP_MONAD_RULES) THEN
    REWRITE_TAC[GSYM BITS_OF_BYTES_APPEND] THEN
    ASM_SIMP_TAC(EQ_H_HOL :: TOP_MONAD_RULES));;

let EQ_ML_DSA_VERIFY_INTERNAL_MLDSA44,
    EQ_ML_DSA_VERIFY_INTERNAL_MLDSA65,
    EQ_ML_DSA_VERIFY_INTERNAL_MLDSA87 =
  let f p th =
    top_prove [HYP_BYTESTOBITSSTRING; top_tm p STMT_VERIFY_INTERNAL_MU]
     (top_tm p STMT_VERIFY_INTERNAL)
     (REPEAT STRIP_TAC THEN ASM_SIMP_TAC[th; mldsa_verify_internal]) in
  f "44" TOP_VERIFY_INTERNAL_VIA_MU_MLDSA44,
  f "65" TOP_VERIFY_INTERNAL_VIA_MU_MLDSA65,
  f "87" TOP_VERIFY_INTERNAL_VIA_MU_MLDSA87;;


(* ------------------------------------------------------------------------- *)
(* Helpers for the abstract signing loop lemmas, which sign.ml proves   *)
(* (Sign_internal_mu and Sign_internal: given one Value equation per         *)
(* component call, the loop returns the signature of the first accepted      *)
(* attempt, or does not terminate).                                          *)
(* ------------------------------------------------------------------------- *)


let TOP_BIND_COND = prove
 (`!c (a:(A)native_result) b (f:A->(B)native_result).
     native_bind (if c then a else b) f =
     if c then native_bind a f else native_bind b f`,
  MESON_TAC[]);;
let SIGN44_EXT = [
  ML_DSA_Sign_internal_mu_MLDSA44_Configuration_hol_emitted_rho''_EXT;
  ML_DSA_Sign_internal_mu_MLDSA44_Configuration_hol_emitted_kappa_EXT;
  ML_DSA_Sign_internal_mu_MLDSA44_Configuration_hol_emitted_A_NTT_EXT;
  ML_DSA_Sign_internal_mu_MLDSA44_Configuration_hol_emitted_s1_NTT_EXT;
  ML_DSA_Sign_internal_mu_MLDSA44_Configuration_hol_emitted_s2_NTT_EXT;
  ML_DSA_Sign_internal_mu_MLDSA44_Configuration_hol_emitted_t0_NTT_EXT;
  ML_DSA_Sign_internal_mu_MLDSA44_Configuration_hol_emitted_z_EXT;
  ML_DSA_Sign_internal_mu_MLDSA44_Configuration_hol_emitted_h_EXT;
  ML_DSA_Sign_internal_mu_MLDSA44_Configuration_hol_emitted_c_tilde_EXT];;
let sign44_wi = `\n s.
   ML_DSA_Sign_internal_mu_MLDSA44_Configuration_hol_emitted_rho'' s = Native_Assigned (rho2:byte list) /\
   ML_DSA_Sign_internal_mu_MLDSA44_Configuration_hol_emitted_kappa s = Native_Assigned (&(4 * n)) /\
   ML_DSA_Sign_internal_mu_MLDSA44_Configuration_hol_emitted_A_NTT s = Native_Assigned A /\
   ML_DSA_Sign_internal_mu_MLDSA44_Configuration_hol_emitted_s1_NTT s = Native_Assigned S1 /\
   ML_DSA_Sign_internal_mu_MLDSA44_Configuration_hol_emitted_s2_NTT s = Native_Assigned S2 /\
   ML_DSA_Sign_internal_mu_MLDSA44_Configuration_hol_emitted_t0_NTT s = Native_Assigned T0 /\
   ML_DSA_Sign_internal_mu_MLDSA44_Configuration_hol_emitted_z s = Native_Assigned Native_Bottom /\
   ML_DSA_Sign_internal_mu_MLDSA44_Configuration_hol_emitted_h s = Native_Assigned Native_Bottom`;;
let sign44_Q = `\n s.
   ML_DSA_Sign_internal_mu_MLDSA44_Configuration_hol_emitted_c_tilde s = Native_Assigned ((CT:num->byte list) n) /\
   ML_DSA_Sign_internal_mu_MLDSA44_Configuration_hol_emitted_z s = Native_Assigned (Native_Value (Z n)) /\
   ML_DSA_Sign_internal_mu_MLDSA44_Configuration_hol_emitted_h s = Native_Assigned (Native_Value (HV n))`;;
let sign44_rej = `\n. ~((acc:num->bool) n)`;;
let TOP_WHILE_TAC wi rej q (asl,w) =
  let nw = rand(rator(lhand w)) in
  let s0 = rand nw and body = rand(rator nw) and test = rand(rator(rator nw)) in
  MP_TAC(ISPECL [test; body; wi; rej; q; s0] TOP_NATIVE_WHILE) (asl,w);;

let TOP_SIGN_LOOP_HYPS_44 = `
  skDecode_MLDSA44_Configuration_hol sk = Value (rho,K,tr,s1,s2,t0) /\
  LENGTH rho = 32 /\ LENGTH K = 32 /\ LENGTH tr = 64 /\
  ML_DSA_Sign_internal_mu_MLDSA44_Configuration_callable_5_0_call (Native_Value s1) = Value S1 /\
  ML_DSA_Sign_internal_mu_MLDSA44_Configuration_callable_5_0_call (Native_Value s2) = Value S2 /\
  ML_DSA_Sign_internal_mu_MLDSA44_Configuration_callable_5_0_call (Native_Value t0) = Value T0 /\
  ML_DSA_Sign_internal_mu_MLDSA44_Configuration_callable_4_0_call (Native_Value rho) = Value A /\
  HBytesString_hol (APPEND (APPEND K rnd) mu) (&64) = Value rho2 /\ LENGTH rho2 = 64 /\
  (!n. ExpandMask_MLDSA44_Configuration_hol rho2 (&(4 * n)) = Value (Y n)) /\
  (!n. IntVectorToRq_4_body_hol (Y n) = Value (Yq n)) /\
  (!n. VectorNTT_4_MLDSA44_Configuration_hol (Yq n) = Value (Yh n)) /\
  (!n. MatrixVectorNTT_4_4_MLDSA44_Configuration_hol A (Yh n) = Value (Wh n)) /\
  (!n. VectorNTTInv_4_MLDSA44_Configuration_hol (Wh n) = Value (W n)) /\
  (!n. FixedVectorHighBits_4_MLDSA44_Configuration_hol (W n) = Value (W1 n)) /\
  (!n. w1Encode_MLDSA44_Configuration_hol (W1 n) = Value (Native_Value (W1E n))) /\
  (!n. HBytesString_hol (APPEND mu (W1E n)) (&32) = Value (CT n)) /\
  (!n. SampleInBall_MLDSA44_Configuration_hol (CT n) = Value (C n)) /\
  (!n. IntPolyToRq_hol (C n) = Value (Cq n)) /\
  (!n. NTT_hol (Cq n) = Value (Ch n)) /\
  (!n. ScalarVectorNTT_4_MLDSA44_Configuration_hol (Ch n) S1 = Value (CS1h n)) /\
  (!n. VectorNTTInv_4_MLDSA44_Configuration_hol (CS1h n) = Value (CS1 n)) /\
  (!n. ScalarVectorNTT_4_MLDSA44_Configuration_hol (Ch n) S2 = Value (CS2h n)) /\
  (!n. VectorNTTInv_4_MLDSA44_Configuration_hol (CS2h n) = Value (CS2 n)) /\
  (!n. RqVectorAdd_4_hol (Yq n) (CS1 n) = Value (Z n)) /\
  (!n. FixedVectorSubtract_4_FIPS204_Time_hol (W n) (CS2 n) = Value (R n)) /\
  (!n. FixedVectorLowBits_4_MLDSA44_Configuration_hol (R n) = Value (R0 n)) /\
  (!n. ML_DSA_Sign_internal_mu_MLDSA44_Configuration_callable_3_0_call (Native_Value (Z n)) = Value (NZ n)) /\
  (!n. IntVectorInfNorm_4_hol (R0 n) = Value (NR n)) /\
  (!n. ScalarVectorNTT_4_MLDSA44_Configuration_hol (Ch n) T0 = Value (CT0h n)) /\
  (!n. VectorNTTInv_4_MLDSA44_Configuration_hol (CT0h n) = Value (CT0 n)) /\
  (!n. RqVectorNegate_4_hol (CT0 n) = Value (NCT0 n)) /\
  (!n. RqVectorAdd_4_hol (R n) (CT0 n) = Value (RC n)) /\
  (!n. FixedVectorMakeHint_4_MLDSA44_Configuration_hol (NCT0 n) (RC n) = Value (HV n)) /\
  (!n. ML_DSA_Sign_internal_mu_MLDSA44_Configuration_callable_3_0_call (Native_Value (CT0 n)) = Value (NCT n)) /\
  (!n. ML_DSA_Sign_internal_mu_MLDSA44_Configuration_callable_2_0_call (Native_Value (HV n)) = Value (CNT n)) /\
  (!n. ML_DSA_Sign_internal_mu_MLDSA44_Configuration_callable_1_0_call (Native_Value (Z n)) (&8380417) = Value (Native_Value (ZC n))) /\
  (!n. ML_DSA_Sign_internal_mu_MLDSA44_Configuration_callable_0_0_call (CT n) (Native_Value (ZC n)) (Native_Value (HV n)) = Value (SIG n)) /\
  (!n. acc n <=> ~((&0 <= NZ n - &130994 \/ &0 <= NR n - &95154) \/
                   (&0 <= NCT n - &95232 \/ &0 < CNT n - &80)))`;;


(* ML-DSA-65                                                                 *)
let SIGN65_EXT = [
  ML_DSA_Sign_internal_mu_MLDSA65_Configuration_hol_emitted_rho''_EXT;
  ML_DSA_Sign_internal_mu_MLDSA65_Configuration_hol_emitted_kappa_EXT;
  ML_DSA_Sign_internal_mu_MLDSA65_Configuration_hol_emitted_A_NTT_EXT;
  ML_DSA_Sign_internal_mu_MLDSA65_Configuration_hol_emitted_s1_NTT_EXT;
  ML_DSA_Sign_internal_mu_MLDSA65_Configuration_hol_emitted_s2_NTT_EXT;
  ML_DSA_Sign_internal_mu_MLDSA65_Configuration_hol_emitted_t0_NTT_EXT;
  ML_DSA_Sign_internal_mu_MLDSA65_Configuration_hol_emitted_z_EXT;
  ML_DSA_Sign_internal_mu_MLDSA65_Configuration_hol_emitted_h_EXT;
  ML_DSA_Sign_internal_mu_MLDSA65_Configuration_hol_emitted_c_tilde_EXT];;
let sign65_wi = `\n s.
   ML_DSA_Sign_internal_mu_MLDSA65_Configuration_hol_emitted_rho'' s = Native_Assigned (rho2:byte list) /\
   ML_DSA_Sign_internal_mu_MLDSA65_Configuration_hol_emitted_kappa s = Native_Assigned (&(5 * n)) /\
   ML_DSA_Sign_internal_mu_MLDSA65_Configuration_hol_emitted_A_NTT s = Native_Assigned A /\
   ML_DSA_Sign_internal_mu_MLDSA65_Configuration_hol_emitted_s1_NTT s = Native_Assigned S1 /\
   ML_DSA_Sign_internal_mu_MLDSA65_Configuration_hol_emitted_s2_NTT s = Native_Assigned S2 /\
   ML_DSA_Sign_internal_mu_MLDSA65_Configuration_hol_emitted_t0_NTT s = Native_Assigned T0 /\
   ML_DSA_Sign_internal_mu_MLDSA65_Configuration_hol_emitted_z s = Native_Assigned Native_Bottom /\
   ML_DSA_Sign_internal_mu_MLDSA65_Configuration_hol_emitted_h s = Native_Assigned Native_Bottom`;;
let sign65_Q = `\n s.
   ML_DSA_Sign_internal_mu_MLDSA65_Configuration_hol_emitted_c_tilde s = Native_Assigned ((CT:num->byte list) n) /\
   ML_DSA_Sign_internal_mu_MLDSA65_Configuration_hol_emitted_z s = Native_Assigned (Native_Value (Z n)) /\
   ML_DSA_Sign_internal_mu_MLDSA65_Configuration_hol_emitted_h s = Native_Assigned (Native_Value (HV n))`;;
let sign65_rej = `\n. ~((acc:num->bool) n)`;;

let TOP_SIGN_LOOP_HYPS_65 = `
  skDecode_MLDSA65_Configuration_hol sk = Value (rho,K,tr,s1,s2,t0) /\
  LENGTH rho = 32 /\ LENGTH K = 32 /\ LENGTH tr = 64 /\
  ML_DSA_Sign_internal_mu_MLDSA65_Configuration_callable_6_0_call (Native_Value s1) = Value S1 /\
  ML_DSA_Sign_internal_mu_MLDSA65_Configuration_callable_5_0_call (Native_Value s2) = Value S2 /\
  ML_DSA_Sign_internal_mu_MLDSA65_Configuration_callable_5_0_call (Native_Value t0) = Value T0 /\
  ML_DSA_Sign_internal_mu_MLDSA65_Configuration_callable_4_0_call (Native_Value rho) = Value A /\
  HBytesString_hol (APPEND (APPEND K rnd) mu) (&64) = Value rho2 /\ LENGTH rho2 = 64 /\
  (!n. ExpandMask_MLDSA65_Configuration_hol rho2 (&(5 * n)) = Value (Y n)) /\
  (!n. IntVectorToRq_5_body_hol (Y n) = Value (Yq n)) /\
  (!n. VectorNTT_5_MLDSA65_Configuration_hol (Yq n) = Value (Yh n)) /\
  (!n. MatrixVectorNTT_6_5_MLDSA65_Configuration_hol A (Yh n) = Value (Wh n)) /\
  (!n. VectorNTTInv_6_MLDSA65_Configuration_hol (Wh n) = Value (W n)) /\
  (!n. FixedVectorHighBits_6_MLDSA65_Configuration_hol (W n) = Value (W1 n)) /\
  (!n. w1Encode_MLDSA65_Configuration_hol (W1 n) = Value (Native_Value (W1E n))) /\
  (!n. HBytesString_hol (APPEND mu (W1E n)) (&48) = Value (CT n)) /\
  (!n. SampleInBall_MLDSA65_Configuration_hol (CT n) = Value (C n)) /\
  (!n. IntPolyToRq_hol (C n) = Value (Cq n)) /\
  (!n. NTT_hol (Cq n) = Value (Ch n)) /\
  (!n. ScalarVectorNTT_5_MLDSA65_Configuration_hol (Ch n) S1 = Value (CS1h n)) /\
  (!n. VectorNTTInv_5_MLDSA65_Configuration_hol (CS1h n) = Value (CS1 n)) /\
  (!n. ScalarVectorNTT_6_MLDSA65_Configuration_hol (Ch n) S2 = Value (CS2h n)) /\
  (!n. VectorNTTInv_6_MLDSA65_Configuration_hol (CS2h n) = Value (CS2 n)) /\
  (!n. RqVectorAdd_5_hol (Yq n) (CS1 n) = Value (Z n)) /\
  (!n. FixedVectorSubtract_6_FIPS204_Time_hol (W n) (CS2 n) = Value (R n)) /\
  (!n. FixedVectorLowBits_6_MLDSA65_Configuration_hol (R n) = Value (R0 n)) /\
  (!n. ML_DSA_Sign_internal_mu_MLDSA65_Configuration_callable_3_0_call (Native_Value (Z n)) = Value (NZ n)) /\
  (!n. IntVectorInfNorm_6_hol (R0 n) = Value (NR n)) /\
  (!n. ScalarVectorNTT_6_MLDSA65_Configuration_hol (Ch n) T0 = Value (CT0h n)) /\
  (!n. VectorNTTInv_6_MLDSA65_Configuration_hol (CT0h n) = Value (CT0 n)) /\
  (!n. RqVectorNegate_6_hol (CT0 n) = Value (NCT0 n)) /\
  (!n. RqVectorAdd_6_hol (R n) (CT0 n) = Value (RC n)) /\
  (!n. FixedVectorMakeHint_6_MLDSA65_Configuration_hol (NCT0 n) (RC n) = Value (HV n)) /\
  (!n. RqVectorInfNorm_6_hol (CT0 n) = Value (NCT n)) /\
  (!n. ML_DSA_Sign_internal_mu_MLDSA65_Configuration_callable_2_0_call (Native_Value (HV n)) = Value (CNT n)) /\
  (!n. ML_DSA_Sign_internal_mu_MLDSA65_Configuration_callable_1_0_call (Native_Value (Z n)) (&8380417) = Value (Native_Value (ZC n))) /\
  (!n. ML_DSA_Sign_internal_mu_MLDSA65_Configuration_callable_0_0_call (CT n) (Native_Value (ZC n)) (Native_Value (HV n)) = Value (SIG n)) /\
  (!n. acc n <=> ~((&0 <= NZ n - &524092 \/ &0 <= NR n - &261692) \/
                   (&0 <= NCT n - &261888 \/ &0 < CNT n - &55)))`;;


(* ML-DSA-87                                                                 *)
let SIGN87_EXT = [
  ML_DSA_Sign_internal_mu_MLDSA87_Configuration_hol_emitted_rho''_EXT;
  ML_DSA_Sign_internal_mu_MLDSA87_Configuration_hol_emitted_kappa_EXT;
  ML_DSA_Sign_internal_mu_MLDSA87_Configuration_hol_emitted_A_NTT_EXT;
  ML_DSA_Sign_internal_mu_MLDSA87_Configuration_hol_emitted_s1_NTT_EXT;
  ML_DSA_Sign_internal_mu_MLDSA87_Configuration_hol_emitted_s2_NTT_EXT;
  ML_DSA_Sign_internal_mu_MLDSA87_Configuration_hol_emitted_t0_NTT_EXT;
  ML_DSA_Sign_internal_mu_MLDSA87_Configuration_hol_emitted_z_EXT;
  ML_DSA_Sign_internal_mu_MLDSA87_Configuration_hol_emitted_h_EXT;
  ML_DSA_Sign_internal_mu_MLDSA87_Configuration_hol_emitted_c_tilde_EXT];;
let sign87_wi = `\n s.
   ML_DSA_Sign_internal_mu_MLDSA87_Configuration_hol_emitted_rho'' s = Native_Assigned (rho2:byte list) /\
   ML_DSA_Sign_internal_mu_MLDSA87_Configuration_hol_emitted_kappa s = Native_Assigned (&(7 * n)) /\
   ML_DSA_Sign_internal_mu_MLDSA87_Configuration_hol_emitted_A_NTT s = Native_Assigned A /\
   ML_DSA_Sign_internal_mu_MLDSA87_Configuration_hol_emitted_s1_NTT s = Native_Assigned S1 /\
   ML_DSA_Sign_internal_mu_MLDSA87_Configuration_hol_emitted_s2_NTT s = Native_Assigned S2 /\
   ML_DSA_Sign_internal_mu_MLDSA87_Configuration_hol_emitted_t0_NTT s = Native_Assigned T0 /\
   ML_DSA_Sign_internal_mu_MLDSA87_Configuration_hol_emitted_z s = Native_Assigned Native_Bottom /\
   ML_DSA_Sign_internal_mu_MLDSA87_Configuration_hol_emitted_h s = Native_Assigned Native_Bottom`;;
let sign87_Q = `\n s.
   ML_DSA_Sign_internal_mu_MLDSA87_Configuration_hol_emitted_c_tilde s = Native_Assigned ((CT:num->byte list) n) /\
   ML_DSA_Sign_internal_mu_MLDSA87_Configuration_hol_emitted_z s = Native_Assigned (Native_Value (Z n)) /\
   ML_DSA_Sign_internal_mu_MLDSA87_Configuration_hol_emitted_h s = Native_Assigned (Native_Value (HV n))`;;
let sign87_rej = `\n. ~((acc:num->bool) n)`;;

let TOP_SIGN_LOOP_HYPS_87 = `
  skDecode_MLDSA87_Configuration_hol sk = Value (rho,K,tr,s1,s2,t0) /\
  LENGTH rho = 32 /\ LENGTH K = 32 /\ LENGTH tr = 64 /\
  ML_DSA_Sign_internal_mu_MLDSA87_Configuration_callable_6_0_call (Native_Value s1) = Value S1 /\
  ML_DSA_Sign_internal_mu_MLDSA87_Configuration_callable_5_0_call (Native_Value s2) = Value S2 /\
  ML_DSA_Sign_internal_mu_MLDSA87_Configuration_callable_5_0_call (Native_Value t0) = Value T0 /\
  ML_DSA_Sign_internal_mu_MLDSA87_Configuration_callable_4_0_call (Native_Value rho) = Value A /\
  HBytesString_hol (APPEND (APPEND K rnd) mu) (&64) = Value rho2 /\ LENGTH rho2 = 64 /\
  (!n. ExpandMask_MLDSA87_Configuration_hol rho2 (&(7 * n)) = Value (Y n)) /\
  (!n. IntVectorToRq_7_body_hol (Y n) = Value (Yq n)) /\
  (!n. VectorNTT_7_MLDSA87_Configuration_hol (Yq n) = Value (Yh n)) /\
  (!n. MatrixVectorNTT_8_7_MLDSA87_Configuration_hol A (Yh n) = Value (Wh n)) /\
  (!n. VectorNTTInv_8_MLDSA87_Configuration_hol (Wh n) = Value (W n)) /\
  (!n. FixedVectorHighBits_8_MLDSA87_Configuration_hol (W n) = Value (W1 n)) /\
  (!n. w1Encode_MLDSA87_Configuration_hol (W1 n) = Value (Native_Value (W1E n))) /\
  (!n. HBytesString_hol (APPEND mu (W1E n)) (&64) = Value (CT n)) /\
  (!n. SampleInBall_MLDSA87_Configuration_hol (CT n) = Value (C n)) /\
  (!n. IntPolyToRq_hol (C n) = Value (Cq n)) /\
  (!n. NTT_hol (Cq n) = Value (Ch n)) /\
  (!n. ScalarVectorNTT_7_MLDSA87_Configuration_hol (Ch n) S1 = Value (CS1h n)) /\
  (!n. VectorNTTInv_7_MLDSA87_Configuration_hol (CS1h n) = Value (CS1 n)) /\
  (!n. ScalarVectorNTT_8_MLDSA87_Configuration_hol (Ch n) S2 = Value (CS2h n)) /\
  (!n. VectorNTTInv_8_MLDSA87_Configuration_hol (CS2h n) = Value (CS2 n)) /\
  (!n. RqVectorAdd_7_hol (Yq n) (CS1 n) = Value (Z n)) /\
  (!n. FixedVectorSubtract_8_FIPS204_Time_hol (W n) (CS2 n) = Value (R n)) /\
  (!n. FixedVectorLowBits_8_MLDSA87_Configuration_hol (R n) = Value (R0 n)) /\
  (!n. ML_DSA_Sign_internal_mu_MLDSA87_Configuration_callable_3_0_call (Native_Value (Z n)) = Value (NZ n)) /\
  (!n. IntVectorInfNorm_8_hol (R0 n) = Value (NR n)) /\
  (!n. ScalarVectorNTT_8_MLDSA87_Configuration_hol (Ch n) T0 = Value (CT0h n)) /\
  (!n. VectorNTTInv_8_MLDSA87_Configuration_hol (CT0h n) = Value (CT0 n)) /\
  (!n. RqVectorNegate_8_hol (CT0 n) = Value (NCT0 n)) /\
  (!n. RqVectorAdd_8_hol (R n) (CT0 n) = Value (RC n)) /\
  (!n. FixedVectorMakeHint_8_MLDSA87_Configuration_hol (NCT0 n) (RC n) = Value (HV n)) /\
  (!n. RqVectorInfNorm_8_hol (CT0 n) = Value (NCT n)) /\
  (!n. ML_DSA_Sign_internal_mu_MLDSA87_Configuration_callable_2_0_call (Native_Value (HV n)) = Value (CNT n)) /\
  (!n. ML_DSA_Sign_internal_mu_MLDSA87_Configuration_callable_1_0_call (Native_Value (Z n)) (&8380417) = Value (Native_Value (ZC n))) /\
  (!n. ML_DSA_Sign_internal_mu_MLDSA87_Configuration_callable_0_0_call (CT n) (Native_Value (ZC n)) (Native_Value (HV n)) = Value (SIG n)) /\
  (!n. acc n <=> ~((&0 <= NZ n - &524168 \/ &0 <= NR n - &261768) \/
                   (&0 <= NCT n - &261888 \/ &0 < CNT n - &75)))`;;


(* ------------------------------------------------------------------------- *)
(* Verify_internal_mu from one Value equation per component call.            *)
(* ------------------------------------------------------------------------- *)

let top_bounds p =
  match p with
    "44" -> ["@ZB@","130994"; "@RB@","95154"; "@G2@","95232"; "@OM@","80"; "@CTL@","32"]
  | "65" -> ["@ZB@","524092"; "@RB@","261692"; "@G2@","261888"; "@OM@","55"; "@CTL@","48"]
  | "87" -> ["@ZB@","524168"; "@RB@","261768"; "@G2@","261888"; "@OM@","75"; "@CTL@","64"]
  | _ -> failwith "top_bounds";;
let top_tmx p s = parse_term (top_subst (top_bounds p @ top_params p) s);;

let TOP_VERIFY_MU_HYPS =
 "pkDecode_@P@_Configuration_hol pk = Value PD /\\
  DecodedPublicKeyStrings_@K@_@P@_Configuration_body_hol PD =
    Value (Native_Value (rho,T1)) /\\ LENGTH rho = 32 /\\
  sigDecode_@P@_Configuration_hol sg = Value (CT,Zv,HH) /\\
  ML_DSA_Verify_internal_mu_@P@_Configuration_callable_2_0_call (Native_Value rho) = Value A /\\
  SampleInBall_@P@_Configuration_hol CT = Value C /\\
  IntPolyToRq_hol C = Value Cq /\\
  IntVectorNTT_@L@_hol Zv = Value Zh /\\
  MatrixVectorNTT_@K@_@L@_@P@_Configuration_hol A Zh = Value AZ /\\
  NTT_hol Cq = Value Ch /\\
  ML_DSA_Verify_internal_mu_@P@_Configuration_callable_1_0_call (Native_Value T1) (&8192) = Value T1S /\\
  IntVectorNTT_@K@_hol T1S = Value T1h /\\
  ScalarVectorNTT_@K@_@P@_Configuration_hol Ch T1h = Value CT1h /\\
  FixedVectorSubtract_@K@_FIPS204_NTT_hol AZ CT1h = Value Wa /\\
  VectorNTTInv_@K@_@P@_Configuration_hol Wa = Value Wp /\\
  ML_DSA_Verify_internal_mu_@P@_Configuration_callable_0_0_call HH Wp = Value W1 /\\
  w1Encode_@P@_Configuration_hol W1 = Value (Native_Value W1E) /\\
  HBytesString_hol (APPEND mu W1E) (&@CTL@) = Value CT2 /\\
  IntVectorInfNorm_@L@_hol Zv = Value NZ";;
let TOP_VERIFY_MU_CONCL =
 "ML_DSA_Verify_internal_mu_@P@_Configuration_hol pk mu sg =
  Value (if HH = Native_Bottom then F else NZ < &@ZB@ /\\ CT = CT2)";;
let TOP_VERIFY_MU_ABS p =
  top_tmx p ("(" ^ TOP_VERIFY_MU_HYPS ^ ") ==> (" ^ TOP_VERIFY_MU_CONCL ^ ")");;


let TOP_VERIFY_MU_ABSTRACT_44, TOP_VERIFY_MU_ABSTRACT_65, TOP_VERIFY_MU_ABSTRACT_87 =
  let f p def =
    prove(TOP_VERIFY_MU_ABS p,
      STRIP_TAC THEN REWRITE_TAC[def] THEN
      REWRITE_TAC TOP_MONAD_RULES THEN ASM_REWRITE_TAC TOP_MONAD_RULES THEN
      TOP_ARITH_TAC THEN ASM_SIMP_TAC(typed_hol_bottom_sequence_extent_DEF :: TOP_MONAD_RULES) THEN
      COND_CASES_TAC THEN REWRITE_TAC[]) in
  f "44" ML_DSA_Verify_internal_mu_MLDSA44_Configuration_hol_DEF,
  f "65" ML_DSA_Verify_internal_mu_MLDSA65_Configuration_hol_DEF,
  f "87" ML_DSA_Verify_internal_mu_MLDSA87_Configuration_hol_DEF;;

(* ------------------------------------------------------------------------- *)
(* KeyGen_internal from one Value equation per component call.               *)
(* ------------------------------------------------------------------------- *)

let TOP_SLICE_PARTS = prove
 (`!(a:A list) b c.
     typed_hol_list_slice (APPEND a (APPEND b c)) (&0) (&(LENGTH a)) = SOME a /\
     typed_hol_list_slice (APPEND a (APPEND b c)) (&(LENGTH a))
       (&(LENGTH a + LENGTH b)) = SOME b /\
     typed_hol_list_slice (APPEND a (APPEND b c)) (&(LENGTH a + LENGTH b))
       (&(LENGTH a + LENGTH b + LENGTH c)) = SOME c`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[TYPED_HOL_LIST_SLICE_NUM; LENGTH_APPEND] THEN
  REWRITE_TAC[ADD_CLAUSES; SUB_0; ADD_SUB2; LE_ADD; ARITH_RULE `(a + b + c) - (a + b) = c`;
              LE_0; ARITH_RULE `a <= a + b + c`; ARITH_RULE `a + b <= a + b + c`; LE_REFL] THEN
  REPEAT CONJ_TAC THEN
  REWRITE_TAC[injectivity "option"; LIST_EQ; LENGTH_LIST_OF_SEQ] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EL_LIST_OF_SEQ; EL_APPEND; LENGTH_LIST_OF_SEQ] THEN
  REPEAT COND_CASES_TAC THEN TRY(ASM_ARITH_TAC) THEN
  TRY(AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC));;

let TOP_KEYGEN_HYPS =
 "IntegerToBytes_1_hol (&@K@) (&1) = Value KB /\\
  @LBHYP@
  HBytes_34_hol (APPEND (APPEND xi KB) @LB@) (&128) = Value SD /\\
  SD = APPEND rho (APPEND rho' kk) /\\
  LENGTH rho = 32 /\\ LENGTH rho' = 64 /\\ LENGTH kk = 32 /\\
  ExpandA_@P@_Configuration_hol rho = Value A /\\
  ExpandS_@P@_Configuration_hol rho' = Value (S1,S2) /\\
  IntVectorNTT_@L@_hol S1 = Value S1h /\\
  MatrixVectorNTT_@K@_@L@_@P@_Configuration_hol A S1h = Value AS /\\
  VectorNTTInv_@K@_@P@_Configuration_hol AS = Value ASi /\\
  RqIntVectorAdd_@K@_hol ASi S2 = Value Tv /\\
  FixedVectorPower2Round_@K@_@P@_Configuration_hol Tv = Value (T1,T0) /\\
  pkEncode_@P@_Configuration_hol rho T1 = Value PK /\\
  HBytesString_hol PK (&64) = Value TR /\\ LENGTH TR = 64 /\\
  skEncode_@P@_Configuration_hol rho kk TR S1 S2 T0 = Value SK";;
let TOP_KEYGEN_CONCL =
 "ML_DSA_KeyGen_internal_@P@_Configuration_hol xi = Value (PK,SK)";;
let TOP_KEYGEN_ABS p =
  top_tmx p (top_subst (if p = "44" then ["@LBHYP@",""; "@LB@","KB"]
     else ["@LBHYP@","IntegerToBytes_1_hol (&@L@) (&1) = Value LB /\\"; "@LB@","LB"])
     ("(" ^ TOP_KEYGEN_HYPS ^ ") ==> (" ^ TOP_KEYGEN_CONCL ^ ")"));;

let TOP_KEYGEN_PROVE p def =
  prove(TOP_KEYGEN_ABS p,
    STRIP_TAC THEN
    MP_TAC(ISPECL [`rho:byte list`; `rho':byte list`; `kk:byte list`] TOP_SLICE_PARTS) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN STRIP_TAC THEN
    REWRITE_TAC[def] THEN REWRITE_TAC TOP_MONAD_RULES THEN
    ASM_REWRITE_TAC TOP_MONAD_RULES THEN TOP_ARITH_TAC THEN
    ASM_SIMP_TAC(TYPED_HOL_SEQUENCE_EXTENT :: TOP_MONAD_RULES));;
let TOP_KEYGEN_ABSTRACT_44 = TOP_KEYGEN_PROVE "44" ML_DSA_KeyGen_internal_MLDSA44_Configuration_hol_DEF;;
let TOP_KEYGEN_ABSTRACT_65 = TOP_KEYGEN_PROVE "65" ML_DSA_KeyGen_internal_MLDSA65_Configuration_hol_DEF;;
let TOP_KEYGEN_ABSTRACT_87 = TOP_KEYGEN_PROVE "87" ML_DSA_KeyGen_internal_MLDSA87_Configuration_hol_DEF;;

(* ------------------------------------------------------------------------- *)
(* The same for Sign_internal, which computes mu from tr and M first.        *)
(* ------------------------------------------------------------------------- *)

(* ML-DSA-44                                                                 *)
let SIGNI44_EXT = [
  ML_DSA_Sign_internal_MLDSA44_Configuration_hol_emitted_mu_EXT;
  ML_DSA_Sign_internal_MLDSA44_Configuration_hol_emitted_rho''_EXT;
  ML_DSA_Sign_internal_MLDSA44_Configuration_hol_emitted_kappa_EXT;
  ML_DSA_Sign_internal_MLDSA44_Configuration_hol_emitted_A_NTT_EXT;
  ML_DSA_Sign_internal_MLDSA44_Configuration_hol_emitted_s1_NTT_EXT;
  ML_DSA_Sign_internal_MLDSA44_Configuration_hol_emitted_s2_NTT_EXT;
  ML_DSA_Sign_internal_MLDSA44_Configuration_hol_emitted_t0_NTT_EXT;
  ML_DSA_Sign_internal_MLDSA44_Configuration_hol_emitted_z_EXT;
  ML_DSA_Sign_internal_MLDSA44_Configuration_hol_emitted_h_EXT;
  ML_DSA_Sign_internal_MLDSA44_Configuration_hol_emitted_c_tilde_EXT];;
let signi44_wi = `\n s.
   ML_DSA_Sign_internal_MLDSA44_Configuration_hol_emitted_rho'' s = Native_Assigned (rho2:byte list) /\
   ML_DSA_Sign_internal_MLDSA44_Configuration_hol_emitted_mu s = Native_Assigned (mu:byte list) /\
   ML_DSA_Sign_internal_MLDSA44_Configuration_hol_emitted_kappa s = Native_Assigned (&(4 * n)) /\
   ML_DSA_Sign_internal_MLDSA44_Configuration_hol_emitted_A_NTT s = Native_Assigned A /\
   ML_DSA_Sign_internal_MLDSA44_Configuration_hol_emitted_s1_NTT s = Native_Assigned S1 /\
   ML_DSA_Sign_internal_MLDSA44_Configuration_hol_emitted_s2_NTT s = Native_Assigned S2 /\
   ML_DSA_Sign_internal_MLDSA44_Configuration_hol_emitted_t0_NTT s = Native_Assigned T0 /\
   ML_DSA_Sign_internal_MLDSA44_Configuration_hol_emitted_z s = Native_Assigned Native_Bottom /\
   ML_DSA_Sign_internal_MLDSA44_Configuration_hol_emitted_h s = Native_Assigned Native_Bottom`;;
let signi44_Q = `\n s.
   ML_DSA_Sign_internal_MLDSA44_Configuration_hol_emitted_c_tilde s = Native_Assigned ((CT:num->byte list) n) /\
   ML_DSA_Sign_internal_MLDSA44_Configuration_hol_emitted_z s = Native_Assigned (Native_Value (Z n)) /\
   ML_DSA_Sign_internal_MLDSA44_Configuration_hol_emitted_h s = Native_Assigned (Native_Value (HV n))`;;
let signi44_rej = `\n. ~((acc:num->bool) n)`;;
let TOP_WHILE_TAC wi rej q (asl,w) =
  let nw = rand(rator(lhand w)) in
  let s0 = rand nw and body = rand(rator nw) and test = rand(rator(rator nw)) in
  MP_TAC(ISPECL [test; body; wi; rej; q; s0] TOP_NATIVE_WHILE) (asl,w);;

let TOP_SIGNI_LOOP_HYPS_44 = `
  skDecode_MLDSA44_Configuration_hol sk = Value (rho,K,tr,s1,s2,t0) /\
  LENGTH rho = 32 /\ LENGTH K = 32 /\ LENGTH tr = 64 /\
  BytesToBitsString_hol tr = Value TRB /\ H_hol (APPEND TRB M) (&64) = Value mu /\
  ML_DSA_Sign_internal_MLDSA44_Configuration_callable_5_0_call (Native_Value s1) = Value S1 /\
  ML_DSA_Sign_internal_MLDSA44_Configuration_callable_5_0_call (Native_Value s2) = Value S2 /\
  ML_DSA_Sign_internal_MLDSA44_Configuration_callable_5_0_call (Native_Value t0) = Value T0 /\
  ML_DSA_Sign_internal_MLDSA44_Configuration_callable_4_0_call (Native_Value rho) = Value A /\
  HBytesString_hol (APPEND (APPEND K rnd) mu) (&64) = Value rho2 /\ LENGTH rho2 = 64 /\
  (!n. ExpandMask_MLDSA44_Configuration_hol rho2 (&(4 * n)) = Value (Y n)) /\
  (!n. IntVectorToRq_4_body_hol (Y n) = Value (Yq n)) /\
  (!n. VectorNTT_4_MLDSA44_Configuration_hol (Yq n) = Value (Yh n)) /\
  (!n. MatrixVectorNTT_4_4_MLDSA44_Configuration_hol A (Yh n) = Value (Wh n)) /\
  (!n. VectorNTTInv_4_MLDSA44_Configuration_hol (Wh n) = Value (W n)) /\
  (!n. FixedVectorHighBits_4_MLDSA44_Configuration_hol (W n) = Value (W1 n)) /\
  (!n. w1Encode_MLDSA44_Configuration_hol (W1 n) = Value (Native_Value (W1E n))) /\
  (!n. HBytesString_hol (APPEND mu (W1E n)) (&32) = Value (CT n)) /\
  (!n. SampleInBall_MLDSA44_Configuration_hol (CT n) = Value (C n)) /\
  (!n. IntPolyToRq_hol (C n) = Value (Cq n)) /\
  (!n. NTT_hol (Cq n) = Value (Ch n)) /\
  (!n. ScalarVectorNTT_4_MLDSA44_Configuration_hol (Ch n) S1 = Value (CS1h n)) /\
  (!n. VectorNTTInv_4_MLDSA44_Configuration_hol (CS1h n) = Value (CS1 n)) /\
  (!n. ScalarVectorNTT_4_MLDSA44_Configuration_hol (Ch n) S2 = Value (CS2h n)) /\
  (!n. VectorNTTInv_4_MLDSA44_Configuration_hol (CS2h n) = Value (CS2 n)) /\
  (!n. RqVectorAdd_4_hol (Yq n) (CS1 n) = Value (Z n)) /\
  (!n. FixedVectorSubtract_4_FIPS204_Time_hol (W n) (CS2 n) = Value (R n)) /\
  (!n. FixedVectorLowBits_4_MLDSA44_Configuration_hol (R n) = Value (R0 n)) /\
  (!n. ML_DSA_Sign_internal_MLDSA44_Configuration_callable_3_0_call (Native_Value (Z n)) = Value (NZ n)) /\
  (!n. IntVectorInfNorm_4_hol (R0 n) = Value (NR n)) /\
  (!n. ScalarVectorNTT_4_MLDSA44_Configuration_hol (Ch n) T0 = Value (CT0h n)) /\
  (!n. VectorNTTInv_4_MLDSA44_Configuration_hol (CT0h n) = Value (CT0 n)) /\
  (!n. RqVectorNegate_4_hol (CT0 n) = Value (NCT0 n)) /\
  (!n. RqVectorAdd_4_hol (R n) (CT0 n) = Value (RC n)) /\
  (!n. FixedVectorMakeHint_4_MLDSA44_Configuration_hol (NCT0 n) (RC n) = Value (HV n)) /\
  (!n. ML_DSA_Sign_internal_MLDSA44_Configuration_callable_3_0_call (Native_Value (CT0 n)) = Value (NCT n)) /\
  (!n. ML_DSA_Sign_internal_MLDSA44_Configuration_callable_2_0_call (Native_Value (HV n)) = Value (CNT n)) /\
  (!n. ML_DSA_Sign_internal_MLDSA44_Configuration_callable_1_0_call (Native_Value (Z n)) (&8380417) = Value (Native_Value (ZC n))) /\
  (!n. ML_DSA_Sign_internal_MLDSA44_Configuration_callable_0_0_call (CT n) (Native_Value (ZC n)) (Native_Value (HV n)) = Value (SIG n)) /\
  (!n. acc n <=> ~((&0 <= NZ n - &130994 \/ &0 <= NR n - &95154) \/
                   (&0 <= NCT n - &95232 \/ &0 < CNT n - &80)))`;;

(* ML-DSA-65                                                                 *)
let SIGNI65_EXT = [
  ML_DSA_Sign_internal_MLDSA65_Configuration_hol_emitted_mu_EXT;
  ML_DSA_Sign_internal_MLDSA65_Configuration_hol_emitted_rho''_EXT;
  ML_DSA_Sign_internal_MLDSA65_Configuration_hol_emitted_kappa_EXT;
  ML_DSA_Sign_internal_MLDSA65_Configuration_hol_emitted_A_NTT_EXT;
  ML_DSA_Sign_internal_MLDSA65_Configuration_hol_emitted_s1_NTT_EXT;
  ML_DSA_Sign_internal_MLDSA65_Configuration_hol_emitted_s2_NTT_EXT;
  ML_DSA_Sign_internal_MLDSA65_Configuration_hol_emitted_t0_NTT_EXT;
  ML_DSA_Sign_internal_MLDSA65_Configuration_hol_emitted_z_EXT;
  ML_DSA_Sign_internal_MLDSA65_Configuration_hol_emitted_h_EXT;
  ML_DSA_Sign_internal_MLDSA65_Configuration_hol_emitted_c_tilde_EXT];;
let signi65_wi = `\n s.
   ML_DSA_Sign_internal_MLDSA65_Configuration_hol_emitted_rho'' s = Native_Assigned (rho2:byte list) /\
   ML_DSA_Sign_internal_MLDSA65_Configuration_hol_emitted_mu s = Native_Assigned (mu:byte list) /\
   ML_DSA_Sign_internal_MLDSA65_Configuration_hol_emitted_kappa s = Native_Assigned (&(5 * n)) /\
   ML_DSA_Sign_internal_MLDSA65_Configuration_hol_emitted_A_NTT s = Native_Assigned A /\
   ML_DSA_Sign_internal_MLDSA65_Configuration_hol_emitted_s1_NTT s = Native_Assigned S1 /\
   ML_DSA_Sign_internal_MLDSA65_Configuration_hol_emitted_s2_NTT s = Native_Assigned S2 /\
   ML_DSA_Sign_internal_MLDSA65_Configuration_hol_emitted_t0_NTT s = Native_Assigned T0 /\
   ML_DSA_Sign_internal_MLDSA65_Configuration_hol_emitted_z s = Native_Assigned Native_Bottom /\
   ML_DSA_Sign_internal_MLDSA65_Configuration_hol_emitted_h s = Native_Assigned Native_Bottom`;;
let signi65_Q = `\n s.
   ML_DSA_Sign_internal_MLDSA65_Configuration_hol_emitted_c_tilde s = Native_Assigned ((CT:num->byte list) n) /\
   ML_DSA_Sign_internal_MLDSA65_Configuration_hol_emitted_z s = Native_Assigned (Native_Value (Z n)) /\
   ML_DSA_Sign_internal_MLDSA65_Configuration_hol_emitted_h s = Native_Assigned (Native_Value (HV n))`;;
let signi65_rej = `\n. ~((acc:num->bool) n)`;;

let TOP_SIGNI_LOOP_HYPS_65 = `
  skDecode_MLDSA65_Configuration_hol sk = Value (rho,K,tr,s1,s2,t0) /\
  LENGTH rho = 32 /\ LENGTH K = 32 /\ LENGTH tr = 64 /\
  BytesToBitsString_hol tr = Value TRB /\ H_hol (APPEND TRB M) (&64) = Value mu /\
  ML_DSA_Sign_internal_MLDSA65_Configuration_callable_6_0_call (Native_Value s1) = Value S1 /\
  ML_DSA_Sign_internal_MLDSA65_Configuration_callable_5_0_call (Native_Value s2) = Value S2 /\
  ML_DSA_Sign_internal_MLDSA65_Configuration_callable_5_0_call (Native_Value t0) = Value T0 /\
  ML_DSA_Sign_internal_MLDSA65_Configuration_callable_4_0_call (Native_Value rho) = Value A /\
  HBytesString_hol (APPEND (APPEND K rnd) mu) (&64) = Value rho2 /\ LENGTH rho2 = 64 /\
  (!n. ExpandMask_MLDSA65_Configuration_hol rho2 (&(5 * n)) = Value (Y n)) /\
  (!n. IntVectorToRq_5_body_hol (Y n) = Value (Yq n)) /\
  (!n. VectorNTT_5_MLDSA65_Configuration_hol (Yq n) = Value (Yh n)) /\
  (!n. MatrixVectorNTT_6_5_MLDSA65_Configuration_hol A (Yh n) = Value (Wh n)) /\
  (!n. VectorNTTInv_6_MLDSA65_Configuration_hol (Wh n) = Value (W n)) /\
  (!n. FixedVectorHighBits_6_MLDSA65_Configuration_hol (W n) = Value (W1 n)) /\
  (!n. w1Encode_MLDSA65_Configuration_hol (W1 n) = Value (Native_Value (W1E n))) /\
  (!n. HBytesString_hol (APPEND mu (W1E n)) (&48) = Value (CT n)) /\
  (!n. SampleInBall_MLDSA65_Configuration_hol (CT n) = Value (C n)) /\
  (!n. IntPolyToRq_hol (C n) = Value (Cq n)) /\
  (!n. NTT_hol (Cq n) = Value (Ch n)) /\
  (!n. ScalarVectorNTT_5_MLDSA65_Configuration_hol (Ch n) S1 = Value (CS1h n)) /\
  (!n. VectorNTTInv_5_MLDSA65_Configuration_hol (CS1h n) = Value (CS1 n)) /\
  (!n. ScalarVectorNTT_6_MLDSA65_Configuration_hol (Ch n) S2 = Value (CS2h n)) /\
  (!n. VectorNTTInv_6_MLDSA65_Configuration_hol (CS2h n) = Value (CS2 n)) /\
  (!n. RqVectorAdd_5_hol (Yq n) (CS1 n) = Value (Z n)) /\
  (!n. FixedVectorSubtract_6_FIPS204_Time_hol (W n) (CS2 n) = Value (R n)) /\
  (!n. FixedVectorLowBits_6_MLDSA65_Configuration_hol (R n) = Value (R0 n)) /\
  (!n. ML_DSA_Sign_internal_MLDSA65_Configuration_callable_3_0_call (Native_Value (Z n)) = Value (NZ n)) /\
  (!n. IntVectorInfNorm_6_hol (R0 n) = Value (NR n)) /\
  (!n. ScalarVectorNTT_6_MLDSA65_Configuration_hol (Ch n) T0 = Value (CT0h n)) /\
  (!n. VectorNTTInv_6_MLDSA65_Configuration_hol (CT0h n) = Value (CT0 n)) /\
  (!n. RqVectorNegate_6_hol (CT0 n) = Value (NCT0 n)) /\
  (!n. RqVectorAdd_6_hol (R n) (CT0 n) = Value (RC n)) /\
  (!n. FixedVectorMakeHint_6_MLDSA65_Configuration_hol (NCT0 n) (RC n) = Value (HV n)) /\
  (!n. RqVectorInfNorm_6_hol (CT0 n) = Value (NCT n)) /\
  (!n. ML_DSA_Sign_internal_MLDSA65_Configuration_callable_2_0_call (Native_Value (HV n)) = Value (CNT n)) /\
  (!n. ML_DSA_Sign_internal_MLDSA65_Configuration_callable_1_0_call (Native_Value (Z n)) (&8380417) = Value (Native_Value (ZC n))) /\
  (!n. ML_DSA_Sign_internal_MLDSA65_Configuration_callable_0_0_call (CT n) (Native_Value (ZC n)) (Native_Value (HV n)) = Value (SIG n)) /\
  (!n. acc n <=> ~((&0 <= NZ n - &524092 \/ &0 <= NR n - &261692) \/
                   (&0 <= NCT n - &261888 \/ &0 < CNT n - &55)))`;;

(* ML-DSA-87                                                                 *)
let SIGNI87_EXT = [
  ML_DSA_Sign_internal_MLDSA87_Configuration_hol_emitted_mu_EXT;
  ML_DSA_Sign_internal_MLDSA87_Configuration_hol_emitted_rho''_EXT;
  ML_DSA_Sign_internal_MLDSA87_Configuration_hol_emitted_kappa_EXT;
  ML_DSA_Sign_internal_MLDSA87_Configuration_hol_emitted_A_NTT_EXT;
  ML_DSA_Sign_internal_MLDSA87_Configuration_hol_emitted_s1_NTT_EXT;
  ML_DSA_Sign_internal_MLDSA87_Configuration_hol_emitted_s2_NTT_EXT;
  ML_DSA_Sign_internal_MLDSA87_Configuration_hol_emitted_t0_NTT_EXT;
  ML_DSA_Sign_internal_MLDSA87_Configuration_hol_emitted_z_EXT;
  ML_DSA_Sign_internal_MLDSA87_Configuration_hol_emitted_h_EXT;
  ML_DSA_Sign_internal_MLDSA87_Configuration_hol_emitted_c_tilde_EXT];;
let signi87_wi = `\n s.
   ML_DSA_Sign_internal_MLDSA87_Configuration_hol_emitted_rho'' s = Native_Assigned (rho2:byte list) /\
   ML_DSA_Sign_internal_MLDSA87_Configuration_hol_emitted_mu s = Native_Assigned (mu:byte list) /\
   ML_DSA_Sign_internal_MLDSA87_Configuration_hol_emitted_kappa s = Native_Assigned (&(7 * n)) /\
   ML_DSA_Sign_internal_MLDSA87_Configuration_hol_emitted_A_NTT s = Native_Assigned A /\
   ML_DSA_Sign_internal_MLDSA87_Configuration_hol_emitted_s1_NTT s = Native_Assigned S1 /\
   ML_DSA_Sign_internal_MLDSA87_Configuration_hol_emitted_s2_NTT s = Native_Assigned S2 /\
   ML_DSA_Sign_internal_MLDSA87_Configuration_hol_emitted_t0_NTT s = Native_Assigned T0 /\
   ML_DSA_Sign_internal_MLDSA87_Configuration_hol_emitted_z s = Native_Assigned Native_Bottom /\
   ML_DSA_Sign_internal_MLDSA87_Configuration_hol_emitted_h s = Native_Assigned Native_Bottom`;;
let signi87_Q = `\n s.
   ML_DSA_Sign_internal_MLDSA87_Configuration_hol_emitted_c_tilde s = Native_Assigned ((CT:num->byte list) n) /\
   ML_DSA_Sign_internal_MLDSA87_Configuration_hol_emitted_z s = Native_Assigned (Native_Value (Z n)) /\
   ML_DSA_Sign_internal_MLDSA87_Configuration_hol_emitted_h s = Native_Assigned (Native_Value (HV n))`;;
let signi87_rej = `\n. ~((acc:num->bool) n)`;;

let TOP_SIGNI_LOOP_HYPS_87 = `
  skDecode_MLDSA87_Configuration_hol sk = Value (rho,K,tr,s1,s2,t0) /\
  LENGTH rho = 32 /\ LENGTH K = 32 /\ LENGTH tr = 64 /\
  BytesToBitsString_hol tr = Value TRB /\ H_hol (APPEND TRB M) (&64) = Value mu /\
  ML_DSA_Sign_internal_MLDSA87_Configuration_callable_6_0_call (Native_Value s1) = Value S1 /\
  ML_DSA_Sign_internal_MLDSA87_Configuration_callable_5_0_call (Native_Value s2) = Value S2 /\
  ML_DSA_Sign_internal_MLDSA87_Configuration_callable_5_0_call (Native_Value t0) = Value T0 /\
  ML_DSA_Sign_internal_MLDSA87_Configuration_callable_4_0_call (Native_Value rho) = Value A /\
  HBytesString_hol (APPEND (APPEND K rnd) mu) (&64) = Value rho2 /\ LENGTH rho2 = 64 /\
  (!n. ExpandMask_MLDSA87_Configuration_hol rho2 (&(7 * n)) = Value (Y n)) /\
  (!n. IntVectorToRq_7_body_hol (Y n) = Value (Yq n)) /\
  (!n. VectorNTT_7_MLDSA87_Configuration_hol (Yq n) = Value (Yh n)) /\
  (!n. MatrixVectorNTT_8_7_MLDSA87_Configuration_hol A (Yh n) = Value (Wh n)) /\
  (!n. VectorNTTInv_8_MLDSA87_Configuration_hol (Wh n) = Value (W n)) /\
  (!n. FixedVectorHighBits_8_MLDSA87_Configuration_hol (W n) = Value (W1 n)) /\
  (!n. w1Encode_MLDSA87_Configuration_hol (W1 n) = Value (Native_Value (W1E n))) /\
  (!n. HBytesString_hol (APPEND mu (W1E n)) (&64) = Value (CT n)) /\
  (!n. SampleInBall_MLDSA87_Configuration_hol (CT n) = Value (C n)) /\
  (!n. IntPolyToRq_hol (C n) = Value (Cq n)) /\
  (!n. NTT_hol (Cq n) = Value (Ch n)) /\
  (!n. ScalarVectorNTT_7_MLDSA87_Configuration_hol (Ch n) S1 = Value (CS1h n)) /\
  (!n. VectorNTTInv_7_MLDSA87_Configuration_hol (CS1h n) = Value (CS1 n)) /\
  (!n. ScalarVectorNTT_8_MLDSA87_Configuration_hol (Ch n) S2 = Value (CS2h n)) /\
  (!n. VectorNTTInv_8_MLDSA87_Configuration_hol (CS2h n) = Value (CS2 n)) /\
  (!n. RqVectorAdd_7_hol (Yq n) (CS1 n) = Value (Z n)) /\
  (!n. FixedVectorSubtract_8_FIPS204_Time_hol (W n) (CS2 n) = Value (R n)) /\
  (!n. FixedVectorLowBits_8_MLDSA87_Configuration_hol (R n) = Value (R0 n)) /\
  (!n. ML_DSA_Sign_internal_MLDSA87_Configuration_callable_3_0_call (Native_Value (Z n)) = Value (NZ n)) /\
  (!n. IntVectorInfNorm_8_hol (R0 n) = Value (NR n)) /\
  (!n. ScalarVectorNTT_8_MLDSA87_Configuration_hol (Ch n) T0 = Value (CT0h n)) /\
  (!n. VectorNTTInv_8_MLDSA87_Configuration_hol (CT0h n) = Value (CT0 n)) /\
  (!n. RqVectorNegate_8_hol (CT0 n) = Value (NCT0 n)) /\
  (!n. RqVectorAdd_8_hol (R n) (CT0 n) = Value (RC n)) /\
  (!n. FixedVectorMakeHint_8_MLDSA87_Configuration_hol (NCT0 n) (RC n) = Value (HV n)) /\
  (!n. RqVectorInfNorm_8_hol (CT0 n) = Value (NCT n)) /\
  (!n. ML_DSA_Sign_internal_MLDSA87_Configuration_callable_2_0_call (Native_Value (HV n)) = Value (CNT n)) /\
  (!n. ML_DSA_Sign_internal_MLDSA87_Configuration_callable_1_0_call (Native_Value (Z n)) (&8380417) = Value (Native_Value (ZC n))) /\
  (!n. ML_DSA_Sign_internal_MLDSA87_Configuration_callable_0_0_call (CT n) (Native_Value (ZC n)) (Native_Value (HV n)) = Value (SIG n)) /\
  (!n. acc n <=> ~((&0 <= NZ n - &524168 \/ &0 <= NR n - &261768) \/
                   (&0 <= NCT n - &261888 \/ &0 < CNT n - &75)))`;;
