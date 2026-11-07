(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Extraction of bytes from a Keccak state. This is the code for             *)
(* mlkem_keccakf1600_extract_bytes from mlkem-native's portable C            *)
(* implementation compiled by clang 17 with -O3 (see mlkem_native/README.md),*)
(* which copies len bytes of the 200-byte state starting at byte off. Like   *)
(* gcc at -O3, clang has vectorized the copy, but with loops instead of      *)
(* straight-line code: if len >= 8 and the output starts at least 32 bytes   *)
(* after byte off of the state (as a difference modulo 2^64), it copies      *)
(* blocks of 32 bytes with Q registers, then blocks of 8 bytes with a D      *)
(* register, and finally single bytes; otherwise it copies single bytes.    *)
(* The specifications are those for gcc. It is verified in the whole image   *)
(* (see libmlkem.ml).                                                        *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_keccakf1600_extract_bytes:
      +0x0: cbz     w3, join3
      +0x4: mov     w9, w2
      +0x8: mov     w8, w3
      +0xc: cmp     w3, #0x8
     +0x10: b.cc    join1
     +0x14: sub     x10, x1, x0
     +0x18: sub     x10, x10, x9
     +0x1c: cmp     x10, #0x20
     +0x20: b.cs    +0x4c
     +0x24: mov     x10, xzr
     +0x28: add     x11, x0, x10
     +0x2c: sub     x8, x8, x10
     +0x30: add     x9, x11, x9
     +0x34: add     x11, x1, x10
     +0x38: ldrb    w10, [x9], #1
     +0x3c: subs    x8, x8, #0x1
     +0x40: strb    w10, [x11], #1
     +0x44: b.ne    loop1
     +0x48: ret
     +0x4c: cmp     w3, #0x20
     +0x50: b.cs    +0x5c
     +0x54: mov     x10, xzr
     +0x58: b       join4
     +0x5c: and     x10, x8, #0xffffffe0
     +0x60: add     x11, x9, x0
     +0x64: add     x11, x11, #0x10
     +0x68: add     x12, x1, #0x10
     +0x6c: mov     x13, x10
     +0x70: ldp     q0, q1, [x11, #-16]
     +0x74: add     x11, x11, #0x20
     +0x78: subs    x13, x13, #0x20
     +0x7c: stp     q0, q1, [x12, #-16]
     +0x80: add     x12, x12, #0x20
     +0x84: b.ne    loop2
     +0x88: cmp     x10, x8
     +0x8c: b.eq    join3
     +0x90: tst     x8, #0x18
     +0x94: b.eq    join2
     +0x98: mov     x13, x10
     +0x9c: and     x10, x8, #0xfffffff8
     +0xa0: add     x11, x0, x13
     +0xa4: add     x12, x1, x13
     +0xa8: add     x11, x11, x9
     +0xac: sub     x13, x13, x10
     +0xb0: ldr     d0, [x11], #8
     +0xb4: adds    x13, x13, #0x8
     +0xb8: str     d0, [x12], #8
     +0xbc: b.ne    loop3
     +0xc0: cmp     x10, x8
     +0xc4: b.eq    join3
     +0xc8: b       join2
 ***)

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_keccakf1600_extract_bytes"];;

(* ------------------------------------------------------------------------- *)
(* Reading 8 and 16 bytes of an array given as a number.                     *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES64_OF_NUM_STMT =
  `!a:int64 m n k s:armstate.
        read (memory :> bytes(a,m)) s = n /\ k + 8 <= m
        ==> read (memory :> bytes64(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 2 EXP 64)`;;

let READ_MEMORY_BYTES64_OF_NUM = assume_spec READ_MEMORY_BYTES64_OF_NUM_STMT;;

let READ_MEMORY_BYTES128_OF_NUM_STMT =
  `!a:int64 m n k s:armstate.
        read (memory :> bytes(a,m)) s = n /\ k + 16 <= m
        ==> read (memory :> bytes128(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 2 EXP 128)`;;

let READ_MEMORY_BYTES128_OF_NUM =
  assume_spec READ_MEMORY_BYTES128_OF_NUM_STMT;;

(*** A block of k bytes after the first j, both as numbers ***)

let READ_MEMORY_BYTES_EXTEND_STMT =
  `!d:int64 j k x s:armstate.
        read (memory :> bytes(d,j)) s = x MOD 2 EXP (8 * j) /\
        read (memory :> bytes(word_add d (word j),k)) s =
        (x DIV 2 EXP (8 * j)) MOD 2 EXP (8 * k)
        ==> read (memory :> bytes(d,j + k)) s = x MOD 2 EXP (8 * (j + k))`;;

let READ_MEMORY_BYTES_EXTEND = assume_spec READ_MEMORY_BYTES_EXTEND_STMT;;

(*** The bytes of 8- and 16-byte words as numbers ***)

let READ_MEMORY_BYTES_OF_BYTES64_STMT =
  `!a:int64 v s:armstate.
        read (memory :> bytes64 a) s = word v
        ==> read (memory :> bytes(a,8)) s = v MOD 2 EXP (8 * 8)`;;

let READ_MEMORY_BYTES_OF_BYTES64 =
  assume_spec READ_MEMORY_BYTES_OF_BYTES64_STMT;;

let READ_MEMORY_BYTES_OF_BYTES128_STMT =
  `!a:int64 v s:armstate.
        read (memory :> bytes128 a) s = word v
        ==> read (memory :> bytes(a,16)) s = v MOD 2 EXP (8 * 16)`;;

let READ_MEMORY_BYTES_OF_BYTES128 =
  assume_spec READ_MEMORY_BYTES_OF_BYTES128_STMT;;

let READ_MEMORY_BYTES_OF_BYTES8_1_STMT =
  `!a:int64 v s:armstate.
        read (memory :> bytes8 a) s = word v
        ==> read (memory :> bytes(a,1)) s = v MOD 2 EXP (8 * 1)`;;

let READ_MEMORY_BYTES_OF_BYTES8_1 =
  assume_spec READ_MEMORY_BYTES_OF_BYTES8_1_STMT;;

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** Weakening the pre- and postconditions of an ensures ***)

let ENSURES_PREPOST_WEAKEN = MESON[ENSURES_PREPOSTCONDITION_THM]
 `ensures step P Q C
  ==> (!x. P' x ==> P x) /\ (!x. Q x ==> Q' x)
      ==> ensures step P' Q' C`;;

(* ------------------------------------------------------------------------- *)
(* Lemmas and tactics for the 32-bit arithmetic of the code on small         *)
(* numbers, and for the addresses with a 32-bit index register (UXTW).       *)
(* ------------------------------------------------------------------------- *)

let WORD_ZX_WORD_SMALL = prove
 (`!n. n < 2 EXP dimindex(:M)
       ==> (word_zx:M word->N word) (word n) = word n`,
  SIMP_TAC[WORD_ZX_WORD; MOD_LT]);;

let WORD_ZX_UXTW_SMALL_STMT =
  `!n. n < 2 EXP 32
       ==> word_zx(word_zx(word n:int64):int32):int64 = word n /\
           word_zx(word_zx(word_zx(word n:int64):int32):int32):int64 = word n`;;

let WORD_ZX_UXTW_SMALL = assume_spec WORD_ZX_UXTW_SMALL_STMT;;

let WORD_ZX_BYTE_MOD = prove
 (`!y. 8 <= dimindex(:M)
       ==> (word_zx:M word->N word) (word (y MOD 256)) = word(y MOD 256)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_ZX_WORD] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `2 EXP 8` THEN REWRITE_TAC[LE_EXP] THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC);;

let WORD_ZX_BYTE_MOD_RULE =
  let pat = `read (memory :> bytes8 x) s = y` in
  let thms = map (fun ty ->
    REWRITE_RULE[] (CONV_RULE(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
                     (INST_TYPE [ty,`:M`] WORD_ZX_BYTE_MOD)))
    [`:8`; `:32`; `:64`] in
  fun th ->
    if can (term_match [] pat) (concl th) then REWRITE_RULE thms th
    else th;;

let WORD_AND_FFFFFFF0_32_STMT =
  `!n. n < 2 EXP 32
       ==> word_and (word n:int32) (word 4294967280) = word(16 * n DIV 16)`;;

let WORD_AND_FFFFFFF0_32 = assume_spec WORD_AND_FFFFFFF0_32_STMT;;

let WORD_AND_FFFFFFF8_32_STMT =
  `!n. n < 2 EXP 32
       ==> word_and (word n:int32) (word 4294967288) = word(8 * n DIV 8)`;;

let WORD_AND_FFFFFFF8_32 = assume_spec WORD_AND_FFFFFFF8_32_STMT;;

let WORD_AND_FFFFFFF0_64_STMT =
  `!n. n < 2 EXP 32
       ==> word_and (word n:int64) (word 4294967280) = word(16 * n DIV 16)`;;

let WORD_AND_FFFFFFF0_64 = assume_spec WORD_AND_FFFFFFF0_64_STMT;;

let VAL_WORD_AND_15_STMT =
  `!n. val(word_and (word n:int64) (word 15)) = (n MOD 2 EXP 64) MOD 16`;;

let VAL_WORD_AND_15 = assume_spec VAL_WORD_AND_15_STMT;;

let VAL_WORD_AND_7_STMT =
  `!n. val(word_and (word n:int64) (word 7)) = (n MOD 2 EXP 64) MOD 8`;;

let VAL_WORD_AND_7 = assume_spec VAL_WORD_AND_7_STMT;;

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** Normalize word arithmetic on small numbers in the register values:  ***)
(*** word_zx (word n) = word n, word_sub (word x) (word y) = word(x - y) ***)
(*** and word_add (word x) (word y) = word(x + y), with the side          ***)
(*** conditions proved by arithmetic from the assumptions, then the       ***)
(*** masks of the length and simple quotients.                            ***)

let W_NORM_TAC =
  let zx_pat = `(word_zx:M word->N word) (word n)`
  and sub_pat = `word_sub (word x) (word y):N word`
  and add_pat = `word_add (word x) (word y):N word`
  and reg_pat = `read (r:(armstate,int64)component) s = x` in
  let is_reg th = can (term_match [] reg_pat) (concl th) in
  let cands (asl,w) =
    let tms = mapfilter (fun (_,th) -> if is_reg th then rand(concl th)
                                       else failwith "") asl in
    let fnd p = setify(itlist (fun t acc -> find_terms p t @ acc) tms []) in
    fnd (can (term_match [] add_pat)) @
    fnd (can (term_match [] sub_pat)) @
    fnd (can (term_match [] zx_pat)) in
  let side_tac =
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) THEN
    SIMPLE_ARITH_TAC in
  let rule th = RULE_ASSUM_TAC(fun a -> if is_reg a then REWRITE_RULE[th] a
                                        else a) in
  let one_tac t =
    if can (term_match [] zx_pat) t then
      let n = rand(rand t) in
      let ity = type_of(rand t) and oty = type_of t in
      let th = SPEC n (INST_TYPE [hd(snd(dest_type ity)),`:M`;
                                  hd(snd(dest_type oty)),`:N`]
                       WORD_ZX_WORD_SMALL) in
      SUBGOAL_THEN (lhand(concl th)) (fun c -> rule(MP th c)) THENL
       [side_tac; ALL_TAC]
    else if can (term_match [] sub_pat) t then
      let x = rand(lhand t) and y = rand(rand t) in
      let th = ISPECL [x; y] (INST_TYPE [hd(snd(dest_type(type_of t))),`:N`]
                              (GEN_ALL WORD_SUB2)) in
      SUBGOAL_THEN (lhand(concl th)) (fun c -> rule(MP th c)) THENL
       [side_tac; ALL_TAC]
    else rule(GSYM WORD_ADD) in
  let pass = W(fun g -> MAP_EVERY (fun t -> TRY(one_tac t)) (cands g)) in
  pass THEN pass THEN pass THEN pass;;

let EXT_NORM_TAC =
  let mask_pats =
   [`word_and (word n:int32) (word 4294967280)`, WORD_AND_FFFFFFF0_32;
    `word_and (word n:int32) (word 4294967288)`, WORD_AND_FFFFFFF8_32;
    `word_and (word n:int64) (word 4294967280)`, WORD_AND_FFFFFFF0_64] in
  W_NORM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_SUB2]) THEN
  W(fun (asl,w) ->
    let tms = setify(itlist (fun (_,th) acc ->
      find_terms (fun t -> exists (fun (p,_) -> can (term_match [] p) t)
                                  mask_pats) (concl th) @ acc) asl []) in
    MAP_EVERY (fun t ->
      let lth = snd(find (fun (p,_) -> can (term_match [] p) t) mask_pats) in
      let th = SPEC (rand(lhand t)) lth in
      TRY(SUBGOAL_THEN (lhand(concl th))
            (fun c -> RULE_ASSUM_TAC(REWRITE_RULE[MP th c])) THENL
          [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC])) tms) THEN
  W(fun (asl,w) ->
    let tms = setify(itlist (fun (_,th) acc ->
      find_terms (fun t -> can (term_match [] `(m * n + p) DIV m`) t &&
                           is_numeral(lhand(lhand(lhand t))))
        (concl th) @ acc) asl []) in
    MAP_EVERY (fun t ->
      let eq = mk_eq(t,rand(lhand(lhand t))) in
      TRY(SUBGOAL_THEN eq (fun c -> RULE_ASSUM_TAC(REWRITE_RULE[c])) THENL
       [ARITH_TAC; ALL_TAC])) tms) THEN
  W_NORM_TAC;;

(*** The tests of the length with TST ***)

let EXT_TST_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_AND_15; VAL_WORD_AND_7]) THEN
  W(fun (asl,w) ->
    let tms = setify(itlist (fun (_,th) acc ->
      find_terms (fun t -> can (term_match [] `n MOD 2 EXP 64`) t)
        (concl th) @ acc) asl []) in
    MAP_EVERY (fun t ->
      TRY(SUBGOAL_THEN (mk_eq(t,lhand t))
            (fun c -> RULE_ASSUM_TAC(REWRITE_RULE[c])) THENL
          [MATCH_MP_TAC MOD_LT THEN CONV_TAC NUM_REDUCE_CONV THEN
           SIMPLE_ARITH_TAC; ALL_TAC])) tms) THEN
  DECIDE_FLAGS_TAC;;

(*** A branch on a comparison, decided by arithmetic ***)

let EXT_BRANCH_TAC =
  TRY(FIRST_X_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),l),Comb(Comb(Comb(Const("COND",_),c),_),_))
        when can (term_match [] `read PC s`) l ->
        (SUBGOAL_THEN c (fun cth -> ASSUME_TAC(REWRITE_RULE[cth] th)) THENL
          [FIRST_ASSUM ACCEPT_TAC ORELSE SIMPLE_ARITH_TAC; ALL_TAC]) ORELSE
        (SUBGOAL_THEN (mk_neg c)
          (fun cth -> ASSUME_TAC(REWRITE_RULE[cth] th)) THENL
          [FIRST_ASSUM ACCEPT_TAC ORELSE SIMPLE_ARITH_TAC; ALL_TAC])
    | _ -> NO_TAC));;

(*** The equations removing the extensions of 32-bit indices j ***)

let EXT_ZX_FACTS_TAC js =
  MAP_EVERY (fun j ->
    MP_TAC(SPEC j WORD_ZX_UXTW_SMALL) THEN
    ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
                    STRIP_TAC]) js;;

(*** The bytes of the state at byte off + j of it, in the form of the ***)
(*** addresses that the code computes from a + off and j               ***)

let READ_MEMORY_BYTES8_OF_NUM_OFF_STMT =
  `!a:int64 m n off j s:armstate.
        read (memory :> bytes(a,m)) s = n /\ off + j < m
        ==> read (memory :> bytes8(word_add (word_add a (word off))
                                            (word j))) s =
            word((n DIV 2 EXP (8 * (off + j))) MOD 256)`;;

let READ_MEMORY_BYTES8_OF_NUM_OFF =
  assume_spec READ_MEMORY_BYTES8_OF_NUM_OFF_STMT;;

let READ_MEMORY_BYTES64_OF_NUM_OFF_STMT =
  `!a:int64 m n off j s:armstate.
        read (memory :> bytes(a,m)) s = n /\ off + j + 8 <= m
        ==> read (memory :> bytes64(word_add (word_add a (word off))
                                             (word j))) s =
            word((n DIV 2 EXP (8 * (off + j))) MOD 2 EXP 64)`;;

let READ_MEMORY_BYTES64_OF_NUM_OFF =
  assume_spec READ_MEMORY_BYTES64_OF_NUM_OFF_STMT;;

let EXT_STATE_FACTS_TAC sname js8 js64 =
  let s = mk_var(sname,`:armstate`) in
  let one lth j =
    MP_TAC(SPECL [`a:int64`; `200`; `val(S:1600 word)`; `off:num`; j; s]
                 lth) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; DISCH_TAC] in
  let one' lth j =
    MP_TAC(SPECL [`a:int64`; `200`; `val(S:1600 word)`;
                  mk_binop `(+):num->num->num` `off:num` j; s] lth) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; DISCH_TAC] in
  MAP_EVERY (one READ_MEMORY_BYTES8_OF_NUM_OFF) js8 THEN
  MAP_EVERY (one READ_MEMORY_BYTES64_OF_NUM_OFF) js64 THEN
  MAP_EVERY (one' READ_MEMORY_BYTES8_OF_NUM) js8 THEN
  MAP_EVERY (one' READ_MEMORY_BYTES64_OF_NUM) js64;;

(*** The stores to the output as byte arrays of the form needed below ***)

let EXT_CHUNK_LEMMA_STMT =
  `!d:int64 J K v s:armstate off.
        read (memory :> bytes(word_add d (word J),K)) s =
        ((v DIV 2 EXP (8 * (off + J))) MOD 2 EXP (8 * K)) MOD 2 EXP (8 * K)
        ==> read (memory :> bytes(word_add d (word J),K)) s =
            ((v DIV 2 EXP (8 * off)) DIV 2 EXP (8 * J)) MOD 2 EXP (8 * K)`;;

let EXT_CHUNK_LEMMA = assume_spec EXT_CHUNK_LEMMA_STMT;;

let EXT_STORES_TAC =
  let pats =
   [`read (memory :> bytes128 (word_add d (word n))) s = word x`,
    READ_MEMORY_BYTES_OF_BYTES128;
    `read (memory :> bytes64 (word_add d (word n))) s = word x`,
    READ_MEMORY_BYTES_OF_BYTES64;
    `read (memory :> bytes8 (word_add d (word n))) s = word x`,
    READ_MEMORY_BYTES_OF_BYTES8_1] in
  let nums = REWRITE_RULE[ARITH_RULE
   `340282366920938463463374607431768211456 = 2 EXP (8 * 16) /\
    18446744073709551616 = 2 EXP (8 * 8) /\ 256 = 2 EXP (8 * 1) /\
    2 EXP 128 = 2 EXP (8 * 16) /\ 2 EXP 64 = 2 EXP (8 * 8)`] in
  RULE_ASSUM_TAC WORD_ZX_BYTE_MOD_RULE THEN
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    match filter (fun (p,_) -> can (term_match [] p) c) pats with
      (_,lth)::_ ->
        (try MATCH_MP EXT_CHUNK_LEMMA (nums(MATCH_MP lth th))
         with Failure _ -> th)
    | [] -> th);;

(*** Fold sums of numerals in the register values ***)

let EXT_FOLD_TAC =
  let reg_pat = `read (r:(armstate,int64)component) s = x` in
  let conv t =
    match t with
      Comb(Comb(Const("+",_),Comb(Comb(Const("+",_),x),m)),n)
        when is_numeral m && is_numeral n ->
        (REWR_CONV (GSYM ADD_ASSOC) THENC RAND_CONV NUM_ADD_CONV) t
    | _ -> failwith "EXT_FOLD_TAC" in
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] reg_pat) (concl th)
    then CONV_RULE(RAND_CONV(DEPTH_CONV conv)) th else th);;

(*** W32_DECIDE_FLAGS_TAC, but rewriting only the flags, so that the ***)
(*** equations for the extended indices are kept                        ***)

let EXT_W32_DECIDE_TAC =
  let flag_pat = `read (f:(armstate,bool)component) s <=> p` in
  let is_flag th = can (term_match [] flag_pat) (concl th) in
  W(fun (asl,w) ->
    let tms = setify (itlist (fun (_,th) acc ->
      if is_flag th then
        find_terms (can (term_match [] `word_zx(word n:int64):int32`))
                   (concl th) @ acc
      else acc) asl []) in
    MAP_EVERY (fun t ->
      MP_TAC(SPEC (rand(rand t)) WORD_ZX_64_32_SMALL) THEN
      ANTS_TAC THENL
       [SIMPLE_ARITH_TAC;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(fun a ->
          if is_flag a then REWRITE_RULE[th] a else a))]) tms) THEN
  CMP_FLAGS_TAC `word_sub (word x) (word y):int32` WORD_CMP_32_FLAGS;;

let EXT_STEP_TAC n =
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_CLANG17_O3_EXEC [n] THEN
  EXT_NORM_TAC THEN EXT_FOLD_TAC THEN
  TRY EXT_W32_DECIDE_TAC THEN EXT_BRANCH_TAC;;

(* Generated tactics follow. *)

let EXT_EVENTS_TERM =
  let ev nm args = "f_ev_" ^ nm ^ " " ^ args in
  let full = "a d off len pc returnaddress" in
  (* byte loop with count cnt, events pieces named pfx e/l/p *)
  let byteloop pfx cnt =
    "APPEND (" ^ ev (pfx ^ "e") full ^ ") (APPEND (ENUMERATEL (" ^ cnt ^
    ") (\\i. " ^ ev (pfx ^ "l") full ^ " i)) (" ^ ev (pfx ^ "p") full ^ "))" in
  (* tail after the 8-byte loop: nothing if len MOD 8 = 0, else bytes *)
  let tail3 pfx =
    "(if len MOD 8 = 0 then " ^ ev (pfx ^ "0") full ^ " else " ^
    byteloop (pfx ^ "1") "len MOD 8" ^ ")" in
  let loop3 pfx cnt =
    "APPEND " ^ tail3 (pfx ^ "t") ^ " (APPEND (" ^ ev (pfx ^ "e") full ^
    ") (APPEND (ENUMERATEL (" ^ cnt ^
    ") (\\i. " ^ ev (pfx ^ "l") full ^ " i)) (" ^ ev (pfx ^ "p") full ^ ")))" in
  let tail2 =
    "(if len MOD 32 = 0 then " ^ ev "t20" full ^
    " else if len MOD 32 < 8 then " ^ byteloop "t21" "len MOD 32" ^
    " else " ^ loop3 "t3" "(len MOD 32) DIV 8" ^ ")" in
  parse_term
   ("\\(a:int64) (d:int64) (off:num) (len:num) (pc:num) " ^
    "(returnaddress:int64). " ^
    "if len = 0 then " ^ ev "len0" full ^
    " else if len <= 7 then " ^ byteloop "b1" "len" ^
    " else if ~(32 <= val(word_sub (word_sub d a) (word off):int64))" ^
    " then " ^ byteloop "b2" "len" ^
    " else if len < 32 then " ^ loop3 "a3" "len DIV 8" ^
    " else APPEND " ^ tail2 ^
    " (APPEND (" ^ ev "v2e" full ^ ") (APPEND (ENUMERATEL (len DIV 32) (\\i. " ^
    ev "v2l" full ^ " i)) (" ^ ev "v2p" full ^ "))) :(uarch_event)list");;

let EXT_INTRO_TAC =
  CONCRETIZE_F_EVENTS_TAC EXT_EVENTS_TERM THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `d:int64`; `off:num`; `len:num`; `S:1600 word`;
    `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              READ_MEMORY_WBYTES_VAL;
              fst MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_CLANG17_O3_EXEC] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `len < 2 EXP 32` ASSUME_TAC THENL
   [UNDISCH_TAC `off + len <= 200` THEN ARITH_TAC; ALL_TAC];;

let EXT_ARGS_TAC =
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  FIRST_ASSUM(fun th ->
    if concl th <> `~(len = 0)` then NO_TAC else
    RULE_ASSUM_TAC(fun th' ->
      if concl th' = concl th then th' else REWRITE_RULE[th] th'));;

let EXT_EXEC = MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_CLANG17_O3_EXEC;;

let EXT_LEN0_TAC =
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC EXT_EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The invariant of the loop over single bytes, after n0 + i bytes ***)

let EXT_INV1 n0 cnt =
  subst [n0,`n0:num`; cnt,`cnt:num`]
  `\i s. read X8 s = word(cnt - i) /\
         read X9 s = word_add a (word(off + n0 + i)) /\
         read X11 s = word_add d (word(n0 + i)) /\
         read X30 s = returnaddress /\
         read (memory :> bytes(a,200)) s = val(S:1600 word) /\
         read (memory :> bytes(d,n0 + i)) s =
         (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * (n0 + i))`;;

let BYTE_CNT_LEMMA_STMT =
  `!cnt i. i < cnt /\ cnt < 2 EXP 64
           ==> (val(word_sub (word (cnt - i)) (word 1):int64) = 0 <=>
                i + 1 = cnt) /\
               word_sub (word (cnt - i)) (word 1):int64 =
               word (cnt - (i + 1))`;;

let BYTE_CNT_LEMMA = assume_spec BYTE_CNT_LEMMA_STMT;;

(*** The test of the loop counter cnt - i, and its decrement ***)

let BYTE_CNT_TAC cnt =
  MP_TAC(SPECL [cnt; `i:num`] BYTE_CNT_LEMMA) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `len < 2 EXP 32` THEN CONV_TAC NUM_REDUCE_CONV THEN
      ARITH_TAC];
    DISCH_THEN(CONJUNCTS_THEN2
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]))];;

let EXT_BYTELOOP_TAC n0 cnt (pos:tactic) (pro:tactic) =
  ENSURES_EVENTS_WHILE_UP2_TAC cnt
   `pc + mlkem_keccakf1600_extract_bytes_loop1`
   `pc + mlkem_keccakf1600_extract_bytes_loop1_exit` (EXT_INV1 n0 cnt) THEN
  REPEAT CONJ_TAC THENL
   [pos;

    pro;

    (*** The loop body, copying one byte, and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    EXT_STATE_FACTS_TAC "s0" [subst [n0,`n0:num`] `n0 + i`] [] THEN
    ARM_STEPS_TAC EXT_EXEC (1--4) THEN
    BYTE_CNT_TAC cnt THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN (subst [cnt,`cnt:num`] `~(i + 1 = cnt) <=> i + 1 < cnt`)
      (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC (subst [cnt,`cnt:num`] `i < cnt`) THEN ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ADD_ASSOC]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ADD_ASSOC]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE (subst [n0,`n0:num`] `n0 + i + 1 = (n0 + i) + 1`)] THEN
      EXT_STORES_TAC THEN
      MATCH_MP_TAC READ_MEMORY_BYTES_EXTEND THEN CONJ_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The return ***)

    REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN (subst [n0,`n0:num`; cnt,`cnt:num`] `n0 + cnt = len`)
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [ARITH_TAC; ALL_TAC] THEN
    ARM_STEPS_TAC EXT_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

(*** The loop over blocks of 32 bytes, q = len DIV 32 iterations ***)

let LOOP2_CNT_LEMMA_STMT =
  `!q i. i < q /\ q < 2 EXP 32
         ==> (val(word_sub (word (32 * (q - i))) (word 32):int64) = 0 <=>
              i + 1 = q) /\
             word_sub (word (32 * (q - i))) (word 32):int64 =
             word (32 * (q - (i + 1)))`;;

let LOOP2_CNT_LEMMA = assume_spec LOOP2_CNT_LEMMA_STMT;;

let EXT_INV2 =
 `\i s. read X0 s = a /\ read X1 s = d /\
        read X8 s = word len /\ read X9 s = word off /\
        read X10 s = word(32 * (len DIV 32)) /\
        read X11 s = word_add (word_add a (word(off + 32 * i))) (word 16) /\
        read X12 s = word_add (word_add d (word(32 * i))) (word 16) /\
        read X13 s = word(32 * (len DIV 32 - i)) /\
        read X30 s = returnaddress /\
        read (memory :> bytes(a,200)) s = val(S:1600 word) /\
        read (memory :> bytes(d,32 * i)) s =
        (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * (32 * i))`;;

let EXT_MIDV =
 `\s. read X0 s = a /\ read X1 s = d /\
      read X8 s = word len /\ read X9 s = word off /\
      read X10 s = word(32 * (len DIV 32)) /\ read X30 s = returnaddress /\
      read (memory :> bytes(a,200)) s = val(S:1600 word) /\
      read (memory :> bytes(d,32 * (len DIV 32))) s =
      (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * (32 * (len DIV 32)))`;;


(*** After a store of k bytes at d + j, the output up to j + k = n ***)

let EXT_PREFIX_TAC j k n =
  let ppat = subst [j,`j:num`] `read (memory :> bytes(d:int64,j)) s = y`
  and cpat = subst [j,`j:num`; k,`k:num`]
    `read (memory :> bytes(word_add (d:int64) (word j),k)) s = y` in
  let eth = ARITH_RULE(mk_eq(mk_binop `(+):num->num->num` j k,n)) in
  EXT_STORES_TAC THEN
  FIRST_ASSUM(fun pth ->
    if not(can (term_match [] ppat) (concl pth)) then NO_TAC else
    FIRST_ASSUM(fun cth ->
      if not(can (term_match [] cpat) (concl cth)) then NO_TAC else
      ASSUME_TAC(REWRITE_RULE[eth]
        (MATCH_MP READ_MEMORY_BYTES_EXTEND (CONJ pth cth)))));;


let WORD_AND_FFFFFFE0_32_STMT =
  `!n. n < 2 EXP 32
       ==> word_and (word n:int32) (word 4294967264) = word(32 * n DIV 32)`;;

let WORD_AND_FFFFFFE0_32 = assume_spec WORD_AND_FFFFFFE0_32_STMT;;

let WORD_AND_FFFFFFE0_64_STMT =
  `!n. n < 2 EXP 32
       ==> word_and (word n:int64) (word 4294967264) = word(32 * n DIV 32)`;;

let WORD_AND_FFFFFFE0_64 = assume_spec WORD_AND_FFFFFFE0_64_STMT;;

let READ_MEMORY_BYTES128_OF_NUM_16_STMT =
  `!a:int64 m n k s:armstate.
        read (memory :> bytes(a,m)) s = n /\ k + 32 <= m
        ==> read (memory :> bytes128(word_add (word_add a (word k)) (word 16)))
                 s =
            word((n DIV 2 EXP (8 * (k + 16))) MOD 2 EXP 128)`;;

let READ_MEMORY_BYTES128_OF_NUM_16 =
  assume_spec READ_MEMORY_BYTES128_OF_NUM_16_STMT;;

let LOOP2_CNT_TAC =
  MP_TAC(SPECL [`len DIV 32`; `i:num`] LOOP2_CNT_LEMMA) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `len < 2 EXP 32` THEN ARITH_TAC];
    DISCH_THEN(CONJUNCTS_THEN2
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]))];;

let EXT_V2_PRO =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC EXT_EXEC (1--1) THEN EXT_ARGS_TAC THEN
  ARM_STEPS_TAC EXT_EXEC (2--3) THEN
  MAP_EVERY EXT_STEP_TAC (4--16) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[WORD_AND_FFFFFFE0_64] THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0; READ_COMPONENT_COMPOSE;
              READ_BYTES_TRIVIAL; EXP; MOD_1; SUB_0] THEN
  CONJ_TAC THENL [CONV_TAC WORD_RULE; DISCHARGE_SAFETY_PROPERTY_TAC];;

let EXT_V2_BODY =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN `32 * i + 32 <= len` ASSUME_TAC THENL
   [UNDISCH_TAC `i < len DIV 32` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `200`; `val(S:1600 word)`; `off + 32 * i`;
                `s0:armstate`] READ_MEMORY_BYTES128_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `off + len <= 200` THEN
    UNDISCH_TAC `32 * i + 32 <= len` THEN ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `200`; `val(S:1600 word)`; `(off + 32 * i) + 16`;
                `s0:armstate`] READ_MEMORY_BYTES128_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `off + len <= 200` THEN
    UNDISCH_TAC `32 * i + 32 <= len` THEN ARITH_TAC;
    DISCH_TAC] THEN
  ARM_STEPS_TAC EXT_EXEC (1--6) THEN
  LOOP2_CNT_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(i + 1 = len DIV 32) <=> i + 1 < len DIV 32`
    (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `i < len DIV 32` THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `off + 32 * (i + 1) = (off + 32 * i) + 32`;
                WORD_ADD] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `32 * (i + 1) = 32 * i + 32`; WORD_ADD] THEN
    CONV_TAC WORD_RULE; ALL_TAC] THEN
  CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE
       [ARITH_RULE `(off + 32 * i) + 16 = off + (32 * i + 16)`]) THEN
    EXT_PREFIX_TAC `32 * i` `16` `32 * i + 16` THEN
    EXT_PREFIX_TAC `32 * i + 16` `16` `32 * i + 32` THEN
    REWRITE_TAC[ARITH_RULE `32 * (i + 1) = 32 * i + 32`] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The tail of the loop of blocks of 32 bytes ***)

let TAIL_CMP_LEMMA_STMT =
  `!len. len < 2 EXP 32
         ==> (val(word_sub (word (32 * len DIV 32)) (word len):int64) = 0 <=>
              len MOD 32 = 0)`;;

let TAIL_CMP_LEMMA = assume_spec TAIL_CMP_LEMMA_STMT;;

let TAIL_CMP_TAC =
  MP_TAC(SPEC `len:num` TAIL_CMP_LEMMA) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN EXT_BRANCH_TAC;;

let VAL_WORD_AND_31_STMT =
  `!n. val(word_and (word n:int64) (word 31)) = (n MOD 2 EXP 64) MOD 32`;;

let VAL_WORD_AND_31 = assume_spec VAL_WORD_AND_31_STMT;;

let TST24_BLAST = BITBLAST_RULE
 `!y:int64. word_and y (word 24) = word 0 <=>
            word_ult (word_and y (word 31)) (word 8)`;;

let TST24_LEMMA_STMT =
  `!n. n < 2 EXP 32
       ==> (val(word_and (word n:int64) (word 24)) = 0 <=> n MOD 32 < 8)`;;

let TST24_LEMMA = assume_spec TST24_LEMMA_STMT;;

let TAIL_TST_TAC =
  MP_TAC(SPEC `len:num` TST24_LEMMA) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN EXT_BRANCH_TAC;;


let WORD_SUB_MOD32_STMT =
  `!len. word_sub (word len) (word (32 * len DIV 32)):int64 = word (len MOD 32)`;;

let WORD_SUB_MOD32 = assume_spec WORD_SUB_MOD32_STMT;;

let WORD_ADD_PTR_STMT =
  `!a:int64 m n. word_add (word_add a (word m)) (word n) = word_add a (word (n + m))`;;

let WORD_ADD_PTR = assume_spec WORD_ADD_PTR_STMT;;

let EXT_T21_PRO =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC EXT_EXEC (1--2) THEN TAIL_CMP_TAC THEN
  ARM_STEPS_TAC EXT_EXEC (3--4) THEN TAIL_TST_TAC THEN
  ARM_STEPS_TAC EXT_EXEC (5--8) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES; SUB_0; WORD_SUB_MOD32; WORD_ADD_PTR] THEN
  ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The loop over blocks of 8 bytes ***)

let WORD_AND_FFFFFFF8_64_STMT =
  `!n. n < 2 EXP 32
       ==> word_and (word n:int64) (word 4294967288) = word(8 * n DIV 8)`;;

let WORD_AND_FFFFFFF8_64 = assume_spec WORD_AND_FFFFFFF8_64_STMT;;

let LOOP3_SUB_STMT =
  `!n0 k i. word_add (word_sub (word (n0 + 8 * i)) (word (n0 + 8 * k)))
                     (word 8):int64 =
            word_sub (word (n0 + 8 * (i + 1))) (word (n0 + 8 * k))`;;

let LOOP3_SUB = assume_spec LOOP3_SUB_STMT;;

let LOOP3_ZERO_STMT =
  `!n0 k i. i < k /\ n0 + 8 * k < 2 EXP 64
            ==> (val(word_sub (word (n0 + 8 * (i + 1)))
                              (word (n0 + 8 * k)):int64) = 0
                 <=> i + 1 = k)`;;

let LOOP3_ZERO = assume_spec LOOP3_ZERO_STMT;;

let EXT_INV3 n0 k3 =
  subst [n0,`n0:num`; k3,`k3:num`]
  `\i s. read X0 s = a /\ read X1 s = d /\
         read X8 s = word len /\ read X9 s = word off /\
         read X10 s = word(n0 + 8 * k3) /\
         read X11 s = word_add a (word(off + n0 + 8 * i)) /\
         read X12 s = word_add d (word(n0 + 8 * i)) /\
         read X13 s = word_sub (word(n0 + 8 * i)) (word(n0 + 8 * k3)) /\
         read X30 s = returnaddress /\
         read (memory :> bytes(a,200)) s = val(S:1600 word) /\
         read (memory :> bytes(d,n0 + 8 * i)) s =
         (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * (n0 + 8 * i))`;;

let EXT_MID3 =
 `\s. read X0 s = a /\ read X1 s = d /\
      read X8 s = word len /\ read X9 s = word off /\
      read X10 s = word(8 * (len DIV 8)) /\ read X30 s = returnaddress /\
      read (memory :> bytes(a,200)) s = val(S:1600 word) /\
      read (memory :> bytes(d,8 * (len DIV 8))) s =
      (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * (8 * (len DIV 8)))`;;

let LOOP3_CNT_TAC n0 k3 =
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [n0; k3; `i:num`] LOOP3_SUB]) THEN
  MP_TAC(SPECL [n0; k3; `i:num`] LOOP3_ZERO) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC (subst [n0,`n0:num`; k3,`k3:num`] `n0 + 8 * k3 <= len`) THEN
      UNDISCH_TAC `len < 2 EXP 32` THEN
      SPEC_TAC(k3,`k:num`) THEN SPEC_TAC(n0,`m:num`) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC];
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                         REWRITE_TAC[th])];;

let DIV8_AUX_STMT =
  `!q r. 8 * ((32 * q + r) DIV 8) = 32 * q + 8 * (r DIV 8)`;;

let DIV8_AUX = assume_spec DIV8_AUX_STMT;;
let DIV8_SPLIT_STMT =
  `!len. 8 * (len DIV 8) = 32 * (len DIV 32) + 8 * ((len MOD 32) DIV 8)`;;

let DIV8_SPLIT = assume_spec DIV8_SPLIT_STMT;;


let ZX64_128 = BITBLAST_RULE `!w:int64. word_zx(word_zx w:int128):int64 = w`;;

let LOOP3_ASSOC_STMT =
  `!n i. n + 8 * (i + 1) = (n + 8 * i) + 8`;;

let LOOP3_ASSOC = assume_spec LOOP3_ASSOC_STMT;;

let EXT_LOOP3_BODY n0 k3 =
  let sb = subst [n0,`n0:num`; k3,`k3:num`] in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN (sb `n0 + 8 * k3 <= len`) ASSUME_TAC THENL
   [SUBGOAL_THEN (sb `n0 + 8 * k3 = 8 * (len DIV 8)`) SUBST1_TAC THENL
     [FIRST [ACCEPT_TAC(SYM(SPEC `len:num` DIV8_SPLIT)); REWRITE_TAC[ADD_CLAUSES]]; ALL_TAC] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (sb `n0 + 8 * i + 8 <= len`) ASSUME_TAC THENL
   [UNDISCH_TAC (sb `n0 + 8 * k3 <= len`) THEN
    UNDISCH_TAC (sb `i < k3`) THEN
    SPEC_TAC(k3,`k:num`) THEN SPEC_TAC(n0,`m:num`) THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `200`; `val(S:1600 word)`; sb `off + n0 + 8 * i`;
                `s0:armstate`] READ_MEMORY_BYTES64_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `off + len <= 200` THEN
    UNDISCH_TAC (sb `n0 + 8 * i + 8 <= len`) THEN
    SPEC_TAC(n0,`m:num`) THEN ARITH_TAC;
    DISCH_TAC] THEN
  ARM_STEPS_TAC EXT_EXEC (1--4) THEN
  LOOP3_CNT_TAC n0 k3 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (sb `~(i + 1 = k3) <=> i + 1 < k3`)
    (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC (sb `i < k3`) THEN SPEC_TAC(k3,`k:num`) THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[WORD_ADD_PTR] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    SPEC_TAC(n0,`m:num`) THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[WORD_ADD_PTR] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    SPEC_TAC(n0,`m:num`) THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[ZX64_128]) THEN
    REWRITE_TAC[SPECL [n0; `i:num`] LOOP3_ASSOC] THEN
    EXT_STORES_TAC THEN
    MATCH_MP_TAC READ_MEMORY_BYTES_EXTEND THEN CONJ_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let EXT_LOOP3_EXIT n0 k3 =
  let sb = subst [n0,`n0:num`; k3,`k3:num`] in
  REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN (sb `n0 + 8 * k3 = 8 * (len DIV 8)`)
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [FIRST [ACCEPT_TAC(SYM(SPEC `len:num` DIV8_SPLIT)); REWRITE_TAC[ADD_CLAUSES]]; ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The loop of blocks of 8 bytes, and then the continuation tail ***)

let EXT_LOOP3_PHASE nested n0 k3 (pos:tactic) (pro:tactic) (tail:tactic) =
  (if nested then ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] else ALL_TAC) THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_keccakf1600_extract_bytes_loop3_exit`
    EXT_MID3 THEN CONJ_TAC THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC k3
      `pc + mlkem_keccakf1600_extract_bytes_loop3`
      `pc + mlkem_keccakf1600_extract_bytes_loop3_exit` (EXT_INV3 n0 k3) THEN
    REPEAT CONJ_TAC THENL
     [pos; pro; EXT_LOOP3_BODY n0 k3; EXT_LOOP3_EXIT n0 k3];
    tail];;

let EXT_A3_PRO =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC EXT_EXEC (1--1) THEN EXT_ARGS_TAC THEN
  ARM_STEPS_TAC EXT_EXEC (2--3) THEN
  MAP_EVERY EXT_STEP_TAC (4--19) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[WORD_AND_FFFFFFF8_64] THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; WORD_ADD_0; READ_COMPONENT_COMPOSE;
              READ_BYTES_TRIVIAL; EXP; MOD_1; SUB_0] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The tail after the loop of blocks of 8 bytes ***)

let TAIL3_CMP_LEMMA_STMT =
  `!len. len < 2 EXP 32
         ==> (val(word_sub (word (8 * len DIV 8)) (word len):int64) = 0 <=>
              len MOD 8 = 0)`;;

let TAIL3_CMP_LEMMA = assume_spec TAIL3_CMP_LEMMA_STMT;;

let TAIL3_CMP_TAC =
  MP_TAC(SPEC `len:num` TAIL3_CMP_LEMMA) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN EXT_BRANCH_TAC;;

let WORD_SUB_MOD8_STMT =
  `!len. word_sub (word len) (word (8 * len DIV 8)):int64 = word (len MOD 8)`;;

let WORD_SUB_MOD8 = assume_spec WORD_SUB_MOD8_STMT;;

let EXT_T30_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN `8 * (len DIV 8) = len`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [UNDISCH_TAC `len MOD 8 = 0` THEN ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXT_STEP_TAC (1--3) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let EXT_T31_PRO =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC EXT_EXEC (1--2) THEN TAIL3_CMP_TAC THEN
  ARM_STEPS_TAC EXT_EXEC (3--7) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_0; SUB_0; WORD_SUB_MOD8; WORD_ADD_PTR] THEN
  ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let EXT_TAIL3_TAC =
  ASM_CASES_TAC `len MOD 8 = 0` THEN ASM_REWRITE_TAC[] THENL
   [EXT_T30_TAC;
    EXT_BYTELOOP_TAC `8 * (len DIV 8)` `(len MOD 8):num`
     (UNDISCH_TAC `~(len MOD 8 = 0)` THEN ARITH_TAC) EXT_T31_PRO];;


(*** The case len MOD 32 >= 8, entering the loop of blocks of 8 bytes ***)

let EXT_T3_PRO =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC EXT_EXEC (1--2) THEN TAIL_CMP_TAC THEN
  ARM_STEPS_TAC EXT_EXEC (3--4) THEN TAIL_TST_TAC THEN
  ARM_STEPS_TAC EXT_EXEC (5--10) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[WORD_AND_FFFFFFF8_64] THEN
  SUBST1_TAC(SPEC `len:num` DIV8_SPLIT) THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; WORD_ADD_0; WORD_ADD_PTR] THEN
  ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let EXT_T20_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN `32 * (len DIV 32) = len`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [UNDISCH_TAC `len MOD 32 = 0` THEN ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXT_STEP_TAC (1--3) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let EXT_V2_EXIT =
  REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let EXT_TAIL2_TAC =
  ASM_CASES_TAC `len MOD 32 = 0` THEN ASM_REWRITE_TAC[] THENL
   [EXT_T20_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `len MOD 32 < 8` THEN ASM_REWRITE_TAC[] THENL
   [EXT_BYTELOOP_TAC `32 * (len DIV 32)` `(len MOD 32):num`
      (UNDISCH_TAC `~(len MOD 32 = 0)` THEN ARITH_TAC) EXT_T21_PRO;
    EXT_LOOP3_PHASE true `32 * (len DIV 32)` `(len MOD 32) DIV 8`
      (UNDISCH_TAC `~(len MOD 32 < 8)` THEN SPEC_TAC(`len MOD 32`,`r:num`) THEN
       ARITH_TAC)
      EXT_T3_PRO EXT_TAIL3_TAC];;

let EXT_PATH_A_TAC =
  EXT_LOOP3_PHASE false `0` `len DIV 8` (UNDISCH_TAC `~(len <= 7)` THEN ARITH_TAC)
    EXT_A3_PRO EXT_TAIL3_TAC;;

let EXT_PATH_B_TAC =
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_keccakf1600_extract_bytes_loop2_exit`
    EXT_MIDV THEN CONJ_TAC THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `len DIV 32`
      `pc + mlkem_keccakf1600_extract_bytes_loop2`
      `pc + mlkem_keccakf1600_extract_bytes_loop2_exit` EXT_INV2 THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `~(len < 32)` THEN ARITH_TAC;
      EXT_V2_PRO; EXT_V2_BODY; EXT_V2_EXIT];
    EXT_TAIL2_TAC];;

let EXT_POS0_TAC = UNDISCH_TAC `~(len = 0)` THEN ARITH_TAC;;

let EXT_B1_PRO =
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC EXT_EXEC (1--1) THEN EXT_ARGS_TAC THEN
    ARM_STEPS_TAC EXT_EXEC (2--3) THEN
    MAP_EVERY EXT_STEP_TAC (4--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; MULT_CLAUSES; EXP;
                MOD_1; ADD_CLAUSES; SUB_0; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;;
let EXT_B2_PRO =
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC EXT_EXEC (1--1) THEN EXT_ARGS_TAC THEN
    ARM_STEPS_TAC EXT_EXEC (2--3) THEN
    MAP_EVERY EXT_STEP_TAC (4--14) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; MULT_CLAUSES; EXP;
                MOD_1; ADD_CLAUSES; SUB_0; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;;

let EXT_MAIN_TAC =
  EXT_INTRO_TAC THEN
  ASM_CASES_TAC `len = 0` THEN ASM_REWRITE_TAC[] THENL
   [EXT_LEN0_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `len <= 7` THEN ASM_REWRITE_TAC[] THENL
   [EXT_BYTELOOP_TAC `0` `len:num` EXT_POS0_TAC EXT_B1_PRO; ALL_TAC] THEN
  ASM_CASES_TAC `32 <= val(word_sub (word_sub d a) (word off):int64)` THEN
  ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    EXT_BYTELOOP_TAC `0` `len:num` EXT_POS0_TAC EXT_B2_PRO] THEN
  ASM_CASES_TAC `len < 32` THEN ASM_REWRITE_TAC[] THENL
   [EXT_PATH_A_TAC; EXT_PATH_B_TAC];;


(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, for callers  *)
(* whose events depend on the result, such as the rejection sampling in      *)
(* mlkem_poly_rej_uniform. As in common/fips202.ml, the state is a 1600-bit  *)
(* word S, and the bytes extracted are bytes off to off + len - 1 of it,     *)
(* which as a number are (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len).    *)
(* The output is built up from the start as a number in all the paths. The  *)
(* events are given by the path: the byte loop (entered after one or two     *)
(* tests), a straight line for 8 <= len < 16, or the loop over the blocks of *)
(* 16 bytes and a straight line depending on len MOD 16. The theorems of     *)
(* correctness and of constant time and memory safety are derived from this  *)
(* one.                                                                      *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
       forall e a d off len (S:1600 word) pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           off + len <= 200 /\
           ALL (nonoverlapping (d,len)) [word pc,libmlkem_size; a,200]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem_keccakf1600_extract_bytes) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; d; word off; word len] s /\
                    read (memory :> wbytes a) s = S /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    read (memory :> bytes(d,len)) s =
                    (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a d off len pc returnaddress /\
                         memaccess_inbounds e2 [a,200; d,len] [d,len]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (d,len)])`;;

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* The theorems of correctness and of constant time and memory safety, from  *)
(* the combined one.                                                         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a d off len (S:1600 word) pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        off + len <= 200 /\
        ALL (nonoverlapping (d,len)) [(word pc,libmlkem_size); (a,200)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem_keccakf1600_extract_bytes) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; d; word off; word len] s /\
                  read (memory :> wbytes a) s = S)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(d,len)) s =
                  (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(d,len)])`;;

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e a d off len pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           off + len <= 200 /\
           ALL (nonoverlapping (d,len)) [word pc,libmlkem_size; a,200]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem_keccakf1600_extract_bytes) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; d; word off; word len] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a d off len pc returnaddress /\
                         memaccess_inbounds e2 [a,200; d,len] [d,len]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (d,len)])`;;

let MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
