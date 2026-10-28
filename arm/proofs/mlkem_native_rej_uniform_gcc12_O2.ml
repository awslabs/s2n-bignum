(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform rejection sampling for ML-KEM.                                    *)
(* This is the code for mlk_rej_uniform_c from mlkem-native's portable C     *)
(* implementation as specialized and compiled by gcc 12 with -O2, the        *)
(* function mlk_rej_uniform_c.constprop.0 in the binary (see                 *)
(* mlkem_native/README.md). Unlike the hand-written kernel, it appends to    *)
(* the coefficients already sampled, from a given offset, and does not use a *)
(* table or a temporary buffer on the stack.                                 *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/consttime.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;

(**** print_literal_from_elf
        "arm/mlkem_native/mlkem_native_rej_uniform_gcc12_O2.o";;
 ****)

let mlkem_native_rej_uniform_gcc12_O2_mc = define_assert_from_elf
  "mlkem_native_rej_uniform_gcc12_O2_mc"
  "arm/mlkem_native/mlkem_native_rej_uniform_gcc12_O2.o"
[
  0xaa0003e8;       (* arm_MOV X8 X0 *)
  0x2a0103e0;       (* arm_MOV W0 W1 *)
  0x7103fc3f;       (* arm_CMP W1 (rvalue (word 255)) *)
  0x54000468;       (* arm_BHI (word 140) *)
  0x52800069;       (* arm_MOV W9 (rvalue (word 3)) *)
  0x5281a00b;       (* arm_MOV W11 (rvalue (word 3328)) *)
  0x4b020129;       (* arm_SUB W9 W9 W2 *)
  0x52801fea;       (* arm_MOV W10 (rvalue (word 255)) *)
  0x1400000d;       (* arm_B (word 52) *)
  0x7134003f;       (* arm_CMP W1 (rvalue (word 3328)) *)
  0x2a0003e5;       (* arm_MOV W5 W0 *)
  0x7a4ad002;       (* arm_CCMP W0 W10 (word 2) Condition_LE *)
  0x540000a8;       (* arm_BHI (word 20) *)
  0x110004a0;       (* arm_ADD W0 W5 (rvalue (word 1)) *)
  0x78255901;       (* arm_STRH W1 X8
                       (Shiftreg_Offset (Extendedreg W5 UXTW) 1) *)
  0x7104001f;       (* arm_CMP W0 (rvalue (word 256)) *)
  0x540002c0;       (* arm_BEQ (word 88) *)
  0x91000c42;       (* arm_ADD X2 X2 (rvalue (word 3)) *)
  0x0b020121;       (* arm_ADD W1 W9 W2 *)
  0x6b01007f;       (* arm_CMP W3 W1 *)
  0x54000243;       (* arm_BCC (word 72) *)
  0x39400444;       (* arm_LDRB W4 X2 (Immediate_Offset (word 1)) *)
  0x11000405;       (* arm_ADD W5 W0 (rvalue (word 1)) *)
  0x39400047;       (* arm_LDRB W7 X2 (Immediate_Offset (word 0)) *)
  0x39400841;       (* arm_LDRB W1 X2 (Immediate_Offset (word 2)) *)
  0x53047c86;       (* arm_LSR W6 W4 4 *)
  0x2a0420e4;       (* arm_ORR W4 W7 (Shiftedreg W4 LSL 8) *)
  0x12002c84;       (* arm_AND W4 W4 (rvalue (word 4095)) *)
  0x2a0110c1;       (* arm_ORR W1 W6 (Shiftedreg W1 LSL 4) *)
  0x7134009f;       (* arm_CMP W4 (rvalue (word 3328)) *)
  0x54fffd6c;       (* arm_BGT (word 2097068) *)
  0x78205904;       (* arm_STRH W4 X8
                       (Shiftreg_Offset (Extendedreg W0 UXTW) 1) *)
  0x7103fcbf;       (* arm_CMP W5 (rvalue (word 255)) *)
  0x7a4b9020;       (* arm_CCMP W1 W11 (word 0) Condition_LS *)
  0x2a0503e0;       (* arm_MOV W0 W5 *)
  0x54fffd4d;       (* arm_BLE (word 2097064) *)
  0x7104001f;       (* arm_CMP W0 (rvalue (word 256)) *)
  0x54fffd81;       (* arm_BNE (word 2097072) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let MLKEM_NATIVE_REJ_UNIFORM_GCC12_O2_EXEC =
  ARM_MK_EXEC_RULE mlkem_native_rej_uniform_gcc12_O2_mc;;

(* ------------------------------------------------------------------------- *)
(* The sampling as in the specification of the hand-written kernel, where    *)
(* the input buffer is a list of 12-bit words (two from each 3 bytes).       *)
(* ------------------------------------------------------------------------- *)

let REJ_SAMPLE = define
 `REJ_SAMPLE l = FILTER (\x. val x < 3329) (MAP (word_zx:12 word->int16) l)`;;

let REJ_SAMPLE_EMPTY = prove
 (`REJ_SAMPLE [] = []`,
  REWRITE_TAC[REJ_SAMPLE; FILTER; MAP]);;

let REJ_SAMPLE_APPEND = prove
 (`!l1 l2. REJ_SAMPLE(APPEND l1 l2) =
           APPEND (REJ_SAMPLE l1) (REJ_SAMPLE l2)`,
  REWRITE_TAC[REJ_SAMPLE; MAP_APPEND; FILTER_APPEND]);;

let VAL_WORD_ZX_12_16 = prove
 (`!x:12 word. val(word_zx x:int16) = val x`,
  GEN_TAC THEN MATCH_MP_TAC VAL_WORD_ZX THEN
  REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  ARITH_TAC);;

let REJ_SAMPLE_PAIR = prove
 (`!v0 v1:12 word.
        REJ_SAMPLE [v0; v1] =
        APPEND (if val v0 < 3329 then [word_zx v0] else [])
               (if val v1 < 3329 then [word_zx v1] else [])`,
  REWRITE_TAC[REJ_SAMPLE; MAP; FILTER; VAL_WORD_ZX_12_16] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `val(v0:12 word) < 3329` THEN
  ASM_CASES_TAC `val(v1:12 word) < 3329` THEN ASM_REWRITE_TAC[APPEND]);;

(* ------------------------------------------------------------------------- *)
(* The bytes of the group of 3 bytes giving the 12-bit words 2 * i and       *)
(* 2 * i + 1 in the list.                                                    *)
(* ------------------------------------------------------------------------- *)

let DIMINDEX_12 = DIMINDEX_CONV `dimindex(:12)`;;
let DIMINDEX_24 = DIMINDEX_CONV `dimindex(:24)`;;

let REJ_GROUP_BYTES = prove
 (`!buf n (l:(12 word)list) i s:armstate.
        read (memory :> bytes(buf,n)) s = num_of_wordlist l /\
        8 * n = 12 * LENGTH l /\ 3 * i + 3 <= n
        ==> !k. k < 3
                ==> read (memory :> bytes8(word_add buf (word(3 * i + k)))) s =
                    word_subword (word_join (EL (2 * i + 1) l) (EL (2 * i) l)
                                  :24 word) (8 * k,8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD] THEN
  SIMP_TAC[VAL_WORD_JOIN_SIMPLE; DIMINDEX_12; DIMINDEX_24; ARITH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
   `4096 * val (EL (2 * i + 1) (l:(12 word)list)) + val (EL (2 * i) l) =
    (num_of_wordlist l DIV 2 EXP (24 * i)) MOD 2 EXP 24`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`l:(12 word)list`; `2 * i`; `2`]
           NUM_OF_WORDLIST_SUB_LIST) THEN
    REWRITE_TAC[DIMINDEX_12; ARITH_RULE `12 * 2 * i = 24 * i`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `2 * i + 2 <= LENGTH(l:(12 word)list)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `2 = 1 + 1`; SUB_LIST_SPLIT] THEN
    REWRITE_TAC[SUB_LIST_1; ARITH_RULE `1 + 1 = 2`] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `2 * i + 2 <= l ==> 2 * i < l /\ 2 * i + 1 < l`] THEN
    REWRITE_TAC[APPEND; num_of_wordlist; DIMINDEX_12] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `val (read (memory :> bytes8 (word_add buf (word (3 * i + k)))) s) =
    (num_of_wordlist (l:(12 word)list) DIV 2 EXP (8 * (3 * i + k))) MOD
    2 EXP (8 * 1)`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl) o
      check (fun th -> free_in `num_of_wordlist (l:(12 word)list)`
                               (concl th))) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD] THEN
    REWRITE_TAC[GSYM READ_BYTES_BYTES8] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_8; ARITH_RULE `8 * (3 * i + k) = 24 * i + 8 * k`] THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `MIN 8 8 = 8`] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The signed comparisons of small 32-bit numbers, the position in the       *)
(* buffer as compared by the code, and the 16-bit values stored.             *)
(* ------------------------------------------------------------------------- *)

let WORD_CMP_32_SFLAGS = prove
 (`!x y. x < 2147483648 /\ y < 2147483648
         ==> (ival(word_sub (word x) (word y):int32) < &0 <=> x < y) /\
             (ival(word x:int32) - &y =
              ival(word_sub (word x) (word y):int32)) /\
             (ival(word x:int32) - ival(word y:int32) =
              ival(word_sub (word x) (word y):int32))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN STRIP_TAC THEN
  SUBGOAL_THEN `ival(word x:int32) = &x /\ ival(word y:int32) = &y`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[WORD_IWORD] THEN CONJ_TAC THEN MATCH_MP_TAC IVAL_IWORD THEN
    REWRITE_TAC[DIMINDEX_32] THEN
    CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ival(word_sub (word x) (word y):int32) = &x - &y`
  SUBST1_TAC THENL
   [REWRITE_TAC[WORD_RULE `word_sub (word x) (word y):int32 =
                           iword(&x - &y)`] THEN
    MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN
    CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN ASM_INT_ARITH_TAC;
    ASM_REWRITE_TAC[INT_LT_SUB_RADD; INT_ADD_LID; INT_OF_NUM_LT] THEN
    INT_ARITH_TAC]);;

(*** The code compares the buffer length with w9 + w2 = (3 - buf) + x2 ***)

let REJ_POS_LEMMA = prove
 (`!(buf:int64) k.
        k + 6 < 4294967296
        ==> word_zx(word_add
                     (word_zx(word_zx(word_sub (word 3) (word_zx buf):int32)
                              :int64))
                     (word_zx(word_add (word_add buf (word k)) (word 3)))
                    :int32):int64 =
            word(k + 6)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[BITBLAST_RULE
   `!buf w:int64.
      word_zx(word_add
               (word_zx(word_zx(word_sub (word 3) (word_zx buf):int32)
                        :int64))
               (word_zx(word_add (word_add buf w) (word 3))):int32):int64 =
      word_zx(word_add (word_zx w) (word 6):int32)`] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `k + 6 < 4294967296 ==> k < 18446744073709551616 /\ k < 4294967296`]);;

let WORD_ZX_32_64_SMALL = prove
 (`!n. n < 4294967296 ==> word_zx(word n:int32):int64 = word n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_zx; VAL_WORD; DIMINDEX_32] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let WORD_ZX_STORED = prove
 (`!n. n < 65536
       ==> word_zx(word n:int32):int16 = word n /\
           word_zx(word n:int64):int16 = word n /\
           word_zx(word_zx(word n:int64):int32):int16 = word n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[word_zx; VAL_WORD; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `n < 65536 ==> n < 18446744073709551616 /\ n < 4294967296`]);;

(* ------------------------------------------------------------------------- *)
(* Reading lists of 16-bit words, built up element by element.               *)
(* ------------------------------------------------------------------------- *)

let READ_BYTES16_APPEND = prove
 (`!(a:int64) (l1:int16 list) (l2:int16 list) s:armstate.
     read (memory :> bytes(a,2 * LENGTH l1)) s = num_of_wordlist l1 /\
     read (memory :> bytes(word_add a (word(2 * LENGTH l1)),2 * LENGTH l2)) s =
     num_of_wordlist l2
     ==> read (memory :> bytes(a,2 * LENGTH(APPEND l1 l2))) s =
         num_of_wordlist(APPEND l1 l2)`,
  REWRITE_TAC[LENGTH_APPEND; NUM_OF_WORDLIST_APPEND; LEFT_ADD_DISTRIB;
              READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE; DIMINDEX_16] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `8 * 2 * n = 16 * n`]);;

let READ_BYTES16_CONS = prove
 (`!(a:int64) x (l:int16 list) s:armstate.
     read (memory :> bytes16 a) s = x /\
     read (memory :> bytes(word_add a (word 2),2 * LENGTH l)) s =
     num_of_wordlist l
     ==> read (memory :> bytes(a,2 * LENGTH(CONS x l))) s =
         num_of_wordlist(CONS x l)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `2 * SUC n = 2 + 2 * n`; num_of_wordlist] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE; DIMINDEX_16] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    can (term_match [] `read (bytes16 a) s = x`) (concl th))) THEN
  REWRITE_TAC[BYTES16_WBYTES; VAL_READ_WBYTES; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIMINDEX_16] THEN ARITH_TAC);;

let READ_BYTES16_NIL = prove
 (`!(a:int64) s:armstate.
     read (memory :> bytes(a,2 * LENGTH([]:int16 list))) s =
     num_of_wordlist([]:int16 list)`,
  REWRITE_TAC[LENGTH; MULT_CLAUSES; READ_COMPONENT_COMPOSE;
              READ_BYTES_TRIVIAL; num_of_wordlist]);;

(* ------------------------------------------------------------------------- *)
(* Taking initial segments of the sampled list.                              *)
(* ------------------------------------------------------------------------- *)

let SUB_LIST_APPEND_RIGHT = prove
 (`!l1 l2:A list n.
        LENGTH l1 <= n
        ==> SUB_LIST(0,n) (APPEND l1 l2) =
            APPEND l1 (SUB_LIST(0,n - LENGTH l1) l2)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; LENGTH; SUB_0] THEN
  X_GEN_TAC `l2:A list` THEN INDUCT_TAC THEN
  REWRITE_TAC[LE; NOT_SUC; LE_SUC; SUB_LIST_CLAUSES; SUB_SUC; CONS_11] THEN
  ASM_SIMP_TAC[]);;

let SUB_LIST_REJ_SAMPLE_PREFIX = prove
 (`!(l:(12 word)list) k m.
        m <= LENGTH(REJ_SAMPLE(SUB_LIST(0,k) l)) \/ LENGTH l <= k
        ==> SUB_LIST(0,m) (REJ_SAMPLE l) =
            SUB_LIST(0,m) (REJ_SAMPLE(SUB_LIST(0,k) l))`,
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
     [GSYM(ISPECL [`l:(12 word)list`; `k:num`] SUB_LIST_TOPSPLIT)] THEN
    REWRITE_TAC[REJ_SAMPLE_APPEND] THEN
    MATCH_MP_TAC SUB_LIST_APPEND_LEFT THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[SUB_LIST_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Tactics for simulating the code for one group of 3 bytes, containing      *)
(* the two 12-bit values n0 and n1, where L is the list sampled so far.      *)
(* ------------------------------------------------------------------------- *)

(*** The PC in the current state ***)

let current_pc (asl,w) =
  let s = rand w in
  let th = snd(find (fun (_,th) -> try let l,_ = dest_eq(concl th) in
                                       l = mk_comb(`read PC`,s)
                                   with Failure _ -> false) asl) in
  rhs(concl th);;

(*** Decide a condition by arithmetic, keeping it as an assumption ***)

let DECIDE_PROP_TAC c =
  (SUBGOAL_THEN c
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[EQT_INTRO th]) THEN
               ASSUME_TAC th) THENL
    [SIMPLE_ARITH_TAC; ALL_TAC]) ORELSE
  (SUBGOAL_THEN (mk_neg c)
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[EQF_INTRO th]) THEN
               ASSUME_TAC th) THENL
    [SIMPLE_ARITH_TAC; ALL_TAC]);;

(*** Decide all the flags, including the signed ones, where possible ***)

let DECIDE_SFLAGS_TAC =
  W(fun (asl,w) ->
     let ps = mapfilter (fun (_,th) ->
       let l,r = dest_eq(concl th) in
       let f = rand(rator l) in
       if mem f [`CF`;`ZF`;`NF`;`VF`] && not(r = `T` || r = `F`) then r
       else failwith "") asl in
     MAP_EVERY (fun p -> TRY(DECIDE_PROP_TAC p)) ps);;

let CMP_SFLAGS_TAC pat th =
  W(fun (asl,w) ->
    let tms = setify (find_terms (can (term_match [] pat))
                                 (list_mk_conj(map (concl o snd) asl))) in
    MAP_EVERY (fun t ->
      let x = rand(lhand t) and y = rand(rand t) in
      MP_TAC(SPECL [x;y] th) THEN
      ANTS_TAC THENL
       [CONJ_TAC THEN SIMPLE_ARITH_TAC;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))]) tms);;

let W32S_DECIDE_FLAGS_TAC =
  W32_SMALL_TAC THEN
  CMP_SFLAGS_TAC `word_sub (word x) (word y):int32` WORD_CMP_32_FLAGS THEN
  CMP_SFLAGS_TAC `word_sub (word x) (word y):int32` WORD_CMP_32_SFLAGS THEN
  DECIDE_SFLAGS_TAC;;

(*** Decide the conditions in the flags set by the CCMP instructions ***)

let DECIDE_COND_TAC =
  W(fun (asl,w) ->
     let conds = setify(mapfilter (fun (_,th) ->
        let l,r = dest_eq(concl th) in
        if mem (rand(rator l)) [`CF`;`ZF`;`NF`;`VF`] && is_cond r
        then lhand(rator r) else failwith "") asl) in
     MAP_EVERY DECIDE_PROP_TAC conds);;

(*** Decide the condition of a conditional branch ***)

let DECIDE_BRANCH_TAC =
  FIRST_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if not (is_cond r) || not(can (term_match [] `read PC s`) l)
    then failwith "DECIDE_BRANCH_TAC" else
    DECIDE_PROP_TAC (lhand(rator r)));;

(*** Replace the value of a register by an equal one ***)

let REPLACE_REG_TAC r t =
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && (try rand(rator(lhs c)) = r with Failure _ -> false)
    then ASSUME_TAC(REWRITE_RULE[word_zx]
                     (TRANS th (BITBLAST_RULE(mk_eq(rhs c,t)))))
    else failwith "REPLACE_REG_TAC");;

(*** Replace 64-bit views of small 32-bit numbers ***)

let W64_SMALL_TAC =
  W(fun (asl,w) ->
    let tms = setify (find_terms
      (can (term_match [] `word_zx(word n:int32):int64`))
      (list_mk_conj(w::map (concl o snd) asl))) in
    MAP_EVERY (fun t ->
      MP_TAC(SPEC (rand(rand t)) WORD_ZX_32_64_SMALL) THEN
      ANTS_TAC THENL
       [SIMPLE_ARITH_TAC;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                             REWRITE_TAC[th])]) tms);;

let REJ_NORM_TAC =
  TRY W32_SMALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64; GSYM WORD_ADD]) THEN
  TRY W64_SMALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64; GSYM WORD_ADD]);;

(*** Discharging the memory safety conditions, as in the kernel proof ***)

let DISCHARGE_MEMSAFE_TAC:tactic =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

let STRIP_EXISTS_ASSUM_TAC =
  FIRST_X_ASSUM(CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC));;

(*** The setup for group number idx, splitting into cases on n0 and n1 ***)

let REJ_GROUP_TAC idx =
  let ix t = subst [idx,`i:num`] t in
  let e0 = ix `EL (2 * i) inlist:12 word`
  and e1 = ix `EL (2 * i + 1) inlist:12 word` in
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_SAMPLE_APPEND; LENGTH_APPEND;
                              REJ_SAMPLE_PAIR]) THEN
  REWRITE_TAC[REJ_SAMPLE_APPEND; REJ_SAMPLE_PAIR] THEN
  ABBREV_TAC (ix `L = REJ_SAMPLE(SUB_LIST(0,2 * i) inlist)`) THEN
  ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
  MP_TAC(SPECL [`buf:int64`; `buflen:num`; `inlist:(12 word)list`; idx;
                `s0:armstate`] REJ_GROUP_BYTES) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC e0 VAL_BOUND) THEN MP_TAC(ISPEC e1 VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_12] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ABBREV_TAC (mk_eq(`n0:num`,mk_comb(`val:12 word->num`,e0))) THEN
  ABBREV_TAC (mk_eq(`n1:num`,mk_comb(`val:12 word->num`,e1))) THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   (mk_conj(mk_eq(mk_comb(`word_zx:12 word->int16`,e0),`word n0:int16`),
            mk_eq(mk_comb(`word_zx:12 word->int16`,e1),`word n1:int16`)))
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[word_zx] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`buf:int64`; ix `3 * i`] REJ_POS_LEMMA) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    free_in `n0:num` (concl th) && free_in `L:int16 list` (concl th))) THEN
  ASM_CASES_TAC `n0 < 3329` THEN ASM_CASES_TAC `n1 < 3329` THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o CONV_RULE
   (REWRITE_CONV[LENGTH_APPEND; LENGTH; ADD_CLAUSES] THENC
    NUM_REDUCE_CONV));;

(*** The indices of the two stores, which use UXTW register offsets ***)

let REJ_UXTW_TAC =
  MP_TAC(SPEC `offset + LENGTH(L:int16 list)` VAL_WORD_ZX_UXTW) THEN
  MP_TAC(SPEC `(offset + LENGTH(L:int16 list)) + 1` VAL_WORD_ZX_UXTW) THEN
  REPEAT(ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC]);;

(*** One step, recognizing the two values once they have been computed ***)

let REJ_STEP_TAC idx posth n =
  (fun g -> if mem (current_pc g) [`word (pc + 56):int64`;
                                   `word (pc + 124):int64`]
            then REJ_UXTW_TAC g else ALL_TAC g) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_REJ_UNIFORM_GCC12_O2_EXEC [n] THEN
  (if n = 8 then
     let e0 = subst [idx,`i:num`] `EL (2 * i) inlist:12 word`
     and e1 = subst [idx,`i:num`] `EL (2 * i + 1) inlist:12 word` in
     REPLACE_REG_TAC `X4` (mk_comb(`word_zx:12 word->int64`,e0)) THEN
     REPLACE_REG_TAC `X1` (mk_comb(`word_zx:12 word->int64`,e1)) THEN
     RULE_ASSUM_TAC(REWRITE_RULE
      [ASSUME(mk_eq(mk_comb(`val:12 word->num`,e0),`n0:num`));
       ASSUME(mk_eq(mk_comb(`val:12 word->num`,e1),`n1:num`))])
   else ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[posth]) THEN
  REJ_NORM_TAC THEN TRY DECIDE_COND_TAC THEN
  TRY W32S_DECIDE_FLAGS_TAC THEN TRY DECIDE_BRANCH_TAC;;

(*** Simulate from the head of the group until the PC is the target ***)

let rec REJ_RUN_TAC idx posth n target (asl,w) =
  (REJ_STEP_TAC idx posth n THEN
   (fun g -> if current_pc g = target then ALL_TAC g
             else REJ_RUN_TAC idx posth (n + 1) target g)) (asl,w);;

let REJ_CASE_TAC idx target =
  let pos = subst [idx,`i:num`] `word(3 * i + 6):int64` in
  FIRST_ASSUM(fun th ->
    if (try rand(concl th) = pos with Failure _ -> false)
    then REJ_RUN_TAC idx th 1 target
    else failwith "REJ_CASE_TAC");;

(*** A stored coefficient, read at an address equal to the one written ***)

let READ16_TAC (asl,w) =
  let a = rand(rand(rand(rator(lhs w)))) and s = rand(lhs w) in
  let ths = filter (fun th ->
    try let l = lhs(concl th) in
        rand l = s && can (term_match [] `read (memory :> bytes16 a) s`) l
    with Failure _ -> false) (map snd asl) in
  let tac th =
    let a' = rand(rand(rand(rator(lhs(concl th))))) in
    SUBGOAL_THEN (mk_eq(a,a')) SUBST1_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
      REWRITE_TAC[th] THEN
      ASM_SIMP_TAC[WORD_ZX_STORED; ARITH_RULE `n < 4096 ==> n < 65536`]] in
  FIRST (map tac ths) (asl,w);;

(*** The final state: the count, the pointer, the stored list and the ***)
(*** memory accesses                                                  ***)

let REJ_CLOSE_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST
   [DISCHARGE_MEMSAFE_ASM_TAC;
    REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN AP_TERM_TAC THEN
    SIMPLE_ARITH_TAC;
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
    MATCH_MP_TAC READ_BYTES16_APPEND THEN ASM_REWRITE_TAC[APPEND] THEN
    REPEAT(MATCH_MP_TAC READ_BYTES16_CONS THEN CONJ_TAC THENL
            [READ16_TAC; ALL_TAC]) THEN
    REWRITE_TAC[READ_BYTES16_NIL]];;

(*** In the last group, derive that the buffer is exhausted if possible ***)

let RESOLVE_EXIT_TAC =
  FIRST_ASSUM(fun th ->
    if is_disj(concl th) && free_in `buflen:num` (concl th) then
      let a = lhand(concl th) in
      TRY(SUBGOAL_THEN a ASSUME_TAC THENL
           [MP_TAC th THEN SIMPLE_ARITH_TAC; ALL_TAC])
    else failwith "RESOLVE_EXIT_TAC");;

(*** In the last group, the part of the group's values within the limit ***)

let SUBLIST_EVAL_TAC =
  REWRITE_TAC[APPEND] THEN
  W(fun (asl,w) ->
    let t = find_term (can (term_match [] `SUB_LIST (0,c) (l:int16 list)`))
                      w in
    let c = rand(rand(rator t)) and l = rand t in
    (SUBGOAL_THEN (mk_eq(t,l)) SUBST1_TAC THENL
      [MATCH_MP_TAC SUB_LIST_REFL THEN REWRITE_TAC[LENGTH] THEN
       SIMPLE_ARITH_TAC;
       ALL_TAC]) ORELSE
    (SUBGOAL_THEN (mk_eq(c,`1`)) SUBST1_TAC THENL
      [SIMPLE_ARITH_TAC;
       REWRITE_TAC[SUB_LIST_1; LENGTH; LT_0; LT_REFL; EL; HD]]));;

(* ------------------------------------------------------------------------- *)
(* Correctness and memory safety, proved together since the memory accesses  *)
(* depend on the data as well. The number N of groups before the last one    *)
(* processed is the least such that the following group would go beyond the  *)
(* buffer or the coefficients from the group after N would reach 256.        *)
(* ------------------------------------------------------------------------- *)

(*** The invariant at the head of the loop, after i groups ***)

let rej_inv = `\i s.
  read X0 s = word(offset + LENGTH(REJ_SAMPLE(SUB_LIST(0,2 * i) inlist))) /\
  read X2 s = word_add buf (word(3 * i)) /\
  read X3 s = word buflen /\ read X8 s = r /\
  read X9 s = word_zx(word_sub (word 3) (word_zx buf:int32)) /\
  read X10 s = word 255 /\ read X11 s = word 3328 /\
  read(memory :> bytes(buf,buflen)) s = num_of_wordlist inlist /\
  read(memory :> bytes(word_add r (word(2 * offset)),
                       2 * LENGTH(REJ_SAMPLE(SUB_LIST(0,2 * i) inlist)))) s =
  num_of_wordlist(REJ_SAMPLE(SUB_LIST(0,2 * i) inlist)) /\
  (exists e_acc.
     read events s = APPEND e_acc e /\
     memaccess_inbounds e_acc [buf,buflen]
       [word_add r (word(2 * offset)),2 * (256 - offset)])`;;

let rej_inv_at n =
  mk_abs(`s:armstate`,
         mk_conj(`aligned_bytes_loaded s (word pc)
                    mlkem_native_rej_uniform_gcc12_O2_mc`,
                 rhs(concl(BETA_CONV(mk_comb(rhs(concl(BETA_CONV
                   (mk_comb(rej_inv,n)))),`s:armstate`))))));;

let MLKEM_NATIVE_REJ_UNIFORM_GCC12_O2_CORRECT_MEMSAFE = prove
 (`!r offset buf buflen (inlist:(12 word)list) pc e.
      offset <= 256 /\ 3 <= buflen /\ buflen <= 4096 /\
      8 * buflen = 12 * LENGTH inlist /\
      ALL (nonoverlapping (word_add r (word(2 * offset)),2 * (256 - offset)))
          [(word pc,0x9c); (buf,buflen)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  mlkem_native_rej_uniform_gcc12_O2_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [r; word offset; buf; word buflen] s /\
                wordlist_from_memory(buf,LENGTH inlist) s = inlist /\
                read events s = e)
           (\s. read PC s = word(pc + 0x98) /\
                (let inlist' = MAP (word_zx:12 word->16 word) inlist in
                 let outlist =
                   SUB_LIST (0,256 - offset)
                            (FILTER (\x. val x < 3329) inlist') in
                 let outlen = LENGTH outlist in
                 C_RETURN s = word(offset + outlen) /\
                 wordlist_from_memory(word_add r (word(2 * offset)),outlen) s =
                 outlist) /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   memaccess_inbounds e2 [buf,buflen]
                     [word_add r (word(2 * offset)),2 * (256 - offset)]))
           (MAYCHANGE [PC; X0; X1; X2; X4; X5; X6; X7; X8; X9; X10; X11] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(word_add r (word(2 * offset)),
                                       2 * (256 - offset))])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `offset:num`; `buf:int64`; `buflen:num`;
    `inlist:(12 word)list`; `pc:num`; `e:(uarch_event)list`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; NONOVERLAPPING_CLAUSES; ALL;
              SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The input and output in terms of bytes ***)

  MP_TAC(ISPECL
   [`buf:int64`; `LENGTH(inlist:(12 word)list)`;
    `buflen:num`; `inlist:(12 word)list`]
   (INST_TYPE [`:12`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  ASM_REWRITE_TAC[DIMINDEX_12] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM REJ_SAMPLE] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[GSYM REJ_SAMPLE] THEN
  ABBREV_TAC `outlist = SUB_LIST (0,256 - offset) (REJ_SAMPLE inlist)` THEN
  MP_TAC(ISPECL
   [`word_add r (word(2 * offset)):int64`; `LENGTH(outlist:int16 list)`;
    `2 * LENGTH(outlist:int16 list)`; `outlist:int16 list`]
   (INST_TYPE [`:16`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  REWRITE_TAC[DIMINDEX_16; ARITH_RULE `16 * l = 8 * 2 * l`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN

  (*** The case where there are already 256 coefficients ***)

  ASM_CASES_TAC `offset = 256` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `outlist:int16 list`)) THEN
    REWRITE_TAC[SUB_0; SUB_LIST_CLAUSES; LENGTH; MULT_CLAUSES;
                ADD_CLAUSES] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL;
                num_of_wordlist] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_REJ_UNIFORM_GCC12_O2_EXEC (1--3) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_REJ_UNIFORM_GCC12_O2_EXEC (4--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUB_LIST_CLAUSES; LENGTH; MULT_CLAUSES; ADD_CLAUSES;
                READ_BYTES_TRIVIAL; num_of_wordlist] THEN
    DISCHARGE_MEMSAFE_TAC;
    ALL_TAC] THEN

  (*** Define the number N of groups processed in the loop ***)

  SUBGOAL_THEN `offset < 256` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `?N. buflen < 3 * (N + 2) \/
        256 <= offset + LENGTH(REJ_SAMPLE(SUB_LIST(0,2 * (N + 1)) inlist))`
  MP_TAC THENL
   [EXISTS_TAC `buflen:num` THEN ARITH_TAC;
    GEN_REWRITE_TAC LAND_CONV [num_WOP]] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_LT; NOT_LE] THEN DISCH_TAC THEN

  (*** The initialization, up to the loop head ***)

  ENSURES_SEQUENCE_TAC `pc + 0x54` (rej_inv_at `0`) THEN CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_REJ_UNIFORM_GCC12_O2_EXEC (1--3) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_REJ_UNIFORM_GCC12_O2_EXEC (4--4) THEN
    DECIDE_BRANCH_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_REJ_UNIFORM_GCC12_O2_EXEC (5--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES; REJ_SAMPLE_EMPTY; LENGTH;
                ADD_CLAUSES; WORD_ADD_0; READ_COMPONENT_COMPOSE;
                READ_BYTES_TRIVIAL; num_of_wordlist] THEN
    REPEAT CONJ_TAC THEN (DISCHARGE_MEMSAFE_TAC ORELSE WORD_SMALL_TAC);
    ALL_TAC] THEN

  (*** The loop over the first N groups ***)

  ENSURES_SEQUENCE_TAC `pc + 0x54` (rej_inv_at `N:num`) THEN CONJ_TAC THENL
   [ASM_CASES_TAC `N = 0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ENSURES_INIT_TAC "s0" THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ENSURES_WHILE_UP_TAC `N:num` `pc + 0x54` `pc + 0x54` rej_inv THEN
    REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[]] THEN

    (*** The loop body, for group i < N, with four cases ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_ASSUM(fun th ->
      if is_forall(concl th) && free_in `N:num` (concl th)
      then STRIP_ASSUME_TAC(MP (SPEC `i:num` th) (ASSUME `i < N`))
      else failwith "") THEN
    SUBGOAL_THEN `2 * i + 2 <= LENGTH(inlist:(12 word)list)` ASSUME_TAC
    THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `SUB_LIST(0,2 * (i + 1)) inlist =
      APPEND (SUB_LIST(0,2 * i) inlist)
             [EL (2 * i) inlist:12 word; EL (2 * i + 1) inlist]`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
     [ASM_SIMP_TAC[ARITH_RULE `2 * (i + 1) = 2 * i + 2`; SUB_LIST_0_SNOC2];
      ALL_TAC] THEN
    REJ_GROUP_TAC `i:num` THEN
    (SUBGOAL_THEN `offset + LENGTH(L:int16 list) < 256` ASSUME_TAC THENL
      [ASM_ARITH_TAC; ALL_TAC]) THEN
    REJ_CASE_TAC `i:num` `word (pc + 84):int64` THEN REJ_CLOSE_TAC;
    ALL_TAC] THEN

  (*** The last group, number N, in twelve cases ***)

  SUBGOAL_THEN `?k. buflen = 3 * k /\ LENGTH(inlist:(12 word)list) = 2 * k`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `EVEN(LENGTH(inlist:(12 word)list))` MP_TAC THENL
     [SUBGOAL_THEN `3 * LENGTH(inlist:(12 word)list) = 2 * buflen` MP_TAC
      THENL [ASM_ARITH_TAC; DISCH_THEN(MP_TAC o AP_TERM `EVEN`)] THEN
      REWRITE_TAC[EVEN_MULT; ARITH];
      REWRITE_TAC[EVEN_EXISTS] THEN MATCH_MP_TAC MONO_EXISTS THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `3 * (N + 1) <= buflen /\
    offset + LENGTH(REJ_SAMPLE(SUB_LIST(0,2 * N) inlist)) < 256`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `N = 0` THENL
     [ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_LIST_CLAUSES;
                      REJ_SAMPLE_EMPTY; LENGTH] THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `N - 1`) THEN
      ASM_SIMP_TAC[ARITH_RULE
       `~(N = 0) ==> N - 1 < N /\ N - 1 + 1 = N /\ N - 1 + 2 = N + 1`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 * N + 2 <= LENGTH(inlist:(12 word)list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `buflen < 3 * (N + 2) ==> LENGTH(inlist:(12 word)list) <= 2 * (N + 1)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
     `3 * k < 3 * (N + 2) ==> k <= N + 1`)) THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The output list, depending only on the values up to group N ***)

  SUBGOAL_THEN
   `outlist =
    APPEND (REJ_SAMPLE(SUB_LIST(0,2 * N) inlist))
     (SUB_LIST(0,256 - offset - LENGTH(REJ_SAMPLE(SUB_LIST(0,2 * N) inlist)))
       (REJ_SAMPLE [EL (2 * N) inlist; EL (2 * N + 1) inlist]))`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      rhs(concl th) = `outlist:int16 list`)) THEN
    MP_TAC(ISPECL [`inlist:(12 word)list`; `2 * (N + 1)`; `256 - offset`]
      SUB_LIST_REJ_SAMPLE_PREFIX) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    SIMP_TAC[ARITH_RULE `2 * (N + 1) = 2 * N + 2`; SUB_LIST_0_SNOC2;
             ASSUME `2 * N + 2 <= LENGTH(inlist:(12 word)list)`] THEN
    REWRITE_TAC[REJ_SAMPLE_APPEND] THEN
    MATCH_MP_TAC SUB_LIST_APPEND_RIGHT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCARD_MATCHING_ASSUMPTIONS
   [`buflen = 3 * k`; `LENGTH(inlist:(12 word)list) = 2 * k`] THEN

  (*** The same setup as for the loop body, then cases on the count ***)

  SUBGOAL_THEN
   `SUB_LIST(0,2 * (N + 1)) inlist =
    APPEND (SUB_LIST(0,2 * N) inlist)
           [EL (2 * N) inlist:12 word; EL (2 * N + 1) inlist]`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [SIMP_TAC[ARITH_RULE `2 * (N + 1) = 2 * N + 2`; SUB_LIST_0_SNOC2;
             ASSUME `2 * N + 2 <= LENGTH(inlist:(12 word)list)`];
    ALL_TAC] THEN
  REJ_GROUP_TAC `N:num` THEN
  MP_TAC(MATCH_MP (ARITH_RULE
   `offset + LENGTH(L:int16 list) < 256
    ==> 255 <= offset + LENGTH L \/
        254 <= offset + LENGTH L /\ offset + LENGTH L < 255 \/
        offset + LENGTH L < 254`)
   (ASSUME `offset + LENGTH(L:int16 list) < 256`)) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
  RESOLVE_EXIT_TAC THEN SUBLIST_EVAL_TAC THEN
  REJ_CASE_TAC `N:num` `word (pc + 152):int64` THEN REJ_CLOSE_TAC);;

(* ------------------------------------------------------------------------- *)
(* The correctness and memory safety theorems separately, and the            *)
(* subroutine versions. The precise sets of registers changed are kept,      *)
(* since the callers rely on X3 being preserved.                             *)
(* ------------------------------------------------------------------------- *)

let ENSURES_WEAKEN_RULE = prove
 (`!step P P' Q Q' C:A->A->bool.
        ensures step P Q C
        ==> (!s. P' s ==> P s) /\ (!s. Q s ==> Q' s)
            ==> ensures step P' Q' C`,
  MESON_TAC[ENSURES_PREPOSTCONDITION_THM]);;

let MLKEM_NATIVE_REJ_UNIFORM_GCC12_O2_CORRECT = prove
 (`!r offset buf buflen (inlist:(12 word)list) pc.
      offset <= 256 /\ 3 <= buflen /\ buflen <= 4096 /\
      8 * buflen = 12 * LENGTH inlist /\
      ALL (nonoverlapping (word_add r (word(2 * offset)),2 * (256 - offset)))
          [(word pc,0x9c); (buf,buflen)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  mlkem_native_rej_uniform_gcc12_O2_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [r; word offset; buf; word buflen] s /\
                wordlist_from_memory(buf,LENGTH inlist) s = inlist)
           (\s. read PC s = word(pc + 0x98) /\
                let inlist' = MAP (word_zx:12 word->16 word) inlist in
                let outlist =
                  SUB_LIST (0,256 - offset)
                           (FILTER (\x. val x < 3329) inlist') in
                let outlen = LENGTH outlist in
                C_RETURN s = word(offset + outlen) /\
                wordlist_from_memory(word_add r (word(2 * offset)),outlen) s =
                outlist)
           (MAYCHANGE [PC; X0; X1; X2; X4; X5; X6; X7; X8; X9; X10; X11] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(word_add r (word(2 * offset)),
                                       2 * (256 - offset))])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  GHOST_INTRO_TAC `e:(uarch_event)list` `read events` THEN
  MP_TAC(SPECL [`r:int64`; `offset:num`; `buf:int64`; `buflen:num`;
                `inlist:(12 word)list`; `pc:num`; `e:(uarch_event)list`]
         MLKEM_NATIVE_REJ_UNIFORM_GCC12_O2_CORRECT_MEMSAFE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_WEAKEN_RULE) THEN
  SIMP_TAC[]);;

let MLKEM_NATIVE_REJ_UNIFORM_GCC12_O2_SUBROUTINE_CORRECT = prove
 (`!r offset buf buflen (inlist:(12 word)list) pc returnaddress.
      offset <= 256 /\ 3 <= buflen /\ buflen <= 4096 /\
      8 * buflen = 12 * LENGTH inlist /\
      ALL (nonoverlapping (word_add r (word(2 * offset)),2 * (256 - offset)))
          [(word pc,0x9c); (buf,buflen)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  mlkem_native_rej_uniform_gcc12_O2_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [r; word offset; buf; word buflen] s /\
                wordlist_from_memory(buf,LENGTH inlist) s = inlist)
           (\s. read PC s = returnaddress /\
                let inlist' = MAP (word_zx:12 word->16 word) inlist in
                let outlist =
                  SUB_LIST (0,256 - offset)
                           (FILTER (\x. val x < 3329) inlist') in
                let outlen = LENGTH outlist in
                C_RETURN s = word(offset + outlen) /\
                wordlist_from_memory(word_add r (word(2 * offset)),outlen) s =
                outlist)
           (MAYCHANGE [PC; X0; X1; X2; X4; X5; X6; X7; X8; X9; X10; X11] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(word_add r (word(2 * offset)),
                                       2 * (256 - offset))])`,
  let TWEAK_CONV =
    TOP_DEPTH_CONV let_CONV THENC
    REWRITE_CONV[wordlist_from_memory] in
  CONV_TAC TWEAK_CONV THEN
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_REJ_UNIFORM_GCC12_O2_EXEC
    (CONV_RULE TWEAK_CONV MLKEM_NATIVE_REJ_UNIFORM_GCC12_O2_CORRECT));;

let MLKEM_NATIVE_REJ_UNIFORM_GCC12_O2_MEMSAFE = prove
 (`!r offset buf buflen (inlist:(12 word)list) pc e.
      offset <= 256 /\ 3 <= buflen /\ buflen <= 4096 /\
      8 * buflen = 12 * LENGTH inlist /\
      ALL (nonoverlapping (word_add r (word(2 * offset)),2 * (256 - offset)))
          [(word pc,0x9c); (buf,buflen)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  mlkem_native_rej_uniform_gcc12_O2_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [r; word offset; buf; word buflen] s /\
                wordlist_from_memory(buf,LENGTH inlist) s = inlist /\
                read events s = e)
           (\s. read PC s = word(pc + 0x98) /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   memaccess_inbounds e2 [buf,buflen]
                     [word_add r (word(2 * offset)),2 * (256 - offset)]))
           (MAYCHANGE [PC; X0; X1; X2; X4; X5; X6; X7; X8; X9; X10; X11] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(word_add r (word(2 * offset)),
                                       2 * (256 - offset))])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`r:int64`; `offset:num`; `buf:int64`; `buflen:num`;
                `inlist:(12 word)list`; `pc:num`; `e:(uarch_event)list`]
         MLKEM_NATIVE_REJ_UNIFORM_GCC12_O2_CORRECT_MEMSAFE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_WEAKEN_RULE) THEN
  SIMP_TAC[]);;

let MLKEM_NATIVE_REJ_UNIFORM_GCC12_O2_SUBROUTINE_SAFE = prove
 (`!r offset buf buflen (inlist:(12 word)list) pc e returnaddress.
      offset <= 256 /\ 3 <= buflen /\ buflen <= 4096 /\
      8 * buflen = 12 * LENGTH inlist /\
      ALL (nonoverlapping (word_add r (word(2 * offset)),2 * (256 - offset)))
          [(word pc,0x9c); (buf,buflen)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  mlkem_native_rej_uniform_gcc12_O2_mc /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [r; word offset; buf; word buflen] s /\
                wordlist_from_memory(buf,LENGTH inlist) s = inlist /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                (exists e2.
                   read events s = APPEND e2 e /\
                   memaccess_inbounds e2 [buf,buflen]
                     [word_add r (word(2 * offset)),2 * (256 - offset)]))
           (MAYCHANGE [PC; X0; X1; X2; X4; X5; X6; X7; X8; X9; X10; X11] ,,
            MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(word_add r (word(2 * offset)),
                                       2 * (256 - offset))])`,
  let TWEAK_CONV = REWRITE_CONV[wordlist_from_memory] in
  CONV_TAC TWEAK_CONV THEN
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_REJ_UNIFORM_GCC12_O2_EXEC
    (CONV_RULE TWEAK_CONV MLKEM_NATIVE_REJ_UNIFORM_GCC12_O2_MEMSAFE) THEN
  DISCHARGE_MEMSAFE_TAC);;
