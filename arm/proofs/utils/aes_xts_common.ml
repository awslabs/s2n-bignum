(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* BOZO: Do I need all of base?*)
needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/aes_xts_encrypt_spec.ml";;
needs "arm/proofs/utils/aes_xts_decrypt_spec.ml";;

(**********************************************************************)
(**                      Common definitions                          **)

(* For defining the input and output buffers of arbitrary length len.
   byte_list_at is adapted from Amanda's code at
   https://github.com/amanda-zx/s2n-bignum/blob/ed25519/arm/sha512/utils.ml *)
let byte_list_at = define
  `byte_list_at (m : byte list) (m_p : int64) (len: int64) s =
    ! i. i < val len ==> read (memory :> bytes8(word_add m_p (word i))) s = EL i m`;;

(** Function for initializing key schedule *)
let set_key_schedule = new_definition
  `set_key_schedule (s:armstate) (key_ptr:int64) (k0:int128)
     (k1:int128) (k2:int128) (k3:int128) (k4:int128) (k5:int128)
     (k6:int128) (k7:int128) (k8:int128) (k9:int128) (ka:int128)
     (kb:int128) (kc:int128) (kd:int128) (ke:int128) : bool =
     (read(memory :> bytes128 key_ptr) s = k0 /\
      read(memory :> bytes128 (word_add key_ptr (word 16))) s = k1 /\
      read(memory :> bytes128 (word_add key_ptr (word 32))) s = k2 /\
      read(memory :> bytes128 (word_add key_ptr (word 48))) s = k3 /\
      read(memory :> bytes128 (word_add key_ptr (word 64))) s = k4 /\
      read(memory :> bytes128 (word_add key_ptr (word 80))) s = k5 /\
      read(memory :> bytes128 (word_add key_ptr (word 96))) s = k6 /\
      read(memory :> bytes128 (word_add key_ptr (word 112))) s = k7 /\
      read(memory :> bytes128 (word_add key_ptr (word 128))) s = k8 /\
      read(memory :> bytes128 (word_add key_ptr (word 144))) s = k9 /\
      read(memory :> bytes128 (word_add key_ptr (word 160))) s = ka /\
      read(memory :> bytes128 (word_add key_ptr (word 176))) s = kb /\
      read(memory :> bytes128 (word_add key_ptr (word 192))) s = kc /\
      read(memory :> bytes128 (word_add key_ptr (word 208))) s = kd /\
      read(memory :> bytes128 (word_add key_ptr (word 224))) s = ke /\
      read(memory :> bytes32 (word_add key_ptr (word 240))) s = word 14)`;;

(** Define length of rest of input in bytes after the loop *)
let acc_len = new_definition
`acc_len (i:int64) (len:int64) : num =
  if val i * 0x50 + 0x40 = val len then 0x50 * val i + 0x40
  else
    if val i * 0x50 + 0x30 = val len then 0x50 * val i + 0x30
    else
      if val i * 0x50 + 0x20 = val len then 0x50 * val i + 0x20
      else
        if val i * 0x50 + 0x10 = val len then 0x50 * val i + 0x10
        else 0x50 * val i`;;

(** Define length of rest of input in blocks after the loop *)
let acc_blocks = new_definition
`acc_blocks (i:int64) (len:int64) (last:bool) : num =
  if val i * 0x50 + 0x40 = val len then val i * 0x5 + 4
  else
    if val i * 0x50 + 0x30 = val len then val i * 0x5 + 3
    else
      if val i * 0x50 + 0x20 = val len then val i * 0x5 + 2
      else
        if val i * 0x50 + 0x10 = val len then val i * 0x5 + 1
        else val i * 0x5`;;

(* The cipher-stealing invariant is the block read at ctxt_p + curr_len - 16 where Cm is being replaced by Pm
   one byte at a time with a decreasing offset i from the beginning of the block.
   Differs from decrypt in that, there, it's curr_len.
   The following is copied from decrypt and will be instantiated with l1_curr_len (= curr_len-16) instead of curr_len *)
let cipher_stealing_inv = new_definition
`cipher_stealing_inv (i:num) (curr_len:num) (tail_len:num) (PP:int128) (ct:byte list): int128 =
  bytes_to_int128(
    APPEND (SUB_LIST (0, i) (int128_to_bytes PP))
      (APPEND (SUB_LIST (i, tail_len - i) (SUB_LIST (curr_len + 16, tail_len) ct))
              (SUB_LIST (tail_len, 16 - tail_len) (int128_to_bytes PP))))`;;


(**********************************************************************)
(**                      Common List Lemmas                          **)

let SUB_LIST_SUCSPLIT = prove(
  `!(l:A list) n p. SUB_LIST(p,SUC n) l = APPEND (SUB_LIST(p,1) l) (SUB_LIST(p+1,n) l)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [ARITH_RULE `SUC n = 1 + n`] THEN
  REWRITE_TAC [SUB_LIST_SPLIT]
);;

let HD_SUB_LIST_CONS = prove
 (`!(h:A) (t:A list) n. 0 < n ==> HD (SUB_LIST (0,n) (CONS h t)) = h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `n:num` num_CASES) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; HD]);;

let HD_SUB_LIST_CONS_GENERAL = prove(
  `!p n (l:A list). p < LENGTH l /\ 0 < n ==> HD (SUB_LIST (p,n) l) = EL p l`,
  INDUCT_TAC THENL
  [
    GEN_TAC THEN
    LIST_INDUCT_TAC THENL
    [
      REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      REPEAT STRIP_TAC THEN
      REWRITE_TAC[EL; HD] THEN
      MP_TAC (SPECL [`h:A`; `t:A list`; `n:num`] HD_SUB_LIST_CONS) THEN
      ASM_SIMP_TAC[]
    ]; ALL_TAC
  ] THEN
  GEN_TAC THEN
  LIST_INDUCT_TAC THENL
  [
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[SUB_LIST_CLAUSES] THEN
    REWRITE_TAC[EL; TL] THEN
    FIRST_X_ASSUM (fun th -> MATCH_MP_TAC (SPECL [`n:num`; `t:A list`] th)) THEN
    ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `SUC p < LENGTH (CONS h (t:A list))` THEN
    REWRITE_TAC[LENGTH] THEN
    ARITH_TAC
  ]
);;

let TL_SUB_LIST_CONS = prove
(`!(h:A) (t:A list) n. 0 < n ==> TL (SUB_LIST (0,n) (CONS h t)) = SUB_LIST (0, n - 1) t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `n:num` num_CASES) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < n ==> ~(n = 0)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; TL] THEN
  REWRITE_TAC[ARITH_RULE `SUC m - 1 = m`]);;

let TL_SUB_LIST_CONS_GENERAL = prove(
  `!p n (l:A list). p < LENGTH l ==> 0 < n
    ==> TL (SUB_LIST (p, n) l) = SUB_LIST (p + 1, n - 1) l`,
  INDUCT_TAC THENL
  [
    GEN_TAC THEN
    LIST_INDUCT_TAC THENL
    [
      REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      CONV_TAC NUM_REDUCE_CONV THEN
      REPEAT STRIP_TAC THEN
      MP_TAC (SPECL [`h:A`; `t:A list`; `n:num`] TL_SUB_LIST_CONS) THEN
      ASM_SIMP_TAC[num_CONV `1`; SUB_LIST_CLAUSES]
    ]; ALL_TAC
  ] THEN
  GEN_TAC THEN
  LIST_INDUCT_TAC THENL
  [
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[ARITH_RULE `SUC p + 1 = SUC (p + 1)`] THEN
    REWRITE_TAC[SUB_LIST_CLAUSES] THEN
    FIRST_X_ASSUM (fun th -> MP_TAC (SPECL [`n:num`; `t:A list`] th)) THEN
    SUBGOAL_THEN `p < LENGTH (t:A list)` ASSUME_TAC THENL
    [ UNDISCH_TAC `SUC p < LENGTH (CONS h (t:A list))` THEN
      REWRITE_TAC[LENGTH] THEN ARITH_TAC
      ; ALL_TAC] THEN
    ASM_SIMP_TAC[]
  ]
);;

let EL_SUB_LIST_TRIVIAL = prove(
  `!i n (l:A list). i < LENGTH l /\ 0 < n ==> EL 0x0 (SUB_LIST (i, n) l) = EL i l`,
  REWRITE_TAC[EL] THEN
  SIMP_TAC[HD_SUB_LIST_CONS_GENERAL]
);;

let EL_SUB_LIST = prove(
  `!(i:num) n (l:A list). i < n /\ n <= LENGTH l ==>
    EL i (SUB_LIST (0, n) l) = EL i l`,
  INDUCT_TAC THENL
  [ (* i = 0 *)
    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    LIST_INDUCT_TAC THENL
    [
      REPEAT STRIP_TAC THEN
      IMP_REWRITE_TAC[SUB_LIST_TRIVIAL] THEN
      REWRITE_TAC[LENGTH] THEN
      ARITH_TAC; ALL_TAC
    ] THEN
    REPEAT STRIP_TAC THEN
    IMP_REWRITE_TAC[EL; HD; HD_SUB_LIST_CONS];
    ALL_TAC
  ] THEN
  (* i != 0 *)
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THENL
  [
    REPEAT STRIP_TAC THEN
    IMP_REWRITE_TAC[SUB_LIST_TRIVIAL] THEN
    REWRITE_TAC[LENGTH] THEN
    ARITH_TAC; ALL_TAC
  ] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EL; TL] THEN
  IMP_REWRITE_TAC[TL_SUB_LIST_CONS] THEN
  REPEAT CONJ_TAC THENL
  [ ASM_SIMP_TAC[ARITH_RULE `SUC i < n ==> i < n - 1`];
    SUBGOAL_THEN `LENGTH (CONS h (t:A list)) = SUC (LENGTH t)` ASSUME_TAC THENL
    [ REWRITE_TAC[LENGTH]; ALL_TAC ] THEN
    ASM_ARITH_TAC;
    MP_TAC (ARITH_RULE `SUC i < n ==> 0 < n`) THEN
    ASM_SIMP_TAC[]
  ]
);;

let EL_SUB_LIST_GENERAL = prove(
  `!p (l:A list) i n. i >= p /\ i < p + n /\ p + n <= LENGTH l ==>
    EL (i - p) (SUB_LIST (p, n) l) = EL i l`,
  INDUCT_TAC THENL
  [ IMP_REWRITE_TAC[ADD; SUB_0; EL_SUB_LIST];
    ALL_TAC
  ] THEN
  LIST_INDUCT_TAC THENL
  [ REWRITE_TAC[SUB_LIST_CLAUSES; LENGTH] THEN
    REPEAT STRIP_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN
  REWRITE_TAC[LENGTH] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SUB_LIST_CLAUSES] THEN
  SUBGOAL_THEN `EL i (CONS h (t:A list)) = EL (i - 1) t` SUBST1_TAC THENL
  [ SUBGOAL_THEN `i = SUC (i - 1)` SUBST1_TAC THENL
    [ ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EL; TL] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `i - SUC p = i - 1 - p`] THEN
  FIRST_X_ASSUM (fun th -> MP_TAC (SPECL [`t:A list`; `(i - 1):num`; `n:num`] th)) THEN
  ANTS_TAC THENL [ ASM_ARITH_TAC; ALL_TAC ] THEN
  SIMP_TAC[]
);;

let EL_SUB_LIST_SHIFT = prove(
  `!(i:num) p (l:A list) n. 0 < i /\ i < n /\ n <= LENGTH l - p ==>
    EL (i - 1) (SUB_LIST (p + 1, n - 1) l) = EL i (SUB_LIST (p, n) l)`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `EL i (SUB_LIST (p, n) (l:A list)) = EL (SUC (i - 1)) (SUB_LIST (p, SUC (n - 1)) l)` SUBST1_TAC THENL
    [ IMP_REWRITE_TAC[ARITH_RULE `0 < i ==> SUC (i - 1) = i`] THEN
      ASM_ARITH_TAC; ALL_TAC ] THEN
    DISJ_CASES_TAC (ISPEC `l:(A)list` list_CASES) THENL [
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      UNDISCH_TAC `n <= LENGTH ([]:A list) - p` THEN
      REWRITE_TAC[LENGTH] THEN
      ASM_ARITH_TAC; ALL_TAC
    ] THEN

    REPEAT_N 2 (FIRST_X_ASSUM CHOOSE_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[EL; TL] THEN
    IMP_REWRITE_TAC[TL_SUB_LIST_CONS_GENERAL] THEN
    IMP_REWRITE_TAC[ARITH_RULE `0 < n ==> SUC (n - 1) = n`] THEN
    ASM_ARITH_TAC
  );;


let SUB_LIST_APPEND_RIGHT_LEMMA = prove(
  `!(x:A list) y n m. LENGTH x = n ==> SUB_LIST (n,m) (APPEND x y) = SUB_LIST (0,m) y`,
  LIST_INDUCT_TAC THENL
  [ REPEAT GEN_TAC THEN
    SIMP_TAC[CONJUNCT1 LENGTH; APPEND; SUB_LIST_CLAUSES];

    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    INDUCT_TAC THENL[
      SIMP_TAC[LENGTH_EQ_NIL] THEN REWRITE_TAC[APPEND];
      ASM_SIMP_TAC[APPEND; LENGTH; SUB_LIST_CLAUSES; SUC_INJ]]]);;

let SUB_LIST_APPEND_RIGHT_GENERAL = prove(
  `!(x:A list) y n m p. LENGTH x = p ==> n >= p ==>
    SUB_LIST (n,m) (APPEND x y) = SUB_LIST (n - p,m) y`,
  LIST_INDUCT_TAC THENL
  [
    REPEAT GEN_TAC THEN
    SIMP_TAC[CONJUNCT1 LENGTH; APPEND; SUB_LIST_CLAUSES] THEN
    DISCH_THEN (fun th -> REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[SUB_0];

    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    INDUCT_TAC THENL
    [
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `p = 0` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      SUBGOAL_THEN `CONS h t = ([]:A list)` ASSUME_TAC THENL
      [ UNDISCH_TAC `LENGTH (CONS h (t:A list)) = 0` THEN
        SIMP_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[APPEND];

      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `p > 0` ASSUME_TAC THENL
      [ UNDISCH_TAC `LENGTH (CONS h (t:A list)) = p` THEN
        ASM_REWRITE_TAC[LENGTH] THEN
        MP_TAC (SPEC `LENGTH (t:A list)` (ARITH_RULE `!x. SUC x > 0`)) THEN
        ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `LENGTH (t:A list) = p - 1` ASSUME_TAC THENL
      [ UNDISCH_TAC `LENGTH (CONS h (t:A list)) = p` THEN
        ASM_REWRITE_TAC[LENGTH] THEN
        MP_TAC (SPECL [`LENGTH (t:A list)`; `p:num`] (ARITH_RULE `!n m. SUC n = m ==> n = m - 1`)) THEN
        SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `n >= p - 1` ASSUME_TAC THENL
      [ MP_TAC (ARITH_RULE `SUC n >= p /\ p > 0 ==> n >= p - 1`) THEN
        ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `SUC n - p = n - (p - 1)` ASSUME_TAC THENL
      [ MP_TAC (ARITH_RULE `SUC n >= p /\ p > 0 ==> SUC n - p = n - (p - 1)`) THEN
        ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[APPEND; LENGTH; SUB_LIST_CLAUSES; SUC_INJ] THEN
      FIRST_X_ASSUM (fun th -> MP_TAC (SPECL [`y:A list`; `n:num`; `m:num`; `(p-1):num`] th)) THEN
      ASM_SIMP_TAC[]
    ]
  ]
);;

let SUB_LIST_LENGTH_IMPLIES = prove(
  `!(l:A list) n. LENGTH l = n ==> SUB_LIST(0,n) l = l`,
   REPEAT STRIP_TAC THEN
   UNDISCH_THEN `LENGTH (l:A list) = n` (fun th -> REWRITE_TAC[GSYM th]) THEN
   REWRITE_TAC[SUB_LIST_LENGTH]
);;

let SUB_LIST_IDEMPOTENT_P = prove(
  `!p n (l:(A)list). SUB_LIST (0,n) (SUB_LIST (p,n) l) = SUB_LIST (p,n) l`,
  INDUCT_TAC THENL[
    REWRITE_TAC[SUB_LIST_IDEMPOTENT];

    REPEAT STRIP_TAC THEN
    DISJ_CASES_TAC (ISPEC `l:(A)list` list_CASES) THENL [
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUB_LIST_CLAUSES];
      ALL_TAC
    ] THEN
    FIRST_X_ASSUM MP_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUB_LIST_CLAUSES] THEN
    ASM_REWRITE_TAC[]
  ]);;

let SUB_LIST_MIN_RIGHT = prove(
  `!p (l:(A)list) (n:num) m. SUB_LIST (0,n) (SUB_LIST (p,m) l) = SUB_LIST (p, MIN n m) l`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(m:num) <= n` THENL [
    FIRST_X_ASSUM MP_TAC THEN REWRITE_TAC[LE_EXISTS] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUB_LIST_SPLIT;ADD_CLAUSES;ARITH_RULE`MIN ((x:num)+y) x = x`] THEN
    REWRITE_TAC[SUB_LIST_IDEMPOTENT_P] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM APPEND_NIL] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC SUB_LIST_TRIVIAL THEN
    REWRITE_TAC[LENGTH_SUB_LIST] THEN ARITH_TAC; ALL_TAC] THEN

  IMP_REWRITE_TAC[ARITH_RULE `~(m <= n) ==> MIN n m = n`] THEN
  FIRST_X_ASSUM MP_TAC THEN REWRITE_TAC[NOT_LE;LT_EXISTS] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUB_LIST_SPLIT;ADD_CLAUSES;ARITH_RULE`MIN (x:num) (x+y) = x`] THEN

  MP_TAC (ISPECL [`l:A list`; `p:num`; `n:num`] LENGTH_SUB_LIST) THEN
  ASM_CASES_TAC `n <= LENGTH (l:A list) - p` THENL [
    IMP_REWRITE_TAC[ARITH_RULE `!n m. n <= m ==> MIN n m = n`] THEN
    DISCH_TAC THEN
    IMP_REWRITE_TAC[SUB_LIST_APPEND_LEFT] THEN
    IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES] THEN
    ARITH_TAC; ALL_TAC
  ] THEN

  IMP_REWRITE_TAC[ARITH_RULE `!n m. ~(n <= m) ==> MIN n m = m`] THEN
  SUBGOAL_THEN `SUB_LIST (p + n,SUC d) (l:A list) = []` SUBST1_TAC THENL
  [ MATCH_MP_TAC SUB_LIST_TRIVIAL THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[APPEND_NIL] THEN
  REWRITE_TAC[SUB_LIST_IDEMPOTENT_P]
);;

let SUB_LIST_MIN_LEFT = prove(
  `!q (l:A list) n m.
    SUB_LIST (q,n) (SUB_LIST (0,m) l) = SUB_LIST (q, MIN n (m - q)) l`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `n <= m - q` THENL [
    IMP_REWRITE_TAC[ARITH_RULE `x <= y ==> MIN x y = x`] THEN
    UNDISCH_TAC `n <= m - q` THEN
    MAP_EVERY SPEC1_TAC [`n:num`; `l:A list`; `q:num`; `m:num`] THEN
    (* Induct over m *)
    INDUCT_TAC THENL
    [
      REPEAT STRIP_TAC THEN
      IMP_REWRITE_TAC[ARITH_RULE `n <= 0 - q ==> n = 0`] THEN
      REWRITE_TAC[SUB_LIST_CLAUSES];

      INDUCT_TAC THENL
      [
        REWRITE_TAC[SUB_0] THEN
        REPEAT STRIP_TAC THEN
        MP_TAC (SPECL [`0:num`; `l:A list`; `n:num`; `SUC m:num`] SUB_LIST_MIN_RIGHT) THEN
        IMP_REWRITE_TAC[ARITH_RULE `x <= y ==> MIN x y = x`];

        LIST_INDUCT_TAC THENL[
          REWRITE_TAC[SUB_LIST_CLAUSES];
          REWRITE_TAC[SUB_LIST_CLAUSES] THEN
          REPEAT STRIP_TAC THEN
          FIRST_X_ASSUM
            (fun th -> MP_TAC
              (SPECL [`q:num`; `t:A list`; `n:num`] th)) THEN
          ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
          SIMP_TAC[]
        ]
      ]
    ]; ALL_TAC
  ] THEN

  (* Case n > m - q*)
  IMP_REWRITE_TAC[ARITH_RULE `~(x <= y) ==> MIN x y = y`] THEN
  UNDISCH_TAC `~(n <= m - q)` THEN
  MAP_EVERY SPEC1_TAC [`n:num`; `l:A list`; `q:num`; `m:num`] THEN
  INDUCT_TAC THENL
  [
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[ARITH_RULE `0 - q = 0`] THEN
    REWRITE_TAC[SUB_LIST_CLAUSES];

    INDUCT_TAC THENL
    [
      REWRITE_TAC[SUB_0] THEN
      REPEAT STRIP_TAC THEN
      MP_TAC (SPECL [`0:num`; `l:A list`; `n:num`; `SUC m:num`] SUB_LIST_MIN_RIGHT) THEN
      IMP_REWRITE_TAC[ARITH_RULE `~(x <= y) ==> MIN x y = y`];

      LIST_INDUCT_TAC THENL[
        REWRITE_TAC[SUB_LIST_CLAUSES];
        REWRITE_TAC[SUB_LIST_CLAUSES] THEN
        REPEAT STRIP_TAC THEN
        REWRITE_TAC[ARITH_RULE `SUC m - SUC q = m - q`] THEN
        FIRST_X_ASSUM
            (fun th -> MP_TAC
              (SPECL [`q:num`; `t:A list`; `n:num`] th)) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        SIMP_TAC[]
      ]
    ]
  ]
);;

let SUB_LIST_MIN_GENERAL = prove(
  `!p q (l:(A)list) (n:num) m.
    SUB_LIST (q,n) (SUB_LIST (p,m) l) = SUB_LIST (p + q, MIN n (m - q)) l`,
  REPEAT STRIP_TAC THEN
  (* Case n <= m - q *)
  ASM_CASES_TAC `n <= m - q` THENL [
    IMP_REWRITE_TAC[ARITH_RULE `x <= y ==> MIN x y = x`] THEN
    (* Induct over p *)
    UNDISCH_TAC `n <= m - q` THEN
    MAP_EVERY SPEC1_TAC [`m:num`; `n:num`; `l:A list`; `q:num`; `p:num`] THEN
    INDUCT_TAC THENL
    [
      REWRITE_TAC[ADD] THEN
      REPEAT STRIP_TAC THEN
      MP_TAC (SPECL [`q:num`; `l:A list`; `n:num`; `m:num`] SUB_LIST_MIN_LEFT) THEN
      IMP_REWRITE_TAC[ARITH_RULE `x <= y ==> MIN x y = x`];
      ALL_TAC
    ] THEN

    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    LIST_INDUCT_TAC THENL[
      REWRITE_TAC[SUB_LIST_CLAUSES];
      REWRITE_TAC[ARITH_RULE `SUC p + q = SUC (p + q)`] THEN
      REWRITE_TAC[SUB_LIST_CLAUSES] THEN
      ASM_REWRITE_TAC[]
    ]; ALL_TAC
  ] THEN

  (* Case n > m - q*)
  IMP_REWRITE_TAC[ARITH_RULE `~(x <= y) ==> MIN x y = y`] THEN
  UNDISCH_TAC `~(n <= m - q)` THEN
  MAP_EVERY SPEC1_TAC [`m:num`; `n:num`; `l:A list`; `q:num`; `p:num`] THEN
  INDUCT_TAC THENL
  [
    REWRITE_TAC[ADD] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (SPECL [`q:num`; `l:A list`; `n:num`; `m:num`] SUB_LIST_MIN_LEFT) THEN
    IMP_REWRITE_TAC[ARITH_RULE `~(x <= y) ==> MIN x y = y`];
    ALL_TAC
  ] THEN

  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THENL[
    REWRITE_TAC[SUB_LIST_CLAUSES];
    REWRITE_TAC[ARITH_RULE `SUC p + q = SUC (p + q)`] THEN
    REWRITE_TAC[SUB_LIST_CLAUSES] THEN
    ASM_REWRITE_TAC[]
  ]
);;

let NUM_OF_BYTELIST_APPEND = prove
 (`!l1 l2. num_of_bytelist (APPEND l1 l2) =
           num_of_bytelist l1 + 2 EXP (8 * LENGTH l1) * num_of_bytelist l2`,
   LIST_INDUCT_TAC THENL
   [ REWRITE_TAC[APPEND; LENGTH; num_of_bytelist; MULT_CLAUSES; EXP; ADD_CLAUSES];
     REWRITE_TAC[APPEND; LENGTH; num_of_bytelist] THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[MULT_SUC; EXP_ADD] THEN
     REWRITE_TAC[MULT_ASSOC; LEFT_ADD_DISTRIB] THEN
     ARITH_TAC]);;

let NUM_OF_BYTELIST_OF_SUB_LIST = prove(
  `!sz len (x:byte list).
   sz <= LENGTH x ==>
   num_of_bytelist (SUB_LIST (0, sz + len) x) =
   num_of_bytelist (SUB_LIST (0, sz) x) +
   2 EXP (8 * sz) * num_of_bytelist (SUB_LIST (sz, len) x)`,
  REPEAT STRIP_TAC THEN
  SUBST1_TAC(ISPECL [`x:byte list`; `sz:num`; `len:num`; `0:num`] SUB_LIST_SPLIT) THEN
  REWRITE_TAC[NUM_OF_BYTELIST_APPEND] THEN
  ASM_SIMP_TAC[LENGTH_SUB_LIST; SUB_0; MIN; ARITH_RULE `0 + sz = sz`]
);;


(**********************************************************************)
(**                      Common Lemmas                               **)

let MEMORY_BYTES_BOUND = prove
  (`read (memory :> bytes (x,16)) s < 2 EXP dimindex (:128)`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; DIMINDEX_128] THEN
  SUBST1_TAC(ARITH_RULE `128 = 8 * 16`) THEN REWRITE_TAC[READ_BYTES_BOUND]
  );;

(* Copied from bignum_copy_row_from_table_8n.ml *)
let READ_MEMORY_BYTES_BYTES128 = prove(`!z s.
    read (memory :> bytes (z,16)) s = val (read (memory :> bytes128 z) s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
  REWRITE_TAC[VAL_WORD_JOIN;DIMINDEX_64;DIMINDEX_128] THEN
  IMP_REWRITE_TAC[MOD_LT] THEN
  REWRITE_TAC[ARITH_RULE`2 EXP 128 = 2 EXP 64 * 2 EXP 64`] THEN
  IMP_REWRITE_TAC[LT_MULT_ADD_MULT] THEN
  REWRITE_TAC[VAL_BOUND_64;ARITH_RULE`0<2 EXP 64`;LE_REFL] THEN
  REWRITE_TAC[ARITH_RULE`16 = 8*(1+1)`;GSYM BIGNUM_FROM_MEMORY_BYTES;BIGNUM_FROM_MEMORY_STEP;BIGNUM_FROM_MEMORY_SING] THEN
  REWRITE_TAC[ARITH_RULE`8*1=8`;ARITH_RULE`64*1=64`] THEN ARITH_TAC);;


let WORD_AND_MASK16 = prove(
  `word_and (len:int64) (word 0xfffffffffffffff0) = word_sub len (word_and len (word 0xf))`,
  BITBLAST_TAC
);;

let WORD_AND_MASK16_EQ_0 = prove(
  `!(x:int64). val x < 16 ==> ~(val x = 0x0) ==> ~(val (word_and x (word 0xf)) = 0x0)`,
  BITBLAST_TAC);;

let word_split_lemma = prove(
  `!len:int64. word_add (word_and len (word 0xf))
      (word_and len (word 0xfffffffffffffff0)) = len`,
  BITBLAST_TAC);;

let BYTE_LIST_AT_ADD_ASSUM_TAC new_pos bound =
  let rule = subst [new_pos, `new_pos:num`; bound, `bound:num`]
    `(pos:num) + bound <= LENGTH (bl:byte list) ==> new_pos < LENGTH bl` in
  let p = subst [new_pos, `new_pos:num`] `new_pos:num` in
  MP_TAC (ARITH_RULE rule) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN (LABEL_TAC "tmp") THEN
  FIRST_ASSUM(fun th -> MP_TAC(SPEC p th)) THEN
  USE_THEN "tmp" (fun th -> REWRITE_TAC[th]) THEN
  POP_ASSUM (K ALL_TAC);;

let BYTES128_TO_BYTES8_THM = prove(
  `!pos bl_ptr s.
    read (memory :> bytes128 (word_add bl_ptr (word pos))) s =
    bytes_to_int128
      [read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x0)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x1)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x2)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x3)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x4)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x5)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x6)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x7)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x8)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0x9)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xa)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xb)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xc)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xd)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xe)))) s;
       read (memory :> bytes8 (word_add bl_ptr (word (pos + 0xf)))) s]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bytes_to_int128] THEN
  REWRITE_TAC EL_16_8_CLAUSES THEN
  GEN_REWRITE_TAC TOP_DEPTH_CONV [READ_MEMORY_BYTESIZED_SPLIT; WORD_ADD_ASSOC_CONSTS] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  ONCE_REWRITE_TAC [ARITH_RULE `pos + 0 = (pos:num)`] THEN
  REFL_TAC
);;

let SUB_LIST_16_TAC n exp =
  let subgoal = subst [exp, `exp:num`] `exp < LENGTH (l:A list)` in
  CONV_TAC(RAND_CONV (REWRITE_CONV[num_CONV n; SUB_LIST_SUCSPLIT])) THEN
  SUBGOAL_THEN subgoal ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUB_LIST_1] THEN ASM_SIMP_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC;;

let SUB_LIST_16 = prove(
  `!(l:A list) n. n + 16 <= LENGTH l ==>
    [ EL (n + 0) l; EL (n + 1) l; EL (n + 2) l; EL (n + 3) l;
      EL (n + 4) l; EL (n + 5) l; EL (n + 6) l; EL (n + 7) l;
      EL (n + 8) l; EL (n + 9) l; EL (n + 10) l; EL (n + 11) l;
      EL (n + 12) l; EL (n + 13) l; EL (n + 14) l; EL (n + 15) l
    ] = SUB_LIST (n,16) l`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY (fun i ->
    if i == 0
    then SUB_LIST_16_TAC `0x10` `n:num`
    else SUB_LIST_16_TAC (mk_numeral (num (16 - i)))
    (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("n", `:num`))
      (mk_numeral (num i)))) (0--14) THEN
  SUBGOAL_THEN `n + 15 < LENGTH (l:A list)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[APPEND; ARITH_RULE `n + 0 = n`]
);;

let BYTE_LIST_AT_5BLOCKS = prove(
  `! pos bl bl_ptr len s.
    byte_list_at bl bl_ptr len s
    ==> LENGTH bl = val len
    ==> pos + 0x50 <= LENGTH bl
    ==> (read (memory :> bytes128 (word_add bl_ptr (word pos))) s =
         bytes_to_int128 (SUB_LIST (pos, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x10))) s =
         bytes_to_int128 (SUB_LIST (pos + 0x10, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x20))) s =
         bytes_to_int128 (SUB_LIST (pos + 0x20, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x30))) s =
         bytes_to_int128 (SUB_LIST (pos + 0x30, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x40))) s =
         bytes_to_int128 (SUB_LIST (pos + 0x40, 0x10) bl))`,
  REWRITE_TAC[byte_list_at] THEN
  REPEAT STRIP_TAC THENL
  [ (* Subgoal1 *)
     MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x50`) (0--15) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `pos:num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    (* Subgoal2 *)
    MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x50`) (16--31) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `(pos+0x10):num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    (* Subgoal3 *)
    MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x50`) (32--47) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `(pos+0x20):num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    (* Subgoal4 *)
    MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x50`) (48--63) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `(pos+0x30):num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    (* Subgoal 5 *)
    MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x50`) (64--79) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `(pos+0x40):num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC
  ]
);;

let BYTE_LIST_AT_4BLOCKS = prove(
  `! pos bl bl_ptr len s.
    byte_list_at bl bl_ptr len s
    ==> LENGTH bl = val len
    ==> pos + 0x40 <= LENGTH bl
    ==> (read (memory :> bytes128 (word_add bl_ptr (word pos))) s =
         bytes_to_int128 (SUB_LIST (pos, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x10))) s =
         bytes_to_int128 (SUB_LIST (pos + 0x10, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x20))) s =
         bytes_to_int128 (SUB_LIST (pos + 0x20, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x30))) s =
         bytes_to_int128 (SUB_LIST (pos + 0x30, 0x10) bl))`,
  REWRITE_TAC[byte_list_at] THEN
  REPEAT STRIP_TAC THENL
  [ (* Subgoal1 *)
    MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x40`) (0--15) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `pos:num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    (* Subgoal2 *)
    MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x40`) (16--31) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `(pos+0x10):num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    (* Subgoal3 *)
    MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x40`) (32--47) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `(pos+0x20):num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    (* Subgoal4 *)
    MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x40`) (48--63) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `(pos+0x30):num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC
  ]
);;

let BYTE_LIST_AT_3BLOCKS = prove(
  `! pos bl bl_ptr len s.
    byte_list_at bl bl_ptr len s
    ==> LENGTH bl = val len
    ==> pos + 0x30 <= LENGTH bl
    ==> (read (memory :> bytes128 (word_add bl_ptr (word pos))) s =
         bytes_to_int128 (SUB_LIST (pos, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x10))) s =
         bytes_to_int128 (SUB_LIST (pos + 0x10, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x20))) s =
         bytes_to_int128 (SUB_LIST (pos + 0x20, 0x10) bl))`,
  REWRITE_TAC[byte_list_at] THEN
  REPEAT STRIP_TAC THENL
  [ (* Subgoal1 *)
    MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x30`) (0--15) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `pos:num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    (* Subgoal2 *)
    MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x30`) (16--31) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `(pos+0x10):num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    (* Subgoal3 *)
    MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x30`) (32--47) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `(pos+0x20):num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC
  ]
);;

let BYTE_LIST_AT_2BLOCKS = prove(
  `! pos bl bl_ptr len s.
    byte_list_at bl bl_ptr len s
    ==> LENGTH bl = val len
    ==> pos + 0x20 <= LENGTH bl
    ==> (read (memory :> bytes128 (word_add bl_ptr (word pos))) s =
         bytes_to_int128 (SUB_LIST (pos, 0x10) bl) /\
         read (memory :> bytes128 (word_add (word_add bl_ptr (word pos)) (word 0x10))) s =
         bytes_to_int128 (SUB_LIST (pos + 0x10, 0x10) bl))`,
  REWRITE_TAC[byte_list_at] THEN
  REPEAT STRIP_TAC THENL
  [ (* Subgoal1 *)
    MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x20`) (0--15) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `pos:num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    (* Subgoal2 *)
    MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x20`) (16--31) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `(pos+0x10):num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC
  ]
);;

let BYTE_LIST_AT_1BLOCKS = prove(
  `! pos bl bl_ptr len s.
    byte_list_at bl bl_ptr len s
    ==> LENGTH bl = val len
    ==> pos + 0x10 <= LENGTH bl
    ==> read (memory :> bytes128 (word_add bl_ptr (word pos))) s =
        bytes_to_int128 (SUB_LIST (pos, 0x10) bl)`,
  REWRITE_TAC[byte_list_at] THEN
  REPEAT STRIP_TAC THENL
  [ (* Subgoal1 *)
    MAP_EVERY (fun i -> BYTE_LIST_AT_ADD_ASSUM_TAC
      (mk_binop (mk_const("+", [`:num`, `:A`])) (mk_var("pos", `:num`))
        (mk_numeral (num i))) `0x10`) (0--15) THEN
    REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[BYTES128_TO_BYTES8_THM; GSYM ADD_ASSOC] THEN
    NUM_REDUCE_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC (ISPECL [`bl:byte list`; `pos:num`] SUB_LIST_16) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN NUM_REDUCE_TAC THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC
  ]
);;

let READ_BL_LEMMA = prove(
  `!ptr i (len:int64) (bl:byte list) s.
    (forall j. j < val len ==> read (memory :> bytes8 (word_add ptr (word j))) s = EL j bl)
    /\ i * 0x50 + 0x50 <= val len
    /\ LENGTH bl = val len
    ==>
    read (memory :> bytes128 (word_add ptr (word_mul (word 0x50) (word i)))) s =
      bytes_to_int128 (SUB_LIST (i * 80, 16) bl) /\
    read (memory :> bytes128 (word_add (word_add ptr (word_mul (word 0x50) (word i))) (word 0x10))) s =
      bytes_to_int128 (SUB_LIST (i * 80 + 16, 16) bl) /\
    read (memory :> bytes128 (word_add (word_add ptr (word_mul (word 0x50) (word i))) (word 0x20))) s =
      bytes_to_int128 (SUB_LIST (i * 80 + 32, 16) bl) /\
    read (memory :> bytes128 (word_add (word_add ptr (word_mul (word 0x50) (word i))) (word 0x30))) s =
      bytes_to_int128 (SUB_LIST (i * 80 + 48, 16) bl) /\
    read (memory :> bytes128 (word_add (word_add ptr (word_mul (word 0x50) (word i))) (word 0x40))) s =
      bytes_to_int128 (SUB_LIST (i * 80 + 64, 16) bl)
    `,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC [WORD_RULE `word_mul (word 0x50) (word i) = word (i * 80)`] THEN
  MP_TAC
    (SPECL [`(i * 80):num`; `bl:byte list`; `ptr:int64`; `len:int64`; `s:armstate`]
     BYTE_LIST_AT_5BLOCKS) THEN
  REWRITE_TAC[byte_list_at] THEN ASM_SIMP_TAC[]
);;

let READ_TAIL4_LEMMA = prove(
  `!ptr (n5blocks:int64) (len:int64) (bl:byte list) s.
    (forall j. j < val len ==> read (memory :> bytes8 (word_add ptr (word j))) s = EL j bl)
    /\ val n5blocks * 0x50 + 0x40 <= val len
    /\ LENGTH bl = val len
    ==>
    read (memory :> bytes128 (word_add
      (word_add ptr (word_mul (word 0x50) n5blocks))
      (word 0x30))) s =
      bytes_to_int128 (SUB_LIST (val n5blocks * 80 + 0x30, 16) bl) /\
    read (memory :> bytes128 (word_add
      (word_add ptr (word_mul (word 0x50) n5blocks))
      (word 0x20))) s =
      bytes_to_int128 (SUB_LIST (val n5blocks * 80 + 0x20, 16) bl) /\
    read (memory :> bytes128 (word_add
      (word_add ptr (word_mul (word 0x50) n5blocks))
      (word 0x10))) s =
      bytes_to_int128 (SUB_LIST (val n5blocks * 80 + 0x10, 16) bl) /\
    read (memory :> bytes128
      (word_add ptr (word_mul (word 0x50) n5blocks))) s =
      bytes_to_int128 (SUB_LIST (val n5blocks * 80, 16) bl)
    `,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC [WORD_RULE `(word_mul (word 0x50) (n5blocks:int64)) = word (val n5blocks * 80)`] THEN
  MP_TAC
    (SPECL [`(val (n5blocks:int64) * 80):num`; `bl:byte list`; `ptr:int64`; `len:int64`; `s:armstate`]
     BYTE_LIST_AT_4BLOCKS) THEN
  REWRITE_TAC[byte_list_at] THEN ASM_SIMP_TAC[]
);;

let READ_TAIL3_LEMMA = prove(
  `!ptr (n5blocks:int64) (len:int64) (bl:byte list) s.
    (forall j. j < val len ==> read (memory :> bytes8 (word_add ptr (word j))) s = EL j bl)
    /\ val n5blocks * 0x50 + 0x30 <= val len
    /\ LENGTH bl = val len
    ==>
    read (memory :> bytes128 (word_add
      (word_add ptr (word_mul (word 0x50) n5blocks))
      (word 0x20))) s =
      bytes_to_int128 (SUB_LIST (val n5blocks * 80 + 0x20, 16) bl) /\
    read (memory :> bytes128 (word_add
      (word_add ptr (word_mul (word 0x50) n5blocks))
      (word 0x10))) s =
      bytes_to_int128 (SUB_LIST (val n5blocks * 80 + 0x10, 16) bl) /\
    read (memory :> bytes128
      (word_add ptr (word_mul (word 0x50) n5blocks))) s =
      bytes_to_int128 (SUB_LIST (val n5blocks * 80, 16) bl)
    `,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC [WORD_RULE `(word_mul (word 0x50) (n5blocks:int64)) = word (val n5blocks * 80)`] THEN
  MP_TAC
    (SPECL [`(val (n5blocks:int64) * 80):num`; `bl:byte list`; `ptr:int64`; `len:int64`; `s:armstate`]
     BYTE_LIST_AT_3BLOCKS) THEN
  REWRITE_TAC[byte_list_at] THEN ASM_SIMP_TAC[]
);;

let READ_TAIL2_LEMMA = prove(
  `!ptr (n5blocks:int64) (len:int64) (bl:byte list) s.
    (forall j. j < val len ==> read (memory :> bytes8 (word_add ptr (word j))) s = EL j bl)
    /\ val n5blocks * 0x50 + 0x20 <= val len
    /\ LENGTH bl = val len
    ==>
    read (memory :> bytes128 (word_add
      (word_add ptr (word_mul (word 0x50) n5blocks))
      (word 0x10))) s =
      bytes_to_int128 (SUB_LIST (val n5blocks * 80 + 0x10, 16) bl) /\
    read (memory :> bytes128
      (word_add ptr (word_mul (word 0x50) n5blocks))) s =
      bytes_to_int128 (SUB_LIST (val n5blocks * 80, 16) bl)
    `,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC [WORD_RULE `(word_mul (word 0x50) (n5blocks:int64)) = word (val n5blocks * 80)`] THEN
  MP_TAC
    (SPECL [`(val (n5blocks:int64) * 80):num`; `bl:byte list`; `ptr:int64`; `len:int64`; `s:armstate`]
     BYTE_LIST_AT_2BLOCKS) THEN
  REWRITE_TAC[byte_list_at] THEN ASM_SIMP_TAC[]
);;

let READ_TAIL1_LEMMA = prove(
  `!ptr (n5blocks:int64) (len:int64) (bl:byte list) s.
    (forall j. j < val len ==> read (memory :> bytes8 (word_add ptr (word j))) s = EL j bl)
    /\ val n5blocks * 0x50 + 0x10 <= val len
    /\ LENGTH bl = val len
    ==>
    read (memory :> bytes128
      (word_add ptr (word_mul (word 0x50) n5blocks))) s =
      bytes_to_int128 (SUB_LIST (val n5blocks * 80, 16) bl)
    `,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC [WORD_RULE `(word_mul (word 0x50) (n5blocks:int64)) = word (val n5blocks * 80)`] THEN
  MP_TAC
    (SPECL [`(val (n5blocks:int64) * 80):num`; `bl:byte list`; `ptr:int64`; `len:int64`; `s:armstate`]
     BYTE_LIST_AT_1BLOCKS) THEN
  REWRITE_TAC[byte_list_at] THEN ASM_SIMP_TAC[]
);;

let READ_LAST_LEMMA = prove(
  `!ptr (curr_len:num) (len:int64) (bl:byte list) s.
    (forall j. j < val len ==> read (memory :> bytes8 (word_add ptr (word j))) s = EL j bl)
    /\ curr_len + 0x10 <= val len
    /\ LENGTH bl = val len
    ==>
    read (memory :> bytes128 (word_add ptr (word curr_len))) s =
      bytes_to_int128 (SUB_LIST (curr_len, 16) bl)
    `,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
    (SPECL [`curr_len:num`; `bl:byte list`; `ptr:int64`; `len:int64`; `s:armstate`]
     BYTE_LIST_AT_1BLOCKS) THEN
  REWRITE_TAC[byte_list_at] THEN ASM_SIMP_TAC[]
);;

let UDIV_OPT_THM = prove(`!n:num. n < 0x2 EXP 0x40
  ==> (word (val ((word ((n * 0xcccccccccccccccd) DIV 0x2 EXP 0x40)):int64) DIV 0x2 EXP 0x6)):int64 = word (n DIV 0x50)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `!p n:num. ~(p = 0) /\ n < p * p ==> n DIV p MOD p = n DIV p`
    (MP_TAC o SPECL [`0x2 EXP 0x40`; `n * 0xcccccccccccccccd`]) THENL
  [ REPEAT STRIP_TAC THEN
    REWRITE_TAC[DIV_MOD] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC MOD_LT THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* For encrypt *)
let LEN_FULL_BLOCKS_LO_BOUND_THM = prove(
  `!(len:int64) len_full_blocks. word_and len (word 0xfffffffffffffff0) = len_full_blocks
   ==> ~(val len < 0x50)
   ==> ~(val len_full_blocks < 0x50)`,
   BITBLAST_TAC);;

(* For decrypt *)
let NUM_BLOCKS_LO_BOUND_THM = prove(
  `!(len:int64) num_blocks. word_and len (word 0xfffffffffffffff0) = num_blocks
   ==> ~(val len < 0x60)
   ==> ~(val num_blocks < 0x60)`,
   BITBLAST_TAC);;

let NUM_BLOCKS_LO_BOUND_1BLOCK_THM = prove(
  `!(len:int64) num_blocks. word_and len (word 0xfffffffffffffff0) = num_blocks
   ==> ~(val len < 16)
   ==> ~(val num_blocks < 16)`,
   BITBLAST_TAC);;

let NUM_BLOCKS_HI_BOUND_THM = prove(
  `!(len:int64) num_blocks. word_and len (word 0xfffffffffffffff0) = num_blocks
   ==> val len <= 2 EXP 24
   ==> val num_blocks <= 2 EXP 24`,
   BITBLAST_TAC);;

let TAIL_LEN_BOUND_THM = prove(
  `!(len:int64) tail_len. word_and len (word 0xf) = tail_len
   ==> val tail_len < 0x10`,
   BITBLAST_TAC);;

let NUM_BLOCKS_LT_LEN_THM = prove(
  `!(len:int64). val (word_and len (word 0xfffffffffffffff0)) <= val len`,
  BITBLAST_TAC
);;

(* For encrypt *)
let NUM_5BLOCKS_LO_BOUND_THM = prove(
  `!(len_full_blocks:int64) (num_5blocks:int64).
    val len_full_blocks <= 2 EXP 24
    ==> ~(val len_full_blocks < 0x50)
    ==> word (val len_full_blocks DIV 0x50) = num_5blocks
    ==> 0x0 < val num_5blocks`,
  REPEAT STRIP_TAC THEN
  EXPAND_TAC "num_5blocks" THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  UNDISCH_TAC `~(val (len_full_blocks:int64) < 0x50)` THEN
  ABBREV_TAC `n = val (len_full_blocks:int64)` THEN
  SUBGOAL_THEN `n DIV 0x50 < 2 EXP 64` ASSUME_TAC THENL
  [ ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  ARITH_TAC
);;

(* For decrypt *)
let NUM_BLOCKS_ADJUSTED_LO_BOUND_THM = prove(
  `!(num_blocks:int64) (tail_len:int64) num_blocks_adjusted.
    (if val tail_len = 0x0 then num_blocks else word_sub num_blocks (word 0x10)) = num_blocks_adjusted
    ==> ~(val num_blocks < 0x60)
    ==> ~(val num_blocks_adjusted < 0x50)`,
  BITBLAST_TAC
);;

let NUM_BLOCKS_ADJUSTED_LO_BOUND_1BLOCK_THM = prove(
  `!(num_blocks:int64) (tail_len:int64) num_blocks_adjusted.
    (if val tail_len = 0x0 then num_blocks else word_sub num_blocks (word 0x10)) = num_blocks_adjusted
    ==> ~(val num_blocks < 16)
    ==> ~(val num_blocks_adjusted < 0)`,
  BITBLAST_TAC
);;

let NUM_BLOCKS_ADJUSTED_HI_BOUND_THM = prove(
  `!(num_blocks:int64) (tail_len:int64) num_blocks_adjusted.
    (if val tail_len = 0x0 then num_blocks else word_sub num_blocks (word 0x10)) = num_blocks_adjusted
    ==> val num_blocks <= 2 EXP 24
    ==> ~(val num_blocks < 16)
    ==> val num_blocks_adjusted <= 2 EXP 24`,
  BITBLAST_TAC
);;

let NUM_5BLOCKS_ADJUSTED_LO_BOUND_THM = prove(
  `!(num_blocks_adjusted:int64) (num_5blocks_adjusted:int64).
    val num_blocks_adjusted <= 0x2 EXP 0x18
    ==> ~(val num_blocks_adjusted < 0x50)
    ==> word (val num_blocks_adjusted DIV 0x50) = num_5blocks_adjusted
    ==> 0x0 < val num_5blocks_adjusted`,
  REPEAT STRIP_TAC THEN
  EXPAND_TAC "num_5blocks_adjusted" THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  UNDISCH_TAC `~(val (num_blocks_adjusted:int64) < 0x50)` THEN
  ABBREV_TAC `n = val (num_blocks_adjusted:int64)` THEN
  SUBGOAL_THEN `n DIV 80 < 2 EXP 64` ASSUME_TAC THENL
  [ ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN
  ARITH_TAC
);;

let NUM_BLOCKS_ADJUSTED_LT_LEN_THM = prove(
  `!(len:int64) num_blocks.
    word_and len (word 0xfffffffffffffff0) = num_blocks
    ==> ~(val num_blocks < 16)
    ==> val (word_sub num_blocks (word 0x10)) <= val len`,
    BITBLAST_TAC
);;


let MEMORY_READ_SUBSET_LEMMA = prove
 (`!len (ptr:int64) (bl:byte list) s.
   (forall i.
          i < SUC len
          ==> read (memory :> bytes8 (word_add ptr (word i))) s = EL i bl) ==>
   (forall i.
           i < len
           ==> read (memory :> bytes8 (word_add ptr (word i))) s = EL i bl) /\
   read (memory :> bytes (word_add ptr (word len),1)) s =
    val(read (memory :> bytes8 (word_add ptr (word len))) s)
   `,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  CONJ_TAC THENL
  [ GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[LT_SUC_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[bytes8; READ_COMPONENT_COMPOSE; asword; through; read] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  IMP_REWRITE_TAC[MOD_LT] THEN
  MP_TAC (ISPECL [`(word_add (ptr:int64) (word len)):int64`; `1:num`; `(read memory s):int64->byte`] READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV
);;

let BYTE_LIST_AT_SPLIT = prove(
  `!len (ptr:int64) (bl:byte list) s.
  SUC len <= LENGTH bl ==>
   ((forall i.
     i < SUC len
     ==> read (memory :> bytes8 (word_add ptr (word i))) s = EL i bl) <=>
   ((forall i.
     i < len
     ==> read (memory :> bytes8 (word_add ptr (word i))) s = EL i bl) /\
    read (memory :> bytes8 (word_add ptr (word len))) s = EL len bl))`,
    REPEAT STRIP_TAC THEN
    EQ_TAC THENL
    [ STRIP_TAC THEN
      CONJ_TAC THENL
      [ ASM_SIMP_TAC[ARITH_RULE `i < len ==> i < SUC len`];
        ASM_SIMP_TAC[ARITH_RULE `len < SUC len`]];
      ALL_TAC ] THEN
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `i < len` THENL
    [ FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[];
      SUBGOAL_THEN `i = len:num` SUBST1_TAC THENL
      [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]
    ]
);;

let BYTE_LIST_AT_SPLIT_BACKWARDS = prove(
  `!(pt_ptr:int64) i len curr_len bl s.
  0 <= i ==> i < len ==> len < 16 ==> LENGTH bl >= 16 ==>
  (forall j.
    j < len - (i + 1)
    ==> read (memory :> bytes8
          (word_add (word_add pt_ptr (word (curr_len + 16 + i + 1)))
                    (word j))) s =
        EL j (SUB_LIST (i + 1, len - (i + 1)) bl)) ==>
  read (memory :> bytes8 (word_add pt_ptr (word (curr_len + 16 + i)))) s = (EL i bl) ==>
  forall j.
    j < len - i
    ==> read (memory :> bytes8
          (word_add (word_add pt_ptr (word (curr_len + 16 + i)))
                    (word j))) s =
        EL j (SUB_LIST (i, len - i) bl)
  `,
  REPEAT GEN_TAC THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `j > 0` THENL
  [
    FIRST_X_ASSUM(MP_TAC o SPEC `j - 1`) THEN
    ANTS_TAC THENL[ ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(word_add (word_add (pt_ptr:int64) (word (curr_len + 0x10 + i + 0x1)))
      (word (j - 0x1))) = (word_add (word_add pt_ptr (word (curr_len + 0x10 + i))) (word j))` SUBST1_TAC THENL
    [ REWRITE_TAC[WORD_RULE `word_add (word_add a (word b)) (word c) = word_add a (word (b + c))`] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[] THEN DISCH_TAC THEN
    IMP_REWRITE_TAC[ARITH_RULE `len - (i + 1) = len - i - 1`;
      EL_SUB_LIST_SHIFT] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN

  SUBGOAL_THEN `j = 0` SUBST_ALL_TAC THENL[ASM_ARITH_TAC;ALL_TAC] THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN
  IMP_REWRITE_TAC[EL_SUB_LIST_TRIVIAL] THEN
  ASM_ARITH_TAC
);;

(* Differs from Encrypt in that the address is written in a canonical form *)
let BYTE_LIST_AT_SPLIT_BACKWARDS_CARNONICAL = prove(
  `!(pt_ptr:int64) i len curr_len bl s.
  0 <= i ==> i < len ==> len < 16 ==> LENGTH bl >= 16 ==>
  (forall j.
    j < len - (i + 1)
    ==> read (memory :> bytes8
          (word_add pt_ptr (word (curr_len + 16 + i + 1 + j)))) s =
        EL j (SUB_LIST (i + 1, len - (i + 1)) bl)) ==>
  read (memory :> bytes8 (word_add pt_ptr (word (curr_len + 16 + i)))) s = (EL i bl) ==>
  forall j.
    j < len - i
    ==> read (memory :> bytes8
          (word_add pt_ptr (word (curr_len + 16 + i + j)))) s =
        EL j (SUB_LIST (i, len - i) bl)
  `,
  REPEAT GEN_TAC THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `j > 0` THENL
  [
    FIRST_X_ASSUM(MP_TAC o SPEC `j - 1`) THEN
    ANTS_TAC THENL[ ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ADD_ASSOC; ARITH_RULE `j > 0 ==> curr_len + 0x10 + i + 0x1 + j - 0x1 = curr_len + 0x10 + i + j`] THEN
    SIMP_TAC[] THEN DISCH_TAC THEN
    IMP_REWRITE_TAC[ARITH_RULE `len - (i + 1) = len - i - 1`;
      EL_SUB_LIST_SHIFT] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN

  SUBGOAL_THEN `j = 0` SUBST_ALL_TAC THENL[ASM_ARITH_TAC;ALL_TAC] THEN
  REWRITE_TAC[ADD_0] THEN
  ASM_REWRITE_TAC[] THEN
  IMP_REWRITE_TAC[EL_SUB_LIST_TRIVIAL] THEN
  ASM_ARITH_TAC
);;

let MEMORY_READ_BYTES_SUBSET_LEMMA = prove(
  `!len (ptr:int64) (bl:byte list) s.
   SUC len <= LENGTH bl ==>
   read (memory :> bytes (ptr,SUC len)) s =
      num_of_bytelist (SUB_LIST (0x0,SUC len) bl) ==>
   read (memory :> bytes (ptr,len)) s =
      num_of_bytelist (SUB_LIST (0x0,len) bl) /\
   read (memory :> bytes8 (word_add ptr (word len))) s = EL len bl`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `SUC len = len + 1` SUBST_ALL_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  SUBGOAL_THEN `len <= LENGTH (bl:byte list)` ASSUME_TAC THENL [ ASM_ARITH_TAC; ALL_TAC] THEN
  (* Use READ_BYTES_COMBINE to decompose the memory read *)
  MP_TAC(ISPECL [`ptr:int64`; `len:num`; `1:num`; `(read memory s):int64->byte`] READ_BYTES_COMBINE) THEN
  DISCH_TAC THEN
  (* Use SUB_LIST_SPLIT to decompose the byte list *)
  MP_TAC(ISPECL [`bl:byte list`; `len:num`; `1:num`; `0:num`] SUB_LIST_SPLIT) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN
  (* Decompose num_of_bytelist *)
  SUBGOAL_THEN
   `num_of_bytelist (SUB_LIST (0,len + 1) (bl:byte list)) =
    num_of_bytelist (SUB_LIST (0,len) bl) +
    2 EXP (8 * len) * num_of_bytelist (SUB_LIST (len,1) bl)`
  ASSUME_TAC THENL
   [ ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[NUM_OF_BYTELIST_APPEND] THEN
     AP_TERM_TAC THEN AP_THM_TAC THEN REPEAT_N 3 AP_TERM_TAC THEN
     IMP_REWRITE_TAC[LENGTH_SUB_LIST; MIN; SUB_0] THEN
     ASM_SIMP_TAC[]
     ; ALL_TAC] THEN
  (* Rewrite in goal *)
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  CONJ_TAC THENL
  [ (* First part: read (memory :> bytes (ptr,len)) s = num_of_bytelist (SUB_LIST (0,len) bl) *)
    FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x MOD 2 EXP (8 * len)`) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MOD_MULT_ADD; MOD_LT] THEN
    REWRITE_TAC[READ_BYTES_MOD; MIN] THEN
    SIMP_TAC[ARITH_RULE `len <= len`] THEN
    DISCH_TAC THEN
    IMP_REWRITE_TAC[MOD_LT] THEN
    MP_TAC (SPEC `(SUB_LIST (0,len) bl:byte list)` NUM_OF_BYTELIST_BOUND) THEN
    IMP_REWRITE_TAC[LENGTH_SUB_LIST; SUB_0; MIN] THEN
    SUBGOAL_THEN `256 EXP len = 2 EXP (8 * len)` SUBST1_TAC THENL
    [ REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP]; ALL_TAC] THEN
    SIMP_TAC[];
    ALL_TAC
  ] THEN
  (* Second part: read (memory :> bytes8 (word_add ptr (word len))) s = EL len bl *)
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x DIV 2 EXP (8 * len)`) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(0x2 EXP (0x8 * len) = 0x0)` ASSUME_TAC THENL
  [ REWRITE_TAC[EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  IMP_REWRITE_TAC[DIV_MULT_ADD] THEN
  SUBGOAL_THEN `read (bytes (ptr,len)) (read memory s) < 0x2 EXP (0x8 * len)` ASSUME_TAC THENL
  [ REWRITE_TAC[READ_BYTES_BOUND]; ALL_TAC] THEN
  SUBGOAL_THEN `num_of_bytelist (SUB_LIST (0x0,len) bl) < 0x2 EXP (0x8 * len)` ASSUME_TAC THENL
  [ MP_TAC (SPEC `(SUB_LIST (0,len) bl:byte list)` NUM_OF_BYTELIST_BOUND) THEN
    IMP_REWRITE_TAC[LENGTH_SUB_LIST; SUB_0; MIN] THEN
    SUBGOAL_THEN `256 EXP len = 2 EXP (8 * len)` SUBST1_TAC THENL
    [ REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP]; ALL_TAC] THEN SIMP_TAC[]; ALL_TAC] THEN
  IMP_REWRITE_TAC[DIV_LT; ADD] THEN
  (* Some rewrites to close the goal *)
  REWRITE_TAC[bytes8; READ_COMPONENT_COMPOSE; asword; through; read] THEN
  SUBGOAL_THEN `len < LENGTH (bl:byte list)` ASSUME_TAC THENL [ ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SUB_LIST_1] THEN
  REWRITE_TAC[num_of_bytelist; MULT_CLAUSES; ADD_CLAUSES; WORD_VAL]
);;

let BYTE_LIST_TO_NUM_THM = prove(
  `!len (ptr:int64) (bl:byte list) s.
    len <= LENGTH bl ==>
    ((forall i. i < len
      ==> read (memory :> bytes8 (word_add ptr (word i))) s = EL i bl) <=>
    (read (memory :> bytes (ptr, len)) s = num_of_bytelist (SUB_LIST (0, len) bl)))`,
  REPEAT GEN_TAC THEN
  SPEC_TAC (`len:num`, `len:num`) THEN
  (* Base case: len = 0 *)
  INDUCT_TAC THENL
  [ STRIP_TAC THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL;
      CONJUNCT1 SUB_LIST; CONJUNCT1 num_of_bytelist] THEN
    GEN_TAC THEN MESON_TAC[ARITH_RULE `~(i < 0)`];
    ALL_TAC] THEN

  (* Inductive step: left to right *)
  STRIP_TAC THEN
  EQ_TAC THENL
  [ MP_TAC (ARITH_RULE `SUC len <= LENGTH (bl:byte list) ==> len <= LENGTH bl`) THEN
    ASM_SIMP_TAC[] THEN REPEAT DISCH_TAC THEN
    MP_TAC (SPECL [`len:num`; `ptr:int64`; `bl:byte list`; `s:armstate`] MEMORY_READ_SUBSET_LEMMA) THEN
    ASM_SIMP_TAC[] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; ADD1] THEN
    ONCE_REWRITE_TAC[READ_BYTES_COMBINE] THEN
    REWRITE_TAC[SUB_LIST_SPLIT; NUM_OF_BYTELIST_APPEND; CONJUNCT1 ADD] THEN
    IMP_REWRITE_TAC[ARITH_RULE `a = c ==> (a + b = c + d) = (b = d)`] THEN
    CONJ_TAC THENL [
      REWRITE_TAC[LENGTH_SUB_LIST; MIN; SUB_0] THEN
      ASM_SIMP_TAC[] THEN
      AP_TERM_TAC THEN
      REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
      FIRST_X_ASSUM (fun th -> MP_TAC (SPEC `len:num` th)) THEN
      REWRITE_TAC[ARITH_RULE `len < SUC len`] THEN
      SUBGOAL_THEN `len < LENGTH (bl:byte list)` ASSUME_TAC THENL
      [ ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[SUB_LIST_1; num_of_bytelist] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ADD_0] THEN
      STRIP_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC[]
      ; ALL_TAC] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    ASM_SIMP_TAC[]
    ; ALL_TAC] THEN

  (* Inductive step: right to left *)
  MP_TAC (ARITH_RULE `SUC len <= LENGTH (bl:byte list) ==> len <= LENGTH bl`) THEN
  ASM_SIMP_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC (SPECL [`len:num`; `ptr:int64`; `bl:byte list`; `s:armstate`] MEMORY_READ_BYTES_SUBSET_LEMMA) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  IMP_REWRITE_TAC[BYTE_LIST_AT_SPLIT] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[]
);;


let READ_MEMORY_BYTES128_BYTES = prove(`!z s.
    read (memory :> bytes128 z) s = word (read (memory :> bytes (z,16)) s)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  IMP_REWRITE_TAC [VAL_WORD_EQ] THEN
  CONJ_TAC THENL [REWRITE_TAC [READ_MEMORY_BYTES_BYTES128]; ALL_TAC] THEN
  REWRITE_TAC [MEMORY_BYTES_BOUND]
  );;

let WORD_JOIN_BOUND_TAC x y =
  REWRITE_TAC[VAL_WORD_JOIN; DIMINDEX_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  IMP_REWRITE_TAC[MOD_LT] THEN
  CONJ_TAC THENL[ REWRITE_TAC[ADD_SYM]; ALL_TAC ] THEN
  MP_TAC (ISPECL [x] VAL_BOUND) THEN
  MP_TAC (ISPECL [y] VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC;;

let WORD_JOIN_16_8_ASSOC = WORD_BLAST
  `!(x0:byte) (x1:byte) (x2:byte) (x3:byte)
    (x4:byte) (x5:byte) (x6:byte) (x7:byte)
    (x8:byte) (x9:byte) (x10:byte) (x11:byte)
    (x12:byte) (x13:byte) (x14:byte) (x15:byte).
    (word_join
      (word_join
        (word_join (word_join x15 x14 : int16) (word_join x13 x12 : int16) : int32)
        (word_join (word_join x11 x10 : int16) (word_join x9 x8 : int16) : int32) : int64)
      (word_join
        (word_join (word_join x7 x6 : int16) (word_join x5 x4 : int16) : int32)
        (word_join (word_join x3 x2 : int16) (word_join x1 x0 : int16) : int32) : int64)) =
    (word_join
      (word_join
        (word_join
          (word_join
            (word_join
              (word_join
                (word_join
                  (word_join
                    (word_join
                      (word_join
                        (word_join
                          (word_join
                            (word_join
                              (word_join
                                (word_join x15 x14:16 word)
                              x13:24 word)
                            x12:32 word)
                          x11:40 word)
                        x10:48 word)
                      x9:56 word)
                    x8:64 word)
                  x7:72 word)
                x6:80 word)
              x5:88 word)
            x4:96 word)
          x3:104 word)
        x2:112 word)
      x1:120 word)
    x0:128 word)`;;

let VAL_OF_BYTES_TO_INT128_EQ_NUM_OF_BYTELIST = prove(
  `!x:byte list. LENGTH x = 16 ==> val (bytes_to_int128 x) = num_of_bytelist x`,
  REPEAT STRIP_TAC THEN
  (* conversion for breaking down a list *)
  MP_TAC ((GEN_REWRITE_CONV I [LENGTH_EQ_LIST_OF_SEQ] THENC
   RAND_CONV LIST_OF_SEQ_CONV) `LENGTH (x:byte list) = 16`) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN (fun th -> ONCE_REWRITE_TAC[th]) THEN
  REWRITE_TAC[bytes_to_int128] THEN
  REWRITE_TAC EL_16_8_CLAUSES THEN
  REPEAT_N 16 (ONCE_REWRITE_TAC[num_of_bytelist]) THEN
  REWRITE_TAC[CONJUNCT1 num_of_bytelist] THEN
  MAP_EVERY ABBREV_TAC
    [`x0 = EL 0 x:byte`; `x1 = EL 1 x:byte`; `x2 = EL 2 x:byte`; `x3 = EL 3 x:byte`;
     `x4 = EL 4 x:byte`; `x5 = EL 5 x:byte`; `x6 = EL 6 x:byte`; `x7 = EL 7 x:byte`;
     `x8 = EL 8 x:byte`; `x9 = EL 9 x:byte`; `x10 = EL 10 x:byte`; `x11 = EL 11 x:byte`;
     `x12 = EL 12 x:byte`; `x13 = EL 13 x:byte`; `x14 = EL 14 x:byte`; `x15 = EL 15 x:byte`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ADD_0; WORD_JOIN_16_8_ASSOC] THEN
  (* reduce RHS to LHS *)
  SUBGOAL_THEN `val (x14:byte) + 0x100 * val (x15:byte) = val ((word_join x15 x14):int16)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `x15:byte` `x14:byte`; ALL_TAC] THEN ABBREV_TAC `y14:int16 = word_join (x15:byte) (x14:byte)` THEN
  SUBGOAL_THEN `val (x13:byte) + 0x100 * val (y14:16 word) = val ((word_join y14 x13):24 word)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `y14:16 word` `x13:byte`; ALL_TAC] THEN ABBREV_TAC `y13:24 word = word_join (y14:16 word) (x13:byte)` THEN
  SUBGOAL_THEN `val (x12:byte) + 0x100 * val (y13:24 word) = val ((word_join y13 x12):32 word)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `y13:24 word` `x12:byte`; ALL_TAC] THEN ABBREV_TAC `y12:32 word = word_join (y13:24 word) (x12:byte)` THEN
  SUBGOAL_THEN `val (x11:byte) + 0x100 * val (y12:32 word) = val ((word_join y12 x11):40 word)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `y12:32 word` `x11:byte`; ALL_TAC] THEN ABBREV_TAC `y11:40 word = word_join (y12:32 word) (x11:byte)` THEN
  SUBGOAL_THEN `val (x10:byte) + 0x100 * val (y11:40 word) = val ((word_join y11 x10):48 word)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `y11:40 word` `x10:byte`; ALL_TAC] THEN ABBREV_TAC `y10:48 word = word_join (y11:40 word) (x10:byte)` THEN
  SUBGOAL_THEN `val (x9:byte) + 0x100 * val (y10:48 word) = val ((word_join y10 x9):56 word)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `y10:48 word` `x9:byte`; ALL_TAC] THEN ABBREV_TAC `y9:56 word = word_join (y10:48 word) (x9:byte)` THEN
  SUBGOAL_THEN `val (x8:byte) + 0x100 * val (y9:56 word) = val ((word_join y9 x8):64 word)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `y9:56 word` `x8:byte`; ALL_TAC] THEN ABBREV_TAC `y8:64 word = word_join (y9:56 word) (x8:byte)` THEN
  SUBGOAL_THEN `val (x7:byte) + 0x100 * val (y8:64 word) = val ((word_join y8 x7):72 word)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `y8:64 word` `x7:byte`; ALL_TAC] THEN ABBREV_TAC `y7:72 word = word_join (y8:64 word) (x7:byte)` THEN
  SUBGOAL_THEN `val (x6:byte) + 0x100 * val (y7:72 word) = val ((word_join y7 x6):80 word)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `y7:72 word` `x6:byte`; ALL_TAC] THEN ABBREV_TAC `y6:80 word = word_join (y7:72 word) (x6:byte)` THEN
  SUBGOAL_THEN `val (x5:byte) + 0x100 * val (y6:80 word) = val ((word_join y6 x5):88 word)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `y6:80 word` `x5:byte`; ALL_TAC] THEN ABBREV_TAC `y5:88 word = word_join (y6:80 word) (x5:byte)` THEN
  SUBGOAL_THEN `val (x4:byte) + 0x100 * val (y5:88 word) = val ((word_join y5 x4):96 word)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `y5:88 word` `x4:byte`; ALL_TAC] THEN ABBREV_TAC `y4:96 word = word_join (y5:88 word) (x4:byte)` THEN
  SUBGOAL_THEN `val (x3:byte) + 0x100 * val (y4:96 word) = val ((word_join y4 x3):104 word)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `y4:96 word` `x3:byte`; ALL_TAC] THEN ABBREV_TAC `y3:104 word = word_join (y4:96 word) (x3:byte)` THEN
  SUBGOAL_THEN `val (x2:byte) + 0x100 * val (y3:104 word) = val ((word_join y3 x2):112 word)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `y3:104 word` `x2:byte`; ALL_TAC] THEN ABBREV_TAC `y2:112 word = word_join (y3:104 word) (x2:byte)` THEN
  SUBGOAL_THEN `val (x1:byte) + 0x100 * val (y2:112 word) = val ((word_join y2 x1):120 word)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `y2:112 word` `x1:byte`; ALL_TAC] THEN ABBREV_TAC `y1:120 word = word_join (y2:112 word) (x1:byte)` THEN
  SUBGOAL_THEN `val (x0:byte) + 0x100 * val (y1:120 word) = val ((word_join y1 x0):128 word)` SUBST1_TAC THENL
  [ WORD_JOIN_BOUND_TAC `y1:120 word` `x0:byte`; ALL_TAC] THEN ABBREV_TAC `y0:128 word = word_join (y1:120 word) (x0:byte)` THEN
  REFL_TAC
);;


let READ_BYTES_AND_BYTE128_SPLIT = prove(
  `!(pt_ptr:int64) (sz:num) (x:byte list) (s:armstate).
    sz + 16 <= LENGTH x ==>
    read (memory :> bytes128 (word_add pt_ptr (word sz))) s = bytes_to_int128 (SUB_LIST (sz, 0x10) x)
    /\ read (memory :> bytes (pt_ptr, sz)) s = num_of_bytelist (SUB_LIST (0, sz) x)
    ==> read (memory :> bytes (pt_ptr,sz + 0x10)) s = num_of_bytelist (SUB_LIST (0, sz + 0x10) x)`,
  REWRITE_TAC[READ_MEMORY_BYTES128_BYTES] THEN
  REPEAT STRIP_TAC THEN

  SUBGOAL_THEN `sz <= LENGTH (x:byte list)` ASSUME_TAC THENL
  [ UNDISCH_TAC `sz + 16 <= LENGTH (x:byte list)` THEN ARITH_TAC; ALL_TAC ] THEN

  SUBGOAL_THEN `16 <= LENGTH (x:byte list) - sz` ASSUME_TAC THENL
  [ UNDISCH_TAC `sz + 16 <= LENGTH (x:byte list)` THEN ARITH_TAC; ALL_TAC ] THEN

  SUBGOAL_THEN `read (memory :> bytes (pt_ptr, sz + 16)) s =
                read (memory :> bytes (pt_ptr, sz)) s +
                2 EXP (8 * sz) * (read (memory :> bytes (word_add pt_ptr (word sz), 16)) s)` SUBST1_TAC THENL
  [ REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
    REWRITE_TAC[READ_BYTES_COMBINE]; ALL_TAC] THEN

  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `read (memory :> bytes (word_add pt_ptr (word sz),0x10)) s =
      val (bytes_to_int128 (SUB_LIST (sz,0x10) x))` SUBST1_TAC THENL
  [ UNDISCH_THEN
     `word (read (memory :> bytes (word_add (pt_ptr:int64) (word sz),0x10)) s) =
      bytes_to_int128 (SUB_LIST (sz,0x10) x)`
      (fun th -> MP_TAC (AP_TERM `val:int128->num` th)) THEN
    IMP_REWRITE_TAC[VAL_WORD] THEN
    SUBGOAL_THEN `read (memory :> bytes (word_add pt_ptr (word sz),0x10)) s < 2 EXP dimindex (:128)` ASSUME_TAC THENL
    [ SIMP_TAC[MEMORY_BYTES_BOUND] ; ALL_TAC] THEN
    SUBST_ALL_TAC DIMINDEX_128 THEN
    ASM_SIMP_TAC[MOD_LT]; ALL_TAC] THEN

  IMP_REWRITE_TAC[NUM_OF_BYTELIST_OF_SUB_LIST] THEN
  IMP_REWRITE_TAC[VAL_OF_BYTES_TO_INT128_EQ_NUM_OF_BYTELIST] THEN
  REWRITE_TAC[LENGTH_SUB_LIST; MIN] THEN ASM_SIMP_TAC[]
);;

let READ_BYTES_AND_BYTE128_MERGE = prove(
  `!(pt_ptr:int64) (sz:num) (x:byte list) (s:armstate).
    sz + 16 <= LENGTH x ==>
    read (memory :> bytes (pt_ptr,sz + 0x10)) s = num_of_bytelist (SUB_LIST (0, sz + 0x10) x)
    ==> (read (memory :> bytes (pt_ptr, sz)) s = num_of_bytelist (SUB_LIST (0, sz) x) /\
         read (memory :> bytes128 (word_add pt_ptr (word sz))) s = bytes_to_int128 (SUB_LIST (sz, 0x10) x))`,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  REWRITE_TAC[READ_MEMORY_BYTES128_BYTES] THEN

  SUBGOAL_THEN `sz <= LENGTH (x:byte list)` ASSUME_TAC THENL
  [ UNDISCH_TAC `sz + 16 <= LENGTH (x:byte list)` THEN ARITH_TAC; ALL_TAC ] THEN

  SUBGOAL_THEN `16 <= LENGTH (x:byte list) - sz` ASSUME_TAC THENL
  [ UNDISCH_TAC `sz + 16 <= LENGTH (x:byte list)` THEN ARITH_TAC; ALL_TAC ] THEN

  SUBGOAL_THEN `read (memory :> bytes (pt_ptr, sz + 16)) s =
                read (memory :> bytes (pt_ptr, sz)) s +
                2 EXP (8 * sz) * (read (memory :> bytes (word_add pt_ptr (word sz), 16)) s)` SUBST1_TAC THENL
  [ REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
    REWRITE_TAC[READ_BYTES_COMBINE]; ALL_TAC] THEN

  IMP_REWRITE_TAC[NUM_OF_BYTELIST_OF_SUB_LIST] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN

  DISCH_TAC THEN
  CONJ_TAC THENL
  [ (* First part: `read (bytes (pt_ptr,sz)) (read memory s) =
        num_of_bytelist (SUB_LIST (0x0,sz) x)`*)
    FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x MOD 2 EXP (8 * sz)`) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MOD_MULT_ADD; MOD_LT] THEN
    REWRITE_TAC[READ_BYTES_MOD; MIN] THEN
    SIMP_TAC[ARITH_RULE `len <= len`] THEN
    DISCH_TAC THEN
    IMP_REWRITE_TAC[MOD_LT] THEN
    MP_TAC (SPEC `(SUB_LIST (0,sz) x:byte list)` NUM_OF_BYTELIST_BOUND) THEN
    IMP_REWRITE_TAC[LENGTH_SUB_LIST; SUB_0; MIN] THEN
    SUBGOAL_THEN `256 EXP sz = 2 EXP (8 * sz)` SUBST1_TAC THENL
    [ REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP]; ALL_TAC] THEN
    SIMP_TAC[];
    ALL_TAC
  ] THEN
  (* Second part: word (read (bytes (word_add pt_ptr (word sz),0x10)) (read memory s)) =
      bytes_to_int128 (SUB_LIST (sz,0x10) x) *)
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x DIV 2 EXP (8 * sz)`) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(0x2 EXP (0x8 * sz) = 0x0)` ASSUME_TAC THENL
  [ REWRITE_TAC[EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  IMP_REWRITE_TAC[DIV_MULT_ADD] THEN
  SUBGOAL_THEN `read (bytes (pt_ptr,sz)) (read memory s) < 0x2 EXP (0x8 * sz)` ASSUME_TAC THENL
  [ REWRITE_TAC[READ_BYTES_BOUND]; ALL_TAC] THEN
  SUBGOAL_THEN `num_of_bytelist (SUB_LIST (0x0,sz) x) < 0x2 EXP (0x8 * sz)` ASSUME_TAC THENL
  [ MP_TAC (SPEC `(SUB_LIST (0,sz) x:byte list)` NUM_OF_BYTELIST_BOUND) THEN
    IMP_REWRITE_TAC[LENGTH_SUB_LIST; SUB_0; MIN] THEN
    SUBGOAL_THEN `256 EXP sz = 2 EXP (8 * sz)` SUBST1_TAC THENL
    [ REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP]; ALL_TAC] THEN SIMP_TAC[]; ALL_TAC] THEN
  IMP_REWRITE_TAC[DIV_LT; ADD] THEN
  DISCH_TAC THEN

  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  IMP_REWRITE_TAC[VAL_OF_BYTES_TO_INT128_EQ_NUM_OF_BYTELIST] THEN
  REWRITE_TAC[LENGTH_SUB_LIST; MIN] THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_128] THEN
  SUBGOAL_THEN `num_of_bytelist (SUB_LIST (sz,0x10) x) < 2 EXP 0x80` ASSUME_TAC THENL
  [ MP_TAC (SPEC `(SUB_LIST (sz,0x10) x:byte list)` NUM_OF_BYTELIST_BOUND) THEN
    IMP_REWRITE_TAC[LENGTH_SUB_LIST; SUB_0; MIN] THEN
    ARITH_TAC; ALL_TAC] THEN
  IMP_REWRITE_TAC[MOD_LT]
);;


let DIVISION_BY_80_LEMMA = prove(
  `!(a:num) b. a DIV 0x50 = b /\
    0x10 divides a /\
    ~(a - b * 0x50 = 0x10) /\
    ~(a - b * 0x50 = 0x20) /\
    ~(a - b * 0x50 = 0x30) /\
    ~(a - b * 0x50 = 0x40) ==>
    b * 0x50 = a`,
  REPEAT STRIP_TAC THEN
  (* Use the division theorem: a = b * 0x50 + (a MOD 0x50) *)
  MP_TAC (SPECL [`a:num`; `0x50`] DIVISION) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN

  (* We have a = b * 0x50 + (a MOD 0x50) and a DIV 0x50 = b *)
  SUBGOAL_THEN `a = b * 0x50 + (a MOD 0x50)` ASSUME_TAC THENL [
    ASM_ARITH_TAC; ALL_TAC] THEN

  (* Show that a MOD 0x50 = 0 by case analysis *)
  SUBGOAL_THEN `a MOD 0x50 = 0` ASSUME_TAC THENL [
    (* Since 0x10 divides a, we know a = k * 0x10 for some k *)
    UNDISCH_TAC `0x10 divides a` THEN
    REWRITE_TAC[divides] THEN
    STRIP_TAC THEN

    (* The remainder a MOD 0x50 must be a multiple of 0x10 and < 0x50 *)
    (* So it's one of: 0, 0x10, 0x20, 0x30, 0x40 *)
    SUBGOAL_THEN `(a MOD 0x50 = 0) \/ (a MOD 0x50 = 0x10) \/
                  (a MOD 0x50 = 0x20) \/ (a MOD 0x50 = 0x30) \/
                  (a MOD 0x50 = 0x40)` ASSUME_TAC THENL
    [ ASM_REWRITE_TAC[] THEN

      SUBGOAL_THEN `(0x10 * x) MOD 0x50 = (x MOD 5) * 0x10` SUBST1_TAC THENL [
        SUBGOAL_THEN `0x50 = 5 * 0x10` SUBST1_TAC THENL [
          CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
        MP_TAC (SPECL [`0x10 * x`; `0x10`; `5`] MOD_MULT_MOD) THEN
        REWRITE_TAC[MOD_MULT; ADD_CLAUSES] THEN
        IMP_REWRITE_TAC[DIV_MULT] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        SIMP_TAC[] THEN DISCH_TAC THEN
        REWRITE_TAC[MULT_SYM]
        ; ALL_TAC] THEN

      SUBGOAL_THEN `x MOD 5 < 5` ASSUME_TAC THENL [
        REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
      SUBGOAL_THEN `x MOD 5 = 0 \/ x MOD 5 = 1 \/ x MOD 5 = 2 \/ x MOD 5 = 3 \/ x MOD 5 = 4` ASSUME_TAC THENL [
        UNDISCH_TAC `x MOD 0x5 < 0x5` THEN ARITH_TAC ; ALL_TAC] THEN

      REPEAT (FIRST_X_ASSUM DISJ_CASES_TAC) THENL
      [ ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV]
      ; ALL_TAC] THEN

    (* Now eliminate the non-zero cases using the assumptions *)
    SUBGOAL_THEN `~(a MOD 0x50 = 0x10)` ASSUME_TAC THENL
    [ UNDISCH_TAC `~(a - b * 0x50 = 0x10)` THEN
      UNDISCH_TAC `a = b * 0x50 + a MOD 0x50` THEN
      ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(a MOD 0x50 = 0x20)` ASSUME_TAC THENL
    [ UNDISCH_TAC `~(a - b * 0x50 = 0x20)` THEN
      UNDISCH_TAC `a = b * 0x50 + a MOD 0x50` THEN
      ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(a MOD 0x50 = 0x30)` ASSUME_TAC THENL
    [ UNDISCH_TAC `~(a - b * 0x50 = 0x30)` THEN
      UNDISCH_TAC `a = b * 0x50 + a MOD 0x50` THEN
      ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(a MOD 0x50 = 0x40)` ASSUME_TAC THENL
    [ UNDISCH_TAC `~(a - b * 0x50 = 0x40)` THEN
      UNDISCH_TAC `a = b * 0x50 + a MOD 0x50` THEN
      ARITH_TAC; ALL_TAC] THEN

    ASM_MESON_TAC[]; ALL_TAC
  ] THEN

  (* Finally conclude b * 0x50 = a *)
  ASM_ARITH_TAC
);;


let NUM_BLOCKS_TO_VAL = prove(
  `!(len:int64). word_and len (word 0xfffffffffffffff0) = word (16 * (val len DIV 16))`,
  GEN_TAC THEN
  REWRITE_TAC[WORD_AND_MASK16] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `16 * val (len:int64) DIV 16 = val len - (val len MOD 16)` SUBST1_TAC THENL
  [REWRITE_TAC[DIVISION_SIMP] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `0xf = 2 EXP 4 - 1`] THEN
  REWRITE_TAC[WORD_AND_MASK_WORD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN

  REWRITE_TAC[VAL_WORD_SUB] THEN
  SUBGOAL_THEN `val (len:int64) >= val ((word (val len MOD 0x10)):int64)` ASSUME_TAC THENL [
    REWRITE_TAC[VAL_WORD; DIMINDEX_64; GE] THEN
    MP_TAC (SPECL [`val (len:int64) MOD 0x10`; `0x2 EXP 0x40`] MOD_LE) THEN
    ARITH_TAC;
    ALL_TAC
  ] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN

  SUBGOAL_THEN `val (len:int64) MOD 0x10 < 0x2 EXP 0x40` ASSUME_TAC THENL
  [ TRANS_TAC LET_TRANS `val (len:int64)` THEN
    REWRITE_TAC[VAL_BOUND_64; MOD_LE]; ALL_TAC] THEN

  SUBGOAL_THEN `val (len:int64) MOD 0x10 MOD 0x2 EXP 0x40 = val len MOD 0x10` ASSUME_TAC THENL
  [ MP_TAC (SPECL [`val (len:int64) MOD 0x10`; `0x2 EXP 0x40`] MOD_LT) THEN
    ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN

  MP_TAC (SPECL [`val (len:int64)`; `0x2 EXP 0x40`; `val (len:int64) MOD 0x10`]
    (ARITH_RULE `!a b c. c <= a ==> c <= b ==> a + b - c = (a - c) + b`)) THEN
  ANTS_TAC THENL [ REWRITE_TAC[MOD_LE]; ALL_TAC] THEN
  ANTS_TAC THENL [ ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN

  MP_TAC (SPECL [`1`; `0x2 EXP 0x40`; `val (len:int64) - val len MOD 0x10`]
    (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 MOD_MULT_ADD)))) THEN
  CONV_TAC NUM_REDUCE_CONV
);;

let NUM_BLOCKS_MINUS1_TO_VAL = prove(
  `!(len:int64). val len >= 16 ==>
    word_sub (word_and (len:int64) (word 0xfffffffffffffff0)) (word 0x10) =
    word (16 * (val len DIV 16 - 1))`,
  REWRITE_TAC[NUM_BLOCKS_TO_VAL] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LEFT_SUB_DISTRIB; WORD_SUB] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `0x10 <= 0x10 * val (len:int64) DIV 0x10` ASSUME_TAC THENL
  [ MP_TAC (SPECL [`0x10`; `val (len:int64)`; `1`] LE_RDIV_EQ) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[GSYM GE] THEN
    ASM_SIMP_TAC[] THEN
    ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[]
);;

let BREAK_ONE_BLOCK_INTO_BYTES = prove(
  `!(addr:int64) (s:armstate) (p:int128).
  read (memory :> bytes128 addr) s = p <=>
   (read (memory :> bytes8 addr) s = EL 0 (int128_to_bytes p) /\
    read (memory :> bytes8 (word_add addr (word 1))) s = EL 1 (int128_to_bytes p) /\
    read (memory :> bytes8 (word_add addr (word 2))) s = EL 2 (int128_to_bytes p) /\
    read (memory :> bytes8 (word_add addr (word 3))) s = EL 3 (int128_to_bytes p) /\
    read (memory :> bytes8 (word_add addr (word 4))) s = EL 4 (int128_to_bytes p) /\
    read (memory :> bytes8 (word_add addr (word 5))) s = EL 5 (int128_to_bytes p) /\
    read (memory :> bytes8 (word_add addr (word 6))) s = EL 6 (int128_to_bytes p) /\
    read (memory :> bytes8 (word_add addr (word 7))) s = EL 7 (int128_to_bytes p) /\
    read (memory :> bytes8 (word_add addr (word 8))) s = EL 8 (int128_to_bytes p) /\
    read (memory :> bytes8 (word_add addr (word 9))) s = EL 9 (int128_to_bytes p) /\
    read (memory :> bytes8 (word_add addr (word 10))) s = EL 10 (int128_to_bytes p) /\
    read (memory :> bytes8 (word_add addr (word 11))) s = EL 11 (int128_to_bytes p) /\
    read (memory :> bytes8 (word_add addr (word 12))) s = EL 12 (int128_to_bytes p) /\
    read (memory :> bytes8 (word_add addr (word 13))) s = EL 13 (int128_to_bytes p) /\
    read (memory :> bytes8 (word_add addr (word 14))) s = EL 14 (int128_to_bytes p) /\
    read (memory :> bytes8 (word_add addr (word 15))) s = EL 15 (int128_to_bytes p))
   `,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL[
    STRIP_TAC THEN
    MP_TAC (SPECL [`0:num`; `addr:int64`; `s:armstate`] BYTES128_TO_BYTES8_THM) THEN
    REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    REWRITE_TAC[int128_to_bytes] THEN
    REWRITE_TAC EL_16_8_CLAUSES THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[bytes_to_int128] THEN
    REWRITE_TAC EL_16_8_CLAUSES THEN
    REWRITE_TAC[WORD_ADD_0] THEN
    ABBREV_TAC `x0 = read (memory :> bytes8 (addr:int64)) s` THEN
    ABBREV_TAC `x1 = read (memory :> bytes8 (word_add (addr:int64) (word 0x1))) s` THEN
    ABBREV_TAC `x2 = read (memory :> bytes8 (word_add (addr:int64) (word 0x2))) s` THEN
    ABBREV_TAC `x3 = read (memory :> bytes8 (word_add (addr:int64) (word 0x3))) s` THEN
    ABBREV_TAC `x4 = read (memory :> bytes8 (word_add (addr:int64) (word 0x4))) s` THEN
    ABBREV_TAC `x5 = read (memory :> bytes8 (word_add (addr:int64) (word 0x5))) s` THEN
    ABBREV_TAC `x6 = read (memory :> bytes8 (word_add (addr:int64) (word 0x6))) s` THEN
    ABBREV_TAC `x7 = read (memory :> bytes8 (word_add (addr:int64) (word 0x7))) s` THEN
    ABBREV_TAC `x8 = read (memory :> bytes8 (word_add (addr:int64) (word 0x8))) s` THEN
    ABBREV_TAC `x9 = read (memory :> bytes8 (word_add (addr:int64) (word 0x9))) s` THEN
    ABBREV_TAC `xa = read (memory :> bytes8 (word_add (addr:int64) (word 0xa))) s` THEN
    ABBREV_TAC `xb = read (memory :> bytes8 (word_add (addr:int64) (word 0xb))) s` THEN
    ABBREV_TAC `xc = read (memory :> bytes8 (word_add (addr:int64) (word 0xc))) s` THEN
    ABBREV_TAC `xd = read (memory :> bytes8 (word_add (addr:int64) (word 0xd))) s` THEN
    ABBREV_TAC `xe = read (memory :> bytes8 (word_add (addr:int64) (word 0xe))) s` THEN
    ABBREV_TAC `xf = read (memory :> bytes8 (word_add (addr:int64) (word 0xf))) s` THEN
    REPEAT STRIP_TAC THEN
    REPEAT BITBLAST_TAC; ALL_TAC] THEN

  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`0:num`; `addr:int64`; `s:armstate`] BYTES128_TO_BYTES8_THM) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[int128_to_bytes] THEN
  REWRITE_TAC EL_16_8_CLAUSES THEN
  REWRITE_TAC[bytes_to_int128] THEN
  REWRITE_TAC EL_16_8_CLAUSES THEN
  BITBLAST_TAC
);;

let SELECT_ONE_BYTE_FROM_BLOCK = prove(
  `!(addr:int64) (off:int64) (s:armstate) (p:int128).
  read (memory :> bytes128 addr) s = p ==>
  val off < 16 ==>
  read (memory :> bytes8 (word_add addr off)) s = EL (val off) (int128_to_bytes p)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM (STRIP_ASSUME_TAC o
    MATCH_MP (fst (EQ_IMP_RULE
      (SPECL [`addr:int64`; `s:armstate`; `p:int128`] BREAK_ONE_BLOCK_INTO_BYTES)))) THEN
  SUBGOAL_THEN `word_add addr (off:int64) = word_add addr (word (val off))` SUBST1_TAC THENL
  [REWRITE_TAC[WORD_VAL]; ALL_TAC] THEN
  UNDISCH_TAC `val (off:int64) < 16` THEN
  SPEC_TAC (`val (off:int64)`, `n:num`) THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  ASM_REWRITE_TAC[WORD_ADD_0]
);;

let SELECT_ONE_BYTE_FROM_FORALL = prove(
  `!(ptr:int64) (len:int64) (addr:int64) (bl:byte list) (s:armstate).
    (forall j. j < val len ==> read (memory :> bytes8 (word_add ptr (word j))) s = EL j bl) ==>
    val addr < val len ==>
    LENGTH bl = val len ==>
    read (memory :> bytes8 (word_add ptr addr)) s = EL (val addr) bl`,
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `val (addr:int64)`) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WORD_VAL]
);;

let IVAL_WORD_LT = prove(
  `!i. i < 2 EXP 63 ==> ival ((word i):int64) = &i`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ival; DIMINDEX_64; ARITH_RULE `64 - 1 = 63`] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `i < 2 EXP 64` ASSUME_TAC THENL
  [ TRANS_TAC LT_TRANS `2 EXP 63` THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT]
);;

let READ_LT_2BLOCK = prove(
  `!(ptr:int64) (len:int64) (bl:byte list) (s:armstate).
    LENGTH bl = val len ==>
    val len >= 0x10 ==>
    val len < 0x20 ==>
    (forall i. i < val len
      ==> read (memory :> bytes8 (word_add ptr (word i))) s = EL i bl)
    ==> read (memory :> bytes128 ptr) s = bytes_to_int128 (SUB_LIST (0, 16) bl)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`0:num`; `bl:byte list`; `ptr:int64`;
    `len:int64`; `s:armstate`] BYTE_LIST_AT_1BLOCKS) THEN
  REWRITE_TAC[byte_list_at] THEN
  ANTS_TAC THENL[ ASM_SIMP_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL[ ASM_SIMP_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL[ ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[WORD_ADD_0]
);;

let READ_LT_3BLOCK = prove(
  `!(ptr:int64) (len:int64) (bl:byte list) (s:armstate).
  LENGTH bl = val len ==>
  ~(val len < 0x20) ==>
  val len < 0x30 ==>
  (forall i. i < val len
    ==> read (memory :> bytes8 (word_add ptr (word i))) s = EL i bl)
  ==> read (memory :> bytes128 ptr) s = bytes_to_int128 (SUB_LIST (0, 16) bl) /\
      read (memory :> bytes128 (word_add ptr (word 16))) s =
        bytes_to_int128 (SUB_LIST (16, 16) bl)`,
  REPEAT GEN_TAC THEN REPEAT_N 4 STRIP_TAC THEN
  MP_TAC (SPECL [`0:num`; `bl:byte list`; `ptr:int64`;
    `len:int64`; `s:armstate`] BYTE_LIST_AT_2BLOCKS) THEN
  REWRITE_TAC[byte_list_at] THEN
  ANTS_TAC THENL[ ASM_SIMP_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL[ ASM_SIMP_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL[ ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[WORD_ADD_0]
);;

let READ_LT_4BLOCK = prove(
  `!(ptr:int64) (len:int64) (bl:byte list) (s:armstate).
  LENGTH bl = val len ==>
  ~(val len < 0x30) ==>
  val len < 0x40 ==>
  (forall i. i < val len
    ==> read (memory :> bytes8 (word_add ptr (word i))) s = EL i bl)
  ==> read (memory :> bytes128 ptr) s = bytes_to_int128 (SUB_LIST (0, 16) bl) /\
      read (memory :> bytes128 (word_add ptr (word 16))) s =
        bytes_to_int128 (SUB_LIST (16, 16) bl) /\
      read (memory :> bytes128 (word_add ptr (word 32))) s =
        bytes_to_int128 (SUB_LIST (32, 16) bl)`,
  REPEAT GEN_TAC THEN REPEAT_N 4 STRIP_TAC THEN
  MP_TAC (SPECL [`0:num`; `bl:byte list`; `ptr:int64`;
    `len:int64`; `s:armstate`] BYTE_LIST_AT_3BLOCKS) THEN
  REWRITE_TAC[byte_list_at] THEN
  ANTS_TAC THENL[ ASM_SIMP_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL[ ASM_SIMP_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL[ ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[WORD_ADD_0]
);;

let READ_LT_5BLOCK = prove(
  `!(ptr:int64) (len:int64) (bl:byte list) (s:armstate).
  LENGTH bl = val len ==>
  ~(val len < 0x40) ==>
  val len < 0x50 ==>
  (forall i. i < val len
    ==> read (memory :> bytes8 (word_add ptr (word i))) s = EL i bl)
  ==> read (memory :> bytes128 ptr) s = bytes_to_int128 (SUB_LIST (0, 16) bl) /\
      read (memory :> bytes128 (word_add ptr (word 16))) s =
        bytes_to_int128 (SUB_LIST (16, 16) bl) /\
      read (memory :> bytes128 (word_add ptr (word 32))) s =
        bytes_to_int128 (SUB_LIST (32, 16) bl) /\
      read (memory :> bytes128 (word_add ptr (word 48))) s =
        bytes_to_int128 (SUB_LIST (48, 16) bl)`,
  REPEAT GEN_TAC THEN REPEAT_N 4 STRIP_TAC THEN
  MP_TAC (SPECL [`0:num`; `bl:byte list`; `ptr:int64`;
    `len:int64`; `s:armstate`] BYTE_LIST_AT_4BLOCKS) THEN
  REWRITE_TAC[byte_list_at] THEN
  ANTS_TAC THENL[ ASM_SIMP_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL[ ASM_SIMP_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL[ ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[WORD_ADD_0]
);;

let READ_LT_6BLOCK = prove(
  `!(ptr:int64) (len:int64) (bl:byte list) (s:armstate).
  LENGTH bl = val len ==>
  ~(val len < 0x50) ==>
  val len < 0x60 ==>
  (forall i. i < val len
    ==> read (memory :> bytes8 (word_add ptr (word i))) s = EL i bl)
  ==> read (memory :> bytes128 ptr) s = bytes_to_int128 (SUB_LIST (0, 16) bl) /\
      read (memory :> bytes128 (word_add ptr (word 16))) s =
        bytes_to_int128 (SUB_LIST (16, 16) bl) /\
      read (memory :> bytes128 (word_add ptr (word 32))) s =
        bytes_to_int128 (SUB_LIST (32, 16) bl) /\
      read (memory :> bytes128 (word_add ptr (word 48))) s =
        bytes_to_int128 (SUB_LIST (48, 16) bl) /\
      read (memory :> bytes128 (word_add ptr (word 64))) s =
        bytes_to_int128 (SUB_LIST (64, 16) bl)`,
  REPEAT GEN_TAC THEN REPEAT_N 4 STRIP_TAC THEN
  MP_TAC (SPECL [`0:num`; `bl:byte list`; `ptr:int64`;
    `len:int64`; `s:armstate`] BYTE_LIST_AT_5BLOCKS) THEN
  REWRITE_TAC[byte_list_at] THEN
  ANTS_TAC THENL[ ASM_SIMP_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL[ ASM_SIMP_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL[ ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[WORD_ADD_0]
);;


(**********************************************************************)
(**              Common Spec function lemmas                         **)

let INT128_TO_BYTES_OF_BYTES_TO_INT128 = prove(
  `!x. LENGTH x = 16 ==> int128_to_bytes (bytes_to_int128 x) = x`,
  REPEAT STRIP_TAC THEN
  MP_TAC ((GEN_REWRITE_CONV I [LENGTH_EQ_LIST_OF_SEQ] THENC
   RAND_CONV LIST_OF_SEQ_CONV) `LENGTH (x:byte list) = 16`) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN (fun th -> ONCE_REWRITE_TAC[th]) THEN
  REWRITE_TAC[bytes_to_int128] THEN
  REWRITE_TAC EL_16_8_CLAUSES THEN
  REWRITE_TAC[int128_to_bytes] THEN
  REWRITE_TAC[CONS_11] THEN
  REPEAT (CONJ_TAC THEN BITBLAST_TAC)
);;

let LENGTH_OF_INT128_TO_BYTES = prove(
  `!x. LENGTH(int128_to_bytes x) = 16`,
  STRIP_TAC THEN
  REWRITE_TAC[int128_to_bytes] THEN
  REWRITE_TAC[LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV
);;

let SUB_LIST_OF_INT128_TO_BYTES = prove(
  `!x. SUB_LIST (0, 16) (int128_to_bytes x) = int128_to_bytes x`,
  GEN_TAC THEN
  MP_TAC (SPEC `x:int128` LENGTH_OF_INT128_TO_BYTES) THEN
  DISCH_TAC THEN
  IMP_REWRITE_TAC[SUB_LIST_LENGTH_IMPLIES]
);;

let ELEM_TAC i =
  CONV_TAC (RAND_CONV (REWRITE_CONV [num_CONV i])) THEN
  REWRITE_TAC[bytelist_of_num] THEN
  REWRITE_TAC[CONS_11] THEN
  CONJ_TAC THENL [
    REWRITE_TAC[word_subword] THEN
    AP_TERM_TAC THEN
    (ARITH_TAC ORELSE
      ( ASM_REWRITE_TAC[CONJUNCT1 EXP; DIV_1; DIV_DIV] THEN
        CONV_TAC NUM_REDUCE_CONV)); ALL_TAC];;

let INT128_TO_BYTES_EQ_BYTELIST_OF_NUM = prove(
  `!x. int128_to_bytes x = bytelist_of_num 16 (val x)`,
  GEN_TAC THEN
  REWRITE_TAC[int128_to_bytes] THEN

  MAP_EVERY (fun i -> ELEM_TAC (mk_numeral (num i))) (List.rev (2 -- 16)) THEN
  CONV_TAC (RAND_CONV (REWRITE_CONV [num_CONV `1`])) THEN
  REWRITE_TAC[bytelist_of_num] THEN
  REWRITE_TAC[CONS_11] THEN
  REWRITE_TAC[word_subword] THEN
  AP_TERM_TAC THEN
  ASM_REWRITE_TAC[DIV_DIV] THEN
  CONV_TAC NUM_REDUCE_CONV
);;

let NUM_OF_BYTELIST_OF_INT128_TO_BYTES = prove(
  `!x. num_of_bytelist (int128_to_bytes x) = val x`,
  GEN_TAC THEN
  REWRITE_TAC[INT128_TO_BYTES_EQ_BYTELIST_OF_NUM] THEN
  REWRITE_TAC[NUM_OF_BYTELIST_OF_NUM] THEN
  SUBGOAL_THEN `val (x:int128) < 2 EXP 128` ASSUME_TAC THENL
  [ MP_TAC (ISPEC `x:int128` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_128] THEN
    ARITH_TAC; ALL_TAC
  ] THEN
  IMP_REWRITE_TAC[MOD_LT] THEN
  ASM_ARITH_TAC
);;

let BYTES_TO_INT128_OF_INT128_TO_BYTES = prove(
  `!x. bytes_to_int128 (int128_to_bytes x) = x`,
  GEN_TAC THEN
  REWRITE_TAC[int128_to_bytes; bytes_to_int128] THEN
  REWRITE_TAC EL_16_8_CLAUSES THEN
  BITBLAST_TAC
);;

let CALCULATE_TWEAK_EXPAND = prove(
  `!x iv key.
    GF_128_mult_by_primitive (calculate_tweak x iv key) =
    calculate_tweak (x + 0x1) iv key`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `x + 1 = SUC x`] THEN
  CONV_TAC (RAND_CONV (REWRITE_CONV[CONJUNCT2 calculate_tweak])) THEN
  REFL_TAC
);;

let VALUE_OF_ACC_LEN = prove(
  `!(i:int64) (len:int64).
    val i * 0x50 <= val len ==>
    val len DIV 0x50 = val i ==>
    0x10 divides val len ==>
    acc_len i len = val len`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[acc_len] THEN
  REPEAT COND_CASES_TAC THENL
  [
    ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `!a. 0x50 * a = a * 0x50`] THEN
    SUBGOAL_THEN `val (i:int64) * 0x50 = val (len:int64)` ASSUME_TAC THENL
    [ MATCH_MP_TAC (SPECL [`val (len:int64)`; `val (i:int64)`] DIVISION_BY_80_LEMMA) THEN
      REPEAT CONJ_TAC THENL
      [
        ASM_SIMP_TAC[];
        ASM_SIMP_TAC[];
        UNDISCH_TAC `~(val (i:int64) * 0x50 + 0x10 = val (len:int64))` THEN
        UNDISCH_TAC `val (i:int64) * 0x50 <= val (len:int64)` THEN
        ARITH_TAC;
        UNDISCH_TAC `~(val (i:int64) * 0x50 + 0x20 = val (len:int64))` THEN
        UNDISCH_TAC `val (i:int64) * 0x50 <= val (len:int64)` THEN
        ARITH_TAC;
        UNDISCH_TAC `~(val (i:int64) * 0x50 + 0x30 = val (len:int64))` THEN
        UNDISCH_TAC `val (i:int64) * 0x50 <= val (len:int64)` THEN
        ARITH_TAC;
        UNDISCH_TAC `~(val (i:int64) * 0x50 + 0x40 = val (len:int64))` THEN
        UNDISCH_TAC `val (i:int64) * 0x50 <= val (len:int64)` THEN
        ARITH_TAC
      ]; ALL_TAC] THEN
    ASM_ARITH_TAC
  ]
);;

let BOUND_OF_ACC_LEN = prove(
  `!(i:int64) (len:int64) x.
      val i * 0x50 <= val len ==>
      val len DIV 0x50 = val i ==>
      0x10 divides val len ==>
      val len < x ==> acc_len i len < x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `acc_len i len = val (len:int64)` ASSUME_TAC THENL
  [ MP_TAC (SPECL [`i:int64`; `len:int64`] VALUE_OF_ACC_LEN) THEN
    ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_ARITH_TAC
);;


(* In the cipher-stealing loop invariant, all bytes remain the same between iterations
   except the current byte i, which is from the corresponding location i in the tail of pt *)
let CIPHER_STEALING_BYTE_EQUAL = prove(
  `!(i:num) (curr_len:num) (tail_len:int64) (PP:int128) (ct:byte list).
  i < val tail_len /\ val tail_len < 16 ==>
  curr_len + 16 + val tail_len = LENGTH ct ==>
  let InvPP = cipher_stealing_inv (i + 1) curr_len (val tail_len) PP ct
  and InvPP' = cipher_stealing_inv i curr_len (val tail_len) PP ct in
  (!j. 0 <= j /\ j < 16 /\ ~(j = i) ==> EL j (int128_to_bytes InvPP) = EL j (int128_to_bytes InvPP')) /\
  EL i (int128_to_bytes InvPP') = word_zx (EL (curr_len + 16 + i) ct)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  CONJ_TAC THENL
  [
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[cipher_stealing_inv] THEN
    IMP_REWRITE_TAC[INT128_TO_BYTES_OF_BYTES_TO_INT128] THEN
    REPEAT CONJ_TAC THENL
    [
      (* Three cases: 0 <= j < i, i < j < val tail_len, val tail_len <= j < 16 *)
      ASM_CASES_TAC `j < i` THENL
      [
        SUBGOAL_THEN `j < LENGTH (SUB_LIST (0x0,i + 0x1) (int128_to_bytes PP))` ASSUME_TAC THENL
        [ REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
          ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `j < LENGTH (SUB_LIST (0x0,i) (int128_to_bytes PP))` ASSUME_TAC THENL
        [ REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
          ASM_ARITH_TAC ; ALL_TAC] THEN
        REWRITE_TAC[EL_APPEND] THEN
        ASM_SIMP_TAC[] THEN
        MP_TAC (ISPECL [`j:num`; `i:num`; `(int128_to_bytes PP):byte list`] EL_SUB_LIST) THEN
        ANTS_TAC THENL
        [ REWRITE_TAC[LENGTH_OF_INT128_TO_BYTES] THEN
          ASM_ARITH_TAC; ALL_TAC ] THEN
        MP_TAC (ISPECL [`j:num`; `(i + 1):num`; `(int128_to_bytes PP):byte list`] EL_SUB_LIST) THEN
        ANTS_TAC THENL
        [ REWRITE_TAC[LENGTH_OF_INT128_TO_BYTES] THEN
          ASM_ARITH_TAC; ALL_TAC ] THEN
        SIMP_TAC[]; ALL_TAC
      ] THEN
      ASM_CASES_TAC `j < val (tail_len:int64)` THENL
      [
        SUBGOAL_THEN `j > i` ASSUME_TAC THENL[ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[EL_APPEND] THEN
        SUBGOAL_THEN `LENGTH (SUB_LIST (0x0,i + 0x1) (int128_to_bytes PP)) = i + 1` SUBST1_TAC THENL
        [ REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
          ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `LENGTH (SUB_LIST (0x0,i) (int128_to_bytes PP)) = i` SUBST1_TAC THENL
        [ REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
          ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `LENGTH (SUB_LIST (i + 0x1,val (tail_len:int64) - (i + 0x1))
                                (SUB_LIST (curr_len + 0x10,val tail_len) (ct:byte list)))
                        = val tail_len - (i + 1)` SUBST1_TAC THENL
        [ REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
          ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `LENGTH (SUB_LIST (i,val (tail_len:int64) - i)
                              (SUB_LIST (curr_len + 0x10,val tail_len) (ct:byte list)))
                        = val tail_len - i` SUBST1_TAC THENL
        [ REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
          ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `~(j < i)` ASSUME_TAC THENL
        [ ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `~(j < i + 1)` ASSUME_TAC THENL
        [ ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `j - i < val (tail_len:int64) - i` ASSUME_TAC THENL
        [ ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `j - (i + 1) < val (tail_len:int64) - (i + 1)` ASSUME_TAC THENL
        [ ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[] THEN
        MP_TAC (ISPECL [`(j - i):num`; `i:num`;
          `(SUB_LIST (curr_len + 16,val (tail_len:int64)) (ct:byte list)):byte list`;
          `(val (tail_len:int64) - i):num`] EL_SUB_LIST_SHIFT) THEN
        ASM_SIMP_TAC[] THEN
        ANTS_TAC THENL [ REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        IMP_REWRITE_TAC[ARITH_RULE `!i j. j > i ==> j - i - 1 = j - (i + 1)`] THEN
        ASM_ARITH_TAC; ALL_TAC
      ] THEN
      (* j >= val tail_len *)
      REWRITE_TAC[EL_APPEND] THEN
      SUBGOAL_THEN `LENGTH (SUB_LIST (0x0,i + 0x1) (int128_to_bytes PP)) = i + 1` SUBST1_TAC THENL
      [ REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
        ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `LENGTH (SUB_LIST (0x0,i) (int128_to_bytes PP)) = i` SUBST1_TAC THENL
      [ REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
        ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `LENGTH (SUB_LIST (i + 0x1,val (tail_len:int64) - (i + 0x1))
                              (SUB_LIST (curr_len + 0x10,val tail_len) (ct:byte list)))
                      = val tail_len - (i + 1)` SUBST1_TAC THENL
      [ REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
        ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `LENGTH (SUB_LIST (i,val (tail_len:int64) - i)
                            (SUB_LIST (curr_len + 0x10,val tail_len) (ct:byte list)))
                      = val tail_len - i` SUBST1_TAC THENL
      [ REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
        ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(j < i)` ASSUME_TAC THENL
      [ ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(j < i + 1)` ASSUME_TAC THENL
      [ ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(j - i < val (tail_len:int64) - i)` ASSUME_TAC THENL
      [ ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(j - (i + 1) < val (tail_len:int64) - (i + 1))` ASSUME_TAC THENL
      [ ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      ASM_ARITH_TAC;

      REWRITE_TAC[LENGTH_APPEND] THEN
      REWRITE_TAC[LENGTH_SUB_LIST] THEN
      REWRITE_TAC[LENGTH_OF_INT128_TO_BYTES] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      IMP_REWRITE_TAC[ARITH_RULE `i < 16 ==> MIN i 16 = i`] THEN
      SUBGOAL_THEN `LENGTH (ct:byte list) - (curr_len + 16) = val (tail_len:int64)` SUBST1_TAC THENL
      [ ASM_ARITH_TAC; ALL_TAC ] THEN
      REWRITE_TAC[ARITH_RULE `!x. MIN x x = x`] THEN
      ASM_ARITH_TAC;

      REWRITE_TAC[LENGTH_APPEND] THEN
      REWRITE_TAC[LENGTH_SUB_LIST] THEN
      REWRITE_TAC[LENGTH_OF_INT128_TO_BYTES] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      IMP_REWRITE_TAC[ARITH_RULE `i < 16 ==> MIN (i + 1) 16 = i + 1`] THEN
      SUBGOAL_THEN `LENGTH (ct:byte list) - (curr_len + 16) = val (tail_len:int64)` SUBST1_TAC THENL
      [ ASM_ARITH_TAC; ALL_TAC ] THEN
      REWRITE_TAC[ARITH_RULE `!x. MIN x x = x`] THEN
      ASM_ARITH_TAC
    ] ; ALL_TAC
  ] THEN

  REWRITE_TAC[cipher_stealing_inv] THEN
  IMP_REWRITE_TAC[INT128_TO_BYTES_OF_BYTES_TO_INT128] THEN
  CONJ_TAC THENL [
    REWRITE_TAC[EL_APPEND] THEN
    SUBGOAL_THEN `LENGTH (SUB_LIST (0x0,i) (int128_to_bytes PP)) = i` SUBST1_TAC THENL
    [ REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `LENGTH (SUB_LIST (i,val (tail_len:int64) - i)
                          (SUB_LIST (curr_len + 0x10,val tail_len) (ct:byte list)))
                    = val tail_len - i` SUBST1_TAC THENL
    [ REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[ARITH_RULE `~(i < i)`; SUB_REFL] THEN
    SUBGOAL_THEN `0 < val (tail_len:int64) - i` ASSUME_TAC THENL
    [ ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC (ISPECL [`curr_len + 0x10:num`; `i:num`; `ct:byte list`;
      `val (tail_len:int64) - i:num`; `val (tail_len:int64)`] SUB_LIST_MIN_GENERAL) THEN
    REWRITE_TAC[ARITH_RULE `!a. MIN a a = a`; GSYM ADD_ASSOC] THEN
    DISCH_THEN (fun th -> (REWRITE_TAC [th])) THEN
    REWRITE_TAC[WORD_ZX_TRIVIAL; EL] THEN
    MATCH_MP_TAC HD_SUB_LIST_CONS_GENERAL THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LENGTH_APPEND] THEN
  REWRITE_TAC[LENGTH_SUB_LIST] THEN
  REWRITE_TAC[LENGTH_OF_INT128_TO_BYTES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_ARITH_TAC
);;

let CIPHER_STEALING_INV_SELECT = prove(
 `!(i:num) (curr_len:num) (tail_len:int64) (PP:int128) (ct:byte list).
  i < val tail_len ==> val tail_len < 16 ==>
  curr_len + 16 + (val tail_len) = LENGTH ct ==>
  EL i (int128_to_bytes (cipher_stealing_inv (i + 1) curr_len (val tail_len) PP ct)) =
  EL i (int128_to_bytes PP)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[cipher_stealing_inv] THEN
  IMP_REWRITE_TAC[INT128_TO_BYTES_OF_BYTES_TO_INT128] THEN
  CONJ_TAC THENL [
    SUBGOAL_THEN `LENGTH (SUB_LIST (0x0,i + 1) (int128_to_bytes PP)) <= i + 1` ASSUME_TAC THENL
    [ REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
      ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EL_APPEND] THEN
    SUBGOAL_THEN `i < LENGTH (SUB_LIST (0x0,i + 0x1) (int128_to_bytes PP))` ASSUME_TAC THENL
    [ REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_OF_INT128_TO_BYTES] THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC EL_SUB_LIST THEN
    REWRITE_TAC[LENGTH_OF_INT128_TO_BYTES] THEN
    ASM_ARITH_TAC; ALL_TAC
  ] THEN

  REWRITE_TAC[LENGTH_APPEND] THEN
  REWRITE_TAC[LENGTH_SUB_LIST] THEN
  REWRITE_TAC[LENGTH_OF_INT128_TO_BYTES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  IMP_REWRITE_TAC[ARITH_RULE `i < 16 ==> MIN (i + 1) 16 = i + 1`] THEN
  SUBGOAL_THEN `LENGTH (ct:byte list) - (curr_len + 16) = val (tail_len:int64)` SUBST1_TAC THENL
  [ ASM_ARITH_TAC; ALL_TAC ] THEN
  REWRITE_TAC[ARITH_RULE `!x. MIN x x = x`] THEN
  ASM_ARITH_TAC
);;

let CIPHER_STEALING_INV_SIMP_TAC i =
  ( FIRST_ASSUM (fun th -> MATCH_MP_TAC(SPEC i th)) THEN CONV_TAC NUM_REDUCE_CONV) ORELSE
  ( ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WORD_RULE `!a b. word_add ((word a):int64) (word b) = word (a + b)`] THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    IMP_REWRITE_TAC[WORD_ZX_ZX; WORD_ZX_TRIVIAL] THEN
    REWRITE_TAC[DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
    IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN
    ASM_ARITH_TAC);;

let BREAK_DATA_INTO_PARTS_ENCRYPT = prove(
 `!curr_len (tail_len:int64) (pt_ptr:int64) (s:armstate).
 ((curr_len + 0x10 + val tail_len <= LENGTH bl) /\
  (forall i. i < curr_len
    ==> read (memory :> bytes8 (word_add pt_ptr (word i))) s = EL i bl) /\
  (forall i. i < 16
    ==> read (memory :> bytes8 (word_add (word_add pt_ptr (word curr_len)) (word i))) s =
        EL i (SUB_LIST (curr_len, 16) bl)) /\
  (forall i. i < val tail_len
    ==> read (memory :> bytes8
          (word_add (word_add pt_ptr (word (curr_len + 0x10))) (word i))) s =
        EL i (SUB_LIST (curr_len + 16, val tail_len) bl))) ==>
  forall i.
     i < curr_len + 0x10 + val tail_len
     ==> read (memory :> bytes8 (word_add pt_ptr (word i))) s = EL i bl`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "H")
    (CONJUNCTS_THEN2 (LABEL_TAC "H1")
      (CONJUNCTS_THEN2 (LABEL_TAC "H2") (LABEL_TAC "H3")))) THEN
  REPEAT STRIP_TAC THEN

  ASM_CASES_TAC `i < curr_len` THENL
  [
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC
  ] THEN

  ASM_CASES_TAC `i < curr_len + 16` THENL
  [
    USE_THEN "H2" (fun th -> MP_TAC (SPEC `i - curr_len` th)) THEN
    REMOVE_THEN "H2" (K ALL_TAC) THEN
    SUBGOAL_THEN `(word_add (word_add (pt_ptr:int64) (word curr_len)) (word (i - curr_len)))
      = (word_add pt_ptr (word i))` ASSUME_TAC THENL
    [ REWRITE_TAC[WORD_RULE `word_add (word_add a (word b)) (word c) = word_add a (word (b + c))`] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL[ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[] THEN DISCH_TAC THEN
    IMP_REWRITE_TAC[EL_SUB_LIST_GENERAL] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN

  ASM_CASES_TAC `i < curr_len + 16 + val (tail_len:int64)` THENL
  [
    USE_THEN "H3" (fun th -> MP_TAC (SPEC `i - curr_len - 16` th)) THEN
    REMOVE_THEN "H3" (K ALL_TAC) THEN
    SUBGOAL_THEN `(word_add (word_add (pt_ptr:int64) (word (curr_len + 0x10)))
       (word (i - curr_len - 0x10))) = (word_add pt_ptr (word i))` ASSUME_TAC THENL
    [ REWRITE_TAC[WORD_RULE `word_add (word_add a (word b)) (word c) = word_add a (word (b + c))`] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL[ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[ARITH_RULE `i - curr_len - 16 = i - (curr_len + 16)`] THEN
    IMP_REWRITE_TAC[EL_SUB_LIST_GENERAL] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN

  ASM_ARITH_TAC
);;

let BREAK_DATA_INTO_PARTS_DECRYPT = prove(
 `!curr_len (tail_len:int64) (pt_ptr:int64) (s:armstate).
 ((curr_len + 0x10 + val tail_len <= LENGTH bl) /\
  (forall i. i < curr_len
    ==> read (memory :> bytes8 (word_add pt_ptr (word i))) s = EL i bl) /\
  (forall i. i < 16
    ==> read (memory :> bytes8 (word_add (word_add pt_ptr (word curr_len)) (word i))) s =
        EL i (SUB_LIST (curr_len, 16 + val tail_len) bl)) /\
  (forall i. i < val tail_len
    ==> read (memory :> bytes8
          (word_add (word_add pt_ptr (word (curr_len + 0x10))) (word i))) s =
        EL i (SUB_LIST (curr_len + 16, val tail_len) bl))) ==>
  forall i.
     i < curr_len + 0x10 + val tail_len
     ==> read (memory :> bytes8 (word_add pt_ptr (word i))) s = EL i bl`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "H")
    (CONJUNCTS_THEN2 (LABEL_TAC "H1")
      (CONJUNCTS_THEN2 (LABEL_TAC "H2") (LABEL_TAC "H3")))) THEN
  REPEAT STRIP_TAC THEN

  ASM_CASES_TAC `i < curr_len` THENL
  [
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC
  ] THEN

  ASM_CASES_TAC `i < curr_len + 16` THENL
  [
    USE_THEN "H2" (fun th -> MP_TAC (SPEC `i - curr_len` th)) THEN
    REMOVE_THEN "H2" (K ALL_TAC) THEN
    SUBGOAL_THEN `(word_add (word_add (pt_ptr:int64) (word curr_len)) (word (i - curr_len)))
      = (word_add pt_ptr (word i))` ASSUME_TAC THENL
    [ REWRITE_TAC[WORD_RULE `word_add (word_add a (word b)) (word c) = word_add a (word (b + c))`] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL[ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[] THEN DISCH_TAC THEN
    IMP_REWRITE_TAC[EL_SUB_LIST_GENERAL] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN

  ASM_CASES_TAC `i < curr_len + 16 + val (tail_len:int64)` THENL
  [
    USE_THEN "H3" (fun th -> MP_TAC (SPEC `i - curr_len - 16` th)) THEN
    REMOVE_THEN "H3" (K ALL_TAC) THEN
    SUBGOAL_THEN `(word_add (word_add (pt_ptr:int64) (word (curr_len + 0x10)))
       (word (i - curr_len - 0x10))) = (word_add pt_ptr (word i))` ASSUME_TAC THENL
    [ REWRITE_TAC[WORD_RULE `word_add (word_add a (word b)) (word c) = word_add a (word (b + c))`] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL[ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[ARITH_RULE `i - curr_len - 16 = i - (curr_len + 16)`] THEN
    IMP_REWRITE_TAC[EL_SUB_LIST_GENERAL] THEN
    ASM_ARITH_TAC;
    ALL_TAC
  ] THEN

  ASM_ARITH_TAC
);;
