(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* XOR of bytes into a Keccak state: lemmas for the byte loops.              *)
(* In the monolithic gcc 12 -O2 build (see mlkem_native/README.md),          *)
(* mlkem_keccakf1600_xor_bytes has no code of its own: the compiler has      *)
(* inlined it into mlk_keccakf1600x4_xor_bytes_c and mlk_keccak_absorb_once  *)
(* as loops that XOR len bytes of data into the 200-byte state starting at   *)
(* byte off. The proofs of these functions prove each such loop with the     *)
(* specification of mlkem_keccakf1600_xor_bytes of the gcc12_O2 build: the   *)
(* state, as a 1600-bit word S, becomes word_xor S (word(2 EXP (8 * off) *   *)
(* m)) where m is the number that the len bytes of data form. The lemmas     *)
(* here are the ones about numbers and bytes that those proofs share.        *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/libmlkem.ml";;

(* ------------------------------------------------------------------------- *)
(* The state after i of the bytes of the data m have been XORed into it, as  *)
(* bytes. Only byte off + i changes in the next step.                        *)
(* ------------------------------------------------------------------------- *)

let BYTE_UPDATE_STMT =
  `!x c k j.
        x < 2 EXP (8 * k) /\ c < 256
        ==> ((x + 2 EXP (8 * k) * c) DIV 2 EXP (8 * j)) MOD 256 =
            if j = k then c else (x DIV 2 EXP (8 * j)) MOD 256`;;

let BYTE_UPDATE = assume_spec BYTE_UPDATE_STMT;;

let XOR_BYTES_STEP_STMT =
  `!(S:1600 word) m off i j.
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
                  (8 * j,8)`;;

let XOR_BYTES_STEP = assume_spec XOR_BYTES_STEP_STMT;;

(*** The invariant for the bytes other than byte t ***)

let XOR_BYTES_RESTRICT_RULE t th =
  let j,bod = dest_forall(concl th) in
  let p,q = dest_imp bod in
  let p' = mk_conj(p,mk_neg(mk_eq(j,t))) in
  GEN j (DISCH p' (MP (SPEC j th) (CONJUNCT1(ASSUME p'))));;

(* ------------------------------------------------------------------------- *)
(* After the loop, the whole state from its bytes.                           *)
(* ------------------------------------------------------------------------- *)

let XOR_BYTES_FINAL_STMT =
  `!(a:int64) (S:1600 word) off len d m s:armstate.
        off + len <= 200 /\
        read (memory :> bytes(d,len)) s = m /\
        (!j. j < 200
             ==> read (memory :> bytes8(word_add a (word j))) s =
                 word_subword
                  (word_xor S (word(2 EXP (8 * off) * m MOD 2 EXP (8 * len))))
                  (8 * j,8))
        ==> read (memory :> wbytes a) s = word_xor S (word(2 EXP (8 * off) * m))`;;

let XOR_BYTES_FINAL = assume_spec XOR_BYTES_FINAL_STMT;;

(* ------------------------------------------------------------------------- *)
(* The test of a loop that stops at the last index len - 1, which is kept in *)
(* a register, after counting from 0.                                        *)
(* ------------------------------------------------------------------------- *)

let XOR_LAST_FLAG_STMT =
  `!len i. ~(len = 0) /\ i < len /\ len <= 200
           ==> (~(val(word_sub (word (len - 1)) (word i):int64) = 0) <=>
                i + 1 < len)`;;

let XOR_LAST_FLAG = assume_spec XOR_LAST_FLAG_STMT;;

(* ------------------------------------------------------------------------- *)
(* The same as XOR_BYTES_FINAL, with a bound on the data m instead of its    *)
(* bytes in memory. It gives the state after a single byte (len = 1) has     *)
(* been XORed in, e.g. by the code that adds the padding.                    *)
(* ------------------------------------------------------------------------- *)

let XOR_BYTES_FINAL2_STMT =
  `!(a:int64) (S:1600 word) off len m s:armstate.
        off + len <= 200 /\ m < 2 EXP (8 * len) /\
        (!j. j < 200
             ==> read (memory :> bytes8(word_add a (word j))) s =
                 word_subword
                  (word_xor S (word(2 EXP (8 * off) * m MOD 2 EXP (8 * len))))
                  (8 * j,8))
        ==> read (memory :> wbytes a) s = word_xor S (word(2 EXP (8 * off) * m))`;;

let XOR_BYTES_FINAL2 = assume_spec XOR_BYTES_FINAL2_STMT;;

(*** The index of a load or store with a UXTW register offset ***)

let VAL_ZX_UXTW_STMT =
  `!n. n < 4294967296
       ==> val(word_zx(word_zx(word_zx(word n:int64):int32):int32):int64) =
           n /\
           val(word_zx(word_zx(word n:int64):int32):int64) = n`;;

let VAL_ZX_UXTW = assume_spec VAL_ZX_UXTW_STMT;;

(*** The state as bytes, from its 1600-bit word ***)

let XOR_BYTES_OF_STATE_STMT =
  `!(a:int64) (S:1600 word) s:armstate.
        read (memory :> bytes(a,200)) s = val S
        ==> !j. j < 200
                ==> read (memory :> bytes8(word_add a (word j))) s =
                    word_subword S (8 * j,8)`;;

let XOR_BYTES_OF_STATE = assume_spec XOR_BYTES_OF_STATE_STMT;;

(*** Reading a part of a number in memory, and the bytes of a 32-bit value ***)

let READ_MEMORY_BYTES_SUB_STMT =
  `!a:int64 n x k l s:armstate.
        read (memory :> bytes(a,n)) s = x /\ k + l <= n
        ==> read (memory :> bytes(word_add a (word k),l)) s =
            (x DIV 2 EXP (8 * k)) MOD 2 EXP (8 * l)`;;

let READ_MEMORY_BYTES_SUB = assume_spec READ_MEMORY_BYTES_SUB_STMT;;

let WORD_ZX_BYTE_SMALL_STMT =
  `!p. p < 256 ==> word_zx(word_zx(word p:int64):int32):byte = word p`;;

let WORD_ZX_BYTE_SMALL = assume_spec WORD_ZX_BYTE_SMALL_STMT;;

let WORD_ZX_SUB1_SMALL_STMT =
  `!r. 0 < r /\ r < 2 EXP 32
       ==> word_zx (word_sub (word_zx (word r:int64):int32) (word 1)):int64 =
           word(r - 1)`;;

let WORD_ZX_SUB1_SMALL = assume_spec WORD_ZX_SUB1_SMALL_STMT;;

(* ------------------------------------------------------------------------- *)
(* The same lemmas with the events of the loop, for the constant-time and    *)
(* memory safety proofs (the "FULL" form, with the correctness statement     *)
(* and the events together). The events depend on off and len, not on the   *)
(* data. xor_full_stmt states a lemma for the loop of an inlined call, from  *)
(* the label from_lab to the label to_lab, with the registers and the state  *)
(* address given as strings, and xorF_prove proves it for a loop whose head  *)
(* is lab1 and whose exit is lab2, init_n instructions after from_lab and    *)
(* exit_n instructions before to_lab, as the loops of the callers have       *)
(* them. The flag flip tells in which order the loop counter is compared.    *)
(* OFF0_PROVE specializes such a lemma to the offset 0.                      *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let xor_full_stmt from_lab to_lab st_addr pre post regs =
  parse_term (Printf.sprintf
   "exists f_events.
     forall (e:(uarch_event)list) (a:int64) (d:int64) off len (S:1600 word)
            m pc.
        aligned 4096 (word pc:int64) /\\ pc + libmlkem_size <= 2 EXP 64 /\\
        off + len <= 200 /\\ ~(len = 0) /\\
        ALL (nonoverlapping (%s,200)) [(word pc,libmlkem_size); (d,len)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mono_mc /\\
                  read PC s = word (pc + %s) /\\ %s /\\
                  read (memory :> wbytes (%s)) s = S /\\
                  read (memory :> bytes(d,len)) s = m /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\ %s /\\
                  read (memory :> wbytes (%s)) s =
                  word_xor S (word(2 EXP (8 * off) * m)) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a d off len pc /\\
                     memaccess_inbounds e2 [%s,200; d,len] [%s,200]))
             (MAYCHANGE [PC; %s] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(%s,200)])"
   st_addr from_lab pre st_addr to_lab post st_addr st_addr st_addr regs st_addr);;

let xorF_prove exec stmt lab1 lab2 inv_regs init_n exit_n flip =
  let sn = Printf.sprintf "s%d" exit_n in
  let flagtm = if flip then
   "~(val(word_sub (word_add (word i) (word 1)) (word len):int64) = 0) <=> i + 1 < len"
   else "~(val(word_sub (word len) (word_add (word i) (word 1)):int64) = 0) <=> i + 1 < len" in
  prove(stmt,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (d:int64) (off:num) (len:num) (pc:num).
      APPEND
        (f_ev_epil a d off len pc)
        (APPEND
          (ENUMERATEL len (\i. f_ev_loop a d off len pc i))
          (f_ev_prol a d off len pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `d:int64`;
                       `off:num`; `len:num`;
                       `S:1600 word`; `m:num`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL;
              READ_MEMORY_WBYTES_VAL; fst exec] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `len:num` (parse_term ("pc + "^lab1))
   (parse_term ("pc + "^lab2))
   (parse_term (Printf.sprintf
   "\\i s. %s /\\
          read (memory :> bytes(d,len)) s = m /\\
          !j. j < 200
              ==> read (memory :> bytes8(word_add a (word j))) s =
                  word_subword
                   (word_xor (S:1600 word)
                     (word(2 EXP (8 * off) * m MOD 2 EXP (8 * i))))
                   (8 * j,8)" (inv_regs "i"))) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** Entry: only the bytes of the state ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    (if init_n > 0 then
       ARM_STEPS_TAC exec (1--init_n) THEN ARGS_32_TAC [`len:num`]
     else ALL_TAC) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; WORD_XOR_0; word_subword] THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC READ_MEMORY_BYTES8_OF_NUM THEN
      EXISTS_TAC `200` THEN ASM_REWRITE_TAC[];
      DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The loop body, for byte off + i of the state, and the test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN `off + i < 200` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && free_in `bytes8` (concl th) then
        ASSUME_TAC(MP (SPEC `off + i` th) (ASSUME `off + i < 200`)) THEN
        ASSUME_TAC(XOR_BYTES_RESTRICT_RULE `off + i` th)
      else failwith "XOR_BYTES_RESTRICT_RULE") THEN
    MP_TAC(SPECL [`d:int64`; `len:num`; `m:num`; `i:num`; `s0:armstate`]
                 READ_MEMORY_BYTES8_OF_NUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ARM_STEPS_TAC exec (1--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN (parse_term flagtm)
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      SUBGOAL_THEN `len < 2 EXP 64 /\ i + 1 < 2 EXP 64` MP_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[MOD_LT] THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[ADD_SUB; GSYM WORD_ADD] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[XOR_BYTES_STEP] THEN
      COND_CASES_TAC THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
      FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      W(fun (_,w) -> SPEC_TAC(lhand(rand w),`b1:byte`) THEN
                     SPEC_TAC(rand(rand w),`b2:byte`)) THEN
      REPEAT GEN_TAC THEN W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w));
      DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The loop exit, with the whole state ***)

    REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    (if exit_n > 0 then ARM_STEPS_TAC exec (1--exit_n) else ALL_TAC) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    FIRST
     [MP_TAC(ISPECL [`a:int64`; `S:1600 word`; `off:num`; `len:num`;
                     `d:int64`; `m:num`; parse_term (sn^":armstate")]
                    XOR_BYTES_FINAL) THEN
      ASM_REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN NO_TAC;
      DISCHARGE_SAFETY_PROPERTY_TAC;
      ASM_MESON_TAC[]]]);;

(*** The lemma for off = 0, with the shorter list of arguments of the events ***)

let OFF0_PROVE =
  let simps = [WORD_ADD_0; ADD_CLAUSES; EXP; MULT_CLAUSES; MOD_1;
               ARITH_RULE `8 * 0 = 0`] in
  fun th ->
    let fv,body = dest_exists (concl th) in
    let vs,b = strip_forall body in
    let off = find (fun v -> name_of v = "off") vs in
    let vs' = filter (fun v -> v <> off) vs in
    let byname n = find (fun v -> name_of v = n) vs in
    let f0 = mk_var("f_events",`:int64->int64->num->num->(uarch_event)list`) in
    let inst = vsubst [`0`,off] b in
    let t0 = find_term (fun t -> is_comb t && fst(strip_comb t) = fv) inst in
    let new_ev = list_mk_comb(f0,map byname ["a";"d";"len";"pc"]) in
    let inst1 = subst [new_ev,t0] inst in
    let inst2 = rand(concl(REWRITE_CONV simps inst1)) in
    let stmt0 = mk_exists(f0,list_mk_forall(vs',inst2)) in
    let fg = mk_var("fg",type_of fv) in
    prove(stmt0,
      X_CHOOSE_TAC fg th THEN
      EXISTS_TAC (list_mk_abs(map byname ["a";"d";"len";"pc"],
                  list_mk_comb(fg,[byname "a"; byname "d"; `0`; byname "len";
                                   byname "pc"]))) THEN
      MAP_EVERY X_GEN_TAC vs' THEN
      FIRST_X_ASSUM(MP_TAC o SPECL (map (fun v -> if v = off then `0` else v) vs)) THEN
      REWRITE_TAC simps THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC simps);;
