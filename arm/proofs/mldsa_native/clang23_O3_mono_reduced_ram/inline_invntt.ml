(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The loops of the inverse NTT of mldsa-native as clang 23 -O3 has          *)
(* compiled it (mldsa_poly_invntt_tomont): lemmas generated for the          *)
(* registers, constants and addresses of each loop, from its head to its     *)
(* exit, with the correctness and the events. Loops 6 to 12 (layers 3 to 1)  *)
(* do two butterflies per iteration with the zeta in a register: their       *)
(* proofs are those of the forward NTT (inline_ntt.ml) with the butterfly of *)
(* mld_invntt_block. Loop 13 scales the coefficients. Loops 3 to 5 (layers   *)
(* 6 to 4) do one block per iteration with the zeta from the table through a *)
(* pointer that goes down (loop 5 spills to the stack). Loops 1 and 2 are on *)
(* vectors with ld2/st2 and ld4/st4. Lemmas on the blocks of a layer and the *)
(* Montgomery multiplications that the loops need come with them.            *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_ntt.ml";;

let INV_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa_poly_invntt_tomont"];;

(* ------------------------------------------------------------------------- *)
(* The halves of an inverse NTT block.                                       *)
(* ------------------------------------------------------------------------- *)

let INV_BLK_LO = prove
 (`!z m (j:num) start len. start <= j /\ j < start + len
     ==> mld_invntt_block z start len m j =
         word_add (m j) (m (j + len))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[mld_invntt_block]);;

let INV_BLK_HI = prove
 (`!z m (j:num) start len. start + len <= j /\ j < start + 2 * len
     ==> mld_invntt_block z start len m j =
         mld_fqmul (word_sub (m (j - len)) (m j)) z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_invntt_block] THEN
  SUBGOAL_THEN `~(start <= j /\ j < start + len)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

let INV_INV_EXIT = prove
 (`!(m:num->int32) (mem:num->int32) z start len n.
        2 * n = len /\ start + 2 * len <= 256 /\
        (!j. j < 256
             ==> mem j = (if start <= j /\ j < start + 2 * n \/
                             start + len <= j /\ j < start + len + 2 * n
                          then mld_invntt_block z start len m j else m j))
        ==> !j. j < 256 ==> mem j = mld_invntt_block z start len m j`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[mld_invntt_block] THEN
  SUBGOAL_THEN `~(start <= j /\ j < start + len) /\
                ~(start + len <= j /\ j < start + 2 * len)`
   (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The Montgomery multiplication by the constant z of the difference of two  *)
(* coefficients, as the code computes it (the constant z in a register).     *)
(* ------------------------------------------------------------------------- *)

let INV_TWIST_GEN swap z =
  let zw = ((z mod 4294967296) + 4294967296) mod 4294967296 in
  let zq = (zw * 58728449) mod 4294967296 in
  let c = Num.string_of_num
   (Num.mult_num (Num.num_of_int zq) (Num.power_num (Num.num_of_int 2) (Num.num_of_int 32))) in
  let znum = if z >= 0 then Printf.sprintf "&%d" z
             else Printf.sprintf "-- &%d" (-z) in
  let pt s = parse_term s in
  let nt = NTT_TWIST z in
  let qp = Printf.sprintf "word_zx(word_ishr (word (0 + val(word_sx (x:int32):int64) * %s):int64) 32):int32" c in
  prove(pt (Printf.sprintf
   "!x:int32. word_zx(word_ushr (iword(ival(iword(&0 + ival(%s) * -- &8380417):int64) + %s):int64) 32):int32 = mld_fqmul x (word %d)"
   qp (if swap then Printf.sprintf "ival x * (%s)" znum else Printf.sprintf "(%s) * ival x" znum) zw),
   GEN_TAC THEN
   SUBGOAL_THEN (pt (Printf.sprintf
    "ival(iword(&0 + ival(%s) * -- &8380417):int64) + %s =
     ival(iword(&0 + ival(word_zx(word_sx x:int64):int32) * (%s)):int64) + ival(%s) * -- &8380417"
    qp (if swap then Printf.sprintf "ival x * (%s)" znum else Printf.sprintf "(%s) * ival x" znum) znum qp)) SUBST1_TAC THENL
    [MP_TAC(ISPEC (pt qp) IVAL_BOUND) THEN MP_TAC(ISPEC `x:int32` IVAL_BOUND) THEN
     REWRITE_TAC[DIMINDEX_32; WORD_ZX_SX_32_64_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
     REWRITE_TAC[INT_ADD_LID] THEN REPEAT DISCH_TAC THEN
     SUBGOAL_THEN (pt (Printf.sprintf "ival(iword(ival(%s) * -- &8380417):int64) = ival(%s) * -- &8380417" qp qp)) SUBST1_TAC THENL
      [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
       CONV_TAC INT_REDUCE_CONV THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN (pt (Printf.sprintf "ival(iword(ival(x:int32) * (%s)):int64) = ival x * (%s)" znum znum)) SUBST1_TAC THENL
      [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
       CONV_TAC INT_REDUCE_CONV THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
     INT_ARITH_TAC;
     ALL_TAC] THEN
   ACCEPT_TAC(SPEC `x:int32` nt));;

let INV_TWIST z = INV_TWIST_GEN false z;;
let INV_TWIST_SWAP z = INV_TWIST_GEN true z;;

(*** The sign extension of the difference, as the simulator has it ***)

let INV_SXT = prove
 (`!x:int32. word_sxfrom 31 (word_subword (word_zx x:int64) (0,32):int64):int64 =
             word_sx x`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* A loop of two butterflies per iteration with the zeta in registers.       *)
(* ------------------------------------------------------------------------- *)

let inv_dbg = ref false;;
let inv_mk = ref false;;   (* for development: assume the lemmas of the loops *)
let INV_PROVE tm tac = if !inv_mk then mk_thm([],tm) else prove(tm,tac);;

type inv_const_loop =
  { iloop:string; iexit:string; iptr:string; ik0:int; icnt:string;
    istart:int; ilen:int; iz:int; iconsts:(string*string) list; isteps:int;
    ilo0:string; ilo1:string; iup0:string; iup1:string;
    iwsub:(int*int) list; iregs:string list };;

let INV_CLOOP_TERM mc (p:inv_const_loop) =
  let nit = p.ilen / 2 in
  let zw = ((p.iz mod 4294967296) + 4294967296) mod 4294967296 in
  let consts = String.concat " /\\ "
    (map (fun (r,v) -> Printf.sprintf "read %s s = word %s" r v) p.iconsts) in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e a (m:num->int32) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALL (nonoverlapping (a,1024)) [(word pc,libmldsa_size)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read %s s = %s /\\
                  read %s s = word %d /\\ %s /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                           m i) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                           mld_invntt_block (word %d) %d %d m i) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a pc /\\
                     memaccess_inbounds e2 [a,1024] [a,1024]))
             (MAYCHANGE [PC; %s; %s; %s] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a,1024)])"
   mc p.iloop p.iptr (if p.ik0 = 0 then "a" else Printf.sprintf "word_add a (word %d)" p.ik0) p.icnt p.ilen consts p.iexit zw p.istart p.ilen
   p.iptr p.icnt (String.concat "; " p.iregs))
  |> fun t -> ignore nit; t;;

let INV_CLOOP mc exec (p:inv_const_loop) =
  let pt s = parse_term s in
  let nit = p.ilen / 2 in
  let zw = ((p.iz mod 4294967296) + 4294967296) mod 4294967296 in
  let s = p.istart and l = p.ilen in
  let sl = s + l in
  let lo0j = Printf.sprintf "%d + 2 * i" s
  and lo1j = Printf.sprintf "%d + 2 * i + 1" s
  and up0j = Printf.sprintf "%d + %d + 2 * i" s l
  and up1j = Printf.sprintf "%d + %d + 2 * i + 1" s l in
  let cond i = Printf.sprintf "%d <= j /\\ j < %d + 2 * %s \\/ %d + %d <= j /\\ j < %d + %d + 2 * %s" s s i s l s l i in
  let inv = pt (Printf.sprintf
   "\\i s. %s /\\ read %s s = word_add a (word (%d + 8 * i)) /\\
          read %s s = word (%d - 2 * i) /\\
          (!j. j < 256 ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                           if %s then mld_invntt_block (word %d) %d %d m j else m j)"
   (String.concat " /\\ " (map (fun (r,v) -> Printf.sprintf "read %s s = word %s" r v) p.iconsts))
   p.iptr p.ik0 p.icnt p.ilen (cond "i") zw s l) in
  let tm = INV_CLOOP_TERM mc p in
  let sname = Printf.sprintf "s%d" p.isteps in
  let twist = INV_TWIST p.iz in
  (* the equalities of the components at the code's addresses and the canonical ones *)
  let comp (code,j) =
    prove(pt (Printf.sprintf
      "!a:int64 i. (memory :> bytes32 (%s)) = (memory :> bytes32 (word_add a (word (4 * (%s)))))" code j),
      REPEAT GEN_TAC THEN
      REWRITE_TAC (map (fun (k,d) -> NTT_WSUB_LEMMA k d) p.iwsub) THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC) in
  let comps = map comp [p.ilo0,lo0j; p.ilo1,lo1j; p.iup0,up0j; p.iup1,up1j] in
  let evl = map (fun (k,d) -> NTT_WSUB_ADD_LEMMA k d) p.iwsub in
  let cnt_th = prove(pt (Printf.sprintf
    "!i. i < %d ==> (val (word_sub (word (%d - 2 * i)) (word 2):int64) = 0 <=> ~(i + 1 < %d))" nit p.ilen nit),
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV) in
  let blk_lo j =
    MP_TAC(SPECL [pt (Printf.sprintf "word %d:int32" zw); `m:num->int32`; pt j;
                  pt (string_of_int s); pt (string_of_int l)] INV_BLK_LO) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[ARITH_RULE (pt (Printf.sprintf "(%s) + %d = %d + %d + 2 * i" lo0j l s l));
                    ARITH_RULE (pt (Printf.sprintf "(%s) + %d = %d + %d + 2 * i + 1" lo1j l s l))] THEN
    TRY(CONV_TAC WORD_RULE) in
  let blk_hi j =
    MP_TAC(SPECL [pt (Printf.sprintf "word %d:int32" zw); `m:num->int32`; pt j;
                  pt (string_of_int s); pt (string_of_int l)] INV_BLK_HI) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[ARITH_RULE (pt (Printf.sprintf "(%s) - %d = %d + 2 * i" up0j l s));
                    ARITH_RULE (pt (Printf.sprintf "(%s) - %d = %d + 2 * i + 1" up1j l s))] in
  let inv_apply =
    let th = SPECL [pt (Printf.sprintf "mld_invntt_block (word %d) %d %d m" zw s l);
                    `m:num->int32`;
                    pt (Printf.sprintf "\j. read (memory :> bytes32 (word_add a (word (4 * j)))) %s" sname);
                    pt (string_of_int s); pt (string_of_int l); `i:num`] NTT_INV_STEP in
    MATCH_MP_TAC(CONV_RULE(DEPTH_CONV BETA_CONV) th) in
  let fact addr j =
    let tm = pt (Printf.sprintf "read (memory :> bytes32 (%s)) s0 = (m:num->int32) (%s)" addr j) in
    let eq = pt (Printf.sprintf "(%s) = word_add (a:int64) (word (4 * (%s)))" addr j) in
    SUBGOAL_THEN tm ASSUME_TAC THENL
     [SUBGOAL_THEN eq (fun th -> REWRITE_TAC[th]) THENL
       [REWRITE_TAC(map (fun (k,d) -> NTT_WSUB_LEMMA k d) p.iwsub) THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM(fun th ->
        if is_forall(concl th) && free_in `mld_invntt_block` (concl th) then
          MP_TAC(SPEC (pt j) th) else NO_TAC) THEN
      ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      COND_CASES_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC];
      ALL_TAC] in
  let rest_fact =
    SUBGOAL_THEN (pt (Printf.sprintf
     "!j. j < 256 /\\ ~(j = %s) /\\ ~(j = %s) /\\ ~(j = %s) /\\ ~(j = %s)
          ==> read (memory :> bytes32 (word_add a (word (4 * j)))) s0 =
              (if %s then mld_invntt_block (word %d) %d %d m j else m j)"
     lo0j lo1j up0j up1j (cond "i") zw s l)) ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o
        check (fun th -> is_forall(concl th) &&
                         free_in `mld_invntt_block` (concl th))) THEN
      ASM_REWRITE_TAC[]; ALL_TAC] in
  let ptr_th = prove(`!a:int64 n k. word_add (word_add a (word n)) (word k) = word_add a (word (n + k))`,
    REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]) in
  let tac =
  CONCRETIZE_F_EVENTS_TAC
   (pt (Printf.sprintf
     "\\(a:int64) (pc:num).
        APPEND (f_ev_epil a pc)
         (APPEND (ENUMERATEL %d (\\i. f_ev_loop a pc i)) (f_ev_prol a pc))
      :(uarch_event)list" nit)) THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `m:num->int32`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC (pt (string_of_int nit))
   (pt ("pc + " ^ p.iloop)) (pt ("pc + " ^ p.iexit)) inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The head ***)

    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; ADD_CLAUSES; SUB_0;
                WORD_ADD_0; NTT_LT_SAME; OR_CLAUSES; COND_ID] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The body ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    fact p.iup0 up0j THEN fact p.iup1 up1j THEN fact p.ilo0 lo0j THEN fact p.ilo1 lo1j THEN
    rest_fact THEN
    ARM_STEPS_TAC exec (1--p.isteps) THEN
    RULE_ASSUM_TAC(REWRITE_RULE(comps @ evl @ [INV_SXT; twist; INV_TWIST_SWAP p.iz; WORD_ZX_ZX_32_64_32])) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MP (SPEC `i:num` cnt_th) (ASSUME (pt (Printf.sprintf "i < %d" nit)))] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [REWRITE_TAC[ptr_th] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(SPECL [pt (Printf.sprintf "%d - 2 * i" p.ilen); `2`] WSUB) THEN
      ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [inv_apply THEN REPEAT CONJ_TAC THENL
       [SIMPLE_ARITH_TAC; ARITH_TAC; blk_lo lo0j; blk_lo lo1j; blk_hi up0j; blk_hi up1j;
        FIRST_ASSUM ACCEPT_TAC];
      DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The exit ***)

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MP_TAC(SPECL [`m:num->int32`;
                    pt (Printf.sprintf "\\j. read (memory :> bytes32 (word_add a (word (4 * j)))) s0");
                    pt (Printf.sprintf "word %d:int32" zw); pt (string_of_int s);
                    pt (string_of_int l); pt (string_of_int nit)] INV_INV_EXIT) THEN
      CONV_TAC(LAND_CONV(DEPTH_CONV BETA_CONV)) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THENL [ARITH_TAC; ARITH_TAC; FIRST_ASSUM ACCEPT_TAC]; ALL_TAC] THEN
      DISCH_THEN ACCEPT_TAC;
      DISCHARGE_SAFETY_PROPERTY_TAC]] in
  if !inv_dbg then (ignore(g tm); ignore(e tac); failwith "dbg") else INV_PROVE tm tac;;

(* ------------------------------------------------------------------------- *)
(* The scaling loop: four coefficients per iteration, each multiplied by    *)
(* 41978 = 2^56 mod q with a Montgomery reduction (mld_fqscale).             *)
(* ------------------------------------------------------------------------- *)

let INV_FQSCALE_FQMUL = prove
 (`!a:int32. mld_fqscale a = mld_fqmul a (word 41978)`,
  GEN_TAC THEN REWRITE_TAC[mld_fqscale; mld_fqmul] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REFL_TAC);;

let INV_SCALE_TM = parse_term
   "exists f_events.
      forall e a (m:num->int32) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALL (nonoverlapping (a,1024)) [(word pc,libmldsa_size)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                  read PC s = word (pc + mldsa_poly_invntt_tomont_loop13) /\\
                  read X9 s = word_add a (word 8) /\\ read X10 s = word 256 /\\
                  read X8 s = word 18410684464595206144 /\\ read X11 s = word 41978 /\\
                  read X12 s = word 18446744073701171199 /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s = m i) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + mldsa_poly_invntt_tomont_loop13_exit) /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                           mld_fqscale (m i)) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a pc /\\
                     memaccess_inbounds e2 [a,1024] [a,1024]))
             (MAYCHANGE [PC; X0; X1; X9; X10; X13; X14; X15; X16; X17; X18] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a,1024)])";;

let INV_SCALE_INV =
 `\i s. read X8 s = word 18410684464595206144 /\ read X11 s = word 41978 /\
        read X12 s = word 18446744073701171199 /\
        read X9 s = word_add a (word (8 + 16 * i)) /\
        read X10 s = word (256 - 4 * i) /\
        (!j. j < 256 ==> read (memory :> bytes32 (word_add a (word (4 * j)))) s =
                         (if j < 4 * i then mld_fqscale ((m:num->int32) j) else m j))`;;

let INV_SCALE_HEAD =
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (pc:num).
      APPEND (f_ev_epil a pc)
       (APPEND (ENUMERATEL 64 (\i. f_ev_loop a pc i)) (f_ev_prol a pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `m:num->int32`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst INV_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `64` `pc + mldsa_poly_invntt_tomont_loop13`
   `pc + mldsa_poly_invntt_tomont_loop13_exit` INV_SCALE_INV THEN
  REPEAT CONJ_TAC;;

let INV_SCALE_STEP = prove
 (`!(f:num->int32) (m:num->int32) (mem:num->int32) i.
        i < 64 /\
        mem (4 * i) = f (4 * i) /\ mem (4 * i + 1) = f (4 * i + 1) /\
        mem (4 * i + 2) = f (4 * i + 2) /\ mem (4 * i + 3) = f (4 * i + 3) /\
        (!j. j < 256 /\ ~(j = 4 * i) /\ ~(j = 4 * i + 1) /\
             ~(j = 4 * i + 2) /\ ~(j = 4 * i + 3)
             ==> mem j = (if j < 4 * i then f j else m j))
        ==> !j. j < 256 ==> mem j = (if j < 4 * (i + 1) then f j else m j)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `j = 4 * i` THENL [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `4 * i < 4 * (i + 1)` (fun th -> REWRITE_TAC[th]) THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `j = 4 * i + 1` THENL [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `4 * i + 1 < 4 * (i + 1)` (fun th -> REWRITE_TAC[th]) THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `j = 4 * i + 2` THENL [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `4 * i + 2 < 4 * (i + 1)` (fun th -> REWRITE_TAC[th]) THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `j = 4 * i + 3` THENL [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `4 * i + 3 < 4 * (i + 1)` (fun th -> REWRITE_TAC[th]) THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(j < 4 * i <=> j < 4 * (i + 1))` (fun th -> REWRITE_TAC[th]) THEN
  ASM_ARITH_TAC);;

let INV_SCALE_WSUB k = NTT_WSUB_LEMMA 8 k;;

let INV_SCALE_BODY =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  (let fact addr j =
    let tm = parse_term (Printf.sprintf "read (memory :> bytes32 (%s)) s0 = (m:num->int32) (%s)" addr j) in
    let eq = parse_term (Printf.sprintf "(%s) = word_add (a:int64) (word (4 * (%s)))" addr j) in
    SUBGOAL_THEN tm ASSUME_TAC THENL
     [SUBGOAL_THEN eq (fun th -> REWRITE_TAC[th]) THENL
       [REWRITE_TAC[NTT_WSUB_LEMMA 8 8; NTT_WSUB_LEMMA 8 4] THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM(fun th ->
        if is_forall(concl th) && free_in `mld_fqscale` (concl th) then
          MP_TAC(SPEC (parse_term j) th) else NO_TAC) THEN
      ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      COND_CASES_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC];
      ALL_TAC] in
   fact "word_add a (word_sub (word (8 + 16 * i)) (word 8))" "4 * i" THEN
   fact "word_add a (word_sub (word (8 + 16 * i)) (word 4))" "4 * i + 1" THEN
   fact "word_add a (word (8 + 16 * i))" "4 * i + 2" THEN
   fact "word_add a (word ((8 + 16 * i) + 4))" "4 * i + 3") THEN
  SUBGOAL_THEN `!j. j < 256 /\ ~(j = 4 * i) /\ ~(j = 4 * i + 1) /\ ~(j = 4 * i + 2) /\ ~(j = 4 * i + 3)
          ==> read (memory :> bytes32 (word_add a (word (4 * j)))) s0 =
              (if j < 4 * i then mld_fqscale ((m:num->int32) j) else m j)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o
      check (fun th -> is_forall(concl th) && free_in `mld_fqscale` (concl th) &&
                       not(free_in `i + 1` (concl th)))) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ARM_STEPS_TAC INV_EXEC (1--26) THEN
  (let comp (code,j) =
     prove(parse_term (Printf.sprintf
       "!a:int64 i. (memory :> bytes32 (%s)) = (memory :> bytes32 (word_add a (word (4 * (%s)))))" code j),
       REPEAT GEN_TAC THEN
       REWRITE_TAC[NTT_WSUB_LEMMA 8 8; NTT_WSUB_LEMMA 8 4] THEN
       AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC) in
   let comps = map comp
     ["word_add a (word_sub (word (8 + 16 * i)) (word 8))","4 * i";
      "word_add a (word_sub (word (8 + 16 * i)) (word 4))","4 * i + 1";
      "word_add a (word (8 + 16 * i))","4 * i + 2";
      "word_add a (word ((8 + 16 * i) + 4))","4 * i + 3"] in
   let evl = [NTT_WSUB_ADD_LEMMA 8 8; NTT_WSUB_ADD_LEMMA 8 4] in
   let cnt_th = prove(`!i. i < 64 ==> (val (word_sub (word (256 - 4 * i)) (word 4):int64) = 0 <=> ~(i + 1 < 64))`,
     CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
     CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV) in
   let ptr_th = prove(`!a:int64 n k. word_add (word_add a (word n)) (word k) = word_add a (word (n + k))`,
     REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]) in
   RULE_ASSUM_TAC(REWRITE_RULE(comps @ evl @ [NTT_TWIST 41978; WORD_ZX_ZX_32_64_32])) THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[MP (SPEC `i:num` cnt_th) (ASSUME `i < 64`)] THEN
   CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
   CONJ_TAC THENL [REWRITE_TAC[ptr_th] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
   CONJ_TAC THENL
    [MP_TAC(SPECL [`256 - 4 * i`; `4`] WSUB) THEN
     ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
     DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
   CONJ_TAC THENL
    [MATCH_MP_TAC(CONV_RULE(DEPTH_CONV BETA_CONV)
       (SPECL [`\j. mld_fqscale ((m:num->int32) j)`; `m:num->int32`;
               `\j. read (memory :> bytes32 (word_add a (word (4 * j)))) s26`; `i:num`]
              INV_SCALE_STEP)) THEN
     REPEAT CONJ_TAC THENL
      [SIMPLE_ARITH_TAC;
       ASM_REWRITE_TAC[INV_FQSCALE_FQMUL]; ASM_REWRITE_TAC[INV_FQSCALE_FQMUL];
       ASM_REWRITE_TAC[INV_FQSCALE_FQMUL]; ASM_REWRITE_TAC[INV_FQSCALE_FQMUL];
       FIRST_ASSUM ACCEPT_TAC];
     DISCHARGE_SAFETY_PROPERTY_TAC]);;

let INV_SCALE_EXIT =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) && free_in `mld_fqscale` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `j < 4 * 64` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let INV_SCALE_TAC =
  INV_SCALE_HEAD THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; ADD_CLAUSES; SUB_0; WORD_ADD_0; OR_CLAUSES; COND_ID] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    INV_SCALE_BODY;
    INV_SCALE_EXIT];;

let INV_SCALE_LOOP = INV_PROVE INV_SCALE_TM INV_SCALE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The blocks of a layer of the inverse transform: the coefficients outside  *)
(* the blocks done are unchanged, and inside they are those of the block.   *)
(* ------------------------------------------------------------------------- *)

let INV_BLOCKS_BELOW = prove
 (`!l len n r (j:num). len = 2 EXP (8 - l) /\ 2 * len * n <= j
                       ==> mld_invntt_blocks l n r j = r j`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[mld_invntt_blocks; MULT_CLAUSES; LE_0] THEN
  STRIP_TAC THEN FIRST_ASSUM(fun th -> if concl th = `len = 2 EXP (8 - l)` then REWRITE_TAC[GSYM th] else NO_TAC) THEN
  REWRITE_TAC[mld_invntt_block] THEN
  SUBGOAL_THEN `~(2 * len * n <= j /\ j < 2 * len * n + len) /\
                ~(2 * len * n + len <= j /\ j < 2 * len * n + 2 * len)`
   (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let INV_BLOCK_OUT = prove
 (`!z (f:num->int32) s len (j:num).
     ~(s <= j /\ j < s + len) /\ ~(s + len <= j /\ j < s + 2 * len)
     ==> mld_invntt_block z s len f j = f j`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[mld_invntt_block]);;

let INV_BLOCKS_AT = prove
 (`!l len n b r (j:num).
        len = 2 EXP (8 - l) /\ b < n /\ 2 * len * b <= j /\ j < 2 * len * b + 2 * len
        ==> mld_invntt_blocks l n r j =
            mld_invntt_block (word_neg (mld_zeta (2 EXP l - 1 - b))) (2 * len * b) len r j`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[CONJUNCT1 LT]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mld_invntt_blocks] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> if concl th = `len = 2 EXP (8 - l)` then REWRITE_TAC[GSYM th] else NO_TAC) THEN
  ASM_CASES_TAC `b:num = n` THENL
   [TRC "c1" (FIRST_X_ASSUM(fun th -> if concl th = `b:num = n` then SUBST_ALL_TAC th else NO_TAC)) THEN
    REWRITE_TAC[mld_invntt_block] THEN
    FIRST_ASSUM(fun th -> if concl th = `len = 2 EXP (8 - l)` then REWRITE_TAC[GSYM th] else NO_TAC) THEN
    ASM_CASES_TAC `2 * len * n <= j /\ j < 2 * len * n + len` THENL
     [FIRST_ASSUM(fun th -> if concl th = `2 * len * n <= j /\ j < 2 * len * n + len` then REWRITE_TAC[th] else NO_TAC) THEN
      SUBGOAL_THEN `mld_invntt_blocks l n r j = r j` SUBST1_TAC THENL
       [MATCH_MP_TAC INV_BLOCKS_BELOW THEN EXISTS_TAC `len:num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `mld_invntt_blocks l n r (j + len) = r (j + len)` SUBST1_TAC THENL
       [MATCH_MP_TAC INV_BLOCKS_BELOW THEN EXISTS_TAC `len:num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[];
      ASM_CASES_TAC `2 * len * n + len <= j /\ j < 2 * len * n + 2 * len` THENL
       [FIRST_ASSUM(fun th -> if concl th = `~(2 * len * n <= j /\ j < 2 * len * n + len)` then REWRITE_TAC[th] else NO_TAC) THEN
        FIRST_ASSUM(fun th -> if concl th = `2 * len * n + len <= j /\ j < 2 * len * n + 2 * len` then REWRITE_TAC[th] else NO_TAC) THEN
        SUBGOAL_THEN `mld_invntt_blocks l n r j = r j` SUBST1_TAC THENL
         [MATCH_MP_TAC INV_BLOCKS_BELOW THEN EXISTS_TAC `len:num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `mld_invntt_blocks l n r (j - len) = r (j - len)` SUBST1_TAC THENL
         [MATCH_MP_TAC INV_BLOCKS_BELOW THEN EXISTS_TAC `len:num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[];
        SUBGOAL_THEN `F` MP_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]]]];
    TRC "c2a" (SUBGOAL_THEN `b < n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    TRC "c2b" (SUBGOAL_THEN `len * (b + 1) <= len * n` ASSUME_TAC THENL
     [MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[LE_REFL] THEN ASM_ARITH_TAC; ALL_TAC]) THEN
    TRC "c2c" (SUBGOAL_THEN `mld_invntt_block (word_neg (mld_zeta (2 EXP l - 1 - n))) (2 * len * n) len
                              (mld_invntt_blocks l n r) j = mld_invntt_blocks l n r j`
      (fun th -> REWRITE_TAC[th]) THENL
      [MATCH_MP_TAC INV_BLOCK_OUT THEN ASM_ARITH_TAC; ALL_TAC]) THEN
    TRC "c2d" (FIRST_X_ASSUM MATCH_MP_TAC) THEN TRC "c2e" ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Loop 1: ld2/st2, blocks of 2 coefficients, four blocks per iteration; the *)
(* zetas of the iteration are loaded as a vector, negated and reversed.      *)
(* ------------------------------------------------------------------------- *)

let INV_V1_TM = parse_term
   "exists f_events.
      forall e a (m:num->int32) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALL (nonoverlapping (a,1024)) [(word pc,libmldsa_size)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                  read PC s = word (pc + mldsa_poly_invntt_tomont_loop1) /\\
                  read X11 s = a /\\ read X9 s = word 1008 /\\
                  read X8 s = word (pc + rodata_mld_zetas) /\\
                  read X10 s = word 252236767799803904 /\\
                  read Q0 s = word 18410750461054296063 /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s = m i) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + mldsa_poly_invntt_tomont_loop1_exit) /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                           mld_invntt_blocks 8 128 m i) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a pc /\\
                     memaccess_inbounds e2
                      [a,1024; word(pc + rodata_mld_zetas),1024] [a,1024]))
             (MAYCHANGE [PC; X9; X11; X12; X13; X14; X15] ,,
              MAYCHANGE [Q1; Q2; Q3; Q4; Q5; Q6] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a,1024)])";;

let INV_V1_HEAD =
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (pc:num).
      APPEND (f_ev_epil a pc)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop a pc i)) (f_ev_prol a pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `m:num->int32`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst INV_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mldsa_poly_invntt_tomont_loop1`
   `pc + mldsa_poly_invntt_tomont_loop1_exit`
   `\i s. read X11 s = word_add a (word (32 * i)) /\
          read X9 s = word (1008 - 16 * i) /\
          read X8 s = word (pc + rodata_mld_zetas) /\
          read X10 s = word 252236767799803904 /\
          read Q0 s = word 18410750461054296063 /\
          (!j. j < 256 ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                           mld_invntt_blocks 8 (4 * i) m j)` THEN
  REPEAT CONJ_TAC;;

let INV_V1_PRE =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLD_ZETAS_LOADED o MATCH_MP NTT_ZETAS_IMG) THEN
  SUBGOAL_THEN `!k. k < 8 ==> read (memory :> bytes32 (word_add a (word (32 * i + 4 * k)))) s0 = (m:num->int32) (8 * i + k)` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `8 * i + k` o check (fun th -> is_forall(concl th) && free_in `mld_invntt_blocks` (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`8`; `1`; `4 * i`; `m:num->int32`; `8 * i + k`] INV_BLOCKS_BELOW) THEN
    ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `word (4 * (8 * i + k)):int64 = word (32 * i + 4 * k)` SUBST1_TAC THENL [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN ACCEPT_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(MP (SPECL [`a:int64`; `m:num->int32`; `i:num`; `s0:armstate`] LD256) th)) THEN
  SUBGOAL_THEN `!k. k < 4 ==> read (memory :> bytes32 (word_add (word (pc + 247592)) (word (4 * (252 - 4 * i) + 4 * k)))) s0 = mld_zeta ((252 - 4 * i) + k)` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `(252 - 4 * i) + k` o check (fun th -> is_forall(concl th) && free_in `mld_zeta` (concl th) && not(free_in `m:num->int32` (concl th)))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `word (4 * ((252 - 4 * i) + k)):int64 = word (4 * (252 - 4 * i) + 4 * k)` SUBST1_TAC THENL [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN ACCEPT_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(MP (SPECL [`word (pc + 247592):int64`; `mld_zeta`; `252 - 4 * i`; `s0:armstate`] LDZ) th)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `4 * (252 - 4 * i) = 1008 - 16 * i`; GSYM ADD_ASSOC]) THEN
  SUBGOAL_THEN `!j. j < 8 * i ==> read (memory :> bytes32 (word_add a (word (4 * j)))) s0 = mld_invntt_blocks 8 (4 * i) m j` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) && free_in `mld_invntt_blocks` (concl th) && not(free_in `m:num->int32` (concl th) && false) && is_imp(snd(dest_forall(concl th))) && fst(dest_imp(snd(dest_forall(concl th)))) = `j:num < 256`)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `!j. 8 * i + 8 <= j /\ j < 256 ==> read (memory :> bytes32 (word_add a (word (4 * j)))) s0 = mld_invntt_blocks 8 (4 * i) m j` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) && free_in `mld_invntt_blocks` (concl th) && is_imp(snd(dest_forall(concl th))) && fst(dest_imp(snd(dest_forall(concl th)))) = `j:num < 256`)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC]; ALL_TAC];;
let INV_LANE1 = prove
 (`!(mem:num->int32) (m:num->int32) i.
     i < 32 /\
     (!c. c < 4
          ==> mem (8 * i + 2 * c) =
              word_add (m (8 * i + 2 * c)) (m (8 * i + 2 * c + 1)) /\
              mem (8 * i + 2 * c + 1) =
              mld_fqmul (word_sub (m (8 * i + 2 * c)) (m (8 * i + 2 * c + 1)))
                        (word_neg (mld_zeta (252 - 4 * i + (3 - c))))) /\
     (!j. j < 256 /\ (j < 8 * i \/ 8 * i + 8 <= j)
          ==> mem j = mld_invntt_blocks 8 (4 * i) m j)
     ==> !j. j < 256 ==> mem j = mld_invntt_blocks 8 (4 * (i + 1)) m j`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `8 * i <= j /\ j < 8 * i + 8` THENL
   [SUBGOAL_THEN `?c. c < 4 /\ (j = 8 * i + 2 * c \/ j = 8 * i + 2 * c + 1)`
      MP_TAC THENL
     [EXISTS_TAC `(j - 8 * i) DIV 2` THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:num` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    MP_TAC(SPECL [`8`; `1`; `4 * (i + 1)`; `4 * i + c`; `m:num->int32`; `j:num`]
                 INV_BLOCKS_AT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:num` o check (fun th -> free_in `mld_fqmul` (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
    SUBGOAL_THEN `word_neg (mld_zeta (2 EXP 8 - 1 - (4 * i + c))) = word_neg (mld_zeta (252 - 4 * i + (3 - c)))`
      SUBST1_TAC THENL [AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [MP_TAC(SPECL [`word_neg (mld_zeta (252 - 4 * i + (3 - c)))`; `m:num->int32`; `j:num`; `2 * 1 * (4 * i + c)`; `1`] INV_BLK_LO) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH_RULE `8 * i + 2 * c + 1 = (8 * i + 2 * c) + 1`];
      MP_TAC(SPECL [`word_neg (mld_zeta (252 - 4 * i + (3 - c)))`; `m:num->int32`; `j:num`; `2 * 1 * (4 * i + c)`; `1`] INV_BLK_HI) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[ARITH_RULE `(8 * i + 2 * c + 1) - 1 = 8 * i + 2 * c`]];
    SUBGOAL_THEN `mld_invntt_blocks 8 (4 * (i + 1)) m j = mld_invntt_blocks 8 (4 * i) m j` SUBST1_TAC THENL
     [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC] THEN
    ASM_CASES_TAC `j < 8 * i` THENL
     [MP_TAC(SPECL [`8`; `1`; `4 * (i + 1)`; `j DIV 2`; `m:num->int32`; `j:num`]
                   INV_BLOCKS_AT) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      MP_TAC(SPECL [`8`; `1`; `4 * i`; `j DIV 2`; `m:num->int32`; `j:num`]
                   INV_BLOCKS_AT) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN REFL_TAC;
      MP_TAC(SPECL [`8`; `1`; `4 * (i + 1)`; `m:num->int32`; `j:num`]
                   INV_BLOCKS_BELOW) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ASM_ARITH_TAC]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      MP_TAC(SPECL [`8`; `1`; `4 * i`; `m:num->int32`; `j:num`]
                   INV_BLOCKS_BELOW) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ASM_ARITH_TAC]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN REFL_TAC]]);;


let INV_CNT1 = prove(`!i. i < 32 ==> (val (word_sub (word_sub (word (1008 - 16 * i)) (word 16)) (word 496):int64) = 0 <=> ~(i + 1 < 32))`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let INV_V1_BODY =
  INV_V1_PRE THEN
  TRC "steps" (MAP_EVERY (fun k -> ARM_STEPS_TAC INV_EXEC (k--k) THEN NORM) (1--31)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[JL0; JL1; MVL]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[el 0 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT); el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT); el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)]) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PTR_ADD_G; GSYM ADD_ASSOC]) THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)) THEN
  FIRST_X_ASSUM(fun th -> if is_conj(concl th) && free_in `s31:armstate` (concl th) then STRIP_ASSUME_TAC th else NO_TAC) THEN
  TRC "final" (ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[MP (SPEC `i:num` INV_CNT1) (ASSUME `i < 32`)] THEN
  TRC "pc" (CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC]) THEN
  TRC "ptr" (CONJ_TAC THENL [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC]) THEN
  TRC "x9" (CONJ_TAC THENL
   [MP_TAC(SPECL [`1008 - 16 * i`; `16`] WSUB) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC]) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(CONV_RULE(DEPTH_CONV BETA_CONV)
      (SPECL [`\j. read (memory :> bytes32 (word_add a (word(4 * j)))) s31`; `m:num->int32`; `i:num`] INV_LANE1)) THEN
    REPEAT CONJ_TAC THENL
     [TRC "m1" (FIRST_ASSUM ACCEPT_TAC);
      TRC "m2" (CONV_TAC(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; ADD_CLAUSES] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES] THEN
      TRC "m2b" (ASM_REWRITE_TAC[mld_fqmul] THEN TRY(REPEAT CONJ_TAC THEN CONV_TAC WORD_RULE));
      TRC "m3a" (X_GEN_TAC `j:num` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
      TRC "m3b" (FIRST_X_ASSUM DISJ_CASES_TAC) THENL
       [FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term (fun t -> t = `j < 8 * i`)) (concl th) then MP_TAC(SPEC `j:num` th) else NO_TAC) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC];
        FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term (fun t -> t = `8 * i + 8 <= j`)) (concl th) then MP_TAC(SPEC `j:num` th) else NO_TAC) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC]]];
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let INV_V1_TAC =
  INV_V1_HEAD THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0; SUB_0; CONJUNCT1 mld_invntt_blocks] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    INV_V1_BODY;
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV)) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC];;

let INV_V1_LOOP = INV_PROVE INV_V1_TM INV_V1_TAC;;

(* ------------------------------------------------------------------------- *)
(* Loop 2: ld4/st4, blocks of 4 coefficients, four blocks per iteration.     *)
(* ------------------------------------------------------------------------- *)

let INV_L2_STMT = `!(mem:num->int32) (m:num->int32) i.
     i < 16 /\
     (!c. c < 4
          ==> mem (16 * i + 4 * c) =
              word_add (m (16 * i + 4 * c)) (m (16 * i + 4 * c + 2)) /\
              mem (16 * i + 4 * c + 1) =
              word_add (m (16 * i + 4 * c + 1)) (m (16 * i + 4 * c + 3)) /\
              mem (16 * i + 4 * c + 2) =
              mld_fqmul (word_sub (m (16 * i + 4 * c)) (m (16 * i + 4 * c + 2)))
                        (word_neg (mld_zeta (124 - 4 * i + (3 - c)))) /\
              mem (16 * i + 4 * c + 3) =
              mld_fqmul (word_sub (m (16 * i + 4 * c + 1)) (m (16 * i + 4 * c + 3)))
                        (word_neg (mld_zeta (124 - 4 * i + (3 - c))))) /\
     (!j. j < 256 /\ (j < 16 * i \/ 16 * i + 16 <= j)
          ==> mem j = mld_invntt_blocks 7 (4 * i) m j)
     ==> !j. j < 256 ==> mem j = mld_invntt_blocks 7 (4 * (i + 1)) m j`;;
let INV_LANE2 = prove(INV_L2_STMT,


  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `16 * i <= j /\ j < 16 * i + 16` THENL
   [SUBGOAL_THEN `?c e. c < 4 /\ e < 4 /\ j = 16 * i + 4 * c + e` MP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`(j - 16 * i) DIV 4`; `(j - 16 * i) MOD 4`] THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:num` (X_CHOOSE_THEN `e:num` STRIP_ASSUME_TAC)) THEN
    MP_TAC(SPECL [`7`; `2`; `4 * (i + 1)`; `4 * i + c`; `m:num->int32`; `j:num`]
                 INV_BLOCKS_AT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:num` o check (fun th -> free_in `mld_fqmul` (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
    SUBGOAL_THEN `word_neg (mld_zeta (2 EXP 7 - 1 - (4 * i + c))) = word_neg (mld_zeta (124 - 4 * i + (3 - c)))`
      SUBST1_TAC THENL [AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `e = 0 \/ e = 1 \/ e = 2 \/ e = 3` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THENL
     [TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhand(concl th) = `j:num`))) THEN REWRITE_TAC[ADD_CLAUSES] THEN MP_TAC(SPECL [`word_neg (mld_zeta (124 - 4 * i + (3 - c)))`; `m:num->int32`; `16 * i + 4 * c`; `2 * 2 * (4 * i + c)`; `2`] INV_BLK_LO) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[ARITH_RULE `(16 * i + 4 * c) + 2 = 16 * i + 4 * c + 2`];
      TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhand(concl th) = `j:num`))) THEN MP_TAC(SPECL [`word_neg (mld_zeta (124 - 4 * i + (3 - c)))`; `m:num->int32`; `16 * i + 4 * c + 1`; `2 * 2 * (4 * i + c)`; `2`] INV_BLK_LO) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[ARITH_RULE `(16 * i + 4 * c + 1) + 2 = 16 * i + 4 * c + 3`];
      TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhand(concl th) = `j:num`))) THEN MP_TAC(SPECL [`word_neg (mld_zeta (124 - 4 * i + (3 - c)))`; `m:num->int32`; `16 * i + 4 * c + 2`; `2 * 2 * (4 * i + c)`; `2`] INV_BLK_HI) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[ARITH_RULE `(16 * i + 4 * c + 2) - 2 = 16 * i + 4 * c`];
      TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhand(concl th) = `j:num`))) THEN MP_TAC(SPECL [`word_neg (mld_zeta (124 - 4 * i + (3 - c)))`; `m:num->int32`; `16 * i + 4 * c + 3`; `2 * 2 * (4 * i + c)`; `2`] INV_BLK_HI) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[ARITH_RULE `(16 * i + 4 * c + 3) - 2 = 16 * i + 4 * c + 1`]];
    SUBGOAL_THEN `mld_invntt_blocks 7 (4 * (i + 1)) m j = mld_invntt_blocks 7 (4 * i) m j` SUBST1_TAC THENL
     [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC] THEN
    ASM_CASES_TAC `j < 16 * i` THENL
     [MP_TAC(SPECL [`7`; `2`; `4 * (i + 1)`; `j DIV 4`; `m:num->int32`; `j:num`]
                   INV_BLOCKS_AT) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      MP_TAC(SPECL [`7`; `2`; `4 * i`; `j DIV 4`; `m:num->int32`; `j:num`]
                   INV_BLOCKS_AT) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN REFL_TAC;
      MP_TAC(SPECL [`7`; `2`; `4 * (i + 1)`; `m:num->int32`; `j:num`]
                   INV_BLOCKS_BELOW) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ASM_ARITH_TAC]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      MP_TAC(SPECL [`7`; `2`; `4 * i`; `m:num->int32`; `j:num`]
                   INV_BLOCKS_BELOW) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ASM_ARITH_TAC]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN REFL_TAC]]);;


let INV_V2_TM = parse_term
   "exists f_events.
      forall e a (m:num->int32) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALL (nonoverlapping (a,1024)) [(word pc,libmldsa_size)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                  read PC s = word (pc + mldsa_poly_invntt_tomont_loop2) /\\
                  read X11 s = a /\\ read X9 s = word 496 /\\
                  read X8 s = word (pc + rodata_mld_zetas) /\\
                  read X10 s = word 252236767799803904 /\\
                  read Q0 s = word 18410750461054296063 /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s = m i) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + mldsa_poly_invntt_tomont_loop2_exit) /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                           mld_invntt_blocks 7 64 m i) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a pc /\\
                     memaccess_inbounds e2
                      [a,1024; word(pc + rodata_mld_zetas),1024] [a,1024]))
             (MAYCHANGE [PC; X9; X11; X12; X13; X14; X15; X16; X17] ,,
              MAYCHANGE [Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23; Q24] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a,1024)])";;

let INV_CNT2 = prove(`!i. i < 16 ==> (val (word_sub (word_sub (word (496 - 16 * i)) (word 16)) (word 240):int64) = 0 <=> ~(i + 1 < 16))`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let INV_V2_TAC =
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (pc:num).
      APPEND (f_ev_epil a pc)
       (APPEND (ENUMERATEL 16 (\i. f_ev_loop a pc i)) (f_ev_prol a pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `m:num->int32`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst INV_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `16` `pc + mldsa_poly_invntt_tomont_loop2` `pc + mldsa_poly_invntt_tomont_loop2_exit`
   `\i s. read X11 s = word_add a (word (64 * i)) /\
          read X9 s = word (496 - 16 * i) /\
          read X8 s = word (pc + rodata_mld_zetas) /\
          read X10 s = word 252236767799803904 /\
          read Q0 s = word 18410750461054296063 /\
          (!j. j < 256 ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                           mld_invntt_blocks 7 (4 * i) m j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0; SUB_0; CONJUNCT1 mld_invntt_blocks] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLD_ZETAS_LOADED o MATCH_MP NTT_ZETAS_IMG) THEN
    SUBGOAL_THEN `!k. k < 16 ==> read (memory :> bytes32 (word_add a (word (64 * i + 4 * k)))) s0 = (m:num->int32) (16 * i + k)` ASSUME_TAC THENL
     [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `16 * i + k` o check (fun th -> is_forall(concl th) && free_in `mld_invntt_blocks` (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`7`; `2`; `4 * i`; `m:num->int32`; `16 * i + k`] INV_BLOCKS_BELOW) THEN
      ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `word (4 * (16 * i + k)):int64 = word (64 * i + 4 * k)` SUBST1_TAC THENL [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN ACCEPT_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> STRIP_ASSUME_TAC(MP (SPECL [`a:int64`; `m:num->int32`; `i:num`; `s0:armstate`] LD4Q) th)) THEN
    SUBGOAL_THEN `!k. k < 4 ==> read (memory :> bytes32 (word_add (word (pc + 247592)) (word (4 * (124 - 4 * i) + 4 * k)))) s0 = mld_zeta ((124 - 4 * i) + k)` ASSUME_TAC THENL
     [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `(124 - 4 * i) + k` o check (fun th -> is_forall(concl th) && free_in `mld_zeta` (concl th) && not(free_in `m:num->int32` (concl th)))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `word (4 * ((124 - 4 * i) + k)):int64 = word (4 * (124 - 4 * i) + 4 * k)` SUBST1_TAC THENL [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN ACCEPT_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> ASSUME_TAC(MP (SPECL [`word (pc + 247592):int64`; `mld_zeta`; `124 - 4 * i`; `s0:armstate`] LDZ) th)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `4 * (124 - 4 * i) = 496 - 16 * i`; GSYM ADD_ASSOC]) THEN
    SUBGOAL_THEN `!j. j < 16 * i ==> read (memory :> bytes32 (word_add a (word (4 * j)))) s0 = mld_invntt_blocks 7 (4 * i) m j` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> try free_in `mld_invntt_blocks` (concl th) && fst(dest_imp(snd(dest_forall(concl th)))) = `j:num < 256` with _ -> false)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC]; ALL_TAC] THEN
    SUBGOAL_THEN `!j. 16 * i + 16 <= j /\ j < 256 ==> read (memory :> bytes32 (word_add a (word (4 * j)))) s0 = mld_invntt_blocks 7 (4 * i) m j` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> try free_in `mld_invntt_blocks` (concl th) && fst(dest_imp(snd(dest_forall(concl th)))) = `j:num < 256` with _ -> false)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC]; ALL_TAC] THEN
    TRC "steps" (MAP_EVERY (fun k -> ARM_STEPS_TAC INV_EXEC (k--k) THEN NORM) (1--53)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[DEIL0; DEIL1; DEIL2; DEIL3]) THEN
    NORM THEN
    RULE_ASSUM_TAC(REWRITE_RULE[JL0; JL1; MVL]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ILV0; ILV1; ILV2; ILV3]) THEN
    NORM THEN
    RULE_ASSUM_TAC(REWRITE_RULE[el 0 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT); el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT); el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)]) THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[PTR_ADD_G; GSYM ADD_ASSOC]) THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)) THEN
    REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && free_in `s53:armstate` (concl th) && free_in `memory` (concl th) && not(free_in `ensures` (concl th)) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
    TRC "final" (ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]) THEN
    REWRITE_TAC[MP (SPEC `i:num` INV_CNT2) (ASSUME `i < 16`)] THEN
    TRC "pc" (CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC]) THEN
    TRC "ptr" (CONJ_TAC THENL [REWRITE_TAC[WORD_RULE `word_add (word_add a (word x)) (word y) = word_add a (word (x + y))`] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC]) THEN
    TRC "x9" (CONJ_TAC THENL [MP_TAC(SPECL [`496 - 16 * i`; `16`] WSUB) THEN ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(CONV_RULE(DEPTH_CONV BETA_CONV)
        (SPECL [`\j. read (memory :> bytes32 (word_add a (word(4 * j)))) s53`; `m:num->int32`; `i:num`] INV_LANE2)) THEN
      REPEAT CONJ_TAC THENL
       [TRC "m1" (FIRST_ASSUM ACCEPT_TAC);
        TRC "m2" (CONV_TAC(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
        REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; ADD_CLAUSES] THEN
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES] THEN
        TRC "m2b" (ASM_REWRITE_TAC[mld_fqmul] THEN TRY(REPEAT CONJ_TAC THEN CONV_TAC WORD_RULE));
        TRC "m3a" (X_GEN_TAC `j:num` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
        TRC "m3b" (FIRST_X_ASSUM DISJ_CASES_TAC) THENL
         [FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term (fun t -> t = `j < 16 * i`)) (concl th) then MP_TAC(SPEC `j:num` th) else NO_TAC) THEN
          ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC];
          FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term (fun t -> t = `16 * i + 16 <= j`)) (concl th) then MP_TAC(SPEC `j:num` th) else NO_TAC) THEN
          ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC]]];
      DISCHARGE_SAFETY_PROPERTY_TAC];
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV)) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC];;

let INV_V2_LOOP = INV_PROVE INV_V2_TM INV_V2_TAC;;

(* ------------------------------------------------------------------------- *)
(* Loops that do one block per iteration, with the zeta from the table of    *)
(* the image through a pointer that goes down.                              *)
(* ------------------------------------------------------------------------- *)

type inv_block_loop =
  { bloop:string; bexit:string; lay:int; bptr:string; bk0:int; bzptr:string;
    bz0:int; bcnt:string; bc0:string; bcstep:int; bconsts:(string*string) list;
    bsteps:int; bops:(string*int) list; bwsub:(int*int) list;
    bregs:string list; bsp:bool };;

let INV_BLOOP_TERM mc (p:inv_block_loop) =
  let nit = 1 lsl (p.lay - 1) in
  let len = 1 lsl (8 - p.lay) in
  let consts = String.concat " /\\ "
    (map (fun (r,v) -> Printf.sprintf "read %s s = word %s" r v) p.bconsts) in
  let sp_in = if p.bsp then " sp" else "" in
  let sp_hyp = if p.bsp then
    " /\\ aligned 16 sp /\\ ALL (nonoverlapping (word_add sp (word 8),104)) [(a,1024); (word pc,libmldsa_size)]"
    else "" in
  let sp_pre = if p.bsp then "read SP s = sp /\\ " else "" in
  let sp_reg = if p.bsp then "; sp,112" else "" in
  let sp_may = if p.bsp then " ,, MAYCHANGE [memory :> bytes(word_add sp (word 8),104)]" else "" in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e a (m:num->int32) pc%s.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALL (nonoverlapping (a,1024)) [(word pc,libmldsa_size)]%s
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\ %s
                  read %s s = word_add a (word %d) /\\
                  read %s s = word (pc + %d) /\\
                  read %s s = word %s /\\ %s /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                           m i) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\ %s /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                           mld_invntt_blocks %d %d m i) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a pc%s /\\
                     memaccess_inbounds e2
                      [a,1024; word(pc + rodata_mld_zetas),1024%s] [a,1024%s]))
             (MAYCHANGE [PC; %s] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a,1024)]%s)"
   sp_in sp_hyp mc p.bloop sp_pre p.bptr p.bk0 p.bzptr (247592 + p.bz0) p.bcnt p.bc0 consts
   p.bexit consts p.lay nit sp_in sp_reg sp_reg
   (String.concat "; " (p.bptr :: p.bzptr :: p.bcnt :: p.bregs)) sp_may);;

let INV_BLOCK_STEP = prove
 (`!(r:num->int32) (mem:num->int32) z s len.
        s + 2 * len <= 256 /\
        (!k. k < 2 * len ==> mem (s + k) = mld_invntt_block z s len r (s + k)) /\
        (!j. j < 256 /\ ~(s <= j /\ j < s + 2 * len) ==> mem j = r j)
        ==> !j. j < 256 ==> mem j = mld_invntt_block z s len r j`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "K") (LABEL_TAC "R"))) THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `s <= j /\ j < s + 2 * len` THENL
   [USE_THEN "K" (MP_TAC o SPEC `j - s`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `s + (j - s) = j` (fun th -> REWRITE_TAC[th]) THEN
    TRY(ASM_ARITH_TAC);
    ALL_TAC] THEN
  USE_THEN "R" (fun th ->
    MP_TAC(MP (SPEC `j:num` th)
              (CONJ (ASSUME `j < 256`)
                    (ASSUME `~(s <= j /\ j < s + 2 * len)`)))) THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[mld_invntt_block] THEN
  SUBGOAL_THEN `~(s <= j /\ j < s + len) /\ ~(s + len <= j /\ j < s + 2 * len)`
   (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC);;

let INV_BLOCKS_SUC l =
  let len = 1 lsl (8 - l) in
  prove(parse_term(Printf.sprintf
   "!i m j. mld_invntt_blocks %d (i + 1) m j =
            mld_invntt_block (word_neg (mld_zeta (%d - i))) (%d * i) %d (mld_invntt_blocks %d i m) j"
   l ((1 lsl l) - 1) (2 * len) len l),
   REWRITE_TAC[GSYM ADD1; mld_invntt_blocks] THEN CONV_TAC NUM_REDUCE_CONV THEN
   REWRITE_TAC[ARITH_RULE `2 * 4 * i = 8 * i /\ 2 * 8 * i = 16 * i /\ 2 * 16 * i = 32 * i /\
                           2 * 2 * i = 4 * i /\ 2 * 1 * i = 2 * i /\ 2 * 32 * i = 64 * i /\
                           2 * 64 * i = 128 * i`]);;

(* ------------------------------------------------------------------------- *)
(* The Montgomery multiplication of a difference by a zeta from the table,   *)
(* as the loops of layers 3 to 5 compute it (negated zeta in a register).    *)
(* ------------------------------------------------------------------------- *)

let NEG_ARITH_TAC =
  TRY(FIRST_X_ASSUM(fun th -> if is_neg(concl th) && is_conj(dest_neg(concl th)) then MP_TAC th else NO_TAC)) THEN SIMPLE_ARITH_TAC;;
let INV_IWORD_SWAP = prove
 (`!P Q:int. iword(ival(iword Q:int64) + P):int64 = iword(ival(iword P:int64) + Q)`,
  REWRITE_TAC[IWORD_INT_ADD; IWORD_IVAL; WORD_ADD_SYM]);;

let INV_TW_GEN = prove
 (`!d w:int32.
    word_zx(word_ushr
     (iword(ival(iword(&0 + ival(word_zx(word_ishr
        (word (0 + val(iword(&0 + ival d * ival w):int64) * 252236767799803904):int64) 32):int32) *
        -- &8380417):int64) + ival d * ival w):int64) 32):int32 = mld_fqmul d w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_ZX_USHR_ISHR_32; INT_ADD_LID; NTT_QT; INV_IWORD_SWAP] THEN
  ACCEPT_TAC(SPECL [`d:int32`; `w:int32`] FQMUL_SCALAR_SWAP));;

let INV_NEGSUB = prove(`!z:int32. word_sub (word 0) z = word_neg z`, GEN_TAC THEN CONV_TAC WORD_RULE);;
let INV_BLOOP mc exec (p:inv_block_loop) =
  let pt s = parse_term s in
  let nit = 1 lsl (p.lay - 1) in
  let len = 1 lsl (8 - p.lay) in
  let sfac = 2 * len in
  let tm = INV_BLOOP_TERM mc p in
  let sname = Printf.sprintf "s%d" p.bsteps in
  let jstr n = if n = 0 then Printf.sprintf "%d * i" sfac
               else Printf.sprintf "%d * i + %d" sfac n in
  let wsubs = map (fun (k,d) -> NTT_WSUB_LEMMA k d) p.bwsub in
  let evl = map (fun (k,d) -> NTT_WSUB_ADD_LEMMA k d) p.bwsub in
  let comps = map (fun (code,n) ->
    prove(pt (Printf.sprintf
      "!a:int64 i. (memory :> bytes32 (%s)) = (memory :> bytes32 (word_add a (word (4 * (%s)))))" code (jstr n)),
      REPEAT GEN_TAC THEN REWRITE_TAC wsubs THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC))
    p.bops in
  let fact (code,n) =
    let tm = pt (Printf.sprintf "read (memory :> bytes32 (%s)) s0 = (mld_invntt_blocks %d i m) (%s)" code p.lay (jstr n)) in
    let eq = pt (Printf.sprintf "(%s) = word_add (a:int64) (word (4 * (%s)))" code (jstr n)) in
    SUBGOAL_THEN tm ASSUME_TAC THENL
     [SUBGOAL_THEN eq (fun th -> REWRITE_TAC[th]) THENL
       [REWRITE_TAC wsubs THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM(fun th ->
        if is_forall(concl th) && free_in `mld_invntt_blocks` (concl th) then
          MP_TAC(SPEC (pt (jstr n)) th) else NO_TAC) THEN
      ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN ACCEPT_TAC];
      ALL_TAC] in
  let zidx = Printf.sprintf "%d - i" (2 * nit - 1) in
  let zaddr = Printf.sprintf "word (pc + %d - 4 * i)" (247592 + p.bz0) in
  let zfact =
    SUBGOAL_THEN (pt (Printf.sprintf
      "read (memory :> bytes32 (%s)) s0 = mld_zeta (%s)" zaddr zidx)) ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in `mld_zeta` (concl th) && not(free_in `m:num->int32` (concl th))
                            then MP_TAC(SPEC (pt zidx) th) else NO_TAC) THEN
      ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN (pt (Printf.sprintf "word_add (word (pc + 247592)) (word (4 * (%s))):int64 = %s" zidx zaddr))
        SUBST1_TAC THENL
       [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN ACCEPT_TAC;
      ALL_TAC] in
  let rest_fact =
    SUBGOAL_THEN (pt (Printf.sprintf
     "!j. j < %d * i ==> read (memory :> bytes32 (word_add a (word (4 * j)))) s0 =
                         mld_invntt_blocks %d i m j" sfac p.lay)) ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o
        check (fun th -> is_forall(concl th) &&
                         free_in `mld_invntt_blocks` (concl th))) THEN
      ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN ACCEPT_TAC]; ALL_TAC] THEN
    SUBGOAL_THEN (pt (Printf.sprintf
     "!j. %d * i + 2 * %d <= j /\\ j < 256
          ==> read (memory :> bytes32 (word_add a (word (4 * j)))) s0 =
              mld_invntt_blocks %d i m j" sfac len p.lay)) ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o
        check (fun th -> is_forall(concl th) &&
                         free_in `mld_invntt_blocks` (concl th) &&
                         not(free_in (pt (Printf.sprintf "%d * i" sfac)) (concl th)))) THEN
      ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN ACCEPT_TAC]; ALL_TAC] in
  let rest_accept =
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC (pt (Printf.sprintf "j < %d * i" sfac)) THENL
     [FIRST_ASSUM(fun th ->
        if is_forall(concl th) && free_in `mld_invntt_blocks` (concl th) &&
           not(is_conj(fst(dest_imp(snd(dest_forall(concl th)))))) &&
           free_in (pt (Printf.sprintf "j < %d * i" sfac)) (concl th) && false
        then NO_TAC else
        let c = concl th in
        if is_forall c && is_imp(snd(dest_forall c)) &&
           (let a = fst(dest_imp(snd(dest_forall c))) in
            is_binary "<" a && free_in `i:num` a) &&
           free_in `mld_invntt_blocks` c
        then MP_TAC(SPEC `j:num` th) else NO_TAC) THEN
      ANTS_TAC THENL [NEG_ARITH_TAC; DISCH_THEN ACCEPT_TAC];
      FIRST_ASSUM(fun th ->
        let c = concl th in
        if is_forall c && is_imp(snd(dest_forall c)) &&
           is_conj(fst(dest_imp(snd(dest_forall c)))) &&
           free_in `mld_invntt_blocks` c
        then MP_TAC(SPEC `j:num` th) else NO_TAC) THEN
      ANTS_TAC THENL [NEG_ARITH_TAC; DISCH_THEN ACCEPT_TAC]] in
  let ptr_th = prove(`!a:int64 n k. word_add (word_add a (word n)) (word k) = word_add a (word (n + k))`,
    REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]) in
  let inv = pt (Printf.sprintf
   "\\i s. %s%s /\\ read %s s = word_add a (word (%d + %d * i)) /\\
          read %s s = word (pc + %d - 4 * i) /\\
          read %s s = word (%s + %d * i) /\\
          (!j. j < 256 ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                           mld_invntt_blocks %d i m j)"
   (String.concat " /\\ " (map (fun (r,v) -> Printf.sprintf "read %s s = word %s" r v) p.bconsts))
   (if p.bsp then " /\\ read SP s = sp" else "")
   p.bptr p.bk0 (4 * sfac) p.bzptr (247592 + p.bz0) p.bcnt p.bc0 p.bcstep p.lay) in
  let consts_asm = String.concat " /\\ "
    (map (fun (r,v) -> Printf.sprintf "read %s s = word %s" r v) p.bconsts) in
  ignore consts_asm;
  let blocks_suc = INV_BLOCKS_SUC p.lay in
  let nops = 2 * len in
  let zterm = Printf.sprintf "word_neg (mld_zeta (%d - i))" (2 * nit - 1) in
  let blk_tac k = TRC (Printf.sprintf "blk%d" k) @@
    let r = Printf.sprintf "mld_invntt_blocks %d i m" p.lay in
    ignore r;
    if k < len then
      MP_TAC(SPECL [pt zterm; pt (Printf.sprintf "mld_invntt_blocks %d i m" p.lay);
                    pt (jstr k); pt (Printf.sprintf "%d * i" sfac); pt (string_of_int len)]
                   INV_BLK_LO) THEN
      ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC[ARITH_RULE (pt (Printf.sprintf "(%s) + %d = %s" (jstr k) len (jstr (k + len))))] THEN
      TRY(CONV_TAC WORD_RULE)
    else
      MP_TAC(SPECL [pt zterm; pt (Printf.sprintf "mld_invntt_blocks %d i m" p.lay);
                    pt (jstr k); pt (Printf.sprintf "%d * i" sfac); pt (string_of_int len)]
                   INV_BLK_HI) THEN
      ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC[ARITH_RULE (pt (Printf.sprintf "(%s) - %d = %s" (jstr k) len (jstr (k - len))))] in
  let rec blk_conj k =
    if k = nops - 1 then blk_tac k
    else CONJ_TAC THENL [blk_tac k; blk_conj (k + 1)] in
  let rest_pat = Printf.sprintf "%d * i" sfac in
  ignore rest_pat;
  let cnt_th = prove(pt (Printf.sprintf
    "!i. i < %d ==> (val (word_add (word (%s + %d * i)) (word %d):int64) < %d <=> i + 1 < %d)"
    nit p.bc0 p.bcstep p.bcstep (p.bcstep * (nit - 1)) nit),
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV) in
  let BODY_REST_TAC =
    TRC "final" (ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]) THEN
    TRC "cmp" (REWRITE_TAC[MP (SPEC `i:num` cnt_th) (ASSUME (pt (Printf.sprintf "i < %d" nit)))]) THEN
    TRC "pc" (CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC]) THEN
    TRC "ptr" (CONJ_TAC THENL [REWRITE_TAC[ptr_th] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC]) THEN
    TRC "zptr" (CONJ_TAC THENL
     [SUBGOAL_THEN (pt (Printf.sprintf "word (pc + %d - 4 * i):int64 = word_add (word (pc + %d - 4 * (i + 1))) (word 4)" (247592 + p.bz0) (247592 + p.bz0)))
        SUBST1_TAC THENL
       [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `word 18446744073709551612:int64 = word_neg (word 4)` SUBST1_TAC THENL
       [CONV_TAC WORD_REDUCE_CONV; CONV_TAC WORD_RULE]; ALL_TAC]) THEN
    TRC "cnt" (CONJ_TAC THENL [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC]) THEN
    CONJ_TAC THENL
     [TRC "mem" (REWRITE_TAC[blocks_suc] THEN
      MATCH_MP_TAC(CONV_RULE(DEPTH_CONV BETA_CONV)
        (SPECL [pt (Printf.sprintf "mld_invntt_blocks %d i m" p.lay);
                pt (Printf.sprintf "\\j. read (memory :> bytes32 (word_add a (word (4 * j)))) %s" sname);
                pt zterm; pt (Printf.sprintf "%d * i" sfac); pt (string_of_int len)]
               INV_BLOCK_STEP)) THEN
      REPEAT CONJ_TAC THENL
       [TRC "m1" SIMPLE_ARITH_TAC;
        TRC "m2" (CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN CONV_TAC EXPAND_CASES_CONV THEN
        REWRITE_TAC[ADD_CLAUSES]) THEN TRC "m2b" (blk_conj 0);
        TRC "m3" rest_accept]);
      TRC "events" DISCHARGE_SAFETY_PROPERTY_TAC] in
  let tac =
  CONCRETIZE_F_EVENTS_TAC
   (pt (Printf.sprintf
     "\(a:int64) (pc:num)%s.
        APPEND (f_ev_epil a pc%s)
         (APPEND (ENUMERATEL %d (\i. f_ev_loop a pc%s i)) (f_ev_prol a pc%s))
      :(uarch_event)list"
     (if p.bsp then " (sp:int64)" else "") (if p.bsp then " sp" else "") nit
     (if p.bsp then " sp" else "") (if p.bsp then " sp" else ""))) THEN
  TRC "c1" (REPEAT META_EXISTS_TAC) THEN
  MAP_EVERY X_GEN_TAC ([`e:(uarch_event)list`; `a:int64`; `m:num->int32`; `pc:num`] @ (if p.bsp then [`sp:int64`] else [])) THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  TRC "c2" (ENSURES_EVENTS_WHILE_UP2_TAC (pt (string_of_int nit))
   (pt ("pc + " ^ p.bloop)) (pt ("pc + " ^ p.bexit)) inv) THEN
  TRC "c3" (REPEAT CONJ_TAC) THENL
   [TRC "t0" ARITH_TAC;

    (*** The head ***)

    TRC "t1a" (FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]) THEN
    TRC "t1b" (REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0; SUB_0; CONJUNCT1 mld_invntt_blocks] THEN
    ASM_REWRITE_TAC[]) THEN TRC "t1c" DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The body ***)

    TRC "b0" (X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN FULL_INIT_TAC) THEN
    TRC "b1" (FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLD_ZETAS_LOADED o MATCH_MP NTT_ZETAS_IMG)) THEN
    TRC "facts" (MAP_EVERY fact p.bops THEN zfact THEN rest_fact) THEN
    TRC "steps" (ARM_STEPS_TAC exec (1--p.bsteps)) THEN
    TRC "rewrite" (RULE_ASSUM_TAC(REWRITE_RULE(comps @ evl @ [INV_NEGSUB; INV_TW_GEN; WORD_ZX_ZX_32_64_32]))) THEN
    BODY_REST_TAC;

    (*** The exit ***)

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC] in
  if !inv_dbg then (ignore(g tm); ignore(e tac); failwith "dbg") else INV_PROVE tm tac;;


