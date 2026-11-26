(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The loops of the forward NTT of mldsa-native as clang 23 -O3 has          *)
(* compiled it (mldsa_poly_ntt): lemmas, generated for the registers, the    *)
(* constants and the addresses of each loop, from its head to its exit, with *)
(* the correctness and the events. Part 1: the arithmetic: the Montgomery    *)
(* multiplication by a constant zeta whose product with 2^32 * q^-1 mod 2^32 *)
(* the code has in a register, the half-blocks of an NTT block, and the      *)
(* invariants of the loops that do two butterflies per iteration. Part 2:    *)
(* the loops of layers 1 to 3, with the zeta in a register (loops 1 to 7).  *)
(* Part 3: the loops of layers 4 to 6, one block per iteration (loops 8 to   *)
(* 10), with the zeta from the table of the image. Part 4: the loops of      *)
(* layers 7 and 8 (loops 11 and 12), which use the vector loads and stores   *)
(* ld4/st4 and ld2/st2 and do the multiplications by the zetas from the      *)
(* table on vectors, with the library of the blocks of a layer they need.    *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_ntt.ml";;
needs "common/mldsa_native_poly.ml";;
needs "arm/proofs/consttime.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(* ------------------------------------------------------------------------- *)
(* Part 1: arithmetic.                                                       *)
(* ------------------------------------------------------------------------- *)

let WORD_ZX_SX_32_64_32 = prove
 (`!x:int32. word_zx(word_sx x:int64):int32 = x`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let WORD_ZX_USHR_ISHR_32 = prove
 (`!w:int64. word_zx(word_ushr w 32):int32 = word_zx(word_ishr w 32)`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let WORD_SHL32_ISHR = prove
 (`!w:int64. word_zx(word_ishr (word_shl w 32) 32):int32 = word_zx w`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

let SHL32_MUL = prove
 (`!w:int64. word_shl w 32 = word_mul w (word 4294967296)`,
  GEN_TAC THEN BITBLAST_TAC);;

let WORD_VALMUL = prove
 (`!(a:N word) c. word(val a * c) = word_mul a (word c)`,
  REWRITE_TAC[WORD_MUL; WORD_VAL]);;

(*** The Montgomery multiplication by the constant z of an int32, as the   ***)
(*** loops of poly_ntt compute it: the product by z, and the multiple of q ***)
(*** from the product of the coefficient with the constant                 ***)
(*** zq * 2^32 for zq = z * q^-1 mod 2^32, as the code has it in a         ***)
(*** register; the result is mld_fqmul x (word z) (z mod 2^32).            ***)

let NTT_TWIST z =
  let zw = ((z mod 4294967296) + 4294967296) mod 4294967296 in
  let zq = (zw * 58728449) mod 4294967296 in
  let c = Num.string_of_num
   (Num.mult_num (Num.num_of_int zq) (Num.power_num (Num.num_of_int 2) (Num.num_of_int 32))) in
  let znum = if z >= 0 then Printf.sprintf "&%d" z
             else Printf.sprintf "-- &%d" (-z) in
  let pt s = parse_term s in
  let twz = prove(pt (Printf.sprintf
    "!x:int32. word_mul (word_zx (iword (ival x * (%s)):int64):int32) (word 58728449) = word_mul x (word %d)"
    znum zq),
    GEN_TAC THEN
    SUBGOAL_THEN (pt (Printf.sprintf "(%s) = ival (word %d:int32)" znum zw))
      SUBST1_TAC THENL
     [CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REFL_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM WORD_MUL_SX_IWORD] THEN
    SIMP_TAC[WORD_ZX_MUL; DIMINDEX_32; DIMINDEX_64; ARITH;
             WORD_ZX_SX_32_64_32] THEN
    REWRITE_TAC[WORD_RULE `word_mul (word_mul x a) b = word_mul x (word_mul a b)`] THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[]) in
  let tt = prove(pt (Printf.sprintf
    "!x:int32. word_zx(word_ishr (word (0 + val (word_sx x:int64) * %s):int64) 32):int32 = word_mul x (word %d)"
    c zq),
    GEN_TAC THEN REWRITE_TAC[ADD_CLAUSES; WORD_VALMUL] THEN
    SUBGOAL_THEN (pt (Printf.sprintf
      "word %s:int64 = word_mul (word %d) (word 4294967296)" c zq))
      SUBST1_TAC THENL [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[WORD_RULE `word_mul a (word_mul b c) = word_mul (word_mul a b) c`;
                GSYM SHL32_MUL; WORD_SHL32_ISHR] THEN
    SIMP_TAC[WORD_ZX_MUL; DIMINDEX_32; DIMINDEX_64; ARITH;
             WORD_ZX_SX_32_64_32] THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[]) in
  prove(pt (Printf.sprintf
   "!x:int32. word_zx(word_ushr (iword(ival(iword(&0 + ival(word_zx(word_sx x:int64):int32) * (%s)):int64) + ival(word_zx(word_ishr (word (0 + val(word_sx x:int64) * %s):int64) 32):int32) * -- &8380417):int64) 32):int32 = mld_fqmul x (word %d)"
   znum c zw),
   GEN_TAC THEN
   REWRITE_TAC[WORD_ZX_USHR_ISHR_32; WORD_ZX_SX_32_64_32; INT_ADD_LID; tt;
               GSYM twz] THEN
   MP_TAC(SPECL [`x:int32`; pt (Printf.sprintf "word %d:int32" zw)]
               FQMUL_SCALAR_SWAP) THEN
   SUBGOAL_THEN (pt (Printf.sprintf "ival (word %d:int32) = %s" zw znum))
     (fun th -> REWRITE_TAC[th]) THEN
   TRY(CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REFL_TAC));;

(*** The halves of an NTT block ***)

let NTT_BLK_LO = prove
 (`!z m (j:num) start len. start <= j /\ j < start + len
     ==> mld_ntt_block z start len m j =
         word_add (m j) (mld_fqmul (m (j + len)) z)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[mld_ntt_block]);;

let NTT_BLK_HI = prove
 (`!z m (j:num) start len. start + len <= j /\ j < start + 2 * len
     ==> mld_ntt_block z start len m j =
         word_sub (m (j - len)) (mld_fqmul (m j) z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_ntt_block] THEN
  SUBGOAL_THEN `~(start <= j /\ j < start + len)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(*** The invariant of a loop with two butterflies per iteration, in the    ***)
(*** state after an iteration, from that before: the four coefficients     ***)
(*** done and the others as they were                                      ***)

let NTT_INV_STEP = prove
 (`!(f:num->int32) (m:num->int32) (mem:num->int32) start len i.
        2 * i + 2 <= len /\ start + 2 * len <= 256 /\
        mem (start + 2 * i) = f (start + 2 * i) /\
        mem (start + 2 * i + 1) = f (start + 2 * i + 1) /\
        mem (start + len + 2 * i) = f (start + len + 2 * i) /\
        mem (start + len + 2 * i + 1) = f (start + len + 2 * i + 1) /\
        (!j. j < 256 /\ ~(j = start + 2 * i) /\ ~(j = start + 2 * i + 1) /\
             ~(j = start + len + 2 * i) /\ ~(j = start + len + 2 * i + 1)
             ==> mem j = (if start <= j /\ j < start + 2 * i \/
                             start + len <= j /\ j < start + len + 2 * i
                          then f j else m j))
        ==> !j. j < 256
                ==> mem j = (if start <= j /\ j < start + 2 * (i + 1) \/
                                start + len <= j /\
                                j < start + len + 2 * (i + 1)
                             then f j else m j)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `j = start + 2 * i` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `start <= start + 2 * i /\ start + 2 * i < start + 2 * (i + 1)`
      ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `j = start + 2 * i + 1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `start <= start + 2 * i + 1 /\ start + 2 * i + 1 < start + 2 * (i + 1)`
      ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `j = start + len + 2 * i` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `start + len <= start + len + 2 * i /\
                  start + len + 2 * i < start + len + 2 * (i + 1)`
      ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `j = start + len + 2 * i + 1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `start + len <= start + len + 2 * i + 1 /\
                  start + len + 2 * i + 1 < start + len + 2 * (i + 1)`
      ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

(*** At the exit, the invariant is the result of the block ***)

let NTT_INV_EXIT = prove
 (`!(m:num->int32) (mem:num->int32) z start len n.
        2 * n = len /\ start + 2 * len <= 256 /\
        (!j. j < 256
             ==> mem j = (if start <= j /\ j < start + 2 * n \/
                             start + len <= j /\ j < start + len + 2 * n
                          then mld_ntt_block z start len m j else m j))
        ==> !j. j < 256 ==> mem j = mld_ntt_block z start len m j`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[mld_ntt_block] THEN
  SUBGOAL_THEN `~(start <= j /\ j < start + len) /\
                ~(start + len <= j /\ j < start + 2 * len)`
   (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC);;

(*** At the head, no coefficient is done ***)

let NTT_LT_SAME = prove
 (`!s j:num. (s <= j /\ j < s) <=> F`,
  ARITH_TAC);;

let WSUB = prove
 (`!n k. k <= n ==> word_sub (word n:int64) (word k) = word(n - k)`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `n = (n - k) + k` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ADD_SUB; WORD_RULE `word_sub (word (d + k)) (word k) = word d`]);;

(*** The addresses of the coefficients in the code: given as words of a    ***)
(*** base and the offset, the offset as the simulator computes it. The     ***)
(*** lemmas below rewrite them to word_add a (word (4 * j)).               ***)

(*** word_sub (word (K + n)) (word d) with numerals K and d <= K ***)

let NTT_WSUB_LEMMA k d =
  prove(parse_term(Printf.sprintf
   "!n. word_sub (word (%d + n):int64) (word %d) = word (%d + n)" k d (k - d)),
   GEN_TAC THEN REWRITE_TAC[WORD_ADD] THEN
   CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN CONV_TAC WORD_RULE);;

(*** the same with a base: events have word_sub (word_add a (word (K + n))) ***)

let NTT_WSUB_ADD_LEMMA k d =
  prove(parse_term(Printf.sprintf
   "!a:int64 n. word_sub (word_add a (word (%d + n))) (word %d) = word_add a (word (%d + n))" k d (k - d)),
   REPEAT GEN_TAC THEN REWRITE_TAC[WORD_ADD] THEN
   CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* Part 2: a loop of two butterflies per iteration with the zeta in          *)
(* registers. Parameters:                                                    *)
(*   loop, exit: labels; ptr, cnt: the registers of the pointer (from        *)
(*   a + k0, 8 more per iteration) and of the counter (from len, 2 less);   *)
(*   consts: the registers that keep their value, with the value;            *)
(*   start, len: the block (2 * len coefficients from start); z: the zeta;   *)
(*   steps: the instructions of an iteration;                                *)
(*   lo0, lo1, up0, up1: the addresses, as in the code, of the coefficients  *)
(*   start + 2i, start + 2i + 1, start + len + 2i, start + len + 2i + 1.     *)
(* ------------------------------------------------------------------------- *)

type ntt_const_loop =
  { loop:string; exit:string; ptr:string; k0:int; cnt:string;
    start:int; len:int; z:int; consts:(string*string) list; steps:int;
    lo0:string; lo1:string; up0:string; up1:string;
    wsub:(int*int) list };;

let NTT_CLOOP_TERM mc (p:ntt_const_loop) =
  let nit = p.len / 2 in
  let zw = ((p.z mod 4294967296) + 4294967296) mod 4294967296 in
  let consts = String.concat " /\\ "
    (map (fun (r,v) -> Printf.sprintf "read %s s = word %s" r v) p.consts) in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e a (m:num->int32) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALL (nonoverlapping (a,1024)) [(word pc,libmldsa_size)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read %s s = word_add a (word %d) /\\
                  read %s s = word %d /\\ %s /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                           m i) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                           mld_ntt_block (word %d) %d %d m i) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a pc /\\
                     memaccess_inbounds e2 [a,1024] [a,1024]))
             (MAYCHANGE [PC; %s; %s; X13; X14; X15; X16; X17; X18] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a,1024)])"
   mc p.loop p.ptr p.k0 p.cnt p.len consts p.exit zw p.start p.len
   p.ptr p.cnt)
  |> fun t -> ignore nit; t;;

let NTT_CLOOP mc exec (p:ntt_const_loop) =
  let pt s = parse_term s in
  let nit = p.len / 2 in
  let zw = ((p.z mod 4294967296) + 4294967296) mod 4294967296 in
  let s = p.start and l = p.len in
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
                           if %s then mld_ntt_block (word %d) %d %d m j else m j)"
   (String.concat " /\\ " (map (fun (r,v) -> Printf.sprintf "read %s s = word %s" r v) p.consts))
   p.ptr p.k0 p.cnt p.len (cond "i") zw s l) in
  let tm = NTT_CLOOP_TERM mc p in
  let sname = Printf.sprintf "s%d" p.steps in
  let twist = NTT_TWIST p.z in
  (* the equalities of the components at the code's addresses and the canonical ones *)
  let comp (code,j) =
    prove(pt (Printf.sprintf
      "!a:int64 i. (memory :> bytes32 (%s)) = (memory :> bytes32 (word_add a (word (4 * (%s)))))" code j),
      REPEAT GEN_TAC THEN
      REWRITE_TAC (map (fun (k,d) -> NTT_WSUB_LEMMA k d) p.wsub) THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC) in
  let comps = map comp [p.lo0,lo0j; p.lo1,lo1j; p.up0,up0j; p.up1,up1j] in
  let evl = map (fun (k,d) -> NTT_WSUB_ADD_LEMMA k d) p.wsub in
  let cnt_th = prove(pt (Printf.sprintf
    "!i. i < %d ==> (val (word_sub (word (%d - 2 * i)) (word 2):int64) = 0 <=> ~(i + 1 < %d))" nit p.len nit),
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV) in
  let blk_lo j =
    MP_TAC(SPECL [pt (Printf.sprintf "word %d:int32" zw); `m:num->int32`; pt j;
                  pt (string_of_int s); pt (string_of_int l)] NTT_BLK_LO) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[ARITH_RULE (pt (Printf.sprintf "(%s) + %d = %d + %d + 2 * i" lo0j l s l));
                    ARITH_RULE (pt (Printf.sprintf "(%s) + %d = %d + %d + 2 * i + 1" lo1j l s l))] in
  let blk_hi j =
    MP_TAC(SPECL [pt (Printf.sprintf "word %d:int32" zw); `m:num->int32`; pt j;
                  pt (string_of_int s); pt (string_of_int l)] NTT_BLK_HI) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[ARITH_RULE (pt (Printf.sprintf "(%s) - %d = %d + 2 * i" up0j l s));
                    ARITH_RULE (pt (Printf.sprintf "(%s) - %d = %d + 2 * i + 1" up1j l s))] in
  let inv_apply =
    let th = SPECL [pt (Printf.sprintf "mld_ntt_block (word %d) %d %d m" zw s l);
                    `m:num->int32`;
                    pt (Printf.sprintf "\j. read (memory :> bytes32 (word_add a (word (4 * j)))) %s" sname);
                    pt (string_of_int s); pt (string_of_int l); `i:num`] NTT_INV_STEP in
    MATCH_MP_TAC(CONV_RULE(DEPTH_CONV BETA_CONV) th) in
  let fact addr j =
    let tm = pt (Printf.sprintf "read (memory :> bytes32 (%s)) s0 = (m:num->int32) (%s)" addr j) in
    let eq = pt (Printf.sprintf "(%s) = word_add (a:int64) (word (4 * (%s)))" addr j) in
    SUBGOAL_THEN tm ASSUME_TAC THENL
     [SUBGOAL_THEN eq (fun th -> REWRITE_TAC[th]) THENL
       [REWRITE_TAC(map (fun (k,d) -> NTT_WSUB_LEMMA k d) p.wsub) THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM(fun th ->
        if is_forall(concl th) && free_in `mld_ntt_block` (concl th) then
          MP_TAC(SPEC (pt j) th) else NO_TAC) THEN
      ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      COND_CASES_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC];
      ALL_TAC] in
  let rest_fact =
    SUBGOAL_THEN (pt (Printf.sprintf
     "!j. j < 256 /\\ ~(j = %s) /\\ ~(j = %s) /\\ ~(j = %s) /\\ ~(j = %s)
          ==> read (memory :> bytes32 (word_add a (word (4 * j)))) s0 =
              (if %s then mld_ntt_block (word %d) %d %d m j else m j)"
     lo0j lo1j up0j up1j (cond "i") zw s l)) ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o
        check (fun th -> is_forall(concl th) &&
                         free_in `mld_ntt_block` (concl th))) THEN
      ASM_REWRITE_TAC[]; ALL_TAC] in
  let ptr_th = prove(`!a:int64 n k. word_add (word_add a (word n)) (word k) = word_add a (word (n + k))`,
    REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]) in
  prove(tm,
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
   (pt ("pc + " ^ p.loop)) (pt ("pc + " ^ p.exit)) inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The head ***)

    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; ADD_CLAUSES; SUB_0;
                WORD_ADD_0; NTT_LT_SAME; OR_CLAUSES; COND_ID] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The body ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    fact p.up0 up0j THEN fact p.up1 up1j THEN fact p.lo0 lo0j THEN fact p.lo1 lo1j THEN
    rest_fact THEN
    ARM_STEPS_TAC exec (1--p.steps) THEN
    RULE_ASSUM_TAC(REWRITE_RULE(comps @ evl @ [twist; WORD_ZX_ZX_32_64_32])) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MP (SPEC `i:num` cnt_th) (ASSUME (pt (Printf.sprintf "i < %d" nit)))] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [REWRITE_TAC[ptr_th] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(SPECL [pt (Printf.sprintf "%d - 2 * i" p.len); `2`] WSUB) THEN
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
                    pt (string_of_int l); pt (string_of_int nit)] NTT_INV_EXIT) THEN
      CONV_TAC(LAND_CONV(DEPTH_CONV BETA_CONV)) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THENL [ARITH_TAC; ARITH_TAC; FIRST_ASSUM ACCEPT_TAC]; ALL_TAC] THEN
      DISCH_THEN ACCEPT_TAC;
      DISCHARGE_SAFETY_PROPERTY_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Part 3: the loops of layers 4 to 6, which do one block per iteration, with *)
(* the zeta loaded from the table of the image. The Montgomery multiplication *)
(* is the usual one, with q^-1 * 2^32 in a register.                          *)
(* ------------------------------------------------------------------------- *)

let NTT_QT = prove
 (`!a:int64. word_zx(word_ishr (word (0 + val a * 252236767799803904):int64) 32):int32 =
             word_mul (word_zx a) (word 58728449)`,
  GEN_TAC THEN REWRITE_TAC[ADD_CLAUSES; WORD_VALMUL] THEN
  SUBGOAL_THEN `word 252236767799803904:int64 = word_mul (word 58728449) (word 4294967296)`
    SUBST1_TAC THENL [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_mul a (word_mul b c) = word_mul (word_mul a b) c`;
              GSYM SHL32_MUL; WORD_SHL32_ISHR] THEN
  SIMP_TAC[WORD_ZX_MUL; DIMINDEX_32; DIMINDEX_64; ARITH] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[WORD_MUL_SYM]);;

let NTT_TW_GEN = prove
 (`!x z:int32.
     word_zx(word_ushr
      (iword(ival(iword(&0 + ival(word_zx(word_sx x:int64):int32) *
                              ival(word_zx(word_sx z:int64):int32)):int64) +
             ival(word_zx(word_ishr
                   (word (0 + val(iword(&0 + ival(word_zx(word_sx x:int64):int32) *
                                        ival(word_zx(word_sx z:int64):int32)):int64) *
                              252236767799803904):int64) 32):int32) *
             -- &8380417):int64) 32):int32 = mld_fqmul x z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[WORD_ZX_USHR_ISHR_32; WORD_ZX_SX_32_64_32; INT_ADD_LID; NTT_QT] THEN
  REWRITE_TAC[FQMUL_SCALAR_SWAP]);;

(*** One more block of the layer: the blocks of a layer l as a function of ***)
(*** the blocks done, in the form for numerals                            ***)

let NTT_BLOCKS_SUC l =
  let len = 1 lsl (7 - l) in
  prove(parse_term(Printf.sprintf
   "!i m j. mld_ntt_blocks %d (i + 1) m j =
            mld_ntt_block (mld_zeta (%d + i)) (%d * i) %d (mld_ntt_blocks %d i m) j"
   l (1 lsl l) (2 * len) len l),
   REWRITE_TAC[GSYM ADD1; mld_ntt_blocks] THEN CONV_TAC NUM_REDUCE_CONV THEN
   REWRITE_TAC[ARITH_RULE `2 * 4 * i = 8 * i /\ 2 * 8 * i = 16 * i /\ 2 * 16 * i = 32 * i /\
                           2 * 2 * i = 4 * i /\ 2 * 1 * i = 2 * i /\ 2 * 32 * i = 64 * i /\
                           2 * 64 * i = 128 * i`]);;

(*** The coefficients of the block done, and the others as they were ***)

let NTT_BLOCK_STEP = prove
 (`!(r:num->int32) (mem:num->int32) z s len.
        s + 2 * len <= 256 /\
        (!k. k < 2 * len ==> mem (s + k) = mld_ntt_block z s len r (s + k)) /\
        (!j. j < 256 /\ ~(s <= j /\ j < s + 2 * len) ==> mem j = r j)
        ==> !j. j < 256 ==> mem j = mld_ntt_block z s len r j`,
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
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[mld_ntt_block] THEN
  SUBGOAL_THEN `~(s <= j /\ j < s + len) /\ ~(s + len <= j /\ j < s + 2 * len)`
   (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC);;

(*** The table of zetas in the image, as bytes ***)

let NTT_ZETAS_IMG =
  MLDSA_NATIVE_IMAGE_DATA_RULE mld_zetas_data (layout "rodata_mld_zetas");;

(*** Parameters: loop, exit; the layer lay (blocks of 2 * len coefficients,  ***)
(*** nit blocks, one per iteration); the registers of the pointer ptr (from  ***)
(*** a + k0, step bytes per iteration) and of the index idx (4 * i, so that  ***)
(*** the zeta of block i is at table + 4 * (nit + i)); the registers that    ***)
(*** keep their value; the instructions of an iteration; the coefficient     ***)
(*** accesses (address in the code, index relative to the block); the        ***)
(*** address of the zeta in the code; the pairs of numerals (K, d) of the    ***)
(*** subtractions word_sub (word (K + n)) (word d) of the code; the other    ***)
(*** registers that the loop writes.                                          ***)

(*** TRC name tac is tac, and with ntt_trace set it reports the progress ***)

let ntt_trace = ref false;;
let TRC name (tac:tactic) : tactic = fun g ->
  if not !ntt_trace then tac g else
  (Printf.printf "START %s\n%!" name;
   try let r = tac g in Printf.printf "DONE %s\n%!" name; r
   with e -> (Printf.printf "FAILED %s %s\n%!" name (Printexc.to_string e); raise e));;

type ntt_block_loop =
  { bloop:string; bexit:string; lay:int; blen:int; bptr:string; bk0:int;
    bstep:int; bidx:string; bconsts:(string*string) list; bsteps:int;
    bops:(string*int) list; bzaddr:string; bwsub:(int*int) list;
    bregs:string list };;

let NTT_BLOOP_TERM mc (p:ntt_block_loop) =
  let nit = 1 lsl p.lay in
  let consts = String.concat " /\\ "
    (map (fun (r,v) -> Printf.sprintf "read %s s = word %s" r v) p.bconsts) in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e a (m:num->int32) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALL (nonoverlapping (a,1024)) [(word pc,libmldsa_size)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read %s s = word_add a (word %d) /\\
                  read %s s = word 0 /\\ %s /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                           m i) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\ %s /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                           mld_ntt_blocks %d %d m i) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a pc /\\
                     memaccess_inbounds e2
                      [a,1024; word(pc + rodata_mld_zetas),1024] [a,1024]))
             (MAYCHANGE [PC; %s] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a,1024)])"
   mc p.bloop p.bptr p.bk0 p.bidx consts p.bexit consts p.lay nit
   (String.concat "; " (p.bptr :: p.bidx :: p.bregs)));;

let NTT_BLOOP mc exec (p:ntt_block_loop) =
  let pt s = parse_term s in
  let nit = 1 lsl p.lay in
  let len = p.blen in
  let sfac = 2 * len in
  let tm = NTT_BLOOP_TERM mc p in
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
    let tm = pt (Printf.sprintf "read (memory :> bytes32 (%s)) s0 = (mld_ntt_blocks %d i m) (%s)" code p.lay (jstr n)) in
    let eq = pt (Printf.sprintf "(%s) = word_add (a:int64) (word (4 * (%s)))" code (jstr n)) in
    SUBGOAL_THEN tm ASSUME_TAC THENL
     [SUBGOAL_THEN eq (fun th -> REWRITE_TAC[th]) THENL
       [REWRITE_TAC wsubs THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM(fun th ->
        if is_forall(concl th) && free_in `mld_ntt_blocks` (concl th) then
          MP_TAC(SPEC (pt (jstr n)) th) else NO_TAC) THEN
      ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN ACCEPT_TAC];
      ALL_TAC] in
  let zfact =
    SUBGOAL_THEN (pt (Printf.sprintf
      "read (memory :> bytes32 (%s)) s0 = mld_zeta (%d + i)" p.bzaddr nit)) ASSUME_TAC THENL
     [SUBGOAL_THEN (pt (Printf.sprintf "word (4 * i + %d):int64 = word (4 * (%d + i))" (4 * nit) nit))
        SUBST1_TAC THENL [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM(fun th -> if is_forall(concl th) && free_in `mld_zeta` (concl th)
                            then MP_TAC(SPEC (pt (Printf.sprintf "%d + i" nit)) th) else NO_TAC) THEN
      ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN ACCEPT_TAC];
      ALL_TAC] in
  let rest_fact =
    SUBGOAL_THEN (pt (Printf.sprintf
     "!j. j < %d * i ==> read (memory :> bytes32 (word_add a (word (4 * j)))) s0 =
                         mld_ntt_blocks %d i m j" sfac p.lay)) ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o
        check (fun th -> is_forall(concl th) &&
                         free_in `mld_ntt_blocks` (concl th))) THEN
      ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN ACCEPT_TAC]; ALL_TAC] THEN
    SUBGOAL_THEN (pt (Printf.sprintf
     "!j. %d * i + 2 * %d <= j /\\ j < 256
          ==> read (memory :> bytes32 (word_add a (word (4 * j)))) s0 =
              mld_ntt_blocks %d i m j" sfac len p.lay)) ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o
        check (fun th -> is_forall(concl th) &&
                         free_in `mld_ntt_blocks` (concl th) &&
                         not(free_in (pt (Printf.sprintf "%d * i" sfac)) (concl th)))) THEN
      ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN ACCEPT_TAC]; ALL_TAC] in
  let rest_accept =
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC (pt (Printf.sprintf "j < %d * i" sfac)) THENL
     [FIRST_ASSUM(fun th ->
        if is_forall(concl th) && free_in `mld_ntt_blocks` (concl th) &&
           not(is_conj(fst(dest_imp(snd(dest_forall(concl th)))))) &&
           free_in (pt (Printf.sprintf "j < %d * i" sfac)) (concl th) && false
        then NO_TAC else
        let c = concl th in
        if is_forall c && is_imp(snd(dest_forall c)) &&
           (let a = fst(dest_imp(snd(dest_forall c))) in
            is_binary "<" a && free_in `i:num` a) &&
           free_in `mld_ntt_blocks` c
        then MP_TAC(SPEC `j:num` th) else NO_TAC) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC];
      FIRST_ASSUM(fun th ->
        let c = concl th in
        if is_forall c && is_imp(snd(dest_forall c)) &&
           is_conj(fst(dest_imp(snd(dest_forall c)))) &&
           free_in `mld_ntt_blocks` c
        then MP_TAC(SPEC `j:num` th) else NO_TAC) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC]] in
  let cnt_th = prove(pt (Printf.sprintf
    "!i. i < %d ==> (val (word_sub (word_add (word (4 * i)) (word 4)) (word %d):int64) = 0 <=> ~(i + 1 < %d))" nit (4 * nit) nit),
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV) in
  let ptr_th = prove(`!a:int64 n k. word_add (word_add a (word n)) (word k) = word_add a (word (n + k))`,
    REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]) in
  let idx_th = prove(`!i. word_add (word (4 * i)) (word 4):int64 = word (4 * (i + 1))`,
    GEN_TAC THEN REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC) in
  let inv = pt (Printf.sprintf
   "\\i s. %s /\\ read %s s = word_add a (word (%d + %d * i)) /\\
          read %s s = word (4 * i) /\\
          (!j. j < 256 ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                           mld_ntt_blocks %d i m j)"
   (String.concat " /\\ " (map (fun (r,v) -> Printf.sprintf "read %s s = word %s" r v) p.bconsts))
   p.bptr p.bk0 p.bstep p.bidx p.lay) in
  let consts_asm = String.concat " /\\ "
    (map (fun (r,v) -> Printf.sprintf "read %s s = word %s" r v) p.bconsts) in
  ignore consts_asm;
  let blocks_suc = NTT_BLOCKS_SUC p.lay in
  let nops = 2 * len in
  let zterm = Printf.sprintf "mld_zeta (%d + i)" nit in
  let blk_tac k = TRC (Printf.sprintf "blk%d" k) @@
    let r = Printf.sprintf "mld_ntt_blocks %d i m" p.lay in
    ignore r;
    if k < len then
      MP_TAC(SPECL [pt zterm; pt (Printf.sprintf "mld_ntt_blocks %d i m" p.lay);
                    pt (jstr k); pt (Printf.sprintf "%d * i" sfac); pt (string_of_int len)]
                   NTT_BLK_LO) THEN
      ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC[ARITH_RULE (pt (Printf.sprintf "(%s) + %d = %s" (jstr k) len (jstr (k + len))))]
    else
      MP_TAC(SPECL [pt zterm; pt (Printf.sprintf "mld_ntt_blocks %d i m" p.lay);
                    pt (jstr k); pt (Printf.sprintf "%d * i" sfac); pt (string_of_int len)]
                   NTT_BLK_HI) THEN
      ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC[ARITH_RULE (pt (Printf.sprintf "(%s) - %d = %s" (jstr k) len (jstr (k - len))))] in
  let rec blk_conj k =
    if k = nops - 1 then blk_tac k
    else CONJ_TAC THENL [blk_tac k; blk_conj (k + 1)] in
  let rest_pat = Printf.sprintf "%d * i" sfac in
  ignore rest_pat;
  let cmp_th = prove(pt (Printf.sprintf
    "!i. i < %d ==> (val (word_add (word (4 * i)) (word %s):int64) = 0 <=> ~(i + 1 < %d))" nit (Num.string_of_num (Num.add_num (Num.sub_num (Num.power_num (Num.num_of_int 2) (Num.num_of_int 64)) (Num.num_of_int (4 * nit))) (Num.num_of_int 4))) nit),
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV) in
  ignore cnt_th;
  let tac =
  CONCRETIZE_F_EVENTS_TAC
   (pt (Printf.sprintf
     "\(a:int64) (pc:num).
        APPEND (f_ev_epil a pc)
         (APPEND (ENUMERATEL %d (\i. f_ev_loop a pc i)) (f_ev_prol a pc))
      :(uarch_event)list" nit)) THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `m:num->int32`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC (pt (string_of_int nit))
   (pt ("pc + " ^ p.bloop)) (pt ("pc + " ^ p.bexit)) inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The head ***)

    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0; CONJUNCT1 mld_ntt_blocks] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The body ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLD_ZETAS_LOADED o MATCH_MP NTT_ZETAS_IMG) THEN
    TRC "facts" (MAP_EVERY fact p.bops THEN zfact THEN rest_fact) THEN
    TRC "steps" (ARM_STEPS_TAC exec (1--p.bsteps)) THEN
    TRC "rewrite" (RULE_ASSUM_TAC(REWRITE_RULE(comps @ evl @ [NTT_TW_GEN; WORD_ZX_ZX_32_64_32]))) THEN
    TRC "final" (ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]) THEN
    TRC "cmp" (REWRITE_TAC[MP (SPEC `i:num` cmp_th) (ASSUME (pt (Printf.sprintf "i < %d" nit)))]) THEN
    TRC "pc" (CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC]) THEN
    TRC "ptr" (CONJ_TAC THENL [REWRITE_TAC[ptr_th] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC]) THEN
    TRC "idx" (CONJ_TAC THENL [REWRITE_TAC[idx_th]; ALL_TAC]) THEN
    CONJ_TAC THENL
     [TRC "mem" (REWRITE_TAC[blocks_suc] THEN
      MATCH_MP_TAC(CONV_RULE(DEPTH_CONV BETA_CONV)
        (SPECL [pt (Printf.sprintf "mld_ntt_blocks %d i m" p.lay);
                pt (Printf.sprintf "\j. read (memory :> bytes32 (word_add a (word (4 * j)))) %s" sname);
                pt zterm; pt (Printf.sprintf "%d * i" sfac); pt (string_of_int len)]
               NTT_BLOCK_STEP)) THEN
      REPEAT CONJ_TAC THENL
       [TRC "m1" SIMPLE_ARITH_TAC;
        TRC "m2" (CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN CONV_TAC EXPAND_CASES_CONV THEN
        REWRITE_TAC[ADD_CLAUSES]) THEN TRC "m2b" (blk_conj 0);
        TRC "m3" rest_accept]);
      TRC "events" DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The exit ***)

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC] in
  prove(tm,tac);;

(* ------------------------------------------------------------------------- *)
(* Part 4: the loops of layers 7 and 8 (loops 11 and 12), which use NEON     *)
(* ld4/st4 and ld1/st1 of 256 bits and do the Montgomery multiplication on   *)
(* vectors with scalar multiplications by q^-1 * 2^32. First, the lemmas on  *)
(* the blocks of a layer, the lanes of the vectors and the interleaving.     *)
(* ------------------------------------------------------------------------- *)

let NTT_NEON_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa_poly_ntt"];;

let PTR_ADD_G = prove(`!b:int64 n k. word_add (word_add b (word n)) (word k) = word_add b (word (n + k))`, REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]);;

(*** The blocks of a layer: the coefficients outside the blocks done, and inside ***)

let NTT_BLOCKS_BELOW = prove
 (`!l len n r (j:num). len = 2 EXP (7 - l) /\ 2 * len * n <= j
                       ==> mld_ntt_blocks l n r j = r j`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[mld_ntt_blocks; MULT_CLAUSES; LE_0] THEN
  STRIP_TAC THEN FIRST_ASSUM(fun th -> if concl th = `len = 2 EXP (7 - l)` then REWRITE_TAC[GSYM th] else NO_TAC) THEN
  REWRITE_TAC[mld_ntt_block] THEN
  SUBGOAL_THEN `~(2 * len * n <= j /\ j < 2 * len * n + len) /\
                ~(2 * len * n + len <= j /\ j < 2 * len * n + 2 * len)`
   (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let NTT_BLOCK_OUT = prove
 (`!z (f:num->int32) s len (j:num).
     ~(s <= j /\ j < s + len) /\ ~(s + len <= j /\ j < s + 2 * len)
     ==> mld_ntt_block z s len f j = f j`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[mld_ntt_block]);;

let NTT_BLOCKS_AT = prove
 (`!l len n b r (j:num).
        len = 2 EXP (7 - l) /\ b < n /\ 2 * len * b <= j /\ j < 2 * len * b + 2 * len
        ==> mld_ntt_blocks l n r j =
            mld_ntt_block (mld_zeta (2 EXP l + b)) (2 * len * b) len r j`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[CONJUNCT1 LT]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mld_ntt_blocks] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> if concl th = `len = 2 EXP (7 - l)` then REWRITE_TAC[GSYM th] else NO_TAC) THEN
  ASM_CASES_TAC `b:num = n` THENL
   [TRC "c1" (FIRST_X_ASSUM(fun th -> if concl th = `b:num = n` then SUBST_ALL_TAC th else NO_TAC)) THEN
    REWRITE_TAC[mld_ntt_block] THEN
    FIRST_ASSUM(fun th -> if concl th = `len = 2 EXP (7 - l)` then REWRITE_TAC[GSYM th] else NO_TAC) THEN
    ASM_CASES_TAC `2 * len * n <= j /\ j < 2 * len * n + len` THENL
     [FIRST_ASSUM(fun th -> if concl th = `2 * len * n <= j /\ j < 2 * len * n + len` then REWRITE_TAC[th] else NO_TAC) THEN
      SUBGOAL_THEN `mld_ntt_blocks l n r j = r j` SUBST1_TAC THENL
       [MATCH_MP_TAC NTT_BLOCKS_BELOW THEN EXISTS_TAC `len:num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `mld_ntt_blocks l n r (j + len) = r (j + len)` SUBST1_TAC THENL
       [MATCH_MP_TAC NTT_BLOCKS_BELOW THEN EXISTS_TAC `len:num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[];
      ASM_CASES_TAC `2 * len * n + len <= j /\ j < 2 * len * n + 2 * len` THENL
       [FIRST_ASSUM(fun th -> if concl th = `~(2 * len * n <= j /\ j < 2 * len * n + len)` then REWRITE_TAC[th] else NO_TAC) THEN
        FIRST_ASSUM(fun th -> if concl th = `2 * len * n + len <= j /\ j < 2 * len * n + 2 * len` then REWRITE_TAC[th] else NO_TAC) THEN
        SUBGOAL_THEN `mld_ntt_blocks l n r j = r j` SUBST1_TAC THENL
         [MATCH_MP_TAC NTT_BLOCKS_BELOW THEN EXISTS_TAC `len:num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `mld_ntt_blocks l n r (j - len) = r (j - len)` SUBST1_TAC THENL
         [MATCH_MP_TAC NTT_BLOCKS_BELOW THEN EXISTS_TAC `len:num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[];
        SUBGOAL_THEN `F` MP_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]]]];
    TRC "c2a" (SUBGOAL_THEN `b < n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    TRC "c2b" (SUBGOAL_THEN `len * (b + 1) <= len * n` ASSUME_TAC THENL
     [MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[LE_REFL] THEN ASM_ARITH_TAC; ALL_TAC]) THEN
    TRC "c2c" (SUBGOAL_THEN `mld_ntt_block (mld_zeta (2 EXP l + n)) (2 * len * n) len
                              (mld_ntt_blocks l n r) j = mld_ntt_blocks l n r j`
      (fun th -> REWRITE_TAC[th]) THENL
      [MATCH_MP_TAC NTT_BLOCK_OUT THEN ASM_ARITH_TAC; ALL_TAC]) THEN
    TRC "c2d" (FIRST_X_ASSUM MATCH_MP_TAC) THEN TRC "c2e" ASM_ARITH_TAC]);;

(*** The lanes of the vectors ***)

let JL0 = prove(`!A B:int32. word_subword (word_subword (word_join A B:int64) (0,128):int128) (0,32):int32 = B`, REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;
let JL1 = prove(`!A B:int32. word_subword (word_subword (word_join A B:int64) (0,128):int128) (32,32):int32 = A`, REPEAT GEN_TAC THEN CONV_TAC WORD_BLAST);;
let SUBW_USHR = prove(`!X:int64. word_subword (word_ushr X 32) (0,32):int32 = word_zx(word_ishr X 32)`, GEN_TAC THEN CONV_TAC WORD_BLAST);;
let SUBW_ZX = prove(`!P:int64. word_subword P (0,32):int32 = word_zx P`, GEN_TAC THEN CONV_TAC WORD_BLAST);;
let MVL = prove(`!P:int64. word_subword (word_add (word_mul (word_sx (word_subword (word_ushr (word (0 + val P * 252236767799803904):int64) 32) (0,32):int32):int64) (word 18446744073701171199)) P) (32,32):int32 = mld_montgomery_reduce P`,
  GEN_TAC THEN REWRITE_TAC[SUBW_USHR; NTT_QT; GSYM SUBW_ZX] THEN
  REWRITE_TAC[MONTRED_VEC_LANE]);;

(*** ld4 and st4 of the 32-bit lanes ***)

let LD4Q = prove
 (`!(a:int64) (m:num->int32) i s0:armstate.
   (!k. k < 16 ==> read (memory :> bytes32 (word_add a (word (64 * i + 4 * k)))) s0 = m (16 * i + k))
   ==> read (memory :> bytes128 (word_add a (word (64 * i)))) s0 =
         word_join (word_join (m (16*i+3)) (m (16*i+2)):int64) (word_join (m (16*i+1)) (m (16*i)):int64) /\
       read (memory :> bytes128 (word_add a (word (64 * i + 16)))) s0 =
         word_join (word_join (m (16*i+7)) (m (16*i+6)):int64) (word_join (m (16*i+5)) (m (16*i+4)):int64) /\
       read (memory :> bytes128 (word_add a (word (64 * i + 32)))) s0 =
         word_join (word_join (m (16*i+11)) (m (16*i+10)):int64) (word_join (m (16*i+9)) (m (16*i+8)):int64) /\
       read (memory :> bytes128 (word_add a (word (64 * i + 48)))) s0 =
         word_join (word_join (m (16*i+15)) (m (16*i+14)):int64) (word_join (m (16*i+13)) (m (16*i+12)):int64)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o CONV_RULE(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT); el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT); PTR_ADD_G; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;
let DEIL_GEN = prove
 (`!z:512 word j. j < 4 ==> (word_subdeinterleave 4 32 z j : int128 =
     word_join (word_join (word_subword z ((12 + j) * 32, 32):int32) (word_subword z ((8 + j) * 32, 32):int32):int64)
               (word_join (word_subword z ((4 + j) * 32, 32):int32) (word_subword z (j * 32, 32):int32):int64))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `j = 0 \/ j = 1 \/ j = 2 \/ j = 3` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[word_subdeinterleave] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OF_BITS; BIT_WORD_JOIN; BIT_WORD_SUBWORD; IN_ELIM_THM; DIMINDEX_128; DIMINDEX_64; DIMINDEX_32; DIMINDEX_512] THEN
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[LET_DEF; LET_END_DEF; MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;
let DEIL0 = CONV_RULE NUM_REDUCE_CONV (MP (SPECL [`z:512 word`;`0`] DEIL_GEN) (ARITH_RULE `0 < 4`));;
let DEIL1 = CONV_RULE NUM_REDUCE_CONV (MP (SPECL [`z:512 word`;`1`] DEIL_GEN) (ARITH_RULE `1 < 4`));;
let DEIL2 = CONV_RULE NUM_REDUCE_CONV (MP (SPECL [`z:512 word`;`2`] DEIL_GEN) (ARITH_RULE `2 < 4`));;
let DEIL3 = CONV_RULE NUM_REDUCE_CONV (MP (SPECL [`z:512 word`;`3`] DEIL_GEN) (ARITH_RULE `3 < 4`));;
let EL4 = prove(`!a b c d:A. EL 0 [a;b;c;d] = a /\ EL 1 [a;b;c;d] = b /\ EL 2 [a;b;c;d] = c /\ EL 3 [a;b;c;d] = d`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV num_CONV) THEN REWRITE_TAC[EL; HD; TL]);;
let ILV_GEN = prove
 (`!x1 x2 x3 x4:int128 k. k < 4 ==>
   (word_subword (word_interleave 32 [x1;x2;x3;x4]:512 word) (128 * k,128):int128 =
    word_join (word_join (word_subword x4 (k*32,32):int32) (word_subword x3 (k*32,32):int32):int64)
              (word_join (word_subword x2 (k*32,32):int32) (word_subword x1 (k*32,32):int32):int64))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `k = 0 \/ k = 1 \/ k = 2 \/ k = 3` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[word_interleave] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_OF_BITS; BIT_WORD_JOIN; BIT_WORD_SUBWORD; IN_ELIM_THM; DIMINDEX_128; DIMINDEX_64; DIMINDEX_32; DIMINDEX_512] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[BIT_WORD_OF_BITS; IN_ELIM_THM; DIMINDEX_512; LET_DEF; LET_END_DEF; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[EL4] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;
let ILV0 = CONV_RULE NUM_REDUCE_CONV (MP (SPECL [`x1:int128`;`x2:int128`;`x3:int128`;`x4:int128`;`0`] ILV_GEN) (ARITH_RULE `0 < 4`));;
let ILV1 = CONV_RULE NUM_REDUCE_CONV (MP (SPECL [`x1:int128`;`x2:int128`;`x3:int128`;`x4:int128`;`1`] ILV_GEN) (ARITH_RULE `1 < 4`));;
let ILV2 = CONV_RULE NUM_REDUCE_CONV (MP (SPECL [`x1:int128`;`x2:int128`;`x3:int128`;`x4:int128`;`2`] ILV_GEN) (ARITH_RULE `2 < 4`));;
let ILV3 = CONV_RULE NUM_REDUCE_CONV (MP (SPECL [`x1:int128`;`x2:int128`;`x3:int128`;`x4:int128`;`3`] ILV_GEN) (ARITH_RULE `3 < 4`));;

(*** The arithmetic of loop 11 ***)

let L11_STMT = `!(mem:num->int32) (m:num->int32) i.
     i < 16 /\
     (!c. c < 4
          ==> mem (16 * i + 4 * c) =
              word_add (m (16 * i + 4 * c))
                       (mld_fqmul (m (16 * i + 4 * c + 2))
                                  (mld_zeta (64 + 4 * i + c))) /\
              mem (16 * i + 4 * c + 1) =
              word_add (m (16 * i + 4 * c + 1))
                       (mld_fqmul (m (16 * i + 4 * c + 3))
                                  (mld_zeta (64 + 4 * i + c))) /\
              mem (16 * i + 4 * c + 2) =
              word_sub (m (16 * i + 4 * c))
                       (mld_fqmul (m (16 * i + 4 * c + 2))
                                  (mld_zeta (64 + 4 * i + c))) /\
              mem (16 * i + 4 * c + 3) =
              word_sub (m (16 * i + 4 * c + 1))
                       (mld_fqmul (m (16 * i + 4 * c + 3))
                                  (mld_zeta (64 + 4 * i + c)))) /\
     (!j. j < 256 /\ (j < 16 * i \/ 16 * i + 16 <= j)
          ==> mem j = mld_ntt_blocks 6 (4 * i) m j)
     ==> !j. j < 256 ==> mem j = mld_ntt_blocks 6 (4 * (i + 1)) m j`;;
let LANE11 = prove(L11_STMT,


  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `16 * i <= j /\ j < 16 * i + 16` THENL
   [SUBGOAL_THEN `?c e. c < 4 /\ e < 4 /\ j = 16 * i + 4 * c + e` MP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`(j - 16 * i) DIV 4`; `(j - 16 * i) MOD 4`] THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:num` (X_CHOOSE_THEN `e:num` STRIP_ASSUME_TAC)) THEN
    MP_TAC(SPECL [`6`; `2`; `4 * (i + 1)`; `4 * i + c`; `m:num->int32`; `j:num`]
                 NTT_BLOCKS_AT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:num` o check (fun th -> free_in `mld_fqmul` (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
    SUBGOAL_THEN `mld_zeta (2 EXP 6 + (4 * i + c)) = mld_zeta (64 + 4 * i + c)`
      SUBST1_TAC THENL [AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `e = 0 \/ e = 1 \/ e = 2 \/ e = 3` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THENL
     [TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhand(concl th) = `j:num`))) THEN REWRITE_TAC[ADD_CLAUSES] THEN MP_TAC(SPECL [`mld_zeta (64 + 4 * i + c)`; `m:num->int32`; `16 * i + 4 * c`; `2 * 2 * (4 * i + c)`; `2`] NTT_BLK_LO) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[ARITH_RULE `(16 * i + 4 * c) + 2 = 16 * i + 4 * c + 2`];
      TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhand(concl th) = `j:num`))) THEN MP_TAC(SPECL [`mld_zeta (64 + 4 * i + c)`; `m:num->int32`; `16 * i + 4 * c + 1`; `2 * 2 * (4 * i + c)`; `2`] NTT_BLK_LO) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[ARITH_RULE `(16 * i + 4 * c + 1) + 2 = 16 * i + 4 * c + 3`];
      TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhand(concl th) = `j:num`))) THEN MP_TAC(SPECL [`mld_zeta (64 + 4 * i + c)`; `m:num->int32`; `16 * i + 4 * c + 2`; `2 * 2 * (4 * i + c)`; `2`] NTT_BLK_HI) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[ARITH_RULE `(16 * i + 4 * c + 2) - 2 = 16 * i + 4 * c`];
      TRY(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) && lhand(concl th) = `j:num`))) THEN MP_TAC(SPECL [`mld_zeta (64 + 4 * i + c)`; `m:num->int32`; `16 * i + 4 * c + 3`; `2 * 2 * (4 * i + c)`; `2`] NTT_BLK_HI) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[ARITH_RULE `(16 * i + 4 * c + 3) - 2 = 16 * i + 4 * c + 1`]];
    SUBGOAL_THEN `mld_ntt_blocks 6 (4 * (i + 1)) m j = mld_ntt_blocks 6 (4 * i) m j` SUBST1_TAC THENL
     [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC] THEN
    ASM_CASES_TAC `j < 16 * i` THENL
     [MP_TAC(SPECL [`6`; `2`; `4 * (i + 1)`; `j DIV 4`; `m:num->int32`; `j:num`]
                   NTT_BLOCKS_AT) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      MP_TAC(SPECL [`6`; `2`; `4 * i`; `j DIV 4`; `m:num->int32`; `j:num`]
                   NTT_BLOCKS_AT) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN REFL_TAC;
      MP_TAC(SPECL [`6`; `2`; `4 * (i + 1)`; `m:num->int32`; `j:num`]
                   NTT_BLOCKS_BELOW) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ASM_ARITH_TAC]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      MP_TAC(SPECL [`6`; `2`; `4 * i`; `m:num->int32`; `j:num`]
                   NTT_BLOCKS_BELOW) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ASM_ARITH_TAC]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN REFL_TAC]]);;

let CNT11 = prove(`!i. i < 16 ==> (val (word_add (word (16 * i)) (word 18446744073709551376):int64) = 0 <=> ~(i + 1 < 16))`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

(*** Loop 12: ld1/st1 of 256 bits, one block of two coefficients per butterfly ***)

let LD256 = prove
 (`!(a:int64) (m:num->int32) i s0:armstate.
   (!k. k < 8 ==> read (memory :> bytes32 (word_add a (word (32 * i + 4 * k)))) s0 = m (8 * i + k))
   ==> read (memory :> bytes256 (word_add a (word (32 * i)))) s0 =
       word_join (word_join (word_join (m (8 * i + 7)) (m (8 * i + 6)):int64) (word_join (m (8 * i + 5)) (m (8 * i + 4)):int64):int128) (word_join (word_join (m (8 * i + 3)) (m (8 * i + 2)):int64) (word_join (m (8 * i + 1)) (m (8 * i)):int64):int128)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o CONV_RULE(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[el 0 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT); el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT); el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT); PTR_ADD_G; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;
let LDZ = prove
 (`!(b:int64) (z:num->int32) n s0:armstate.
   (!k. k < 4 ==> read (memory :> bytes32 (word_add b (word (4 * n + 4 * k)))) s0 = z (n + k))
   ==> read (memory :> bytes128 (word_add b (word (4 * n)))) s0 =
       word_join (word_join (z (n + 3)) (z (n + 2)):int64) (word_join (z (n + 1)) (z n):int64)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o CONV_RULE(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
  REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT); el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT); PTR_ADD_G; GSYM ADD_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let NORM = RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV));;

let L12_TM = parse_term
   "exists f_events.
      forall e a (m:num->int32) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALL (nonoverlapping (a,1024)) [(word pc,libmldsa_size)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                  read PC s = word (pc + mldsa_poly_ntt_loop12) /\\
                  read X0 s = a /\\ read X9 s = word 0 /\\
                  read X8 s = word (pc + rodata_mld_zetas) /\\
                  read X10 s = word 252236767799803904 /\\
                  read Q0 s = word 18410750461054296063 /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s = m i) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + mldsa_poly_ntt_loop12_exit) /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                           mld_ntt_blocks 7 128 m i) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a pc /\\
                     memaccess_inbounds e2
                      [a,1024; word(pc + rodata_mld_zetas),1024] [a,1024]))
             (MAYCHANGE [PC; X0; X9; X11; X12; X13; X14] ,, MAYCHANGE [Q1; Q2; Q3; Q4; Q5; Q6] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a,1024)])";;
let LANE12 = prove
 (`!(mem:num->int32) (m:num->int32) i.
     i < 32 /\
     (!c. c < 4
          ==> mem (8 * i + 2 * c) =
              word_add (m (8 * i + 2 * c))
                       (mld_fqmul (m (8 * i + 2 * c + 1))
                                  (mld_zeta (128 + 4 * i + c))) /\
              mem (8 * i + 2 * c + 1) =
              word_sub (m (8 * i + 2 * c))
                       (mld_fqmul (m (8 * i + 2 * c + 1))
                                  (mld_zeta (128 + 4 * i + c)))) /\
     (!j. j < 256 /\ (j < 8 * i \/ 8 * i + 8 <= j)
          ==> mem j = mld_ntt_blocks 7 (4 * i) m j)
     ==> !j. j < 256 ==> mem j = mld_ntt_blocks 7 (4 * (i + 1)) m j`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `8 * i <= j /\ j < 8 * i + 8` THENL
   [SUBGOAL_THEN `?c. c < 4 /\ (j = 8 * i + 2 * c \/ j = 8 * i + 2 * c + 1)`
      MP_TAC THENL
     [EXISTS_TAC `(j - 8 * i) DIV 2` THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:num` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    MP_TAC(SPECL [`7`; `1`; `4 * (i + 1)`; `4 * i + c`; `m:num->int32`; `j:num`]
                 NTT_BLOCKS_AT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:num` o check (fun th -> free_in `mld_fqmul` (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
    SUBGOAL_THEN `mld_zeta (2 EXP 7 + (4 * i + c)) = mld_zeta (128 + 4 * i + c)`
      SUBST1_TAC THENL [AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [MP_TAC(SPECL [`mld_zeta (128 + 4 * i + c)`; `m:num->int32`; `j:num`; `2 * 1 * (4 * i + c)`; `1`] NTT_BLK_LO) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH_RULE `8 * i + 2 * c + 1 = (8 * i + 2 * c) + 1`];
      MP_TAC(SPECL [`mld_zeta (128 + 4 * i + c)`; `m:num->int32`; `j:num`; `2 * 1 * (4 * i + c)`; `1`] NTT_BLK_HI) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[ARITH_RULE `(8 * i + 2 * c + 1) - 1 = 8 * i + 2 * c`]];
    SUBGOAL_THEN `mld_ntt_blocks 7 (4 * (i + 1)) m j = mld_ntt_blocks 7 (4 * i) m j` SUBST1_TAC THENL
     [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC] THEN
    ASM_CASES_TAC `j < 8 * i` THENL
     [MP_TAC(SPECL [`7`; `1`; `4 * (i + 1)`; `j DIV 2`; `m:num->int32`; `j:num`]
                   NTT_BLOCKS_AT) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      MP_TAC(SPECL [`7`; `1`; `4 * i`; `j DIV 2`; `m:num->int32`; `j:num`]
                   NTT_BLOCKS_AT) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN REFL_TAC;
      MP_TAC(SPECL [`7`; `1`; `4 * (i + 1)`; `m:num->int32`; `j:num`]
                   NTT_BLOCKS_BELOW) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ASM_ARITH_TAC]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      MP_TAC(SPECL [`7`; `1`; `4 * i`; `m:num->int32`; `j:num`]
                   NTT_BLOCKS_BELOW) THEN
      ANTS_TAC THENL [REPEAT CONJ_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ASM_ARITH_TAC]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN REFL_TAC]]);;

let CNT12 = prove(`!i. i < 32 ==> (val (word_add (word (16 * i)) (word 18446744073709551120):int64) = 0 <=> ~(i + 1 < 32))`,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let NTT_L12_TAC =
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (pc:num).
      APPEND (f_ev_epil a pc)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop a pc i)) (f_ev_prol a pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `m:num->int32`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst NTT_NEON_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mldsa_poly_ntt_loop12` `pc + mldsa_poly_ntt_loop12_exit`
   `\i s. read X0 s = word_add a (word (32 * i)) /\
          read X9 s = word (16 * i) /\
          read X8 s = word (pc + rodata_mld_zetas) /\
          read X10 s = word 252236767799803904 /\
          read Q0 s = word 18410750461054296063 /\
          (!j. j < 256 ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                           mld_ntt_blocks 7 (4 * i) m j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The head ***)

    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0; CONJUNCT1 mld_ntt_blocks] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The body ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLD_ZETAS_LOADED o MATCH_MP NTT_ZETAS_IMG) THEN
    SUBGOAL_THEN `!k. k < 8 ==> read (memory :> bytes32 (word_add a (word (32 * i + 4 * k)))) s0 = (m:num->int32) (8 * i + k)` ASSUME_TAC THENL
     [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `8 * i + k` o check (fun th -> is_forall(concl th) && free_in `mld_ntt_blocks` (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`7`; `1`; `4 * i`; `m:num->int32`; `8 * i + k`] NTT_BLOCKS_BELOW) THEN
      ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `word (4 * (8 * i + k)):int64 = word (32 * i + 4 * k)` SUBST1_TAC THENL [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN ACCEPT_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> ASSUME_TAC(MP (SPECL [`a:int64`; `m:num->int32`; `i:num`; `s0:armstate`] LD256) th)) THEN
    SUBGOAL_THEN `!k. k < 4 ==> read (memory :> bytes32 (word_add (word (pc + 247592)) (word (4 * (128 + 4 * i) + 4 * k)))) s0 = mld_zeta ((128 + 4 * i) + k)` ASSUME_TAC THENL
     [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `(128 + 4 * i) + k` o check (fun th -> is_forall(concl th) && free_in `mld_zeta` (concl th) && not(free_in `m:num->int32` (concl th)))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `word (4 * ((128 + 4 * i) + k)):int64 = word (4 * (128 + 4 * i) + 4 * k)` SUBST1_TAC THENL [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN ACCEPT_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> ASSUME_TAC(MP (SPECL [`word (pc + 247592):int64`; `mld_zeta`; `128 + 4 * i`; `s0:armstate`] LDZ) th)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `4 * (128 + 4 * i) = 16 * i + 512`; GSYM ADD_ASSOC]) THEN
    SUBGOAL_THEN `!j. j < 8 * i ==> read (memory :> bytes32 (word_add a (word (4 * j)))) s0 = mld_ntt_blocks 7 (4 * i) m j` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) && free_in `mld_ntt_blocks` (concl th) && not(free_in `m:num->int32` (concl th) && false))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC]; ALL_TAC] THEN
    SUBGOAL_THEN `!j. 8 * i + 8 <= j /\ j < 256 ==> read (memory :> bytes32 (word_add a (word (4 * j)))) s0 = mld_ntt_blocks 7 (4 * i) m j` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) && free_in `mld_ntt_blocks` (concl th) && is_imp(snd(dest_forall(concl th))) && not(is_conj(fst(dest_imp(snd(dest_forall(concl th)))))) && not(is_binary "<" (fst(dest_imp(snd(dest_forall(concl th)))))  && free_in `i:num` (fst(dest_imp(snd(dest_forall(concl th)))))))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC]; ALL_TAC] THEN
    TRC "steps" (MAP_EVERY (fun k -> ARM_STEPS_TAC NTT_NEON_EXEC (k--k) THEN NORM) (1--29)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[JL0; JL1; MVL]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[el 0 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT); el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT); el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)]) THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[PTR_ADD_G; GSYM ADD_ASSOC]) THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)) THEN
    FIRST_X_ASSUM(fun th -> if is_conj(concl th) && free_in `s29:armstate` (concl th) then STRIP_ASSUME_TAC th else NO_TAC) THEN
    TRC "final" (ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]) THEN
    REWRITE_TAC[MP (SPEC `i:num` CNT12) (ASSUME `i < 32`)] THEN
    TRC "pc" (CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC]) THEN
    TRC "ptr" (CONJ_TAC THENL [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC]) THEN
    TRC "x9" (CONJ_TAC THENL [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(CONV_RULE(DEPTH_CONV BETA_CONV)
        (SPECL [`\j. read (memory :> bytes32 (word_add a (word (4 * j)))) s29`; `m:num->int32`; `i:num`] LANE12)) THEN
      REPEAT CONJ_TAC THENL
       [TRC "m1" (FIRST_ASSUM ACCEPT_TAC);
        TRC "m2" (CONV_TAC(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
        REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; ADD_CLAUSES] THEN
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES] THEN
        TRC "m2b" (ASM_REWRITE_TAC[mld_fqmul]);
        TRC "m3a" (X_GEN_TAC `j:num` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
        TRC "m3b" (FIRST_X_ASSUM DISJ_CASES_TAC) THENL
         [FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term (fun t -> t = `j < 8 * i`)) (concl th) then MP_TAC(SPEC `j:num` th) else NO_TAC) THEN
          ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC];
          FIRST_ASSUM(fun th -> if is_forall(concl th) && can (find_term (fun t -> t = `8 * i + 8 <= j`)) (concl th) then MP_TAC(SPEC `j:num` th) else NO_TAC) THEN
          ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC]]];
      DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The exit ***)

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV)) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC];;

let NTT_LOOP12 = prove(L12_TM, NTT_L12_TAC);;

(*** Loop 11: ld4/st4, one lane per block of four coefficients ***)

let L11L_TM = parse_term
   "exists f_events.
      forall e a (m:num->int32) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALL (nonoverlapping (a,1024)) [(word pc,libmldsa_size)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                  read PC s = word (pc + mldsa_poly_ntt_loop11) /\\
                  read X11 s = a /\\ read X9 s = word 0 /\\
                  read X8 s = word (pc + rodata_mld_zetas) /\\
                  read X10 s = word 252236767799803904 /\\
                  read Q0 s = word 18410750461054296063 /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s = m i) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + mldsa_poly_ntt_loop11_exit) /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                           mld_ntt_blocks 6 64 m i) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a pc /\\
                     memaccess_inbounds e2
                      [a,1024; word(pc + rodata_mld_zetas),1024] [a,1024]))
             (MAYCHANGE [PC; X1; X9; X11; X12; X13; X14; X15; X16; X17; X18] ,, MAYCHANGE [Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q17; Q18; Q19; Q20] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a,1024)])";;

let NTT_L11_TAC =
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (pc:num).
      APPEND (f_ev_epil a pc)
       (APPEND (ENUMERATEL 16 (\i. f_ev_loop a pc i)) (f_ev_prol a pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `m:num->int32`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst NTT_NEON_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `16` `pc + mldsa_poly_ntt_loop11` `pc + mldsa_poly_ntt_loop11_exit`
   `\i s. read X11 s = word_add a (word (64 * i)) /\
          read X9 s = word (16 * i) /\
          read X8 s = word (pc + rodata_mld_zetas) /\
          read X10 s = word 252236767799803904 /\
          read Q0 s = word 18410750461054296063 /\
          (!j. j < 256 ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                           mld_ntt_blocks 6 (4 * i) m j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0; CONJUNCT1 mld_ntt_blocks] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLD_ZETAS_LOADED o MATCH_MP NTT_ZETAS_IMG) THEN
    SUBGOAL_THEN `!k. k < 16 ==> read (memory :> bytes32 (word_add a (word (64 * i + 4 * k)))) s0 = (m:num->int32) (16 * i + k)` ASSUME_TAC THENL
     [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `16 * i + k` o check (fun th -> is_forall(concl th) && free_in `mld_ntt_blocks` (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`6`; `2`; `4 * i`; `m:num->int32`; `16 * i + k`] NTT_BLOCKS_BELOW) THEN
      ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `word (4 * (16 * i + k)):int64 = word (64 * i + 4 * k)` SUBST1_TAC THENL [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN ACCEPT_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> STRIP_ASSUME_TAC(MP (SPECL [`a:int64`; `m:num->int32`; `i:num`; `s0:armstate`] LD4Q) th)) THEN
    SUBGOAL_THEN `!k. k < 4 ==> read (memory :> bytes32 (word_add (word (pc + 247592)) (word (4 * (64 + 4 * i) + 4 * k)))) s0 = mld_zeta ((64 + 4 * i) + k)` ASSUME_TAC THENL
     [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `(64 + 4 * i) + k` o check (fun th -> is_forall(concl th) && free_in `mld_zeta` (concl th) && not(free_in `m:num->int32` (concl th)))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `word (4 * ((64 + 4 * i) + k)):int64 = word (4 * (64 + 4 * i) + 4 * k)` SUBST1_TAC THENL [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN ACCEPT_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> ASSUME_TAC(MP (SPECL [`word (pc + 247592):int64`; `mld_zeta`; `64 + 4 * i`; `s0:armstate`] LDZ) th)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `4 * (64 + 4 * i) = 16 * i + 256`; GSYM ADD_ASSOC]) THEN
    SUBGOAL_THEN `!j. j < 16 * i ==> read (memory :> bytes32 (word_add a (word (4 * j)))) s0 = mld_ntt_blocks 6 (4 * i) m j` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> try free_in `mld_ntt_blocks` (concl th) && fst(dest_imp(snd(dest_forall(concl th)))) = `j:num < 256` with _ -> false)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC]; ALL_TAC] THEN
    SUBGOAL_THEN `!j. 16 * i + 16 <= j /\ j < 256 ==> read (memory :> bytes32 (word_add a (word (4 * j)))) s0 = mld_ntt_blocks 6 (4 * i) m j` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> try free_in `mld_ntt_blocks` (concl th) && fst(dest_imp(snd(dest_forall(concl th)))) = `j:num < 256` with _ -> false)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC]; ALL_TAC] THEN
    TRC "steps" (MAP_EVERY (fun k -> ARM_STEPS_TAC NTT_NEON_EXEC (k--k) THEN NORM) (1--51)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[DEIL0; DEIL1; DEIL2; DEIL3]) THEN
    NORM THEN
    RULE_ASSUM_TAC(REWRITE_RULE[JL0; JL1; MVL]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ILV0; ILV1; ILV2; ILV3]) THEN
    NORM THEN
    RULE_ASSUM_TAC(REWRITE_RULE[el 0 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT); el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT); el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)]) THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[PTR_ADD_G; GSYM ADD_ASSOC]) THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)) THEN
    REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && free_in `s51:armstate` (concl th) && free_in `memory` (concl th) && not(free_in `ensures` (concl th)) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
    TRC "final" (ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]) THEN
    REWRITE_TAC[MP (SPEC `i:num` CNT11) (ASSUME `i < 16`)] THEN
    TRC "pc" (CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC]) THEN
    TRC "ptr" (CONJ_TAC THENL [REWRITE_TAC[WORD_RULE `word_add (word_add a (word x)) (word y) = word_add a (word (x + y))`] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC]) THEN
    TRC "x9" (CONJ_TAC THENL [REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(CONV_RULE(DEPTH_CONV BETA_CONV)
        (SPECL [`\j. read (memory :> bytes32 (word_add a (word(4 * j)))) s51`; `m:num->int32`; `i:num`] LANE11)) THEN
      REPEAT CONJ_TAC THENL
       [TRC "m1" (FIRST_ASSUM ACCEPT_TAC);
        TRC "m2" (CONV_TAC(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
        REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC; ADD_CLAUSES] THEN
        CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES] THEN
        TRC "m2b" (ASM_REWRITE_TAC[mld_fqmul]);
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

let NTT_LOOP11 = prove(L11L_TM, NTT_L11_TAC);;
