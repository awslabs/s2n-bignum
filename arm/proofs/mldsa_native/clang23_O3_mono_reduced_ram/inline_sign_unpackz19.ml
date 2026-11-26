(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The polyz_unpack loops for gamma1 = 2^19 that clang 23 -O3 has inlined    *)
(* into mldsa65_verify_internal and mldsa87_verify_internal                  *)
(* (polyvecl_unpack_z, one loop per polynomial of z): 20 bytes of the input  *)
(* and 8 coefficients per iteration, 32 iterations. The code inserts the     *)
(* bytes into lanes of five vectors (LD1 of a byte), spreads them into the   *)
(* 20-bit fields with UXTL, BIC, USHR, AND, SHL, SLI and ORR, subtracts the  *)
(* fields from 2^19 and stores the two vectors of four coefficients with     *)
(* ST2. The input pointer is a + 19 at the head (the loop reads the bytes    *)
(* at -19 .. 0, as polyt1_unpack does) and the output is at r + off, where   *)
(* the offset off counts from k0 in steps of 32 (k0 = 1024 * polynomial).    *)
(* The vector constants are in registers: QM = 0x000000ff in each lane and   *)
(* QG = 2^19 in each lane. The loop inserts bytes into the five vectors      *)
(* without having defined them, which the lemma treats as unknown values.    *)
(* The loop bound is an immediate, or in a register (bnd) for the loops of   *)
(* the polynomials after the fifth.                                          *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_unpack.ml";;

(*** A 32-bit lane of a vector expression: the subword pushed through the ***)
(*** bitwise operations and the joins of the lanes (the simulation leaves  ***)
(*** the 128-bit results of the vector instructions as joins of lanes)     ***)

let rec Z19_LANE_CONV tm =
  let isop name t = try fst(dest_const(fst(strip_comb t))) = name
                    with Failure _ -> false in
  if not(isop "word_subword" tm) then REFL tm else
  let x = lhand tm in
  if isop "word_or" x then
    (REWR_CONV WORD_SUBWORD_OR THENC BINOP_CONV Z19_LANE_CONV) tm
  else if isop "word_and" x then
    (REWR_CONV WORD_SUBWORD_AND THENC BINOP_CONV Z19_LANE_CONV) tm
  else if isop "word_xor" x then
    (REWR_CONV WORD_SUBWORD_XOR THENC BINOP_CONV Z19_LANE_CONV) tm
  else
    (try (WORD_SIMPLE_SUBWORD_CONV THENC
          (fun t -> if isop "word_subword" t && not(t = tm)
                    then Z19_LANE_CONV t else REFL t)) tm
     with Failure _ -> REFL tm);;

let Z19_LANES_CONV = TOP_DEPTH_CONV (CHANGED_CONV Z19_LANE_CONV);;

(*** The 32-bit facts about the 256-bit store of ST2 at r + e, with the     ***)
(*** constants of the offsets added up, each as one coefficient             ***)

let INLINE_ST2_LANES_TAC (r:term) =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    try let l,_ = dest_eq c in
        let comp = rand(rator l) in
        let bytesf,addr = dest_comb(rand comp) in
        let a0,_ = dest_binop `word_add:int64->int64->int64` addr in
        if fst(dest_const bytesf) = "bytes256" && a0 = r then
          STRIP_ASSUME_TAC
           (CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                      ONCE_DEPTH_CONV
                       (CHANGED_CONV(REWRITE_CONV[GSYM ADD_ASSOC]) THENC
                        NUM_REDUCE_CONV))
              (CONV_RULE(READ_MEMORY_SPLIT_CONV 3) th))
        else NO_TAC
    with Failure _ -> NO_TAC)) THEN
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c && not(is_forall c) && free_in r (lhs c) &&
       can (find_term (fun t -> try fst(dest_const t) = "bytes32"
                                with Failure _ -> false)) (lhs c)
    then CONV_RULE(RAND_CONV(SIMD_SIMPLIFY_CONV [] THENC Z19_LANES_CONV)) th
    else th);;

(*** The coefficients of an iteration: 8 per 20 bytes, two per 5 bytes ***)

let INLINE_DIV2_8 = prove
 (`(!i k. (8 * i + k) DIV 2 = 4 * i + k DIV 2) /\ (!i. (8 * i) DIV 2 = 4 * i)`,
  CONJ_TAC THEN REPEAT GEN_TAC THENL
   [ONCE_REWRITE_TAC[ARITH_RULE `8 * i + k = (4 * i) * 2 + k`];
    ONCE_REWRITE_TAC[ARITH_RULE `8 * i = 2 * (4 * i)`]] THEN
  SIMP_TAC[DIV_MULT_ADD; DIV_MULT; ARITH_EQ]);;

let INLINE_MOD2_8 = prove
 (`(!i k. (8 * i + k) MOD 2 = k MOD 2) /\ (!i. (8 * i) MOD 2 = 0)`,
  CONJ_TAC THEN REPEAT GEN_TAC THENL
   [ONCE_REWRITE_TAC[ARITH_RULE `8 * i + k = (4 * i) * 2 + k`] THEN
    REWRITE_TAC[MOD_MULT_ADD];
    ONCE_REWRITE_TAC[ARITH_RULE `8 * i = 2 * (4 * i)`] THEN
    SIMP_TAC[MOD_MULT; ARITH_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* The two loops of mldsa87_verify_internal for the sixth and seventh        *)
(* polynomials count the offset xoff up from -1024 to 0 (ADDS, B.NE) and     *)
(* form the store address as r + xoff + bnd, with bnd = k0 + 1024 in a      *)
(* register ("neg" loops): the same body with that bookkeeping. The          *)
(* simulation rewrites the store address to r + (k0 + 32 * i) after each     *)
(* step (INLINE_Z19N_ADDR).                                                  *)
(* ------------------------------------------------------------------------- *)

let INLINE_Z19N_START = "18446744073709550592";;

let INLINE_Z19N_ADDR k0 =
  let n = mk_small_numeral in
  let ns = [mk_numeral(Num.num_of_string INLINE_Z19N_START),`N:num`;
            n (k0 + 1024),`K:num`; n k0,`K0:num`] in
  prove(vsubst ns
   `!(r:int64) i. word_add (word_add r (word (N + 32 * i))) (word K) =
                  word_add r (word (K0 + 32 * i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  AP_TERM_TAC THEN REWRITE_TAC[WORD_EQ; DIMINDEX_64; CONG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE(vsubst ns
   `(N + 32 * i) + K = 1 * 18446744073709551616 + (K0 + 32 * i)`);
   MOD_MULT_ADD]);;

(* ------------------------------------------------------------------------- *)
(* The statement and the proof of one instance: the input pointer xin, the   *)
(* base xbase (= r) and the offset xoff of the output, the bound register    *)
(* (or "" when the bound is an immediate), the vector constants (QM, QG) and *)
(* the registers the loop writes. For a neg loop the statement has xoff      *)
(* from -1024 at the head and does not give it at the exit.                  *)
(* ------------------------------------------------------------------------- *)

let INLINE_Z19_GEN_STMT mc loop exit k0 neg (xin,xbase,xoff,xbnd) (qm,qg)
                        (mods:string list) =
  let qmods,xmods = partition (fun r -> String.get r 0 = 'Q') mods in
  let c0 = if neg then INLINE_Z19N_START else string_of_int k0 in
  let cpost = if neg then ""
              else Printf.sprintf "read %s s = word %d /\\" xoff (k0 + 1024) in
  let out = if k0 = 0 then "r" else Printf.sprintf "word_add r (word %d)" k0 in
  let outi = if k0 = 0 then "word_add r (word(4 * i))"
             else Printf.sprintf "word_add r (word(%d + 4 * i))" k0 in
  let bnd = if xbnd = "" then ""
            else Printf.sprintf "read %s s = word %d /\\ " xbnd (k0 + 1024) in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e r a (b:num->byte) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALL (nonoverlapping (%s,1024)) [(word pc,libmldsa_size); (a,640)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read %s s = word_add a (word 19) /\\ read %s s = r /\\
                  read %s s = word %s /\\ %s
                  read %s s = word 0x000000ff000000ff000000ff000000ff /\\
                  read %s s = word 0x00080000000800000008000000080000 /\\
                  (!j. j < 640
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\
                  read %s s = word_add a (word 659) /\\ read %s s = r /\\
                  %s
                  (!i. i < 256
                       ==> read(memory :> bytes32(%s)) s =
                           mld_polyz_unpack_19 b i) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events r a pc /\\
                     memaccess_inbounds e2 [a,640; %s,1024] [%s,1024]))
             (MAYCHANGE [PC; %s] ,, MAYCHANGE [%s] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(%s,1024)])"
   out mc loop xin xbase xoff c0 bnd qm qg
   exit xin xbase cpost outi out out
   (String.concat "; " xmods) (String.concat "; " qmods) out);;

let INLINE_Z19_STMT mc loop exit k0 regs qs mods =
  INLINE_Z19_GEN_STMT mc loop exit k0 false regs qs mods;;

let INLINE_POLYZ19_GEN_LOOP mc exec loop exit k0 neg nsteps
                        (xin,xbase,xoff,xbnd) (qm,qg) (qins:string list)
                        (mods:string list) =
  let outj = if k0 = 0 then "word_add r (word(4 * j))"
             else Printf.sprintf "word_add r (word(%d + 4 * j))" k0 in
  let offi = if neg then INLINE_Z19N_START ^ " + 32 * i"
             else if k0 = 0 then "32 * i" else Printf.sprintf "%d + 32 * i" k0 in
  let bnd = if xbnd = "" then ""
            else Printf.sprintf "read %s s = word %d /\\ " xbnd (k0 + 1024) in
  let steps = if neg then INLINE_STEPS_TAC exec [INLINE_Z19N_ADDR k0] nsteps
              else ARM_STEPS_TAC exec (1--nsteps) in
  let cnt = if neg then [ARITH_RULE (parse_term(Printf.sprintf
                          "%s + 32 * (i + 1) = (%s + 32 * i) + 32"
                          INLINE_Z19N_START INLINE_Z19N_START))]
            else [] in
  INLINE_CHUNK_PROVE
   (INLINE_Z19_GEN_STMT mc loop exit k0 neg (xin,xbase,xoff,xbnd) (qm,qg) mods)
   "(r:int64) (a:int64)" "r a" ["r:int64"; "a:int64"; "b:num->byte"; "pc:num"]
   32 exec loop exit
   (Printf.sprintf
     "\\i s. read %s s = word_add a (word (20 * i + 19)) /\\
            read %s s = r /\\ read %s s = word (%s) /\\ %s
            read %s s = word 0x000000ff000000ff000000ff000000ff /\\
            read %s s = word 0x00080000000800000008000000080000 /\\
            (!j. j < 640
                 ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
            (!j. j < 8 * i
                 ==> read(memory :> bytes32(%s)) s =
                     mld_polyz_unpack_19 b j)"
     xin xbase xoff offi bnd qm qg outj)
   (CHUNK_INPUT_TAC `b:num->byte` 20 THEN
    INLINE_ALIAS_TAC INLINE_T1_ALIASES THEN
    MAP_EVERY (fun q ->
      let v = mk_var(String.lowercase_ascii q,`:int128`) in
      let r = mk_const(q,[]) in
      let rd = list_mk_comb(`read:(armstate,int128)component->armstate->int128`,
                            [r;`s0:armstate`]) in
      SUBGOAL_THEN (mk_exists(v,mk_eq(rd,v))) (X_CHOOSE_TAC v) THENL
       [EXISTS_TAC rd THEN REFL_TAC; ALL_TAC]) qins THEN
    steps THEN
    INLINE_ST2_LANES_TAC `r:int64` THEN
    INLINE_CHUNK_FINAL_TAC mld_polyz_unpack_19 `b:num->byte`
      [INLINE_DIV2_8; INLINE_MOD2_8]
      ([ARITH_RULE `32 * (i + 1) = 32 * i + 32`;
       ARITH_RULE (parse_term(Printf.sprintf
         "%d + 32 * (i + 1) = (%d + 32 * i) + 32" k0 k0));
       ARITH_RULE `20 * (i + 1) + 19 = (20 * i + 19) + 20`] @ cnt)
      INLINE_T1_EVENTS);;

let INLINE_POLYZ19_LOOP mc exec loop exit k0 nsteps regs qs qins mods =
  INLINE_POLYZ19_GEN_LOOP mc exec loop exit k0 false nsteps regs qs qins mods;;

(*** The instances: function, head, exit, k0, the number of steps, the    ***)
(*** input pointer, the base and the offset of the output, the bound     ***)
(*** register, the vector constants (mask, 2^19), the vectors the loop    ***)
(*** inserts bytes into, and the registers the loop writes               ***)

let INLINE_Z19_QINS = ["Q2";"Q3";"Q4";"Q5";"Q6"];;

let INLINE_Z19_MODS xs =
  xs @ ["Q2";"Q3";"Q4";"Q5";"Q6";"Q7"];;

let INLINE_POLYZ19_INSTANCES =
 ["mldsa65_verify_internal", "mldsa65_verify_internal_loop2",
  "mldsa65_verify_internal_loop2_exit", 0, 67,
  ("X9","X10","X8",""), INLINE_Z19_MODS ["X8";"X9";"X11";"X12";"X13";"X14";"X15"];
  "mldsa65_verify_internal", "mldsa65_verify_internal_loop3",
  "mldsa65_verify_internal_loop3_exit", 1024, 67,
  ("X8","X26","X9",""), INLINE_Z19_MODS ["X8";"X9";"X10";"X11";"X12";"X13";"X14"];
  "mldsa65_verify_internal", "mldsa65_verify_internal_loop4",
  "mldsa65_verify_internal_loop4_exit", 2048, 67,
  ("X8","X27","X9",""), INLINE_Z19_MODS ["X8";"X9";"X10";"X11";"X12";"X13";"X14"];
  "mldsa65_verify_internal", "mldsa65_verify_internal_loop5",
  "mldsa65_verify_internal_loop5_exit", 3072, 67,
  ("X8","X28","X9",""), INLINE_Z19_MODS ["X8";"X9";"X10";"X11";"X12";"X13";"X14"];
  "mldsa65_verify_internal", "mldsa65_verify_internal_loop6",
  "mldsa65_verify_internal_loop6_exit", 4096, 67,
  ("X8","X22","X9","X10"), INLINE_Z19_MODS ["X8";"X9";"X11";"X12";"X13";"X14";"X15"]];;

let INLINE_POLYZ19_OF_INSTANCE (fn,hl,el,k0,n,xs,mods) =
  INLINE_POLYZ19_LOOP "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc"
    (INLINE_LOOP_EXEC hl el) hl el k0 n xs ("Q0","Q1") INLINE_Z19_QINS mods;;

(*** mldsa87_verify_internal: loops 2 to 6 as those of mldsa65 (loop 5 with ***)
(*** the output base in X26), loops 7 and 8 neg loops                       ***)

let INLINE_POLYZ19_87_INSTANCES =
 ["mldsa87_verify_internal", "mldsa87_verify_internal_loop2",
  "mldsa87_verify_internal_loop2_exit", 0, 67,
  ("X9","X10","X8",""), INLINE_Z19_MODS ["X8";"X9";"X11";"X12";"X13";"X14";"X15"];
  "mldsa87_verify_internal", "mldsa87_verify_internal_loop3",
  "mldsa87_verify_internal_loop3_exit", 1024, 67,
  ("X8","X27","X9",""), INLINE_Z19_MODS ["X8";"X9";"X10";"X11";"X12";"X13";"X14"];
  "mldsa87_verify_internal", "mldsa87_verify_internal_loop4",
  "mldsa87_verify_internal_loop4_exit", 2048, 67,
  ("X8","X28","X9",""), INLINE_Z19_MODS ["X8";"X9";"X10";"X11";"X12";"X13";"X14"];
  "mldsa87_verify_internal", "mldsa87_verify_internal_loop5",
  "mldsa87_verify_internal_loop5_exit", 3072, 67,
  ("X8","X26","X9",""), INLINE_Z19_MODS ["X8";"X9";"X10";"X11";"X12";"X13";"X14"];
  "mldsa87_verify_internal", "mldsa87_verify_internal_loop6",
  "mldsa87_verify_internal_loop6_exit", 4096, 67,
  ("X8","X22","X9","X10"), INLINE_Z19_MODS ["X8";"X9";"X11";"X12";"X13";"X14";"X15"]];;

let INLINE_POLYZ19N_87_INSTANCES =
 ["mldsa87_verify_internal", "mldsa87_verify_internal_loop7",
  "mldsa87_verify_internal_loop7_exit", 5120, 67,
  ("X8","X23","X9","X10"), INLINE_Z19_MODS ["X8";"X9";"X11";"X12";"X13";"X14";"X15"];
  "mldsa87_verify_internal", "mldsa87_verify_internal_loop8",
  "mldsa87_verify_internal_loop8_exit", 6144, 67,
  ("X8","X24","X9","X10"), INLINE_Z19_MODS ["X8";"X9";"X11";"X12";"X13";"X14";"X15"]];;

let INLINE_POLYZ19N_OF_INSTANCE (fn,hl,el,k0,n,xs,mods) =
  INLINE_POLYZ19_GEN_LOOP "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc"
    (INLINE_LOOP_EXEC hl el) hl el k0 true n xs ("Q0","Q1") INLINE_Z19_QINS mods;;
