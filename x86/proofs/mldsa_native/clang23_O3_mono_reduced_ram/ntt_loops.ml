(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The loops of poly_ntt of the clang 23 build: the lemmas for the vectorised *)
(* loops of layers 1 to 3 (PMULUDQ) and for the scalar and mixed loops of     *)
(* layers 4 to 8, each from the head of a loop to its exit, as generators.   *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/ntt_tools.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_ntt_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The vectorised loops of layers 1 to 3. *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Vectorised butterfly loops: layers 1 to 3 of the forward NTT              *)
(* ------------------------------------------------------------------------- *)

let ntt_mc = "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc";;

(* the generators serve poly_ntt (at 0x7ab0) and poly_invntt_tomont (at 0x9150,
   with the inverse butterfly) according to these settings *)
let ntt_fn_base = par_local_ref (fun () -> 0x7ab0);;
let ntt_inverse = par_local_ref (fun () -> false);;

let pow2_64 = "18446744073709551616";;
let r0_of n = (* 2^64 - 16 n *)
  let p = power_num (num 2) (num 64) in
  string_of_num (sub_num p (num (16 * n)));;

let memq_s st b j =
  if b = 0 then Printf.sprintf "read (memory :> bytes32 (word_add a (word (4 * %s)))) %s" j st
  else Printf.sprintf "read (memory :> bytes32 (word_add a (word (%d + 4 * %s)))) %s" b j st;;
let memq = memq_s "s";;

(* the invariant at iteration i of the loop over the block (start, len) *)
let vec_inv start len ii =
  let x = 4 * start and y = 4 * (start + len) and u = 4 * (start + 2 * len) in
  let nab = 256 - (start + 2 * len) in
  String.concat " /\\\n  " (List.concat
   [ (if start > 0 then
       [Printf.sprintf "(!j. j < %d ==> %s = m j)" start (memq 0 "j")] else []);
     [Printf.sprintf "(!j. 4 * %s <= j /\\ j < %d ==> %s = m (%d + j))" ii len (memq x "j") start;
      Printf.sprintf "(!j. 4 * %s <= j /\\ j < %d ==> %s = m (%d + j))" ii len (memq y "j") (start + len);
      (if !(ntt_inverse ()) then
         Printf.sprintf "(!j. j < 4 * %s ==> %s = word_add (m (%d + j)) (m (%d + j)))" ii (memq x "j") start (start + len)
       else
         Printf.sprintf "(!j. j < 4 * %s ==> %s = word_add (m (%d + j)) (mld_fqmul (m (%d + j)) z))" ii (memq x "j") start (start + len));
      (if !(ntt_inverse ()) then
         Printf.sprintf "(!j. j < 4 * %s ==> %s = mld_fqmul (word_sub (m (%d + j)) (m (%d + j))) z)" ii (memq y "j") start (start + len)
       else
         Printf.sprintf "(!j. j < 4 * %s ==> %s = word_sub (m (%d + j)) (mld_fqmul (m (%d + j)) z))" ii (memq y "j") start (start + len))];
     (if nab > 0 then
       [Printf.sprintf "(!j. j < %d ==> %s = m (%d + j))" nab (memq u "j") (start + 2 * len)] else [])]);;

let vec_consts zpos =
  let c01 = if !(ntt_inverse ())
    then "read XMM1 s = word 0xffffffffff801fffffffffffff801fff /\\\n  read XMM0 s = word 0x00000000ffffffff00000000ffffffff"
    else "read XMM0 s = word 0xffffffffff801fffffffffffff801fff /\\\n  read XMM1 s = word 0x00000000ffffffff00000000ffffffff" in
  c01 ^ " /\\\n  read XMM2 s = word 0 /\\\n  read XMM3 s = word_join (word_sx z:int64) (word_sx z:int64) /\\\n  read XMM4 s = word_join (word_zx (word_mul z (word 58728449):int32):int64) (word_zx (word_mul z (word 58728449):int32):int64)";;

let vec_stmt loop exit start len zpos =
  let n = len / 4 in
  Printf.sprintf
"exists f_events. forall e a pc (m:num->int32) (z:int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    nonoverlapping (a,1024) (word pc,libmldsa_size) /\\ %s
    ==> ensures x86
     (\\s. bytes_loaded s (word pc) %s /\\
          read RIP s = word (pc + %d) /\\ read RDI s = a /\\
          read RAX s = word %s /\\
          %s /\\
          (!j. j < 256 ==> %s = m j) /\\
          read events s = e)
     (\\s. read RIP s = word (pc + %d) /\\ read RDI s = a /\\ read RAX s = word 0 /\\
          %s /\\
          (!j. j < 256 ==> %s = %s z %d %d m j) /\\
          (exists e2. read events s = APPEND e2 e /\\ e2 = f_events a pc /\\
              memaccess_inbounds e2 [a,1024] [a,1024]))
     (MAYCHANGE [RIP; RAX] ,, MAYCHANGE [ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11; ZMM12] ,,
      MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,1024)])"
   (if zpos then "&0 <= ival z" else "ival z < &0") ntt_mc (!(ntt_fn_base ()) + loop) (r0_of n)
   (vec_consts zpos) (memq 0 "j") (!(ntt_fn_base ()) + exit) (vec_consts zpos) (memq 0 "j")
   (if !(ntt_inverse ()) then "mld_invntt_block" else "mld_ntt_block") start len;;
let g_l1 = parse_term(vec_stmt 0x30 0x165 0 128 true);;

(* the facts of a part of the polynomial as the invariant states them,
   from the fact about the whole polynomial *)
let part_fact_tac b l c =
  (* !j. j < l ==> read(bytes32(word_add a (word(b + 4 * j)))) s0 = m (c + j) *)
  let sdef = if b = 0 then "word (4 * j)" else Printf.sprintf "word (%d + 4 * j)" b in
  let tm = parse_term(Printf.sprintf
    "!j. j < %d ==> read (memory :> bytes32 (word_add a (%s))) s0 = (m:num->int32) (%d + j)" l sdef c) in
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC (parse_term(Printf.sprintf "%d + j" c)) o
      check (fun th -> let c = concl th in is_forall c &&
             can (term_match [] `!j. j < 256 ==> read (memory :> bytes32 (word_add a (word (4 * j)))) s = m j`) c)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN (parse_term(Printf.sprintf "4 * (%d + j) = %s" c (if b = 0 then "4 * j" else Printf.sprintf "%d + 4 * j" b))) SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[]; ALL_TAC];;

let vec_exec lo eo = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc [(!(ntt_fn_base ()) + lo, !(ntt_fn_base ()) + eo)];;

let vec_exit_tac start len =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV THENC REWRITE_CONV[ADD_CLAUSES])) THEN
  MP_TAC(CONV_RULE(DEPTH_CONV NUM_RED_CONV THENC REWRITE_CONV[ADD_CLAUSES])
    (SPECL [`a:int64`; `s0:x86state`; `m:num->int32`; `z:int32`;
            mk_small_numeral start; mk_small_numeral len] (if !(ntt_inverse ()) then NTT_IBLK_ASM2 else NTT_BLK_ASM2))) THEN
  ANTS_TAC THENL [REWRITE_TAC[LT; ADD_CLAUSES] THEN ASM_REWRITE_TAC[ADD_CLAUSES]; ALL_TAC] THEN
  DISCH_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[NTT_W264B] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let vec_tac_skel exec lo eo start len zpos body_tac =
  let n = len / 4 in
  let x = 4 * start and y = 4 * (start + len) and u = 4 * (start + 2 * len) in
  let nab = 256 - (start + 2 * len) in
  let r0 = r0_of n in
  CONCRETIZE_F_EVENTS_TAC
   (parse_term(Printf.sprintf
     "\\(a:int64) (pc:num).
        APPEND (f_ev_epil a pc)
         (APPEND (ENUMERATEL %d (\\i. f_ev_loop a pc i)) (f_ev_prol a pc))
      :(uarch_event)list" n)) THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `pc:num`; `m:num->int32`; `z:int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC (mk_small_numeral n)
   (parse_term(Printf.sprintf "pc + %d" (!(ntt_fn_base ()) + lo)))
   (parse_term(Printf.sprintf "pc + %d" (!(ntt_fn_base ()) + eo)))
   (parse_term(Printf.sprintf
     "\\i s. read RDI s = a /\\ read RAX s = word (%s + 16 * i) /\\
            %s /\\ %s" r0 (vec_consts zpos) (vec_inv start len "i"))) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    (*** init ***)
    FULL_INIT_TAC THEN
    (if start > 0 then part_fact_tac 0 start 0 else ALL_TAC) THEN
    part_fact_tac x len start THEN part_fact_tac y len (start + len) THEN
    (if nab > 0 then part_fact_tac u nab (start + 2 * len) else ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN
    TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    (*** body ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    body_tac;
    (*** exit ***)
    vec_exit_tac start len];;


(* address wrap: word(1 * (R0 + 16 i) + D) = word(Dp + 16 i), Dp = D - 16 n - ... *)
let addrw_th r0 d dp =
  let rhs = if dp = 0 then "16 * i" else Printf.sprintf "%d + 16 * i" dp in
  prove(parse_term(Printf.sprintf "!i. word(1 * (%s + 16 * i) + %d):int64 = word(%s)" r0 d rhs),
    GEN_TAC THEN
    SUBGOAL_THEN (parse_term(Printf.sprintf "1 * (%s + 16 * i) + %d = 18446744073709551616 + (%s)" r0 d rhs))
      SUBST1_TAC THENL [ARITH_TAC; REWRITE_TAC[NTT_W264]]);;

let vec_prep start len zpos =
  let n = len / 4 in
  let x = 4 * start and y = 4 * (start + len) in
  let r0 = r0_of n in
  let dx = x + 16 * n and dy = y + 16 * n in
  let ax = addrw_th r0 dx x and ay = addrw_th r0 dy y in
  MAP_EVERY (fun k ->
    GHOST_INTRO_TAC (mk_var(Printf.sprintf "ymm%d_init" k, `:int256`))
                    (parse_term(Printf.sprintf "read YMM%d" k))) [5;6;7;8;9;10;11;12] THEN
  FULL_INIT_TAC THEN
  MAP_EVERY (fun k ->
    XMM_EXISTSTOP_TAC (Printf.sprintf "top%d" k) (parse_term(Printf.sprintf "YMM%d" k))) [0;1;2;3;4] THEN
  SUBGOAL_THEN (parse_term(Printf.sprintf "val(word(%s + 16 * i):int64) = %s + 16 * i" r0 r0)) ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN NUM_ASM_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun (d,th) ->
    SUBGOAL_THEN (parse_term(Printf.sprintf
      "nonoverlapping (word_add a (word(1 * (%s + 16 * i) + %d)):int64,16) (word pc:int64,libmldsa_size)" r0 d))
      ASSUME_TAC THENL
     [REWRITE_TAC[NONOVERLAPPING_CLAUSES; th] THEN MATCH_MP_TAC NTT_NONOV16 THEN
      EXISTS_TAC `1024` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV THEN NUM_ASM_ARITH_TAC;
      ALL_TAC]) [dx,ax; dy,ay];;

(* the 128-bit fact for the chunk of iteration i of the part at offset x
   (elements m (c + j)), in the canonical address and in the address of the
   simulator. The todo fact of the invariant is replaced by that of the
   next iteration. *)
let chunk128_tac len x c axth =
  let xs = if x = 0 then "" else Printf.sprintf "%d + " x in
  let off k = if k = 0 then Printf.sprintf "%s16 * i" xs
              else if x = 0 then Printf.sprintf "16 * i + %d" (4 * k)
              else Printf.sprintf "(%d + 16 * i) + %d" x (4 * k) in
  let pat = parse_term(Printf.sprintf
    "!j. 4 * i <= j /\\ j < %d ==> %s = (m:num->int32) (%d + j)" len (memq_s "s0" x "j") c) in
  let kpat = parse_term(Printf.sprintf
    "!k. k < 4 ==> %s = (m:num->int32) (%d + (4 * i + k))"
      (memq_s "s0" x "(4 * i + k)") c) in
  let tm128 = parse_term(Printf.sprintf "read (memory :> bytes128 (word_add a (word (%s)))) s0" (off 0)) in
  SUBGOAL_THEN (parse_term(Printf.sprintf "4 * (i + 1) <= %d" len)) ASSUME_TAC THENL
   [NUM_ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [MATCH_MP (SPECL [`i:num`; `4`; mk_small_numeral len] NTT_CHUNK_IN_L)
        (ASSUME (parse_term(Printf.sprintf "4 * (i + 1) <= %d" len)))] o
     check (fun th -> aconv (concl th) pat)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  EVERY(map (fun k ->
    let tm = parse_term(Printf.sprintf
      "read (memory :> bytes32 (word_add a (word (%s)))) s0 = (m:num->int32) (%d + (4 * i + %d))" (off k) c k) in
    SUBGOAL_THEN tm ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC (mk_small_numeral k) o
        check (fun th -> aconv (concl th) kpat)) THEN
      ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN (parse_term(Printf.sprintf "%s4 * (4 * i + %d) = %s" xs k (off k))) SUBST1_TAC THENL
       [ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[];
      ALL_TAC]) [0;1;2;3]) THEN
  MP_TAC(CONV_RULE(RAND_CONV(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV))
           (READ_MEMORY_MERGE_CONV 2 tm128)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th) = tm128 with Failure _ -> false)
    then ASSUME_TAC(REWRITE_RULE[GSYM (SPEC `i:num` axth)] th)
    else failwith "chunk128_tac") THEN
  FIRST_X_ASSUM(fun th -> if aconv (concl th) kpat then ALL_TAC else failwith "")
  ;;

(* drivers for the engine: the regions of the invariant against the two
   stores of the iteration, whose addresses wrap around *)
let vec_drivers start len =
  let n = len / 4 in
  let x = 4 * start and y = 4 * (start + len) and u = 4 * (start + 2 * len) in
  let nab = 256 - (start + 2 * len) in
  let r0 = r0_of n in
  let dx = x + 16 * n and dy = y + 16 * n in
  let ax = addrw_th r0 dx x and ay = addrw_th r0 dy y in
  let regions =
   (if start > 0 then [Printf.sprintf "0", Printf.sprintf "%d" x] else []) @
   [Printf.sprintf "%d" x, "16 * i";
    Printf.sprintf "%d + 16 * (i + 1)" x, Printf.sprintf "%d - 16 * (i + 1)" (4 * len);
    Printf.sprintf "%d" y, "16 * i";
    Printf.sprintf "%d + 16 * (i + 1)" y, Printf.sprintf "%d - 16 * (i + 1)" (4 * len)] @
   (if nab > 0 then [Printf.sprintf "%d" u, Printf.sprintf "%d" (4 * nab)] else []) in
  EVERY(map (fun (d,th) ->
    EVERY(map (fun (o1,l1) ->
      let tm = parse_term(Printf.sprintf
        "nonoverlapping ((word_add a (word (%s)):int64),%s) ((word_add a (word(1 * (%s + 16 * i) + %d)):int64),16)"
        o1 l1 r0 d) in
      SUBGOAL_THEN tm ASSUME_TAC THENL
       [REWRITE_TAC[NONOVERLAPPING_CLAUSES; th] THEN
        MATCH_MP_TAC NONOVERLAPPING_MODULO_64_OFFSET_BOTH THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        FIRST [DISJ1_TAC THEN NUM_ASM_ARITH_TAC; DISJ2_TAC THEN NUM_ASM_ARITH_TAC];
        ALL_TAC]) regions)) [dx,ax; dy,ay]);;

(* the lanes of a store, split and with the lane lemma applied *)
let vec_post_tac r0 d axth lane =
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    let l = lhand c in
    if can (term_match [] `read (memory :> bytes128 a) s = v`) c &&
       (try free_in (parse_term(Printf.sprintf "1 * (%s + 16 * i) + %d" r0 d)) l with Failure _ -> false) &&
       not (free_in `s0:x86state` c)
    then
      let th1 = REWRITE_RULE[axth] th in
      let th2 = CONV_RULE(SIMD_SIMPLIFY_CONV []) (CONV_RULE(READ_MEMORY_SPLIT_CONV 2) th1) in
      let th3 = REWRITE_RULE[lane] th2 in
      let th4 = CONV_RULE(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th3 in
      STRIP_ASSUME_TAC th4
    else failwith "vec_post_tac");;

let NORM_ARITH_RULES = [LEFT_ADD_DISTRIB; MULT_ASSOC; ADD_ASSOC; ADD_CLAUSES; MULT_CLAUSES];;
let NORM_ARITH_CONV = REWRITE_CONV NORM_ARITH_RULES THENC DEPTH_CONV NUM_RED_CONV THENC REWRITE_CONV NORM_ARITH_RULES;;
let NORM_ARITH_ASM_TAC = RULE_ASSUM_TAC(CONV_RULE NORM_ARITH_CONV);;

let WORD_ADD_FQ_SYM = prove(`!x y z:int32. word_add (mld_fqmul x z) y = word_add y (mld_fqmul x z)`, REWRITE_TAC[WORD_ADD_SYM]);;

let has_xmm tm =
  can (find_term (fun t -> is_const t &&
        (let n = fst(dest_const t) in String.length n >= 3 && String.sub n 0 3 = "XMM"))) tm;;
let has_forall_lt tm = is_forall tm;;

let vec_final_tac_g extra =
  ENSURES_FINAL_STATE_TAC THEN CONV_TAC NORM_ARITH_CONV THEN ASM_REWRITE_TAC[] THEN
  LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  (fun gl ->
    let w = snd gl in
    if is_exists w then DISCHARGE_SAFETY_PROPERTY_TAC gl
    else if has_xmm w then
      (REWRITE_TAC[XMM0; XMM1; XMM2; XMM3; XMM4; READ_ZEROTOP_128] THEN
       ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST) gl
    else if is_forall w then
      (REWRITE_TAC[NTT_CHUNK_OUTPUT_SPLIT] THEN ASM_REWRITE_TAC[] THEN
       CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NORM_ARITH_CONV THEN
       ASM_REWRITE_TAC extra) gl
    else
      (TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
       TRY(REWRITE_TAC[WORD_ADD] THEN NO_TAC)) gl);;

let vec_final_tac = vec_final_tac_g [];;

let vec_body start len zpos nbody lane_opt =
  let n = len / 4 in
  let x = 4 * start and y = 4 * (start + len) in
  let r0 = r0_of n in
  let dx = x + 16 * n and dy = y + 16 * n in
  let ax = addrw_th r0 dx x and ay = addrw_th r0 dy y in
  let exec = vec_exec 0 0 in ignore exec;
  fun exec_th ->
    vec_prep start len zpos THEN vec_drivers start len THEN
    chunk128_tac len x start ax THEN chunk128_tac len y (start + len) ay THEN
    NTT_SSE_STEPS_TAC exec_th (1--nbody) THEN
    (match lane_opt with
       None -> ALL_TAC
     | Some lane ->
        vec_post_tac r0 dx ax lane THEN vec_post_tac r0 dy ay lane THEN
        RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_FQ_SYM; ax; ay]) THEN
        NORM_ARITH_ASM_TAC THEN vec_final_tac_g (if !(ntt_inverse ()) then [WORD_ADD_SYM] else []));;

let prove_vec lo eo start len zpos nbody =
  let g = parse_term(vec_stmt lo eo start len zpos) in
  let zh = if zpos then `&0 <= ival (z:int32)` else `ival (z:int32) < &0` in
  let lane = GEN `y:int32` (MP (SPECL [`y:int32`;`z:int32`] (if zpos then NTT_LANE_POS else NTT_LANE_NEG)) (ASSUME zh)) in
  let exec = vec_exec lo eo in
  prove(g, vec_tac_skel exec lo eo start len zpos (vec_body start len zpos nbody (Some lane) exec));;

(* ------------------------------------------------------------------------- *)
(* The scalar loops of layers 4 and 5, and the mixed loops of layers 6 to 8. *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Scalar butterfly loops of layers 4 and 5 (one block per iteration, with   *)
(* a pointer register biased to the end of the block)                        *)
(* ------------------------------------------------------------------------- *)

let scal_mem_s st j = Printf.sprintf "read (memory :> bytes32 (word_add a (word (4 * %s)))) %s" j st;;

(* layer l (0-based), blocks of n coefficients, nb blocks, the pointer RDX
   starts at a + rdx0 *)
let scal_inv l n ii =
  Printf.sprintf
   "(!j. j < %d * %s ==> %s = mld_ntt_blocks %d %s m j) /\\
    (!j. %d * %s <= j /\\ j < 256 ==> %s = m j)"
   n ii (scal_mem_s "s" "j") l ii n ii (scal_mem_s "s" "j");;

let scal_regs rdx0 nb ii =
  Printf.sprintf
   "read RDI s = a /\\ read RAX s = word 0x0380200100000000 /\\ read RCX s = zt /\\
    read RDX s = word_add (word_add a (word (%d * %s))) (word %d) /\\ read RSI s = word %s /\\
    (!k. k < 256 ==> read (memory :> bytes32 (word_add zt (word (4 * k)))) s = mld_zeta k)"
   (4 * (256 / nb)) ii rdx0 ii;;

let scal_stmt lo eo l n rdx0 nb =
  let nbl = 256 / n in
  Printf.sprintf
"exists f_events. forall e a pc zt (m:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    nonoverlapping (a,1024) (word pc,libmldsa_size) /\\
    nonoverlapping (a,1024) (zt,1024)
    ==> ensures x86
     (\\s. bytes_loaded s (word pc) %s /\\
          read RIP s = word (pc + %d) /\\
          %s /\\
          (!j. j < 256 ==> %s = m j) /\\
          read events s = e)
     (\\s. read RIP s = word (pc + %d) /\\
          %s /\\
          (!j. j < 256 ==> %s = mld_ntt_blocks %d %d m j) /\\
          (exists e2. read events s = APPEND e2 e /\\ e2 = f_events a pc zt /\\
              memaccess_inbounds e2 [a,1024; zt,1024] [a,1024]))
     (MAYCHANGE [RIP; RDX; RSI; R8; R9; R10; R11; RBX] ,, MAYCHANGE SOME_FLAGS ,,
      MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,1024)])"
   ntt_mc (0x7ab0 + lo)
   (Printf.sprintf "read RDI s = a /\\ read RAX s = word 0x0380200100000000 /\\ read RCX s = zt /\\ read RDX s = word_add a (word %d) /\\ read RSI s = word 0 /\\ (!k. k < 256 ==> read (memory :> bytes32 (word_add zt (word (4 * k)))) s = mld_zeta k)" rdx0)
   (scal_mem_s "s" "j") (0x7ab0 + eo)
   (Printf.sprintf "read RDI s = a /\\ read RAX s = word 0x0380200100000000 /\\ read RCX s = zt /\\ read RDX s = word_add a (word %d) /\\ read RSI s = word %d /\\ (!k. k < 256 ==> read (memory :> bytes32 (word_add zt (word (4 * k)))) s = mld_zeta k)" (rdx0 + 1024) nbl)
   (scal_mem_s "s" "j") l nbl;;

let g_l4 = parse_term(scal_stmt 0x9e0 0xd53 3 32 124 8);;

let scal_tac_skel exec lo eo l n rdx0 nb body_tac =
  let nbl = 256 / n in
  CONCRETIZE_F_EVENTS_TAC
   (parse_term(Printf.sprintf
     "\\(a:int64) (pc:num) (zt:int64).
        APPEND (f_ev_epil a pc zt)
         (APPEND (ENUMERATEL %d (\\i. f_ev_loop a pc zt i)) (f_ev_prol a pc zt))
      :(uarch_event)list" nbl)) THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `pc:num`; `zt:int64`; `m:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC (mk_small_numeral nbl)
   (parse_term(Printf.sprintf "pc + %d" (0x7ab0 + lo)))
   (parse_term(Printf.sprintf "pc + %d" (0x7ab0 + eo)))
   (parse_term(Printf.sprintf "\\i s. %s /\\ %s" (scal_regs rdx0 nbl "i") (scal_inv l n "i"))) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    (*** init ***)
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN
    TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    (*** body ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    body_tac;
    (*** exit ***)
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let scal_prep l n rdx0 nb =
  let bs = 4 * n in
  let zb = 1 lsl l in
  FULL_INIT_TAC THEN
  SUBGOAL_THEN `val(word i:int64) = i` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN NUM_ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (parse_term(Printf.sprintf
     "read (memory :> bytes32 (word_add zt (word (4 * i + %d)))) s0 = mld_zeta (%d + i)" (4 * zb) zb))
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC (parse_term(Printf.sprintf "%d + i" zb)) o
      check (fun th -> can (term_match [] `!k. k < 256 ==> read (memory :> bytes32 (word_add zt (word (4 * k)))) s0 = mld_zeta k`) (concl th))) THEN
    ANTS_TAC THENL [NUM_ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE (parse_term(Printf.sprintf "4 * (%d + i) = 4 * i + %d" zb (4 * zb)))] THEN
    DISCH_THEN ACCEPT_TAC;
    ALL_TAC];;

let scal_chunks l n =
  let bs = 4 * n in
  let pat = parse_term(Printf.sprintf
    "!j. %d * i <= j /\\ j < 256 ==> %s = (m:num->int32) j" n (scal_mem_s "s0" "j")) in
  SUBGOAL_THEN (parse_term(Printf.sprintf "%d * (i + 1) <= 256" n)) ASSUME_TAC THENL
   [NUM_ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [MATCH_MP (SPECL [`i:num`; mk_small_numeral n; `256`] NTT_CHUNK_IN_L)
        (ASSUME (parse_term(Printf.sprintf "%d * (i + 1) <= 256" n)))] o
     check (fun th -> aconv (concl th) pat)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  EVERY(map (fun k ->
    let addr = if k = 0 then Printf.sprintf "word_add a (word (%d * i))" bs
               else Printf.sprintf "word_add (word_add a (word (%d * i))) (word %d)" bs (4 * k) in
    let tm = parse_term(Printf.sprintf
      "read (memory :> bytes32 (%s)) s0 = (m:num->int32) (%d * i + %d)" addr n k) in
    SUBGOAL_THEN tm ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC (mk_small_numeral k) o
        check (fun th -> can (term_match [] `!k. k < n ==> read (memory :> bytes32 (word_add a (word (4 * (n * i + k))))) s0 = m (n * i + k)`) (concl th) &&
                         not (free_in `mld_ntt_blocks` (concl th)))) THEN
      ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN (parse_term(Printf.sprintf "word_add a (word (4 * (%d * i + %d))) = %s:int64" n k addr)) SUBST1_TAC THENL
       [SUBGOAL_THEN (parse_term(Printf.sprintf "4 * (%d * i + %d) = %d * i + %d" n k bs (4 * k))) SUBST1_TAC THENL
         [ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE;
        ALL_TAC] THEN
      REWRITE_TAC[];
      ALL_TAC]) (0--(n-1)));;

(* the instances of the lemmas on blocks for layer l *)
let blk_insts l =
  let lt = mk_small_numeral l in
  let len = 1 lsl (7 - l) in
  let red th = CONV_RULE (DEPTH_CONV NUM_RED_CONV) th in
  let nrm th = CONV_RULE NORM_R_CONV (red th) in
  let lt_th k = EQT_ELIM (NUM_REDUCE_CONV (mk_binop `(<):num->num->bool` (mk_small_numeral k) (mk_small_numeral len))) in
  let inst lem k =
    let th = red (SPECL [lt; `m:num->int32`; `i:num`; mk_small_numeral k] lem) in
    ignore lt_th; nrm th in
  let prev = nrm (SPECL [lt; `m:num->int32`; `i:num`; `j:num`] NTT_BLOCKS_PREV) in
  (prev, map (inst NTT_BLOCKS_LO) (0--(len-1)), map (inst NTT_BLOCKS_HI) (0--(len-1)));;

(* the done facts of the invariant at i + 1 *)
let scal_done_tac_g split l n =
  let (prev, los, his) = blk_insts l in
  REWRITE_TAC[GSYM ADD1; ARITH_RULE (parse_term(Printf.sprintf "%d * SUC i = %d * i + %d" n n n)); NTT_CHUNK_OUTPUT_SPLIT] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[prev] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> can (term_match [] `!j. j < n * i ==> read (memory :> bytes32 (word_add a (word (4 * j)))) s = mld_ntt_blocks l i m j`) (concl th))) THEN
    ASM_REWRITE_TAC[];
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NORM_R_CONV THEN
    (if split then REWRITE_TAC[WORD_ADD_SPLIT_ADDR] else ALL_TAC) THEN
    REWRITE_TAC(los @ his) THEN ASM_REWRITE_TAC[]];;

let scal_done_tac = scal_done_tac_g true;;

let has_blocks tm = can (find_term (fun t -> is_const t && fst(dest_const t) = "mld_ntt_blocks")) tm;;

let scal_final_tac_g split l n =
  ENSURES_FINAL_STATE_TAC THEN CONV_TAC NORM_R_CONV THEN ASM_REWRITE_TAC[] THEN
  LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  (fun gl ->
    let w = snd gl in
    if is_exists w then DISCHARGE_SAFETY_PROPERTY_TAC gl
    else if has_blocks w then scal_done_tac_g split l n gl
    else
      (TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
       TRY(REWRITE_TAC[WORD_ADD; WORD_MUL] THEN CONV_TAC WORD_RULE THEN NO_TAC)) gl);;

let scal_final_tac = scal_final_tac_g true;;

let scal_body l n rdx0 nb nbody exec =
  scal_prep l n rdx0 nb THEN scal_chunks l n THEN
  X86_STEPS_TAC exec (1--nbody) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NTT_MONTRED_CLANG; WORD_ZX_ZX_32_64_32; GSYM mld_fqmul]) THEN
  NORM_R_ASM_TAC THEN
  scal_final_tac l n;;

let prove_scal lo eo l n rdx0 nb nbody =
  let g = parse_term(scal_stmt lo eo l n rdx0 nb) in
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc [(0x7ab0+lo, 0x7ab0+eo)] in
  prove(g, scal_tac_skel exec lo eo l n rdx0 nb (scal_body l n rdx0 nb nbody exec));;

(* ------------------------------------------------------------------------- *)
(* Scalar and mixed loops of layers 6 to 8 (a block of 2, 4 or 8              *)
(* coefficients per iteration, with an index register RDX = word(c * i))      *)
(* ------------------------------------------------------------------------- *)

let sc2_regs c ii =
  let rd = match int_of_string_opt ii with
      Some k -> string_of_int (c * k)
    | None -> if c = 1 then ii else Printf.sprintf "%d * %s" c ii in
  Printf.sprintf
   "read RDI s = a /\\ read RAX s = word 0x0380200100000000 /\\ read RCX s = zt /\\
    read RDX s = word (%s) /\\
    (!k. k < 256 ==> read (memory :> bytes32 (word_add zt (word (4 * k)))) s = mld_zeta k)" rd;;

let sc2_stmt lo eo l n c sse =
  let nbl = 256 / n in
  Printf.sprintf
"exists f_events. forall e a pc zt (m:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    nonoverlapping (a,1024) (word pc,libmldsa_size) /\\
    nonoverlapping (a,1024) (zt,1024)
    ==> ensures x86
     (\\s. bytes_loaded s (word pc) %s /\\
          read RIP s = word (pc + %d) /\\
          %s /\\
          (!j. j < 256 ==> %s = m j) /\\
          read events s = e)
     (\\s. read RIP s = word (pc + %d) /\\
          %s /\\
          (!j. j < 256 ==> %s = mld_ntt_blocks %d %d m j) /\\
          (exists e2. read events s = APPEND e2 e /\\ e2 = f_events a pc zt /\\
              memaccess_inbounds e2 [a,1024; zt,1024] [a,1024]))
     (MAYCHANGE [RIP; RDX; RSI; R8; R9; R10; R11] ,, %s
      MAYCHANGE SOME_FLAGS ,,
      MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,1024)])"
   ntt_mc (0x7ab0 + lo) (sc2_regs c "0") (scal_mem_s "s" "j") (0x7ab0 + eo)
   (sc2_regs c (string_of_int nbl)) (scal_mem_s "s" "j") l nbl
   (if sse then "MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6] ,," else "");;

let sc2_tac_skel exec lo eo l n c body_tac =
  let nbl = 256 / n in
  CONCRETIZE_F_EVENTS_TAC
   (parse_term(Printf.sprintf
     "\\(a:int64) (pc:num) (zt:int64).
        APPEND (f_ev_epil a pc zt)
         (APPEND (ENUMERATEL %d (\\i. f_ev_loop a pc zt i)) (f_ev_prol a pc zt))
      :(uarch_event)list" nbl)) THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `pc:num`; `zt:int64`; `m:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC (mk_small_numeral nbl)
   (parse_term(Printf.sprintf "pc + %d" (0x7ab0 + lo)))
   (parse_term(Printf.sprintf "pc + %d" (0x7ab0 + eo)))
   (parse_term(Printf.sprintf "\\i s. %s /\\ %s" (sc2_regs c "i") (scal_inv l n "i"))) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    (*** init ***)
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN
    TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    (*** body ***)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    body_tac;
    (*** exit ***)
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let sc2_prep l n c sse =
  let bs = 4 * n in
  let zb = 1 lsl l in
  (if sse then
     MAP_EVERY (fun k ->
       GHOST_INTRO_TAC (mk_var(Printf.sprintf "ymm%d_init" k, `:int256`))
                       (parse_term(Printf.sprintf "read YMM%d" k))) [0;1;2;3;4;5;6]
   else ALL_TAC) THEN
  FULL_INIT_TAC THEN
  SUBGOAL_THEN (parse_term(if c = 1 then "val(word i:int64) = i" else Printf.sprintf "val(word (%d * i):int64) = %d * i" c c)) ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN NUM_ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (parse_term(Printf.sprintf
     "read (memory :> bytes32 (word_add zt (word (4 * i + %d)))) s0 = mld_zeta (%d + i)" (4 * zb) zb))
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC (parse_term(Printf.sprintf "%d + i" zb)) o
      check (fun th -> can (term_match [] `!k. k < 256 ==> read (memory :> bytes32 (word_add zt (word (4 * k)))) s0 = mld_zeta k`) (concl th))) THEN
    ANTS_TAC THENL [NUM_ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE (parse_term(Printf.sprintf "4 * (%d + i) = 4 * i + %d" zb (4 * zb)))] THEN
    DISCH_THEN ACCEPT_TAC;
    ALL_TAC] THEN
  (if c = 1 then ALL_TAC else
   SUBGOAL_THEN (parse_term(Printf.sprintf
     "read (memory :> bytes32 (word_add (word (4 * i)) (word (1 * val (zt:int64) + %d)))) s0 = mld_zeta (%d + i)" (4 * zb) zb))
    ASSUME_TAC THENL
    [SUBGOAL_THEN (parse_term(Printf.sprintf "word_add (word (4 * i)) (word (1 * val (zt:int64) + %d)):int64 = word_add zt (word (4 * i + %d))" (4 * zb) (4 * zb))) SUBST1_TAC THENL
      [REWRITE_TAC[MULT_CLAUSES; WORD_ADD; WORD_VAL] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
     FIRST_ASSUM ACCEPT_TAC;
     ALL_TAC]);;

let sc2_chunks l n c sc =
  let bs = 4 * n in
  let pat = parse_term(Printf.sprintf
    "!j. %d * i <= j /\\ j < 256 ==> %s = (m:num->int32) j" n (scal_mem_s "s0" "j")) in
  SUBGOAL_THEN (parse_term(Printf.sprintf "%d * (i + 1) <= 256" n)) ASSUME_TAC THENL
   [NUM_ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [MATCH_MP (SPECL [`i:num`; mk_small_numeral n; `256`] NTT_CHUNK_IN_L)
        (ASSUME (parse_term(Printf.sprintf "%d * (i + 1) <= 256" n)))] o
     check (fun th -> aconv (concl th) pat)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  EVERY(map (fun k ->
    let addr = if k = 0 then Printf.sprintf "word_add a (word (%d * i))" bs
               else Printf.sprintf "word_add a (word (%d * i + %d))" bs (4 * k) in
    let addr2 = if k = 0 then Printf.sprintf "word_add a (word (%d * (%d * i)))" sc c
               else Printf.sprintf "word_add a (word (%d * (%d * i) + %d))" sc c (4 * k) in
    let tm = parse_term(Printf.sprintf
      "read (memory :> bytes32 (%s)) s0 = (m:num->int32) (%d * i + %d)" addr n k) in
    let tm2 = parse_term(Printf.sprintf
      "read (memory :> bytes32 (%s)) s0 = (m:num->int32) (%d * i + %d)" addr2 n k) in
    SUBGOAL_THEN tm ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC (mk_small_numeral k) o
        check (fun th -> can (term_match [] `!k. k < n ==> read (memory :> bytes32 (word_add a (word (4 * (n * i + k))))) s0 = m (n * i + k)`) (concl th) &&
                         not (free_in `mld_ntt_blocks` (concl th)))) THEN
      ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN (parse_term(Printf.sprintf "4 * (%d * i + %d) = %d * i + %d" n k bs (4 * k))) SUBST1_TAC THENL
       [ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ADD_CLAUSES];
      ALL_TAC] THEN
    (if c = 1 then ALL_TAC else
     SUBGOAL_THEN tm2 ASSUME_TAC THENL
      [SUBGOAL_THEN (parse_term(if k = 0 then Printf.sprintf "%d * (%d * i) = %d * i" sc c bs else Printf.sprintf "%d * (%d * i) + %d = %d * i + %d" sc c (4 * k) bs (4 * k))) SUBST1_TAC THENL
        [ARITH_TAC; ALL_TAC] THEN
       REWRITE_TAC[ADD_CLAUSES] THEN FIRST_ASSUM(fun th -> ACCEPT_TAC(REWRITE_RULE[ADD_CLAUSES] th));
       ALL_TAC])) (0--(n-1)));;

(* a wide read at the start of the block: bytes128 (lvl 2) or bytes64 (lvl 1) *)
let sc2_merge bytes lvl n c sc =
  let bs = 4 * n in
  let tm = parse_term(Printf.sprintf "read (memory :> %s (word_add a (word (%d * i)))) s0" bytes bs) in
  MP_TAC(CONV_RULE(RAND_CONV(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV))
           (READ_MEMORY_MERGE_CONV lvl tm)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    if (try lhs(concl th) = tm with Failure _ -> false)
    then ASSUME_TAC(REWRITE_RULE[ARITH_RULE (parse_term(Printf.sprintf "%d * i = %d * (%d * i)" bs sc c))] th)
    else failwith "sc2_merge");;

let NTT_VEC_MONTRED = prove
 (`!p:int64. word_subword (word_add p (word_mul (word_ishr (word_mul p (word 252236767799803904)) 32)
                           (word 18446744073701171199))) (32,32):int32 =
     mld_montgomery_reduce p`,
  GEN_TAC THEN
  REWRITE_TAC[WORD_BLAST `word_subword (v:int64) (32,32):int32 = word_zx(word_ushr v 32)`] THEN
  MP_TAC(SPEC `p:int64` NTT_MONTRED_CLANG) THEN
  MESON_TAC[WORD_ADD_SYM]);;

(* split the wide stores of the last state into narrow facts, with the lanes
   as fqmul *)
let sc2_split_stores =
  let is_wide c =
    can (term_match [] `read (memory :> bytes128 a) s = v`) c ||
    can (term_match [] `read (memory :> bytes64 a) s = v`) c in
  W(fun (asl,w) ->
    let ths = mapfilter (fun (_,th) ->
      let c = concl th in
      if is_wide c && not (free_in `s0:x86state` c) then
        let n = if can (term_match [] `read (memory :> bytes128 a) s = v`) c then 2 else 1 in
        let th1 = CONV_RULE(READ_MEMORY_SPLIT_CONV n) th in
        let th2 = CONV_RULE(SIMD_SIMPLIFY_CONV []) th1 in
        let th3 = REWRITE_RULE[NTT_SUBWORD_JOIN_LO; NTT_SUBWORD_JOIN_HI; NTT_VEC_MONTRED;
                               NTT_MONTRED_CLANG; WORD_ZX_ZX_32_64_32; GSYM mld_fqmul] th2 in
        let th4 = CONV_RULE(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th3 in
        th4
      else failwith "") asl in
    MAP_EVERY STRIP_ASSUME_TAC ths);;

let sc2_body l n c sc sse merge nbody exec =
  sc2_prep l n c sse THEN sc2_chunks l n c sc THEN
  (match merge with None -> ALL_TAC | Some (b,lv) -> sc2_merge b lv n c sc) THEN
  X86_STEPS_TAC exec (1--nbody) THEN
  (if sse then sc2_split_stores else ALL_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NTT_MONTRED_CLANG; WORD_ZX_ZX_32_64_32; GSYM mld_fqmul]) THEN
  NORM_R_ASM_TAC THEN
  scal_final_tac_g false l n;;

let prove_sc2 lo eo l n c sc sse merge nbody =
  let g = parse_term(sc2_stmt lo eo l n c sse) in
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc [(0x7ab0+lo, 0x7ab0+eo)] in
  prove(g, sc2_tac_skel exec lo eo l n c (sc2_body l n c sc sse merge nbody exec));;

