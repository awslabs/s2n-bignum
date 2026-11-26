(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas for the inlined code of mldsa{44,65,87}_signature_internal of the  *)
(* clang 23 -O3 monolithic reduced-RAM build that the generators of          *)
(* inline_sign.ml and inline_sign_map.ml do not cover: the poly_caddq loops  *)
(* of polyveck_caddq, whose byte offset runs on from one polynomial to the   *)
(* next (from k0 to k0 + 1024), and the straight-line sums (poly_add) of the *)
(* product A y, which also set up the next call of mldsa_poly_uniform.       *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_map.ml";;

(* ------------------------------------------------------------------------- *)
(* poly_caddq with the offset register R2 counting from k0 to k0 + 1024      *)
(* (the registers as in INLINE_CADDQ_LOOP).                                   *)
(* ------------------------------------------------------------------------- *)

let INLINE_CADDQK_LOOP_TERM mc loop exit k0 (rs:string list) =
  let r k = List.nth rs k in
  let addr = if k0 = 0 then "word_add a (word(4 * i))"
             else Printf.sprintf "word_add a (word(%d + 4 * i))" k0 in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e a (x:num->int32) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALL (nonoverlapping (word_add a (word %d),1024)) [(word pc,libmldsa_size)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read %s s = a /\\ read %s s = word %d /\\
                  read %s s = word 8380417 /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(%s)) s = x i) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\
                  read %s s = word %d /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(%s)) s = mld_poly_caddq x i) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a pc /\\
                     memaccess_inbounds e2 [word_add a (word %d),1024]
                                           [word_add a (word %d),1024]))
             (MAYCHANGE [PC; %s; %s; %s; %s] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(word_add a (word %d),1024)])"
   k0 mc loop (r 1) (r 2) k0 (r 5) addr exit (r 2) (k0 + 1024) addr k0 k0
   (r 2) (r 0) (r 3) (r 4) k0);;

let INLINE_CADDQK_LOOP mc exec loop exit k0 (rs:string list) =
  let r k = List.nth rs k in
  let tm = INLINE_CADDQK_LOOP_TERM mc loop exit k0 rs in
  let addrj = if k0 = 0 then "word_add a (word(4 * j))"
              else Printf.sprintf "word_add a (word(%d + 4 * j))" k0 in
  let inv = parse_term(Printf.sprintf
   "\\i s. read %s s = a /\\ read %s s = word(%s4 * i) /\\
          read %s s = word 8380417 /\\
          (!j. i <= j /\\ j < 256
               ==> read(memory :> bytes32(%s)) s = (x:num->int32) j) /\\
          (!j. j < i
               ==> read(memory :> bytes32(%s)) s = mld_caddq (x j))"
   (r 1) (r 2) (if k0 = 0 then "" else string_of_int k0 ^ " + ") (r 5) addrj addrj) in
  prove(tm,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (pc:num).
      APPEND (f_ev_epil a pc)
       (APPEND (ENUMERATEL 256 (\i. f_ev_loop a pc i)) (f_ev_prol a pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `x:num->int32`;
                       `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; mld_poly_caddq;
              fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256` (parse_term("pc + "^loop))
   (parse_term("pc + "^exit)) inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ONE_INPUT_SPLIT] o
      check (fun th -> is_forall(concl th) &&
        free_in `x:num->int32` (concl th) &&
        not(free_in `mld_caddq` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ARM_STEPS_TAC exec (1--8) THEN
    INLINE_CADDQ_LANE_TAC THEN
    ARM_STEPS_TAC exec (9--11) THEN
    FULL_FINAL_TAC [ONE_OUTPUT_SPLIT];

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Straight-line map code as INLINE_MAP_STMT of inline_sign_map.ml, with     *)
(* other instructions mixed in: more registers set (extrapost), byte stores  *)
(* to the frame (extramem, as (offset,length) from fp) and more variables    *)
(* (extrabind). The final tactic also bit-blasts the byte stores and puts    *)
(* the operands of the sums in one order (lanes = [WORD_ADD_SYM]).           *)
(* ------------------------------------------------------------------------- *)

(*** INLINE_MAP_STMT with extra memory written (extramem: (offset,len) from ***)
(*** fp) and extra conditions; extrapost may mention the stores             ***)

let INLINE_MAPX_STMT mc start stop (xs:(string*int)list) out fout readlo readlen
                     (mods:string list) extrabind extrapre extrapost
                     (extramem:(int*int) list) =
  let qmods,xmods = partition (fun r -> String.get r 0 = 'Q') mods in
  let binders = String.concat " " (map (fun (x,_) -> "(" ^ x ^ ":num->int32)") xs) ^
                " " ^ extrabind in
  let infacts = String.concat " /\\\n" (map (fun (x,off) ->
    Printf.sprintf
     "(!i. i < 256
           ==> read(memory :> bytes32(word_add fp (word(%d + 4 * i)))) s =
               %s i)" off x) xs) in
  let wr = String.concat "; " (map (fun (oo,l) ->
             Printf.sprintf "word_add fp (word %d),%d" oo l) ((out,1024)::extramem)) in
  let rd = String.concat "; " (map (fun (oo,l) ->
             Printf.sprintf "word_add fp (word %d),%d" oo l) ((readlo,readlen)::extramem)) in
  let mcs = String.concat "; " (map (fun (oo,l) ->
             Printf.sprintf "memory :> bytes(word_add fp (word %d),%d)" oo l)
             ((out,1024)::extramem)) in
  let novs = String.concat " /\\\n" (map (fun (oo,l) ->
     Printf.sprintf "nonoverlapping (word_add fp (word %d),%d) (word pc,libmldsa_size)" oo l)
     ((out,1024)::extramem)) in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e (fp:int64) %s pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        aligned 16 fp /\\
        %s
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read SP s = fp /\\ %s
                  %s /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\ %s
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add fp (word(%d + 4 * i))))
                             s = %s) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events fp pc /\\
                     memaccess_inbounds e2
                      [%s]
                      [%s]))
             (MAYCHANGE [PC; %s] ,, MAYCHANGE [%s] ,, MAYCHANGE [events] ,,
              MAYCHANGE [%s])"
   binders novs mc start extrapre infacts stop extrapost out fout
   rd wr (String.concat "; " xmods) (String.concat "; " qmods) mcs);;

let INLINE_MAPX_PROVE tm exec ins n (defs:thm list) (lanes:thm list) =
  prove(tm,
  CONCRETIZE_F_EVENTS_TAC
   `\(fp:int64) (pc:num). f_ev_map fp pc :(uarch_event)list` THEN
  META_EXISTS_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; fst exec] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  MAP_EVERY (fun (x,off) -> INLINE_MAP_INPUT_TAC off (mk_var(x,`:num->int32`)))
    ins THEN
  ARM_STEPS_TAC exec (1--n) THEN
  WIDE_STORE_SPLIT_TAC `fp:int64` 32 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
      ASM_REWRITE_TAC defs THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      REWRITE_TAC lanes THEN NO_TAC) THEN
  TRY(W(fun (_,w) -> if is_eq w && type_of(lhs w) = `:byte`
                     then CONV_TAC WORD_BLAST else NO_TAC)) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(*** The four sums of the column loop of yvec_lazy in mldsa44_signature_   ***)
(*** internal: polynomial i of w (at F + 4192 + 1024 i) plus the product   ***)
(*** at F + 832, with the setup of the next call of mldsa_poly_uniform     ***)
(*** (seed at F + 10112, its indices at F + 10144 and F + 10145).          ***)

let SI44_ADD_EXTRA i =
  if i < 3 then
    Printf.sprintf
     "read X0 s = word_add fp (word 832) /\\
      read X1 s = word_add fp (word 10112) /\\
      read (memory :> bytes8 (word_add fp (word 10144))) s = word_zx (word j:int64) /\\
      read (memory :> bytes8 (word_add fp (word 10145))) s = word %d /\\" (i + 1)
  else "read X19 s = word_add fp (word 4192) /\\";;

let SI44_ADD_TERM i (a,b) =
  INLINE_MAPX_STMT "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc"
   (string_of_int (layout "mldsa44_signature_internal" + a))
   (string_of_int (layout "mldsa44_signature_internal" + b))
   ["x",4192 + 1024 * i; "y",832] (4192 + 1024 * i) "mld_poly_add x y i"
   832 (4192 + 1024 * (i + 1) - 832)
   ((if i < 3 then ["X0";"X1";"X8"] else ["X19"]) @ INLINE_MAP_QMODS)
   (if i < 3 then "(j:num)" else "")
   (if i = 1 then "read X24 s = word 2 /\\ read X26 s = word_add fp (word 10080) /\\ read X27 s = word j /\\"
    else if i < 3 then "read X26 s = word_add fp (word 10080) /\\ read X27 s = word j /\\" else "")
   (SI44_ADD_EXTRA i)
   (if i < 3 then [10144,2] else []);;

let SI44_ADD_RANGES = [0x748,0xb48; 0xbd0,0xfcc; 0x1054,0x1454; 0x14dc,0x18cc];;

let SI44_ADD_PROVE i =
  let (a,b) = el i SI44_ADD_RANGES in
  INLINE_MAPX_PROVE (SI44_ADD_TERM i (a,b))
   (INLINE_LOOP_EXEC (string_of_int (layout "mldsa44_signature_internal" + a))
                     (string_of_int (layout "mldsa44_signature_internal" + b)))
   ["x",4192 + 1024 * i; "y",832] ((b - a) / 4) [mld_poly_add] [WORD_ADD_SYM];;

(*** mldsa44_signature_internal: z_i += y_i (+0x380c..+0x3c18), with the  ***)
(*** index i reloaded into x21 and the constants of the reduction that    ***)
(*** follows (2^22 and -q in each lane)                                    ***)

let SI44_ZADD_TERM =
  INLINE_MAPX_STMT "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc"
   (string_of_int (layout "mldsa44_signature_internal" + 0x380c))
   (string_of_int (layout "mldsa44_signature_internal" + 0x3c18))
   ["x",2144; "y",9056] 2144 "mld_poly_add x y i" 240 (10080 - 240)
   ("X21"::INLINE_MAP_QMODS) "(i:num)"
   "read (memory :> bytes64 (word_add fp (word 720))) s = word i /\\
    read (memory :> bytes128 (word_add fp (word 240))) s =
      word 0xff801fffff801fffff801fffff801fff /\\"
   "read X21 s = word i /\\
    read Q4 s = word 0x00400000004000000040000000400000 /\\
    read Q5 s = word 0xff801fffff801fffff801fffff801fff /\\"
   [];;

let SI44_ZADD_PROVE () =
  INLINE_MAPX_PROVE SI44_ZADD_TERM
   (INLINE_LOOP_EXEC (string_of_int (layout "mldsa44_signature_internal" + 0x380c))
                     (string_of_int (layout "mldsa44_signature_internal" + 0x3c18)))
   ["x",2144; "y",9056] ((0x3c18 - 0x380c) / 4) [mld_poly_add] [WORD_ADD_SYM];;

(* ------------------------------------------------------------------------- *)
(* Straight-line map code on a polynomial at a pointer w (in place) and one  *)
(* at fp + yoff, as in the row loop of signature_internal, where w is w0_j = *)
(* fp + 4192 + 1024 j. The nonoverlap of w with y and the frame slots read   *)
(* are hypotheses (the simulation needs them to keep the facts of y). A      *)
(* hypothesis w = ... is taken out of the assumptions before the             *)
(* initialization (FULL_INIT_TAC would substitute it into the goal) and      *)
(* given to the tactic fix that runs after step k (naming the pointer that   *)
(* the code computes as w). The store at w itself is split by hand           *)
(* (WIDE_STORE_SPLIT_TAC only takes addresses w + k).                        *)
(* ------------------------------------------------------------------------- *)

(*** The 64 128-bit values of the polynomial x at base (a term) ***)

let MAPP_INPUT_TAC (base:term) (x:term) =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if not(is_forall c && free_in x c) then NO_TAC else
    let lanes = map (fun i ->
      let th1 = SPEC (mk_small_numeral i) th in
      let th2 = MP th1 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th1)))) in
      CONV_RULE(LAND_CONV(DEPTH_CONV NUM_RED_CONV THENC
                          ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                          REWRITE_CONV[WORD_ADD_0])) th2) (0--255) in
    let ths = map (fun k ->
      let a = if k = 0 then base else
              mk_comb(mk_comb(`word_add:int64->int64->int64`,base),
                      mk_comb(`word:num->int64`,mk_small_numeral(16 * k))) in
      let a = rand(concl(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV a)) in
      let tm = subst [a,`A:int64`]
                `read (memory :> bytes128 A) (s0:armstate)` in
      let eth = READ_MEMORY_MERGE_CONV 2 tm in
      let eth = CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV
                  NORMALIZE_RELATIVE_ADDRESS_CONV THENC REWRITE_CONV[WORD_ADD_0])) eth in
      REWRITE_RULE lanes eth) (0--63) in
    MAP_EVERY ASSUME_TAC ths);;

(*** The statement: x at the pointer w (in place), y at fp + yoff; reads  ***)
(*** of the frame in [fp + readlo, readlen); extramem as for MAPX; whyp   ***)
(*** an extra hypothesis (e.g. on w)                                       ***)

let INLINE_MAPP_STMT mc start stop yoff fout readlo readlen (mods:string list)
                     extrabind whyp extrapre extrapost (extramem:(int*int) list)
                     (rslots:(int*int) list) =
  let qmods,xmods = partition (fun r -> String.get r 0 = 'Q') mods in
  let wr = String.concat "; " ("w,1024"::map (fun (oo,l) ->
             Printf.sprintf "word_add fp (word %d),%d" oo l) extramem) in
  let rd = String.concat "; " ("w,1024"::map (fun (oo,l) ->
             Printf.sprintf "word_add fp (word %d),%d" oo l) ((readlo,readlen)::extramem)) in
  let mcs = String.concat "; " ("memory :> bytes(w,1024)"::map (fun (oo,l) ->
             Printf.sprintf "memory :> bytes(word_add fp (word %d),%d)" oo l) extramem) in
  let novs = String.concat " /\\\n" ("nonoverlapping (w,1024) (word pc,libmldsa_size)"::
     Printf.sprintf "nonoverlapping (w,1024) (word_add fp (word %d),1024)" yoff::
     map (fun (oo,l) ->
       Printf.sprintf "nonoverlapping (w,1024) (word_add fp (word %d),%d)" oo l) rslots @
     map (fun (oo,l) ->
     Printf.sprintf "nonoverlapping (word_add fp (word %d),%d) (word pc,libmldsa_size)" oo l)
     extramem) in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e (fp:int64) (w:int64) (x:num->int32) (y:num->int32) %s pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        aligned 16 fp /\\ %s
        %s
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read SP s = fp /\\ %s
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add w (word(4 * i)))) s = x i) /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add fp (word(%d + 4 * i)))) s =
                           y i) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\ %s
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add w (word(4 * i)))) s = %s) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events fp w pc /\\
                     memaccess_inbounds e2 [%s] [%s]))
             (MAYCHANGE [PC; %s] ,, MAYCHANGE [%s] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events] ,, MAYCHANGE [%s])"
   extrabind whyp novs mc start extrapre yoff stop extrapost fout rd wr
   (String.concat "; " xmods) (String.concat "; " qmods) mcs);;

(*** The proof: n steps, with fix (a tactic) after step k (e.g. naming the ***)
(*** pointer that the code computes)                                       ***)

let INLINE_MAPP_PROVE tm exec yoff n k fix (defs:thm list) (lanes:thm list) =
  prove(tm,
  CONCRETIZE_F_EVENTS_TAC
   `\(fp:int64) (w:int64) (pc:num). f_ev_map fp w pc :(uarch_event)list` THEN
  META_EXISTS_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS; fst exec] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  (fun g -> let asl = fst g in
    match filter (fun (_,th) -> let c = concl th in is_eq c && lhs c = `w:int64`) asl with
      (_,th)::_ -> (UNDISCH_THEN (concl th) (fun th -> ALL_TAC) THEN FULL_INIT_TAC THEN
                    MAPP_INPUT_TAC `w:int64` `x:num->int32` THEN
                    MAPP_INPUT_TAC (parse_term(Printf.sprintf "word_add fp (word %d):int64" yoff))
                     `y:num->int32` THEN
                    ARM_STEPS_TAC exec (1--k) THEN fix th) g
    | [] -> (FULL_INIT_TAC THEN MAPP_INPUT_TAC `w:int64` `x:num->int32` THEN
             MAPP_INPUT_TAC (parse_term(Printf.sprintf "word_add fp (word %d):int64" yoff))
              `y:num->int32` THEN
             ARM_STEPS_TAC exec (1--k) THEN fix TRUTH) g) THEN
  ARM_STEPS_TAC exec ((k+1)--n) THEN
  WIDE_STORE_SPLIT_TAC `w:int64` 32 THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes128 (w:int64)) s = v`) (concl th)
    then STRIP_ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                           (CONV_RULE(READ_MEMORY_SPLIT_CONV 2) th))
    else NO_TAC)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
      REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC defs THEN
      CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
      REWRITE_TAC lanes THEN NO_TAC) THEN
  TRY(W(fun (asl,w) -> if is_iff w && free_in `j:num` w &&
                          exists (fun (_,th) -> concl th = `j < 4`) asl
       then UNDISCH_TAC `j < 4` THEN SPEC_TAC(`j:num`,`j:num`) THEN
            CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
            CONV_TAC NUM_REDUCE_CONV THEN NO_TAC
       else NO_TAC)) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(*** mldsa44_signature_internal: w0_j -= c s2 (+0x445c..+0x4774), with    ***)
(*** w0_j at x21 = fp + 4192 + 1024 j computed in the code (step 5); the  ***)
(*** region ends with the loads of the constants of the reduction (q4 and ***)
(*** q5 from fp + 240)                                                    ***)

let SI44_RSUB_TERM =
  INLINE_MAPP_STMT "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc"
   (string_of_int (layout "mldsa44_signature_internal" + 0x445c))
   (string_of_int (layout "mldsa44_signature_internal" + 0x4774))
   9056 "mld_poly_sub x y i" 224 (10080 - 224)
   ("X8"::"X9"::"X21"::INLINE_MAP_QMODS) "(j:num) (p:int64)"
   "w = word_add fp (word (4192 + 1024 * j)) /\\ j < 4 /\\"
   "read X8 s = word_add fp (word 4096) /\\ read X21 s = word j /\\
    read (memory :> bytes64 (word_add fp (word 224))) s = p /\\
    read (memory :> bytes128 (word_add fp (word 240))) s =
    word 339618401959998730991157055895298383871 /\\"
   "read X8 s = p /\\ read X9 s = word 256 /\\ read X21 s = w /\\
    read Q4 s = word 0x00400000004000000040000000400000 /\\
    read Q5 s = word 339618401959998730991157055895298383871 /\\"
   [] [224,8; 240,16];;

let SI44_RSUB_FIX wth =
  SUBGOAL_THEN `word_add (word_add fp (word 4192)) (word_shl (word j) 10):int64 = w`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[wth] THEN UNDISCH_TAC `j < 4` THEN SPEC_TAC(`j:num`,`j:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_RULE;
    ALL_TAC];;

(*** mldsa44_signature_internal: w0_j += c t0 (+0x4a70..+0x4d94, up to the ***)
(*** back edge of the row loop): the counters of the loop advance (x19 = j, ***)
(*** x20 = 96 j, x27 = the hint polynomial, the pointers at fp + 216, 224)  ***)

let SI44_RADD_TERM =
  INLINE_MAPP_STMT "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc"
   (string_of_int (layout "mldsa44_signature_internal" + 0x4a70))
   (string_of_int (layout "mldsa44_signature_internal" + 0x4d94))
   9056 "mld_poly_add x y i" 216 (10080 - 216)
   ("X8"::"X9"::"X10"::"X19"::"X20"::"X21"::"X27"::INLINE_MAP_QMODS)
   "(j:num) (k:num) (h:int64) (p:int64) (q:int64)" "j < 4 /\\"
   "read X21 s = w /\\ read X19 s = word j /\\ read X20 s = word k /\\
    read X27 s = h /\\
    read (memory :> bytes64 (word_add fp (word 216))) s = p /\\
    read (memory :> bytes64 (word_add fp (word 224))) s = q /\\"
   "read X19 s = word (j + 1) /\\ read X21 s = word (j + 1) /\\
    read X20 s = word (k + 96) /\\ read X27 s = word_add h (word 1024) /\\
    read (memory :> bytes64 (word_add fp (word 216))) s = word_add p (word 416) /\\
    read (memory :> bytes64 (word_add fp (word 224))) s = word_add q (word 1024) /\\
    (read ZF s <=> j + 1 = 4) /\\"
   [216,16] [216,16];;


let SI44_RSUB_PROVE () =
  INLINE_MAPP_PROVE SI44_RSUB_TERM
   (INLINE_LOOP_EXEC (string_of_int (layout "mldsa44_signature_internal" + 0x445c))
                     (string_of_int (layout "mldsa44_signature_internal" + 0x4774)))
   9056 ((0x4774 - 0x445c) / 4) 5 SI44_RSUB_FIX [mld_poly_sub] [];;

let SI44_RADD_PROVE () =
  INLINE_MAPP_PROVE SI44_RADD_TERM
   (INLINE_LOOP_EXEC (string_of_int (layout "mldsa44_signature_internal" + 0x4a70))
                     (string_of_int (layout "mldsa44_signature_internal" + 0x4d94)))
   9056 ((0x4d94 - 0x4a70) / 4) 0 (K ALL_TAC) [mld_poly_add] [WORD_ADD_SYM];;
