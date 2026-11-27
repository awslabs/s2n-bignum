(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Generators for the inlined code that mldsa65_signature_internal and      *)
(* mldsa87_signature_internal (clang 23 -O3 monolithic reduced-RAM build)   *)
(* share and mldsa44_signature_internal does not have: the parameters of    *)
(* ML-DSA-65 and ML-DSA-87 are gamma1 = 2^19 and gamma2 = (q - 1) / 32.     *)
(* Each generator states a loop or a region once, with the registers, the   *)
(* offsets in the frame and the step numbers as parameters, so that the 65  *)
(* and the 87 instances are calls with other arguments. The statements have *)
(* the forms of the 44 lemmas (inline_sign.ml, inline_sign_pack.ml).        *)
(*                                                                           *)
(* - Z19S: polyz_unpack for gamma1 = 2^19 in the sampling of y (8           *)
(*   coefficients from 20 bytes per iteration, the input pointer a + bias). *)
(* - DEC32: poly_decompose for gamma2 = (q - 1) / 32, one coefficient per    *)
(*   iteration, the high part to a1 and the low part in place.               *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_pack.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_unpack.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_unpackz19.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_arith.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_usehint32.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_w1pack32.ml";;
needs "common/fips204/properties/mldsa_native_hints.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_hrow.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_eta.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_gamma1.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_sig.ml";;

let SG_MC = "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc";;

(* ------------------------------------------------------------------------- *)
(* Z19S: the polyz_unpack loop of the sampling of y (gamma1 = 2^19), 32      *)
(* iterations of 20 bytes and 8 coefficients. The input pointer xin is      *)
(* a + 20 i + bias at the head of iteration i (the loads are LD1 lane       *)
(* inserts at xin - bias .. xin + 19 - bias), the output is ST2 to           *)
(* xbase + xoff with the byte offset xoff counting from 0 in steps of 32.   *)
(* qm holds 0xff in each lane, qg 2^19. The vectors in qpart are written    *)
(* first by lane inserts, so their initial values are abbreviated before    *)
(* the simulation (else the store of the results, which mentions them, is   *)
(* lost in stepping).                                                       *)
(* ------------------------------------------------------------------------- *)

let SG_Z19S_STMT mc loop exit bias (xin,xbase,xoff) (qm,qg) (mods:string list) =
  let qmods,xmods = partition (fun r -> String.get r 0 = 'Q') mods in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e r a (b:num->byte) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (a,640)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read %s s = word_add a (word %d) /\\ read %s s = r /\\
                  read %s s = word 0 /\\
                  read %s s = word 0x000000ff000000ff000000ff000000ff /\\
                  read %s s = word 0x00080000000800000008000000080000 /\\
                  (!j. j < 640
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\
                  read %s s = word_add a (word %d) /\\ read %s s = r /\\
                  read %s s = word 1024 /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r (word(4 * i)))) s =
                           mld_polyz_unpack_19 b i) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events r a pc /\\
                     memaccess_inbounds e2 [a,640; r,1024] [r,1024]))
             (MAYCHANGE [PC; %s] ,, MAYCHANGE [%s] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(r,1024)])"
   mc loop xin bias xbase xoff qm qg
   exit xin (640 + bias) xbase xoff
   (String.concat "; " xmods) (String.concat "; " qmods));;

(*** The addresses of the loads, as the simulation forms them from the  ***)
(*** input pointer a + 20 * i + bias, as the facts of CHUNK_INPUT_TAC   ***)

let SG_Z19S_ADDRS bias =
  let ptr = Printf.sprintf "(20 * i + %d)" bias in
  let old k = if k = 0 then "word_add a (word (20 * i))"
              else Printf.sprintf "word_add a (word (20 * i + %d))" k in
  let big m = string_of_num (((Num.num_of_int 2) **/ (Num.num_of_int 64)) -/
                             (Num.num_of_int m)) in
  map (fun k ->
    let d = k - bias in
    if d > 0 then
      [Printf.sprintf "word_add a (word (%s + %d)):int64 = %s" ptr d (old k)],
      [Printf.sprintf "word_add (word_add a (word %s)) (word %d):int64 = %s"
         ptr d (old k);
       Printf.sprintf "word_add a (word (%s + %d)):int64 = %s" ptr d (old k)]
    else
      let m = -d in
      [Printf.sprintf "word_add a (word (%s + %s)):int64 = %s" ptr (big m) (old k);
       Printf.sprintf "word_add a (word_sub (word %s) (word %d)):int64 = %s"
         ptr m (old k)],
      [Printf.sprintf "word_add (word_add a (word %s)) (word %s):int64 = %s"
         ptr (big m) (old k);
       Printf.sprintf "word_sub (word_add a (word %s)) (word %d):int64 = %s"
         ptr m (old k);
       Printf.sprintf "word_add a (word_sub (word %s) (word %d)):int64 = %s"
         ptr m (old k)])
   (filter (fun k -> k <> bias) (0--19));;

let SG_Z19S_ALIASES bias = List.concat(map fst (SG_Z19S_ADDRS bias));;
let SG_Z19S_EVENTS bias = [List.concat(map snd (SG_Z19S_ADDRS bias))];;

let SG_Z19S_LOOP mc exec loop exit bias nsteps (xin,xbase,xoff) (qm,qg)
                 (qpart:string list) (mods:string list) =
  INLINE_CHUNK_PROVE
   (SG_Z19S_STMT mc loop exit bias (xin,xbase,xoff) (qm,qg) mods)
   "(r:int64) (a:int64)" "r a" ["r:int64"; "a:int64"; "b:num->byte"; "pc:num"]
   32 exec loop exit
   (Printf.sprintf
     "\\i s. read %s s = word_add a (word (20 * i + %d)) /\\
            read %s s = r /\\ read %s s = word (32 * i) /\\
            read %s s = word 0x000000ff000000ff000000ff000000ff /\\
            read %s s = word 0x00080000000800000008000000080000 /\\
            (!j. j < 640
                 ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\\
            (!j. j < 8 * i
                 ==> read(memory :> bytes32(word_add r (word(4 * j)))) s =
                     mld_polyz_unpack_19 b j)"
     xin bias xbase xoff qm qg)
   (CHUNK_INPUT_TAC `b:num->byte` 20 THEN
    INLINE_ALIAS_TAC (SG_Z19S_ALIASES bias) THEN
    MAP_EVERY (fun q ->
      let v = mk_var(String.lowercase_ascii q,`:int128`) in
      let r = mk_const(q,[]) in
      let rd = list_mk_comb(`read:(armstate,int128)component->armstate->int128`,
                            [r;`s0:armstate`]) in
      SUBGOAL_THEN (mk_exists(v,mk_eq(rd,v))) (X_CHOOSE_TAC v) THENL
       [EXISTS_TAC rd THEN REFL_TAC; ALL_TAC]) qpart THEN
    ARM_STEPS_TAC exec (1--nsteps) THEN
    INLINE_ST2_LANES_TAC `r:int64` THEN
    INLINE_CHUNK_FINAL_TAC mld_polyz_unpack_19 `b:num->byte`
      [INLINE_DIV2_8; INLINE_MOD2_8]
      [ARITH_RULE `32 * (i + 1) = 32 * i + 32`;
       ARITH_RULE (parse_term(Printf.sprintf
         "20 * (i + 1) + %d = (20 * i + %d) + 20" bias bias))]
      (SG_Z19S_EVENTS bias));;

(*** The loops of the sampling of y in 65 and 87 (loop5 and the loop of the ***)
(*** z loop): input pointer x9 = a + 9, offset x8, output base xb, mask q6, ***)
(*** 2^19 q7, lane inserts into q0 .. q4                                    ***)

let SG_Z19S_MODS = ["X8";"X9";"X10";"X11";"X12";"X13";
                    "Q0";"Q1";"Q2";"Q3";"Q4";"Q5"];;

let SG_Z19S fn loop xb =
  let hl = fn ^ "_" ^ loop and el = fn ^ "_" ^ loop ^ "_exit" in
  SG_Z19S_LOOP SG_MC (INLINE_LOOP_EXEC hl el) hl el 9 69 ("X9",xb,"X8")
    ("Q6","Q7") ["Q0";"Q1";"Q2";"Q3";"Q4"] SG_Z19S_MODS;;

(* ------------------------------------------------------------------------- *)
(* DEC32: poly_decompose for gamma2 = (q - 1) / 32 (one coefficient per      *)
(* iteration, a1[i] = high part, a[i] := low part), the statement of the     *)
(* shapes "62" and "63" of inline_sign_arith.ml (INLINE_DECOMPOSE_LOOP_TERM, *)
(* registers rs in its numbering). The proof does not bit-blast the whole   *)
(* iteration: as in the use_hint loop of inline_sign_usehint32.ml, the high *)
(* part is taken as mld_decompose_hi_32 in its register right after the     *)
(* code computes it (step hstep, register hreg), and the low part, which    *)
(* the code computes from it with MADD, as mld_decompose_lo_32 after step   *)
(* lstep (register lreg, DECOMPOSE_LO_32_MADD).                              *)
(* ------------------------------------------------------------------------- *)

let SG_DEC32_LOOP kind mc exec loop exit k0 (rs:string list)
                  (hstep,hreg) (lstep,lreg) =
  let r k = List.nth rs k in
  let (a1r,consts,temps,nsteps) = INLINE_DECOMPOSE_LAYOUT kind in
  let pa = if k0 = 0 then "a" else Printf.sprintf "(word_add a (word %d))" k0 in
  let tm = INLINE_DECOMPOSE_LOOP_TERM kind mc loop exit k0 rs in
  let creg = String.concat " /\\ "
    (map (fun (k,v) -> Printf.sprintf "read %s s = word %s" (r k) v) consts) in
  let inv = parse_term(INLINE_FILL
   "\\i s. read @a@ s = a /\\ read @a1r@ s = a1 /\\
          read @ir@ s = word(4 * i) /\\ @creg@ /\\
          (!j. i <= j /\\ j < 256
               ==> read(memory :> bytes32(word_add @pa@ (word(4 * j)))) s =
                   (x:num->int32) j) /\\
          (!j. j < i
               ==> read(memory :> bytes32(word_add a1 (word(4 * j)))) s =
                   mld_decompose_hi_32 (x j)) /\\
          (!j. j < i
               ==> read(memory :> bytes32(word_add @pa@ (word(4 * j)))) s =
                   mld_decompose_lo_32 (x j))"
   ["a",r 1; "a1r",r a1r; "ir",r 2; "creg",creg; "pa",pa]) in
  let paddr = if k0 = 0 then `word_add (a:int64) (word(4 * i))`
              else parse_term(Printf.sprintf "word_add (a:int64) (word(4 * i + %d))" k0) in
  let normk =
    if k0 = 0 then ALL_TAC else
    let lem = prove(parse_term(Printf.sprintf
      "!a i. word_add (word_add a (word %d)) (word (4 * i)):int64 =
             word_add a (word (4 * i + %d))" k0 k0), CONV_TAC WORD_RULE) in
    RULE_ASSUM_TAC(REWRITE_RULE[lem]) THEN REWRITE_TAC[lem] in
  let xi = `(x:num->int32) i` in
  prove(tm,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (a1:int64) (pc:num).
      APPEND (f_ev_epil a a1 pc)
       (APPEND (ENUMERATEL 256 (\i. f_ev_loop a a1 pc i)) (f_ev_prol a a1 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `a1:int64`;
                       `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; PAIRWISE; ALL; SOME_FLAGS; fst exec;
              mld_poly_decompose_hi_32; mld_poly_decompose_lo_32] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256` (parse_term("pc + "^loop))
   (parse_term("pc + "^exit)) inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN normk THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ONE_INPUT_SPLIT] o
      check (fun th -> is_forall(concl th) &&
        free_in `x:num->int32` (concl th) &&
        not(free_in `mld_decompose_hi_32` (concl th)) &&
        not(free_in `mld_decompose_lo_32` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ARM_STEPS_TAC exec (1--hstep) THEN
    REG_LANE_TAC (mk_const(hreg,[])) xi `mld_decompose_hi_32`
      [DECOMPOSE_HI_32_ALT] THEN
    ARM_STEPS_TAC exec ((hstep+1)--lstep) THEN
    REG_LANE_TAC (mk_const(lreg,[])) xi `mld_decompose_lo_32`
      [DECOMPOSE_LO_32_MADD; mld_ct_sel] THEN
    ARM_STEPS_TAC exec ((lstep+1)--nsteps) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32]) THEN
    FULL_FINAL_TAC [ONE_OUTPUT_SPLIT];

    INLINE_EXIT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* W1PS32: polyw1_pack_32 as clang has inlined it after the decompose loop   *)
(* of a row (as SI_W1PS of inline_sign_w1pack_sig.ml for polyw1_pack_88):   *)
(* straight-line vector code that loads w1 (x, at F + ws_in, 1024 bytes)    *)
(* with LD2 of 32 bytes through pointer registers (given in ws_pre), packs  *)
(* two 4-bit coefficients per byte (SHL by 4, ORR, UZP1), spills to the     *)
(* frame (the regions ws_spill) and stores the 128 bytes of the row at       *)
(* F + ws_out. The code is that of the w1 pack of verify (W1PACK32 of       *)
(* inline_sign_w1pack32.ml) with other registers and addresses.             *)
(* ------------------------------------------------------------------------- *)

type w1ps32_inst =
  { w2_start : string; w2_stop : string; w2_steps : int;
    w2_in : int; w2_out : int; w2_pre : string; w2_post : string;
    w2_spill : (int * int) list; w2_mods : string list };;

let SG_W1PS32_TERM mc p =
  let regs = p.w2_spill @ [p.w2_out,128] in
  let fl f = String.concat "; " (map f regs) in
  let nov = String.concat " /\\\n      " (map (fun (oo,l) ->
    Printf.sprintf "nonoverlapping (word_add fp (word %d),%d) (word pc,libmldsa_size)"
      oo l) regs) in
  parse_term(Printf.sprintf
 "exists f_events.
    forall e (fp:int64) (x:num->int32) pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 fp /\\
      %s
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc) %s /\\
                read PC s = word (pc + %s) /\\
                read SP s = fp /\\ %s /\\
                (!j. j < 256
                     ==> read(memory :> bytes32(word_add fp (word(%d + 4 * j)))) s =
                         x j) /\\
                read events s = e)
           (\\s. read PC s = word (pc + %s) /\\ %s
                (!j. j < 128
                     ==> read(memory :> bytes8(word_add fp (word(%d + j)))) s =
                         mld_polyw1_pack_32 x j) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events fp pc /\\
                   memaccess_inbounds e2
                    [word_add fp (word %d),1024; %s]
                    [%s]))
           (MAYCHANGE [PC; %s] ,,
            MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12;
                       Q13; Q14; Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23;
                       Q24; Q25; Q26; Q27; Q28; Q29; Q30; Q31] ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [%s])"
  nov mc p.w2_start p.w2_pre p.w2_in p.w2_stop p.w2_post p.w2_out p.w2_in
  (fl (fun (oo,l) -> Printf.sprintf "word_add fp (word %d),%d" oo l))
  (fl (fun (oo,l) -> Printf.sprintf "word_add fp (word %d),%d" oo l))
  (String.concat "; " p.w2_mods)
  (fl (fun (oo,l) -> Printf.sprintf "memory :> bytes(word_add fp (word %d),%d)" oo l)));;

(*** Byte j of the output from the 128-bit store that holds it, found by ***)
(*** its normalized address F + out + 16 * (j DIV 16)                    ***)

let SG_W1PS32_BYTE_TAC out stores j =
  let m = j / 16 and t = j mod 16 in
  let addr = mk_comb(mk_comb(`word_add:int64->int64->int64`,`fp:int64`),
                     mk_comb(`word:num->int64`,mk_small_numeral(out + 16 * m))) in
  let nrm a = try rhs(concl(NORMALIZE_RELATIVE_ADDRESS_CONV a)) with Failure _ -> a in
  let sth = find (fun th ->
    nrm(rand(rand(rand(rator(lhs(concl th)))))) = addr) stores in
  let faddr = rand(rand(rand(rator(lhs(concl sth))))) in
  let bth = MP (SPECL [faddr; rhs(concl sth); rand(lhs(concl sth));
                       mk_small_numeral t] INLINE_BYTES8_OF_BYTES128)
               (CONJ sth (EQT_ELIM(NUM_REDUCE_CONV
                  (mk_binop `(<):num->num->bool` (mk_small_numeral t) `16`)))) in
  let bth = CONV_RULE(RAND_CONV(RAND_CONV(LAND_CONV NUM_MULT_CONV) THENC
                                W1P_EXTRACT_CONV)) bth in
  let baddr = rand(rand(rand(rator(lhs(concl bth))))) in
  W(fun (asl,w) ->
    let gaddr = rand(rand(rand(rator(lhs w)))) in
    let eq = prove(mk_eq(gaddr,baddr),
                   REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
                   AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC) in
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [eq] THEN
    GEN_REWRITE_TAC LAND_CONV [bth] THEN
    REWRITE_TAC[mld_polyw1_pack_32] THEN
    CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
    REWRITE_TAC[] THEN W1P_BITBLAST_TAC);;

let SG_W1PS32_BYTES_TAC out =
  CONV_TAC EXPAND_CASES_CONV THEN
  W(fun (asl,w) ->
    let stores = mapfilter (fun (_,th) ->
      let c = concl th in
      if is_eq c &&
         (try fst(dest_const(rator(rand(rand(rator(lhs c)))))) = "bytes128"
          with Failure _ -> false)
      then th else fail()) asl in
    REPEAT CONJ_TAC THENL (map (SG_W1PS32_BYTE_TAC out stores) (0--127)));;

let SG_W1PS32_PROVE mc p =
  let ex = INLINE_LOOP_EXEC p.w2_start p.w2_stop in
  prove(SG_W1PS32_TERM mc p,
  CONCRETIZE_F_EVENTS_TAC
   `\(fp:int64) (pc:num). f_ev_w1 fp pc :(uarch_event)list` THEN
  META_EXISTS_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; fst ex] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN INLINE_MAP_INPUT_TAC p.w2_in `x:num->int32` THEN
  INLINE_MAP_INPUT256_TAC p.w2_in THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC ex [n] THEN INLINE_W1P2_FIX_TAC THEN
                      INLINE_W1P2_SIMP_TAC) (1--p.w2_steps) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST [CONV_TAC WORD_RULE THEN NO_TAC;
         SG_W1PS32_BYTES_TAC p.w2_out;
         MONOTONE_MAYCHANGE_TAC THEN NO_TAC;
         DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* HROW32: the hint loop of row k of mld_pack_sig_h for gamma2 = (q-1)/32,   *)
(* SI_HROW of inline_sign_hrow.ml with the parameters of the function: the  *)
(* frame offsets of the row of w0 (x, hr3_woff) and of the unpacked row of  *)
(* w1 (hr3_w1off, in hr3_w1reg), the hint bytes at sig + hr3_hoff (in      *)
(* hr3_hreg), omega, the registers of -gamma2, gamma2 and 2 gamma2 + 1, and  *)
(* the register of the row base (hr3_wreg, "" if the body loads it). The    *)
(* iterations go from the head (j = 0 in x9, the count of the rows before  *)
(* in w8) to the exit of the loop or, with more than omega hints, to the    *)
(* label exit1 of the loop (join9 in 65, join10 in 87). The rows have the   *)
(* shapes of the 44 rows (row 0: a CCMP chain and B.CC; the                 *)
(* others: CSET, B.CS, TBNZ), which SG_HR_DECIDE_TAC recognizes by the      *)
(* conditions of the branches.                                              *)
(* ------------------------------------------------------------------------- *)

type hrow32_inst =
  { hr3_fn : string; hr3_k : int; hr3_head : string; hr3_exit : string;
    hr3_lo : int; hr3_hi : int; hr3_wreg : string; hr3_woff : int;
    hr3_w1reg : string; hr3_w1off : int; hr3_hreg : string; hr3_hoff : int;
    hr3_omega : int; hr3_cregs : string * string * string;
    hr3_mods : string; hr3_slot : (int * int) list };;

let sghr_toks c =
  let (rm,rg,r2) = c.hr3_cregs in
  ["@MC@",SG_MC; "@HEAD@",c.hr3_head; "@EXIT@",c.hr3_exit;
   "@JOIN9@",c.hr3_head ^ "_exit1";
   "@W@",string_of_int c.hr3_woff; "@W1@",string_of_int c.hr3_w1off;
   "@W1REG@",c.hr3_w1reg; "@HREG@",c.hr3_hreg;
   "@H@",string_of_int c.hr3_hoff; "@OM@",string_of_int c.hr3_omega;
   "@WB@",string_of_int (128 * c.hr3_k); "@P0@",string_of_int (256 * c.hr3_k);
   "@P1@",string_of_int (256 * (c.hr3_k + 1));
   "@CREGS@",Printf.sprintf
     "read %s s = word 4294705408 /\\ read %s s = word 261888 /\\ read %s s = word 523777 /\\"
     rm rg r2;
   "@WREG@",(if c.hr3_wreg = "" then ""
             else "read " ^ c.hr3_wreg ^ " s = word_add fp (word " ^
                  string_of_int c.hr3_woff ^ ") /\\");
   "@MODS@",c.hr3_mods;
   "@SLOT@",String.concat "" (map (fun (a,v) -> Printf.sprintf
      "read (memory :> bytes64 (word_add fp (word %d))) s = word_add fp (word %d) /\\ " a v)
      c.hr3_slot);
   "@SNOV@",String.concat "" (map (fun (a,_) -> Printf.sprintf
      "; (word_add fp (word %d),8)" a) c.hr3_slot);
   "@SRD@",String.concat "" (map (fun (a,_) -> Printf.sprintf
      "; word_add fp (word %d),8" a) c.hr3_slot)];;

let sghr_sub c s = hrow_subst (sghr_toks c) s;;

let SG_HR_TEMPLATE c = parse_term(sghr_sub c
 "\\(x:num->int32) (b:num->byte) (sig:int64) (fp:int64) (pc:num).
   APPEND (f_ev_epi x b sig fp pc)
   (APPEND
    (ENUMERATEL (glue_hint_steps @OM@ @P1@ (mld_polyvec_make_hint_32 x b) - @P0@)
      (\\i. if glue_hint_fail @OM@ (mld_polyvec_make_hint_32 x b) (@P0@ + i)
           then if glue_hint_inr_32 (x(@P0@ + i))
                then f_ev_f2 x b sig fp pc i else f_ev_f1 x b sig fp pc i
           else if i < 255
           then if mld_polyvec_make_hint_32 x b (@P0@ + i)
                then if glue_hint_inr_32 (x(@P0@ + i))
                     then f_ev_m2 x b sig fp pc i else f_ev_m1 x b sig fp pc i
                else f_ev_m3 x b sig fp pc i
           else if mld_polyvec_make_hint_32 x b (@P0@ + i)
                then if glue_hint_inr_32 (x(@P0@ + i))
                     then f_ev_l2 x b sig fp pc i else f_ev_l1 x b sig fp pc i
                else f_ev_l3 x b sig fp pc i))
    (f_ev_pro x b sig fp pc)) :(uarch_event)list");;

let SG_HR_TERM c = parse_term(sghr_sub c
 "exists f_events.
    forall e (x:num->int32) (b:num->byte) (sig:int64) (fp:int64) pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 fp /\\
      mld_hint_count (mld_polyvec_make_hint_32 x b) @P0@ <= @OM@ /\\
      ALL (nonoverlapping (word_add sig (word @H@),@OM@))
          [(word_add fp (word @W@),1024); (word_add fp (word @W1@),1024);
           (word pc,libmldsa_size)@SNOV@]
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc) @MC@ /\\
                read PC s = word (pc + @HEAD@) /\\
                read SP s = fp /\\
                read @W1REG@ s = word_add fp (word @W1@) /\\
                read @HREG@ s = word_add sig (word @H@) /\\ @WREG@ @CREGS@ @SLOT@
                read X9 s = word 0 /\\
                read X8 s = word (mld_hint_count (mld_polyvec_make_hint_32 x b) @P0@) /\\
                (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (@W@ + 4 * i)))) s =
                                 x (@P0@ + i)) /\\
                (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (@W1@ + 4 * i)))) s =
                                 mld_polyw1_unpack_32 (\\t. b (@WB@ + t)) i) /\\
                (!t. t < @OM@ ==> read (memory :> bytes8 (word_add sig (word (@H@ + t)))) s =
                                mld_hint_index (mld_polyvec_make_hint_32 x b) @P0@ t) /\\
                read events s = e)
           (\\s. read PC s =
                (if mld_hint_count (mld_polyvec_make_hint_32 x b) @P1@ <= @OM@
                 then word (pc + @EXIT@)
                 else word (pc + @JOIN9@)) /\\
                (mld_hint_count (mld_polyvec_make_hint_32 x b) @P1@ <= @OM@
                 ==> read X8 s = word (mld_hint_count (mld_polyvec_make_hint_32 x b) @P1@) /\\
                     (!t. t < @OM@ ==> read (memory :> bytes8 (word_add sig (word (@H@ + t)))) s =
                                     mld_hint_index (mld_polyvec_make_hint_32 x b) @P1@ t)) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events x b sig fp pc /\\
                   memaccess_inbounds e2
                    [word_add fp (word @W@),1024; word_add fp (word @W1@),1024;
                     word_add sig (word @H@),@OM@@SRD@]
                    [word_add sig (word @H@),@OM@]))
           (MAYCHANGE [PC; @MODS@] ,, MAYCHANGE SOME_FLAGS ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(word_add sig (word @H@),@OM@)])");;

let SG_HR_INV c = parse_term(sghr_sub c
 "\\i s. read SP s = fp /\\
        read @W1REG@ s = word_add fp (word @W1@) /\\
        read @HREG@ s = word_add sig (word @H@) /\\ @WREG@ @CREGS@ @SLOT@
        (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (@W@ + 4 * i)))) s =
                         x (@P0@ + i)) /\\
        (!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (@W1@ + 4 * i)))) s =
                         mld_polyw1_unpack_32 (\\t. b (@WB@ + t)) i) /\\
        (i < glue_hint_steps @OM@ @P1@ (mld_polyvec_make_hint_32 x b) - @P0@ \\/
         mld_hint_count (mld_polyvec_make_hint_32 x b) @P1@ <= @OM@
         ==> read X9 s = word i /\\
             read X8 s = word (mld_hint_count (mld_polyvec_make_hint_32 x b) (@P0@ + i)) /\\
             (!t. t < @OM@ ==> read (memory :> bytes8 (word_add sig (word (@H@ + t)))) s =
                             mld_hint_index (mld_polyvec_make_hint_32 x b) (@P0@ + i) t))");;

let SG_HR_EXEC c =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [(layout c.hr3_fn + c.hr3_lo, layout c.hr3_fn + c.hr3_hi)];;

(*** The arithmetic of SI_HROW for gamma2 = (q-1)/32 ***)

let SG_HR_UNF = prove
 (`!x b k i. i < 256
     ==> (mld_polyvec_make_hint_32 x b (256 * k + i) <=>
          mld_make_hint_32 (x (256 * k + i))
           (mld_polyw1_unpack_32 (\t. b (128 * k + t)) i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GLUE_POLYVEC_HINT_32] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP SI_HROW_DIVMOD th]));;

let SG_HR_CF = prove
 (`!v:int32. (&(val v) - &523777:int = &(val(word_sub v (word 523777)))) <=>
             ~(val v <= 523776)`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_SUB_CASES; DIMINDEX_32; VAL_WORD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `v:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THENL
   [ASM_ARITH_TAC;
    REWRITE_TAC[INT_ARITH `&a - &c:int = &b <=> &a:int = &b + &c`;
                INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ASM_ARITH_TAC]);;

let SG_HR_C0 = prove
 (`!a0 a1:int32.
     (if ~(~(a1 = word 0) /\ a0 = word 4294705408)
      then &(val (word_add a0 (word 261888))) - &523777:int =
           &(val (word_sub (word_add a0 (word 261888)) (word 523777)))
      else T) <=> mld_make_hint_32 a0 a1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SG_HR_CF; GLUE_INR_32] THEN
  ASM_CASES_TAC `glue_hint_inr_32 a0` THEN
  ASM_SIMP_TAC[GLUE_HINT_INR_32; GLUE_HINT_OUT_32] THEN
  ASM_CASES_TAC `~(a1:int32 = word 0) /\ a0:int32 = word 4294705408` THEN
  ASM_REWRITE_TAC[]);;

let SG_HR_INC32 om = prove
 (subst [mk_small_numeral om,`OM:num`]
  `!n. n < OM
       ==> word_zx (word_add (word_zx (word n:int64):int32) (word 1)):int64 =
           word (n + 1)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `n MOD 18446744073709551616 = n /\ n MOD 4294967296 = n /\
                (n + 1) MOD 4294967296 = n + 1 /\
                (n + 1) MOD 18446744073709551616 = n + 1`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

let SG_HR_TBNZ = prove
 (`!a0 a1:int32.
     glue_hint_inr_32 a0
     ==> ((if val (word_sub a0 (word 4294705408)) = 0
           then val (word_sub a1 (word 0)) = 0 else T) <=>
          ~mld_make_hint_32 a0 a1)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GLUE_HINT_INR_32] THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; WORD_SUB_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(*** The simulation of an iteration (SI_HROW_DECIDE_TAC etc. with the  ***)
(*** parameters)                                                       ***)

let SG_HR_TM k s = subst [mk_small_numeral(256 * k),`P0:num`;
                          mk_small_numeral(256 * (k + 1)),`P1:num`] s;;
let SG_HR_OMT c tm = subst [mk_small_numeral c.hr3_omega,`OM:num`;
                            mk_small_numeral c.hr3_hoff,`HO:num`]
                       (SG_HR_TM c.hr3_k tm);;
let SG_HR_CNT c = SG_HR_OMT c
  `mld_hint_count (mld_polyvec_make_hint_32 x b) (P0 + i)`;;
let SG_HR_FAIL c = SG_HR_OMT c
  `glue_hint_fail OM (mld_polyvec_make_hint_32 x b) (P0 + i)`;;
let SG_HR_H c = SG_HR_OMT c `mld_polyvec_make_hint_32 x b (P0 + i)`;;
let SG_HR_INR c = SG_HR_OMT c `glue_hint_inr_32 (x (P0 + i))`;;
let SG_HR_STEPS c = SG_HR_OMT c
  `glue_hint_steps OM P1 (mld_polyvec_make_hint_32 x b)`;;

let SG_HR_CNT_FACTS_TAC c (s:term) =
  let cnt = SG_HR_CNT c and om = mk_small_numeral c.hr3_omega in
  let ltom = mk_binop `(<):num->num->bool` cnt om in
  let ltom_tac = FIRST_ASSUM(MP_TAC o check (fun th -> concl th = ltom)) THEN
                 ARITH_TAC in
  SUBGOAL_THEN ltom ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> concl th = mk_neg(SG_HR_FAIL c))) THEN
    REWRITE_TAC[glue_hint_fail] THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o check (fun th ->
      concl th = mk_binop `(<=):num->num->bool` cnt om)) THEN
    ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC cnt VAL_WORD_ZX_UXTW) THEN ANTS_TAC THENL [ltom_tac; STRIP_TAC] THEN
  MP_TAC(SPEC cnt WORD_ZX_ZX_SMALL) THEN ANTS_TAC THENL [ltom_tac; DISCH_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,mk_comb(`word:num->int64`,cnt)),cnt))
  ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN ltom_tac;
    ALL_TAC] THEN
  SUBGOAL_THEN (vsubst [cnt,`c:num`; s,`s:armstate`] (SG_HR_OMT c
   `!t. t < OM /\ ~(t = c)
        ==> read(memory :> bytes8(word_add sig (word(HO + t)))) s =
            mld_hint_index (mld_polyvec_make_hint_32 x b) (P0 + i) t`))
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let SG_HR_HINT_OUT_TAC c =
  let th = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
             (SPECL [`x:num->int32`; `b:num->byte`; mk_small_numeral c.hr3_k; `i:num`]
                    SG_HR_UNF) in
  SUBGOAL_THEN (SG_HR_H c) ASSUME_TAC THENL
   [REWRITE_TAC[MP th (ASSUME `i < 256`)] THEN MATCH_MP_TAC GLUE_HINT_OUT_32 THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC];;

let SG_HR_DECIDE_TAC c (asl,w) =
  let th = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
             (SPECL [`x:num->int32`; `b:num->byte`; mk_small_numeral c.hr3_k; `i:num`]
                    SG_HR_UNF) in
  let uf = MP th (ASSUME `i < 256`) in
  let s = rand w in
  let om = mk_small_numeral c.hr3_omega in
  let pcfact th = let cc = concl th in
    is_eq cc && (lhs cc = mk_comb(`read PC`,s) || lhs cc = mk_comb(`read events`,s)) in
  let norm = REWRITE_RULE[SG_HR_CF; GLUE_INR_32] o REWRITE_RULE[GSYM uf] o
             REWRITE_RULE[SG_HR_C0] o
             REWRITE_RULE[WORD_ZX_ZX_32_64_32; GLUE_CCMP_EQ] in
  (RULE_ASSUM_TAC(fun th -> if pcfact th then norm th else th) THEN
   W(fun (asl,w) ->
     let c0,_ = dest_cond(hrow_current_pc (asl,w)) in
     let cd = if is_neg c0 then rand c0 else c0 in
     let occurs t = can (find_term ((=) t)) cd in
     let canon eq =
       RULE_ASSUM_TAC(fun th -> if pcfact th then REWRITE_RULE[eq] th else th) in
     if cd = SG_HR_H c then SI_HROW_CASES_TAC cd
     else if cd = SG_HR_INR c then
       SI_HROW_CASES_TAC cd THENL [ALL_TAC; SG_HR_HINT_OUT_TAC c]
     else if occurs `word 18446744073709551361:int64` then
       canon(MP (SPEC `i:num` GLUE_J_TEST) (ASSUME `i < 256`)) THEN
       SI_HROW_CASES_TAC `i < 255`
     else if occurs (SG_HR_CNT c) then
       let fl = SG_HR_FAIL c in
       SUBGOAL_THEN (mk_iff(cd,fl)) canon THENL
        [REWRITE_TAC[glue_hint_fail; ASSUME (SG_HR_H c)] THEN
         MATCH_MP_TAC GLUE_W32_EQ THEN CONV_TAC NUM_REDUCE_CONV THEN
         FIRST_ASSUM(MP_TAC o check (fun th ->
           concl th = mk_binop `(<=):num->num->bool` (SG_HR_CNT c) om)) THEN
         ARITH_TAC;
         ALL_TAC] THEN
       SI_HROW_CASES_TAC fl THENL [ALL_TAC; SG_HR_CNT_FACTS_TAC c s]
     else if is_comb cd && rator(rator cd) = `bit:num->int32->bool` ||
             is_comb cd && rator(rator cd) = `bit:num->int64->bool` then
       let h = SG_HR_H c in
       SUBGOAL_THEN (mk_iff(cd,mk_neg h)) canon THENL
        [REWRITE_TAC[SI_HROW_BIT0; NOT_CLAUSES; uf] THEN
         MATCH_MP_TAC SG_HR_TBNZ THEN FIRST_ASSUM ACCEPT_TAC;
         ALL_TAC] THEN
       SI_HROW_CASES_TAC h
     else failwith ("SG_HR_DECIDE_TAC: " ^ string_of_term cd))) (asl,w);;

let SG_HR_NOFAIL_TAC =
  FIRST_ASSUM ACCEPT_TAC ORELSE (REWRITE_TAC[glue_hint_fail] THEN ASM_REWRITE_TAC[]);;

let SG_HR_NEXT_TAC c =
  let k = c.hr3_k in
  let p0 = 256 * k and p1 = 256 * (k + 1) in
  let p = mk_binop `(+):num->num->num` (mk_small_numeral p0) `i:num` in
  MP_TAC(SPECL [`mld_polyvec_make_hint_32 x b`; mk_small_numeral c.hr3_omega;
                mk_small_numeral p1; p] GLUE_HINT_NEXT) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  W(fun (asl,w) ->
    let fl = SG_HR_FAIL c in
    let has t = exists (fun (_,th) -> concl th = t) asl in
    if has fl then DISCH_THEN(MP_TAC o C MP (ASSUME fl) o CONJUNCT1) THEN STRIP_TAC
    else
    (if has (mk_neg fl) then ALL_TAC
     else SUBGOAL_THEN (mk_neg fl) ASSUME_TAC THENL [SG_HR_NOFAIL_TAC; ALL_TAC]) THEN
    if has `~(i < 255)` then
      DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL [CONJ_TAC THENL [SG_HR_NOFAIL_TAC; SI_HROW_IDX_ARITH_TAC];
                      STRIP_TAC]
    else
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      ANTS_TAC THENL [CONJ_TAC THENL [SG_HR_NOFAIL_TAC; SI_HROW_IDX_ARITH_TAC];
                      STRIP_TAC]);;

let SG_HR_STEPS_LT_TAC c =
  let tm = SG_HR_OMT c
   `i + 1 < glue_hint_steps OM P1 (mld_polyvec_make_hint_32 x b) - P0 <=>
    (P0 + i) + 1 < glue_hint_steps OM P1 (mld_polyvec_make_hint_32 x b)` in
  SUBGOAL_THEN tm SUBST1_TAC THENL [ARITH_TAC; ALL_TAC];;

let SG_HR_BYTES_TAC c =
  let bth = MP (SPECL [mk_small_numeral c.hr3_k; `i:num`] SI_HROW_BYTE)
               (ASSUME `i < 256`) in
  let bth = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) bth in
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN REWRITE_TAC[MLD_HINT_INDEX_ADD1] THEN
  ASM_REWRITE_TAC[] THEN
  TRY(COND_CASES_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_eq o concl)) THEN ASM_REWRITE_TAC[bth] THEN
    NO_TAC;
    ALL_TAC]) THEN
  TRY(FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let SG_HR_EVENTS_TAC c =
  let inr = SG_HR_INR c in
  REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  W(fun (asl,w) ->
    if free_in inr w then ASM_CASES_TAC inr THEN ASM_REWRITE_TAC[]
    else ALL_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let SG_HR_REGS_TAC c =
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD; MULT_CLAUSES]) THEN
  TRY(FIRST_ASSUM(fun th ->
    if is_comb(concl th) &&
       can (term_match [] (subst [mk_small_numeral c.hr3_omega,`OM:num`]
                                 `mld_hint_count h p < OM`)) (concl th)
    then RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP (SG_HR_INC32 c.hr3_omega) th])
    else NO_TAC));;

let SG_HR_FINAL_TAC c =
  SG_HR_REGS_TAC c THEN
  SG_HR_NEXT_TAC c THEN ENSURES_FINAL_STATE_TAC THEN
  SG_HR_STEPS_LT_TAC c THEN
  ASM_REWRITE_TAC[GSYM ADD_ASSOC; LT_REFL] THEN
  REWRITE_TAC[ADD_ASSOC; MLD_HINT_COUNT_ADD1] THEN ASM_REWRITE_TAC[ADD_0] THEN
  REPEAT CONJ_TAC THEN
  TRY(SG_HR_BYTES_TAC c THEN NO_TAC) THEN
  SG_HR_EVENTS_TAC c;;

let rec SG_HR_RUN_TAC c ex n (asl,w) =
  let pct = hrow_current_pc (asl,w) in
  let tgt l = mk_comb(`word:num->int64`,
                mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral(layout l))) in
  if n > 1 && mem pct (map tgt [c.hr3_head; c.hr3_exit; c.hr3_head ^ "_exit1"]) then
    SG_HR_FINAL_TAC c (asl,w)
  else if is_cond pct then
    (SG_HR_DECIDE_TAC c THEN SG_HR_RUN_TAC c ex n) (asl,w)
  else (ARM_STEPS_TAC ex [n] THEN SG_HR_RUN_TAC c ex (n + 1)) (asl,w);;

let SG_HR_BODY_TAC c ex =
  let k = c.hr3_k and om = mk_small_numeral c.hr3_omega in
  let p0 = mk_small_numeral(256 * k) in
  let steps = SG_HR_STEPS c in
  let n = mk_binop `(-):num->num->num` steps p0 in
  let lt_n = mk_binop `(<):num->num->bool` `i:num` n in
  let p_lt = mk_binop `(<):num->num->bool` (mk_binop `(+):num->num->num` p0 `i:num`) steps in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN p_lt ASSUME_TAC THENL
   [UNDISCH_TAC lt_n THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `i < 256` ASSUME_TAC THENL
   [UNDISCH_TAC p_lt THEN
    FIRST_ASSUM(MP_TAC o check (fun th ->
      concl th = mk_binop `(<=):num->num->bool` steps (mk_small_numeral(256 * (k + 1))))) THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (mk_binop `(<=):num->num->bool` (SG_HR_CNT c) om) ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (term_match [] (subst [om,`OM:num`]
             `!p. p < n ==> mld_hint_count h p <= OM`)) (concl th))) THEN
    FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASSUME lt_n] THEN
  FULL_INIT_TAC THEN
  SI_HROW_SPEC_TAC (parse_term(Printf.sprintf
    "!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (%d + 4 * i)))) s0 = y i"
    c.hr3_woff)) THEN
  SI_HROW_SPEC_TAC (parse_term(Printf.sprintf
    "!i. i < 256 ==> read (memory :> bytes32 (word_add fp (word (%d + 4 * i)))) s0 = y i"
    c.hr3_w1off)) THEN
  VAL_INT64_TAC `i:num` THEN
  SG_HR_RUN_TAC c ex 1;;

let SG_HR_EXIT_TAC c =
  let cntok = SG_HR_OMT c `mld_hint_count (mld_polyvec_make_hint_32 x b) P1 <= OM` in
  let steps_eq = SG_HR_OMT c
    `glue_hint_steps OM P1 (mld_polyvec_make_hint_32 x b) = P1` in
  let fin = FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
            (DISCHARGE_SAFETY_PROPERTY_TAC ORELSE SI_CLOSED_E2_TAC) in
  ASM_CASES_TAC cntok THENL
   [SUBGOAL_THEN steps_eq SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_imp(concl th) && lhand(concl th) = cntok)) THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN fin;
    ASM_REWRITE_TAC[] THEN fin];;

let SG_HROW32_PROVE c =
  let ex = SG_HR_EXEC c and k = c.hr3_k in
  let om = mk_small_numeral c.hr3_omega in
  let p0 = mk_small_numeral(256 * k) and p1 = mk_small_numeral(256 * (k + 1)) in
  let pcn l = mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral(layout l)) in
  prove(SG_HR_TERM c,
  CONCRETIZE_F_EVENTS_TAC (SG_HR_TEMPLATE c) THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `x:num->int32`; `b:num->byte`;
                       `sig:int64`; `fp:int64`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst ex] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`mld_polyvec_make_hint_32 x b`; om; p1] GLUE_HINT_STEPS) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC (mk_binop `(-):num->num->num` (SG_HR_STEPS c) p0)
   (pcn c.hr3_head)
   (mk_cond(SG_HR_OMT c `mld_hint_count (mld_polyvec_make_hint_32 x b) P1 <= OM`,
            pcn c.hr3_exit, pcn (c.hr3_head ^ "_exit1")))
   (SG_HR_INV c) THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`mld_polyvec_make_hint_32 x b`; om; p0; p1] SI_HROW_STEPS_POS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ARITH_TAC];
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    SG_HR_BODY_TAC c ex;
    SG_HR_EXIT_TAC c]);;

(* ------------------------------------------------------------------------- *)
(* G1A: the absorbing of the inlined poly_uniform_gamma1 (G1_A of            *)
(* inline_sign_gamma1.ml, for the code of 65 and 87): rho'' (64 bytes at rp) *)
(* is copied to the input buffer at sp + io with the nonce nb + j (16 bits   *)
(* by two STRB), the state at sp + so (200 bytes and the position after it) *)
(* is zeroed, and the code XORs the input and the padding into it with      *)
(* vector and byte stores. ga_pre gives where the code finds rp, nb and j   *)
(* (frame slots or registers), ga_post the registers of the squeeze loop    *)
(* that the region sets. The schedule differs between the functions, so the *)
(* points where the proof splits zero vectors into bytes (before the byte    *)
(* stores and loads that overlap them) and makes the 16-bit nonce from its  *)
(* two bytes are given as a plan: (n, actions) with the actions done in      *)
(* state n: ("split",off) splits the zero 128-bit fact at sp + off into     *)
(* bytes, ("zero16",off) makes the zero 16-bit fact there from them, and     *)
(* ("nonce",off) the 16-bit nonce at sp + off from its two bytes, and       *)
(* ("nonce16",off) the nonce that STRH has stored there as word(nb + j).     *)
(* ------------------------------------------------------------------------- *)

type g1a_inst =
  { ga_start : string; ga_stop : string; ga_steps : int;
    ga_pre : string; ga_post : string; ga_so : int; ga_io : int;
    ga_slots : (int * int) list; ga_mods : string list;
    ga_plan : (int * (string * int) list) list };;

let SG_G1A_TERM mc p =
  let sl = String.concat "" (map (fun (oo,l) ->
             Printf.sprintf "; (word_add sp (word %d),%d)" oo l) p.ga_slots) in
  let sr = String.concat "" (map (fun (oo,l) ->
             Printf.sprintf "; word_add sp (word %d),%d" oo l) p.ga_slots) in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e (rp:int64) RHO nb j (sp:int64) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        aligned 16 sp /\\
        ALL (nonoverlapping (word_add sp (word %d),204))
            [(word pc,libmldsa_size); (rp,64); (word_add sp (word %d),66)%s] /\\
        ALL (nonoverlapping (word_add sp (word %d),66))
            [(word pc,libmldsa_size); (rp,64)%s]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read SP s = sp /\\ %s
                  read (memory :> bytes(rp,64)) s = RHO /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\
                  read SP s = sp /\\ %s
                  read (memory :> wbytes (word_add sp (word %d))) s =
                    mld_keccak_absorb_once 136 0x1F 66
                     (RHO + 2 EXP 512 * val(word(nb + j):int16)) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events rp sp pc /\\
                     memaccess_inbounds e2
                      [rp,64; word_add sp (word %d),66; word_add sp (word %d),204%s]
                      [word_add sp (word %d),66; word_add sp (word %d),204]))
             (MAYCHANGE [PC; %s] ,,
              MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7] ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(word_add sp (word %d),66);
                         memory :> bytes(word_add sp (word %d),204)])"
   p.ga_so p.ga_io sl p.ga_io sl mc p.ga_start p.ga_pre
   p.ga_stop p.ga_post p.ga_so p.ga_io p.ga_so sr p.ga_io p.ga_so
   (String.concat "; " p.ga_mods) p.ga_io p.ga_so);;

(*** The 16-bit nonce at sp + off from its two bytes: the bytes of the     ***)
(*** 32-bit sum nb + j that STRB stores (the value w and w >> 8), joined    ***)

let SG_ZX_WORD_64_32 = prove
 (`!n. word_zx (word n:int64):int32 = word n`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  CONV_TAC(DEPTH_CONV NUM_MIN_CONV) THEN REWRITE_TAC[]);;

let SG_ZX_WORD_32_16 = prove
 (`!n. word_zx (word n:int32):int16 = word n`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  CONV_TAC(DEPTH_CONV NUM_MIN_CONV) THEN REWRITE_TAC[]);;

let SG_G1_NONCE_TAC off s =
  let tm = subst [s,`s:armstate`; mk_small_numeral off,`OFF:num`]
    `read (memory :> bytes16 (word_add sp (word OFF))) s = word(nb + j)` in
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [REWRITE_TAC[el 4 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT); G1_PTR_ADD;
                GSYM ADD_ASSOC] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WORD_ZX_ZX_32_64_32; SG_ZX_WORD_64_32; GSYM WORD_ADD;
                GSYM SG_ZX_WORD_32_16] THEN
    SPEC_TAC(`word(nb + j):int32`,`w:int32`) THEN CONV_TAC WORD_BLAST;
    ALL_TAC];;

(*** The nonce stored by STRH of the 16 low bits of nb + j: its value as  ***)
(*** word(nb + j) (G1_NONCE_TAC of inline_sign_gamma1.ml at sp + off)      ***)

let SG_G1_NONCE16_TAC off s =
  W(fun (asl,w) ->
    let pat = subst [s,`s:armstate`; mk_small_numeral off,`OFF:num`]
                `read (memory :> bytes16 (word_add sp (word OFF))) s` in
    let th = snd(find (fun (_,th) -> is_eq(concl th) && lhs(concl th) = pat) asl) in
    let v = rhs(concl th) in
    let lem = prove(mk_eq(v,`word(nb + j):int16`),
      REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD] THEN
      CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
      CONV_TAC(DEPTH_CONV NUM_MIN_CONV) THEN
      ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
      CONV_TAC(DEPTH_CONV NUM_MIN_CONV) THEN REWRITE_TAC[]) in
    RULE_ASSUM_TAC(REWRITE_RULE[lem]));;

let SG_G1A_ACT_TAC n a =
  let sn = "s" ^ string_of_int n in
  match a with
    "split",off -> G1_ZSPLIT_TAC sn off
  | "zero16",off -> G1_ZLD_TAC sn 2 off
  | "nonce",off -> SG_G1_NONCE_TAC off (mk_var(sn,`:armstate`))
  | "nonce16",off -> SG_G1_NONCE16_TAC off (mk_var(sn,`:armstate`))
  | _ -> failwith "SG_G1A_ACT_TAC";;

let SG_G1A_PROVE mc p =
  let exec = INLINE_LOOP_EXEC p.ga_start p.ga_stop in
  let rec run k plan =
    match plan with
      [] -> if k <= p.ga_steps then ARM_STEPS_TAC exec (k--p.ga_steps) else ALL_TAC
    | (n,acts)::rest ->
        (if k <= n then ARM_STEPS_TAC exec (k--n) else ALL_TAC) THEN
        MAP_EVERY (SG_G1A_ACT_TAC n) acts THEN run (n + 1) rest in
  let sn = "s" ^ string_of_int p.ga_steps in
  prove(SG_G1A_TERM mc p,
  CONCRETIZE_F_EVENTS_TAC
   `\(rp:int64) (sp:int64) (pc:num). f_ev_a rp sp pc:(uarch_event)list` THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rp:int64`; `RHO:num`; `nb:num`;
                       `j:num`; `sp:int64`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  FIRST_ASSUM(MP_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o MATCH_MP G1_READ_BYTES_BOUND o
    check (can (term_match [] `read (memory :> bytes(rp:int64,64)) s0 = RHO`) o concl)) THEN
  DISCH_TAC THEN
  G1_RP_FACTS_TAC `s0:armstate` THEN
  run 1 p.ga_plan THEN
  G1_CHAIN_TAC sn p.ga_so THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[G1_S_WORD; G1_M_BOUND; G1_M_JOIN] THEN
    REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN
    FIRST_X_ASSUM(fun th ->
      if can (term_match [] (subst [mk_small_numeral p.ga_so,`OFF:num`]
          `read (memory :> bytes(word_add sp (word OFF),200)) s = x`))
             (concl th)
      then ACCEPT_TAC (REWRITE_RULE[G1_MODLEMMA] th) else NO_TAC);
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* CADDQI: poly_caddq of the polynomial at a + k0 (INLINE_CADDQK_LOOP of     *)
(* inline_sign_sig.ml) with the index register R2 counting coefficients     *)
(* from k0 / 4 to k0 / 4 + 256 (LDRSW/STR with LSL #2, ADD #1).             *)
(* ------------------------------------------------------------------------- *)

let SG_CADDQI_LOOP_TERM mc loop exit k0 (rs:string list) =
  let r k = List.nth rs k in
  let c0 = k0 / 4 in
  let addr = Printf.sprintf "word_add a (word(%d + 4 * i))" k0 in
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
   k0 mc loop (r 1) (r 2) c0 (r 5) addr exit (r 2) (c0 + 256) addr k0 k0
   (r 2) (r 0) (r 3) (r 4) k0);;

let SG_CADDQI_LOOP mc exec loop exit k0 (rs:string list) =
  let r k = List.nth rs k in
  let c0 = k0 / 4 in
  let tm = SG_CADDQI_LOOP_TERM mc loop exit k0 rs in
  let addrj = Printf.sprintf "word_add a (word(%d + 4 * j))" k0 in
  let inv = parse_term(Printf.sprintf
   "\\i s. read %s s = a /\\ read %s s = word(%d + i) /\\
          read %s s = word 8380417 /\\
          (!j. i <= j /\\ j < 256
               ==> read(memory :> bytes32(%s)) s = (x:num->int32) j) /\\
          (!j. j < i
               ==> read(memory :> bytes32(%s)) s = mld_caddq (x j))"
   (r 1) (r 2) c0 (r 5) addrj addrj) in
  let aeq = prove(parse_term(Printf.sprintf
    "word_add (a:int64) (word (4 * (%d + i))) = word_add a (word (%d + 4 * i))"
    c0 k0), AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC) in
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
    VAL_INT64_TAC (parse_term(Printf.sprintf "%d + i" c0)) THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [] (parse_term(Printf.sprintf
           "read(memory :> bytes32(word_add a (word(%d + 4 * i)))) s0 = y" k0)))
           (concl th)
      then ASSUME_TAC(REWRITE_RULE[GSYM aeq] th) else NO_TAC) THEN
    ARM_STEPS_TAC exec (1--8) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[aeq]) THEN
    INLINE_CADDQ_LANE_TAC THEN
    ARM_STEPS_TAC exec (9--11) THEN
    FULL_FINAL_TAC [ONE_OUTPUT_SPLIT];

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* G1M: the whole inlined poly_uniform_gamma1 for gamma1 = 2^19 (G1_MAIN of *)
(* inline_sign_gamma1.ml): the absorbing (an SG_G1A lemma, step 1), the     *)
(* squeeze loop (a G1_SQZ lemma, step 2), gm_n1 instructions that set up    *)
(* the unpacking, the polyz_unpack loop (an SG_Z19S lemma), and gm_n2       *)
(* instructions that zero the state and call memset on the buffer. The       *)
(* frame base is fr = SP - 240 (the frame of mldsa_keccakf1600_permute), the *)
(* offsets of the record are from SP: the input buffer (io, 66 bytes), the  *)
(* state (so, 208 bytes with the position and the zeroing), the squeeze     *)
(* buffer (bo, 680) and the output polynomial (zo, 1024). gm_pre states     *)
(* where the code finds rp, nb and j and the setup of the unpacking (in     *)
(* terms of fr), gm_post what else the region leaves (ADRPs in the gm_n1    *)
(* instructions are normalized, so their pages can be stated there).        *)
(* ------------------------------------------------------------------------- *)

type g1m_inst =
  { gm_start : string; gm_stop : string; gm_sqzx : int; gm_sqzl : string;
    gm_sqz : string * string * string * string * string; gm_zl : string;
    gm_io : int; gm_so : int; gm_bo : int; gm_zo : int;
    gm_slots : (int * int) list; gm_pre : string; gm_post : string;
    gm_n1 : int; gm_n2 : int; gm_mods : string list };;

let SG_G1M_TERM mc p =
  let f ofs = 240 + ofs in
  let regs = [f p.gm_io,66; f p.gm_so,208; f p.gm_bo,680; f p.gm_zo,1024] in
  let rl l = String.concat "; " (map (fun (oo,n) ->
               Printf.sprintf "(word_add fr (word %d),%d)" oo n) l) in
  let ml l = String.concat "; " (map (fun (oo,n) ->
               Printf.sprintf "word_add fr (word %d),%d" oo n) l) in
  let sl = map (fun (oo,n) -> f oo,n) p.gm_slots in
  parse_term(Printf.sprintf
  "!mf mc ea el ev.
     memset_full_contract mf ea el ev /\\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e (rp:int64) RHO nb j (fr:int64) pc.
          aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
          aligned 16 (word_add fr (word 240)) /\\
          PAIRWISE nonoverlapping [(fr,240); %s; %s] /\\
          ALLPAIRS nonoverlapping [(fr,240); %s]
           [(rp,64); (word pc,libmldsa_size);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\\s. aligned_bytes_loaded s (word pc) %s /\\
                    read PC s = word (pc + %s) /\\
                    read SP s = word_add fr (word 240) /\\ %s
                    read (memory :> bytes(rp,64)) s = RHO /\\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                    read (memory :> bytes(ea,el)) s = ev /\\
                    read events s = e)
               (\\s. read PC s = word (pc + %s) /\\
                    read SP s = word_add fr (word 240) /\\ %s
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\\
                    read (memory :> bytes(ea,el)) s = ev /\\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add fr (word(%d + 4 * i))))
                               s = mld_poly_uniform_gamma1_19 RHO (word(nb + j)) i) /\\
                    (exists e2.
                       read events s = APPEND e2 e /\\
                       e2 = f_events rp mf mc pc fr /\\
                       memaccess_inbounds e2
                        [rp,64; fr,240; %s; %s;
                         word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [fr,240; %s]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
                MAYCHANGE [%s] ,,
                MAYCHANGE [memory :> bytes(fr,240); %s])"
   (rl regs) (rl sl) (rl regs) mc p.gm_start p.gm_pre p.gm_stop p.gm_post
   (f p.gm_zo) (ml regs) (ml sl) (ml regs) (String.concat "; " p.gm_mods)
   (String.concat "; " (map (fun (oo,n) ->
      Printf.sprintf "memory :> bytes(word_add fr (word %d),%d)" oo n) regs)));;

let SG_G1M_PROVE mc p (tha,thsqz,thz) =
  let exec = G1_EXEC_PLT p.gm_start p.gm_stop in
  let allowed = [`rp:int64`; `mf:int64`; `mc:int64`; `pc:num`; `fr:int64`] in
  let call name ilist n = FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
                            exec name ilist allowed n in
  let fo ofs = mk_small_numeral(240 + ofs) in
  let fra ofs = mk_comb(mk_comb(`word_add:int64->int64->int64`,`fr:int64`),
                      mk_comb(`word:num->int64`,fo ofs)) in
  let n1 = p.gm_n1 and n2 = p.gm_n2 in
  let zstep = 3 + n1 in
  let sqb = `mld_keccak_squeeze_byte 136
               (mld_keccak_absorb_once 136 0x1F 66
                 (RHO + 2 EXP 512 * val(word(nb + j):int16))) 136` in
  prove(SG_G1M_TERM mc p,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    let ms,mcp = CONJ_PAIR th in
    ASSUME_CALLEE_SAFETY_TAILED_TAC
      (MP (SPECL [`mc:int64`;`ea:int64`;`el:num`;`ev:num`] thsqz) mcp) "H_SQZ" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC (REWRITE_RULE[memset_full_contract] ms) "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC tha "H_A" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC thz "H_Z" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(rp:int64) (mf:int64) (mc:int64) (pc:num) (fr:int64). f_ev_main rp mf mc pc fr:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rp:int64`; `RHO:num`; `nb:num`; `j:num`;
                       `fr:int64`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE] THEN
  DISCH_THEN(fun th -> (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) th THEN
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)(REWRITE_RULE[NONOVERLAPPING_CLAUSES; fst exec] th)) THEN
  MAP_EVERY (fun g -> REWRITE_TAC[SPECL [`pc:num`; g] WORD_ADD] THEN
                      RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; g] WORD_ADD]))
    [`got_memset:num`; `got_memcpy:num`] THEN
  FULL_INIT_TAC THEN
  call "H_A" [`rp:int64`; `RHO:num`; `nb:num`; `j:num`; `word_add fr (word 240):int64`; `pc:num`] 1 THEN
  G1_NORM_ASM_TAC THEN
  call "H_SQZ" [`mld_keccak_absorb_once 136 0x1F 66 (RHO + 2 EXP 512 * val(word(nb + j):int16))`;
                `fr:int64`; `pc:num`] 2 THEN
  ARM_STEPS_TAC exec (3--(zstep - 1)) THEN MLKEM_NATIVE_ADRP_TAC THEN
  SUBGOAL_THEN (subst [sqb,`b:num->byte`; fo p.gm_bo,`B:num`;
                       mk_var("s"^string_of_int(zstep-1),`:armstate`),`s:armstate`]
   `!i. i < 640 ==> read (memory :> bytes8 (word_add fr (word (B + i)))) s =
                    (b:num->byte) i`) ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  call "H_Z" [fra p.gm_zo; fra p.gm_bo; sqb; `pc:num`] zstep THEN
  ARM_STEPS_TAC exec ((zstep + 1)--(zstep + n2)) THEN
  LIBC_PLT_TAC exec (zstep + n2) THEN
  G1_LIBC_CALL_TAC "H_MEMSET" exec
    [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`]
    [`rp:int64`; `mf:int64`; `mc:int64`; `pc:num`; `fr:int64`] (zstep + n2 + 5) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[mld_poly_uniform_gamma1_19; mld_shake256_stream] THEN
  ASM_REWRITE_TAC[] THEN G1_SAFETY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Vectors of constants in the image: the n 16-byte vectors at pc + d, as    *)
(* facts at word_add (word pc) (word (d + 16 k)) under aligned_bytes_loaded. *)
(* ------------------------------------------------------------------------- *)

let SG_VAL_WORD128 = prove
 (`!(x:int128) n. val x = n ==> x = word n`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[WORD_VAL]);;

let SG_IMAGE_VECS d n =
  let bytes = dest_list(rhs(concl mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc)) in
  map (fun k ->
    let off = d + 16 * k in
    let l = mk_list(fst(chop_list 16 (snd(chop_list off bytes))),`:byte`) in
    let lth = MLDSA_NATIVE_IMAGE_DATA_RULE (REFL l) off
    and lenth = LENGTH_CONV(mk_comb(`LENGTH:byte list->num`,l)) in
    let nth = (REWRITE_CONV[num_of_bytelist] THENC DEPTH_CONV WORD_RED_CONV THENC
               REWRITE_CONV[DIMINDEX_8] THENC NUM_REDUCE_CONV)
              (mk_comb(`num_of_bytelist`,l)) in
    let v = rand(concl nth) in
    let th16 = prove
     (mk_forall(`s:armstate`,mk_forall(`pc:num`,
        mk_imp(`aligned_bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc`,
          mk_eq(parse_term(Printf.sprintf "read (memory :> bytes(word(pc + %d),16)) s" off),v)))),
      REPEAT GEN_TAC THEN
      DISCH_THEN(MP_TAC o MATCH_MP lth) THEN
      REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES; lenth; nth]) in
    prove
     (mk_forall(`s:armstate`,mk_forall(`pc:num`,
        mk_imp(`aligned_bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc`,
          mk_eq(parse_term(Printf.sprintf
                  "read (memory :> bytes128 (word_add (word pc) (word %d))) s" off),
                mk_comb(`word:num->int128`,v))))),
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SG_VAL_WORD128 THEN
      REWRITE_TAC[GSYM G1_B16; GSYM WORD_ADD] THEN ASM_SIMP_TAC[th16]))
   (0--(n-1));;

let SG_IMAGE_VECS_TAC ths =
  MAP_EVERY (fun th -> FIRST_ASSUM(fun a ->
    if can (term_match [] `aligned_bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc`) (concl a)
    then ASSUME_TAC(MATCH_MP th a) else NO_TAC)) ths;;

(* ------------------------------------------------------------------------- *)
(* W1U32: polyw1_unpack_32 of row k in pack_sig_h as straight-line code (the *)
(* region between two hint loops): the 128 packed bytes b at F + w3_in, AND  *)
(* and USHR split the nibbles, ZIP and UXTL spread them to 32-bit lanes, and *)
(* 64 STR Q store the 256 coefficients at F + w3_out. The region also does   *)
(* the glue of the rows (the count byte of the row before, the c~ copy and   *)
(* the zeroing of the hints before row 0), given as strings: w3_bind (more   *)
(* variables), w3_nov (more hypotheses), w3_pre, w3_post, w3_rd / w3_wr      *)
(* (more regions read / written, as "addr,len"), w3_mods; w3_plan lists the  *)
(* steps after which a zero 128-bit fact (at the address of the string) is   *)
(* split into bytes, before an overlapping store.                            *)
(* ------------------------------------------------------------------------- *)

type w1u32_inst =
  { w3_start : string; w3_stop : string; w3_steps : int;
    w3_in : int; w3_out : int; w3_bind : string; w3_nov : string;
    w3_pre : string; w3_post : string; w3_rd : string list; w3_wr : string list;
    w3_ev : string; w3_mods : string list; w3_plan : (int * string list) list };;

let SG_W1U32_TERM mc p =
  let ex l = String.concat "" (map (fun r -> "; " ^ r) l) in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e (fp:int64) (b:num->byte) %s pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        aligned 16 fp /\\ %s
        ALL (nonoverlapping (word_add fp (word %d),1024))
            [(word pc,libmldsa_size); (word_add fp (word %d),128)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read SP s = fp /\\ %s
                  (!j. j < 128
                       ==> read(memory :> bytes8(word_add fp (word(%d + j)))) s =
                           b j) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\ read SP s = fp /\\ %s
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add fp (word(%d + 4 * i)))) s =
                           mld_polyw1_unpack_32 b i) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events fp %s pc /\\
                     memaccess_inbounds e2
                      [word_add fp (word %d),128; word_add fp (word %d),1024%s]
                      [word_add fp (word %d),1024%s]))
             (MAYCHANGE [PC; %s] ,,
              MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q8; Q9; Q10; Q11; Q12;
                         Q13; Q14; Q15; Q16; Q17; Q18; Q19; Q20; Q21; Q22; Q23;
                         Q24; Q25; Q26; Q27; Q28; Q29; Q30; Q31] ,,
              MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(word_add fp (word %d),1024)%s])"
   p.w3_bind p.w3_nov p.w3_out p.w3_in mc p.w3_start p.w3_pre p.w3_in
   p.w3_stop p.w3_post p.w3_out p.w3_ev p.w3_in p.w3_out (ex p.w3_rd)
   p.w3_out (ex p.w3_wr) (String.concat "; " p.w3_mods) p.w3_out
   (String.concat "" (map (fun r -> "; memory :> bytes(" ^ r ^ ")") p.w3_wr)));;

(*** The input bytes at base + (off + j) as 128-bit facts at base + off + 16 m ***)

let SG_INPUT128_TAC (base:term) off n =
  let pat = if off = 0 then subst [base,`B:int64`]
      `!j. j < N ==> read(memory :> bytes8(word_add B (word j))) s0 = b j`
    else subst [base,`B:int64`; mk_small_numeral off,`OFF:num`]
      `!j. j < N ==> read(memory :> bytes8(word_add B (word (OFF + j)))) s0 = b j` in
  let pat = subst [mk_small_numeral(16 * n),`N:num`] pat in
  FIRST_ASSUM(fun th ->
    if can (term_match [] pat) (concl th) then
      let bths = map (fun j ->
        CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
         (MP (SPEC (mk_small_numeral j) th)
             (EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool` (mk_small_numeral j)
                                                (mk_small_numeral(16 * n)))))))
        (0--(16 * n - 1)) in
      let merged = map (fun m ->
        let addr = mk_comb(mk_comb(`word_add:int64->int64->int64`,base),
                     mk_comb(`word:num->int64`,mk_small_numeral(off + 16 * m))) in
        let tm = subst [addr,`A:int64`] `read (memory :> bytes128 A) (s0:armstate)` in
        let mth = CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV))
                    (READ_MEMORY_MERGE_CONV 4 tm) in
        REWRITE_RULE bths mth) (0--(n-1)) in
      let extra = if off <> 0 then [] else
        [REWRITE_RULE[WORD_ADD_0] (hd merged)] in
      MAP_EVERY ASSUME_TAC (merged @ extra)
    else NO_TAC);;

(*** Split a zero 128-bit fact at the address tm (state sn) into bytes ***)

let SG_ZSPLIT_TAC (tm:string) sn =
  let s = mk_var(sn,`:armstate`) in
  let a = parse_term("(" ^ tm ^ "):int64") in
  let ftm = subst [s,`s0:armstate`; a,`A:int64`]
    `read (memory :> bytes128 A) s0 = word 0:int128` in
  FIRST_ASSUM(fun th ->
    if concl th = ftm then
      let th1 = REWRITE_RULE G1_UNSPLIT th in
      let th2 = CONV_RULE(DEPTH_CONV NUM_ADD_CONV) th1 in
      let ths = map (CONV_RULE(DEPTH_CONV(WORD_SIMPLE_SUBWORD_CONV))) (CONJUNCTS th2) in
      MAP_EVERY ASSUME_TAC ths
    else NO_TAC);;

(*** After the simulation: the 128-bit stores in [F + out, F + out + 1024) ***)
(*** as their four 32-bit lanes, simplified                                ***)

let SG_LANES128_TAC out =
  let ok a = try
      let bb,oo = dest_binop `word_add:int64->int64->int64` a in
      bb = `fp:int64` &&
      (let n = dest_small_numeral(rand oo) in n >= out && n < out + 1024)
    with Failure _ -> false in
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    try let l,_ = dest_eq c in
        let comp = rand(rator l) in
        let bytesf,addr = dest_comb(rand comp) in
        if fst(dest_const bytesf) = "bytes128" && ok addr then
          STRIP_ASSUME_TAC
           (CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                      ONCE_DEPTH_CONV NUM_REDUCE_CONV)
              (CONV_RULE(READ_MEMORY_SPLIT_CONV 2) th))
        else NO_TAC
    with Failure _ -> NO_TAC)) THEN
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c && not(is_forall c) &&
       can (find_term (fun t -> try fst(dest_const t) = "bytes32"
                                with Failure _ -> false)) (lhs c) &&
       free_in `fp:int64` (lhs c)
    then CONV_RULE(RAND_CONV(SIMD_SIMPLIFY_CONV [] THENC Z19_LANES_CONV)) th
    else th);;

let SG_ZX_WORD_64_8 = prove
 (`!n. word_zx (word n:int64):byte = word n`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  CONV_TAC(DEPTH_CONV NUM_MIN_CONV) THEN REWRITE_TAC[]);;

let SG_ZX_WORD_32_8 = prove
 (`!n. word_zx (word n:int32):byte = word n`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  CONV_TAC(DEPTH_CONV NUM_MIN_CONV) THEN REWRITE_TAC[]);;

let SG_W1U32_PROVE mc p =
  let exec = INLINE_LOOP_EXEC p.w3_start p.w3_stop in
  let rec run k plan =
    match plan with
      [] -> if k <= p.w3_steps
            then MAP_EVERY (fun n -> ARM_STEPS_TAC exec [n] THEN ETA_NORM) (k--p.w3_steps)
            else ALL_TAC
    | (n,addrs)::rest ->
        (if k <= n then MAP_EVERY (fun j -> ARM_STEPS_TAC exec [j] THEN ETA_NORM) (k--n)
         else ALL_TAC) THEN
        MAP_EVERY (fun a -> SG_ZSPLIT_TAC a ("s" ^ string_of_int n)) addrs THEN
        run (n + 1) rest in
  prove(SG_W1U32_TERM mc p,
  CONCRETIZE_F_EVENTS_TAC
   (parse_term(Printf.sprintf "\\(fp:int64) %s (pc:num). f_ev_w1u fp %s pc :(uarch_event)list"
      p.w3_ev p.w3_ev)) THEN
  META_EXISTS_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN SG_INPUT128_TAC `fp:int64` p.w3_in 8 THEN
  run 1 p.w3_plan THEN
  SG_LANES128_TAC p.w3_out THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[SG_ZX_WORD_64_8; SG_ZX_WORD_64_32; SG_ZX_WORD_32_8] THEN
  REPEAT CONJ_TAC THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[mld_polyw1_unpack_32] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REPEAT CONJ_TAC THEN APP_BLAST_TAC `b:num->byte` THEN NO_TAC) THEN
  TRY(CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_BLAST THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* ETA4V (65 only): the vectorized polyeta_unpack for eta = 4 (the path of   *)
(* the overlap test where input and output do not overlap), 8 iterations of  *)
(* 16 bytes to 32 coefficients: AND/USHR split the nibbles, TBL with four    *)
(* index vectors from the constants (through the page registers pg) spreads *)
(* the low nibbles to 32-bit lanes, UXTL the high ones, the lanes are        *)
(* subtracted from 4 and stored with ST2 (and some lanes first with 32-bit   *)
(* stores that the ST2 overwrite). Registers: xin = a, x8 = byte offset,    *)
(* x10 = r + 64 + 128 i, q16 = 0x0f in each byte, q17 = 4 in each lane.     *)
(* ------------------------------------------------------------------------- *)

let SG_ETA4V_STMT mc loop exit (xin,pg,qm,q4) cd (mods:string list) =
  let qmods,xmods = partition (fun r -> String.get r 0 = 'Q') mods in
  let pgs = String.concat " " (map (fun r ->
    Printf.sprintf "read %s s = word_add (word pc) (word 245760) /\\" r) pg) in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e r a (b:num->byte) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (a,128)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read %s s = a /\\ read X8 s = word 0 /\\
                  read X10 s = word_add r (word 64) /\\
                  read %s s = word 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f /\\
                  read %s s = word 0x00000004000000040000000400000004 /\\ %s
                  (!j. j < 128
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\
                  read X8 s = word 128 /\\
                  read X10 s = word_add r (word 1088) /\\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r (word(4 * i)))) s =
                           mld_polyeta_unpack_4 b i) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events r a pc /\\
                     memaccess_inbounds e2 [a,128; r,1024; word(pc + %d),64]
                                           [r,1024]))
             (MAYCHANGE [PC; %s] ,, MAYCHANGE [%s] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(r,1024)])"
   mc loop xin qm q4 pgs exit cd
   (String.concat "; " xmods) (String.concat "; " qmods));;

(*** The proof simulates the eight iterations as straight-line code, so    ***)
(*** that all addresses are r or a plus a numeral (the negative offsets of  ***)
(*** the 32-bit stores of an iteration from the pointer r + 64 + 128 i are  ***)
(*** not normalized otherwise).                                            ***)

let SG_ETA4V_LOOP mc exec loop exit cd regs (mods:string list) =
  let vecs = SG_IMAGE_VECS cd 4 in
  prove(SG_ETA4V_STMT mc loop exit regs cd mods,
  CONCRETIZE_F_EVENTS_TAC
   `\(r:int64) (a:int64) (pc:num). f_ev_e4 r a pc :(uarch_event)list` THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `r:int64`; `a:int64`;
                       `b:num->byte`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN SG_INPUT128_TAC `a:int64` 0 8 THEN SG_IMAGE_VECS_TAC vecs THEN
  MAP_EVERY (fun k -> ARM_STEPS_TAC exec [k] THEN ETA_NORM) (1--504) THEN
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read (memory :> bytes256 r) s = x`) (concl th) &&
       rand(rand(rand(rator(lhs(concl th))))) = `r:int64`
    then CONV_RULE(LAND_CONV(RATOR_CONV(RAND_CONV(RAND_CONV(RAND_CONV
           (REWR_CONV(WORD_RULE `r:int64 = word_add r (word 0)`))))))) th
    else th) THEN
  INLINE_ST2_LANES_TAC `r:int64` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[mld_polyeta_unpack_4] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REPEAT CONJ_TAC THEN APP_BLAST_TAC `b:num->byte` THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;


(* ------------------------------------------------------------------------- *)
(* ETA4C (65 only): the whole inlined polyeta_unpack (eta = 4) of the z loop *)
(* and the row loop, from the head of the loop to the join after the two    *)
(* paths of the overlap test (SI_ETA of inline_sign_eta.ml for eta = 2): the *)
(* input s_i at a + 128 i (a read from the frame slot ec_aslot, i in        *)
(* ec_ireg, 128 i in x12), the output at F + ec_roff (in ec_rreg). The code *)
(* tests whether the input and the output overlap (OV) and takes a scalar   *)
(* loop if they do; with val F + ec_roff + 1024 < 2^63 (the output does not *)
(* wrap) the nonoverlapping hypothesis refutes OV (SG_NOV_NOT_OV), so only  *)
(* the vector loop (SG_ETA4V_LOOP, ec_lv) is taken. (The scalar loop of the *)
(* z loop would need w14 = 4, which the code does not restore after the     *)
(* first iteration.) ec_pre / ec_post / ec_wr are the other facts and the   *)
(* frame regions written; the step numbers are those of the branch, of the  *)
(* ADRPs, of the shifted add (x8 = a + i << 7), and the steps before the    *)
(* calls of the two paths.                                                   *)
(* ------------------------------------------------------------------------- *)

type eta4c_inst =
  { ec_start : string; ec_stop : string; ec_ireg : string; ec_rreg : string;
    ec_roff : int; ec_aslot : int; ec_pre : string; ec_post : string;
    ec_wr : (int * int) list; ec_rd : (int * int) list; ec_mods : string list;
    ec_branch : int; ec_adrp : int list; ec_shl : int;
    ec_ns : int; ec_nv : int };;

let SG_ETA4C_OV roff =
  Printf.sprintf
   "val (word_add (a:int64) (word (128 * i))) < val (word_add (fp:int64) (word %d)) /\\
    val (word_add fp (word %d)) < val (word_add (word_add a (word (128 * i))) (word 128))"
   (roff + 1024) roff;;

let SG_ETA4C_TERM mc p =
  let regs = (p.ec_roff,1024) :: p.ec_wr in
  let rl = String.concat "; " (map (fun (oo,l) ->
             Printf.sprintf "(word_add fp (word %d),%d)" oo l) regs) in
  let ml = String.concat "; " (map (fun (oo,l) ->
             Printf.sprintf "word_add fp (word %d),%d" oo l) regs) in
  let mcs = String.concat "; " (map (fun (oo,l) ->
             Printf.sprintf "memory :> bytes(word_add fp (word %d),%d)" oo l) regs) in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e (fp:int64) (a:int64) i (b:num->byte) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        aligned 16 fp /\\ i < 8 /\\ val fp + %d < 2 EXP 63 /\\
        ALL (nonoverlapping (word_add a (word (128 * i)),128)) [%s] /\\
        ALL (nonoverlapping (word pc,libmldsa_size)) [%s]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read SP s = fp /\\
                  read %s s = word i /\\ read X12 s = word (128 * i) /\\
                  read %s s = word_add fp (word %d) /\\
                  read (memory :> bytes64 (word_add fp (word %d))) s = a /\\ %s
                  (!j. j < 128
                       ==> read(memory :> bytes8(word_add a (word(128 * i + j)))) s =
                           b j) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\ %s
                  (!j. j < 256
                       ==> read(memory :> bytes32(word_add fp (word(%d + 4 * j)))) s =
                           mld_polyeta_unpack_4 b j) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events fp a i pc /\\
                     memaccess_inbounds e2
                      [word_add a (word (128 * i)),128; word_add fp (word %d),8;%s
                       word (pc + mldsa65_pk_from_sk_consts),64; %s]
                      [%s]))
             (MAYCHANGE [PC; %s] ,,
              MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q17] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [%s])"
   (p.ec_roff + 1024) rl rl mc p.ec_start p.ec_ireg p.ec_rreg p.ec_roff p.ec_aslot p.ec_pre
   p.ec_stop p.ec_post p.ec_roff p.ec_aslot
   (String.concat "" (map (fun (oo,l) ->
      Printf.sprintf " word_add fp (word %d),%d;" oo l) p.ec_rd)) ml ml
   (String.concat "; " p.ec_mods) mcs);;

(*** One event function for the whole region: with APPEND of two, as in  ***)
(*** SI_ETA, FULL_UNIFY_F_EVENTS_TAC fails ("Not a var"), since the region ***)
(*** ends with the call of the loop                                       ***)

let SG_ETA4C_TEMPLATE =
  `\(fp:int64) (a:int64) (i:num) (pc:num). f_ev_eta fp a i pc :(uarch_event)list`;;

(*** The overlap test of the code cannot hold for regions that do not     ***)
(*** overlap when the second one does not wrap                            ***)

let SG_NOV_NOT_OV = prove
 (`!(a:int64) (r:int64) m n.
     val r + n < 2 EXP 63 /\ m <= 2 EXP 62 /\ 0 < m /\ 0 < n /\
     nonoverlapping_modulo (2 EXP 64) (val a,m) (val r,n)
     ==> ~(val a < val r + n /\ val r < val(word_add a (word m)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nonoverlapping_modulo] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `a:int64` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_64] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `val(word_add (a:int64) (word m)) = val a + m` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    SUBGOAL_THEN `m MOD 2 EXP 64 = m` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `m <= 2 EXP 62` THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MOD_LT THEN
    MAP_EVERY UNDISCH_TAC [`val (a:int64) < val (r:int64) + n`; `val (r:int64) + n < 2 EXP 63`;
                           `m <= 2 EXP 62`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `val (a:int64) <= val (r:int64)` THENL
   [MAP_EVERY EXISTS_TAC [`val (r:int64) - val (a:int64)`; `0`];
    MAP_EVERY EXISTS_TAC [`0`; `val (a:int64) - val (r:int64)`]] THEN
  REPEAT CONJ_TAC THEN TRY(ASM_ARITH_TAC THEN NO_TAC) THEN
  MATCH_MP_TAC(MESON[CONG_REFL] `x:num = y ==> (x == y) (mod n)`) THEN
  ASM_ARITH_TAC);;

let SG_ETA4C_SHL = prove
 (`!(a:int64) i. i < 8 ==> word_add a (word_shl (word i) 7) = word_add a (word (128 * i))`,
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SHL; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC MOD_DOWN_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let SG_ETA4C_PROVE mc p lv =
  let ex = INLINE_LOOP_EXEC p.ec_start p.ec_stop in
  let ov = parse_term(SG_ETA4C_OV p.ec_roff) in
  let rt = parse_term(Printf.sprintf "word_add fp (word %d):int64" p.ec_roff) in
  let rtv = parse_term(Printf.sprintf "word_add fp (word %d):int64" p.ec_roff) in
  let allowed = [`fp:int64`; `a:int64`; `i:num`; `pc:num`] in
  let call name ilist n = FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
                            ex name ilist allowed n in
  let ap = `word_add (a:int64) (word (128 * i))` in
  let bnd = parse_term(Printf.sprintf "val (fp:int64) + %d < 2 EXP 63" (p.ec_roff + 1024)) in
  prove(SG_ETA4C_TERM mc p,
  ASSUME_CALLEE_SAFETY_TAILED_TAC lv "H_V" THEN
  CONCRETIZE_F_EVENTS_TAC SG_ETA4C_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `fp:int64`; `a:int64`; `i:num`;
                       `b:num->byte`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; fst ex] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  SUBGOAL_THEN
   `!j. j < 128 ==> read (memory :> bytes8 (word_add (word_add a (word (128 * i))) (word j))) s0 =
                    (b:num->byte) j` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[WORD_RULE `word_add (word_add (a:int64) (word (128 * i))) (word j) =
                           word_add a (word (128 * i + j))`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC ex [k] THEN
    (if k = p.ec_shl then
       RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [`a:int64`;`i:num`] SG_ETA4C_SHL)
                                      (ASSUME `i < 8`)])
     else if mem k p.ec_adrp then MLKEM_NATIVE_ADRP_TAC else ALL_TAC))
   (1--p.ec_branch) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SI_ETA_CF]) THEN
  SUBGOAL_THEN (mk_neg ov) ASSUME_TAC THENL
   [MP_TAC(SPECL [ap; rt; `128`; `1024`] SG_NOV_NOT_OV) THEN
    SUBGOAL_THEN (parse_term(Printf.sprintf
      "val (word_add fp (word %d):int64) = val (fp:int64) + %d /\\
       val (word_add fp (word %d):int64) = val (fp:int64) + %d"
      p.ec_roff p.ec_roff (p.ec_roff + 1024) (p.ec_roff + 1024)))
     (fun th -> REWRITE_TAC[th] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[th; ADD_ASSOC]) THEN ASSUME_TAC th) THENL
     [CONJ_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN
      UNDISCH_TAC bnd THEN ARITH_TAC;
      ALL_TAC] THEN
    (*** the nonoverlapping fact has 2 EXP 64 unreduced: no NUM_REDUCE_CONV ***)
    (*** on the whole goal before the antecedent is proved                  ***)
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      TRY(CONV_TAC NUM_REDUCE_CONV THEN NO_TAC) THEN
      UNDISCH_TAC bnd THEN ARITH_TAC;
      REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                          REWRITE_TAC[th] THEN ASSUME_TAC th) THEN
  ARM_STEPS_TAC ex ((p.ec_branch + 1)--(p.ec_branch + p.ec_nv)) THEN
  call "H_V" [rtv; ap; `b:num->byte`; `pc:num`] (p.ec_branch + p.ec_nv + 1) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* ZPACK19: polyz_pack for gamma1 = 2^19, the vector loop of pack_sig_z (8   *)
(* iterations of 32 coefficients to 80 bytes: LD2, subtraction from 2^19,   *)
(* shifts, XTN/UZP1, TBL with index vectors from the constants of the image *)
(* through page registers, BSL, and STR/STP of the 80 bytes). The loop is    *)
(* simulated as straight-line code (zp_steps steps in all), so that all      *)
(* addresses are numeral offsets. z is at F + zp_in (fp = SP), the output at *)
(* op + zp_out; the code reads the pointer of z from zp_inreg and the output *)
(* base from zp_opreg with the offset in zp_offreg (zp_out at the head).    *)
(* ------------------------------------------------------------------------- *)

type zpack_inst =
  { zp_start : string; zp_stop : string; zp_steps : int; zp_in : int;
    zp_out : int; zp_inreg : string; zp_opreg : string; zp_offreg : string;
    zp_pages : string list; zp_cd : int; zp_ncd : int; zp_q : string;
    zp_post : string; zp_mods : string list };;

let SG_ZPACK19_TERM mc p =
  let qmods,xmods = partition (fun r -> String.get r 0 = 'Q') p.zp_mods in
  let pgs = String.concat " " (map (fun r ->
    Printf.sprintf "read %s s = word_add (word pc) (word 245760) /\\" r) p.zp_pages) in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e (fp:int64) (op:int64) (z:num->int32) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        ALL (nonoverlapping (word_add op (word %d),640))
            [(word pc,libmldsa_size); (word_add fp (word %d),1024)]
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %s) /\\
                  read %s s = word_add fp (word %d) /\\ read %s s = op /\\
                  read %s s = word %d /\\
                  read %s s = word 0x00080000000800000008000000080000 /\\ %s
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add fp (word(%d + 4 * i)))) s =
                           z i) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %s) /\\ read %s s = op /\\ %s
                  (!j. j < 640
                       ==> read(memory :> bytes8(word_add op (word(%d + j)))) s =
                           mld_polyz_pack_19 z j) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events fp op pc /\\
                     memaccess_inbounds e2
                      [word_add fp (word %d),1024; word_add op (word %d),640;
                       word (pc + %d),%d]
                      [word_add op (word %d),640]))
             (MAYCHANGE [PC; %s] ,, MAYCHANGE [%s] ,, MAYCHANGE SOME_FLAGS ,,
              MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(word_add op (word %d),640)])"
   p.zp_out p.zp_in mc p.zp_start p.zp_inreg p.zp_in p.zp_opreg p.zp_offreg p.zp_out
   p.zp_q pgs p.zp_in p.zp_stop p.zp_opreg p.zp_post p.zp_out p.zp_in p.zp_out
   p.zp_cd (16 * p.zp_ncd) p.zp_out
   (String.concat "; " xmods) (String.concat "; " qmods) p.zp_out);;

(*** Byte j of the output from the 128-bit store that holds it (a store    ***)
(*** fact at op + k with k <= zp_out + j < k + 16)                         ***)

let SG_ZPACK_BYTE_TAC out stores j =
  let nrm a = try rhs(concl(NORMALIZE_RELATIVE_ADDRESS_CONV a)) with Failure _ -> a in
  let off th = let a = nrm(rand(rand(rand(rator(lhs(concl th)))))) in
    try dest_small_numeral(rand(rand a)) with Failure _ -> 0 in
  let b = out + j in
  let sth = find (fun th -> let k = off th in k <= b && b < k + 16) stores in
  let k = off sth in
  let faddr = rand(rand(rand(rator(lhs(concl sth))))) in
  let bth = MP (SPECL [faddr; rhs(concl sth); rand(lhs(concl sth));
                       mk_small_numeral (b - k)] INLINE_BYTES8_OF_BYTES128)
               (CONJ sth (EQT_ELIM(NUM_REDUCE_CONV
                  (mk_binop `(<):num->num->bool` (mk_small_numeral (b - k)) `16`)))) in
  let bth = CONV_RULE(RAND_CONV(RAND_CONV(LAND_CONV NUM_MULT_CONV) THENC
                                W1P_EXTRACT_CONV)) bth in
  let baddr = rand(rand(rand(rator(lhs(concl bth))))) in
  W(fun (asl,w) ->
    let gaddr = rand(rand(rand(rator(lhs w)))) in
    let eq = prove(mk_eq(gaddr,baddr),
                   REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
                   AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC) in
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [eq] THEN
    GEN_REWRITE_TAC LAND_CONV [bth] THEN
    REWRITE_TAC[mld_polyz_pack_19] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV THENC DEPTH_CONV NUM_RED_CONV) THEN
    REWRITE_TAC[] THEN APP_BLAST_TAC `z:num->int32`);;

let SG_ZPACK19_PROVE mc p =
  let ex = INLINE_LOOP_EXEC p.zp_start p.zp_stop in
  let vecs = SG_IMAGE_VECS p.zp_cd p.zp_ncd in
  prove(SG_ZPACK19_TERM mc p,
  CONCRETIZE_F_EVENTS_TAC
   `\(fp:int64) (op:int64) (pc:num). f_ev_zp fp op pc :(uarch_event)list` THEN
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `fp:int64`; `op:int64`;
                       `z:num->int32`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst ex] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN INLINE_MAP_INPUT_TAC p.zp_in `z:num->int32` THEN
  INLINE_MAP_INPUT256_TAC p.zp_in THEN SG_IMAGE_VECS_TAC vecs THEN
  MAP_EVERY (fun n -> ARM_STEPS_TAC ex [n] THEN INLINE_W1P2_FIX_TAC THEN ETA_NORM)
    (1--p.zp_steps) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CONV_TAC EXPAND_CASES_CONV THEN
      W(fun (asl,w) ->
        let stores = mapfilter (fun (_,th) ->
          let c = concl th in
          if is_eq c && free_in `op:int64` (lhs c) &&
             (try fst(dest_const(rator(rand(rand(rator(lhs c)))))) = "bytes128"
              with Failure _ -> false)
          then th else fail()) asl in
        REPEAT CONJ_TAC THENL (map (SG_ZPACK_BYTE_TAC p.zp_out stores) (0--639))) THEN
      NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* INLINE_MAPP_PROVE of inline_sign_sig.ml (map code on the polynomial at a  *)
(* pointer w) for a loop bound jk other than 4 (the test of the counter of   *)
(* the row loop, (ZF <=> j + 1 = jk), is decided for each j < jk).           *)
(* ------------------------------------------------------------------------- *)

let SG_MAPP_PROVE jk tm exec yoff n k fix (defs:thm list) (lanes:thm list) =
  let jlt = parse_term(Printf.sprintf "j < %d" jk) in
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
                          exists (fun (_,th) -> concl th = jlt) asl
       then UNDISCH_TAC jlt THEN SPEC_TAC(`j:num`,`j:num`) THEN
            CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
            CONV_TAC NUM_REDUCE_CONV THEN NO_TAC
       else NO_TAC)) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
