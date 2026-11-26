(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The unpacking of polynomials with 4 bits per coefficient (eta = 4) that   *)
(* clang 23 -O3 has inlined into mldsa65_pk_from_sk (and keypair_internal):  *)
(* straight-line vector code, which loads 128 bytes of the secret key with   *)
(* LDP and LDR of Q registers, splits each byte into its two nibbles (AND    *)
(* with 0x0f, USHR #4), widens them (UXTL, UXTL2) to 32 bits, subtracts them *)
(* from 4 (USUBW, USUBW2) and stores the lanes interleaved (ST2 of two       *)
(* vectors of four 32-bit lanes) as the 256 words of mld_polyeta_unpack_4.   *)
(*                                                                           *)
(* A region of such code is simulated step by step, normalizing the vector   *)
(* registers after each step (E4_NORM): without it the 256-bit stored values *)
(* grow to a megabyte each. The loads of the secret key are given as facts   *)
(* about 16 and 32 bytes made of the individual bytes skb j (E4_LD_TAC,      *)
(* E4_256_TAC), so that each stored lane is a small term of those bytes, and *)
(* each lane is proved equal to the specification by a bit-blast             *)
(* (E4_LANES_TAC, E4_LANE_TAC).                                              *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_polyeta.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign.ml";;
needs "arm/proofs/utils/mldsa_native_top.ml";;

(*** The 16 bytes of the secret key (4032 bytes skb) at sk + ofs as a 128-bit ***)
(*** load, made of the bytes                                                  ***)

let E4_LD_FACT ofs =
  let hth = ASSUME `!j. j < 4032 ==> read (memory :> bytes8 (word_add sk (word j))) s0 = (skb:num->byte) j` in
  let insts = map (fun i ->
    let j = ofs + i in
    let th = MP (SPEC (mk_small_numeral j) hth)
                (EQT_ELIM(NUM_REDUCE_CONV(mk_binary "<" (mk_small_numeral j,`4032`)))) in
    REWRITE_RULE[WORD_ADD_0] th) (0--15) in
  let lhs = parse_term(Printf.sprintf "read (memory :> bytes128 (word_add (sk:int64) (word %d))) s0" ofs) in
  let conv = REWRITE_CONV[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
                          el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
                          el 3 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
                          el 4 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT);
                          PTR_ADD_G; GSYM ADD_ASSOC] THENC
             DEPTH_CONV NUM_ADD_CONV in
  let th = conv lhs in
  REWRITE_RULE (WORD_ADD_0 :: insts) th;;

let E4_LD_TAC ofss =
  W(fun (asl,w) ->
    let skf = find (fun th -> can (term_match [] `!j. j < 4032 ==> read (memory :> bytes8 (word_add sk (word j))) s0 = (skb:num->byte) j`) (concl th)) (map snd asl) in
    MAP_EVERY (fun ofs -> ASSUME_TAC (PROVE_HYP skf (E4_LD_FACT ofs))) ofss);;

(*** The 16-byte chunks lo, ..., hi of the secret key as loaded (mld_chunk128), ***)
(*** for the bytes that the code copies unchanged                              ***)

let E4_CHUNK_TAC lo hi =
  W(fun (asl,w) ->
    let skf = find (fun th -> can (term_match []
       `!j. j < 4032 ==> read(memory :> bytes8(word_add sk (word j))) s0 = skb j`) (concl th)) (map snd asl) in
    MAP_EVERY (fun m ->
      let th = MP (SPECL [`sk:int64`; `4032`; `skb:num->byte`; `s0:armstate`;
                          mk_small_numeral m] BYTES128_OF_BYTES8)
                  (CONJ skf (EQT_ELIM(NUM_REDUCE_CONV
                     (subst [mk_small_numeral m,`m:num`] `16 * m + 16 <= 4032`)))) in
      ASSUME_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV THENC
                           REWRITE_CONV[WORD_ADD_0]) th)) (lo--hi));;

(*** The 32 bytes at sk + ofs (LDP of two Q registers) from the two 128-bit ***)
(*** facts                                                                   ***)

let E4_256_TAC offs =
  W(fun (asl,_) ->
    let f128 = mapfilter (fun (_,th) ->
      let c = concl th in
      if is_eq c && can (term_match [] `read (memory :> bytes128 a) (s0:armstate)`) (lhs c)
      then th else fail()) asl in
    MAP_EVERY (fun ofs ->
      let base = mk_comb(`word_add (sk:int64)`, mk_comb(`word:num->int64`, mk_small_numeral ofs)) in
      let tm = subst [base,`A:int64`] `read (memory :> bytes256 A) (s0:armstate)` in
      let eth = GEN_REWRITE_CONV I [el 0 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] tm in
      let eth = CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) eth in
      ASSUME_TAC(REWRITE_RULE f128 eth)) offs);;

(*** The normalization of the vector registers after each step ***)

let E4_NORM = RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV));;

(*** The 256-bit stores at sp + n of the state sname as facts about their ***)
(*** 32-bit lanes                                                         ***)

let E4_UNSPLIT =
  [el 0 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT);
   el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT);
   el 2 (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT);
   PTR_ADD_G; GSYM ADD_ASSOC; WORD_ADD_0];;

let E4_LANES_TAC sname =
  let is_store t =
    try let l,_ = dest_eq t in
        (match l with
           Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),_),Comb(Const(bn,_),addr))),_)
             when bn = "bytes256" ->
             (match addr with
                Comb(Comb(Const("word_add",_),r0),_) -> r0 = `sp:int64`
              | _ -> false)
         | _ -> false)
    with _ -> false in
  W(fun (asl,w) ->
    let sts = filter (fun (_,th) -> is_store(concl th) &&
                      free_in (mk_var(sname,`:armstate`)) (concl th)) asl in
    MAP_EVERY (fun (_,th) ->
      let th1 = REWRITE_RULE E4_UNSPLIT th in
      let th2 = CONV_RULE(DEPTH_CONV NUM_ADD_CONV) th1 in
      let th3 = map (CONV_RULE(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) (CONJUNCTS th2) in
      MAP_EVERY ASSUME_TAC th3) sts);;

(*** One lane against the specification (the polyvec form covers both the ***)
(*** single polynomial, with the vector of one polynomial, and the vectors) ***)

let E4_LANE_TAC =
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  W(fun (asl,w) ->
    let l = lhand w in
    FIRST_ASSUM(fun th -> if lhand(concl th) = l then REWRITE_TAC[th] else NO_TAC)) THEN
  REWRITE_TAC[mld_polyvec_unpack; mld_polyvec; mld_polyeta_unpack_4] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  APP_BLAST_TAC `skb:num->byte`;;

(* ------------------------------------------------------------------------- *)
(* The statement for a region [st, en) of the image that unpacks np          *)
(* polynomials from the 128 * np bytes at inofs of the secret key (4032      *)
(* bytes skb, at the pointer in the register inreg) to the 1024 * np bytes   *)
(* at sp + outofs, as the first np polynomials of the vector of unpacked     *)
(* polynomials of the bytes of the key from inofs on.                        *)
(*   vars    extra variables of the statement (for the value of a register)  *)
(*   pre     extra facts about the state before, each followed by a /\       *)
(*   post    registers and facts about the state after, each followed by /\ *)
(*   mayregs the registers that change (PC and X registers)                  *)
(*   stores  the other ranges (offset, size) from sp that the region writes  *)
(* ------------------------------------------------------------------------- *)

let INLINE_ETA4_TERM st en inreg inofs outofs np (poly:bool)
                     (vars:string) (pre:string) (post:string) (mayregs:string)
                     (stores:(int*int) list) (xloads:(int*int) list) =
  let ss = Printf.sprintf in
  let lacc = String.concat "" (map (fun (off,sz) -> ss "; word_add sk (word %d),%d" off sz) xloads) in
  let nov = String.concat "" (map (fun (off,sz) ->
      ss "      nonoverlapping (word_add sp (word %d),%d) (sk,4032) /\\\n      nonoverlapping (word_add sp (word %d),%d) (word pc,libmldsa_size) /\\\n      nonoverlapping (word_add sp (word %d),%d) (word_add sp (word %d),%d) /\\\n"
        off sz off sz off sz outofs (1024 * np)) stores) in
  let nov2 = String.concat "" (map (fun ((o1,n1),(o2,n2)) ->
      ss "      nonoverlapping (word_add sp (word %d),%d) (word_add sp (word %d),%d) /\\\n" o1 n1 o2 n2)
      (let rec pairs l = match l with [] -> [] | h::t -> map (fun x -> (h,x)) t @ pairs t in pairs stores)) in
  let sacc = String.concat "" (map (fun (off,sz) -> ss "; word_add sp (word %d),%d" off sz) stores) in
  let smem = String.concat "" (map (fun (off,sz) -> ss ";\n                       memory :> bytes(word_add sp (word %d),%d)" off sz) stores) in
  let specj = if poly then ss "mld_polyeta_unpack_4 (\\t. skb (%d + t)) j" inofs
              else ss "mld_polyvec_unpack 128 mld_polyeta_unpack_4 (\\t. skb (%d + t)) j" inofs in
  parse_term(ss
 "exists f_events.
    forall e (sk:int64) (sp:int64) (skb:num->byte)%s pc.
      aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
      aligned 16 sp /\\
      nonoverlapping (word_add sp (word %d),%d) (sk,4032) /\\
      nonoverlapping (word_add sp (word %d),%d) (word pc,libmldsa_size) /\\
%s%s      T
      ==> ensures arm
           (\\s. aligned_bytes_loaded s (word pc)
                  mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
                read PC s = word (pc + %d) /\\
                read SP s = sp /\\ read %s s = sk /\\ %s
                (!j. j < 4032
                     ==> read (memory :> bytes8 (word_add sk (word j))) s = skb j) /\\
                read events s = e)
           (\\s. read PC s = word (pc + %d) /\\ %s
                (!j. j < %d
                     ==> read (memory :> bytes32 (word_add sp (word (%d + 4 * j)))) s =
                         %s) /\\
                (exists e2.
                   read events s = APPEND e2 e /\\
                   e2 = f_events sk sp pc /\\
                   memaccess_inbounds e2 [word_add sk (word %d),%d%s]
                    [word_add sp (word %d),%d%s]))
           (MAYCHANGE [%s] ,,
            MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q17; Q18; Q19] ,,
            MAYCHANGE [events] ,,
            MAYCHANGE [memory :> bytes(word_add sp (word %d),%d)%s])"
  vars outofs (1024 * np) outofs (1024 * np) nov nov2
  st inreg pre
  en post (256 * np) outofs specj inofs (128 * np) lacc outofs (1024 * np) sacc
  mayregs outofs (1024 * np) smem);;

(*** The proof: simulate the nsteps steps of the region (the loads of the  ***)
(*** key at the offsets ldofs of 16 bytes and ldpofs of 32 bytes), then    ***)
(*** the lanes of the stores to the specification                          ***)

let INLINE_ETA4_PROVE exec tm vars chunks ldofs ldpofs nsteps =
  let sname = "s" ^ string_of_int nsteps in
  let lam = `\(sk:int64) (sp:int64) (pc:num). f_ev_e4 sk sp pc :(uarch_event)list` in
  prove(tm,
   CONCRETIZE_F_EVENTS_TAC lam THEN
   META_EXISTS_TAC THEN
   REWRITE_TAC[NONOVERLAPPING_CLAUSES; fst exec] THEN
   REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
   FULL_INIT_TAC THEN
   (match chunks with [lo;hi] -> E4_CHUNK_TAC lo hi | _ -> ALL_TAC) THEN
   E4_LD_TAC ldofs THEN E4_256_TAC ldpofs THEN
   MAP_EVERY (fun n -> ARM_STEPS_TAC exec [n] THEN E4_NORM) (1--nsteps) THEN
   E4_LANES_TAC sname THEN
   ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
   REPEAT CONJ_TAC THEN
   TRY(CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THEN E4_LANE_TAC THEN NO_TAC) THEN
   TRY(DISCHARGE_SAFETY_PROPERTY_TAC THEN NO_TAC));;

(* ------------------------------------------------------------------------- *)
(* mldsa65_pk_from_sk: the unpacking of the six polynomials of s2 (the       *)
(* secret key at offset 768 + 128 k), one per region from the end of the     *)
(* previous norm check loop (the return from the call of polyvecl_chknorm    *)
(* for the first) to the head of its own: the buffer at sp + 2528 is used    *)
(* for all of them, and the norm check accumulator is cleared in the region  *)
(* (X26, X28, X22, X21, X27, X23). The first region also stores the result   *)
(* of the call (w0) at sp + 20.                                              *)
(* ------------------------------------------------------------------------- *)

let ETA4_65_STARTS = [0x20f34; 0x21258; 0x21574; 0x218a0; 0x21bcc; 0x21ef8];;
let ETA4_65_ENDS   = [0x21220; 0x2153c; 0x21868; 0x21b94; 0x21ec0; 0x221ec];;
let ETA4_65_ACCS   = ["X26"; "X28"; "X22"; "X21"; "X27"; "X23"];;

let ETA4_65_VARS k = if k = 0 then " (x0:int64)" else "";;

let INLINE_ETA4_65_TERM k =
  let st = el k ETA4_65_STARTS and en = el k ETA4_65_ENDS and acc = el k ETA4_65_ACCS in
  INLINE_ETA4_TERM st en "X20" (768 + 128 * k) 2528 1 true (ETA4_65_VARS k)
   (if k = 0 then "read X0 s = x0 /\\" else "")
   (Printf.sprintf "read X8 s = word 0 /\\ read X9 s = word_add sp (word 2528) /\\ read X10 s = word 4 /\\ read %s s = word 0 /\\ %s" acc
      (if k = 0 then "read (memory :> bytes32 (word_add sp (word 20))) s = word_zx x0 /\\" else ""))
   (Printf.sprintf "PC; X8; X9; X10; %s" acc)
   (if k = 0 then [(20,4)] else []) [];;

let INLINE_ETA4_65 k =
  let st = el k ETA4_65_STARTS and en = el k ETA4_65_ENDS in
  let exec = INLINE_LOOP_EXEC (string_of_int st) (string_of_int en) in
  let io = 768 + 128 * k in
  INLINE_ETA4_PROVE exec (INLINE_ETA4_65_TERM k) (ETA4_65_VARS k) []
   (map (fun m -> io + 16 * m) (0--7)) (map (fun m -> io + 32 * m) (0--3))
   ((en - st) / 4);;

(* ------------------------------------------------------------------------- *)
(* The five polynomials of s1 (the secret key at offset 128 to 767), in one  *)
(* block of 948 instructions from the add of the buffer address to the bl of *)
(* polyvecl_chknorm: the constants of the vector code are in Q18 and Q19,    *)
(* the polynomials at sp + 3552 + 1024 k, and the code copies in between     *)
(* rho (at sp + 8832), the key (sp + 8672) and tr (sp + 8768) from the       *)
(* secret key to the stack (as the chunks of 16 bytes of the key), puts the  *)
(* bound 5 in X1, and keeps the addresses of polynomials 1 to 4 in           *)
(* registers and in the stack (sp + 24 and sp + 8), for the calls of         *)
(* poly_ntt that follow.                                                     *)
(* ------------------------------------------------------------------------- *)

let INLINE_ETA4_65_S1_TERM =
  INLINE_ETA4_TERM 0x20060 0x20f30 "X1" 128 3552 5 false ""
   "read Q19 s = word 20016609818878733144904388672456953615 /\\
    read Q18 s = word 316912650130844326686193876996 /\\"
   "read X1 s = word 5 /\\
    read X8 s = word_add sp (word 8640) /\\ read X9 s = word 5088 /\\
    read X10 s = word_add sp (word 5600) /\\ read X24 s = word_add sp (word 6624) /\\
    read X25 s = word_add sp (word 7648) /\\
    read (memory :> bytes64 (word_add sp (word 24))) s = word_add sp (word 4576) /\\
    read (memory :> bytes64 (word_add sp (word 8))) s = word_add sp (word 5600) /\\
    read (memory :> bytes128 (word_add sp (word 8832))) s = mld_chunk128 skb 0 /\\
    read (memory :> bytes128 (word_add sp (word 8848))) s = mld_chunk128 skb 1 /\\
    read (memory :> bytes128 (word_add sp (word 8672))) s = mld_chunk128 skb 2 /\\
    read (memory :> bytes128 (word_add sp (word 8688))) s = mld_chunk128 skb 3 /\\
    read (memory :> bytes128 (word_add sp (word 8768))) s = mld_chunk128 skb 4 /\\
    read (memory :> bytes128 (word_add sp (word 8784))) s = mld_chunk128 skb 5 /\\
    read (memory :> bytes128 (word_add sp (word 8800))) s = mld_chunk128 skb 6 /\\
    read (memory :> bytes128 (word_add sp (word 8816))) s = mld_chunk128 skb 7 /\\"
   "PC; X1; X8; X9; X10; X24; X25"
   [(8,8); (24,8); (8672,32); (8768,96)] [(0,128)];;

let INLINE_ETA4_65_S1 () =
  let st = 0x20060 and en = 0x20f30 in
  INLINE_ETA4_PROVE (INLINE_LOOP_EXEC (string_of_int st) (string_of_int en))
   INLINE_ETA4_65_S1_TERM "" [0;7]
   (map (fun m -> 128 + 16 * m) (0--39))
   ((map (fun m -> 32 * m) (0--3)) @ (map (fun m -> 128 + 32 * m) (0--19)))
   ((en - st) / 4);;
