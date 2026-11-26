(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Region lemmas for mldsa{44,65,87}_poly_uniform_eta_4x of the clang 23 -O3 *)
(* build, where clang inlined the fourfold SHAKE256 and the rejection        *)
(* sampling mld_rej_eta_c. The code samples each polynomial in a loop over   *)
(* the bytes of a buffer on the stack, from a count c < 256 of coefficients  *)
(* so far: it reads byte i, stores the value of each acceptable nibble at    *)
(* the count (the second one only if the count is below 256), and stops     *)
(* when the count reaches 256 or the buffer is used up. There are eight such *)
(* loops in each function, of three shapes (the pointer to the polynomial    *)
(* reloaded from the stack in each iteration or kept in a register, a CSET   *)
(* of the flag count < 256 or not, other registers); ESCAN_PROVE proves the  *)
(* lemma for one of them, from its head to its exit, from a description of  *)
(* the registers. The result is that of the gcc proof of mld_rej_eta_c       *)
(* (gcc12_O2_reduced_ram/rej_eta_*_proof.ml): the count mld_rej_eta_ctr and  *)
(* the coefficients of mld_rej_eta_list, with the events a function of the   *)
(* values that mld_rej_eta_c declassifies (mld_rej_eta_declass), by the      *)
(* paths of an iteration: which nibbles are accepted, whether the second one *)
(* fits, and whether the count is full after it.                             *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_challenge.ml";;

let ETA_MC = "mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc";;

(* ------------------------------------------------------------------------- *)
(* A scan loop: absolute offsets of its head and exit from pc, the offset of *)
(* the buffer from sp and its length, eta, the counter and flag registers,  *)
(* the pointer to the polynomial (a register, or None for the stack slot at *)
(* sp + 88 that the loop reloads), the facts about the registers that the   *)
(* loop reads and keeps, and the registers that it changes besides PC, the  *)
(* counter, the flag and X8 (the byte index).                                *)
(* ------------------------------------------------------------------------- *)

type escan =
  { eh : int; ex : int; eb : int; el : int; eeta : int;
    ectr : string; eflag : string option; eptr : string option;
    eregs : string; ech : string list; esplit : bool; edisp : int;
    ekeep : string };;

(*** ekeep: facts about registers that the loop leaves alone and that the  ***)
(*** caller needs afterwards (in terms of the variable x1); the region     ***)
(*** lemma restates them, with eregs and the pointer, in its post          ***)

let ESCAN_KEEP p = if p.ekeep = "" then "T" else p.ekeep;;

let ESCAN_PTR p = match p.eptr with
    Some r -> Printf.sprintf "read %s s = a" r
  | None -> "read (memory :> bytes64 (word_add sp (word 88))) s = a";;

let ESCAN_TM p =
  let ctr = Printf.sprintf "mld_rej_eta_ctr %d 256 c b %d" p.eeta p.el in
  let flagpost = match p.eflag with
      None -> ""
    | Some r -> Printf.sprintf "read %s s = (if %s < 256 then word 1 else word 0) /\\ " r ctr in
  let slotnov, slotacc = match p.eptr with
      Some _ -> "", ""
    | None -> " /\\ nonoverlapping (a,1024) (word_add sp (word 88),8)", "; word_add sp (word 88),8" in
  let ch = ["PC"; "X8"; p.ectr] @ (match p.eflag with Some r -> [r] | None -> []) @ p.ech in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e (a:int64) (sp:int64) (c:num) (f:num->int32) (b:num->byte) %s pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        c < 256 /\\ aligned 16 sp /\\
        nonoverlapping (a,1024) (word pc,libmldsa_size) /\\
        nonoverlapping (a,1024) (word_add sp (word %d),%d)%s
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %d) /\\
                  read X8 s = word 0 /\\ read %s s = word c /\\ %s /\\ %s /\\ %s /\\
                  (!j. j < %d
                       ==> read (memory :> bytes8 (word_add sp (word (%d + j)))) s = b j) /\\
                  (!k. k < c
                       ==> read (memory :> bytes32 (word_add a (word (4 * k)))) s = f k) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %d) /\\ %s /\\ %s /\\ %s /\\
                  read %s s = word (%s) /\\ %s %s <= 256 /\\
                  (!k. k < %s
                       ==> read (memory :> bytes32 (word_add a (word (4 * k)))) s =
                           (if k < c then f k
                            else EL (k - c) (mld_rej_eta_list %d b (2 * %d)))) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a sp c (mld_rej_eta_declass %d 256 c b %d) pc /\\
                     memaccess_inbounds e2
                      [a,1024; word_add sp (word %d),%d%s] [a,1024]))
             (MAYCHANGE [%s] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a,1024)])"
   (if p.ekeep = "" then "" else "(x1:int64)")
   p.eb p.el slotnov ETA_MC p.eh p.ectr p.eregs (ESCAN_PTR p) (ESCAN_KEEP p) p.el p.eb
   p.ex p.eregs (ESCAN_PTR p) (ESCAN_KEEP p) p.ectr ctr flagpost ctr ctr p.eeta p.el p.eeta p.el p.eb p.el slotacc
   (String.concat "; " ch));;

(*** The events: the paths of iteration i by the two nibbles of byte i, ***)
(*** whether the second fits and whether the count is full after it     ***)

let ESCAN_TEMPLATE_F split =
  let cont n =
    if split then Printf.sprintf
      "(if i + 1 < LENGTH D DIV 2 then %s a sp c D pc i else %sl a sp c D pc i)" n n
    else Printf.sprintf "%s a sp c D pc i" n in
  let l = "LENGTH(FILTER (\\x. x) (SUB_LIST(0,2 * i) D))" in
  parse_term(Printf.sprintf
   "\\(a:int64) (sp:int64) (c:num) (D:bool list) (pc:num).
     APPEND (f_ev_epil a sp c D pc)
      (APPEND
        (ENUMERATEL (LENGTH D DIV 2)
          (\\i. if EL (2 * i) D
               then if EL (2 * i + 1) D
                    then if c + %s + 1 < 256
                         then if c + %s + 2 < 256
                              then %s
                              else f_ev_vvf a sp c D pc i
                         else f_ev_vs a sp c D pc i
                    else if c + %s + 1 < 256
                         then %s
                         else f_ev_vxf a sp c D pc i
               else if EL (2 * i + 1) D
                    then if c + %s + 1 < 256
                         then %s
                         else f_ev_xvf a sp c D pc i
                    else %s))
        (f_ev_prol a sp c D pc)):(uarch_event)list"
   l l (cont "f_ev_vvc") l (cont "f_ev_vxc") l (cont "f_ev_xvc") (cont "f_ev_xx"));;

let ESCAN_TEMPLATE = ESCAN_TEMPLATE_F false;;

let ESCAN_INV p =
  let flag = match p.eflag with
      None -> ""
    | Some r -> Printf.sprintf
        "(0 < i ==> read %s s = (if c + MIN (256 - c) (LENGTH(FILTER (\\x. x) (SUB_LIST(0,2 * i) D))) < 256 then word 1 else word 0)) /\\ " r in
  parse_term(Printf.sprintf
   "\\i s. (i < M ==> read X8 s = word i) /\\ %s /\\ %s /\\ %s /\\
          read %s s = word (c + MIN (256 - c) (LENGTH(FILTER (\\x. x) (SUB_LIST(0,2 * i) D)))) /\\ %s
          (!j. j < %d
               ==> read (memory :> bytes8 (word_add sp (word (%d + j)))) s = b j) /\\
          (!k. k < c + MIN (256 - c) (LENGTH(FILTER (\\x. x) (SUB_LIST(0,2 * i) D)))
               ==> read (memory :> bytes32 (word_add a (word (4 * k)))) s =
                   (if k < c then f k else EL (k - c) (mld_rej_eta_list %d b (2 * i))))"
   p.eregs (ESCAN_PTR p) (ESCAN_KEEP p) p.ectr flag p.el p.eb p.eeta);;

(* ------------------------------------------------------------------------- *)
(* The proof of a scan lemma, following the gcc proof of mld_rej_eta_c.      *)
(* ------------------------------------------------------------------------- *)

let ESCAN_VAL_WORD = prove
 (`!n. n < 2 EXP 64 ==> val(word n:int64) = n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT]);;

(* ------------------------------------------------------------------------- *)
(* The absorbing (ETA_ABS): after memset has zeroed the four states of 200   *)
(* bytes at sp + 96 + 200 k, the straight-line code XORs the four extended   *)
(* seeds of 66 bytes at sp + 896 + 96 k (the seed, the nonce, a zero byte)   *)
(* and the padding into them, from the head of the absorbing to the first    *)
(* call of mldsa_keccakf1600_permute. The states are then those of           *)
(* mld_keccak_absorb_once, as words: the seed, 0x1F after it and 0x80 at the *)
(* end of the rate (PC_SW of inline_challenge.ml).                           *)
(* ------------------------------------------------------------------------- *)

let ETA_BYTES_SUB = prove
 (`!a:int64 n x k l s:armstate.
        read (memory :> bytes(a,n)) s = x /\ k + l <= n
        ==> read (memory :> bytes(word_add a (word k),l)) s =
            (x DIV 2 EXP (8 * k)) MOD 2 EXP (8 * l)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let ETA_LOAD_OF_BYTES = prove
 (`(!a:int64 n s:armstate.
      read (memory :> bytes(a,16)) s = n
      ==> read (memory :> bytes128 a) s = word n) /\
   (!a:int64 n s:armstate.
      read (memory :> bytes(a,8)) s = n
      ==> read (memory :> bytes64 a) s = word n) /\
   (!a:int64 n s:armstate.
      read (memory :> bytes(a,2)) s = n
      ==> read (memory :> bytes16 a) s = word n) /\
   (!a:int64 n s:armstate.
      read (memory :> bytes(a,1)) s = n
      ==> read (memory :> bytes8 a) s = word n)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES128_WBYTES; BYTES64_WBYTES; BYTES16_WBYTES; BYTES8_WBYTES;
              READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; VAL_WORD;
              DIMINDEX_128; DIMINDEX_64; DIMINDEX_16; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPECL [`a:int64`; `16`; `read memory (s:armstate)`] READ_BYTES_BOUND) THEN
  MP_TAC(ISPECL [`a:int64`; `8`; `read memory (s:armstate)`] READ_BYTES_BOUND) THEN
  MP_TAC(ISPECL [`a:int64`; `2`; `read memory (s:armstate)`] READ_BYTES_BOUND) THEN
  MP_TAC(ISPECL [`a:int64`; `1`; `read memory (s:armstate)`] READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[]);;

let ETA_STATE_WORD66 = PC_STATE_WORD 66;;

let ETA_ABS_WORD = prove
 (`!C. C < 2 EXP 528
       ==> mld_keccak_absorb_once 136 0x1F 66 C =
           word_or (word_zx (word C:528 word):1600 word)
                   (word(2 EXP 528 * 31 + 2 EXP 1080 * 128))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`136`; `0x1F`; `66`; `C:num`] MLD_KECCAK_ABSORB_ONCE_SHORT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ARITH_RULE `8 * 66 = 528`] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM mld_shake256_state] THEN
  MATCH_MP_TAC ETA_STATE_WORD66 THEN ASM_REWRITE_TAC[]);;

(*** A piece of the state that is zero ***)

let ETA_PIECE_ZERO = prove
 (`!(S:1600 word) (A:int64) (s:armstate) off len.
     read (memory :> bytes(A,len)) s = 0 /\
     word_subword S (8 * off,8 * len):1600 word = word 0 /\ 8 * len <= 1600
     ==> read (memory :> bytes(A,len)) s =
         (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(AP_TERM `val:1600 word->num`
   (ASSUME `word_subword (S:1600 word) (8 * off,8 * len):1600 word = word 0`)) THEN
  ASM_SIMP_TAC[VAL_WORD_SUBWORD; DIMINDEX_CONV `dimindex(:1600)`;
               ARITH_RULE `l <= 1600 ==> MIN l 1600 = l`; VAL_WORD_0] THEN
  MESON_TAC[]);;

(*** The statement: h and x the absolute offsets of the head and the exit ***)

let ETA_ST k = 96 + 200 * k and ETA_EXT k = 896 + 96 * k;;

(*** The registers that the absorbing reads (pointers to the states and   ***)
(*** buffers), those that it sets or keeps, and those that it changes      ***)

type etaabs = { aregs : string; apost : string; ach : string };;

let ETA2_ABS =
  { aregs = "read X19 s = word_add sp (word 96) /\\ read X20 s = word_add sp (word 696)";
    apost = "read X19 s = word_add sp (word 96) /\\ read X20 s = word_add sp (word 696) /\\ " ^
            "read X21 s = word_add sp (word 296)";
    ach = "PC; X0; X8; X9; X10; X21" };;

let ETA_ABS_GEN_TM r h x =
  let cs = map (fun k -> Printf.sprintf "C%d" k) (0--3) in
  let pre = String.concat " /\\ "
    (map (fun k -> Printf.sprintf
       "read (memory :> bytes(word_add sp (word %d),66)) s = C%d" (ETA_EXT k) k) (0--3)) in
  let post = String.concat " /\\ "
    (map (fun k -> Printf.sprintf
       "read (memory :> bytes(word_add sp (word %d),200)) s = val(mld_keccak_absorb_once 136 0x1F 66 C%d)"
       (ETA_ST k) k) (0--3)) in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e (sp:int64) %s pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        aligned 16 sp /\\
        nonoverlapping (word_add sp (word 24),1256) (word pc,libmldsa_size)
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %d) /\\
                  read SP s = sp /\\ %s /\\
                  read (memory :> bytes(word_add sp (word 96),800)) s = 0 /\\ %s /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %d) /\\
                  read SP s = sp /\\ read X0 s = word_add sp (word 96) /\\ %s /\\
                  read (memory :> bytes64 (word_add sp (word 24))) s = word_add sp (word 496) /\\
                  %s /\\ %s /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events sp pc /\\
                     memaccess_inbounds e2
                      [word_add sp (word 24),1256] [word_add sp (word 24),1256]))
             (MAYCHANGE [%s] ,,
              MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q17; Q18] ,,
              MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(word_add sp (word 24),8);
                         memory :> bytes(word_add sp (word 96),800)])"
   (String.concat " " cs) ETA_MC h r.aregs pre x r.apost post pre r.ach);;

let ETA_ABS_TM = ETA_ABS_GEN_TM ETA2_ABS;;

(*** The facts for the loads: the bytes of the extended seeds as subwords  ***)
(*** of word Ck (as for the seed of poly_challenge), and the zero states   ***)

let ETA_SP_ADDR n =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,`sp:int64`),
          mk_comb(`word:num->int64`,mk_small_numeral n));;

let ETA_EXT_FACTS_TAC k =
  let a = ETA_SP_ADDR (ETA_EXT k) and c = mk_var("C"^string_of_int k,`:num`) in
  let bth = ASSUME(subst [a,`a:int64`; c,`c:num`]
             `read (memory :> bytes(a,66)) s0 = c`) in
  let bound = REWRITE_RULE[ARITH_RULE `8 * 66 = 528`]
   (REWRITE_RULE[GSYM READ_COMPONENT_COMPOSE; bth]
     (ISPECL [a; `66`; `read memory (s0:armstate)`] READ_BYTES_BOUND)) in
  let h8 = REWRITE_RULE[GEN `j:num` (MP (SPECL [c; `j:num`] (PC_BYTE_SUB 66)) bound)]
            (MATCH_MP MLD_READ_BYTES_BYTES8 bth) in
  let facts = map (fun (sz,off) ->
     let th = INST [a,`seed:int64`; c,`C:num`] (PC_SEED_FACT 66 sz off) in
     PC_NORM(MP th h8)) [16,0; 16,16; 16,32; 16,48; 2,64] in
  ASSUME_TAC bound THEN MAP_EVERY ASSUME_TAC facts;;

let ETA_ZERO_FACTS_TAC k =
  let zth = ASSUME `read (memory :> bytes(word_add sp (word 96),800)) s0 = 0` in
  let sub off len =
    let th = MP (SPECL [`word_add sp (word 96):int64`; `800`; `0`; mk_small_numeral(200 * k + off);
                        mk_small_numeral len; `s0:armstate`] ETA_BYTES_SUB)
                (CONJ zth (EQT_ELIM(NUM_REDUCE_CONV(mk_binary "<="
                   (mk_binary "+" (mk_small_numeral(200 * k + off),mk_small_numeral len),`800`))))) in
    CONV_RULE(PC_NORMC THENC RAND_CONV NUM_REDUCE_CONV) th in
  let ld off len lem = MATCH_MP lem (sub off len) in
  let [l128;_;l16;l8] = CONJUNCTS ETA_LOAD_OF_BYTES in
  MAP_EVERY ASSUME_TAC
   ([ld 0 16 l128; ld 16 16 l128; ld 32 16 l128; ld 48 16 l128;
     ld 64 2 l16; ld 66 1 l8; ld 135 1 l8; sub 67 68; sub 136 64]);;

(*** The chain of pieces of state k after the stores: Q (16 bytes), B (one ***)
(*** byte) and Z (zero, len bytes), against the word sw                    ***)

let ETA_CHAIN_TAC boff sw sname pieces =
  W(fun (asl,w) ->
    let s = mk_var(sname,`:armstate`) in
    let addr off = ETA_SP_ADDR (boff + off) in
    let d = addr 0 in
    let x = mk_comb(`val:1600 word->num`,sw) in
    let cur0 = PC_NORM(prove(
      subst [s,`s:armstate`; x,`x:num`; d,`d:int64`]
       `read (memory :> bytes(d,0)) s = x MOD 2 EXP (8 * 0)`,
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; MULT_CLAUSES; EXP; MOD_1])) in
    let find_fact tm = snd(find (fun (_,th) -> let c = concl th in is_eq c && lhs c = tm) asl) in
    let step (cur,j) (off,len) =
      assert (off = j);
      let a = addr off in
      let pth =
        if len = 16 || len = 1 then
          let comp,lem = if len = 16 then "bytes128",PU_PIECE16 else "bytes8",PU_PIECE8 in
          let fact = snd(find (fun (_,th) -> let c = concl th in
                       is_eq c && (try rand(lhs c) = s && rand(rand(lhand(lhs c))) = a &&
                                       fst(dest_const(rator(rand(lhand(lhs c))))) = comp
                                   with Failure _ -> false)) asl) in
          let v = rhs(concl fact) in
          let inst = SPECL [sw; a; s; v; mk_small_numeral off] lem in
          let eqt = snd(dest_conj(fst(dest_imp(concl inst)))) in
          let eqth = prove(eqt, CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST) in
          MP inst (CONJ fact eqth)
        else
          let zf = find_fact (subst [a,`a:int64`; s,`s:armstate`; mk_small_numeral len,`l:num`]
                               `read (memory :> bytes(a,l)) s`) in
          let inst = SPECL [sw; a; s; mk_small_numeral off; mk_small_numeral len] ETA_PIECE_ZERO in
          let ante = fst(dest_imp(concl inst)) in
          let _,r = dest_conj ante in
          let sth = prove(r, CONJ_TAC THENL
                        [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST;
                         CONV_TAC NUM_REDUCE_CONV]) in
          MP inst (CONJ zf sth) in
      let pth = PC_NORM pth in
      let ext = PC_NORM(SPECL [d; mk_small_numeral j; mk_small_numeral len; x; s]
                          READ_MEMORY_BYTES_EXTEND) in
      (MP ext (CONJ cur pth), j + len) in
    let fin,_ = rev_itlist (fun p st -> step st p) pieces (cur0,0) in
    ASSUME_TAC(REWRITE_RULE[PC_MODLEMMA] fin));;

let ETA_PIECES =
  [0,16; 16,16; 32,16; 48,16; 64,1; 65,1; 66,1; 67,68; 135,1; 136,64];;

let ETA_SW k =
  vsubst [mk_var("C"^string_of_int k,`:num`),`C:num`]
   `word_or (word_zx (word C:528 word):1600 word)
            (word(2 EXP 528 * 31 + 2 EXP 1080 * 128))`;;

(*** The facts for iteration i, after FULL_INIT_TAC, as in the gcc proof ***)

let ESCAN_SETUP_TAC p =
  let eta = mk_small_numeral p.eeta and len = mk_small_numeral p.el in
  let mtm = list_mk_comb(`mld_rej_eta_bytes`,[eta; `256`; `c:num`; `b:num->byte`; len]) in
  let ltm = list_mk_comb(`mld_rej_eta_list`,[eta; `b:num->byte`; `2 * i`]) in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < M` ASSUME_TAC THENL
   [UNDISCH_TAC `i < LENGTH (D:bool list) DIV 2` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `i < M`) o
    check (fun th -> is_forall(concl th) &&
                     can (term_match [] `!m. m < M ==> P m`) (concl th))) THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `2 * i` o
    check (fun th -> is_forall(concl th) &&
                     can (term_match [] `!n. n <= 2 * M ==> P n`) (concl th))) THEN
  ANTS_TAC THENL [UNDISCH_TAC `i < M` THEN ARITH_TAC; DISCH_TAC] THEN
  FULL_INIT_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_imp(concl th) && free_in `X8` (concl th)
                          then ASSUME_TAC(MP th (ASSUME `i < M`)) else NO_TAC) THEN
  ABBREV_TAC `l = LENGTH(FILTER (\x. x) (SUB_LIST (0,2 * i) (D:bool list)))` THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `l:num`)) THEN
  SUBGOAL_THEN `c + l < 256` ASSUME_TAC THENL
   [UNDISCH_TAC (mk_binary "<" (mk_binary "+" (`c:num`,mk_comb(`LENGTH:int32 list->num`,ltm)),`256`)) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `MIN (256 - c) l = l` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [UNDISCH_TAC `c + l < 256` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME (mk_binary "<" (`i:num`,len))) o SPEC `i:num` o
    check (fun th -> is_forall(concl th) && free_in `bytes8` (concl th))) THEN
  DISCH_TAC THEN
  (if p.edisp = 0 then ALL_TAC else
   let alt = parse_term(Printf.sprintf "word_add sp (word (%d + i + %d)):int64" (p.eb - p.edisp) p.edisp)
   and std = parse_term(Printf.sprintf "word_add sp (word (%d + i)):int64" p.eb) in
   SUBGOAL_THEN (subst [alt,`x:int64`] `read (memory :> bytes8 x) s0 = (b:num->byte) i`) ASSUME_TAC THENL
    [SUBGOAL_THEN (mk_eq(alt,std)) SUBST1_TAC THENL [CONV_TAC WORD_RULE; ASM_REWRITE_TAC[]];
     ALL_TAC]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `2 * (i + 1)` o
    check (fun th -> is_forall(concl th) &&
                     can (term_match [] `!n. n <= 2 * M ==> P n`) (concl th))) THEN
  ANTS_TAC THENL [UNDISCH_TAC `i < M` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(MATCH_MP MLD_REJ_ETA_BYTES_NEXT
   (CONJ (ASSUME (mk_eq(mtm,`M:num`))) (ASSUME `i < M`))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `2 * i + 1` o
    check (fun th -> is_forall(concl th) &&
                     can (term_match [] `!k. k < 2 * M ==> P k`) (concl th))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `2 * i` o
    check (fun th -> is_forall(concl th) &&
                     can (term_match [] `!k. k < 2 * M ==> P k`) (concl th))) THEN
  REWRITE_TAC[ARITH_RULE `2 * i < 2 * M <=> i < M`;
              ARITH_RULE `2 * i + 1 < 2 * M <=> i < M`; ASSUME `i < M`] THEN
  REWRITE_TAC[MLD_REJ_ETA_LIST_BYTE; LENGTH_APPEND; SAMPLING_LENGTH_COND;
              MLD_REJ_ETA_VALID_BYTE; mld_rej_eta_coeff;
              ASSUME (mk_eq(mk_comb(`LENGTH:int32 list->num`,ltm),`l:num`))] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_EQ_CONV) THEN REWRITE_TAC[] THEN
  MP_TAC(ISPEC `(b:num->byte) i` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ABBREV_TAC `n = val((b:num->byte) i)` THEN REPEAT DISCH_TAC;;

(*** Simulation: the nibbles as numbers, the compares of the counter    ***)
(*** (64 bits) and of the nibbles (32 bits) decided from the cases       ***)

let ESCAN_CMP64 = prove
 (`!x y. x < 2 EXP 64 /\ y < 2 EXP 64
         ==> ((&(val(word x:int64)) - &(val(word y:int64)):int =
               &(val(word_sub (word x) (word y):int64)) <=> y <= x) /\
              (&(val(word x:int64)) - &y:int =
               &(val(word_sub (word x) (word y):int64)) <=> y <= x) /\
              (&x - &y:int =
               &(val(word_sub (word x) (word y):int64)) <=> y <= x) /\
              (val(word_sub (word x) (word y):int64) = 0 <=> x = y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word x:int64) = x /\ val(word y:int64) = y`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONJ_TAC THEN
    MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES; DIMINDEX_64] THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN
  REWRITE_TAC[INT_ARITH `x - y:int = z <=> x = y + z`] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ASM_ARITH_TAC);;

(*** Deciding a proposition by arithmetic, keeping it as an assumption,  ***)
(*** but an equation x = y only as x <= y and y <= x, as the simulator     ***)
(*** would rewrite later states with it                                    ***)

let ESCAN_DECIDE_PROP_TAC c =
  let keep th =
    if is_eq(concl th) then
      MAP_EVERY ASSUME_TAC
       (CONJUNCTS(MATCH_MP (ARITH_RULE `x:num = y ==> x <= y /\ y <= x`) th))
    else ASSUME_TAC th in
  (SUBGOAL_THEN c (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[EQT_INTRO th]) THEN keep th)
   THENL [SIMPLE_ARITH_TAC; ALL_TAC]) ORELSE
  (SUBGOAL_THEN (mk_neg c)
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[EQF_INTRO th]) THEN ASSUME_TAC th)
   THENL [SIMPLE_ARITH_TAC; ALL_TAC]);;

let ESCAN_CMP_REWRITE_TAC pat th =
  W(fun (asl,w) ->
    let tms = setify (find_terms (can (term_match [] pat))
                                 (list_mk_conj(map (concl o snd) asl))) in
    MAP_EVERY (fun t ->
      let x = rand(lhand t) and y = rand(rand t) in
      TRY(MP_TAC(SPECL [x;y] th) THEN
          ANTS_TAC THENL
           [CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THEN SIMPLE_ARITH_TAC;
            DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))])) tms);;

let ESCAN_DECIDE_TAC =
  let has_read tm =
    can (find_term (fun t -> is_const t && fst(dest_const t) = "read")) tm in
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD]) THEN
  W32_SMALL_TAC THEN
  ESCAN_CMP_REWRITE_TAC `word_sub (word x) (word y):int32` WORD_CMP_32_FLAGS THEN
  ESCAN_CMP_REWRITE_TAC `word_sub (word x) (word y):int64` ESCAN_CMP64 THEN
  W(fun (asl,w) ->
     let ps = mapfilter (fun (_,th) ->
       let l,r = dest_eq(concl th) in
       let f = rand(rator l) in
       if mem f [`CF`;`ZF`] && not(r = `T` || r = `F`) then r
       else failwith "") asl in
     MAP_EVERY (fun p -> TRY(ESCAN_DECIDE_PROP_TAC p)) ps) THEN
  W(fun (asl,w) ->
    let rec conds bound tm acc =
      match tm with
        Comb(Comb(Comb(Const("COND",_),p),a),b) ->
          let acc' = if intersect (frees p) bound = [] && not (mem p acc)
                     then p::acc else acc in
          conds bound p (conds bound a (conds bound b acc'))
      | Comb(l,r) -> conds bound l (conds bound r acc)
      | Abs(v,bd) -> conds (v::bound) bd acc
      | _ -> acc in
    let ps = itlist (fun (_,th) acc ->
                if has_read (concl th) then conds [] (concl th) acc
                else acc) asl [] in
    MAP_EVERY (fun p -> TRY(ESCAN_DECIDE_PROP_TAC p)) ps);;

(*** For eta = 4 the code compares the byte itself (byte <= 0x8f for the  ***)
(*** high nibble): ESCAN_ZX_SUB puts its 32-bit compare in the form of     ***)
(*** WORD_CMP_32_FLAGS                                                      ***)

let ESCAN_ZX_SUB = prove
 (`!(y:byte) k. word_sub (word_zx y:int32) k = word_sub (word(val y)) k /\
                val(word_zx y:int32) = val(word(val y):int32)`,
  REWRITE_TAC[word_zx]);;

(*** The store address [ptr, ctr, lsl #2] is shown to be inside the     ***)
(*** polynomial with the fact val(word t) = t for the counter word t,    ***)
(*** for that step only (as SAMPLING_UXTW_THMS in the gcc proofs)        ***)

let ESCAN_STEP_X_TAC extra execth ctr n (asl,w) =
  let ths = try let t = rand(SAMPLING_REGVAL ctr (asl,w)) in
                if is_numeral t || is_var t then [] else [SPEC t ESCAN_VAL_WORD]
            with Failure _ -> [] in
  let ts = map (fun th -> rand(concl th)) ths in
  (MAP_EVERY (fun th ->
     TRY(MP_TAC th THEN ANTS_TAC THENL
          [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; DISCH_TAC])) ths THEN
   ARM_STEPS_TAC execth [n] THEN
   REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> mem (concl th) ts))) THEN
   RULE_ASSUM_TAC(REWRITE_RULE(MLD_BYTE_NIBBLES :: extra)) THEN
   (fun g ->
     if exists (fun (_,th) -> concl th = `val((b:num->byte) i) = n`) (fst g) then
       RULE_ASSUM_TAC(fun th ->
         if concl th = `val((b:num->byte) i) = n` then th
         else REWRITE_RULE[ASSUME `val((b:num->byte) i) = n`] th) g
     else ALL_TAC g) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32]) THEN
   TRY SAMPLING_W64_TAC THEN TRY(SAMPLING_COND_REWRITE_TAC [ESCAN_VAL_WORD]) THEN
   ESCAN_DECIDE_TAC) (asl,w);;

let ESCAN_STEP_TAC = ESCAN_STEP_X_TAC [];;

let rec ESCAN_RUN_TAC extra execth ctr n stop (asl,w) =
  (ESCAN_STEP_X_TAC extra execth ctr n THEN
   (fun g -> let pcv = SAMPLING_REGVAL `PC` g in
             if is_cond pcv || mem pcv stop then ALL_TAC g
             else ESCAN_RUN_TAC extra execth ctr (n + 1) stop g)) (asl,w);;

(*** The coefficient for eta = 2 as clang computes it: q = (205 t) >> 10 ***)
(*** (q <= 2), q | (q << 2) = 5 q, and 5 q - t + 2                        ***)

let ESCAN_ETA2_COEFF = prove
 (`!t. t < 16
       ==> word_add
            (word_sub
              (word_or (word_ushr (word (0 + val(word t:int32) * 205)) 10)
                       (word_shl (word_ushr (word (0 + val(word t:int32) * 205)) 10) 2))
              (word t))
            (word 2):int32 =
           word_sub (word 2)
            (word_sub (word t)
              (word_mul (word_ushr (word_mul (word 205) (word t)) 10)
                        (word 5)))`,
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(REPEATC(CHANGED_CONV(NUM_REDUCE_CONV THENC WORD_REDUCE_CONV))));;

(*** Deciding the arithmetic conditionals of the goal ***)

let ESCAN_DECIDE_GOAL_TAC =
  W(fun (asl,w) ->
    let cs = setify(map (fun t -> lhand(rator t)) (find_terms is_cond w)) in
    let cs = filter (fun c -> not(can (find_term (fun t -> is_const t &&
                       mem (fst(dest_const t)) ["EL"; "read"])) c)) cs in
    MAP_EVERY (fun c ->
      TRY(SUBGOAL_THEN c MP_TAC THENL
           [SIMPLE_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])]) THEN
      TRY(SUBGOAL_THEN (mk_neg c) MP_TAC THENL
           [SIMPLE_ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])]))
     cs);;

(*** The coefficients after iteration i: those before, and the new ones ***)

let ESCAN_STORE_TAC p =
  let ltm = list_mk_comb(`mld_rej_eta_list`,[mk_small_numeral p.eeta; `b:num->byte`; `2 * i`]) in
  let lth = ASSUME (mk_eq(mk_comb(`LENGTH:int32 list->num`,ltm),`l:num`)) in
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[APPEND] THEN
  ASM_CASES_TAC `k < c + l` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      is_forall(concl th) && free_in `bytes32` (concl th) &&
      free_in `l:num` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[EL_APPEND; lth] THEN
    SUBGOAL_THEN `k - c < l` (fun th -> REWRITE_TAC[th]) THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `k = (c + l) + 0 \/ k = (c + l) + 1`
   (DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[MIN]) THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    REPEAT COND_CASES_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC; ALL_TAC] THEN
  TRY(SUBGOAL_THEN `F` CONTR_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MIN]) THEN
      POP_ASSUM MP_TAC THEN REPEAT COND_CASES_TAC THEN SIMPLE_ARITH_TAC THEN NO_TAC) THEN
  REWRITE_TAC[EL_APPEND; lth;
              ARITH_RULE `~((c + l) + k < c)`; ARITH_RULE `((c + l) + k) - c = l + k`;
              ARITH_RULE `~(l + k < l)`; ARITH_RULE `(l + k) - l = k`] THEN
  CONV_TAC(RAND_CONV SAMPLING_EL_LIST_CONV) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN ASM_REWRITE_TAC[];;

(*** One path of the iteration, from the head to the loop test ***)

let ESCAN_PATH_TAC execth p =
  let pcw off = mk_comb(`word:num->int64`,
                mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral off)) in
  let pc1 = pcw p.eh in
  ESCAN_RUN_TAC (if p.eeta = 2 then [] else [ESCAN_ZX_SUB])
    execth (mk_const(p.ectr,[])) 1 [pc1; pcw p.ex] THEN
  SAMPLING_COND_REWRITE_TAC[ESCAN_ETA2_COEFF] THEN
  (SAMPLING_LOOP_PC_TAC `LENGTH (D:bool list) DIV 2`
     [SYM(ASSUME `M = LENGTH (D:bool list) DIV 2`)] ORELSE
   TRY(SAMPLING_LOOP_EXIT_TAC `LENGTH (D:bool list) DIV 2`
         [SYM(ASSUME `M = LENGTH (D:bool list) DIV 2`)] pc1)) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_iff(concl th) && lhand(concl th) = `i + 1 < M`)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(SAMPLING_SELECT_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(DISCH_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(STRIP_TAC THEN SUBGOAL_THEN `F` CONTR_TAC THEN SIMPLE_ARITH_TAC THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(AP_TERM_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[MIN]) THEN REWRITE_TAC[MIN] THEN
      REPEAT COND_CASES_TAC THEN SIMPLE_ARITH_TAC THEN NO_TAC) THEN
  TRY(DISCH_TAC THEN REWRITE_TAC[MIN] THEN ESCAN_DECIDE_GOAL_TAC THEN
      ESCAN_DECIDE_GOAL_TAC THEN NO_TAC) THEN
  TRY(ESCAN_STORE_TAC p THEN NO_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `l:num` &&
    can (term_match [] `LENGTH(FILTER (\x:bool. x) l)`) (lhs(concl th)))) THEN
  SAMPLING_PATH_DISCHARGE_TAC;;

(*** The whole lemma ***)

(*** In a lemma with the split option (the last iteration of a path      ***)
(*** that continues has other events), the facts i + 1 < 136 or not      ***)

let ESCAN_LAST_TAC last =
  let mth = ASSUME `M = LENGTH (D:bool list) DIV 2` in
  FIRST_ASSUM(fun th -> if is_iff(concl th) && lhand(concl th) = `i + 1 < M`
                        then MP_TAC(REWRITE_RULE[mth] th) else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  (if not last then STRIP_TAC
   else DISCH_THEN(fun th ->
     let p,q = dest_conj(rand(concl th)) in
     SUBGOAL_THEN q ASSUME_TAC THENL
      [SIMPLE_ARITH_TAC;
       ASSUME_TAC(MP (MP (SPECL [p;q] (TAUT `!p q. ~(p /\ q) ==> q ==> ~p`)) th)
                     (ASSUME q))]));;

let ESCAN_BODY_TAC execth p =
  let path = ESCAN_PATH_TAC execth p in
  let cpath = if not p.esplit then path else
    ASM_CASES_TAC `i + 1 < LENGTH (D:bool list) DIV 2` THENL
     [ESCAN_LAST_TAC false THEN path; ESCAN_LAST_TAC true THEN path] in
  ESCAN_SETUP_TAC p THEN
  SAMPLING_CASES_TAC `EL (2 * i) (D:bool list)` THENL
   [SAMPLING_CASES_TAC `EL (2 * i + 1) (D:bool list)` THENL
     [ASM_CASES_TAC `c + l + 1 < 256` THENL
       [ASM_CASES_TAC `c + l + 2 < 256` THENL [cpath; path]; path];
      ASM_CASES_TAC `c + l + 1 < 256` THENL [cpath; path]];
    SAMPLING_CASES_TAC `EL (2 * i + 1) (D:bool list)` THENL
     [ASM_CASES_TAC `c + l + 1 < 256` THENL [cpath; path]; cpath]];;

let ESCAN_EXIT_TAC p =
  let len = mk_small_numeral p.el in
  let mth = ASSUME `M = LENGTH (D:bool list) DIV 2` in
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  RULE_ASSUM_TAC(fun th -> if concl th = concl mth then th
                           else REWRITE_RULE[GSYM mth] th) THEN
  REWRITE_TAC[GSYM mth] THEN
  FIRST_ASSUM(MP_TAC o SPEC `2 * M` o
    check (fun th -> is_forall(concl th) &&
                     can (term_match [] `!n. n <= 2 * M ==> P n`) (concl th))) THEN
  REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THEN
  RULE_ASSUM_TAC(fun th -> if is_imp(concl th) && lhand(concl th) = `0 < M`
                           then MP th (ASSUME `0 < M`) else th) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN SIMPLE_ARITH_TAC THEN NO_TAC) THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      is_forall(concl th) && free_in `bytes32` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC EL_MLD_REJ_ETA_LIST_PREFIX THEN
    CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [mk_binary "<=" (`M:num`,len); concl mth] THEN ARITH_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[MIN]) THEN
      POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
      REPEAT COND_CASES_TAC THEN SIMPLE_ARITH_TAC];
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let ESCAN_PROVE execth p =
  let eta = mk_small_numeral p.eeta and len = mk_small_numeral p.el in
  let pcn off = mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral off) in
  prove(ESCAN_TM p,
  CONCRETIZE_F_EVENTS_TAC (ESCAN_TEMPLATE_F p.esplit) THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC ([`e:(uarch_event)list`; `a:int64`; `sp:int64`; `c:num`;
                       `f:num->int32`; `b:num->byte`] @
                       (if p.ekeep = "" then [] else [`x1:int64`]) @ [`pc:num`]) THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[MLD_REJ_ETA_CTR] THEN
  MP_TAC(SPECL [eta; `256`; `c:num`; `b:num->byte`; len] MLD_REJ_ETA_DECLASS) THEN
  MP_TAC(SPECL [eta; `256`; `c:num`; `b:num->byte`; len;
    list_mk_comb(`mld_rej_eta_bytes`,[eta; `256`; `c:num`; `b:num->byte`; len])]
    MLD_REJ_ETA_BYTES) THEN REWRITE_TAC[] THEN
  ABBREV_TAC(mk_eq(`D:bool list`,
    list_mk_comb(`mld_rej_eta_declass`,[eta; `256`; `c:num`; `b:num->byte`; len]))) THEN
  ABBREV_TAC(mk_eq(`M:num`,
    list_mk_comb(`mld_rej_eta_bytes`,[eta; `256`; `c:num`; `b:num->byte`; len]))) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `0 < M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC MLD_REJ_ETA_BYTES_POS THEN
    ASM_REWRITE_TAC[ARITH]; ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `l = 2 * M ==> M = l DIV 2`) o
    check (fun th -> concl th = `LENGTH (D:bool list) = 2 * M`)) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `LENGTH (D:bool list) DIV 2`
    (pcn p.eh) (pcn p.ex) (ESCAN_INV p) THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `M = LENGTH (D:bool list) DIV 2`)) THEN
    UNDISCH_TAC `0 < M` THEN ARITH_TAC;
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES; FILTER; LENGTH;
                ARITH_RULE `MIN a 0 = 0`; ADD_CLAUSES; LT_REFL] THEN
    CONJ_TAC THENL [X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[];
                    DISCHARGE_SAFETY_PROPERTY_TAC];
    ESCAN_BODY_TAC execth p;
    ESCAN_EXIT_TAC p]);;

let ETA_ABS_GEN_PROVE r execth h x nsteps =
  prove(ETA_ABS_GEN_TM r h x,
  CONCRETIZE_F_EVENTS_TAC `\(sp:int64) (pc:num). f_ev_abs sp pc:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `sp:int64`; `C0:num`; `C1:num`;
                       `C2:num`; `C3:num`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  MAP_EVERY ETA_EXT_FACTS_TAC (0--3) THEN MAP_EVERY ETA_ZERO_FACTS_TAC (0--3) THEN
  ARM_STEPS_TAC execth (1--nsteps) THEN
  MAP_EVERY (fun k -> ETA_CHAIN_TAC (ETA_ST k) (ETA_SW k)
                        ("s" ^ string_of_int nsteps) ETA_PIECES) (0--3) THEN
  ENSURES_FINAL_STATE_TAC THEN
  W(fun (asl,w) ->
    let bs = mapfilter (fun (_,th) -> let c = concl th in
               if can (term_match [] `C < 2 EXP 528`) c
               then MP (SPEC (lhand c) ETA_ABS_WORD) th else failwith "") asl in
    REWRITE_TAC bs) THEN
  ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC);;

let ETA_ABS_PROVE = ETA_ABS_GEN_PROVE ETA2_ABS;;

(* ------------------------------------------------------------------------- *)
(* The tests of whether a polynomial needs more (ETA_TST): from the counts   *)
(* c0..c3 in the registers ctrs, the code sets the flags (CSET) ck < 256 in  *)
(* the registers csets (none in the test after the first pass) and branches  *)
(* to cont if one count is below 256, else to ext. The events depend on the  *)
(* first polynomial that needs more.                                         *)
(* ------------------------------------------------------------------------- *)

let ETA_FLAG k = Printf.sprintf "(if c%d < 256 then word 1 else word 0)" k;;

let ETA_TST_TM ent ctrs csets cont ext =
  let pre = String.concat " /\\ "
    (map (fun (r,k) -> Printf.sprintf "read %s s = word c%d" r k) (zip ctrs (0--3))) in
  let flags = String.concat ""
    (map (fun (r,k) -> Printf.sprintf "read %s s = %s /\\ " r (ETA_FLAG k)) csets) in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e c0 c1 c2 c3 pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        c0 <= 256 /\\ c1 <= 256 /\\ c2 <= 256 /\\ c3 <= 256
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %d) /\\ %s /\\ read events s = e)
             (\\s. read PC s =
                  (if c0 < 256 \\/ c1 < 256 \\/ c2 < 256 \\/ c3 < 256
                   then word (pc + %d) else word (pc + %d)) /\\ %s
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events c0 c1 c2 c3 pc /\\
                     memaccess_inbounds e2 [] []))
             (MAYCHANGE [%s] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])"
   ETA_MC ent pre cont ext flags (String.concat "; " ("PC" :: map fst csets)));;

let ETA_TST_TEMPLATE =
 `\(c0:num) (c1:num) (c2:num) (c3:num) (pc:num).
    if c0 < 256 then f_ev_t0 c0 c1 c2 c3 pc
    else if c1 < 256 then f_ev_t1 c0 c1 c2 c3 pc
    else if c2 < 256 then f_ev_t2 c0 c1 c2 c3 pc
    else if c3 < 256 then f_ev_t3 c0 c1 c2 c3 pc
    else f_ev_t4 c0 c1 c2 c3 pc:(uarch_event)list`;;

let rec ETA_RUN_TO_TAC execth n stop (asl,w) =
  (ESCAN_STEP_TAC execth `X30` n THEN
   (fun g -> let pcv = SAMPLING_REGVAL `PC` g in
             if mem pcv stop then ALL_TAC g
             else ETA_RUN_TO_TAC execth (n + 1) stop g)) (asl,w);;

let ETA_PCW off = mk_comb(`word:num->int64`,
                    mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral off));;

let ETA_CSET = prove
 (`(!c. word_zx (if 256 <= c then word 0 else word 1:int32):int64 =
        if c < 256 then word 1 else word 0) /\
   (!p. word_zx (if p then word 1 else word 0:int64):int32 =
        if p then word 1 else word 0) /\
   (!p. word_zx (if p then word 1 else word 0:int32):int64 =
        if p then word 1 else word 0)`,
  REPEAT CONJ_TAC THEN GEN_TAC THENL
   [ASM_CASES_TAC `c < 256` THEN ASM_REWRITE_TAC[GSYM NOT_LT];
    ASM_CASES_TAC `p:bool` THEN ASM_REWRITE_TAC[];
    ASM_CASES_TAC `p:bool` THEN ASM_REWRITE_TAC[]] THEN
  CONV_TAC WORD_REDUCE_CONV);;

let ETA_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ETA_CSET] THEN
  ESCAN_DECIDE_GOAL_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(CONV_TAC(DEPTH_CONV WORD_RED_CONV)) THEN REWRITE_TAC[] THEN
  TRY DISCHARGE_SAFETY_PROPERTY_TAC;;

let ETA_TST_PROVE execth ent ctrs csets cont ext =
  let run = FULL_INIT_TAC THEN ETA_RUN_TO_TAC execth 1 [ETA_PCW cont; ETA_PCW ext] THEN
            ETA_FINAL_TAC in
  prove(ETA_TST_TM ent ctrs csets cont ext,
  CONCRETIZE_F_EVENTS_TAC ETA_TST_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `c0:num`; `c1:num`; `c2:num`; `c3:num`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `c0 < 256` THENL
   [run; ASM_CASES_TAC `c1 < 256` THENL
   [run; ASM_CASES_TAC `c2 < 256` THENL
   [run; ASM_CASES_TAC `c3 < 256` THEN run]]]);;

(* ------------------------------------------------------------------------- *)
(* The guarded scans of the loop over the further blocks: the code tests the *)
(* flag c < 256 of a polynomial (TBZ) and runs its scan only if it is set.   *)
(* With c <= 256 the result has the same form as that of the scan, as        *)
(* mld_rej_eta_ctr eta 256 256 b L = 256. ETA_GS1 is a test and one scan;    *)
(* ETA_GS01 the tests and scans of the first two polynomials, whose code     *)
(* interleaves them.                                                         *)
(* ------------------------------------------------------------------------- *)

let ETA_CTR_FULL = prove
 (`!eta c (b:num->byte) L. 256 <= c ==> mld_rej_eta_ctr eta 256 c b L = c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_rej_eta_ctr] THEN
  SUBGOAL_THEN `256 - c = 0` SUBST1_TAC THENL
   [UNDISCH_TAC `256 <= c` THEN ARITH_TAC; ARITH_TAC]);;

let ETA_MCODE = mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc;;

let ETA_CALL_TAC execth name ilist allowed n =
  REMOVE_THEN name (fun th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true (ETA_MCODE,execth,0x0,ETA_MCODE,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [(FULL_EXISTS_E2_TAC (ref allowed) ORELSE PC_E2_TAC (ref allowed));
      LABEL_TAC name th]);;

let rec ETA_RUN_CALLS_TAC execth calls stop allowed n (asl,w) =
  let pcv = SAMPLING_REGVAL `PC` (asl,w) in
  if mem pcv stop then ALL_TAC (asl,w) else
  let call = try Some(assoc pcv calls) with Failure _ -> None in
  match call with
    Some(name,ilist) ->
      (ETA_CALL_TAC execth name ilist allowed n THEN
       ETA_RUN_CALLS_TAC execth calls stop allowed (n + 1)) (asl,w)
  | None ->
      (ESCAN_STEP_TAC execth `X30` n THEN
       RULE_ASSUM_TAC(fun th ->
         let c = concl th in
         if is_eq c && (try rand(rator(lhs c)) = `PC` with Failure _ -> false) &&
            is_cond(rhs c)
         then CONV_RULE(RAND_CONV(DEPTH_CONV WORD_RED_CONV THENC REWRITE_CONV[])) th
         else th) THEN
       ETA_RUN_CALLS_TAC execth calls stop allowed (n + 1)) (asl,w);;

let ETA_GS1_TM ent ext flagpre p extra_nov extra_rd extra_ch =
  let ctr = Printf.sprintf "mld_rej_eta_ctr %d 256 c b %d" p.eeta p.el in
  let ch = ["PC"; "X8"; p.ectr] @ p.ech @ extra_ch in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e (a:int64) (sp:int64) (c:num) (f:num->int32) (b:num->byte) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        c <= 256 /\\ aligned 16 sp /\\
        nonoverlapping (a,1024) (word pc,libmldsa_size) /\\
        nonoverlapping (a,1024) (word_add sp (word %d),%d)%s
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %d) /\\ %s /\\
                  read %s s = word c /\\ %s /\\ %s /\\
                  (!j. j < %d
                       ==> read (memory :> bytes8 (word_add sp (word (%d + j)))) s = b j) /\\
                  (!k. k < c
                       ==> read (memory :> bytes32 (word_add a (word (4 * k)))) s = f k) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %d) /\\
                  read %s s = word (%s) /\\ %s <= 256 /\\
                  (!k. k < %s
                       ==> read (memory :> bytes32 (word_add a (word (4 * k)))) s =
                           (if k < c then f k
                            else EL (k - c) (mld_rej_eta_list %d b (2 * %d)))) /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events a sp c (mld_rej_eta_declass %d 256 c b %d) pc /\\
                     memaccess_inbounds e2
                      [a,1024; word_add sp (word %d),%d%s] [a,1024]))
             (MAYCHANGE [%s] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(a,1024)])"
   p.eb p.el extra_nov ETA_MC ent flagpre p.ectr p.eregs (ESCAN_PTR p) p.el p.eb
   ext p.ectr ctr ctr ctr p.eeta p.el p.eeta p.el p.eb p.el extra_rd
   (String.concat "; " ch));;

let ETA_GS1_TEMPLATE =
 `\(a:int64) (sp:int64) (c:num) (D:bool list) (pc:num).
    if c < 256 then f_ev_s a sp c D pc else f_ev_k a sp c D pc:(uarch_event)list`;;

let ETA_GS_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(X_GEN_TAC `k:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[] THEN SUBGOAL_THEN `F` CONTR_TAC THEN SIMPLE_ARITH_TAC THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let ETA_GS1_PROVE execth ent ext flagpre p extra_nov extra_rd extra_ch scanth =
  let declass = list_mk_comb(`mld_rej_eta_declass`,
    [mk_small_numeral p.eeta; `256`; `c:num`; `b:num->byte`; mk_small_numeral p.el]) in
  let ctrtm = list_mk_comb(`mld_rej_eta_ctr`,
    [mk_small_numeral p.eeta; `256`; `c:num`; `b:num->byte`; mk_small_numeral p.el]) in
  let allowed = [`a:int64`; `sp:int64`; `c:num`; `D:bool list`; `pc:num`] in
  let stop = [ETA_PCW ext] in
  prove(ETA_GS1_TM ent ext flagpre p extra_nov extra_rd extra_ch,
  ASSUME_CALLEE_SAFETY_TAILED_TAC scanth "H_SCAN" THEN
  CONCRETIZE_F_EVENTS_TAC ETA_GS1_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `a:int64`; `sp:int64`; `c:num`;
                       `f:num->int32`; `b:num->byte`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ABBREV_TAC(mk_eq(`D:bool list`,declass)) THEN
  ASM_CASES_TAC `c < 256` THENL
   [FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(fun th -> if concl th = `c < 256` then th
                             else REWRITE_RULE[ASSUME `c < 256`] th) THEN
    ETA_RUN_CALLS_TAC execth
      [ETA_PCW p.eh, ("H_SCAN",[`a:int64`; `sp:int64`; `c:num`; `f:num->int32`;
                                `b:num->byte`] @ (if p.ekeep = "" then [] else [`read X1 s`]) @
                                [`pc:num`])] stop allowed 1 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME(mk_eq(declass,`D:bool list`))]) THEN
    ETA_GS_FINAL_TAC;
    FULL_INIT_TAC THEN
    RULE_ASSUM_TAC(fun th -> if concl th = `~(c < 256)` then th
                             else REWRITE_RULE[ASSUME `~(c < 256)`] th) THEN
    ETA_RUN_CALLS_TAC execth [] stop allowed 1 THEN
    SUBGOAL_THEN (mk_eq(ctrtm,`c:num`)) SUBST1_TAC THENL
     [MATCH_MP_TAC ETA_CTR_FULL THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ETA_GS_FINAL_TAC]);;

(*** The first two polynomials of the loop: from the TBZ of the flag of    ***)
(*** polynomial 0 (in X8) to that of polynomial 2 (in X15, loaded from     ***)
(*** fl2 at sp + 80), with the scans p0 and p1 (pointers loaded from the   ***)
(*** stack slots at sp + 88 and sp + 48); r2 and r3 are loaded into        ***)
(*** X13/X12 for the later scans                                           ***)

(*** The parameters: eta, the value of X21 (the constant of the scans),   ***)
(*** the offset of buffer 1 (in X28), the length of the region of the two ***)
(*** buffers from sp + 1280, and the registers that keep the flag of       ***)
(*** polynomial 1 across scan 0 and that of polynomial 2 across scan 1     ***)

type etags = { geta : int; gk : int; gb1 : int; gblen : int; gkeep0 : string; gkeep1 : string };;

let ETA2_GS = { geta = 2; gk = 205; gb1 = 1440; gblen = 296; gkeep0 = "X1"; gkeep1 = "X15" };;

let ETA_GS01_GEN_TM g ent ext p0 p1 =
  let ctr k = Printf.sprintf "mld_rej_eta_ctr %d 256 c%d b%d 136" g.geta k k in
  let coef k = Printf.sprintf
    "(!k. k < %s ==> read (memory :> bytes32 (word_add r%d (word (4 * k)))) s =
          (if k < c%d then f%d k else EL (k - c%d) (mld_rej_eta_list %d b%d (2 * 136))))"
    (ctr k) k k k k g.geta k in
  parse_term(Printf.sprintf
   "exists f_events.
      forall e (r0:int64) (r1:int64) (sp:int64) (c0:num) (c1:num)
             (f0:num->int32) (f1:num->int32) (b0:num->byte) (b1:num->byte)
             (r2:int64) (r3:int64) (fl2:int32) pc.
        aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
        c0 <= 256 /\\ c1 <= 256 /\\ aligned 16 sp /\\
        nonoverlapping (r0,1024) (word pc,libmldsa_size) /\\
        nonoverlapping (r1,1024) (word pc,libmldsa_size) /\\
        nonoverlapping (r0,1024) (r1,1024) /\\
        nonoverlapping (r0,1024) (word_add sp (word 48),48) /\\
        nonoverlapping (r1,1024) (word_add sp (word 48),48) /\\
        nonoverlapping (r0,1024) (word_add sp (word 1280),%d) /\\
        nonoverlapping (r1,1024) (word_add sp (word 1280),%d)
        ==> ensures arm
             (\\s. aligned_bytes_loaded s (word pc) %s /\\
                  read PC s = word (pc + %d) /\\ read SP s = sp /\\
                  read X8 s = %s /\\ read X21 s = word %d /\\
                  read X28 s = word_add sp (word %d) /\\
                  read %s s = word c0 /\\ read %s s = word c1 /\\
                  read (memory :> bytes64 (word_add sp (word 88))) s = r0 /\\
                  read (memory :> bytes64 (word_add sp (word 48))) s = r1 /\\
                  read (memory :> bytes64 (word_add sp (word 56))) s = r2 /\\
                  read (memory :> bytes64 (word_add sp (word 64))) s = r3 /\\
                  read (memory :> bytes32 (word_add sp (word 84))) s = %s /\\
                  read (memory :> bytes32 (word_add sp (word 80))) s = fl2 /\\
                  (!j. j < 136
                       ==> read (memory :> bytes8 (word_add sp (word (1280 + j)))) s = b0 j) /\\
                  (!j. j < 136
                       ==> read (memory :> bytes8 (word_add sp (word (%d + j)))) s = b1 j) /\\
                  (!k. k < c0
                       ==> read (memory :> bytes32 (word_add r0 (word (4 * k)))) s = f0 k) /\\
                  (!k. k < c1
                       ==> read (memory :> bytes32 (word_add r1 (word (4 * k)))) s = f1 k) /\\
                  read events s = e)
             (\\s. read PC s = word (pc + %d) /\\
                  read %s s = word (%s) /\\ read %s s = word (%s) /\\
                  read X13 s = r2 /\\ read X12 s = r3 /\\ read X15 s = word_zx fl2 /\\
                  %s <= 256 /\\ %s <= 256 /\\ %s /\\ %s /\\
                  (exists e2.
                     read events s = APPEND e2 e /\\
                     e2 = f_events r0 r1 sp c0 c1
                            (mld_rej_eta_declass %d 256 c0 b0 136)
                            (mld_rej_eta_declass %d 256 c1 b1 136) pc /\\
                     memaccess_inbounds e2
                      [r0,1024; r1,1024; word_add sp (word 48),48;
                       word_add sp (word 1280),%d] [r0,1024; r1,1024]))
             (MAYCHANGE [PC; %s; X8; X9; X10; X11; X12; X13; X14; X15; X16; %s; %s] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(r0,1024); memory :> bytes(r1,1024)])"
   g.gblen g.gblen ETA_MC ent (ETA_FLAG 0) g.gk g.gb1 p0.ectr p1.ectr (ETA_FLAG 1) g.gb1
   ext p0.ectr (ctr 0) p1.ectr (ctr 1) (ctr 0) (ctr 1) (coef 0) (coef 1) g.geta g.geta
   g.gblen g.gkeep0 p0.ectr p1.ectr);;

let ETA_GS01_TM = ETA_GS01_GEN_TM ETA2_GS;;

let ETA_GS01_TEMPLATE =
 `\(r0:int64) (r1:int64) (sp:int64) (c0:num) (c1:num) (DC0:bool list) (DC1:bool list) (pc:num).
    if c0 < 256
    then if c1 < 256 then f_ev_tt r0 r1 sp c0 c1 DC0 DC1 pc
         else f_ev_tf r0 r1 sp c0 c1 DC0 DC1 pc
    else if c1 < 256 then f_ev_ft r0 r1 sp c0 c1 DC0 DC1 pc
         else f_ev_ff r0 r1 sp c0 c1 DC0 DC1 pc:(uarch_event)list`;;

let ETA_GS01_GEN_PROVE g execth ent ext p0 p1 scan0 scan1 =
  let eta = mk_small_numeral g.geta in
  let dc k = list_mk_comb(`mld_rej_eta_declass`,
    [eta; `256`; mk_var("c"^string_of_int k,`:num`); mk_var("b"^string_of_int k,`:num->byte`); `136`])
  and ct k = list_mk_comb(`mld_rej_eta_ctr`,
    [eta; `256`; mk_var("c"^string_of_int k,`:num`); mk_var("b"^string_of_int k,`:num->byte`); `136`]) in
  let rd r = mk_comb(mk_comb(`read:(armstate,int64)component->armstate->int64`,mk_const(r,[])),`s:armstate`) in
  let dv k = mk_var("DC"^string_of_int k,`:bool list`) in
  let allowed = [`r0:int64`; `r1:int64`; `sp:int64`; `c0:num`; `c1:num`;
                 `DC0:bool list`; `DC1:bool list`; `pc:num`] in
  let calls = [ETA_PCW p0.eh, ("H_SCAN0",[`r0:int64`; `sp:int64`; `c0:num`; `f0:num->int32`; `b0:num->byte`; rd g.gkeep0; `pc:num`]);
               ETA_PCW p1.eh, ("H_SCAN1",[`r1:int64`; `sp:int64`; `c1:num`; `f1:num->int32`; `b1:num->byte`; rd g.gkeep1; `pc:num`])] in
  let full k = TRY(SUBGOAL_THEN (mk_eq(ct k,mk_var("c"^string_of_int k,`:num`))) SUBST1_TAC THENL
                    [MATCH_MP_TAC ETA_CTR_FULL THEN SIMPLE_ARITH_TAC; ALL_TAC]) in
  let run =
    FULL_INIT_TAC THEN
    W(fun (asl,_) ->
      let cs = filter (fun th -> mem (concl th)
                 [`c0 < 256`; `~(c0 < 256)`; `c1 < 256`; `~(c1 < 256)`]) (map snd asl) in
      RULE_ASSUM_TAC(fun th -> if mem th cs then th else REWRITE_RULE cs th)) THEN
    ETA_RUN_CALLS_TAC execth calls [ETA_PCW ext] allowed 1 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME(mk_eq(dc 0,dv 0)); ASSUME(mk_eq(dc 1,dv 1))]) THEN
    full 0 THEN full 1 THEN ETA_GS_FINAL_TAC in
  prove(ETA_GS01_GEN_TM g ent ext p0 p1,
  ASSUME_CALLEE_SAFETY_TAILED_TAC scan0 "H_SCAN0" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC scan1 "H_SCAN1" THEN
  CONCRETIZE_F_EVENTS_TAC ETA_GS01_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `r0:int64`; `r1:int64`; `sp:int64`;
     `c0:num`; `c1:num`; `f0:num->int32`; `f1:num->int32`; `b0:num->byte`;
     `b1:num->byte`; `r2:int64`; `r3:int64`; `fl2:int32`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS; fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ABBREV_TAC(mk_eq(dv 0,dc 0)) THEN ABBREV_TAC(mk_eq(dv 1,dc 1)) THEN
  ASM_CASES_TAC `c0 < 256` THEN ASM_CASES_TAC `c1 < 256` THEN run);;

let ETA_GS01_PROVE = ETA_GS01_GEN_PROVE ETA2_GS;;

(* ------------------------------------------------------------------------- *)
(* The instances for the code of mldsa44 and mldsa87 (eta = 2, the same      *)
(* code at the function offset b): the four scans of the first block, the    *)
(* four of the loop, the guarded scans, the tests and the absorbing.         *)
(* ------------------------------------------------------------------------- *)

let ETA2_SCANS b =
  let sb ch ctr flag ptr h x buf disp =
    { eh = b + h; ex = b + x; eb = buf; el = 136; eeta = 2; ectr = ctr;
      eflag = Some flag; eptr = Some ptr;
      eregs = "read X9 s = word_add sp (word 1280) /\\ read X10 s = word 205";
      ech = ch; esplit = false; edisp = disp; ekeep = "" } in
  let oc (base,boff) ctr ptr h x split keep =
    { eh = b + h; ex = b + x; eb = boff; el = 136; eeta = 2; ectr = ctr;
      eflag = None; eptr = Some ptr;
      eregs = Printf.sprintf "read %s s = word_add sp (word %d) /\\ read X21 s = word 205" base boff;
      ech = ["X9"; "X10"; "X11"]; esplit = split; edisp = 0; ekeep = keep } in
  [{ eh = b + 0x3bc; ex = b + 0x454; eb = 1280; el = 136; eeta = 2;
     ectr = "X26"; eflag = Some "X2"; eptr = None;
     eregs = "read SP s = sp /\\ read X9 s = word_add sp (word 1280) /\\ read X10 s = word 205";
     ech = ["X11"; "X12"; "X13"; "X14"]; esplit = false; edisp = 0; ekeep = "" };
   sb ["X11";"X12";"X13"] "X25" "X1" "X16" 0x46c 0x4f0 1440 160;
   sb ["X11";"X12";"X13"] "X24" "X16" "X15" 0x500 0x584 1600 320;
   sb ["X12";"X13"] "X19" "X11" "X14" 0x594 0x618 1760 480],
  [oc ("X16",1280) "X26" "X15" 0x748 0x7c0 false
      "read X1 s = x1";
   oc ("X28",1440) "X25" "X14" 0x7cc 0x85c true
      "read X15 s = x1";
   oc ("X23",1600) "X24" "X13" 0x864 0x8dc false "";
   oc ("X0",1760) "X19" "X12" 0x8e8 0x960 false ""];;

type etalem =
  { labs : thm; lscan : thm list; loscan : thm list; lgs01 : thm; lgs2 : thm;
    lgs3 : thm; lt0 : thm; lt1 : thm };;

let ETA_TIMED name f =
  let t0 = Unix.gettimeofday() in
  let th = f () in
  Printf.printf "ETA_TIME %s %.1f\n%!" name (Unix.gettimeofday() -. t0); th;;

let ETA2_GS2_FLAG = "read X15 s = (if c < 256 then word 1 else word 0)";;
let ETA2_GS3_FLAG =
  "read SP s = sp /\\ read (memory :> bytes32 (word_add sp (word 76))) s = (if c < 256 then word 1 else word 0)";;

let ETA2_PROVE_ALL execth b =
  let ss,os = ETA2_SCANS b in
  let abs = ETA_TIMED "ABS" (fun () -> ETA_ABS_PROVE execth (b + 0xbc) (b + 0x290) 117) in
  let sc = map (fun (k,p) -> ETA_TIMED ("S"^string_of_int k) (fun () -> ESCAN_PROVE execth p))
               (zip (0--3) ss) in
  let oc = map (fun (k,p) -> ETA_TIMED ("O"^string_of_int k) (fun () -> ESCAN_PROVE execth p))
               (zip (0--3) os) in
  let g01 = ETA_TIMED "GS01" (fun () ->
    ETA_GS01_PROVE execth (b + 0x72c) (b + 0x85c) (el 0 os) (el 1 os) (el 0 oc) (el 1 oc)) in
  let g2 = ETA_TIMED "GS2" (fun () ->
    ETA_GS1_PROVE execth (b + 0x85c) (b + 0x8dc) ETA2_GS2_FLAG (el 2 os) "" "" [] (el 2 oc)) in
  let g3 = ETA_TIMED "GS3" (fun () ->
    ETA_GS1_PROVE execth (b + 0x8dc) (b + 0x960) ETA2_GS3_FLAG (el 3 os)
      " /\\ nonoverlapping (a,1024) (word_add sp (word 76),4)" "; word_add sp (word 76),4" []
      (el 3 oc)) in
  let t0 = ETA_TIMED "T0" (fun () ->
    ETA_TST_PROVE execth (b + 0x618) ["X26";"X25";"X24";"X19"] [] (b + 0x638) (b + 0x99c)) in
  let t1 = ETA_TIMED "T1" (fun () ->
    ETA_TST_PROVE execth (b + 0x960) ["X26";"X25";"X24";"X19"]
      ["X1",1; "X16",2; "X11",3; "X2",0] (b + 0x644) (b + 0x99c)) in
  { labs = abs; lscan = sc; loscan = oc; lgs01 = g01; lgs2 = g2; lgs3 = g3;
    lt0 = t0; lt1 = t1 };;

(*** The same statements as mk_thm stubs, for developing the main proof ***)

let ETA2_STUB_ALL b =
  let ss,os = ETA2_SCANS b in
  let st tm = mk_thm([],tm) in
  { labs = st(ETA_ABS_TM (b + 0xbc) (b + 0x290));
    lscan = map (st o ESCAN_TM) ss; loscan = map (st o ESCAN_TM) os;
    lgs01 = st(ETA_GS01_TM (b + 0x72c) (b + 0x85c) (el 0 os) (el 1 os));
    lgs2 = st(ETA_GS1_TM (b + 0x85c) (b + 0x8dc) ETA2_GS2_FLAG (el 2 os) "" "" []);
    lgs3 = st(ETA_GS1_TM (b + 0x8dc) (b + 0x960) ETA2_GS3_FLAG (el 3 os)
               " /\\ nonoverlapping (a,1024) (word_add sp (word 76),4)" "; word_add sp (word 76),4" []);
    lt0 = st(ETA_TST_TM (b + 0x618) ["X26";"X25";"X24";"X19"] [] (b + 0x638) (b + 0x99c));
    lt1 = st(ETA_TST_TM (b + 0x960) ["X26";"X25";"X24";"X19"]
               ["X1",1; "X16",2; "X11",3; "X2",0] (b + 0x644) (b + 0x99c)) };;

let ETA_SQ1 = prove(`!S:1600 word. keccak_f1600 S = keccak_squeeze 1 S`,
  REWRITE_TAC[keccak_squeeze; ARITH_RULE `1 = SUC 0`] THEN REWRITE_TAC[keccak_squeeze]);;

(*** The bytes of a block copied to a buffer as bytes of the stream ***)

let ETA_BUF_BYTES = prove
 (`!(S:1600 word) t (a:int64) (s:armstate).
     read (memory :> bytes(a,136)) s = val(keccak_squeeze (t + 1) S) MOD 2 EXP (8 * 136)
     ==> !j. j < 136
             ==> read (memory :> bytes8 (word_add a (word j))) s =
                 mld_keccak_squeeze_byte 136 S 136 (136 * t + j)`,
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP MLD_READ_BYTES_BYTES8) THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[mld_keccak_squeeze_byte] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `(136 + 136 * t + j) DIV 136 = t + 1 /\ (136 + 136 * t + j) MOD 136 = j`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `j:num` THEN ASM_ARITH_TAC;
      MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `t + 1` THEN ASM_ARITH_TAC]; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_SUBWORD; DIMINDEX_8] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  REWRITE_TAC[ARITH_RULE `MIN 8 8 = 8`; ARITH_RULE `256 = 2 EXP 8`; MOD_MOD_REFL] THEN
  SUBGOAL_THEN `2 EXP (8 * 136) = 2 EXP (8 * j) * 2 EXP (8 * 136 - 8 * j)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM DIV_MOD; MOD_MOD_EXP_MIN] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(*** Two blocks copied to one buffer (the first pass of mldsa65) ***)

let ETA_BUF2_BYTES = prove
 (`!(S:1600 word) (a:int64) off (s:armstate).
     read (memory :> bytes(word_add a (word off),136)) s =
       val(keccak_squeeze 1 S) MOD 2 EXP (8 * 136) /\
     read (memory :> bytes(word_add a (word (off + 136)),136)) s =
       val(keccak_squeeze 2 S) MOD 2 EXP (8 * 136)
     ==> !j. j < 272
             ==> read (memory :> bytes8 (word_add a (word (off + j)))) s =
                 mld_keccak_squeeze_byte 136 S 136 j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `j < 136` THENL
   [MP_TAC(SPECL [`S:1600 word`; `0`; `word_add a (word off):int64`; `s:armstate`]
      ETA_BUF_BYTES) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
    DISCH_THEN(MP_TAC o SPEC `j:num`) THEN
    ASM_REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD];
    MP_TAC(SPECL [`S:1600 word`; `1`; `word_add a (word (off + 136)):int64`; `s:armstate`]
      ETA_BUF_BYTES) THEN
    REWRITE_TAC[ARITH_RULE `1 + 1 = 2`] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `j - 136`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    SUBGOAL_THEN `(off + 136) + (j - 136) = off + j /\ 136 * 1 + (j - 136) = j`
     (fun th -> REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The instances for the code of mldsa65 (eta = 4, at the function offset b). *)
(* The first pass squeezes two blocks into each buffer (272 bytes at sp +     *)
(* 1280 + 288 k), and its scans compare the byte itself for the high nibble. *)
(* ------------------------------------------------------------------------- *)

let ETA4_SCANS b =
  let sb ch ctr flag ptr h x buf disp =
    { eh = b + h; ex = b + x; eb = buf; el = 272; eeta = 4; ectr = ctr;
      eflag = Some flag; eptr = Some ptr;
      eregs = "read X9 s = word_add sp (word 1280) /\\ read X10 s = word 4";
      ech = ch; esplit = false; edisp = disp; ekeep = "" } in
  let oc (base,boff) ctr ptr h x split keep =
    { eh = b + h; ex = b + x; eb = boff; el = 136; eeta = 4; ectr = ctr;
      eflag = None; eptr = Some ptr;
      eregs = Printf.sprintf "read %s s = word_add sp (word %d) /\\ read X21 s = word 4" base boff;
      ech = ["X9"; "X10"; "X11"]; esplit = split; edisp = 0; ekeep = keep } in
  [{ eh = b + 0x4a0; ex = b + 0x514; eb = 1280; el = 272; eeta = 4;
     ectr = "X23"; eflag = Some "X18"; eptr = None;
     eregs = "read SP s = sp /\\ read X25 s = word_add sp (word 1280) /\\ read X9 s = word 4";
     ech = ["X10"; "X11"; "X12"; "X13"]; esplit = false; edisp = 0; ekeep = "" };
   sb ["X11";"X12";"X13"] "X25" "X17" "X16" 0x52c 0x590 1568 288;
   sb ["X11";"X12";"X13"] "X24" "X16" "X15" 0x5a0 0x604 1856 576;
   sb ["X12";"X13"] "X19" "X11" "X14" 0x614 0x678 2144 864],
  [oc ("X16",1280) "X23" "X15" 0x7a8 0x800 false "read X17 s = x1";
   oc ("X28",1568) "X25" "X14" 0x80c 0x87c true "read X15 s = x1";
   oc ("X27",1856) "X24" "X13" 0x884 0x8dc false "";
   oc ("X26",2144) "X19" "X12" 0x8e8 0x940 false ""];;

let ETA4_ABS =
  { aregs = "read X19 s = word_add sp (word 96) /\\ read X24 s = word_add sp (word 696) /\\ " ^
            "read X25 s = word_add sp (word 1280)";
    apost = "read X19 s = word_add sp (word 96) /\\ read X24 s = word_add sp (word 696) /\\ " ^
            "read X25 s = word_add sp (word 1280) /\\ read X26 s = word_add sp (word 2144) /\\ " ^
            "read X27 s = word_add sp (word 1856) /\\ read X28 s = word_add sp (word 1568)";
    ach = "PC; X0; X8; X9; X10; X26; X27; X28" };;

let ETA4_GS = { geta = 4; gk = 4; gb1 = 1568; gblen = 424; gkeep0 = "X17"; gkeep1 = "X15" };;

let ETA4_TSTS b =
  (b + 0x678, ["X23";"X25";"X24";"X19"], [], b + 0x698, b + 0x97c),
  (b + 0x940, ["X23";"X25";"X24";"X19"], ["X17",1; "X16",2; "X11",3; "X18",0],
   b + 0x6a0, b + 0x97c);;

let ETA4_PROVE_ALL execth b =
  let ss,os = ETA4_SCANS b in
  let (e0,c0,s0,k0,x0),(e1,c1,s1,k1,x1) = ETA4_TSTS b in
  let abs = ETA_TIMED "ABS" (fun () -> ETA_ABS_GEN_PROVE ETA4_ABS execth (b + 0xc0) (b + 0x29c) 119) in
  let sc = map (fun (k,p) -> ETA_TIMED ("S"^string_of_int k) (fun () -> ESCAN_PROVE execth p))
               (zip (0--3) ss) in
  let oc = map (fun (k,p) -> ETA_TIMED ("O"^string_of_int k) (fun () -> ESCAN_PROVE execth p))
               (zip (0--3) os) in
  let g01 = ETA_TIMED "GS01" (fun () ->
    ETA_GS01_GEN_PROVE ETA4_GS execth (b + 0x78c) (b + 0x87c) (el 0 os) (el 1 os) (el 0 oc) (el 1 oc)) in
  let g2 = ETA_TIMED "GS2" (fun () ->
    ETA_GS1_PROVE execth (b + 0x87c) (b + 0x8dc) ETA2_GS2_FLAG (el 2 os) "" "" [] (el 2 oc)) in
  let g3 = ETA_TIMED "GS3" (fun () ->
    ETA_GS1_PROVE execth (b + 0x8dc) (b + 0x940) ETA2_GS3_FLAG (el 3 os)
      " /\\ nonoverlapping (a,1024) (word_add sp (word 76),4)" "; word_add sp (word 76),4" []
      (el 3 oc)) in
  let t0 = ETA_TIMED "T0" (fun () -> ETA_TST_PROVE execth e0 c0 s0 k0 x0) in
  let t1 = ETA_TIMED "T1" (fun () -> ETA_TST_PROVE execth e1 c1 s1 k1 x1) in
  { labs = abs; lscan = sc; loscan = oc; lgs01 = g01; lgs2 = g2; lgs3 = g3;
    lt0 = t0; lt1 = t1 };;

let ETA4_STUB_ALL b =
  let ss,os = ETA4_SCANS b in
  let (e0,c0,s0,k0,x0),(e1,c1,s1,k1,x1) = ETA4_TSTS b in
  let st tm = mk_thm([],tm) in
  { labs = st(ETA_ABS_GEN_TM ETA4_ABS (b + 0xc0) (b + 0x29c));
    lscan = map (st o ESCAN_TM) ss; loscan = map (st o ESCAN_TM) os;
    lgs01 = st(ETA_GS01_GEN_TM ETA4_GS (b + 0x78c) (b + 0x87c) (el 0 os) (el 1 os));
    lgs2 = st(ETA_GS1_TM (b + 0x87c) (b + 0x8dc) ETA2_GS2_FLAG (el 2 os) "" "" []);
    lgs3 = st(ETA_GS1_TM (b + 0x8dc) (b + 0x940) ETA2_GS3_FLAG (el 3 os)
               " /\\ nonoverlapping (a,1024) (word_add sp (word 76),4)" "; word_add sp (word 76),4" []);
    lt0 = st(ETA_TST_TM e0 c0 s0 k0 x0); lt1 = st(ETA_TST_TM e1 c1 s1 k1 x1) };;

(* ------------------------------------------------------------------------- *)
(* The parameters of the main lemma of inline_eta4x_main.ml for each code:    *)
(* eta, the bytes of each buffer in the first pass, the counter and flag      *)
(* registers of the four polynomials, the stride of the buffers (buffer k at  *)
(* fr + 1520 + stride * k), the frame (fr, frlen) with the canary at fr +      *)
(* canary, the frame facts, the extra facts at the first test and in the      *)
(* loop, the offsets of the first test, the loop head, the exit and the end,  *)
(* the steps from the first test to the loop head, the steps of the body      *)
(* (the four calls of permute, the end of the copy, GS01, GS2, GS3, T1), the  *)
(* stack of the function and the last step of its epilogue.                   *)
(* ------------------------------------------------------------------------- *)

type empar =
  { m_eta : int; m_first : int; m_ctrs : term list; m_flags : term list;
    m_bstride : int; m_frlen : int; m_canary : int; m_frame : term;
    m_a1 : term list; m_inv : term list;
    m_pt0 : int; m_ploop : int; m_pexit : int; m_pend : int;
    m_init : int list; m_body : int list; m_stack : int; m_nend : int };;

let ETA2_MAIN_PAR =
  { m_eta = 2; m_first = 136; m_ctrs = [`X26`; `X25`; `X24`; `X19`];
    m_flags = [`X2`; `X1`; `X16`; `X11`]; m_bstride = 160; m_frlen = 2192; m_canary = 2184;
    m_frame =
     `read SP s = word_add fr (word 240) /\ read X29 s = fp /\
      read (memory :> bytes64 (word_add fr (word 328))) s = r0 /\
      read (memory :> bytes64 (word_add fr (word 288))) s = r1 /\
      read (memory :> bytes64 (word_add fr (word 296))) s = r2 /\
      read (memory :> bytes64 (word_add fr (word 304))) s = r3 /\
      read (memory :> bytes64 (word_add fr (word 264))) s = word_add fr (word 736) /\
      read (memory :> bytes64 (word_add fr (word 272))) s = word_add fr (word 536) /\
      read (memory :> bytes64 (word_add fr (word 280))) s = word_add fr (word 936) /\
      read (memory :> bytes64 (word_add fr (word 2184))) s = canary /\
      read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard))) s = guard /\
      read (memory :> bytes64 guard) s = canary /\
      read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\
      read (memory :> bytes(ea,el)) s = ev /\
      read X28 s = word_add fr (word 1680) /\ read X23 s = word_add fr (word 1840)`;
    m_a1 = [`read X0 s = word_add fr (word 2000)`];
    m_inv = [`read X27 s = word_add fr (word 736)`; `read X21 s = word 205`;
             `read (memory :> bytes64 (word_add fr (word 256))) s = word_add fr (word 2000)`];
    m_pt0 = 0x618; m_ploop = 0x644; m_pexit = 0x99c; m_pend = 0xa1c;
    m_init = [2; 3; 4]; m_body = [4; 8; 11; 15; 62; 63; 64; 65; 66];
    m_stack = 2336; m_nend = 41 };;

let ETA4_MAIN_PAR =
  { m_eta = 4; m_first = 272; m_ctrs = [`X23`; `X25`; `X24`; `X19`];
    m_flags = [`X18`; `X17`; `X16`; `X11`]; m_bstride = 288; m_frlen = 2704; m_canary = 2696;
    m_frame =
     `read SP s = word_add fr (word 240) /\ read X29 s = fp /\
      read (memory :> bytes64 (word_add fr (word 328))) s = r0 /\
      read (memory :> bytes64 (word_add fr (word 288))) s = r1 /\
      read (memory :> bytes64 (word_add fr (word 296))) s = r2 /\
      read (memory :> bytes64 (word_add fr (word 304))) s = r3 /\
      read (memory :> bytes64 (word_add fr (word 264))) s = word_add fr (word 736) /\
      read (memory :> bytes64 (word_add fr (word 272))) s = word_add fr (word 536) /\
      read (memory :> bytes64 (word_add fr (word 280))) s = word_add fr (word 936) /\
      read (memory :> bytes64 (word_add fr (word 2696))) s = canary /\
      read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard))) s = guard /\
      read (memory :> bytes64 guard) s = canary /\
      read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\
      read (memory :> bytes(ea,el)) s = ev /\
      read X28 s = word_add fr (word 1808) /\ read X27 s = word_add fr (word 2096) /\
      read X26 s = word_add fr (word 2384)`;
    m_a1 = [];
    m_inv = [`read X21 s = word 4`;
             `read (memory :> bytes64 (word_add fr (word 256))) s = word_add fr (word 2384)`];
    m_pt0 = 0x678; m_ploop = 0x6a0; m_pexit = 0x97c; m_pend = 0x9fc;
    m_init = [2; 3]; m_body = [4; 8; 12; 16; 63; 64; 65; 66; 67];
    m_stack = 2848; m_nend = 43 };;
