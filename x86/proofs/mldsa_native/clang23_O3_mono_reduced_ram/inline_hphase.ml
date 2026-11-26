(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The absorbs of the second and third inputs of mld_H44, mld_H65 and        *)
(* mld_H87 of the clang 23 -O3 build, as lemmas with the pre and post of the *)
(* gcc mldsa_shake256_absorb spec (the state becomes FST(mld_keccak_absorb   *)
(* 136 S p len M) and the position SND(..)), built from the region lemmas of *)
(* inline_hxor.ml:                                                           *)
(*  - HXB_PROVE: the loop over the 136-byte blocks (fill region, call of     *)
(*    mldsa_keccakf1600_permute), as the loop of the gcc shake256_absorb     *)
(*    proof; checked on the second absorb of mld_H44.                        *)
(*  - HXP_STMT / HXP_TAC: a whole absorb (nothing, tail only, or blocks and  *)
(*    the rest). WORK IN PROGRESS: not yet proved for any instance.          *)
(* The frame: the state at bq + 296 + so (so = 16 for mld_H44/65, 0 for      *)
(* mld_H87), the permutation below bq + 296, writable (bq,296) and the state *)
(* with the position (bq + 296 + so,204) only, so that the saved out pointer *)
(* and registers and the stack arguments survive.                            *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_hxor.ml";;

(* ------------------------------------------------------------------------- *)
(* The loop over the blocks of an absorb at position p (from its head, where *)
(* R15 = p and RAX = 136 - p, to its exit): each iteration XORs the next     *)
(* 136 - p (first) or 136 bytes into the state with the fill region, calls   *)
(* mldsa_keccakf1600_permute, and continues if 136 bytes or more are left.   *)
(* As the loop of shake256_absorb of the gcc12_O2_reduced_ram build.         *)
(* ------------------------------------------------------------------------- *)

type hx_blk =
 { bk_fn : string; bk_head : int; bk_fill : int; bk_exit : int; bk_so : int; bk_fr : int;
   bk_len : string; bk_dat : string; bk_st : string; bk_keep : (string * string) list;
   bk_call : int };;

let bk_tok b s = subst_tokens
  ["@KEEP@",String.concat "" (map (fun (r,v) -> Printf.sprintf "read %s s = %s /\\ " r v) b.bk_keep);
   "@HEAD@",string_of_int (layout b.bk_fn + b.bk_head); "@EXIT@",string_of_int (layout b.bk_fn + b.bk_exit);
   "@SA@",string_of_int (296 + b.bk_so); "@FR@",string_of_int b.bk_fr;
   "@LEN@",b.bk_len; "@DAT@",b.bk_dat; "@ST@",b.bk_st] s;;

let HXB_STMT b = parse_term(bk_tok b
 "exists f_events. forall e bq p m len M (S:1600 word) pc.
   p < 136 /\\ 136 <= p + len /\\
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   nonoverlapping (m,len) (bq,@FR@) /\\ nonoverlapping (word pc,libmldsa_size) (bq,@FR@)
   ==> ensures x86
    (\\s. bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
         read RIP s = word (pc + @HEAD@) /\\ read RSP s = word_add bq (word 296) /\\
         read R15 s = word p /\\ read RAX s = word (136 - p) /\\
         read @LEN@ s = word len /\\ read @DAT@ s = m /\\
         read @ST@ s = word_add bq (word @SA@) /\\ @KEEP@
         read (memory :> bytes(m,len)) s = M /\\
         read (memory :> wbytes (word_add bq (word @SA@))) s = S /\\
         read events s = e)
    (\\s. read RIP s = word (pc + @EXIT@) /\\ read RSP s = word_add bq (word 296) /\\
         read @ST@ s = word_add bq (word @SA@) /\\ @KEEP@
         read @LEN@ s = word (len - (136 * ((p + len) DIV 136) - p)) /\\
         read @DAT@ s = word_add m (word (136 * ((p + len) DIV 136) - p)) /\\
         read (memory :> bytes(m,len)) s = M /\\
         read (memory :> wbytes (word_add bq (word @SA@))) s =
           mld_keccak_absorb_blocks 136 S (2 EXP (8 * p) * M) ((p + len) DIV 136) /\\
         (exists e2. read events s = APPEND e2 e /\\ e2 = f_events bq p m len pc /\\
            memaccess_inbounds e2 [m,len; bq,@FR@; word(pc + rodata_mld_KeccakF_RoundConstants),192]
                                  [bq,@FR@]))
    (MAYCHANGE [RIP; RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [R15; @LEN@; @DAT@] ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(bq,296); memory :> bytes(word_add bq (word @SA@),200)])");;

let HXB_INV b = parse_term(bk_tok b
 "\\k s. read RSP s = word_add bq (word 296) /\\
        read @ST@ s = word_add bq (word @SA@) /\\ @KEEP@
        read @LEN@ s = word(len - (if k = 0 then 0 else 136 * k - p)) /\\
        read @DAT@ s = word_add m (word(if k = 0 then 0 else 136 * k - p)) /\\
        read R15 s = word(if k = 0 then p else 0) /\\
        read RAX s = word(136 - (if k = 0 then p else 0)) /\\
        read (memory :> bytes(m,len)) s = M /\\
        read (memory :> wbytes (word_add bq (word @SA@))) s =
          mld_keccak_absorb_blocks 136 S (2 EXP (8 * p) * M) k");;

(* The 32-bit forms of a position p < 136 (mov esi, r15d; sub eax, r15d) *)
let HX_P32 = HX_RCASES 136
 `word_zx (word r:int64):int32 = word r /\ word_zx (word r:int32):int64 = word r /\
  word_sub (word 136:int32) (word r) = word (136 - r) /\
  word_zx (word (136 - r):int32):int64 = word (136 - r) /\
  val(word r:int32) = r /\ val(word (136 - r):int64) = 136 - r /\
  (val(word_sub (word r:int32) (word 136)) = 0 <=> F) /\
  (word r:int32 = word 136 <=> F)`;;

let hx_p32 p = CONJUNCTS(MP (SPEC p HX_P32) (ASSUME (mk_binop `(<):num->num->bool` p `136`)));;

let HXB_WORD_ADD_8 = WORD_RULE `word_add (word_sub (x:int64) (word 8)) (word 8) = x`;;

let HX_VAL135 = prove(`val(word 135:int64) = 135`, CONV_TAC WORD_REDUCE_CONV);;

let HXB_BODY_TAC b exec extra ntail =
  let sat = mk_small_numeral (296 + b.bk_so) in
  let st = mk_comb(`word_add (bq:int64)`,mk_comb(`word:num->int64`,sat)) in
  let vars = [`bq:int64`; `p:num`; `m:int64`; `len:num`; `pc:num`; `i:num`; `n:num`; `pp:num`; `c:num`; `e2:(uarch_event)list`] in
  let blk = `(2 EXP (8 * p) * M) DIV 2 EXP (8 * 136 * i) MOD 2 EXP (8 * 136)` in
  let X = `mld_keccak_absorb_blocks 136 S (2 EXP (8 * p) * M) i` in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `136 * (i + 1) <= p + len` ASSUME_TAC THENL
   [TRANS_TAC LE_TRANS `136 * n` THEN CONJ_TAC THENL
     [REWRITE_TAC[LE_MULT_LCANCEL] THEN UNDISCH_TAC `i < n` THEN ARITH_TAC;
      EXPAND_TAC "n" THEN REWRITE_TAC[DIV_MUL_LE]];
    ALL_TAC] THEN
  ABBREV_TAC `pp = if i = 0 then p else 0` THEN
  ABBREV_TAC `c = if i = 0 then 0 else 136 * i - p` THEN
  SUBGOAL_THEN
   `pp < 136 /\ c + (136 - pp) = 136 * (i + 1) - p /\
    c + (136 - pp) <= len /\
    (if i + 1 = 0 then 0 else 136 * (i + 1) - p) = c + (136 - pp) /\
    (if i + 1 = 0 then p else 0) = 0`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["pp"; "c"] THEN
    REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
    UNDISCH_TAC `136 * (i + 1) <= p + len` THEN UNDISCH_TAC `p < 136` THEN
    COND_CASES_TAC THENL
     [ASM_REWRITE_TAC[] THEN ARITH_TAC;
      SUBGOAL_THEN `136 <= 136 * i` MP_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `136 = 136 * 1`] THEN
        REWRITE_TAC[LE_MULT_LCANCEL] THEN UNDISCH_TAC `~(i = 0)` THEN ARITH_TAC;
        ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `0 < 136 - pp /\ pp + (136 - pp) <= 136` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pp < 136` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (subst [st,`st:int64`] `nonoverlapping_modulo (2 EXP 64) (val (word_add (m:int64) (word c)),136 - pp) (val (st:int64),200)`) ASSUME_TAC THENL
   [MATCH_MP_TAC SPONGE_NOV_SUB2 THEN MAP_EVERY EXISTS_TAC [`len:num`; mk_small_numeral b.bk_fr] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  FULL_INIT_TAC THEN
  HX_DRIVE_TAC exec ([MATCH_MP TG_VALR (ASSUME `pp < 136`)] @ extra) (layout b.bk_fn + b.bk_fill) THEN
  HX_RESTATE_TAC `RCX` (mk_comb(mk_comb(`word_add:int64->int64->int64`,st),`word pp:int64`)) HX_ADDR_EQ_TAC THEN
  W(fun (asl,w) -> let s = hx_cur_state asl in
    SUBGOAL_THEN (subst [s,`s:x86state`]
      `read (memory :> bytes(word_add m (word c),136 - pp)) s = (M DIV 2 EXP (8 * c)) MOD 2 EXP (8 * (136 - pp))`)
      ASSUME_TAC THENL
     [MATCH_MP_TAC READ_MEMORY_BYTES_SUB THEN EXISTS_TAC `len:num` THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  HX_LCALL_TAC exec "H_FILL"
    [st; `pp:num`; `word_add m (word c):int64`; `136 - pp`;
     `(M DIV 2 EXP (8 * c)) MOD 2 EXP (8 * (136 - pp))`; X; `pc:num`] vars THEN
  SUBGOAL_THEN (mk_eq(`2 EXP (8 * pp) * (M DIV 2 EXP (8 * c)) MOD 2 EXP (8 * (136 - pp))`,blk))
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[SYM(ASSUME `(if i = 0 then p else 0) = pp`); SYM(ASSUME `(if i = 0 then 0 else 136 * i - p) = c`)] THEN
    MATCH_MP_TAC HX_ABSORB_CHUNK THEN
    UNDISCH_TAC `p < 136` THEN ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  HX_DRIVE_TAC exec [] (layout "mldsa_keccakf1600_permute") THEN
  KECCAK_STATE_WBYTES_TAC (mk_binop `word_xor:1600 word->1600 word->1600 word` X (mk_comb(`word:num->1600 word`,blk))) THEN
  HX_LCALL_TAC exec "H_PERM"
    [`read RDI s`; mk_binop `word_xor:1600 word->1600 word->1600 word` X (mk_comb(`word:num->1600 word`,blk));
     `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] vars THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HXB_WORD_ADD_8]) THEN
  SUBGOAL_THEN `word_sub (word (len - c)) (word (136 - pp)):int64 = word(len - (136 * (i + 1) - p))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `c + (136 - pp) = 136 * (i + 1) - p`)] THEN
    REWRITE_TAC[ARITH_RULE `len - (c + d) = len - c - d`] THEN
    REWRITE_TAC[WORD_SUB] THEN
    SUBGOAL_THEN `136 - pp <= len - c` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `c + (136 - pp) <= len` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word (len - (136 * (i + 1) - p)):int64) = len - (136 * (i + 1) - p)` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC (parse_term(Printf.sprintf "%d + len <= 2 EXP 64" b.bk_fr)) THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `len:num`; `i:num`] HX_ABSORB_LOOP_TEST) THEN
  ANTS_TAC THENL [UNDISCH_TAC `p < 136` THEN UNDISCH_TAC `136 * (i + 1) <= p + len` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  W(fun (asl,w) -> let k = hx_state_num asl in X86_STEPS_TAC exec ((k+1)--(k+ntail))) THEN
  HX_RES [ASSUME `word_sub (word (len - c)) (word (136 - pp)):int64 = word(len - (136 * (i + 1) - p))`;
          ASSUME `val(word (len - (136 * (i + 1) - p)):int64) = len - (136 * (i + 1) - p)`;
          VAL_WORD_SUB_EQ_0; HX_VAL135;
          MATCH_MP (TAUT `!a b. (~a <=> b) ==> (a <=> ~b)`)
            (ASSUME `~(len - (136 * (i + 1) - p) < 135 \/ len - (136 * (i + 1) - p) = 135) <=> i + 1 < n`);
          COND_SWAP];;

let HXB_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  W(fun (_,g) ->
    if is_exists g then (UNABBREV_VARS_TAC [`pp:num`; `c:num`; `n:num`] THEN SIGN_LOOP_DISCHARGE_TAC)
    else if is_cond(rand g) || is_cond(lhand g) then (COND_CASES_TAC THEN REWRITE_TAC[])
    else FIRST [CONV_TAC WORD_RULE THEN NO_TAC;
                REWRITE_TAC[GSYM ADD1; mld_keccak_absorb_blocks] THEN REWRITE_TAC[ADD1] THEN ASM_REWRITE_TAC[] THEN NO_TAC;
                REWRITE_TAC[READ_MEMORY_WBYTES_1600; GSYM ADD1; mld_keccak_absorb_blocks] THEN ASM_REWRITE_TAC[] THEN NO_TAC;
                ASM_REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN NO_TAC;
                REWRITE_TAC[GSYM(ASSUME `c + (136 - pp) = 136 * (i + 1) - p`)] THEN
                REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN NO_TAC;
                CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN NO_TAC;
                ALL_TAC]);;

let HXB_TAC b fillth extra ntail =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
               [layout_range b.bk_fn; layout_range "mldsa_keccakf1600_permute"] in
  let hd = mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral (layout b.bk_fn + b.bk_head))
  and ex = mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral (layout b.bk_fn + b.bk_exit)) in
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 fillth) "H_FILL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
   (SPONGE_RENAME_E2 MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600) "H_PERM" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(bq:int64) (p:num) (m:int64) (len:num) (pc:num).
      APPEND (f_ev_epil bq p m len pc)
       (APPEND (ENUMERATEL ((p + len) DIV 136) (\i. f_ev_loop bq p m len pc i)) (f_ev_prol bq p m len pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `bq:int64`; `p:num`; `m:int64`; `len:num`; `M:num`; `S:1600 word`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN (parse_term(Printf.sprintf "%d + len <= 2 EXP 64" b.bk_fr)) ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(bq:int64)`; `val(m:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `n = (p + len) DIV 136` THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN SIMP_TAC[DIV_EQ_0; ARITH_EQ] THEN UNDISCH_TAC `136 <= p + len` THEN ARITH_TAC; ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `n:num` hd ex (HXB_INV b) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[mld_keccak_absorb_blocks; WORD_ADD_0; SUB_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    HXB_BODY_TAC b exec extra ntail THEN HXB_FINAL_TAC;
    REWRITE_TAC[] THEN FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC];;

let HXB_PROVE b fillth extra ntail = prove(HXB_STMT b, HXB_TAC b fillth extra ntail);;

(* ------------------------------------------------------------------------- *)
(* An absorb phase after the first (in2 or in3 of mld_H): from its start,    *)
(* with the position p in R15 and the state at bq + sa, to its end, as the   *)
(* gcc shake256_absorb spec: the state becomes FST(mld_keccak_absorb 136 S p *)
(* len M) and R15 its position. If len = 0 nothing; if p + len < 136 the     *)
(* tail at p; otherwise the blocks, then the tail at 0 if bytes are left.    *)
(* ------------------------------------------------------------------------- *)

type hx_phase =
 { ph_fn : string; ph_entry : int; ph_exit : int; ph_so : int; ph_fr : int;
   ph_len : string; ph_dat : string;
   ph_pre : string;    (* the facts at the entry (the stack slots) *)
   ph_post : string;   (* the facts at the exit *)
   ph_mc : string;     (* MAYCHANGE registers *)
   ph_args : string;   (* the readable stack slots of the memaccess list *)
   ph_tail : int;      (* the entry of the tail *)
   ph_tdst : string;   (* the register with the address of the tail *)
   ph_blk : int };;    (* the head of the block loop *)

let ph_tok ph s = subst_tokens
  ["@PRE@",ph.ph_pre; "@POST@",ph.ph_post; "@MC@",ph.ph_mc; "@ARGS@",ph.ph_args;
   "@ENTRY@",string_of_int (layout ph.ph_fn + ph.ph_entry); "@EXIT@",string_of_int (layout ph.ph_fn + ph.ph_exit);
   "@SA@",string_of_int (296 + ph.ph_so); "@FR@",string_of_int ph.ph_fr;
   "@LEN@",ph.ph_len; "@DAT@",ph.ph_dat] s;;

let HXP_STMT ph = parse_term(ph_tok ph
 "exists f_events. forall e bq p m len M (S:1600 word) (out:int64) (x:num) pc.
   p < 136 /\\
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   nonoverlapping (m,len) (bq,@FR@) /\\ nonoverlapping (word pc,libmldsa_size) (bq,@FR@)
   ==> ensures x86
    (\\s. bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
         read RIP s = word (pc + @ENTRY@) /\\ read RSP s = word_add bq (word 296) /\\
         read R15 s = word p /\\ @PRE@
         read (memory :> bytes(m,len)) s = M /\\
         read (memory :> wbytes (word_add bq (word @SA@))) s = S /\\
         read events s = e)
    (\\s. read RIP s = word (pc + @EXIT@) /\\ read RSP s = word_add bq (word 296) /\\
         read R15 s = word (SND(mld_keccak_absorb 136 S p len M)) /\\ @POST@
         read (memory :> wbytes (word_add bq (word @SA@))) s = FST(mld_keccak_absorb 136 S p len M) /\\
         (exists e2. read events s = APPEND e2 e /\\ e2 = f_events bq p m len pc /\\
            memaccess_inbounds e2 [m,len; bq,@FR@; @ARGS@ word(pc + rodata_mld_KeccakF_RoundConstants),192]
                                  [bq,@FR@]))
    (MAYCHANGE [RIP; RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [@MC@] ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(bq,296); memory :> bytes(word_add bq (word @SA@),204)])");;

(* mld_keccak_absorb in the three cases of the code *)
let HXP_ABSORB_0 = prove
 (`!(S:1600 word) p. p < 136 ==> mld_keccak_absorb 136 S p 0 0 = (S,p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_keccak_absorb] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[ADD_CLAUSES; DIV_LT; MOD_LT; MULT_CLAUSES; mld_keccak_absorb_blocks; DIV_0; MOD_0; WORD_XOR_0]);;

let HXP_ABSORB_SHORT = prove
 (`!(S:1600 word) p len M. p + len < 136 /\ M < 2 EXP (8 * len)
     ==> mld_keccak_absorb 136 S p len M = (word_xor S (word(2 EXP (8 * p) * M)),p + len)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_keccak_absorb] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[DIV_LT; MOD_LT; MULT_CLAUSES; mld_keccak_absorb_blocks; EXP; DIV_1; PAIR_EQ] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MOD_LT THEN
  TRANS_TAC LTE_TRANS `2 EXP (8 * p) * 2 EXP (8 * len)` THEN
  ASM_REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD; LE_EXP] THEN ASM_ARITH_TAC);;

(* rewrite the other assumptions with the equation t (an assumption) and   *)
(* simplify (the length of the rest is 0), so that no other assumption     *)
(* rewrites the left-hand side of t; assumptions that would become 0 = x   *)
(* (which would rewrite every 0) are dropped                               *)
let HX_SUBST_ZERO_TAC t =
  FIRST_ASSUM(fun th -> if concl th = t then
    let rw = REWRITE_RULE[th; MULT_CLAUSES; EXP; MOD_1; DIV_0; WORD_XOR_0] in
    let bad a = concl a <> t && (let c = concl(rw a) in is_eq c && is_numeral(lhs c)) in
    REPEAT(FIRST_X_ASSUM(fun a -> if bad a then ALL_TAC else NO_TAC)) THEN
    RULE_ASSUM_TAC(fun a -> if concl a = t then a else rw a) else NO_TAC);;

(* the block after the last one of a message that ends at a block boundary *)
let HXP_BLK_ZERO = prove
 (`!p len M n. M < 2 EXP (8 * len) /\ p + len = 136 * n
     ==> ((2 EXP (8 * p) * M) DIV 2 EXP (8 * 136 * n)) MOD 2 EXP (8 * 136) = 0 /\
         (M DIV 2 EXP (8 * 136 * n)) MOD 2 EXP (8 * 136) = 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `2 EXP (8 * p) * M < 2 EXP (8 * 136 * n) /\ M < 2 EXP (8 * 136 * n)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `p + len = 136 * n`); LEFT_ADD_DISTRIB; EXP_ADD] THEN
    ASM_REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
    TRANS_TAC LTE_TRANS `2 EXP (8 * len)` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `x = 1 * x`] THEN
    REWRITE_TAC[LE_MULT_RCANCEL; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0; ARITH_EQ];
    ASM_SIMP_TAC[DIV_LT; MOD_0]]);;

(* The tactic for a phase, given the tail and block-loop lemmas. dst0 is the *)
(* register that the code sets to the state + p before the tail.            *)
let HXP_TAC ph tailth blkth =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc [layout_range ph.ph_fn] in
  let sat = mk_small_numeral (296 + ph.ph_so) in
  let st = mk_comb(`word_add (bq:int64)`,mk_comb(`word:num->int64`,sat)) in
  let vars = [`bq:int64`; `p:num`; `m:int64`; `len:num`; `pc:num`] in
  let tdst = mk_const(ph.ph_tdst,[]) in
  let ent l = layout ph.ph_fn + l in
  let val_len = `val (word len:int64) = len` in
  let nov_m st' r = (* nonoverlap of (m',r) with the state *)
    subst [st',`st:int64`; r,`r:num`] `nonoverlapping_modulo (2 EXP 64) (val (m:int64),r) (val (st:int64),200)` in
  let _ = nov_m in
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 tailth) "H_TAIL" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 blkth) "H_BLK" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(bq:int64) (p:num) (m:int64) (len:num) (pc:num).
      if len = 0 then f_ev_0 bq p m len pc
      else if p + len < 136 then f_ev_1 bq p m len pc
      else if (p + len) MOD 136 = 0 then f_ev_2 bq p m len pc else f_ev_3 bq p m len pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `bq:int64`; `p:num`; `m:int64`; `len:num`; `M:num`; `S:1600 word`;
                       `out:int64`; `x:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN (parse_term(Printf.sprintf "%d + len <= 2 EXP 64" ph.ph_fr)) ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(bq:int64)`; `val(m:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN val_len ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC (parse_term(Printf.sprintf "%d + len <= 2 EXP 64" ph.ph_fr)) THEN ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `p:num` THEN
  SUBGOAL_THEN `val(word (136 - p):int64) = 136 - p /\ word_sub (word 136) (word p):int64 = word (136 - p)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC;
                    ASM_SIMP_TAC[WORD_SUB2; LT_IMP_LE]]; ALL_TAC] THEN
  FULL_INIT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  SUBGOAL_THEN `M < 2 EXP (8 * len)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if can (term_match [`m:int64`; `len:num`; `M:num`] `read (memory :> bytes (m,len)) s = M`) (concl th)
                          then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND]; ALL_TAC] THEN
  ASM_CASES_TAC `len = 0` THENL
   [(*** nothing ***)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `M = 0` SUBST_ALL_TAC THENL [UNDISCH_TAC `M < 2 EXP (8 * 0)` THEN REWRITE_TAC[MULT_CLAUSES; EXP] THEN ARITH_TAC; ALL_TAC] THEN
    HX_DRIVE_TAC exec [ASSUME `val (word 0:int64) = 0`] (ent ph.ph_exit) THEN
    ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN ASM_SIMP_TAC[HXP_ABSORB_0] THEN DISCHARGE_SAFETY_PROPERTY_SPINE_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `p + len < 136` THENL
   [(*** the tail only, at p ***)
    SUBGOAL_THEN `len < 136 - p` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`p + len < 136`] THEN ARITH_TAC; ALL_TAC] THEN
    HX_DRIVE_TAC exec ((map (fun t -> ASSUME t) [val_len; `val(word (136 - p):int64) = 136 - p`;
         `word_sub (word 136) (word p):int64 = word (136 - p)`; `val (word p:int64) = p`]) @
         [EQT_INTRO(ASSUME `len < 136 - p`); EQF_INTRO(ASSUME `~(len = 0)`)] @ hx_p32 `p:num`)
      (ent ph.ph_tail) THEN
    HX_RESTATE_TAC tdst (mk_comb(mk_comb(`word_add:int64->int64->int64`,st),`word p:int64`)) HX_ADDR_EQ_TAC THEN
    SUBGOAL_THEN `0 < len` ASSUME_TAC THENL [UNDISCH_TAC `~(len = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN (subst [st,`st:int64`] `nonoverlapping_modulo (2 EXP 64) (val (m:int64),len) (val (st:int64),200)`) ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN MATCH_MP_TAC SPONGE_NOV_OFFSET THEN
      EXISTS_TAC (mk_small_numeral ph.ph_fr) THEN
      ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    KECCAK_STATE_WBYTES_TAC `S:1600 word` THEN
    HX_LCALL_TAC exec "H_TAIL" [st; `p:num`; `m:int64`; `len:num`; `M:num`; `S:1600 word`; `pc:num`] vars THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    HX_DRIVE_TAC exec [] (ent ph.ph_exit) THEN
    HX_RESTATE_TAC `R15` `word (p + len):int64`
      (REWRITE_TAC[WORD_ZX_ZX_32_64_32] THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
       REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
       CONV_TAC NUM_REDUCE_CONV THEN
       SUBGOAL_THEN `p < 4294967296 /\ len < 4294967296 /\ p + len < 4294967296` STRIP_ASSUME_TAC THENL
        [MAP_EVERY UNDISCH_TAC [`p + len < 136`] THEN ARITH_TAC; ALL_TAC] THEN
       ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x < 4294967296 ==> x < 18446744073709551616`]) THEN
    ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN ASM_SIMP_TAC[HXP_ABSORB_SHORT] THEN DISCHARGE_SAFETY_PROPERTY_SPINE_TAC;
    ALL_TAC] THEN
  (*** the blocks, then the rest if any ***)
  SUBGOAL_THEN `~(len < 136 - p) /\ 136 <= p + len` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`~(p + len < 136)`; `~(len = 0)`] THEN ARITH_TAC; ALL_TAC] THEN
  HX_DRIVE_TAC exec ((map (fun t -> ASSUME t) [val_len; `val(word (136 - p):int64) = 136 - p`;
       `word_sub (word 136) (word p):int64 = word (136 - p)`; `val (word p:int64) = p`]) @
       [EQF_INTRO(ASSUME `~(len < 136 - p)`); EQF_INTRO(ASSUME `~(len = 0)`)] @ hx_p32 `p:num`)
    (ent ph.ph_blk) THEN
  HX_RESTATE_TAC tdst st HX_ADDR_EQ_TAC THEN
  KECCAK_STATE_WBYTES_TAC `S:1600 word` THEN
  HX_LCALL_TAC exec "H_BLK" [`bq:int64`; `p:num`; `m:int64`; `len:num`; `M:num`; `S:1600 word`; `pc:num`] vars THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  MP_TAC(SPECL [`M:num`; `len:num`; `p:num`; `136`] HX_ABSORB_TAIL) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < 136`; LT_IMP_LE] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `n = (p + len) DIV 136` THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN SIMP_TAC[DIV_EQ_0; ARITH_EQ] THEN UNDISCH_TAC `136 <= p + len` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if concl th = `len - (136 * n - p) = (p + len) MOD 136` then ASSUME_TAC(SYM th) else NO_TAC) THEN
  SUBGOAL_THEN `FST(mld_keccak_absorb 136 S p len M) =
                word_xor (mld_keccak_absorb_blocks 136 S (2 EXP (8 * p) * M) n)
                         (word((M DIV 2 EXP (8 * (136 * n - p))) MOD 2 EXP (8 * (len - (136 * n - p))))) /\
                SND(mld_keccak_absorb 136 S p len M) = len - (136 * n - p)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mld_keccak_absorb] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `val(word (len - (136 * n - p)):int64) = len - (136 * n - p)` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC (parse_term(Printf.sprintf "%d + len <= 2 EXP 64" ph.ph_fr)) THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `len - (136 * n - p) = 0` THEN
  (* the case of the events template *)
  FIRST_ASSUM(fun eq -> if concl eq = `(p + len) MOD 136 = len - (136 * n - p)` then
    FIRST_ASSUM(fun c -> if concl c = `len - (136 * n - p) = 0` then ASSUME_TAC(TRANS eq c)
                         else if concl c = `~(len - (136 * n - p) = 0)` then ASSUME_TAC(REWRITE_RULE[SYM eq] c)
                         else NO_TAC)
    else NO_TAC) THENL
   [(*** no rest ***)
    HX_DRIVE_TAC exec [ASSUME `val(word (len - (136 * n - p)):int64) = len - (136 * n - p)`;
                       ASSUME `len - (136 * n - p) = 0`] (ent ph.ph_exit) THEN
    HX_RESTATE_TAC `R15` `word (len - (136 * n - p)):int64`
      (REWRITE_TAC[ASSUME `len - (136 * n - p) = 0`] THEN CONV_TAC WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN `p + len = 136 * n` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(p + len) MOD 136 = 0`; `(p + len) DIV 136 = n`] THEN
      MP_TAC(SPECL [`p + len`; `136`] DIVISION) THEN ARITH_TAC; ALL_TAC] THEN
    HX_SUBST_ZERO_TAC `len - (136 * n - p) = 0` THEN
    ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN ASM_REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; DIV_0; WORD_XOR_0] THEN
    ASM_SIMP_TAC[HXP_BLK_ZERO; MOD_1; WORD_XOR_0] THEN UNABBREV_VARS_TAC [`n:num`] THEN DISCHARGE_SAFETY_PROPERTY_SPINE_TAC;
    ALL_TAC] THEN
  (*** the rest of the message, at 0 ***)
  SUBGOAL_THEN `val(word ((p + len) MOD 136):int64) = (p + len) MOD 136` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    MP_TAC(SPECL [`p + len`; `136`] MOD_LT_EQ) THEN ARITH_TAC; ALL_TAC] THEN
  HX_DRIVE_TAC exec [ASSUME `val(word (len - (136 * n - p)):int64) = len - (136 * n - p)`;
                     EQF_INTRO(ASSUME `~(len - (136 * n - p) = 0)`);
                     ASSUME `val(word ((p + len) MOD 136):int64) = (p + len) MOD 136`;
                     EQF_INTRO(ASSUME `~((p + len) MOD 136 = 0)`)] (ent ph.ph_tail) THEN
  HX_RESTATE_TAC tdst (mk_comb(mk_comb(`word_add:int64->int64->int64`,st),`word 0:int64`)) HX_ADDR_EQ_TAC THEN
  SUBGOAL_THEN `0 < len - (136 * n - p) /\ 0 + len - (136 * n - p) < 136` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`~(len - (136 * n - p) = 0)`; `(p + len) MOD 136 = len - (136 * n - p)`] THEN
    MP_TAC(SPECL [`p + len`; `136`] MOD_LT_EQ) THEN ARITH_TAC; ALL_TAC] THEN
  W(fun (asl,w) -> let s = hx_cur_state asl in
    SUBGOAL_THEN (subst [s,`s:x86state`]
      `read (memory :> bytes(word_add m (word (136 * n - p)),len - (136 * n - p))) s =
       (M DIV 2 EXP (8 * (136 * n - p))) MOD 2 EXP (8 * (len - (136 * n - p)))`) ASSUME_TAC THENL
     [MATCH_MP_TAC READ_MEMORY_BYTES_SUB THEN EXISTS_TAC `len:num` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `136 * n - p <= len` THEN ARITH_TAC; ALL_TAC]) THEN
  SUBGOAL_THEN (subst [st,`st:int64`] `nonoverlapping_modulo (2 EXP 64) (val (word_add (m:int64) (word (136 * n - p))),len - (136 * n - p)) (val (st:int64),200)`) ASSUME_TAC THENL
   [MATCH_MP_TAC SPONGE_NOV_SUB2 THEN MAP_EVERY EXISTS_TAC [`len:num`; mk_small_numeral ph.ph_fr] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `136 * n - p <= len` THEN ARITH_TAC;
    ALL_TAC] THEN
  KECCAK_STATE_WBYTES_TAC `mld_keccak_absorb_blocks 136 S (2 EXP (8 * p) * M) n` THEN
  HX_LCALL_TAC exec "H_TAIL"
    [st; `0`; `word_add m (word (136 * n - p)):int64`; `len - (136 * n - p)`;
     `(M DIV 2 EXP (8 * (136 * n - p))) MOD 2 EXP (8 * (len - (136 * n - p)))`;
     `mld_keccak_absorb_blocks 136 S (2 EXP (8 * p) * M) n`; `pc:num`] vars THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  HX_DRIVE_TAC exec [] (ent ph.ph_exit) THEN
  HX_RESTATE_TAC `R15` `word (len - (136 * n - p)):int64`
    (REWRITE_TAC[WORD_ZX_ZX_32_64_32] THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
     REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     SUBGOAL_THEN `len - (136 * n - p) < 136` ASSUME_TAC THENL
      [UNDISCH_TAC `0 + len - (136 * n - p) < 136` THEN ARITH_TAC; ALL_TAC] THEN
     ASM_SIMP_TAC[MOD_LT; ADD_CLAUSES; ARITH_RULE `x < 136 ==> x < 4294967296 /\ x < 18446744073709551616`]) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN ASM_REWRITE_TAC[MULT_CLAUSES; EXP] THEN
  UNABBREV_VARS_TAC [`n:num`] THEN DISCHARGE_SAFETY_PROPERTY_SPINE_TAC;;

let HXP_PROVE ph tailth blkth = prove(HXP_STMT ph, HXP_TAC ph tailth blkth);;

(* ------------------------------------------------------------------------- *)
(* A region lemma stated with the stack pointer rsp0 of the region, restated *)
(* with rsp0 = bq + k for the phase lemmas (the addresses below rsp0 become  *)
(* bq + n): `?f. !.. rsp0 ... P` to `?f. !.. bq ... P[bq + k/rsp0]`.         *)
(* ------------------------------------------------------------------------- *)

let HX_REBASE_RULE k th =
  let rsp0 = `rsp0:int64` and bq = `bq:int64` in
  let sub = mk_comb(mk_comb(`word_add:int64->int64->int64`,bq),mk_comb(`word:num->int64`,mk_small_numeral k)) in
  let f,body = dest_exists(concl th) in
  let vs,_ = strip_forall body in
  let th1 = SPECL (map (fun v -> if v = rsp0 then sub else v) vs) (ASSUME body) in
  let th2 = CONV_RULE (DEPTH_CONV NORMALIZE_ADD_SUBTRACT_WORD_CONV) th1 in
  let th3 = GENL (map (fun v -> if v = rsp0 then bq else v) vs) th2 in
  CHOOSE (f,th) (EXISTS (mk_exists(f,concl th3),f) th3);;

(* ------------------------------------------------------------------------- *)
(* The absorb of the first input (nonempty, from position 0 of the state at *)
(* bq + 296 + so), from the zeroing of the state to the join after the tail: *)
(* the zeroing (zth), then the tail (tth) if len < 136, otherwise loop1     *)
(* (l1th) and the tail at 0 if bytes are left. The state becomes            *)
(* FST(mld_keccak_absorb 136 (word 0) 0 len M), the length register its     *)
(* position. The region lemmas are stated with rsp0 = bq + 296.             *)
(* ------------------------------------------------------------------------- *)

type hx_p1 =
 { p1_fn : string; p1_entry : int; p1_zend : int; p1_loop : int; p1_tail : int; p1_exit : int;
   p1_so : int; p1_fr : int; p1_dat : string; p1_len : string; p1_st : string; p1_mc : string;
   p1_cmp : string };;   (* the register with the length at the entry test *)

let p1_tok q s = subst_tokens
  ["@ENTRY@",string_of_int (layout q.p1_fn + q.p1_entry); "@EXIT@",string_of_int (layout q.p1_fn + q.p1_exit);
   "@SA@",string_of_int (296 + q.p1_so); "@FR@",string_of_int q.p1_fr;
   "@DAT@",q.p1_dat; "@LEN@",q.p1_len; "@MC@",q.p1_mc; "@CMP@",q.p1_cmp] s;;

let HXP1_STMT q = parse_term(p1_tok q
 "exists f_events. forall e bq m len M pc.
   ~(len = 0) /\\ aligned 16 (word_add bq (word 296):int64) /\\
   aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
   nonoverlapping (m,len) (bq,@FR@) /\\ nonoverlapping (word pc,libmldsa_size) (bq,@FR@)
   ==> ensures x86
    (\\s. bytes_loaded s (word pc) mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\\
         read RIP s = word (pc + @ENTRY@) /\\ read RSP s = word_add bq (word 296) /\\
         read @DAT@ s = m /\\ read @LEN@ s = word len /\\ read @CMP@ s = word len /\\
         read (memory :> bytes(m,len)) s = M /\\
         read events s = e)
    (\\s. read RIP s = word (pc + @EXIT@) /\\ read RSP s = word_add bq (word 296) /\\
         read @LEN@ s = word (SND(mld_keccak_absorb 136 (word 0) 0 len M)) /\\
         read (memory :> wbytes (word_add bq (word @SA@))) s = FST(mld_keccak_absorb 136 (word 0) 0 len M) /\\
         (exists e2. read events s = APPEND e2 e /\\ e2 = f_events bq m len pc /\\
            memaccess_inbounds e2 [m,len; bq,@FR@; word(pc + rodata_mld_KeccakF_RoundConstants),192]
                                  [bq,@FR@]))
    (MAYCHANGE [RIP; RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
     MAYCHANGE [@MC@] ,, MAYCHANGE [events] ,,
     MAYCHANGE [memory :> bytes(bq,296); memory :> bytes(word_add bq (word @SA@),204)])");;

let HXP1_TAC q zth l1th tth =
  let exec = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc [layout_range q.p1_fn] in
  let st = mk_comb(`word_add (bq:int64)`,mk_comb(`word:num->int64`,mk_small_numeral (296 + q.p1_so))) in
  let vars = [`bq:int64`; `m:int64`; `len:num`; `pc:num`] in
  let ent l = layout q.p1_fn + l in
  let val_len = `val (word len:int64) = len` in
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 (HX_REBASE_RULE 296 zth)) "H_ZERO" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 (HX_REBASE_RULE 296 l1th)) "H_L1" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC (SPONGE_RENAME_E2 (HX_REBASE_RULE 296 tth)) "H_TAIL" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(bq:int64) (m:int64) (len:num) (pc:num).
      if len < 136 then f_ev_1 bq m len pc
      else if len MOD 136 = 0 then f_ev_2 bq m len pc else f_ev_3 bq m len pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `bq:int64`; `m:int64`; `len:num`; `M:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; NONOVERLAPPING_CLAUSES; ALL; fst exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN (parse_term(Printf.sprintf "%d + len <= 2 EXP 64" q.p1_fr)) ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(bq:int64)`; `val(m:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN val_len ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC (parse_term(Printf.sprintf "%d + len <= 2 EXP 64" q.p1_fr)) THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `len < 2 EXP 64` ASSUME_TAC THENL
   [UNDISCH_TAC (parse_term(Printf.sprintf "%d + len <= 2 EXP 64" q.p1_fr)) THEN ARITH_TAC; ALL_TAC] THEN
  FULL_INIT_TAC THEN
  SUBGOAL_THEN `M < 2 EXP (8 * len)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if can (term_match [`m:int64`; `len:num`; `M:num`] `read (memory :> bytes (m,len)) s = M`) (concl th)
                          then SUBST1_TAC(SYM th) else NO_TAC) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND]; ALL_TAC] THEN
  HX_LCALL_TAC exec "H_ZERO" [`bq:int64`; `pc:num`] vars THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ASM_CASES_TAC `len < 136` THENL
   [(*** the tail only ***)
    HX_DRIVE_TAC exec [ASSUME val_len; EQT_INTRO(ASSUME `len < 136`)] (ent q.p1_tail) THEN
    SUBGOAL_THEN (subst [st,`st:int64`] `nonoverlapping_modulo (2 EXP 64) (val (m:int64),len) (val (st:int64),200)`) ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN MATCH_MP_TAC SPONGE_NOV_OFFSET THEN
      EXISTS_TAC (mk_small_numeral q.p1_fr) THEN
      ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    SUBGOAL_THEN `0 < len` ASSUME_TAC THENL [UNDISCH_TAC `~(len = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    KECCAK_STATE_WBYTES_TAC `word 0:1600 word` THEN
    HX_LCALL_TAC exec "H_TAIL" [`bq:int64`; `m:int64`; `len:num`; `M:num`; `word 0:1600 word`; `pc:num`] vars THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    HX_DRIVE_TAC exec [] (ent q.p1_exit) THEN
    ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN
    MP_TAC(SPECL [`word 0:1600 word`; `0`; `len:num`; `M:num`] HXP_ABSORB_SHORT) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; EXP] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_SPINE_TAC;
    ALL_TAC] THEN
  (*** loop1, then the rest if any ***)
  ABBREV_TAC `n = len DIV 136` THEN
  SUBGOAL_THEN `0 < n` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN SIMP_TAC[LT_NZ; DIV_EQ_0; ARITH_EQ] THEN UNDISCH_TAC `~(len < 136)` THEN ARITH_TAC; ALL_TAC] THEN
  HX_DRIVE_TAC exec [ASSUME val_len; EQF_INTRO(ASSUME `~(len < 136)`)] (ent q.p1_loop) THEN
  HX_RESTATE_TAC (mk_const(q.p1_st,[])) st HX_ADDR_EQ_TAC THEN
  KECCAK_STATE_WBYTES_TAC `word 0:1600 word` THEN
  HX_LCALL_TAC exec "H_L1" [`m:int64`; `len:num`; `M:num`; `bq:int64`; `n:num`; `word 0:1600 word`; `pc:num`] vars THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  MP_TAC(SPECL [`M:num`; `len:num`; `0`; `136`] HX_ABSORB_TAIL) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < 136`; LE_0] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  SUBGOAL_THEN `~(n = 0)` (fun th -> REWRITE_TAC[th]) THENL [UNDISCH_TAC `0 < n` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; SUB_0; ADD_CLAUSES] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if concl th = `len - 136 * n = len MOD 136` then ASSUME_TAC(SYM th) else NO_TAC) THEN
  SUBGOAL_THEN `FST(mld_keccak_absorb 136 (word 0) 0 len M) =
                word_xor (mld_keccak_absorb_blocks 136 (word 0) M n)
                         (word((M DIV 2 EXP (8 * 136 * n)) MOD 2 EXP (8 * (len - 136 * n)))) /\
                SND(mld_keccak_absorb 136 (word 0) 0 len M) = len - 136 * n` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[mld_keccak_absorb] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; EXP; SUB_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `val(word (len - 136 * n):int64) = len - 136 * n` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `len < 2 EXP 64` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `len - 136 * n = 0` THEN
  (* the case of the events template *)
  FIRST_ASSUM(fun eq -> if concl eq = `len MOD 136 = len - 136 * n` then
    FIRST_ASSUM(fun c -> if concl c = `len - 136 * n = 0` then ASSUME_TAC(TRANS eq c)
                         else if concl c = `~(len - 136 * n = 0)` then ASSUME_TAC(REWRITE_RULE[SYM eq] c)
                         else NO_TAC)
    else NO_TAC) THENL
   [(*** no rest ***)
    HX_DRIVE_TAC exec [ASSUME `val(word (len - 136 * n):int64) = len - 136 * n`;
                       ASSUME `len - 136 * n = 0`] (ent q.p1_exit) THEN
    HX_RESTATE_TAC (mk_const(q.p1_len,[])) `word (len - 136 * n):int64`
      (REWRITE_TAC[ASSUME `len - 136 * n = 0`] THEN CONV_TAC WORD_REDUCE_CONV) THEN
    SUBGOAL_THEN `0 + len = 136 * n` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`len MOD 136 = 0`; `len DIV 136 = n`] THEN
      MP_TAC(SPECL [`len:num`; `136`] DIVISION) THEN ARITH_TAC; ALL_TAC] THEN
    HX_SUBST_ZERO_TAC `len - 136 * n = 0` THEN
    ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; DIV_0; WORD_XOR_0] THEN
    ASM_SIMP_TAC[HXP_BLK_ZERO; MOD_1; WORD_XOR_0] THEN UNABBREV_VARS_TAC [`n:num`] THEN DISCHARGE_SAFETY_PROPERTY_SPINE_TAC;
    ALL_TAC] THEN
  (*** the rest of the message, at 0 ***)
  SUBGOAL_THEN `val(word (len MOD 136):int64) = len MOD 136` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    MP_TAC(SPECL [`len:num`; `136`] MOD_LT_EQ) THEN ARITH_TAC; ALL_TAC] THEN
  HX_DRIVE_TAC exec [ASSUME `val(word (len - 136 * n):int64) = len - 136 * n`;
                     EQF_INTRO(ASSUME `~(len - 136 * n = 0)`);
                     ASSUME `val(word (len MOD 136):int64) = len MOD 136`;
                     EQF_INTRO(ASSUME `~(len MOD 136 = 0)`)] (ent q.p1_tail) THEN
  SUBGOAL_THEN `0 < len - 136 * n /\ len - 136 * n < 136 /\ 136 * n <= len` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`~(len - 136 * n = 0)`; `len DIV 136 = n`] THEN
    MP_TAC(SPECL [`len:num`; `136`] DIVISION) THEN ARITH_TAC; ALL_TAC] THEN
  W(fun (asl,w) -> let s = hx_cur_state asl in
    SUBGOAL_THEN (subst [s,`s:x86state`]
      `read (memory :> bytes(word_add m (word (136 * n)),len - 136 * n)) s =
       (M DIV 2 EXP (8 * 136 * n)) MOD 2 EXP (8 * (len - 136 * n))`) ASSUME_TAC THENL
     [MATCH_MP_TAC READ_MEMORY_BYTES_SUB THEN EXISTS_TAC `len:num` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `136 * n <= len` THEN ARITH_TAC; ALL_TAC]) THEN
  SUBGOAL_THEN (subst [st,`st:int64`] `nonoverlapping_modulo (2 EXP 64) (val (word_add (m:int64) (word (136 * n))),len - 136 * n) (val (st:int64),200)`) ASSUME_TAC THENL
   [MATCH_MP_TAC SPONGE_NOV_SUB2 THEN MAP_EVERY EXISTS_TAC [`len:num`; mk_small_numeral q.p1_fr] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `136 * n <= len` THEN ARITH_TAC;
    ALL_TAC] THEN
  (* the events of loop1 have the argument n: expand it before the call *)
  UNABBREV_VARS_TAC [`n:num`] THEN
  KECCAK_STATE_WBYTES_TAC `mld_keccak_absorb_blocks 136 (word 0) M (len DIV 136)` THEN
  HX_LCALL_TAC exec "H_TAIL"
    [`bq:int64`; `word_add m (word (136 * len DIV 136)):int64`; `len - 136 * len DIV 136`;
     `(M DIV 2 EXP (8 * 136 * len DIV 136)) MOD 2 EXP (8 * (len - 136 * len DIV 136))`;
     `mld_keccak_absorb_blocks 136 (word 0) M (len DIV 136)`; `pc:num`] vars THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  HX_DRIVE_TAC exec [] (ent q.p1_exit) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_SPINE_TAC;;

let HXP1_PROVE q zth l1th tth = prove(HXP1_STMT q, HXP1_TAC q zth l1th tth);;
