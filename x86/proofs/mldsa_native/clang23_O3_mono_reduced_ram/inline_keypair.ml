(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Regions that clang 23 -O3 inlines into mldsa{44,65,87}_keypair_internal   *)
(* in the monolithic reduced-RAM build, as lemmas from a label of the code   *)
(* to another that the proofs of the callers use as they use the theorem for *)
(* a subroutine (see inline_sign.ml and inline_keygen.ml):                   *)
(*                                                                           *)
(*  - SEED: the inlined SHAKE256 of seed || k || l (34 bytes, one block and  *)
(*    one permutation) whose first 128 bytes are rho, rho' and the key;      *)
(*  - PACK2: the inlined mld_polyeta_pack for eta = 2, 8 coefficients to 3   *)
(*    bytes per iteration, in scalar byte code;                              *)
(*  - HASHR: the inlined SHAKE256 of the public key into the state of tr,    *)
(*    as HASHB of inline_keygen.ml with the key pointer in a register.       *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_keygen.ml";;

let has_sub s t = can (find_term (fun u -> u = s)) t;;

(* ------------------------------------------------------------------------- *)
(* SEED. The 34-byte input M = SEED + 2^256 (k + 256 l) of SHAKE256 is       *)
(* copied to rsp0 + 0xe0, the state at rsp0 + 0x1e0 is zeroed, the input     *)
(* and the padding are put into it with stores of 16, 8 and 1 bytes, it is   *)
(* permuted, its first 128 bytes are copied to rsp0 + 0x160 (rho, rho' and   *)
(* the key) and it is zeroed again. The lemmas for the bytes of M in memory  *)
(* and for the state as a chain of pieces are those of inline_pu.ml          *)
(* (x86-A), for a 34-byte input of SHAKE256 instead of SHAKE128.             *)
(* ------------------------------------------------------------------------- *)

let KP_PTR_ADD = prove(`!b:int64 n k. word_add (word_add b (word n)) (word k) = word_add b (word (n + k))`,
  REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]);;

let KP_RDN n =
  let sub = subst_tokens ["@N@",string_of_int n; "@NB@",string_of_int (n/8);
                          "@BN@",Printf.sprintf "bytes%d" n] in
  let wth = (match n with 8 -> BYTES8_WBYTES | 16 -> BYTES16_WBYTES | 32 -> BYTES32_WBYTES
             | 64 -> BYTES64_WBYTES | _ -> BYTES128_WBYTES) in
  prove(parse_term(sub
   "!(a:int64) m x j (s:x86state).
        read (memory :> bytes(a,m)) s = x /\\ j + @NB@ <= m
        ==> read (memory :> @BN@ (word_add a (word j))) s =
            word((x DIV 2 EXP (8 * j)) MOD 2 EXP @N@)"),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[wth; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_REFL; GSYM READ_COMPONENT_COMPOSE] THEN
  MP_TAC(SPECL [`a:int64`; `m:num`; `x:num`; `j:num`; parse_term(sub "@NB@"); `s:x86state`] READ_MEMORY_BYTES_SUB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN CONV_TAC NUM_REDUCE_CONV);;

let KP_RD8 = KP_RDN 8;; let KP_RD64 = KP_RDN 64;; let KP_RD128 = KP_RDN 128;;

(*** word((M DIV 2^(8j)) MOD 2^N) as a subword of word M : 272 word ***)

let KP_SUBW n =
  let sub = subst_tokens ["@N@",string_of_int n; "@NT@",(match n with 8 -> ":byte" | 64 -> ":int64" | _ -> ":int128")] in
  prove(parse_term(sub
   "!M j. M < 2 EXP 272 /\\ 8 * j + @N@ <= 272
         ==> word((M DIV 2 EXP (8 * j)) MOD 2 EXP @N@)@NT@ =
             word_subword (word M:272 word) (8 * j,@N@)"),
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; VAL_WORD_SUBWORD; DIMINDEX_8; DIMINDEX_64; DIMINDEX_128] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  SUBGOAL_THEN `M MOD 2 EXP 272 = M` (fun th -> REWRITE_TAC[th]) THENL [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MIN; MOD_MOD_REFL] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL]);;

let KP_SUBW8 = KP_SUBW 8;; let KP_SUBW64 = KP_SUBW 64;; let KP_SUBW128 = KP_SUBW 128;;

let KP_B16 = prove(`!a:int64 s:x86state. read (memory :> bytes(a,16)) s = val(read (memory :> bytes128 a) s)`,
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV);;
(*** Parts of a zero 128-bit chunk ***)

let KP_ZSUB n =
  let sub = subst_tokens ["@NB@",string_of_int (n/8); "@BN@",Printf.sprintf "bytes%d" n] in
  prove(parse_term(sub
   "!(a:int64) k (s:x86state).
        read (memory :> bytes128 a) s = word 0 /\\ k + @NB@ <= 16
        ==> read (memory :> @BN@ (word_add a (word k))) s = word 0"),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `16`; `read (memory :> bytes(a,16)) (s:x86state)`; `k:num`; `s:x86state`]
    (match n with 8 -> KP_RD8 | 64 -> KP_RD64 | _ -> failwith "zsub")) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `read (memory :> bytes(a,16)) (s:x86state) = 0` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[KP_B16; VAL_WORD_0]; ALL_TAC] THEN
  REWRITE_TAC[DIV_0; MOD_0; WORD_ADD_0]);;

let KP_ZSUB8 = KP_ZSUB 8;; let KP_ZSUB64 = KP_ZSUB 64;;

(*** The fact that the nb bytes at fb + k are zero, from the zero chunk at
     fb + off ***)

let kp_zfact sname off k nb =
  let s = mk_var(sname,`:x86state`) in
  let tm = parse_term(Printf.sprintf "read (memory :> bytes%d (word_add fb (word %d))) %s = word 0" (8*nb) k sname) in
  let lem = if nb = 1 then KP_ZSUB8 else KP_ZSUB64 in
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [MP_TAC(SPECL [parse_term(Printf.sprintf "word_add fb (word %d):int64" off); mk_small_numeral (k-off); s] lem) THEN
    ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ARITH_TAC]; ALL_TAC] THEN
    REWRITE_TAC[KP_PTR_ADD] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN DISCH_THEN ACCEPT_TAC;
    ALL_TAC];;

(*** A chain of pieces of a byte string into bytes(d,n) = x MOD 2^(8n) ***)

let KP_BYTES_EXTEND = prove
 (`!d:int64 j k x s:x86state.
        read (memory :> bytes(d,j)) s = x MOD 2 EXP (8 * j) /\
        read (memory :> bytes(word_add d (word j),k)) s =
        (x DIV 2 EXP (8 * j)) MOD 2 EXP (8 * k)
        ==> read (memory :> bytes(d,j + k)) s = x MOD 2 EXP (8 * (j + k))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; MOD_MULT_MOD] THEN
  ARITH_TAC);;

let KP_B2 = prove(`!a:int64 s:x86state. read (memory :> bytes(a,2)) s = val(read (memory :> bytes16 a) s)`,
  REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV);;
let KP_B1 = prove(`!a:int64 s:x86state. read (memory :> bytes(a,1)) s = val(read (memory :> bytes8 a) s)`,
  REWRITE_TAC[READ_MEMORY_BYTES_BYTES8]);;

(*** A piece of the state S (a 1600-bit word) in memory, from a fact about
     a 128-bit chunk or a byte with the value V of the simulation ***)

let KP_PIECE16 = prove
 (`!(S:1600 word) (A:int64) (s:x86state) (V:int128) off.
     read (memory :> bytes128 A) s = V /\ V = word_subword S (8 * off,128)
     ==> read (memory :> bytes(A,16)) s = (val S DIV 2 EXP (8 * off)) MOD 2 EXP 128`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[KP_B16] THEN ASM_REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_CONV `dimindex(:128)`; MIN; LE_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV);;
let KP_PIECE8 = prove
 (`!(S:1600 word) (A:int64) (s:x86state) (V:byte) off.
     read (memory :> bytes8 A) s = V /\ V = word_subword S (8 * off,8)
     ==> read (memory :> bytes(A,1)) s = (val S DIV 2 EXP (8 * off)) MOD 2 EXP 8`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[KP_B1] THEN ASM_REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_CONV `dimindex(:8)`; MIN; LE_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let KP_ZX_MOD8 = prove(`!y:N word. word (val y MOD 256):byte = word_zx y`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; word_zx; VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL]);;

let KP_NORMC = TRY_CONV(REWRITE_CONV[KP_PTR_ADD]) THENC DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV);;
let KP_NORM = CONV_RULE KP_NORMC;;

(*** The padded state of the 34-byte input M of SHAKE256 ***)

let KP_SW = `word_or (word_zx (word M:272 word):1600 word) (word(2 EXP 272 * 31 + 2 EXP 1080 * 128))`;;

let KP_SW_XOR = prove
 (`!W:272 word. word_xor (word_xor (word_zx W) (word (2 EXP 272 * 31))) (word (2 EXP 1080 * 128)):1600 word =
                word_or (word_zx W) (word (2 EXP 272 * 31 + 2 EXP 1080 * 128))`,
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST);;

let KP_S_WORD = prove
 (`!M. M < 2 EXP 272
       ==> mld_shake256_state 34 M =
           word_or (word_zx (word M:272 word):1600 word)
                   (word(2 EXP 272 * 31 + 2 EXP 1080 * 128))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`M:num`; `0`; `34`; `M:num`] SPONGE_SHAKE_STATE) THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; EXP; DIV_1; ARITH_RULE `34 < 136`;
              ARITH_RULE `8 * 34 = 272`; ARITH_RULE `8 * 135 = 1080`] THEN
  ASM_SIMP_TAC[MOD_LT] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[CONJUNCT1 mld_keccak_absorb_blocks] THEN
  REWRITE_TAC[WORD_XOR_0; CONJUNCT1(SPEC_ALL WORD_XOR_0)] THEN
  SUBGOAL_THEN `word M:1600 word = word_zx (word M:272 word)` SUBST1_TAC THENL
   [REWRITE_TAC[word_zx; VAL_WORD; DIMINDEX_CONV `dimindex(:272)`] THEN
    ASM_SIMP_TAC[MOD_LT];
    ALL_TAC] THEN
  REWRITE_TAC[KP_SW_XOR]);;

(*** The chunks of the seed as subwords of word M, M = SEED + 2^256 c ***)

let KP_DIVMOD_HI = prove
 (`!x c p. p + 128 <= 256
     ==> ((x + 2 EXP 256 * c) DIV 2 EXP p) MOD 2 EXP 128 = (x DIV 2 EXP p) MOD 2 EXP 128`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x + 2 EXP 256 * c = ((2 EXP (128 - p) * c) * 2 EXP 128) * 2 EXP p + x` SUBST1_TAC THENL
   [SUBGOAL_THEN `2 EXP 256 = (2 EXP (128 - p) * 2 EXP 128) * 2 EXP p` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ARITH_TAC];
    ALL_TAC] THEN
  SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ; MOD_MULT_ADD]);;

let KP_SEED128 = prove
 (`!(seed:int64) SEED c j s.
     read (memory :> bytes(seed,32)) s = SEED /\ j + 16 <= 32 /\ c < 2 EXP 16
     ==> read (memory :> bytes128 (word_add seed (word j))) s =
         word_subword (word (SEED + 2 EXP 256 * c):272 word) (8 * j,128)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `SEED < 2 EXP 256` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`seed:int64`; `32`; `read memory (s:x86state)`] READ_BYTES_BOUND) THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(SPECL [`seed:int64`; `32`; `SEED:num`; `j:num`; `s:x86state`] KP_RD128) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`SEED + 2 EXP 256 * c`; `j:num`] KP_SUBW128) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 256 + 2 EXP 256 * c` THEN
    ASM_REWRITE_TAC[LT_ADD_RCANCEL] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 256 + 2 EXP 256 * c = 2 EXP 256 * (c + 1)`;
                ARITH_RULE `2 EXP 272 = 2 EXP 256 * 2 EXP 16`; LE_MULT_LCANCEL] THEN
    ASM_ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC KP_DIVMOD_HI THEN ASM_ARITH_TAC);;

(*** A piece of the state at the base of the state (state offset off) ***)

let KP_PIECE_THM sw base asl sn off len =
  let sz,lem = if len = 16 then "bytes128",KP_PIECE16 else "bytes8",KP_PIECE8 in
  let ftm = parse_term(Printf.sprintf "read (memory :> %s (word_add fb (word %d))) %s" sz (base + off) sn) in
  let fact = try snd(find (fun (_,th) -> let c = concl th in is_eq c && lhs c = ftm) asl)
             with Failure _ -> failwith ("KP_PIECE_THM: no fact "^string_of_term ftm) in
  let v = rhs(concl fact) in
  let a = parse_term(Printf.sprintf "word_add fb (word %d):int64" (base + off)) in
  let s = mk_var(sn,`:x86state`) in
  let inst = SPECL [sw; a; s; v; mk_small_numeral off] lem in
  let eqt = snd(dest_conj(fst(dest_imp(concl inst)))) in
  let eqth = prove(eqt, CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[KP_ZX_MOD8] THEN CONV_TAC WORD_BLAST) in
  MP inst (CONJ fact eqth);;

(* bytes(fb + base,n) = val sw MOD 2^(8n) at the state sn, as a chain *)
let KP_CHAIN_TAC sw base pieces sn =
  W(fun (asl,w) ->
    let s = mk_var(sn,`:x86state`) in
    let d = parse_term(Printf.sprintf "word_add fb (word %d):int64" base) in
    let x = mk_comb(`val:1600 word->num`,sw) in
    let cur0 = KP_NORM(prove(
      subst [s,`s:x86state`; x,`x:num`; d,`d:int64`]
       `read (memory :> bytes(d,0)) s = x MOD 2 EXP (8 * 0)`,
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; MULT_CLAUSES; EXP; MOD_1])) in
    let step (cur,j) (off,len) =
      assert (off = j);
      let pth = KP_NORM(KP_PIECE_THM sw base asl sn off len) in
      let ext = KP_NORM(SPECL [d; mk_small_numeral j; mk_small_numeral len; x; s] KP_BYTES_EXTEND) in
      (MP ext (CONJ cur pth), j + len) in
    let fin,n = rev_itlist (fun p st -> step st p) pieces (cur0,0) in
    ASSUME_TAC fin);;

let KP_MODLEMMA = prove(`!w:1600 word. val w MOD 2 EXP 1600 = val w`,
  GEN_TAC THEN MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `w:1600 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`]);;

(*** The 128 bytes squeezed from a state K in 8 chunks of 128 bits ***)

let KP_SQUEEZE_CHUNKS = prove
 (`!(a:int64) (K:1600 word) (s:x86state) n.
     n <= 12 /\
     (!q. q < n ==> read (memory :> bytes128 (word_add a (word (16 * q)))) s = word_subword K (128 * q,128))
     ==> !j. j < 16 * n ==> read (memory :> bytes8 (word_add a (word j))) s = word_subword K (8 * j,8)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j DIV 16`) THEN
  ANTS_TAC THENL [UNDISCH_TAC `j < 16 * n` THEN ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`word_add (a:int64) (word (16 * (j DIV 16)))`; `word_subword (K:1600 word) (128 * (j DIV 16),128):int128`; `j MOD 16`; `s:x86state`] SPONGE_BYTES8_OF_CHUNK128) THEN
  ASM_REWRITE_TAC[ARITH_RULE `j MOD 16 < 16`] THEN
  SUBGOAL_THEN `word_add (word_add (a:int64) (word (16 * (j DIV 16)))) (word (j MOD 16)) = word_add a (word j)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[SPONGE_SUBSUB128; ARITH_RULE `j MOD 16 < 16`] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(*** The squeezed bytes of SHAKE256 within the first block ***)

let KP_SHAKE_BYTE = prove
 (`!n P j. j < 136 ==> word_subword (keccak_f1600 (mld_shake256_state n P)) (8 * j,8) = mld_shake256_byte n P j`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mld_shake256_byte; mld_keccak_squeeze_byte] THEN
  SUBGOAL_THEN `(136 + j) DIV 136 = 1 /\ (136 + j) MOD 136 = j` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `j:num`; MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1`] THEN
    UNDISCH_TAC `j < 136` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `1 = SUC 0`; keccak_squeeze]);;

(* ------------------------------------------------------------------------- *)
(* SEED: from the copy of the seed (+0x2a) to the end of the zeroing of the  *)
(* state after the squeeze. The input M = SEED + 2^256 (k + 256 l) is copied *)
(* to rsp0 + 0xe0 (34 bytes); the state at rsp0 + 0x1e0 is zeroed, the       *)
(* input and the padding are put in it byte-wise, the state is permuted, its *)
(* 128 bytes are copied to rsp0 + 0x160 (rho, rho', key) and it is zeroed.   *)
(* ------------------------------------------------------------------------- *)

let KPSEED_STMT start exit k l preg =
  parse_term(subst_tokens
   ["@MC@",image_mc; "@S@",string_of_int start; "@X@",string_of_int exit;
    "@K@",string_of_int k; "@L@",string_of_int l; "@PR@",preg]
  "exists f_events.
   forall e rsp0 seed pk pc SEED.
     aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
     aligned 32 (rsp0:int64) /\\
     ALL (nonoverlapping (word_sub rsp0 (word 296),984))
         [(word pc,libmldsa_size); (seed,32)]
     ==> ensures x86
          (\\s. bytes_loaded s (word pc) @MC@ /\\
               read RIP s = word (pc + @S@) /\\
               read RSP s = rsp0 /\\ read RDX s = seed /\\ read RDI s = pk /\\
               read (memory :> bytes(seed,32)) s = SEED /\\
               read events s = e)
          (\\s. read RIP s = word (pc + @X@) /\\
               read RSP s = rsp0 /\\ read R14 s = pk /\\
               read @PR@ s = word_add rsp0 (word 384) /\\
               (!j. j < 128 ==> read (memory :> bytes8 (word_add rsp0 (word (352 + j)))) s =
                                mld_keypair_seedbuf @K@ @L@ SEED j) /\\
               (exists e2. read events s = APPEND e2 e /\\
                  e2 = f_events (word_sub rsp0 (word 296)) seed pc /\\
                  memaccess_inbounds e2
                   [seed,32; word_sub rsp0 (word 296),984;
                    word(pc + rodata_mld_KeccakF_RoundConstants),192]
                   [word_sub rsp0 (word 296),984]))
          (MAYCHANGE [RSP; R12; R14; R15] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub rsp0 (word 296),984)])");;

let KP_SEED_PIECES =
  [0,16; 16,1; 17,16; 33,1; 34,1] @ map (fun j -> j,1) (35--39) @
  map (fun j -> j,16) [40;56;72;88;104] @ map (fun j -> j,1) (120--135) @
  map (fun j -> j,16) [136;152;168;184];;

(* the bytesN at fb + 520 + j (the copy of M), from bytes(.,34) = M *)
let kp_m_fact rd subw j nb =
  let a = `word_add fb (word 520):int64` in
  let th1 = MP (SPECL [a;`34`;`M:num`;mk_small_numeral j;`s5:x86state`] rd)
    (CONJ (ASSUME `read (memory :> bytes(word_add fb (word 520),34)) s5 = M`)
      (EQT_ELIM(NUM_REDUCE_CONV (mk_binary "<=" (mk_binary "+" (mk_small_numeral j,mk_small_numeral nb),`34`))))) in
  let th2 = MP (SPECL [`M:num`; mk_small_numeral j] subw)
    (CONJ (ASSUME `M < 2 EXP 272`)
      (EQT_ELIM(NUM_REDUCE_CONV (mk_binary "<=" (mk_binary "+" (mk_binary "*" (`8`,mk_small_numeral j),mk_small_numeral (8*nb)),`272`))))) in
  KP_NORM(TRANS th1 th2);;

let KP_INBUF34 = prove
 (`!(d:int64) (s:x86state) SEED c.
     SEED < 2 EXP 256 /\ c < 2 EXP 16 /\
     read (memory :> bytes128 d) s = word_subword (word (SEED + 2 EXP 256 * c):272 word) (0,128) /\
     read (memory :> bytes128 (word_add d (word 16))) s = word_subword (word (SEED + 2 EXP 256 * c):272 word) (128,128) /\
     read (memory :> bytes16 (word_add d (word 32))) s = word c
     ==> read (memory :> bytes(d,34)) s = SEED + 2 EXP 256 * c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `SEED + 2 EXP 256 * c < 2 EXP 272` ASSUME_TAC THENL
   [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP 256 + 2 EXP 256 * c` THEN
    ASM_REWRITE_TAC[LT_ADD_RCANCEL] THEN
    REWRITE_TAC[ARITH_RULE `2 EXP 256 + 2 EXP 256 * c = 2 EXP 256 * (c + 1)`;
                ARITH_RULE `2 EXP 272 = 2 EXP 256 * 2 EXP 16`; LE_MULT_LCANCEL] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `34 = 16 + 18`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[ARITH_RULE `18 = 16 + 2`; READ_BYTES_COMBINE; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; KP_B16; KP_B2] THEN
  CONV_TAC(DEPTH_CONV(NUM_ADD_CONV ORELSEC NUM_MULT_CONV)) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD; DIMINDEX_16; DIMINDEX_128] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  REWRITE_TAC[ARITH_RULE `MIN 128 128 = 128`; ARITH_RULE `MIN 128 (272 - 0) = 128`; ARITH_RULE `MIN 128 (272 - 128) = 128`] THEN
  ASM_SIMP_TAC[MOD_LT; EXP; DIV_1] THEN
  MP_TAC(SPECL [`SEED:num`; `c:num`; `128`] KP_DIVMOD_HI) THEN
  MP_TAC(REWRITE_RULE[EXP; DIV_1; ADD_CLAUSES] (SPECL [`SEED:num`; `c:num`; `0`] KP_DIVMOD_HI)) THEN
  REWRITE_TAC[ARITH_RULE `0 + 128 <= 256`; ARITH_RULE `128 + 128 <= 256`] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  SUBGOAL_THEN `(SEED DIV 2 EXP 128) MOD 2 EXP 128 = SEED DIV 2 EXP 128` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
    ASM_REWRITE_TAC[ARITH_RULE `128 + 128 = 256`];
    ALL_TAC] THEN
  MP_TAC(SPECL [`SEED:num`; `2 EXP 128`] DIVISION) THEN
  REWRITE_TAC[EXP_EQ_0; ARITH_EQ; ARITH_RULE `2 EXP 256 = 2 EXP 128 * 2 EXP 128`] THEN
  ARITH_TAC);;

let KP_INBUF34M = prove
 (`!(d:int64) (s:x86state) SEED c M.
     SEED + 2 EXP 256 * c = M /\ SEED < 2 EXP 256 /\ c < 2 EXP 16 /\
     read (memory :> bytes128 d) s = word_subword (word M:272 word) (0,128) /\
     read (memory :> bytes128 (word_add d (word 16))) s = word_subword (word M:272 word) (128,128) /\
     read (memory :> bytes16 (word_add d (word 32))) s = word c
     ==> read (memory :> bytes(d,34)) s = M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if rhs(concl th) = `M:num` then SUBST_ALL_TAC(SYM th) else NO_TAC) THEN
  MATCH_MP_TAC KP_INBUF34 THEN ASM_REWRITE_TAC[]);;


let KPSEED_EXEC start exit = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(start, exit)];;

(* the bytes of the copy of the input at fb + 520 as subwords of word M *)
let KP_INBUF_FACTS_TAC =
  MAP_EVERY (fun (rd,sw,j,nb) -> ASSUME_TAC(kp_m_fact rd sw j nb))
   [KP_RD8,KP_SUBW8,16,1; KP_RD64,KP_SUBW64,25,8; KP_RD64,KP_SUBW64,17,8; KP_RD8,KP_SUBW8,33,1];;

let KPSEED_TAC_A execth k l =
  let klt = parse_term(Printf.sprintf "%d + 256 * %d" k l) in
  let meq = mk_eq(mk_binary "+" (`SEED:num`,mk_binary "*" (`2 EXP 256`,klt)),`M:num`) in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERM" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(fb:int64) (seed:int64) (pc:num). f_ev_all fb seed pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  X_GEN_TAC `e:(uarch_event)list` THEN WORD_FORALL_OFFSET_TAC 296 THEN
  MAP_EVERY X_GEN_TAC [`fb:int64`; `seed:int64`; `pk:int64`; `pc:num`; `SEED:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; NONOVERLAPPING_CLAUSES;
              fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  TR_ALIGNED_TAC 296 (map (fun q -> 16 * q) (14--42)) THEN
  MAP_EVERY (fun n -> GHOST_INTRO_TAC (mk_var(Printf.sprintf "ymm%d_init" n,`:int256`))
                       (parse_term(Printf.sprintf "read YMM%d" n))) [0;1;2;3] THEN
  FULL_INIT_TAC THEN
  SUBGOAL_THEN `SEED < 2 EXP 256` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`seed:int64`; `32`; `read memory (s0:x86state)`] READ_BYTES_BOUND) THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ABBREV_TAC (mk_eq(`M:num`,lhs meq)) THEN
  SUBGOAL_THEN `M < 2 EXP 272` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN UNDISCH_TAC `SEED < 2 EXP 256` THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY (fun j ->
    ASSUME_TAC(REWRITE_RULE[ASSUME meq; WORD_ADD_0] (REWRITE_RULE[ARITH_RULE `8 * 16 = 128`; ARITH_RULE `8 * 0 = 0`]
      (MP (SPECL [`seed:int64`; `SEED:num`; klt; mk_small_numeral j; `s0:x86state`] KP_SEED128)
          (CONJ (ASSUME `read (memory :> bytes(seed,32)) s0 = SEED`)
                (EQT_ELIM(NUM_REDUCE_CONV(mk_conj(mk_binary "<=" (mk_binary "+" (mk_small_numeral j,`16`),`32`),
                                                  mk_binary "<" (klt,`2 EXP 16`))))))))))
   [0;16] THEN
  VERIF_SSE_STEPS_TAC execth (1--5);;



let KPSEED_TAC_B k l =
  let klt = parse_term(Printf.sprintf "%d + 256 * %d" k l) in
  SUBGOAL_THEN `read (memory :> bytes(word_add fb (word 520),34)) s5 = M` ASSUME_TAC THENL
   [MATCH_MP_TAC KP_INBUF34M THEN
    MAP_EVERY EXISTS_TAC [`SEED:num`; klt] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  KP_INBUF_FACTS_TAC;;

let KPSEED_TAC_C execth =
  VERIF_SSE_STEPS_TAC execth (6--18) THEN
  kp_zfact "s18" 800 801 8 THEN
  MAP_EVERY (fun k -> kp_zfact "s18" 800 k 1) (809--815) THEN
  MAP_EVERY (fun k -> kp_zfact "s18" 896 k 1) (896--911) THEN
  VERIF_SSE_STEPS_TAC execth (19--37);;

let KPSEED_TAC_D execth =
  FIRST_X_ASSUM(fun th -> if can (term_match [] `read (memory :> bytes(word_add fb (word 776),200)) s37 = x`) (concl th)
     then ASSUME_TAC(REWRITE_RULE[KP_MODLEMMA; GSYM READ_MEMORY_WBYTES_1600] th) else NO_TAC) THEN
  FIRST_X_ASSUM(fun th -> if can (term_match [] `read (memory :> wbytes (word_add fb (word 776))) s37 = x`) (concl th)
     then ASSUME_TAC(REWRITE_RULE[GSYM(MP (SPEC `M:num` KP_S_WORD) (ASSUME `M < 2 EXP 272`))] th) else NO_TAC) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc execth "H_PERM"
   [`read RDI s`; `mld_shake256_state 34 M`; `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   [`fb:int64`; `seed:int64`; `pc:num`] 38 THEN
  YMM_GHOST_TAC `s38:x86state` ["YMM0","y0_s"; "YMM1","y1_s"; "YMM2","y2_s"; "YMM3","y3_s"] THEN
  TR_STATE_CHUNKS_TAC `word_add fb (word 776):int64` (0--7) [];;

(* the 128 bytes at fb + 648 after the copy, as mld_keypair_seedbuf *)
let KPSEED_TAC_E execth k l =
  let klt = parse_term(Printf.sprintf "%d + 256 * %d" k l) in
  let meq = mk_eq(mk_binary "+" (`SEED:num`,mk_binary "*" (`2 EXP 256`,klt)),`M:num`) in
  VERIF_SSE_STEPS_TAC execth (39--69) THEN
  SUBGOAL_THEN `!j. j < 128 ==> read (memory :> bytes8 (word_add fb (word (648 + j)))) s69 =
                    word_subword (keccak_f1600 (mld_shake256_state 34 M)) (8 * j,8)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`word_add fb (word 648):int64`; `keccak_f1600 (mld_shake256_state 34 M)`; `s69:x86state`; `8`]
                 KP_SQUEEZE_CHUNKS) THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    ANTS_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN ASM_REWRITE_TAC[];
      SIMP_TAC[ARITH_RULE `16 * 8 = 128`]];
    ALL_TAC] THEN
  SUBGOAL_THEN (parse_term(Printf.sprintf "!j. j < 128 ==> read (memory :> bytes8 (word_add fb (word (648 + j)))) s69 =
                    mld_keypair_seedbuf %d %d SEED j" k l)) ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[mld_keypair_seedbuf; ASSUME meq] THEN
    MATCH_MP_TAC KP_SHAKE_BYTE THEN ASM_ARITH_TAC;
    ALL_TAC];;

let KPSEED_TAC_F =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      REWRITE_TAC[ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
      ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The whole region: start and exit as offsets in the image, k and l the
     dimensions of the parameter set, preg the register that the code leaves
     pointing at rho' (rsp0 + 0x180) ***)

let KPSEED_TAC execth k l =
  KPSEED_TAC_A execth k l THEN KPSEED_TAC_B k l THEN KPSEED_TAC_C execth THEN
  KP_CHAIN_TAC KP_SW 776 KP_SEED_PIECES "s37" THEN
  KPSEED_TAC_D execth THEN KPSEED_TAC_E execth k l THEN KPSEED_TAC_F;;

let PROVE_KPSEED start exit k l preg =
  prove(KPSEED_STMT start exit k l preg, KPSEED_TAC (KPSEED_EXEC start exit) k l);;

(* ------------------------------------------------------------------------- *)
(* PACK2: the inlined mld_polyeta_pack for eta = 2 (ML-DSA-44 and -87), from *)
(* the head of its loop to the exit: 32 iterations of 8 coefficients of the  *)
(* polynomial at a (whose low bytes the code loads at [rcx - 0x1c + 4 m],    *)
(* RCX = a + 28 + 32 i) into 3 bytes of the key at rb + ob + 3 i ([rbx + rax *)
(* - 2 + k], RAX = a0 + 3 i, a0 = ob + 2). The code computes in byte         *)
(* registers, so the upper bytes of R8, R9, RSI and the temporary register   *)
(* treg are carried over from the previous iteration as ghosts, and the      *)
(* values of the stores are reduced to bytes (KP_BYTE_RULES) before the      *)
(* comparison with mld_polyeta_pack_2 by bit-blasting. dreg and treg are the *)
(* registers that the instance uses besides the fixed ones.                  *)
(* ------------------------------------------------------------------------- *)

let KPPACK2_STMT fn loop exit ob a0 dreg treg =
  parse_term(subst_tokens
   ["@MC@",image_mc; "@FN@",fn; "@L@",loop; "@X@",exit;
    "@A0@",string_of_int a0; "@OB@",string_of_int ob; "@D@",dreg; "@T@",treg]
  "exists f_events.
  forall e rb a pc (x:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    ALL (nonoverlapping (word_add rb (word @OB@),96))
        [(word pc,libmldsa_size); (a,1024)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) @MC@ /\\
              read RIP s = word (pc + @FN@_@L@) /\\
              read RBX s = rb /\\ read RAX s = word @A0@ /\\
              read RCX s = word_add a (word 28) /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add a (word (4 * i)))) s = x i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + @FN@_@X@) /\\
              (!j. j < 96 ==> read (memory :> bytes8 (word_add rb (word (@OB@ + j)))) s =
                              mld_polyeta_pack_2 x j) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rb a pc /\\
                 memaccess_inbounds e2 [a,1024; word_add rb (word @OB@),96]
                                       [word_add rb (word @OB@),96]))
         (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11; @D@; @T@] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(word_add rb (word @OB@),96)])");;

let KPPACK2_INV ob a0 = parse_term(subst_tokens
   ["@A0@",string_of_int a0; "@OB@",string_of_int ob]
  "\\i s. read RBX s = rb /\\ read RAX s = word (@A0@ + 3 * i) /\\
         read RCX s = word_add (word_add a (word (32 * i))) (word 28) /\\
         (!j. j < 256 ==> read (memory :> bytes32 (word_add a (word (4 * j)))) s = (x:num->int32) j) /\\
         (!j. j < 3 * i ==> read (memory :> bytes8 (word_add rb (word (@OB@ + j)))) s =
                            mld_polyeta_pack_2 x j)");;

let KPPACK2_EXEC fn loop exit = X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
     [(layout (fn^"_"^loop), layout (fn^"_"^exit))];;

(*** Rules for the values of the byte registers after the simulation: the
     low byte of word_join h l is l, also through zero extensions ***)

let KP_BYTE_RULES = map (fun t -> prove(t, REPEAT GEN_TAC THEN TRY(REWRITE_TAC[KP_ZX_MOD8]) THEN CONV_TAC WORD_BLAST))
  [`!(h:56 word) (l:byte). word (val (word_join h l:int64) MOD 256):byte = l`;
   `!(h:56 word) (l:byte). word_zx (word_join h l:int64):byte = l`;
   `!(h:56 word) (l:byte). word (val (word_zx (word_zx (word_join h l:int64):int32):int64) MOD 256):byte = l`;
   `!(h:56 word) (l:byte). word_zx (word_zx (word_zx (word_join h l:int64):int32):int64):byte = l`;
   `!(x:byte). word (val (word_zx (word_zx x:int32):int64) MOD 256):byte = x`;
   `!(x:byte). word_zx (word_zx (word_zx x:int32):int64):byte = x`;
   `!(x:byte). word (val (word_zx x:int64) MOD 256):byte = x`];;

let KP_ADD_MOD = prove
 (`!(x:N word) (y:M word). word (val x MOD 256 + val y MOD 256):byte = word_add (word_zx x) (word_zx y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_ADD; KP_ZX_MOD8]);;

let KP_DIV3_0 = prove
 (`(3 * i) DIV 3 = i /\ (3 * i) MOD 3 = 0`,
  MATCH_MP_TAC(REWRITE_RULE[ADD_CLAUSES] (SPECL [`3`;`i:num`;`0`] DIVMOD_CHUNK)) THEN ARITH_TAC);;

(*** Aliases for the addresses [rbx + rax - 2] and [rbx + rax - 1] with RAX =
     word(a0 + 3 i), as the simulation writes them ***)

let KP_ALIAS_TAC = REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN AP_TERM_TAC THEN
  W(fun (asl,w) ->
    let a = rand(lhs w) and b = rand(rhs w) in
    if a = b then REFL_TAC else
    let eq = (try ARITH_RULE(mk_eq(a,mk_binop `(+):num->num->num` b `18446744073709551616`))
              with Failure _ -> ARITH_RULE(mk_eq(a,b))) in
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [eq] THEN
    REWRITE_TAC[WORD_ADD; WORD_REDUCE_CONV `word 18446744073709551616:int64`; WORD_ADD_0]);;

let kp_alias l r = SUBGOAL_THEN (parse_term (Printf.sprintf
  "word_add (rb:int64) (word (%s)) = word_add rb (word (%s))" l r)) ASSUME_TAC THENL [KP_ALIAS_TAC; ALL_TAC];;

let KP_PACK_ALIASES a0 =
  let f = Printf.sprintf in
  MAP_EVERY (fun (l,r) -> kp_alias l r)
   [f "1 * (%d + 3 * i) + 18446744073709551614" a0, f "%d + 3 * i" (a0 - 2);
    f "(%d + 3 * i) + 18446744073709551614" a0, f "%d + 3 * i" (a0 - 2);
    f "1 * (%d + 3 * i) + 18446744073709551615" a0, f "%d + 3 * i" (a0 - 1);
    f "(%d + 3 * i) + 18446744073709551615" a0, f "%d + 3 * i" (a0 - 1);
    f "1 * (%d + 3 * i)" a0, f "%d + 3 * i" a0];;

(*** The end of an iteration: outputs 3 i + k at rb + (ob + 3 i + k) ***)

let KP_PACK_FINAL_TAC ob =
  let rules = chunk_rules 3 in
  let addr_eqs = map (fun k -> ARITH_RULE(parse_term(Printf.sprintf
                   "(%d + 3 * i) + %d = %d + 3 * i" ob k (ob + k)))) [1;2] in
  RULE_ASSUM_TAC(fun th -> let c = concl th in
    if is_eq c && can (term_match [] `read (memory :> bytes8 a) (s:x86state)`) (lhs c) &&
       has_sub `rb:int64` c
    then REWRITE_RULE (KP_ADD_MOD :: KP_BYTE_RULES) th else th) THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read R8 s = x`; `read R9 s = x`; `read R10 s = x`; `read R11 s = x`;
    `read R12 s = x`; `read R13 s = x`; `read R15 s = x`;
    `read RSI s = x`; `read RDI s = x`; `read RDX s = x`] THEN
  ADDR_NORMALIZE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(REWRITE_TAC[CHUNK_OUTPUT_SPLIT] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      REWRITE_TAC[ADD_CLAUSES; ADD_ASSOC] THEN REWRITE_TAC addr_eqs THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[mld_polyeta_pack_2] THEN
      REWRITE_TAC[rules; KP_DIV3_0] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES] THEN
      REPEAT CONJ_TAC THEN APP_BLAST_TAC `x:num->int32` THEN
      NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let KPPACK2_TAC fn loop exit ob a0 dreg treg =
  let execth = KPPACK2_EXEC fn loop exit in
  let ghosts = ["R8"; "R9"; "RSI"; treg] in
  CONCRETIZE_F_EVENTS_TAC
   `\(rb:int64) (a:int64) (pc:num).
      APPEND (f_ev_epil rb a pc)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop rb a pc i)) (f_ev_prol rb a pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rb:int64`; `a:int64`; `pc:num`; `x:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32`
   (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (KPPACK2_INV ob a0) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0; ADD_CLAUSES] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MAP_EVERY (fun r -> GHOST_INTRO_TAC (mk_var(String.lowercase_ascii r ^ "_g",`:int64`))
                         (parse_term ("read " ^ r))) ghosts THEN
    FULL_INIT_TAC THEN
    CHUNK_INPUT_TAC `x:num->int32` 8 THEN
    INPUT_BYTES_SPLIT_TAC `a:int64` THEN
    INPUT_ALT_ADDR_TAC `a:int64` THEN
    SUBGOAL_THEN (parse_term(Printf.sprintf "val(word(%d + 3 * i):int64) = %d + 3 * i" a0 a0)) ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN UNDISCH_TAC `i < 32` THEN ARITH_TAC; ALL_TAC] THEN
    KP_PACK_ALIASES a0 THEN
    X86_STEPS_TAC execth (1--46) THEN
    KP_PACK_FINAL_TAC ob;
    FULL_EXIT0_TAC];;

let PROVE_KPPACK2 fn loop exit ob a0 dreg treg =
  prove(KPPACK2_STMT fn loop exit ob a0 dreg treg, KPPACK2_TAC fn loop exit ob a0 dreg treg);;

(* ------------------------------------------------------------------------- *)
(* PACK2B: the same packing in the form of the first loop of                 *)
(* mldsa87_keypair_internal, which indexes the polynomial at rsp0 + cb by    *)
(* RCX = 28 + 32 i ([rsp + rcx + cb - 28 + 4 m]) and points into the key     *)
(* with RAX = rb + ob + 2 + 3 i ([rax - 2 + k]).                             *)
(* ------------------------------------------------------------------------- *)

let KPPACK2B_STMT fn loop exit ob cb =
  parse_term(subst_tokens
   ["@MC@",image_mc; "@FN@",fn; "@L@",loop; "@X@",exit;
    "@A0@",string_of_int (ob + 2); "@OB@",string_of_int ob; "@CB@",string_of_int cb]
  "exists f_events.
  forall e rb rsp0 pc (x:num->int32).
    aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
    ALL (nonoverlapping (word_add rb (word @OB@),96))
        [(word pc,libmldsa_size); (word_add rsp0 (word @CB@),1024)]
    ==> ensures x86
         (\\s. bytes_loaded s (word pc) @MC@ /\\
              read RIP s = word (pc + @FN@_@L@) /\\
              read RSP s = rsp0 /\\ read RAX s = word_add rb (word @A0@) /\\
              read RCX s = word 28 /\\
              (!i. i < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (@CB@ + 4 * i)))) s = x i) /\\
              read events s = e)
         (\\s. read RIP s = word (pc + @FN@_@X@) /\\
              read RSP s = rsp0 /\\
              (!j. j < 96 ==> read (memory :> bytes8 (word_add rb (word (@OB@ + j)))) s =
                              mld_polyeta_pack_2 x j) /\\
              (exists e2. read events s = APPEND e2 e /\\ e2 = f_events rb rsp0 pc /\\
                 memaccess_inbounds e2 [word_add rsp0 (word @CB@),1024; word_add rb (word @OB@),96]
                                       [word_add rb (word @OB@),96]))
         (MAYCHANGE [RIP; RAX; RCX; RDX; RSI; RDI; R8; R9; R10; R11; R12; R13] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(word_add rb (word @OB@),96)])");;

let KPPACK2B_INV ob cb = parse_term(subst_tokens
   ["@A0@",string_of_int (ob + 2); "@OB@",string_of_int ob; "@CB@",string_of_int cb]
  "\\i s. read RSP s = rsp0 /\\ read RAX s = word_add rb (word (@A0@ + 3 * i)) /\\
         read RCX s = word (28 + 32 * i) /\\
         (!j. j < 256 ==> read (memory :> bytes32 (word_add rsp0 (word (@CB@ + 4 * j)))) s = (x:num->int32) j) /\\
         (!j. j < 3 * i ==> read (memory :> bytes8 (word_add rb (word (@OB@ + j)))) s =
                            mld_polyeta_pack_2 x j)");;

let kp_alias_b base l r = SUBGOAL_THEN (parse_term (Printf.sprintf
  "word_add (%s:int64) (word (%s)) = word_add %s (word (%s))" base l base r)) ASSUME_TAC THENL [KP_ALIAS_TAC; ALL_TAC];;

let KP_PACKB_ALIASES ob cb =
  let f = Printf.sprintf in
  MAP_EVERY (fun m ->
    let d = cb - 28 + 4 * m in
    kp_alias_b "rsp0" (f "1 * (28 + 32 * i) + %d" d) (if m = 0 then f "%d + 32 * i" cb else f "%d + 32 * i + %d" cb (4 * m)))
   (0--7) THEN
  MAP_EVERY (fun (k,r) ->
    SUBGOAL_THEN (parse_term (f "word_add (word_add (rb:int64) (word (%d + 3 * i))) (word %s) = word_add rb (word (%d + 3 * i))" (ob + 2) k r))
      ASSUME_TAC THENL [KP_ALIAS_TAC; ALL_TAC])
   ["18446744073709551614", ob; "18446744073709551615", ob + 1];;

let KPPACK2B_TAC fn loop exit ob cb =
  let execth = KPPACK2_EXEC fn loop exit in
  CONCRETIZE_F_EVENTS_TAC
   `\(rb:int64) (rsp0:int64) (pc:num).
      APPEND (f_ev_epil rb rsp0 pc)
       (APPEND (ENUMERATEL 32 (\i. f_ev_loop rb rsp0 pc i)) (f_ev_prol rb rsp0 pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `rb:int64`; `rsp0:int64`; `pc:num`; `x:num->int32`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES; ALL; fst execth] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32`
   (parse_term(Printf.sprintf "pc + %s_%s" fn loop))
   (parse_term(Printf.sprintf "pc + %s_%s" fn exit))
   (KPPACK2B_INV ob cb) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FULL_INIT_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0; ADD_CLAUSES] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MAP_EVERY (fun r -> GHOST_INTRO_TAC (mk_var(String.lowercase_ascii r ^ "_g",`:int64`))
                         (parse_term ("read " ^ r))) ["R8"; "R9"; "RSI"; "R13"] THEN
    FULL_INIT_TAC THEN
    CHUNK_INPUT_TAC `x:num->int32` 8 THEN
    INPUT_BYTES_SPLIT_TAC `rsp0:int64` THEN
    SUBGOAL_THEN `val(word(28 + 32 * i):int64) = 28 + 32 * i` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN UNDISCH_TAC `i < 32` THEN ARITH_TAC; ALL_TAC] THEN
    KP_PACKB_ALIASES ob cb THEN
    X86_STEPS_TAC execth (1--46) THEN
    KP_PACK_FINAL_TAC ob;
    FULL_EXIT0_TAC];;

let PROVE_KPPACK2B fn loop exit ob cb =
  prove(KPPACK2B_STMT fn loop exit ob cb, KPPACK2B_TAC fn loop exit ob cb);;


(* ------------------------------------------------------------------------- *)
(* HASHR: the inlined SHAKE256 of the public key of keypair_internal, as     *)
(* HASHB of inline_keygen.ml (whose tactic it uses unchanged) but with the  *)
(* key pointer in the register preg (R14) instead of a stack slot, and the   *)
(* register sreg (R13) that the code sets to the state.                      *)
(* ------------------------------------------------------------------------- *)

let PKHB_STMT_R fn head exitl soff preg sreg plen rlen wlen = parse_term(subst_tokens
 ["@FN@",fn; "@MC@",image_mc; "@START@",string_of_int head; "@EXIT@",exitl;
  "@SA@",pk_rsp0_add soff; "@PR@",preg; "@SR@",sreg; "@PLEN@",string_of_int plen;
  "@RLEN@",string_of_int rlen; "@WLEN@",string_of_int wlen]
 "exists f_events.
   forall e rsp0 pk pc PK.
     aligned 4096 (word pc:int64) /\\ pc + libmldsa_size <= 2 EXP 64 /\\
     aligned 32 (rsp0:int64) /\\
     ALL (nonoverlapping (word_sub rsp0 (word 296),@RLEN@))
         [(word pc,libmldsa_size); (pk,@PLEN@)]
     ==> ensures x86
          (\\s. bytes_loaded s (word pc) @MC@ /\\
               read RIP s = word (pc + @START@) /\\
               read RSP s = rsp0 /\\ read @PR@ s = pk /\\
               read (memory :> bytes(pk,@PLEN@)) s = PK /\\
               read events s = e)
          (\\s. read RIP s = word (pc + @FN@_@EXIT@) /\\
               read RSP s = rsp0 /\\
               read (memory :> wbytes (@SA@)) s =
               keccak_f1600 (mld_shake256_state @PLEN@ PK) /\\
               (exists e2. read events s = APPEND e2 e /\\
                  e2 = f_events (word_sub rsp0 (word 296)) pk pc /\\
                  memaccess_inbounds e2
                   [pk,@PLEN@; word_sub rsp0 (word 296),@RLEN@;
                    word(pc + rodata_mld_KeccakF_RoundConstants),192]
                   [word_sub rsp0 (word 296),@WLEN@]))
          (MAYCHANGE [RSP; @SR@] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub rsp0 (word 296),@WLEN@)])");;

let PROVE_PKHASHB_R fn head exitl soff preg sreg plen rlen wlen c =
  prove(PKHB_STMT_R fn head exitl soff preg sreg plen rlen wlen,
        PKHB_TAC_C plen soff c (PKHB_EXEC fn head exitl));;
