(* ========================================================================= *)
(* gcm_ghash_v8_s2n: the BYTE-LIST-shaped export.                                 *)
(*                                                                           *)
(* `arm/proofs/gcm_ghash_v8_s2n.ml` proves GCM_GHASH_V8_CORRECT and its subroutine *)
(* wrapper with the input quantified as `blk:num->int128`, read through        *)
(* `bytes128` at 16-byte strides.  That is the right shape for the simulation  *)
(* content, but the composition target -- the AES-GCM encrypt/decrypt kernels  *)
(* in arm/proofs/aesv8_gcm_8x_dec_256_wb.ml -- states its GHASH obligation in  *)
(* the `byte_list_at` / `nist_input_block` vocabulary instead.  This file      *)
(* restates both theorems in that vocabulary.                                  *)
(*                                                                           *)
(* It is a SEPARATE file rather than an addition to gcm_ghash_v8_s2n.ml on purpose. *)
(* `nist_input_block`'s body needs `bytes_to_int128`, which lives in           *)
(* arm/proofs/utils/aes_xts_common_spec.ml -- outside gcm_ghash_v8_s2n.ml's        *)
(* deliberately minimal three-`needs` closure (see the comment at              *)
(* gcm_ghash_v8_s2n.ml:391, which records that lifting it there made              *)
(* `new_definition` raise "term not closed", a raise `loadt` SWALLOWS, silently *)
(* voiding every later definition).  Keeping the widened closure in a          *)
(* downstream file leaves the certified nineteen-theorem file untouched.        *)
(*                                                                           *)
(* Everything here is a COROLLARY: no simulation, no new machine reasoning.    *)
(* The whole content is (a) the input bridge byte_list_at -> per-lane bytes128  *)
(* reads, and (b) the observation that `nist_input_block` IS                    *)
(* `word_bytereverse o (\i. bytes_to_int128 (SUB_LIST (16*i,16) x))`, which is  *)
(* exactly the `MAP word_bytereverse (list_of_seq blk n)` the core theorem's    *)
(* postcondition already carries.                                              *)
(* ========================================================================= *)

needs "arm/proofs/gcm_ghash_v8_s2n.ml";;
needs "arm/proofs/utils/aes_xts_common.ml";;

(* ------------------------------------------------------------------------- *)
(* The three items lifted from arm/proofs/aesv8_gcm_8x_dec_256_wb.ml.  They    *)
(* are copied rather than `needs`-ed because that file is 940 KB of decrypt     *)
(* proof whose load cost is unrelated to anything here.  Provenance:           *)
(*   nist_input_block             decrypt :7646                                *)
(*   BYTE_LIST_AT_TO_READ_BYTES   decrypt :7394                                *)
(*   INPUT_BYTES_TO_BYTE128_LANES decrypt :3362                                *)
(* All three are re-proved here from `common/`+`aes_xts_common` primitives, so  *)
(* they cannot silently drift into a weaker statement than the decrypt file's.  *)
(* ------------------------------------------------------------------------- *)

let nist_input_block = new_definition
 `nist_input_block (x:byte list) (i:num) : int128 =
    word_reversefields 8 (bytes_to_int128 (SUB_LIST (16 * i, 16) x))`;;

let BYTE_LIST_AT_TO_READ_BYTES = prove
 (`!bl (ptr:int64) (len:int64) s.
    byte_list_at bl ptr len s /\ LENGTH bl = val len
    ==> read (memory :> bytes (ptr, val len)) s = num_of_bytelist bl`,
  REPEAT GEN_TAC THEN REWRITE_TAC[byte_list_at] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `num_of_bytelist (bl:byte list) =
    num_of_bytelist (SUB_LIST (0, val (len:int64)) bl)`
  SUBST1_TAC THENL
   [AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`val (len:int64)`; `ptr:int64`; `bl:byte list`; `s:armstate`]
    BYTE_LIST_TO_NUM_THM) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN DISCH_THEN(fun th -> ASM_REWRITE_TAC[GSYM th]));;

let INPUT_BYTES_TO_BYTE128_LANES = prove
 (`!n (in_p:int64) (x:byte list) s.
    16 * n <= LENGTH x /\
    read (memory :> bytes (in_p, 16 * n)) s =
    num_of_bytelist (SUB_LIST (0, 16 * n) x)
    ==> !k. k < n
            ==> read (memory :> bytes128 (word_add in_p (word (16 * k)))) s =
                bytes_to_int128 (SUB_LIST (16 * k, 16) x)`,
  INDUCT_TAC THENL [REWRITE_TAC[LT]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`in_p:int64`; `16 * n`; `x:byte list`; `s:armstate`]
    READ_BYTES_AND_BYTE128_MERGE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ARITH_RULE `16 * n + 16 = 16 * SUC n`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ARITH_RULE `16 * n + 16 = 16 * SUC n`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[LT] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`in_p:int64`; `x:byte list`; `s:armstate`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The vocabulary bridge, and the ONE reason this export is nearly free:      *)
(* `nist_input_block x` is literally `word_bytereverse o <the raw lane        *)
(* function>` (`BREV_RF8_128` relates `word_reversefields 8` to               *)
(* `word_bytereverse`), and GCM_GHASH_V8_CORRECT's postcondition already reads  *)
(* `MAP word_bytereverse (list_of_seq blk n)`.  So instantiating `blk` at the  *)
(* raw lane function turns the existing postcondition into this one by         *)
(* rewriting alone.                                                           *)
(*                                                                           *)
(* SPELLING TRAP: the obvious `REWRITE_TAC[MAP_LIST_OF_SEQ; o_DEF;            *)
(* nist_input_block; BREV_RF8_128]` does NOT close it.  Rewriting              *)
(* `nist_input_block` under the binder captures the bound index into the       *)
(* `x:byte list` slot (both print as `x`, so the resulting goal looks correct  *)
(* and is not), leaving `list_of_seq (\x. ... (SUB_LIST (16*x,16) x)) n`.      *)
(* Push MAP through FIRST, then go under the lambda via AP_THM_TAC/AP_TERM_TAC  *)
(* + FUN_EQ_THM so the definition is only ever rewritten at a fixed index.     *)
(* ------------------------------------------------------------------------- *)

let NIST_INPUT_BLOCK_LIST = prove
 (`!(bl:byte list) n.
     list_of_seq (nist_input_block bl) n =
     MAP word_bytereverse
       (list_of_seq (\i. bytes_to_int128 (SUB_LIST (16 * i, 16) bl)) n)`,
  REWRITE_TAC[MAP_LIST_OF_SEQ; o_DEF] THEN
  REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN REWRITE_TAC[nist_input_block; BREV_RF8_128]);;

(* ------------------------------------------------------------------------- *)
(* THE EXPORT.  Reading guide: under the standard nonoverlapping side          *)
(* conditions, given the H table for `ghash_twist H` at htbl_p, the 16*n input  *)
(* bytes `ibytes` at in_p, and the tag at xi_p holding `word_bytereverse tag0`  *)
(* (the byte-reversed form the aws-lc caller keeps), gcm_ghash_v8_s2n replaces the  *)
(* tag with the byte-reversed SP 800-38D GHASH of those bytes folded onto tag0  *)
(* under the NIST hash key H.  Same vocabulary as the decrypt bands'           *)
(* AESV8_GCM_8X_DEC_256_{1..8}BLOCK, so the two compose directly.              *)
(* ------------------------------------------------------------------------- *)

let GCM_GHASH_V8_CORRECT_BYTES = prove
 (`!xi_p htbl_p in_p pc H h (tag0:int128) (ibytes:byte list) n.
     h = ghash_twist H /\ 1 <= n /\ 16 * n < 2 EXP 64 /\
     LENGTH ibytes = 16 * n /\
     nonoverlapping (word pc, LENGTH ghash_v8_mc) (xi_p,16) /\
     nonoverlapping (xi_p,16) (in_p,16 * n) /\
     nonoverlapping (xi_p,16) (htbl_p,96)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) ghash_v8_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [xi_p; htbl_p; in_p; word (16 * n)] s /\
               read (memory :> bytes128 xi_p) s = word_bytereverse tag0 /\
               byte_list_at ibytes in_p (word (16 * n)) s /\
               htable_mem_4 h htbl_p s)
          (\s. (read PC s = word (pc + 0x168) \/
                read PC s = word (pc + 0x4c0)) /\
               read (memory :> bytes128 xi_p) s =
               word_bytereverse
                 (nist_ghash H tag0 (list_of_seq (nist_input_block ibytes) n)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(xi_p:int64,16)] ,,
           MAYCHANGE [Q0;Q1;Q2;Q3;Q4;Q5;Q6;Q7;
                      Q16;Q17;Q18;Q19;Q20;Q21;Q22;Q23;Q24;Q25;Q26;Q27;Q28;
                      Q29;Q30;Q31])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  EXISTS_TAC
   `\s:armstate.
      aligned_bytes_loaded s (word pc) ghash_v8_mc /\
      read PC s = word pc /\
      C_ARGUMENTS [xi_p; htbl_p; in_p; word (16 * n)] s /\
      read (memory :> bytes128 xi_p) s = word_bytereverse tag0 /\
      (!i. i < n
           ==> read (memory :> bytes128 (word_add in_p (word (16 * i)))) s =
               bytes_to_int128 (SUB_LIST (16 * i, 16) ibytes)) /\
      htable_mem_4 h htbl_p s` THEN
  CONJ_TAC THENL
   [(* --- the input bridge: byte_list_at -> the n per-lane bytes128 reads --- *)
    X_GEN_TAC `s:armstate` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `val (word (16 * n):int64) = 16 * n` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN ASM_SIMP_TAC[MOD_LT]; ALL_TAC] THEN
    MATCH_MP_TAC INPUT_BYTES_TO_BYTE128_LANES THEN
    ASM_REWRITE_TAC[LE_REFL] THEN
    SUBGOAL_THEN `SUB_LIST (0, 16 * n) (ibytes:byte list) = ibytes` SUBST1_TAC THENL
     [MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[LE_REFL];
      ALL_TAC] THEN
    MP_TAC(SPECL [`ibytes:byte list`; `in_p:int64`; `word (16 * n):int64`;
                  `s:armstate`] BYTE_LIST_AT_TO_READ_BYTES) THEN
    ASM_REWRITE_TAC[];
    (* --- the core theorem, input instantiated at the raw lane function --- *)
    REWRITE_TAC[NIST_INPUT_BLOCK_LIST] THEN
    MP_TAC(SPECL
      [`xi_p:int64`; `htbl_p:int64`; `in_p:int64`; `pc:num`; `H:int128`;
       `h:int128`; `word_bytereverse (tag0:int128)`;
       `\i. bytes_to_int128 (SUB_LIST (16 * i, 16) (ibytes:byte list))`;
       `n:num`] GCM_GHASH_V8_CORRECT) THEN
    ASM_REWRITE_TAC[BYTEREVERSE128_INVOLUTION]]);;

(* ------------------------------------------------------------------------- *)
(* The subroutine wrapper, in the same vocabulary.  Derived by exactly the     *)
(* same corollary argument off GCM_GHASH_V8_SUBROUTINE_CORRECT rather than by   *)
(* re-running ARM_ADD_RETURN_NOSTACK_TAC -- the wrapper reasoning is already    *)
(* paid for and the input side is what changes.                                *)
(* ------------------------------------------------------------------------- *)

let GCM_GHASH_V8_SUBROUTINE_CORRECT_BYTES = prove
 (`!xi_p htbl_p in_p pc H h (tag0:int128) (ibytes:byte list) n returnaddress.
     h = ghash_twist H /\ 1 <= n /\ 16 * n < 2 EXP 64 /\
     LENGTH ibytes = 16 * n /\
     nonoverlapping (word pc, LENGTH ghash_v8_mc) (xi_p,16) /\
     nonoverlapping (xi_p,16) (in_p,16 * n) /\
     nonoverlapping (xi_p,16) (htbl_p,96)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) ghash_v8_mc /\
               read PC s = word pc /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [xi_p; htbl_p; in_p; word (16 * n)] s /\
               read (memory :> bytes128 xi_p) s = word_bytereverse tag0 /\
               byte_list_at ibytes in_p (word (16 * n)) s /\
               htable_mem_4 h htbl_p s)
          (\s. read PC s = returnaddress /\
               read (memory :> bytes128 xi_p) s =
               word_bytereverse
                 (nist_ghash H tag0 (list_of_seq (nist_input_block ibytes) n)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(xi_p:int64,16)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  EXISTS_TAC
   `\s:armstate.
      aligned_bytes_loaded s (word pc) ghash_v8_mc /\
      read PC s = word pc /\
      read X30 s = returnaddress /\
      C_ARGUMENTS [xi_p; htbl_p; in_p; word (16 * n)] s /\
      read (memory :> bytes128 xi_p) s = word_bytereverse tag0 /\
      (!i. i < n
           ==> read (memory :> bytes128 (word_add in_p (word (16 * i)))) s =
               bytes_to_int128 (SUB_LIST (16 * i, 16) ibytes)) /\
      htable_mem_4 h htbl_p s` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:armstate` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `val (word (16 * n):int64) = 16 * n` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN ASM_SIMP_TAC[MOD_LT]; ALL_TAC] THEN
    MATCH_MP_TAC INPUT_BYTES_TO_BYTE128_LANES THEN
    ASM_REWRITE_TAC[LE_REFL] THEN
    SUBGOAL_THEN `SUB_LIST (0, 16 * n) (ibytes:byte list) = ibytes` SUBST1_TAC THENL
     [MATCH_MP_TAC SUB_LIST_LENGTH_IMPLIES THEN ASM_REWRITE_TAC[LE_REFL];
      ALL_TAC] THEN
    MP_TAC(SPECL [`ibytes:byte list`; `in_p:int64`; `word (16 * n):int64`;
                  `s:armstate`] BYTE_LIST_AT_TO_READ_BYTES) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[NIST_INPUT_BLOCK_LIST] THEN
    MP_TAC(SPECL
      [`xi_p:int64`; `htbl_p:int64`; `in_p:int64`; `pc:num`; `H:int128`;
       `h:int128`; `word_bytereverse (tag0:int128)`;
       `\i. bytes_to_int128 (SUB_LIST (16 * i, 16) (ibytes:byte list))`;
       `n:num`; `returnaddress:int64`] GCM_GHASH_V8_SUBROUTINE_CORRECT) THEN
    ASM_REWRITE_TAC[BYTEREVERSE128_INVOLUTION]]);;
