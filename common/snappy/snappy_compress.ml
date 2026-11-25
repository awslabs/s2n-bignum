(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Models of the snappy 1.3.1 compressor (snappy.cc) as compiled for the     *)
(* proofs (arm/snappy/config.h: little-endian, no CRC32, so the hash is the  *)
(* multiplicative one; NEON does not affect the compressor's results).       *)
(* ========================================================================= *)

needs "common/snappy/snappy_format.ml";;

(* ------------------------------------------------------------------------- *)
(* MaxCompressedLength (snappy.cc), with its overflow branch for size_t.     *)
(* ------------------------------------------------------------------------- *)

let snappy_max_compressed_length = new_definition
 `snappy_max_compressed_length n =
    if (2 EXP 64 - 33) DIV 7 * 6 < n then 2 EXP 64 - 1
    else 32 + n + n DIV 6`;;

let SNAPPY_MAX_COMPRESSED_LENGTH_BOUND = prove
 (`!n. snappy_max_compressed_length n < 2 EXP 64`,
  GEN_TAC THEN REWRITE_TAC[snappy_max_compressed_length] THEN
  CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;

let SNAPPY_MAX_COMPRESSED_LENGTH_SMALL = prove
 (`!n. n <= (2 EXP 64 - 33) DIV 7 * 6
       ==> snappy_max_compressed_length n = 32 + n + n DIV 6`,
  SIMP_TAC[snappy_max_compressed_length; GSYM NOT_LT]);;

let SNAPPY_MAX_COMPRESSED_LENGTH_32 = prove
 (`!n. n < 2 EXP 32 ==> snappy_max_compressed_length n = 32 + n + n DIV 6`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SNAPPY_MAX_COMPRESSED_LENGTH_SMALL THEN
  POP_ASSUM MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let SNAPPY_MAX_COMPRESSED_LENGTH_MONO = prove
 (`!m n. m <= n
         ==> snappy_max_compressed_length m <= snappy_max_compressed_length n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[snappy_max_compressed_length] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT COND_CASES_TAC THEN TRY ASM_ARITH_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `a <= b /\ c <= d ==> 32 + a + c <= 32 + b + d`) THEN
  ASM_SIMP_TAC[DIV_MONO]);;

(* ------------------------------------------------------------------------- *)
(* Helpers on the input fragment src: little-endian loads (LittleEndian::Load32 *)
(* and Load64 at byte position p), table updates, and the hash functions.    *)
(*                                                                           *)
(* A hash table of table_size ts (a power of 2) is a function from indices    *)
(* 0..ts-1 to positions in the fragment (uint16_t entries); the index i is   *)
(* the entry at byte offset 2 * i of the table. TableEntry(table, v, mask)   *)
(* with mask = 2 * (ts - 1) is the entry ((kMagic * v) >> 16 & mask) / 2,    *)
(* i.e. bits 17.. of the 32-bit product, and similarly for the two hashes of *)
(* CompressFragmentDoubleHash (TableEntry4ByteMatch: 32-bit product >> 17;   *)
(* TableEntry8ByteMatch: 64-bit product >> 49; then & mask, / 2).            *)
(* ------------------------------------------------------------------------- *)

let snappy_load32 = new_definition
 `snappy_load32 (src:byte list) p = num_of_bytelist(SUB_LIST(p,4) src)`;;

let snappy_load64 = new_definition
 `snappy_load64 (src:byte list) p = num_of_bytelist(SUB_LIST(p,8) src)`;;

let snappy_tupd = new_definition
 `snappy_tupd (t:num->num) e v = \j. if j = e then v else t j`;;

let snappy_hash1 = new_definition
 `snappy_hash1 ts v = ((0x1e35a7bd * v) MOD 2 EXP 32) DIV 2 EXP 17 MOD ts`;;

let snappy_hash4 = new_definition
 `snappy_hash4 ts v = ((2654435761 * v) MOD 2 EXP 32) DIV 2 EXP 18 MOD ts`;;

let snappy_hash8 = new_definition
 `snappy_hash8 ts v =
    ((58295818150454627 * v) MOD 2 EXP 64) DIV 2 EXP 50 MOD ts`;;

(* CalculateTableSize: the least power of 2 >= n, clamped to [256,32768].    *)

let snappy_table_size = new_definition
 `snappy_table_size n =
    if n <= 256 then 256 else if n <= 512 then 512
    else if n <= 1024 then 1024 else if n <= 2048 then 2048
    else if n <= 4096 then 4096 else if n <= 8192 then 8192
    else if n <= 16384 then 16384 else 32768`;;

(* FindMatchLength(s1, s2, s2_limit) and FindMatchLengthPlain: the length of *)
(* the longest common prefix of src[a..] and src[b..] within src (b + it <= n).    *)

let snappy_mlen = new_recursive_definition num_RECURSION
 `(snappy_mlen 0 (src:byte list) a b = 0) /\
  (snappy_mlen (SUC k) src a b =
     if EL a src = EL b src then SUC(snappy_mlen k src (a + 1) (b + 1)) else 0)`;;

let snappy_match_length = new_definition
 `snappy_match_length (src:byte list) a b = snappy_mlen (LENGTH src - b) src a b`;;

(* ------------------------------------------------------------------------- *)
(* The emitted tags.                                                         *)
(* ------------------------------------------------------------------------- *)

(* EmitLiteral(op, literal, len), len >= 1 (both template variants).         *)

let snappy_emit_literal = new_definition
 `snappy_emit_literal (d:byte list) =
    let n = LENGTH d - 1 in
    if n < 60 then CONS (word(4 * n)) d
    else let count = if n < 256 then 1 else if n < 65536 then 2
                     else if n < 2 EXP 24 then 3 else 4 in
         CONS (word(4 * (59 + count))) (APPEND (bytelist_of_num count n) d)`;;

(* EmitCopyAtMost64(op, offset, len), 4 <= len <= 64, offset < 65536.        *)

let snappy_emit_copy64 = new_definition
 `snappy_emit_copy64 off len : byte list =
    if len < 12 /\ off < 2048
    then [word(1 + 4 * (len - 4) + 32 * (off DIV 256)); word(off MOD 256)]
    else [word(2 + 4 * (len - 1)); word(off MOD 256); word(off DIV 256)]`;;

(* EmitCopy(op, offset, len), len >= 4, offset < 65536.                      *)

let snappy_emit_copy = define
 `snappy_emit_copy off len : byte list =
    if 68 <= len
    then APPEND (snappy_emit_copy64 off 64) (snappy_emit_copy off (len - 64))
    else if 64 < len
    then APPEND (snappy_emit_copy64 off 60) (snappy_emit_copy64 off (len - 60))
    else snappy_emit_copy64 off len`;;

(* Varint::Encode32.                                                         *)

let snappy_varint_encode = define
 `snappy_varint_encode n : byte list =
    if n < 128 then [word n]
    else CONS (word(n MOD 128 + 128)) (snappy_varint_encode (n DIV 128))`;;

(* ------------------------------------------------------------------------- *)
(* The state of the fragment compressors, as small-step machines. The        *)
(* fields are                                                                *)
(*   phase   the point in the code (see the step functions);                 *)
(*   ip      the input position (ip - base_ip);                              *)
(*   ne      next_emit - base_ip, start of the pending literal;              *)
(*   skip    the skip counter of the match search;                           *)
(*   cand    candidate - base_ip;                                            *)
(*   aux     CompressFragment: the index i of the unrolled 16-probe search;  *)
(*           CompressFragmentDoubleHash: candidate_length;                   *)
(*   t1, t2  the hash table(s) (t2 only for CompressFragmentDoubleHash);     *)
(*   out     the bytes emitted so far for this fragment.                     *)
(* Phase 0 is the end; the result is then the field out.                     *)
(* ------------------------------------------------------------------------- *)

let snappy_cstate_INDUCT,snappy_cstate_RECURSION = define_type
 "snappy_cstate = SnappyCState num num num num num num (num->num) (num->num) (byte list)";;

let snappy_phase = define
 `snappy_phase (SnappyCState ph ip ne sk c x t1 t2 out) = ph`;;
let snappy_ip = define
 `snappy_ip (SnappyCState ph ip ne sk c x t1 t2 out) = ip`;;
let snappy_ne = define
 `snappy_ne (SnappyCState ph ip ne sk c x t1 t2 out) = ne`;;
let snappy_skip = define
 `snappy_skip (SnappyCState ph ip ne sk c x t1 t2 out) = sk`;;
let snappy_cand = define
 `snappy_cand (SnappyCState ph ip ne sk c x t1 t2 out) = c`;;
let snappy_aux = define
 `snappy_aux (SnappyCState ph ip ne sk c x t1 t2 out) = x`;;
let snappy_t1 = define
 `snappy_t1 (SnappyCState ph ip ne sk c x t1 t2 out) = t1`;;
let snappy_t2 = define
 `snappy_t2 (SnappyCState ph ip ne sk c x t1 t2 out) = t2`;;
let snappy_out = define
 `snappy_out (SnappyCState ph ip ne sk c x t1 t2 out) = out`;;

(* ------------------------------------------------------------------------- *)
(* CompressFragment (level 1). Phases:                                       *)
(*   1  head of the main loop (next_emit = ip++);                            *)
(*   6  the unrolled search for the first 16 positions, probe aux = i;       *)
(*   2  the search loop with skip acceleration;                              *)
(*   3  a match at ip with cand has been found: EmitLiteral [ne, ip);         *)
(*   4  head of the emit_match loop: EmitCopy, then the table updates and    *)
(*      the check for an immediate next match;                               *)
(*   5  emit_remainder: EmitLiteral [ip, n) if nonempty.                     *)
(* The fast path of the first 16 probes writes the literal tag itself; it is *)
(* the same as EmitLiteral of length i + 1, so it goes through phase 3.      *)
(* ------------------------------------------------------------------------- *)

let snappy_cf1_step = define
 `snappy_cf1_step (src:byte list) (SnappyCState ph ip ne sk c x t1 t2 out) =
   let n = LENGTH src in
   let ts = snappy_table_size n in
   let lim = n - 15 in
   if ph = 1 then
     (if (ip + 1) + 16 <= lim then SnappyCState 6 (ip + 1) ip sk c 0 t1 t2 out
      else SnappyCState 2 (ip + 1) ip 32 c x t1 t2 out)
   else if ph = 6 then
     let d = snappy_load32 src (ip + x) in
     let e = snappy_hash1 ts d in
     let c' = t1 e in
     let t1' = snappy_tupd t1 e (ip + x) in
     if snappy_load32 src c' = d then SnappyCState 3 (ip + x) ne sk c' x t1' t2 out
     else if x = 15 then SnappyCState 2 (ip + 16) ne 48 c x t1' t2 out
     else SnappyCState 6 ip ne sk c (x + 1) t1' t2 out
   else if ph = 2 then
     let d = snappy_load32 src ip in
     let e = snappy_hash1 ts d in
     let b = sk DIV 32 in
     if lim < ip + b then SnappyCState 5 ne ne (sk + b) c x t1 t2 out
     else let c' = t1 e in
          let t1' = snappy_tupd t1 e ip in
          if snappy_load32 src c' = d
          then SnappyCState 3 ip ne (sk + b) c' x t1' t2 out
          else SnappyCState 2 (ip + b) ne (sk + b) c x t1' t2 out
   else if ph = 3 then
     SnappyCState 4 ip ne sk c x t1 t2
       (APPEND out (snappy_emit_literal (SUB_LIST(ne,ip - ne) src)))
   else if ph = 4 then
     let m = 4 + snappy_match_length src (c + 4) (ip + 4) in
     let ip' = ip + m in
     let out' = APPEND out (snappy_emit_copy (ip - c) m) in
     if lim <= ip' then SnappyCState 5 ip' ne sk c x t1 t2 out'
     else let t1' = snappy_tupd t1 (snappy_hash1 ts (snappy_load32 src (ip' - 1)))
                                (ip' - 1) in
          let e = snappy_hash1 ts (snappy_load32 src ip') in
          let c' = t1' e in
          let t1'' = snappy_tupd t1' e ip' in
          if snappy_load32 src ip' = snappy_load32 src c'
          then SnappyCState 4 ip' ne sk c' x t1'' t2 out'
          else SnappyCState 1 ip' ne sk c' x t1'' t2 out'
   else if ph = 5 then
     SnappyCState 0 ip ne sk c x t1 t2
      (if ip < n then APPEND out (snappy_emit_literal (SUB_LIST(ip,n - ip) src))
       else out)
   else SnappyCState ph ip ne sk c x t1 t2 out`;;

let snappy_cf1_init = new_definition
 `snappy_cf1_init (src:byte list) =
    SnappyCState (if LENGTH src < 15 then 5 else 1) 0 0 0 0 0 (\j. 0) (\j. 0) []`;;

(* ------------------------------------------------------------------------- *)
(* CompressFragmentDoubleHash (level 2), with two tables of half the size    *)
(* (t1 for TableEntry4ByteMatch, t2 for TableEntry8ByteMatch). Phases:       *)
(*   1  head of the main loop (next_emit = ip++, skip = 512);                *)
(*   2  the search loop (aux, cand set when a match is found);               *)
(*   7  the backtracking loop;                                               *)
(*   3  the three table updates after backtracking, EmitLiteral [ne, ip) if  *)
(*      nonempty;                                                            *)
(*   4  head of the copy loop: EmitCopy, the table updates and the checks    *)
(*      for an immediate next match;                                         *)
(*   5  emit_remainder.                                                      *)
(* ------------------------------------------------------------------------- *)

let snappy_cf2_step = define
 `snappy_cf2_step (src:byte list) (SnappyCState ph ip ne sk c x t1 t2 out) =
   let n = LENGTH src in
   let ts = snappy_table_size n DIV 2 in
   let lim = n - 15 in
   if ph = 1 then SnappyCState 2 (ip + 1) ip 512 c x t1 t2 out
   else if ph = 2 then
     let e2 = snappy_hash8 ts (snappy_load64 src ip) in
     let b = sk DIV 512 in
     if lim < ip + b then SnappyCState 5 ne ne (sk + 1) c x t1 t2 out
     else
     let c2 = t2 e2 in
     let t2' = snappy_tupd t2 e2 ip in
     if snappy_load32 src c2 = snappy_load32 src ip
     then SnappyCState 7 ip ne (sk + 1) c2
            (snappy_match_length src (c2 + 4) (ip + 4) + 4) t1 t2' out
     else
     let e1 = snappy_hash4 ts (snappy_load32 src ip) in
     let c1 = t1 e1 in
     let t1' = snappy_tupd t1 e1 ip in
     if snappy_load32 src c1 = snappy_load32 src ip then
       let len1 = snappy_match_length src (c1 + 4) (ip + 4) + 4 in
       let e2b = snappy_hash8 ts (snappy_load64 src (ip + 1)) in
       let c3 = t2' e2b in
       let len3 = snappy_match_length src c3 (ip + 1) in
       if len1 < len3
       then SnappyCState 7 (ip + 1) ne (sk + 1) c3 len3 t1'
                         (snappy_tupd t2' e2b ip) out
       else SnappyCState 7 ip ne (sk + 1) c1 len1 t1' t2' out
     else SnappyCState 2 (ip + b) ne (sk + 1) c x t1' t2' out
   else if ph = 7 then
     (if ne < ip /\ 0 < c /\ EL (ip - 1) src = EL (c - 1) src
      then SnappyCState 7 (ip - 1) ne sk (c - 1) (x + 1) t1 t2 out
      else SnappyCState 3 ip ne sk c x t1 t2 out)
   else if ph = 3 then
     let t2' = snappy_tupd t2 (snappy_hash8 ts (snappy_load64 src (ip + 1)))
                           (ip + 1) in
     let t2'' = snappy_tupd t2' (snappy_hash8 ts (snappy_load64 src (ip + 2)))
                            (ip + 2) in
     let t1' = snappy_tupd t1 (snappy_hash4 ts (snappy_load32 src (ip + 1)))
                           (ip + 1) in
     SnappyCState 4 ip ne sk c x t1' t2''
       (if ne < ip then APPEND out (snappy_emit_literal (SUB_LIST(ne,ip - ne) src))
        else out)
   else if ph = 4 then
     let ip' = ip + x in
     let out' = APPEND out (snappy_emit_copy (ip - c) x) in
     if lim <= ip' then SnappyCState 5 ip' ne sk c x t1 t2 out'
     else
     let t2a = if 7 < ip'
               then snappy_tupd
                     (snappy_tupd t2 (snappy_hash8 ts (snappy_load64 src (ip' - 7)))
                                  (ip' - 7))
                     (snappy_hash8 ts (snappy_load64 src (ip' - 4))) (ip' - 4)
               else t2 in
     let t2b = snappy_tupd
                (snappy_tupd t2a (snappy_hash8 ts (snappy_load64 src (ip' - 3)))
                             (ip' - 3))
                (snappy_hash8 ts (snappy_load64 src (ip' - 2))) (ip' - 2) in
     let t1a = snappy_tupd
                (snappy_tupd t1 (snappy_hash4 ts (snappy_load32 src (ip' - 2)))
                             (ip' - 2))
                (snappy_hash4 ts (snappy_load32 src (ip' - 1))) (ip' - 1) in
     let e2 = snappy_hash8 ts (snappy_load64 src ip') in
     let c2 = t2b e2 in
     let t2c = snappy_tupd t2b e2 ip' in
     if snappy_load32 src ip' = snappy_load32 src c2
     then SnappyCState 4 ip' ne sk c2
            (snappy_match_length src (c2 + 4) (ip' + 4) + 4) t1a t2c out'
     else
     let e1 = snappy_hash4 ts (snappy_load32 src ip') in
     let c1 = t1a e1 in
     let t1b = snappy_tupd t1a e1 ip' in
     if snappy_load32 src ip' = snappy_load32 src c1
     then SnappyCState 4 ip' ne sk c1
            (snappy_match_length src (c1 + 4) (ip' + 4) + 4) t1b t2c out'
     else SnappyCState 1 ip' ne sk c x t1b t2c out'
   else if ph = 5 then
     SnappyCState 0 ip ne sk c x t1 t2
      (if ip < n then APPEND out (snappy_emit_literal (SUB_LIST(ip,n - ip) src))
       else out)
   else SnappyCState ph ip ne sk c x t1 t2 out`;;

let snappy_cf2_init = new_definition
 `snappy_cf2_init (src:byte list) =
    SnappyCState (if LENGTH src < 15 then 5 else 1) 0 0 0 0 0 (\j. 0) (\j. 0) []`;;

(* ------------------------------------------------------------------------- *)
(* Running a machine: snappy_crun step k s is the state after k steps; the   *)
(* fragment's output is that of the first phase-0 state. snappy_cfinish      *)
(* takes the state after enough steps (any number of steps from a phase-0    *)
(* state gives the same state; snappy_cf_steps_bound is proved sufficient).   *)
(* ------------------------------------------------------------------------- *)

let snappy_crun = new_recursive_definition num_RECURSION
 `(snappy_crun (step:snappy_cstate->snappy_cstate) 0 s = s) /\
  (snappy_crun step (SUC k) s = snappy_crun step k (step s))`;;

let snappy_cf_steps_bound = new_definition
 `snappy_cf_steps_bound n = 40 * n + 40`;;

let snappy_compress_fragment = new_definition
 `snappy_compress_fragment level (src:byte list) =
    if level = 1
    then snappy_out(snappy_crun (snappy_cf1_step src) (snappy_cf_steps_bound (LENGTH src))
                                (snappy_cf1_init src))
    else snappy_out(snappy_crun (snappy_cf2_step src) (snappy_cf_steps_bound (LENGTH src))
                                (snappy_cf2_init src))`;;

(* ------------------------------------------------------------------------- *)
(* The block loop of Compress (InternalCompress with a ByteArraySource and   *)
(* an UncheckedByteArraySink, as in RawCompress): the varint of the length,  *)
(* then each fragment of kBlockSize = 65536 bytes (the last one shorter)     *)
(* compressed with a fresh zeroed table. Inputs of 2^32 bytes or more give   *)
(* no output (RawCompress sets *compressed_length to 0).                     *)
(* ------------------------------------------------------------------------- *)

let snappy_blocks_fuel = new_recursive_definition num_RECURSION
 `(snappy_blocks_fuel 0 level (src:byte list) = []) /\
  (snappy_blocks_fuel (SUC k) level src =
     if src = [] then []
     else APPEND (snappy_compress_fragment level (SUB_LIST(0,65536) src))
                 (snappy_blocks_fuel k level
                    (SUB_LIST(65536,LENGTH src - 65536) src)))`;;

let snappy_compress_blocks = new_definition
 `snappy_compress_blocks level (src:byte list) =
    snappy_blocks_fuel (LENGTH src) level src`;;

let snappy_compress = new_definition
 `snappy_compress level (src:byte list) =
    if 2 EXP 32 <= LENGTH src then []
    else APPEND (snappy_varint_encode (LENGTH src)) (snappy_compress_blocks level src)`;;

(* ------------------------------------------------------------------------- *)
(* Evaluation of the models on concrete inputs by Compute.CBV_CONV.          *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_EVAL_CRUN = prove
 (`!step k s. snappy_crun step k s =
              if k = 0 then s else snappy_crun step (k - 1) (step s)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[snappy_crun; NOT_SUC; SUC_SUB1]);;

let SNAPPY_EVAL_MLEN = prove
 (`!k (src:byte list) a b.
     snappy_mlen k src a b =
     if k = 0 then 0
     else if EL a src = EL b src then snappy_mlen (k - 1) src (a + 1) (b + 1) + 1
     else 0`,
  INDUCT_TAC THEN REWRITE_TAC[snappy_mlen; NOT_SUC; SUC_SUB1; ADD1]);;

let SNAPPY_EVAL_BYTELIST_OF_NUM = prove
 (`!k n. bytelist_of_num k n =
         if k = 0 then []
         else CONS (word(n MOD 256):byte) (bytelist_of_num (k - 1) (n DIV 256))`,
  INDUCT_TAC THEN REWRITE_TAC[bytelist_of_num; NOT_SUC; SUC_SUB1]);;

let SNAPPY_EVAL_BLOCKS = prove
 (`!k level (src:byte list).
     snappy_blocks_fuel k level src =
     if k = 0 then [] else if src = [] then [] else
     APPEND (snappy_compress_fragment level (SUB_LIST(0,65536) src))
            (snappy_blocks_fuel (k - 1) level
               (SUB_LIST(65536,LENGTH src - 65536) src))`,
  INDUCT_TAC THEN REWRITE_TAC[snappy_blocks_fuel; NOT_SUC; SUC_SUB1]);;

let snappy_compress_compset =
  let cs = snappy_compset in
  Compute.add_thms
   [snappy_load32; snappy_load64; snappy_tupd; snappy_hash1; snappy_hash4;
    snappy_hash8; snappy_table_size; snappy_match_length; SNAPPY_EVAL_MLEN;
    snappy_emit_literal; snappy_emit_copy64; snappy_emit_copy;
    snappy_varint_encode; snappy_phase; snappy_ip; snappy_ne; snappy_skip;
    snappy_cand; snappy_aux; snappy_t1; snappy_t2; snappy_out;
    snappy_cf1_step; snappy_cf1_init; snappy_cf2_step; snappy_cf2_init;
    SNAPPY_EVAL_CRUN; snappy_cf_steps_bound; snappy_compress_fragment;
    SNAPPY_EVAL_BLOCKS; snappy_compress_blocks; snappy_compress;
    snappy_max_compressed_length; SNAPPY_EVAL_BYTELIST_OF_NUM] cs;
  Compute.add_conv (`(EXP):num->num->num`,2,NUM_EXP_CONV) cs;
  cs;;

let SNAPPY_COMPRESS_EVAL_CONV = Compute.CBV_CONV snappy_compress_compset;;
