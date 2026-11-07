(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Extraction of bytes from four Keccak states. This is the code for         *)
(* mlkem_keccakf1600x4_extract_bytes from mlkem-native's portable C          *)
(* implementation compiled by clang 17 with -O3 (see mlkem_native/README.md),*)
(* which copies len bytes of each of the four 200-byte states, starting at   *)
(* byte off, to its own output. Where gcc calls                              *)
(* mlkem_keccakf1600_extract_bytes for each state, clang has inlined four    *)
(* copies of its code, each with the alias test and the three loops (blocks  *)
(* of 32 bytes, blocks of 8 bytes, single bytes) described in                *)
(* keccakf1600_extract_bytes.ml, so it uses no stack. The copies differ in   *)
(* their registers and address arithmetic, but the same tactics,             *)
(* parametrized by the copy, verify all four. The specifications are those  *)
(* for gcc without the stack frame. It is verified in the whole image (see   *)
(* libmlkem.ml).                                                             *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/clang17_O3/keccakf1600_extract_bytes_proof.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_keccakf1600x4_extract_bytes:
      +0x0: cbz     w6, join12
      +0x4: mov     w8, w5
      +0x8: mov     w9, w6
      +0xc: cmp     w6, #0x8
     +0x10: b.cc    join1
     +0x14: sub     x10, x1, x0
     +0x18: sub     x10, x10, x8
     +0x1c: cmp     x10, #0x20
     +0x20: b.cs    +0x118
     +0x24: mov     x10, xzr
     +0x28: add     x12, x0, x10
     +0x2c: sub     x11, x9, x10
     +0x30: add     x10, x1, x10
     +0x34: add     x12, x12, x8
     +0x38: ldrb    w13, [x12], #1
     +0x3c: subs    x11, x11, #0x1
     +0x40: strb    w13, [x10], #1
     +0x44: b.ne    loop1
     +0x48: cmp     w6, #0x8
     +0x4c: b.cc    join4
     +0x50: add     x10, x0, x8
     +0x54: sub     x10, x2, x10
     +0x58: sub     x10, x10, #0xc8
     +0x5c: cmp     x10, #0x20
     +0x60: b.cs    +0x128
     +0x64: mov     x10, xzr
     +0x68: add     x12, x10, x8
     +0x6c: sub     x11, x9, x10
     +0x70: add     x12, x12, x0
     +0x74: add     x10, x2, x10
     +0x78: add     x12, x12, #0xc8
     +0x7c: ldrb    w13, [x12], #1
     +0x80: subs    x11, x11, #0x1
     +0x84: strb    w13, [x10], #1
     +0x88: b.ne    loop2
     +0x8c: cmp     w6, #0x8
     +0x90: b.cc    join7
     +0x94: add     x10, x0, x8
     +0x98: sub     x10, x3, x10
     +0x9c: sub     x10, x10, #0x190
     +0xa0: cmp     x10, #0x20
     +0xa4: b.cs    +0x138
     +0xa8: mov     x10, xzr
     +0xac: add     x12, x10, x8
     +0xb0: sub     x11, x9, x10
     +0xb4: add     x12, x12, x0
     +0xb8: add     x10, x3, x10
     +0xbc: add     x12, x12, #0x190
     +0xc0: ldrb    w13, [x12], #1
     +0xc4: subs    x11, x11, #0x1
     +0xc8: strb    w13, [x10], #1
     +0xcc: b.ne    loop3
     +0xd0: cmp     w6, #0x8
     +0xd4: b.cc    join10
     +0xd8: add     x11, x0, x8
     +0xdc: sub     x10, x4, x11
     +0xe0: sub     x10, x10, #0x258
     +0xe4: cmp     x10, #0x20
     +0xe8: b.cs    +0x148
     +0xec: mov     x10, xzr
     +0xf0: add     x11, x10, x8
     +0xf4: sub     x8, x9, x10
     +0xf8: add     x11, x11, x0
     +0xfc: add     x9, x4, x10
    +0x100: add     x10, x11, #0x258
    +0x104: ldrb    w11, [x10], #1
    +0x108: subs    x8, x8, #0x1
    +0x10c: strb    w11, [x9], #1
    +0x110: b.ne    loop4
    +0x114: ret
    +0x118: cmp     w6, #0x20
    +0x11c: b.cs    +0x158
    +0x120: mov     x10, xzr
    +0x124: b       join13
    +0x128: cmp     w6, #0x20
    +0x12c: b.cs    +0x1c8
    +0x130: mov     x10, xzr
    +0x134: b       join14
    +0x138: cmp     w6, #0x20
    +0x13c: b.cs    +0x23c
    +0x140: mov     x10, xzr
    +0x144: b       join15
    +0x148: cmp     w6, #0x20
    +0x14c: b.cs    +0x2b0
    +0x150: mov     x10, xzr
    +0x154: b       join16
    +0x158: and     x10, x9, #0xffffffe0
    +0x15c: add     x11, x8, x0
    +0x160: add     x11, x11, #0x10
    +0x164: add     x12, x1, #0x10
    +0x168: mov     x13, x10
    +0x16c: ldp     q0, q1, [x11, #-16]
    +0x170: add     x11, x11, #0x20
    +0x174: subs    x13, x13, #0x20
    +0x178: stp     q0, q1, [x12, #-16]
    +0x17c: add     x12, x12, #0x20
    +0x180: b.ne    loop5
    +0x184: cmp     x10, x9
    +0x188: b.eq    join3
    +0x18c: tst     x9, #0x18
    +0x190: b.eq    join2
    +0x194: mov     x13, x10
    +0x198: and     x10, x9, #0xfffffff8
    +0x19c: add     x11, x0, x13
    +0x1a0: add     x12, x1, x13
    +0x1a4: add     x11, x11, x8
    +0x1a8: sub     x13, x13, x10
    +0x1ac: ldr     d0, [x11], #8
    +0x1b0: adds    x13, x13, #0x8
    +0x1b4: str     d0, [x12], #8
    +0x1b8: b.ne    loop6
    +0x1bc: cmp     x10, x9
    +0x1c0: b.eq    join3
    +0x1c4: b       join2
    +0x1c8: and     x10, x9, #0xffffffe0
    +0x1cc: add     x11, x8, x0
    +0x1d0: add     x11, x11, #0xd8
    +0x1d4: add     x12, x2, #0x10
    +0x1d8: mov     x13, x10
    +0x1dc: ldp     q0, q1, [x11, #-16]
    +0x1e0: add     x11, x11, #0x20
    +0x1e4: subs    x13, x13, #0x20
    +0x1e8: stp     q0, q1, [x12, #-16]
    +0x1ec: add     x12, x12, #0x20
    +0x1f0: b.ne    loop7
    +0x1f4: cmp     x10, x9
    +0x1f8: b.eq    join6
    +0x1fc: tst     x9, #0x18
    +0x200: b.eq    join5
    +0x204: mov     x13, x10
    +0x208: and     x10, x9, #0xfffffff8
    +0x20c: add     x11, x13, x8
    +0x210: add     x12, x2, x13
    +0x214: add     x11, x11, x0
    +0x218: sub     x13, x13, x10
    +0x21c: add     x11, x11, #0xc8
    +0x220: ldr     d0, [x11], #8
    +0x224: adds    x13, x13, #0x8
    +0x228: str     d0, [x12], #8
    +0x22c: b.ne    loop8
    +0x230: cmp     x10, x9
    +0x234: b.eq    join6
    +0x238: b       join5
    +0x23c: and     x10, x9, #0xffffffe0
    +0x240: add     x11, x8, x0
    +0x244: add     x11, x11, #0x1a0
    +0x248: add     x12, x3, #0x10
    +0x24c: mov     x13, x10
    +0x250: ldp     q0, q1, [x11, #-16]
    +0x254: add     x11, x11, #0x20
    +0x258: subs    x13, x13, #0x20
    +0x25c: stp     q0, q1, [x12, #-16]
    +0x260: add     x12, x12, #0x20
    +0x264: b.ne    loop9
    +0x268: cmp     x10, x9
    +0x26c: b.eq    join9
    +0x270: tst     x9, #0x18
    +0x274: b.eq    join8
    +0x278: mov     x13, x10
    +0x27c: and     x10, x9, #0xfffffff8
    +0x280: add     x11, x13, x8
    +0x284: add     x12, x3, x13
    +0x288: add     x11, x11, x0
    +0x28c: sub     x13, x13, x10
    +0x290: add     x11, x11, #0x190
    +0x294: ldr     d0, [x11], #8
    +0x298: adds    x13, x13, #0x8
    +0x29c: str     d0, [x12], #8
    +0x2a0: b.ne    loop10
    +0x2a4: cmp     x10, x9
    +0x2a8: b.eq    join9
    +0x2ac: b       join8
    +0x2b0: and     x10, x9, #0xffffffe0
    +0x2b4: add     x11, x11, #0x258
    +0x2b8: add     x12, x4, #0x10
    +0x2bc: mov     x13, x10
    +0x2c0: ldp     q0, q1, [x11], #32
    +0x2c4: subs    x13, x13, #0x20
    +0x2c8: stp     q0, q1, [x12, #-16]
    +0x2cc: add     x12, x12, #0x20
    +0x2d0: b.ne    loop11
    +0x2d4: cmp     x10, x9
    +0x2d8: b.eq    join12
    +0x2dc: tst     x9, #0x18
    +0x2e0: b.eq    join11
    +0x2e4: mov     x13, x10
    +0x2e8: and     x10, x9, #0xfffffff8
    +0x2ec: add     x11, x13, x8
    +0x2f0: add     x12, x4, x13
    +0x2f4: add     x11, x11, x0
    +0x2f8: sub     x13, x13, x10
    +0x2fc: add     x11, x11, #0x258
    +0x300: ldr     d0, [x11], #8
    +0x304: adds    x13, x13, #0x8
    +0x308: str     d0, [x12], #8
    +0x30c: b.ne    loop12
    +0x310: cmp     x10, x9
    +0x314: b.eq    join12
    +0x318: b       join11
 ***)

let MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_keccakf1600x4_extract_bytes"];;

let EXT4_EXEC = MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_CLANG17_O3_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The four copies of the code. Copy k copies bytes off to off + len - 1 of  *)
(* state k, at a + 200 * k, to dk. Each has a loop of single bytes, a loop   *)
(* of blocks of 32 bytes and a loop of blocks of 8 bytes (loop k + 1,        *)
(* loop 5 + 2 * k and loop 6 + 2 * k), and ends at the next copy (join3,     *)
(* join6, join9) or at the return. They differ in the registers of the loop  *)
(* of single bytes, in the address arithmetic, and so in the numbers of      *)
(* instructions of the paths, which are recorded here as                     *)
(* (b1,b2,a3,v2,t21,t3,t31,v2body): from the start of the copy to the loop   *)
(* of single bytes when len <= 7 or when the alias test fails, to the loop   *)
(* of 8 bytes when 8 <= len < 32, to the loop of 32 bytes otherwise; from    *)
(* the end of the loop of 32 bytes to the loop of single bytes or to the     *)
(* loop of 8 bytes; from the end of the loop of 8 bytes to the loop of       *)
(* single bytes; and the length of the body of the loop of 32 bytes.         *)
(* ------------------------------------------------------------------------- *)

type ext4_block =
  { ek : int; esrc : string; edst : string; ecnt : string;
    esteps : int * int * int * int * int * int * int * int };;

let ext4_blocks =
  [{ek = 0; esrc = "X12"; edst = "X10"; ecnt = "X11";
    esteps = (10,14,19,16,8,10,7,6)};
   {ek = 1; esrc = "X12"; edst = "X10"; ecnt = "X11";
    esteps = (8,13,18,14,9,11,8,6)};
   {ek = 2; esrc = "X12"; edst = "X10"; ecnt = "X11";
    esteps = (8,13,18,14,9,11,8,6)};
   {ek = 3; esrc = "X10"; edst = "X9"; ecnt = "X8";
    esteps = (8,13,18,13,9,11,8,5)}];;

let ext4_label l = parse_term("pc + mlkem_keccakf1600x4_extract_bytes_" ^ l);;
let ext4_lb b = "loop" ^ string_of_int(b.ek + 1);;
let ext4_l32 b = "loop" ^ string_of_int(5 + 2 * b.ek);;
let ext4_l8 b = "loop" ^ string_of_int(6 + 2 * b.ek);;
let ext4_next k = List.nth ["join3"; "join6"; "join9"; "ret"] k;;

let ext4_ks k = string_of_int k;;
let ext4_base_str k =
  if k = 0 then "(a:int64)"
  else "word_add (a:int64) (word " ^ string_of_int(200 * k) ^ ")";;
let ext4_base k = parse_term(ext4_base_str k);;
let ext4_d k = mk_var("d" ^ ext4_ks k,`:int64`);;
let ext4_s k = mk_var("S" ^ ext4_ks k,`:1600 word`);;

(*** Loads from state k at byte off + j, at address a + 200 * k + off + j ***)

let EXT4_BASE_LEMMA = prove
 (`!a:int64 b k. word_add (word_add a (word b)) (word k) =
                 word_add a (word(b + k))`,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]);;

let READ_MEMORY_BYTES8_OF_NUM_BASE = prove
 (`!a:int64 b m n k s.
        read (memory :> bytes(word_add a (word b),m)) s = n /\ k < m
        ==> read (memory :> bytes8(word_add a (word(b + k)))) s =
            word((n DIV 2 EXP (8 * k)) MOD 256)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM EXT4_BASE_LEMMA] THEN
  MATCH_MP_TAC READ_MEMORY_BYTES8_OF_NUM THEN EXISTS_TAC `m:num` THEN
  ASM_REWRITE_TAC[]);;

let READ_MEMORY_BYTES64_OF_NUM_BASE = prove
 (`!a:int64 b m n k s.
        read (memory :> bytes(word_add a (word b),m)) s = n /\ k + 8 <= m
        ==> read (memory :> bytes64(word_add a (word(b + k)))) s =
            word((n DIV 2 EXP (8 * k)) MOD 2 EXP 64)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM EXT4_BASE_LEMMA] THEN
  MATCH_MP_TAC READ_MEMORY_BYTES64_OF_NUM THEN EXISTS_TAC `m:num` THEN
  ASM_REWRITE_TAC[]);;

let READ_MEMORY_BYTES128_OF_NUM_BASE = prove
 (`!a:int64 b m n k s.
        read (memory :> bytes(word_add a (word b),m)) s = n /\ k + 16 <= m
        ==> read (memory :> bytes128(word_add a (word(b + k)))) s =
            word((n DIV 2 EXP (8 * k)) MOD 2 EXP 128)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM EXT4_BASE_LEMMA] THEN
  MATCH_MP_TAC READ_MEMORY_BYTES128_OF_NUM THEN EXISTS_TAC `m:num` THEN
  ASM_REWRITE_TAC[]);;

let READ_MEMORY_BYTES128_OF_NUM_BASE16 = prove
 (`!a:int64 b m n k s.
        read (memory :> bytes(word_add a (word b),m)) s = n /\ k + 32 <= m
        ==> read (memory :> bytes128(word_add a (word((b + k) + 16)))) s =
            word((n DIV 2 EXP (8 * (k + 16))) MOD 2 EXP 128)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[ARITH_RULE `(b + k) + 16 = b + (k + 16)`] THEN
  ONCE_REWRITE_TAC[GSYM EXT4_BASE_LEMMA] THEN
  MATCH_MP_TAC READ_MEMORY_BYTES128_OF_NUM THEN EXISTS_TAC `m:num` THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(*** sz = 8, 64, 128, or 129 for the second register of an LDP of Q ***)

let EXT4_LOAD_FACT_TAC sz k j (bound:tactic) =
  let vs = mk_comb(`val:1600 word->num`,ext4_s k) in
  let ofs = mk_binop `(+):num->num->num` `off:num` j in
  let th =
    if k = 0 then
      let l = match sz with
          8 -> READ_MEMORY_BYTES8_OF_NUM | 64 -> READ_MEMORY_BYTES64_OF_NUM
        | _ -> READ_MEMORY_BYTES128_OF_NUM in
      let ofs' = if sz = 129 then mk_binop `(+):num->num->num` ofs `16`
                 else ofs in
      SPECL [`a:int64`; `200`; vs; ofs'] l
    else
      let l = match sz with
          8 -> READ_MEMORY_BYTES8_OF_NUM_BASE
        | 64 -> READ_MEMORY_BYTES64_OF_NUM_BASE
        | 128 -> READ_MEMORY_BYTES128_OF_NUM_BASE
        | _ -> READ_MEMORY_BYTES128_OF_NUM_BASE16 in
      SPECL [`a:int64`; mk_small_numeral(200 * k); `200`; vs; ofs] l in
  MP_TAC(SPEC `s0:armstate` th) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN bound; DISCH_TAC];;

(*** The address a + 200 * k + ofs, in the form a + word(200 * k + ofs) ***)
(*** that the simulation gives for the loads with immediate offsets     ***)

let ext4_src_str k ofs =
  if k = 0 then "word_add (a:int64) (word(" ^ ofs ^ "))"
  else "word_add (a:int64) (word(" ^ string_of_int(200 * k) ^ " + " ^
       ofs ^ "))";;

let ext4_conj l = String.concat " /\\ " l;;

let ext4_common =
  ["read X0 s = (a:int64)"; "read X1 s = (d0:int64)"; "read X2 s = (d1:int64)";
   "read X3 s = (d2:int64)"; "read X4 s = (d3:int64)"; "read X6 s = word len";
   "read X30 s = (returnaddress:int64)"];;

let ext4_offlen = ["read X8 s = word off"; "read X9 s = word len"];;

let ext4_state j =
  "read (memory :> bytes(" ^ ext4_base_str j ^ ",200)) s = val(S" ^
  ext4_ks j ^ ":1600 word)";;

let ext4_out_str j n =
  "read (memory :> bytes(d" ^ ext4_ks j ^ "," ^ n ^ ")) s = (val(S" ^
  ext4_ks j ^ ":1600 word) DIV 2 EXP (8 * off)) MOD 2 EXP (8 * (" ^ n ^ "))";;

(*** The facts kept by copy k: the states of copies k to 3, and the     ***)
(*** outputs of the copies before                                       ***)

let ext4_frame k =
  ext4_common @ map ext4_state (k--3) @
  map (fun j -> ext4_out_str j "len") (0--(k-1));;

(*** The invariant at the start of copy j (j = 1, 2, 3) and at the return ***)

let EXT4_INV j =
  parse_term("\\s:armstate. " ^ ext4_conj
   (ext4_frame j @ (if j < 4 then ext4_offlen else [])));;

(* ------------------------------------------------------------------------- *)
(* The events, by path as for mlkem_keccakf1600_extract_bytes, per copy.     *)
(* ------------------------------------------------------------------------- *)

(*** The condition under which copy k copies single bytes for len >= 8: ***)
(*** that the output starts less than 32 bytes after the input, as a     ***)
(*** difference modulo 2^64 in the form that the code computes it.        ***)

let ext4_alias k =
  if k = 0 then "val(word_sub (word_sub d0 a) (word off):int64) < 32"
  else "val(word_sub (word_sub d" ^ ext4_ks k ^
       " (word_add a (word off))) (word " ^ string_of_int(200 * k) ^
       "):int64) < 32";;

let EXT4_EVENTS_TERM =
  let args = "a d0 d1 d2 d3 off len pc returnaddress" in
  let ev nm = "f_ev_" ^ nm ^ " " ^ args in
  let byteloop p cnt =
    "APPEND (" ^ ev (p ^ "e") ^ ") (APPEND (ENUMERATEL (" ^ cnt ^
    ") (\\i. " ^ ev (p ^ "l") ^ " i)) (" ^ ev (p ^ "p") ^ "))" in
  let tail3 p =
    "(if len MOD 8 = 0 then " ^ ev (p ^ "0") ^ " else " ^
    byteloop (p ^ "1") "len MOD 8" ^ ")" in
  let loop3 p cnt =
    "APPEND " ^ tail3 (p ^ "t") ^ " (APPEND (" ^ ev (p ^ "e") ^
    ") (APPEND (ENUMERATEL (" ^ cnt ^ ") (\\i. " ^ ev (p ^ "l") ^
    " i)) (" ^ ev (p ^ "p") ^ ")))" in
  let block k =
    let p = "k" ^ ext4_ks k ^ "_" in
    let tail2 =
      "(if len MOD 32 = 0 then " ^ ev (p ^ "t20") ^
      " else if len MOD 32 < 8 then " ^ byteloop (p ^ "t21") "len MOD 32" ^
      " else " ^ loop3 (p ^ "t3") "(len MOD 32) DIV 8" ^ ")" in
    "(if len <= 7 then " ^ byteloop (p ^ "b1") "len" ^
    " else if " ^ ext4_alias k ^ " then " ^ byteloop (p ^ "b2") "len" ^
    " else if len < 32 then " ^ loop3 (p ^ "a3") "len DIV 8" ^
    " else APPEND " ^ tail2 ^ " (APPEND (" ^ ev (p ^ "v2e") ^
    ") (APPEND (ENUMERATEL (len DIV 32) (\\i. " ^ ev (p ^ "v2l") ^
    " i)) (" ^ ev (p ^ "v2p") ^ "))))" in
  parse_term
   ("\\(a:int64) (d0:int64) (d1:int64) (d2:int64) (d3:int64) (off:num) " ^
    "(len:num) (pc:num) (returnaddress:int64). " ^
    "if len = 0 then " ^ ev "len0" ^ " else APPEND (" ^ ev "ret" ^
    ") (APPEND " ^ block 3 ^ " (APPEND " ^ block 2 ^ " (APPEND " ^
    block 1 ^ " " ^ block 0 ^ "))) :(uarch_event)list");;

(* ------------------------------------------------------------------------- *)
(* Simulation steps and the closing of the goals.                            *)
(* ------------------------------------------------------------------------- *)

(*** The branch of the alias test, 32 <= val x, decided by the case ***)
(*** assumption val x < 32 or its negation                          ***)

let EXT4_ALIAS_BRANCH_TAC =
  let pc_pat = `read PC s = x` and lt_pat = `val(x:int64) < 32` in
  FIRST_ASSUM(fun th ->
    let c = concl th in
    let core = if is_neg c then dest_neg c else c in
    if can (term_match [] lt_pat) core then
      RULE_ASSUM_TAC(fun a ->
        if can (term_match [] pc_pat) (concl a)
        then REWRITE_RULE[GSYM NOT_LT; th] a else a)
    else NO_TAC);;

let EXT4_STEP_TAC n =
  ARM_STEPS_TAC EXT4_EXEC [n] THEN
  EXT_NORM_TAC THEN EXT_FOLD_TAC THEN
  TRY EXT_W32_DECIDE_TAC THEN TRY EXT4_ALIAS_BRANCH_TAC THEN EXT_BRANCH_TAC;;

(*** The steps from the start of copy k ***)

let EXT4_ENTRY_TAC b n =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  (if b.ek = 0 then
     ARM_STEPS_TAC EXT4_EXEC (1--1) THEN EXT_ARGS_TAC THEN
     ARM_STEPS_TAC EXT4_EXEC (2--3) THEN MAP_EVERY EXT4_STEP_TAC (4--n)
   else MAP_EVERY EXT4_STEP_TAC (1--n));;

(*** Equations of addresses and counters, after the simulation ***)

let EXT4_WORD_TAC =
  (REWRITE_TAC[WORD_SUB_MOD32; WORD_SUB_MOD8] THEN
   REWRITE_TAC[WORD_ADD; ADD_CLAUSES; WORD_ADD_0] THEN
   CONV_TAC WORD_RULE) ORELSE
  (AP_TERM_TAC THEN ARITH_TAC);;

let EXT4_FINISH_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[WORD_AND_FFFFFFE0_64; WORD_AND_FFFFFFF8_64] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; MULT_CLAUSES; EXP;
              MOD_1; ADD_CLAUSES; SUB_0; WORD_ADD_0] THEN
  REPEAT CONJ_TAC THEN
  FIRST [ASM_REWRITE_TAC[] THEN NO_TAC;
         EXT4_WORD_TAC THEN NO_TAC;
         DISCHARGE_SAFETY_PROPERTY_TAC];;

(* ------------------------------------------------------------------------- *)
(* Reassociating the events of the postcondition only: e2 = APPEND (APPEND   *)
(* x y) z becomes e2 = APPEND x (APPEND y z), so that a loop or sequence of  *)
(* a copy after the first can be split off. Rewriting the whole goal would   *)
(* also reassociate the events of the earlier copies in the precondition.    *)
(* ------------------------------------------------------------------------- *)

let EXT4_REASSOC_TAC =
  let conv t =
    match t with
      Comb(Comb(Const("=",_),Var("e2",_)),_) ->
        RAND_CONV(REWR_CONV(GSYM APPEND_ASSOC)) t
    | _ -> failwith "EXT4_REASSOC_TAC" in
  CONV_TAC(RATOR_CONV(RAND_CONV(ONCE_DEPTH_CONV conv)));;

(* ------------------------------------------------------------------------- *)
(* In the copies after the first, the goals also have the events of the      *)
(* earlier copies, in the precondition (as an assumption e2 = ... after      *)
(* ENSURES_INIT_TAC) and in the postcondition. Arithmetic rewriting of the   *)
(* whole goal or of all assumptions would change only one of them, and then  *)
(* DISCHARGE_SAFETY_PROPERTY_TAC no longer matches them. So the state        *)
(* conjuncts of a goal are rewritten separately from the events, and only    *)
(* the assumptions about the state are rewritten.                            *)
(* ------------------------------------------------------------------------- *)

let ext4_is_state th =
  match concl th with
    Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),_)),_) ->
      not(is_const c && name_of c = "events")
  | _ -> false;;

let EXT4_STATE_RULE_TAC (rule:thm->thm) =
  RULE_ASSUM_TAC(fun th -> if ext4_is_state th then rule th else th);;

let EXT4_SAFETY_TAC (asl,w) =
  if is_exists w then DISCHARGE_SAFETY_PROPERTY_TAC (asl,w)
  else NO_TAC (asl,w);;

(*** The final state, with tac to prove each conjunct of the state ***)

let EXT4_FINISH_TAC (tac:tactic) =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN FIRST [EXT4_SAFETY_TAC; ALL_TAC] THEN tac;;

let EXT4_CLOSE_TAC ths =
  REWRITE_TAC ths THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  EXT4_WORD_TAC;;

(* ------------------------------------------------------------------------- *)
(* The loop of single bytes of copy k, after n0 + i bytes, cnt in all.      *)
(* ------------------------------------------------------------------------- *)

let EXT4_INV1 b n0 cnt =
  let k = b.ek in
  let t = parse_term("\\(i:num) (s:armstate). " ^ ext4_conj
    (ext4_frame k @ (if k < 3 then ext4_offlen else []) @
     ["read " ^ b.ecnt ^ " s = word(cnt - i)";
      "read " ^ b.esrc ^ " s = " ^ ext4_src_str k "off + n0 + i";
      "read " ^ b.edst ^ " s = word_add d" ^ ext4_ks k ^ " (word(n0 + i))";
      ext4_out_str k "n0 + i"])) in
  subst [n0,`n0:num`; cnt,`cnt:num`] t;;

let EXT4_BYTE_FACT_TAC k j = EXT4_LOAD_FACT_TAC 8 k j SIMPLE_ARITH_TAC;;

let EXT4_BYTE_BODY b n0 cnt =
  let sb = subst [n0,`n0:num`; cnt,`cnt:num`] in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  EXT4_BYTE_FACT_TAC b.ek (sb `n0 + i`) THEN
  ARM_STEPS_TAC EXT4_EXEC (1--4) THEN
  BYTE_CNT_TAC cnt THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (sb `~(i + 1 = cnt) <=> i + 1 < cnt`)
    (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC (sb `i < cnt`) THEN ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  FIRST [EXT4_SAFETY_TAC;
         COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC;
         REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; ADD_ASSOC] THEN
         NO_TAC;
         EXT4_WORD_TAC THEN NO_TAC;
         REWRITE_TAC[ARITH_RULE (sb `n0 + i + 1 = (n0 + i) + 1`)] THEN
         EXT_STORES_TAC THEN
         MATCH_MP_TAC READ_MEMORY_BYTES_EXTEND THEN CONJ_TAC THEN
         FIRST_ASSUM ACCEPT_TAC];;

let EXT4_BYTE_EXIT n0 cnt =
  REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN (subst [n0,`n0:num`; cnt,`cnt:num`] `n0 + cnt = len`)
    (fun th -> EXT4_STATE_RULE_TAC(REWRITE_RULE[th])) THENL
   [ARITH_TAC; ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let EXT4_BYTELOOP_TAC b n0 cnt (pos:tactic) (pro:tactic) =
  ENSURES_EVENTS_WHILE_UP2_TAC cnt (ext4_label(ext4_lb b))
   (ext4_label(ext4_lb b ^ "_exit")) (EXT4_INV1 b n0 cnt) THEN
  REPEAT CONJ_TAC THENL
   [pos; pro; EXT4_BYTE_BODY b n0 cnt; EXT4_BYTE_EXIT n0 cnt];;

(* ------------------------------------------------------------------------- *)
(* The loop of blocks of 32 bytes of copy k, len DIV 32 iterations.         *)
(* ------------------------------------------------------------------------- *)

let EXT4_INV2 b =
  let k = b.ek in
  parse_term("\\(i:num) (s:armstate). " ^ ext4_conj
   (ext4_frame k @ ext4_offlen @
    ["read X10 s = word(32 * (len DIV 32))";
     (if k < 3 then
        "read X11 s = word_add (" ^ ext4_src_str k "off + 32 * i" ^
        ") (word 16)"
      else "read X11 s = " ^ ext4_src_str k "off + 32 * i");
     "read X12 s = word_add (word_add d" ^ ext4_ks k ^
     " (word(32 * i))) (word 16)";
     "read X13 s = word(32 * (len DIV 32 - i))";
     ext4_out_str k "32 * i"]));;

let EXT4_MIDV b =
  let k = b.ek in
  parse_term("\\(s:armstate). " ^ ext4_conj
   (ext4_frame k @ ext4_offlen @
    ["read X10 s = word(32 * (len DIV 32))";
     ext4_out_str k "32 * (len DIV 32)"]));;

let EXT4_V2_BODY b =
  let k = b.ek in
  let (_,_,_,_,_,_,_,nb) = b.esteps in
  let fact sz =
    EXT4_LOAD_FACT_TAC sz k `32 * i`
     (UNDISCH_TAC `off + len <= 200` THEN
      UNDISCH_TAC `32 * i + 32 <= len` THEN ARITH_TAC) in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN `32 * i + 32 <= len` ASSUME_TAC THENL
   [UNDISCH_TAC `i < len DIV 32` THEN ARITH_TAC; ALL_TAC] THEN
  fact 128 THEN fact 129 THEN
  ARM_STEPS_TAC EXT4_EXEC (1--nb) THEN
  LOOP2_CNT_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(i + 1 = len DIV 32) <=> i + 1 < len DIV 32`
    (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `i < len DIV 32` THEN ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  FIRST [EXT4_SAFETY_TAC;
         COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC;
         REWRITE_TAC[ARITH_RULE `off + 32 * (i + 1) = (off + 32 * i) + 32`;
                     ARITH_RULE `32 * (i + 1) = 32 * i + 32`; WORD_ADD] THEN
         CONV_TAC WORD_RULE THEN NO_TAC;
         EXT4_STATE_RULE_TAC(REWRITE_RULE
          [ARITH_RULE `(off + 32 * i) + 16 = off + (32 * i + 16)`]) THEN
         EXT_PREFIX_TAC `32 * i` `16` `32 * i + 16` THEN
         EXT_PREFIX_TAC `32 * i + 16` `16` `32 * i + 32` THEN
         REWRITE_TAC[ARITH_RULE `32 * (i + 1) = 32 * i + 32`] THEN
         FIRST_ASSUM ACCEPT_TAC];;

(* ------------------------------------------------------------------------- *)
(* The loop of blocks of 8 bytes of copy k, after n0 bytes, k3 iterations.  *)
(* ------------------------------------------------------------------------- *)

let EXT4_INV3 b n0 k3 =
  let k = b.ek in
  let t = parse_term("\\(i:num) (s:armstate). " ^ ext4_conj
   (ext4_frame k @ ext4_offlen @
    ["read X10 s = word(n0 + 8 * k3)";
     "read X11 s = " ^ ext4_src_str k "off + n0 + 8 * i";
     "read X12 s = word_add d" ^ ext4_ks k ^ " (word(n0 + 8 * i))";
     "read X13 s = word_sub (word(n0 + 8 * i)) (word(n0 + 8 * k3))";
     ext4_out_str k "n0 + 8 * i"])) in
  subst [n0,`n0:num`; k3,`k3:num`] t;;

let EXT4_MID3 b =
  let k = b.ek in
  parse_term("\\(s:armstate). " ^ ext4_conj
   (ext4_frame k @ ext4_offlen @
    ["read X10 s = word(8 * (len DIV 8))";
     ext4_out_str k "8 * (len DIV 8)"]));;

let EXT4_LOOP3_BODY b n0 k3 =
  let k = b.ek in
  let sb = subst [n0,`n0:num`; k3,`k3:num`] in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN (sb `n0 + 8 * k3 <= len`) ASSUME_TAC THENL
   [SUBGOAL_THEN (sb `n0 + 8 * k3 = 8 * (len DIV 8)`) SUBST1_TAC THENL
     [FIRST [ACCEPT_TAC(SYM(SPEC `len:num` DIV8_SPLIT));
             REWRITE_TAC[ADD_CLAUSES]]; ALL_TAC] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (sb `n0 + 8 * i + 8 <= len`) ASSUME_TAC THENL
   [UNDISCH_TAC (sb `n0 + 8 * k3 <= len`) THEN
    UNDISCH_TAC (sb `i < k3`) THEN
    SPEC_TAC(k3,`k:num`) THEN SPEC_TAC(n0,`m:num`) THEN ARITH_TAC;
    ALL_TAC] THEN
  EXT4_LOAD_FACT_TAC 64 k (sb `n0 + 8 * i`)
   (UNDISCH_TAC `off + len <= 200` THEN
    UNDISCH_TAC (sb `n0 + 8 * i + 8 <= len`) THEN
    SPEC_TAC(n0,`m:num`) THEN ARITH_TAC) THEN
  ARM_STEPS_TAC EXT4_EXEC (1--4) THEN
  LOOP3_CNT_TAC n0 k3 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (sb `~(i + 1 = k3) <=> i + 1 < k3`)
    (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC (sb `i < k3`) THEN SPEC_TAC(k3,`k:num`) THEN ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  FIRST [EXT4_SAFETY_TAC;
         COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC;
         REWRITE_TAC[WORD_ADD_PTR] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
         SPEC_TAC(n0,`m:num`) THEN ARITH_TAC;
         EXT4_WORD_TAC THEN NO_TAC;
         EXT4_STATE_RULE_TAC(REWRITE_RULE[ZX64_128]) THEN
         REWRITE_TAC[SPECL [n0; `i:num`] LOOP3_ASSOC] THEN
         EXT_STORES_TAC THEN
         MATCH_MP_TAC READ_MEMORY_BYTES_EXTEND THEN CONJ_TAC THEN
         FIRST_ASSUM ACCEPT_TAC];;

let EXT4_LOOP3_EXIT n0 k3 =
  let sb = subst [n0,`n0:num`; k3,`k3:num`] in
  REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN (sb `n0 + 8 * k3 = 8 * (len DIV 8)`)
    (fun th -> EXT4_STATE_RULE_TAC(REWRITE_RULE[th])) THENL
   [FIRST [ACCEPT_TAC(SYM(SPEC `len:num` DIV8_SPLIT));
           REWRITE_TAC[ADD_CLAUSES]]; ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let EXT4_LOOP3_PHASE b nested n0 k3 (pos:tactic) (pro:tactic) (tail:tactic) =
  (if nested then EXT4_REASSOC_TAC else ALL_TAC) THEN
  ENSURES_EVENTS_SEQUENCE_TAC (ext4_label(ext4_l8 b ^ "_exit"))
    (EXT4_MID3 b) THEN CONJ_TAC THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC k3 (ext4_label(ext4_l8 b))
      (ext4_label(ext4_l8 b ^ "_exit")) (EXT4_INV3 b n0 k3) THEN
    REPEAT CONJ_TAC THENL
     [pos; pro; EXT4_LOOP3_BODY b n0 k3; EXT4_LOOP3_EXIT n0 k3];
    tail];;

(* ------------------------------------------------------------------------- *)
(* The paths of copy k.                                                      *)
(* ------------------------------------------------------------------------- *)

(*** The end of the loop of 8 bytes when len MOD 8 = 0 ***)

let EXT4_T30_TAC b =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN `8 * (len DIV 8) = len`
    (fun th -> EXT4_STATE_RULE_TAC(REWRITE_RULE[th])) THENL
   [UNDISCH_TAC `len MOD 8 = 0` THEN ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXT4_STEP_TAC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let EXT4_T31_PRO b =
  let (_,_,_,_,_,_,n,_) = b.esteps in
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC EXT4_EXEC (1--2) THEN TAIL3_CMP_TAC THEN
  ARM_STEPS_TAC EXT4_EXEC (3--n) THEN
  EXT_NORM_TAC THEN
  EXT4_FINISH_TAC
   (EXT4_CLOSE_TAC[ADD_0; SUB_0; WORD_SUB_MOD8; WORD_ADD_PTR]);;

let EXT4_TAIL3_TAC b =
  ASM_CASES_TAC `len MOD 8 = 0` THEN ASM_REWRITE_TAC[] THENL
   [EXT4_T30_TAC b;
    EXT4_BYTELOOP_TAC b `8 * (len DIV 8)` `(len MOD 8):num`
     (UNDISCH_TAC `~(len MOD 8 = 0)` THEN ARITH_TAC) (EXT4_T31_PRO b)];;

(*** The end of the loop of 32 bytes ***)

let EXT4_T20_TAC b =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  SUBGOAL_THEN `32 * (len DIV 32) = len`
    (fun th -> EXT4_STATE_RULE_TAC(REWRITE_RULE[th])) THENL
   [UNDISCH_TAC `len MOD 32 = 0` THEN ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXT4_STEP_TAC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let EXT4_T21_PRO b =
  let (_,_,_,_,n,_,_,_) = b.esteps in
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC EXT4_EXEC (1--2) THEN TAIL_CMP_TAC THEN
  ARM_STEPS_TAC EXT4_EXEC (3--4) THEN TAIL_TST_TAC THEN
  ARM_STEPS_TAC EXT4_EXEC (5--n) THEN
  EXT_NORM_TAC THEN
  EXT4_FINISH_TAC
   (EXT4_CLOSE_TAC[ADD_CLAUSES; SUB_0; WORD_SUB_MOD32; WORD_ADD_PTR]);;

let EXT4_T3_PRO b =
  let (_,_,_,_,_,n,_,_) = b.esteps in
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC EXT4_EXEC (1--2) THEN TAIL_CMP_TAC THEN
  ARM_STEPS_TAC EXT4_EXEC (3--4) THEN TAIL_TST_TAC THEN
  ARM_STEPS_TAC EXT4_EXEC (5--n) THEN
  EXT_NORM_TAC THEN
  EXT4_FINISH_TAC
   (TRY(ASM_SIMP_TAC[WORD_AND_FFFFFFF8_64]) THEN
    TRY(SUBST1_TAC(SPEC `len:num` DIV8_SPLIT)) THEN
    EXT4_CLOSE_TAC[ADD_CLAUSES; MULT_CLAUSES; WORD_ADD_0; WORD_ADD_PTR]);;

let EXT4_TAIL2_TAC b =
  ASM_CASES_TAC `len MOD 32 = 0` THEN ASM_REWRITE_TAC[] THENL
   [EXT4_T20_TAC b; ALL_TAC] THEN
  ASM_CASES_TAC `len MOD 32 < 8` THEN ASM_REWRITE_TAC[] THENL
   [EXT4_BYTELOOP_TAC b `32 * (len DIV 32)` `(len MOD 32):num`
      (UNDISCH_TAC `~(len MOD 32 = 0)` THEN ARITH_TAC) (EXT4_T21_PRO b);
    EXT4_LOOP3_PHASE b true `32 * (len DIV 32)` `(len MOD 32) DIV 8`
      (UNDISCH_TAC `~(len MOD 32 < 8)` THEN
       SPEC_TAC(`len MOD 32`,`r:num`) THEN ARITH_TAC)
      (EXT4_T3_PRO b) (EXT4_TAIL3_TAC b)];;

(*** From the start of the copy to its first loop ***)

let EXT4_PRO_TAC b n =
  EXT4_ENTRY_TAC b n THEN
  EXT4_FINISH_TAC
   (TRY(ASM_SIMP_TAC[WORD_AND_FFFFFFE0_64; WORD_AND_FFFFFFF8_64]) THEN
    EXT4_CLOSE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; MULT_CLAUSES;
                   EXP; MOD_1; ADD_CLAUSES; SUB_0; WORD_ADD_0]);;

let EXT4_PATH_A_TAC b nested =
  let (_,_,n,_,_,_,_,_) = b.esteps in
  EXT4_LOOP3_PHASE b nested `0` `len DIV 8`
    (UNDISCH_TAC `~(len <= 7)` THEN ARITH_TAC)
    (EXT4_PRO_TAC b n) (EXT4_TAIL3_TAC b);;

let EXT4_PATH_B_TAC b nested =
  let (_,_,_,n,_,_,_,_) = b.esteps in
  (if nested then EXT4_REASSOC_TAC else ALL_TAC) THEN
  ENSURES_EVENTS_SEQUENCE_TAC (ext4_label(ext4_l32 b ^ "_exit"))
    (EXT4_MIDV b) THEN CONJ_TAC THENL
   [ENSURES_EVENTS_WHILE_UP2_TAC `len DIV 32` (ext4_label(ext4_l32 b))
      (ext4_label(ext4_l32 b ^ "_exit")) (EXT4_INV2 b) THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `~(len < 32)` THEN ARITH_TAC;
      EXT4_PRO_TAC b n; EXT4_V2_BODY b; EXT_V2_EXIT];
    EXT4_TAIL2_TAC b];;

let EXT4_BLOCK_TAC b =
  let (n1,n2,_,_,_,_,_,_) = b.esteps in
  let nested = b.ek > 0 in
  ASM_CASES_TAC `len <= 7` THEN ASM_REWRITE_TAC[] THENL
   [EXT4_BYTELOOP_TAC b `0` `len:num` EXT_POS0_TAC (EXT4_PRO_TAC b n1);
    ALL_TAC] THEN
  ASM_CASES_TAC (parse_term(ext4_alias b.ek)) THEN ASM_REWRITE_TAC[] THENL
   [EXT4_BYTELOOP_TAC b `0` `len:num` EXT_POS0_TAC (EXT4_PRO_TAC b n2);
    ALL_TAC] THEN
  ASM_CASES_TAC `len < 32` THEN ASM_REWRITE_TAC[] THENL
   [EXT4_PATH_A_TAC b nested; EXT4_PATH_B_TAC b nested];;

(* ------------------------------------------------------------------------- *)
(* The whole function.                                                       *)
(* ------------------------------------------------------------------------- *)

let EXT4_INTRO_TAC =
  CONCRETIZE_F_EVENTS_TAC EXT4_EVENTS_TERM THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `d0:int64`; `d1:int64`; `d2:int64`; `d3:int64`;
    `off:num`; `len:num`; `S0:1600 word`; `S1:1600 word`; `S2:1600 word`;
    `S3:1600 word`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              READ_MEMORY_WBYTES_VAL; fst EXT4_EXEC] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `len < 2 EXP 32` ASSUME_TAC THENL
   [UNDISCH_TAC `off + len <= 200` THEN ARITH_TAC; ALL_TAC];;

let EXT4_LEN0_TAC =
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC EXT4_EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let EXT4_RET_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC EXT4_EXEC (1--1) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let EXT4_MAIN_TAC =
  EXT4_INTRO_TAC THEN
  ASM_CASES_TAC `len = 0` THEN ASM_REWRITE_TAC[] THENL
   [EXT4_LEN0_TAC; ALL_TAC] THEN
  ENSURES_EVENTS_SEQUENCE_TAC (ext4_label "ret") (EXT4_INV 4) THEN
  CONJ_TAC THENL
   [ENSURES_EVENTS_SEQUENCE_TAC (ext4_label "join9") (EXT4_INV 3) THEN
    CONJ_TAC THENL
     [ENSURES_EVENTS_SEQUENCE_TAC (ext4_label "join6") (EXT4_INV 2) THEN
      CONJ_TAC THENL
       [ENSURES_EVENTS_SEQUENCE_TAC (ext4_label "join3") (EXT4_INV 1) THEN
        CONJ_TAC THENL
         [EXT4_BLOCK_TAC (el 0 ext4_blocks);
          EXT4_BLOCK_TAC (el 1 ext4_blocks)];
        EXT4_BLOCK_TAC (el 2 ext4_blocks)];
      EXT4_BLOCK_TAC (el 3 ext4_blocks)];
    EXT4_RET_TAC];;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof. The four     *)
(* states, each a 1600-bit word as for mlkem_keccakf1600_extract_bytes, are  *)
(* consecutive in memory. The events are those of the copies for the paths  *)
(* that they take, which depend only on len and on the alias tests.          *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_FULL =
  prove
 (`exists f_events.
     forall e a d0 d1 d2 d3 off len (S0:1600 word) (S1:1600 word)
            (S2:1600 word) (S3:1600 word) pc returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       off + len <= 200 /\
       PAIRWISE nonoverlapping [d0,len; d1,len; d2,len; d3,len] /\
       ALLPAIRS nonoverlapping [d0,len; d1,len; d2,len; d3,len]
        [word pc,libmlkem_size; a,800]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_clang17_O3_mc /\
                 read PC s = word (pc + mlkem_keccakf1600x4_extract_bytes) /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [a; d0; d1; d2; d3; word off; word len] s /\
                 read (memory :> wbytes a) s = S0 /\
                 read (memory :> wbytes (word_add a (word 200))) s = S1 /\
                 read (memory :> wbytes (word_add a (word 400))) s = S2 /\
                 read (memory :> wbytes (word_add a (word 600))) s = S3 /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 read (memory :> bytes(d0,len)) s =
                 (val S0 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                 read (memory :> bytes(d1,len)) s =
                 (val S1 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                 read (memory :> bytes(d2,len)) s =
                 (val S2 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                 read (memory :> bytes(d3,len)) s =
                 (val S3 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a d0 d1 d2 d3 off len pc returnaddress /\
                    memaccess_inbounds e2
                     [a,800; d0,len; d1,len; d2,len; d3,len]
                     [d0,len; d1,len; d2,len; d3,len]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(d0,len); memory :> bytes(d1,len);
                        memory :> bytes(d2,len); memory :> bytes(d3,len)])`,
  EXT4_MAIN_TAC);;

(* ------------------------------------------------------------------------- *)
(* The theorems of correctness and of constant time and memory safety, from  *)
(* the combined one.                                                         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT
  = prove
 (`!a d0 d1 d2 d3 off len (S0:1600 word) (S1:1600 word) (S2:1600 word)
    (S3:1600 word) pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        off + len <= 200 /\
        PAIRWISE nonoverlapping [(d0,len); (d1,len); (d2,len); (d3,len)] /\
        ALLPAIRS nonoverlapping [(d0,len); (d1,len); (d2,len); (d3,len)]
         [(word pc,libmlkem_size); (a,800)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem_keccakf1600x4_extract_bytes) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; d0; d1; d2; d3; word off; word len] s /\
                  read (memory :> wbytes a) s = S0 /\
                  read (memory :> wbytes (word_add a (word 200))) s = S1 /\
                  read (memory :> wbytes (word_add a (word 400))) s = S2 /\
                  read (memory :> wbytes (word_add a (word 600))) s = S3)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(d0,len)) s =
                  (val S0 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                  read (memory :> bytes(d1,len)) s =
                  (val S1 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                  read (memory :> bytes(d2,len)) s =
                  (val S2 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                  read (memory :> bytes(d3,len)) s =
                  (val S3 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(d0,len); memory :> bytes(d1,len);
                         memory :> bytes(d2,len); memory :> bytes(d3,len)])`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_TAC
   `f:int64->int64->int64->int64->int64->num->num->num->int64->
      (uarch_event)list`
   MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_FULL THEN
  GHOST_INTRO_TAC `e:(uarch_event)list` `read events` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`; `d0:int64`; `d1:int64`; `d2:int64`;
    `d3:int64`; `off:num`; `len:num`; `S0:1600 word`; `S1:1600 word`;
    `S2:1600 word`; `S3:1600 word`; `pc:num`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;

let MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  prove
 (`exists f_events.
     forall e a d0 d1 d2 d3 off len pc returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       off + len <= 200 /\
       PAIRWISE nonoverlapping [d0,len; d1,len; d2,len; d3,len] /\
       ALLPAIRS nonoverlapping [d0,len; d1,len; d2,len; d3,len]
        [word pc,libmlkem_size; a,800]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_clang17_O3_mc /\
                 read PC s = word (pc + mlkem_keccakf1600x4_extract_bytes) /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [a; d0; d1; d2; d3; word off; word len] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a d0 d1 d2 d3 off len pc returnaddress /\
                    memaccess_inbounds e2
                     [a,800; d0,len; d1,len; d2,len; d3,len]
                     [d0,len; d1,len; d2,len; d3,len]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(d0,len); memory :> bytes(d1,len);
                        memory :> bytes(d2,len); memory :> bytes(d3,len)])`,
  MP_TAC
   MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun (v,t) -> GHOST_INTRO_TAC v t)
   [`S0:1600 word`,`read (memory :> wbytes a):armstate->1600 word`;
    `S1:1600 word`,
    `read (memory :> wbytes (word_add a (word 200))):armstate->1600 word`;
    `S2:1600 word`,
    `read (memory :> wbytes (word_add a (word 400))):armstate->1600 word`;
    `S3:1600 word`,
    `read (memory :> wbytes (word_add a (word 600))):armstate->1600 word`] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`; `d0:int64`; `d1:int64`; `d2:int64`;
    `d3:int64`; `off:num`; `len:num`; `S0:1600 word`; `S1:1600 word`;
    `S2:1600 word`; `S3:1600 word`; `pc:num`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;
