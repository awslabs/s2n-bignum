(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a polynomial to 10 bits per coefficient. This is the code  *)
(* for mlkem_poly_compress_d10 from mlkem-native's portable C implementation *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md). It is verified  *)
(* in the whole image (see libmlkem.ml). It saves four registers on the      *)
(* stack and computes the four 10-bit values for each five bytes of the      *)
(* result into the eight bytes below them, in the red zone, so it is         *)
(* verified directly as a subroutine, with that part of the stack.           *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_compress_d10:
       +0x0: push   r13
       +0x2: lea    rdx,[rdi+0x4]
       +0x6: xor    ecx,ecx
       +0x8: mov    r8d,0x9d7dbc00
       +0xe: movabs rdi,0x100000000
      +0x18: push   r12
      +0x1a: push   rbp
      +0x1b: push   rbx
      +0x1c: lea    r10,[rsp-0x8]
      +0x21: mov    r9,rsp
      +0x24: nop    DWORD PTR [rax+0x0]
      +0x28: mov    r11,r10
      +0x2b: mov    ebx,ecx
      +0x2d: mov    eax,ebx
      +0x2f: add    r11,0x2
      +0x33: add    ebx,0x1
      +0x36: movsx  rax,WORD PTR [rsi+rax*2]
      +0x3b: imul   rax,r8
      +0x3f: add    rax,rdi
      +0x42: shr    rax,0x21
      +0x46: and    ax,0x3ff
      +0x4a: mov    WORD PTR [r11-0x2],ax
      +0x4f: cmp    r9,r11
      +0x52: jne    <mlkem_poly_compress_d10+0x2d>
      +0x54: movzx  ebx,WORD PTR [rsp-0x8]
      +0x59: movzx  r12d,WORD PTR [rsp-0x6]
      +0x5f: add    ecx,0x4
      +0x62: add    rdx,0x5
      +0x66: movzx  eax,WORD PTR [rsp-0x4]
      +0x6b: movzx  r11d,WORD PTR [rsp-0x2]
      +0x71: mov    r13d,ebx
      +0x74: lea    ebp,[r12*4+0x0]
      +0x7c: shr    r12w,0x6
      +0x81: movzx  ebx,bl
      +0x84: shr    r13w,0x8
      +0x89: or     ebp,r13d
      +0x8c: mov    r13d,eax
      +0x8f: shr    ax,0x4
      +0x93: shl    r13d,0x4
      +0x97: movzx  ebp,bpl
      +0x9b: or     r12d,r13d
      +0x9e: mov    r13d,eax
      +0xa1: mov    eax,r11d
      +0xa4: shr    r11w,0x2
      +0xa9: shl    eax,0x6
      +0xac: movzx  r12d,r12b
      +0xb0: mov    BYTE PTR [rdx-0x5],r11b
      +0xb4: or     eax,r13d
      +0xb7: movzx  eax,al
      +0xba: shl    eax,0x8
      +0xbd: or     eax,r12d
      +0xc0: shl    eax,0x8
      +0xc3: or     eax,ebp
      +0xc5: shl    eax,0x8
      +0xc8: or     eax,ebx
      +0xca: mov    DWORD PTR [rdx-0x9],eax
      +0xcd: cmp    ecx,0x100
      +0xd3: jne    <mlkem_poly_compress_d10+0x28>
      +0xd9: pop    rbx
      +0xda: pop    rbp
      +0xdb: pop    r12
      +0xdd: pop    r13
      +0xdf: ret
 ***)

let MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem_poly_compress_d10"];;

(* ------------------------------------------------------------------------- *)
(* The compression of a coefficient to 10 bits, as computed.                 *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D10_ARITH_STMT =
  `!v. v < 3329
       ==> (4294967296 + v * 2642263040) DIV 8589934592 =
           (2048 * v + 3329) DIV 6658`;;

let COMPRESS_D10_ARITH =
  assume_spec COMPRESS_D10_ARITH_STMT;;

let WORD_SX_SMALL_64_STMT =
  `!y:int16. val y < 32768 ==> (word_sx y:int64) = word_zx y`;;

let WORD_SX_SMALL_64 =
  assume_spec WORD_SX_SMALL_64_STMT;;

let COMPRESS_D10_FIELD_STMT =
  `!y:int16.
        val y < 3329
        ==> val(word_subword
                 (word_add (word_mul (word_sx y:int64) (word 2642263040))
                           (word 4294967296))
                 (33,10):10 word) =
            ((2048 * val y + 3329) DIV 6658) MOD 1024`;;

let COMPRESS_D10_FIELD =
  assume_spec COMPRESS_D10_FIELD_STMT;;

(* ------------------------------------------------------------------------- *)
(* The packing of four 10-bit values into five bytes.                        *)
(* ------------------------------------------------------------------------- *)

let BYTES_OF_NUM_5_STMT =
  `!n. n < 2 EXP 40
       ==> n MOD 256 + 256 * (n DIV 256) MOD 256 +
           65536 * (n DIV 65536) MOD 256 +
           16777216 * (n DIV 16777216) MOD 256 +
           4294967296 * (n DIV 4294967296) MOD 256 = n`;;

let BYTES_OF_NUM_5 =
  assume_spec BYTES_OF_NUM_5_STMT;;

let VAL_JOIN_10X4_STMT =
  `!(u0:10 word) (u1:10 word) (u2:10 word) (u3:10 word).
     val(word_join u3 (word_join u2 (word_join u1 u0:20 word):30 word):
         40 word) =
     val u0 + 1024 * val u1 + 1048576 * val u2 + 1073741824 * val u3`;;

let VAL_JOIN_10X4 =
  assume_spec VAL_JOIN_10X4_STMT;;

(*** The stored bytes as parts of the 40-bit join of the four fields. The
 *** first four are stored together, and the fifth is stored with the
 *** pointer incremented, so its address is put in the same form.
 ***)

let d10_indices = map (fun k ->
  if k = 0 then `4 * i` else
  mk_binop `(+):num->num->num` `4 * i` (mk_small_numeral k)) (0--4);;

let d10_xatoms = map (fun j ->
  vsubst [j,`j:num`]
   `word_add (word_mul (word_sx ((x:num->int16) j):int64) (word 2642263040))
             (word 4294967296):int64`) (butlast d10_indices);;

let d10_join =
  vsubst (zip d10_xatoms [`w0:int64`; `w1:int64`; `w2:int64`; `w3:int64`])
  `word_join (word_subword (w3:int64) (33,10):10 word)
    (word_join (word_subword (w2:int64) (33,10):10 word)
      (word_join (word_subword (w1:int64) (33,10):10 word)
                 (word_subword (w0:int64) (33,10):10 word):20 word):30 word):
    40 word`;;

let D10_PACK_TAC =
  let rule m th =
    let th1 = CONV_RULE(RAND_CONV(REWRITE_CONV
       [WORD_VAL_MOD_256; WORD_VAL_MOD_65536] THENC
       SIMD_SIMPLIFY_CONV [])) th in
    let v = rand(concl th1) in
    let target = mk_comb(mk_comb(`word_subword:40 word->num#num->byte`,
                                 d10_join),
                         mk_pair(mk_small_numeral(8 * m),`8`)) in
    let gvs = map (fun _ -> genvar `:int64`) d10_xatoms in
    let eq = subst (zip gvs d10_xatoms) (mk_eq(v,target)) in
    let bth = INST (zip d10_xatoms gvs) (BITBLAST_RULE eq) in
    CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THENC
                        NUM_REDUCE_CONV)) (TRANS th1 bth) in
  W(fun (asl,w) ->
    let get pat =
      snd(find (fun (_,th) -> can (term_match [] pat) (concl th)) asl) in
    let th4 = get
      `read (memory :> bytes32 (word_add r (word (5 * i)))) s = x`
    and th1 = get
      `read (memory :> bytes8 (word_add (word_add r (word (5 * i)))
                                        (word 4))) s = x` in
    MAP_EVERY ASSUME_TAC
     (map2 rule (0--4)
        (CONJUNCTS(CONV_RULE(READ_MEMORY_SPLIT_CONV 2) th4) @ [th1])));;

(* ------------------------------------------------------------------------- *)
(* The loops. The inner one, unrolled in the simulation, computes four       *)
(* 10-bit values into the red zone; EAX is the index of the coefficient,     *)
(* which is tidied up before it is used in the address of the load. The      *)
(* pointer to the result is put in the form of the addresses of the stores   *)
(* before it is incremented.                                                 *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D10_INDEX_TAC k =
  let jt = el k d10_indices in
  let wt = mk_comb(`word:num->int64`,jt) in
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read RAX s = x`) c then
      MP_TAC th THEN SUBGOAL_THEN (mk_eq(rand c,wt)) SUBST1_TAC THENL
       [WORD_SMALL_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,wt),jt)) ASSUME_TAC THENL
       [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        UNDISCH_TAC `i < 64` THEN ARITH_TAC;
        ALL_TAC]
    else failwith "COMPRESS_D10_INDEX_TAC");;

let COMPRESS_D10_BODY_TAC =
  X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC (1--2) THEN
  MAP_EVERY (fun k ->
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC
     [3 + 11 * k] THEN
    COMPRESS_D10_INDEX_TAC k THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC
     ((4 + 11 * k)--(13 + 11 * k)) THEN
    PTR_DECIDE_RIP_TAC) (0--3) THEN
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read RDX s = word_add r (word (5 * i + 4))`)
           (concl th)
    then REWRITE_RULE[WORD_RULE
          `word_add r (word (5 * i + 4)):int64 =
           word_add (word_add r (word (5 * i))) (word 4)`] th
    else th) THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_EXEC (47--78);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_compress 10 in common/fips203/fips203.ml, *)
(* the result for a coefficient x in [0,3329) is the integer closest to      *)
(* 1024 * x / 3329, rounding up on ties, modulo 1024, i.e.                   *)
(* ((2048 * x + 3329) DIV 6658) MOD 1024, and as for mlkem_encode 10 the     *)
(* 10-bit values are put together little-endian. Like the C code, this       *)
(* relies on the coefficients being in [0,3329).                             *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a x pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        ALL (nonoverlapping (r,320))
            [(word pc,libmlkem_size); (a,512);
             (word_sub stackpointer (word 40),48)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 40),48))
            [(word pc,libmlkem_size); (a,512)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + mlkem_poly_compress_d10) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes16
                                     (word_add a (word(2 * i)))) s =
                           x i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,320)) s =
                       nsum {i | i < 256}
                            (\i. ((2048 * val(x i) + 3329) DIV 6658) MOD 1024 *
                                 2 EXP (10 * i))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,320);
                         memory :> bytes(word_sub stackpointer
                                                  (word 40),40)])`;;

let MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, stated directly in the same way.   *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e r a pc stackpointer returnaddress.
       aligned 16 (word pc:int64) /\
       ALL (nonoverlapping (r,320))
           [word pc,libmlkem_size; a,512; word_sub stackpointer (word 40),48] /\
       ALL (nonoverlapping (word_sub stackpointer (word 40),48))
           [word pc,libmlkem_size; a,512]
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + mlkem_poly_compress_d10) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [r; a] s /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a r pc
                           (word_sub stackpointer (word 40)) returnaddress /\
                    memaccess_inbounds e2
                     [a,512; r,320; word_sub stackpointer (word 40),48]
                     [r,320; word_sub stackpointer (word 40),40]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(r,320);
                        memory :> bytes(word_sub stackpointer (word 40),40)])`;;

let MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
