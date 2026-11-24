(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of the functions of the AVX-512 version of the x86   *)
(* mlkem_native2 that run the Keccak sponge of common/fips202/fips202.ml     *)
(* with sha3_keccak_f1600_avx512 on a state in memory (mlkem_hash_h_avx512   *)
(* and mlkem_hash_g_avx512): the state as the 1600-bit word read by wbytes,  *)
(* given by its 25 lanes or its 200 bytes; the theorems for                  *)
(* sha3_keccak_f1600_avx512 in the image, on such a state; the round         *)
(* constants as bytes; and the XOR of the blocks of the message and of the   *)
(* padding into the state, lane by lane or byte by byte, with the padded     *)
(* message as a number for keccak_absorb. A copy of                          *)
(* utils/mlkem_native2_sponge.ml for the AVX2 version, with                  *)
(* sha3_keccak_f1600_avx512 in place of sha3_keccak_f1600_alt2.              *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/asm_avx512/layout.ml";;
needs "x86/proofs/mlkem_native/asm_avx512/sha3_keccak_f1600_avx512_spec.ml";;
needs "x86/proofs/utils/keccak_fips202.ml";;
needs "x86/proofs/utils/mlkem_bytes.ml";;

(* ------------------------------------------------------------------------- *)
(* A Keccak state in memory, as a 1600-bit word, by its 64-bit lanes or by   *)
(* its bytes, and a zero state from stores of 32 and 8 bytes; and a read of  *)
(* 32 bytes from a number in memory.                                         *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_WBYTES_VAL = prove
 (`!a:int64 (x:N word) s:x86state.
        read (memory :> wbytes a) s = x <=>
        read (memory :> bytes(a,dimindex(:N) DIV 8)) s = val x`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM VAL_EQ] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; VAL_READ_WBYTES]);;

let READ_MEMORY_WBYTES_1600 =
  CONV_RULE(DEPTH_CONV DIMINDEX_CONV THENC ONCE_DEPTH_CONV NUM_DIV_CONV)
   (INST_TYPE [`:1600`,`:N`] READ_MEMORY_WBYTES_VAL);;

let READ_MEMORY_BYTES_OF_BYTES64_STMT =
  `!a:int64 n x s:x86state.
        (!j. j < n
             ==> read (memory :> bytes64(word_add a (word(8 * j)))) s =
                 word((x DIV 2 EXP (64 * j)) MOD 2 EXP 64))
        ==> read (memory :> bytes(a,8 * n)) s = x MOD 2 EXP (64 * n)`;;

let READ_MEMORY_BYTES_OF_BYTES64 = assume_spec READ_MEMORY_BYTES_OF_BYTES64_STMT;;

let READ_MEMORY_BYTES_OF_BYTES128_STMT =
  `!a:int64 n x s:x86state.
        (!j. j < n
             ==> read (memory :> bytes128(word_add a (word(16 * j)))) s =
                 word((x DIV 2 EXP (128 * j)) MOD 2 EXP 128))
        ==> read (memory :> bytes(a,16 * n)) s = x MOD 2 EXP (128 * n)`;;

let READ_MEMORY_BYTES_OF_BYTES128 = assume_spec READ_MEMORY_BYTES_OF_BYTES128_STMT;;

let READ_MEMORY_BYTES_OF_BYTES256_STMT =
  `!a:int64 n x s:x86state.
        (!j. j < n
             ==> read (memory :> bytes256(word_add a (word(32 * j)))) s =
                 word((x DIV 2 EXP (256 * j)) MOD 2 EXP 256))
        ==> read (memory :> bytes(a,32 * n)) s = x MOD 2 EXP (256 * n)`;;

let READ_MEMORY_BYTES_OF_BYTES256 = assume_spec READ_MEMORY_BYTES_OF_BYTES256_STMT;;

let READ_MEMORY_WBYTES_LANES_STMT =
  `!a (S:1600 word) s:x86state.
        read (memory :> wbytes a) s = S <=>
        !j. j < 25
            ==> read (memory :> bytes64(word_add a (word(8 * j)))) s =
                word_subword S (64 * j,64)`;;

let READ_MEMORY_WBYTES_LANES = assume_spec READ_MEMORY_WBYTES_LANES_STMT;;

let READ_MEMORY_WBYTES_BYTES_STMT =
  `!a (S:1600 word) s:x86state.
        read (memory :> wbytes a) s = S <=>
        !j. j < 200
            ==> read (memory :> bytes8(word_add a (word j))) s =
                word_subword S (8 * j,8)`;;

let READ_MEMORY_WBYTES_BYTES = assume_spec READ_MEMORY_WBYTES_BYTES_STMT;;

let READ_MEMORY_WBYTES_ZERO_STMT =
  `!a:int64 s:x86state.
        (!j. j < 6
             ==> read (memory :> bytes256(word_add a (word(32 * j)))) s =
                 word 0) /\
        read (memory :> bytes64(word_add a (word 192))) s = word 0
        ==> read (memory :> wbytes a) s = (word 0:1600 word)`;;

let READ_MEMORY_WBYTES_ZERO = assume_spec READ_MEMORY_WBYTES_ZERO_STMT;;

let READ_MEMORY_BYTES256_OF_NUM_STMT =
  `!a:int64 m n k s:x86state.
        read (memory :> bytes(a,m)) s = n /\ k + 32 <= m
        ==> read (memory :> bytes256(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 2 EXP 256)`;;

let READ_MEMORY_BYTES256_OF_NUM = assume_spec READ_MEMORY_BYTES256_OF_NUM_STMT;;

(* ------------------------------------------------------------------------- *)
(* sha3_keccak_f1600_avx512 in the image, at pc + sha3_keccak_f1600_avx512:  *)
(* its code is the code in the image there, so its theorems hold with the    *)
(* image loaded. Also the theorem with the state as a 1600-bit word, and the *)
(* round constants as bytes in memory, which unlike wordlist_from_memory are *)
(* kept by the simulation over other stores.                                 *)
(* ------------------------------------------------------------------------- *)

let mlkem_native2_avx512_keccak_x1_code,
    MLKEM_NATIVE2_AVX512_KECCAK_X1_CODE_LOADED =
  x86_image_data mlkem_native2_avx512_image_mc
    "mlkem_native2_avx512_keccak_x1_code"
    (layout "sha3_keccak_f1600_avx512")
    (layout "sha3_keccak_f1600_avx512_size");;

let MLKEM_NATIVE2_AVX512_KECCAK_X1_MC_STMT =
  `sha3_keccak_f1600_avx512_mc = mlkem_native2_avx512_keccak_x1_code`;;

let MLKEM_NATIVE2_AVX512_KECCAK_X1_MC = assume_spec MLKEM_NATIVE2_AVX512_KECCAK_X1_MC_STMT;;

let SHA3_KECCAK_F1600_AVX512_IMAGE_CORRECT_STMT =
  `!a rc A pc stackpointer returnaddress.
     nonoverlapping (a,200) (word pc,mlkem_native2_avx512_image_size) /\
     nonoverlapping (a,200) (rc,192) /\
     nonoverlapping (a,200) (stackpointer,8)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_native2_avx512_image_mc /\
               read RIP s = word(pc + sha3_keccak_f1600_avx512) /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [a; rc] s /\
               wordlist_from_memory(rc,24) s = round_constants /\
               wordlist_from_memory(a,25) s = A)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               wordlist_from_memory(a,25) s = keccak 24 A)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(a,200)])`;;

let SHA3_KECCAK_F1600_AVX512_IMAGE_CORRECT = assume_spec SHA3_KECCAK_F1600_AVX512_IMAGE_CORRECT_STMT;;

let SHA3_KECCAK_F1600_AVX512_IMAGE_CORRECT_F1600_STMT =
  `!a rc (S:1600 word) pc stackpointer returnaddress.
     nonoverlapping (a,200) (word pc,mlkem_native2_avx512_image_size) /\
     nonoverlapping (a,200) (rc,192) /\
     nonoverlapping (a,200) (stackpointer,8)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_native2_avx512_image_mc /\
               read RIP s = word(pc + sha3_keccak_f1600_avx512) /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [a; rc] s /\
               wordlist_from_memory(rc,24) s = round_constants /\
               read (memory :> wbytes a) s = S)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               read (memory :> wbytes a) s = keccak_f1600 S)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(a,200)])`;;

let SHA3_KECCAK_F1600_AVX512_IMAGE_CORRECT_F1600 = assume_spec SHA3_KECCAK_F1600_AVX512_IMAGE_CORRECT_F1600_STMT;;

let WORDLIST_FROM_MEMORY_ROUND_CONSTANTS_STMT =
  `!c s. wordlist_from_memory(c,24) s = round_constants <=>
         read (memory :> bytes(c,192)) s = num_of_wordlist round_constants`;;

let WORDLIST_FROM_MEMORY_ROUND_CONSTANTS = assume_spec WORDLIST_FROM_MEMORY_ROUND_CONSTANTS_STMT;;

(* ------------------------------------------------------------------------- *)
(* The padded message as a number, as in keccak_sponge: the blocks that      *)
(* keccak_absorb takes from it, the XOR of a block into the state lane by    *)
(* lane, and the last block as the remaining bytes of the message, the       *)
(* domain byte d after them and the final bit at the end of the block.       *)
(* ------------------------------------------------------------------------- *)

let keccak_padded = new_definition
 `keccak_padded r d (m:byte list) =
  num_of_bytelist m +
  2 EXP (8 * LENGTH m) * num_of_bytelist(keccak_pad r d (LENGTH m))`;;

let KECCAK_XOR_LANE_STMT =
  `!(S:1600 word) B n j.
        B < 2 EXP (64 * n) /\ j < 25
        ==> word_subword (word_xor S (word B)) (64 * j,64):int64 =
            if j < n then word_xor (word_subword S (64 * j,64))
                                   (word((B DIV 2 EXP (64 * j)) MOD 2 EXP 64))
            else word_subword S (64 * j,64)`;;

let KECCAK_XOR_LANE = assume_spec KECCAK_XOR_LANE_STMT;;

let KECCAK_BLOCK_LANE_STMT =
  `!M r i j.
        8 * j + 8 <= r
        ==> (((M DIV 2 EXP (8 * r * i)) MOD 2 EXP (8 * r)) DIV
             2 EXP (64 * j)) MOD 2 EXP 64 =
            (M DIV 2 EXP (8 * (r * i + 8 * j))) MOD 2 EXP 64`;;

let KECCAK_BLOCK_LANE = assume_spec KECCAK_BLOCK_LANE_STMT;;

let KECCAK_LAST_BLOCK_XOR_STMT =
  `!r d (m:byte list).
        0 < r /\ d < 128
        ==> word((keccak_padded r d m DIV 2 EXP (8 * r * LENGTH m DIV r)) MOD
                 2 EXP (8 * r)):1600 word =
            word_xor
             (word_xor
               (word(num_of_bytelist m DIV 2 EXP (8 * r * LENGTH m DIV r)))
               (word(2 EXP (8 * LENGTH m MOD r) * d)))
             (word(2 EXP (8 * (r - 1)) * 128))`;;

let KECCAK_LAST_BLOCK_XOR = assume_spec KECCAK_LAST_BLOCK_XOR_STMT;;

(* ------------------------------------------------------------------------- *)
(* The XOR of a prefix of a number into a state, extended by one lane or one *)
(* byte, as for a loop over the last words or bytes of the message; and the  *)
(* bytes of the state after a byte c is XORed into byte p.                   *)
(* ------------------------------------------------------------------------- *)

let ODD_MOD_DIV_POW2_STMT =
  `!n a i. ODD((n MOD 2 EXP a) DIV 2 EXP i) <=> i < a /\ ODD(n DIV 2 EXP i)`;;

let ODD_MOD_DIV_POW2 = assume_spec ODD_MOD_DIV_POW2_STMT;;

let XOR_PREFIX_STEP_TAC =
  let thens = map ARITH_RULE
   [`b < 64 /\ k < 25 ==> (64 * k + b < 1600 <=> T)`;
    `b < 64 ==> (64 * k + b < 64 * (k + 1) <=> T)`;
    `64 * k + b < 64 * k <=> F`;
    `b < 8 /\ k < 200 ==> (8 * k + b < 1600 <=> T)`;
    `b < 8 ==> (8 * k + b < 8 * (k + 1) <=> T)`;
    `8 * k + b < 8 * k <=> F`]
  and elses = map ARITH_RULE
   [`b < 64 /\ j < 25 ==> (64 * j + b < 1600 <=> T)`;
    `~(j = k) /\ b < 64
     ==> (64 * j + b < 64 * (k + 1) <=> 64 * j + b < 64 * k)`;
    `b < 8 /\ j < 200 ==> (8 * j + b < 1600 <=> T)`;
    `~(j = k) /\ b < 8
     ==> (8 * j + b < 8 * (k + 1) <=> 8 * j + b < 8 * k)`] in
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC; ALL_TAC] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_SUBWORD; BIT_WORD_XOR;
              BIT_WORD; DIMINDEX_64; DIMINDEX_8;
              DIMINDEX_CONV `dimindex(:1600)`;
              ARITH_RULE `MIN 64 64 = 64 /\ MIN 8 8 = 8`] THEN
  X_GEN_TAC `b:num` THEN DISCH_TAC THEN
  REWRITE_TAC[ODD_MOD_DIV_POW2; DIV_DIV; GSYM EXP_ADD] THENL
   [ASM_SIMP_TAC thens; ASM_SIMP_TAC elses] THEN
  CONV_TAC TAUT;;

let LANE_XOR_STEP_STMT =
  `!(S:1600 word) n k j.
        k < 25 /\ j < 25
        ==> word_subword (word_xor S (word(n MOD 2 EXP (64 * (k + 1)))))
                         (64 * j,64):int64 =
            if j = k
            then word_xor
                  (word_subword (word_xor S (word(n MOD 2 EXP (64 * k))))
                                (64 * j,64))
                  (word((n DIV 2 EXP (64 * k)) MOD 2 EXP 64))
            else word_subword (word_xor S (word(n MOD 2 EXP (64 * k))))
                              (64 * j,64)`;;

let LANE_XOR_STEP = assume_spec LANE_XOR_STEP_STMT;;

let BYTE_XOR_STEP_STMT =
  `!(S:1600 word) n k j.
        k < 200 /\ j < 200
        ==> word_subword (word_xor S (word(n MOD 2 EXP (8 * (k + 1)))))
                         (8 * j,8):byte =
            if j = k
            then word_xor
                  (word_subword (word_xor S (word(n MOD 2 EXP (8 * k))))
                                (8 * j,8))
                  (word((n DIV 2 EXP (8 * k)) MOD 2 EXP 8))
            else word_subword (word_xor S (word(n MOD 2 EXP (8 * k))))
                              (8 * j,8)`;;

let BYTE_XOR_STEP = assume_spec BYTE_XOR_STEP_STMT;;

let BYTE_XOR_SHIFT_STMT =
  `!(S:1600 word) c p j.
        c < 256 /\ p < 200 /\ j < 200
        ==> word_subword (word_xor S (word(2 EXP (8 * p) * c)))
                         (8 * j,8):byte =
            if j = p then word_xor (word_subword S (8 * j,8)) (word c)
            else word_subword S (8 * j,8)`;;

let BYTE_XOR_SHIFT = assume_spec BYTE_XOR_SHIFT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The byte AL of the register RAX after a load of a byte into EAX with zero *)
(* extension, as the simulation of movzx and an operation on AL gives it.    *)
(* ------------------------------------------------------------------------- *)

let BYTE_ZX_X86_STMT =
  `!x:byte. word(val(word_zx(word_zx x:int32):int64) MOD 256):byte = x`;;

let BYTE_ZX_X86 = assume_spec BYTE_ZX_X86_STMT;;

(* ------------------------------------------------------------------------- *)
(* The count t MOD 8 of the single bytes of the last block, as the           *)
(* simulation of the 32-bit "and ecx, 7" on the length t in RCX gives        *)
(* RCX and the test of ZF on it.                                             *)
(* ------------------------------------------------------------------------- *)

let WORD_AND_7_ZX32_STMT =
  `!t. t < 2 EXP 32
       ==> word_zx(word_and (word_zx (word t:int64):int32) (word 7)):int64 =
           word(t MOD 8) /\
           val(word_and (word_zx (word t:int64):int32) (word 7)) = t MOD 8`;;

let WORD_AND_7_ZX32 = assume_spec WORD_AND_7_ZX32_STMT;;

(* ------------------------------------------------------------------------- *)
(* Addresses and quantified facts in the simulation.                         *)
(* ------------------------------------------------------------------------- *)

(*** The address of a load in the form it has after a post-increment ***)

let WORD_ADD_SPLIT_OFFSET_STMT =
  `!a:int64 n k.
        word_add a (word(n + k)) = word_add (word_add a (word n)) (word k)`;;

let WORD_ADD_SPLIT_OFFSET = assume_spec WORD_ADD_SPLIT_OFFSET_STMT;;

(*** From |- !j. P j ==> Q j, give |- !j. P j /\ ~(j = t) ==> Q j, which   ***)
(*** the simulation keeps over a store to element t                        ***)

let RESTRICT_RULE t th =
  let j,bod = dest_forall(concl th) in
  let p,q = dest_imp bod in
  let p' = mk_conj(p,mk_neg(mk_eq(j,t))) in
  GEN j (DISCH p' (MP (SPEC j th) (CONJUNCT1(ASSUME p'))));;

(*** The 256-bit loads and stores of the state and the message, which are
 *** known as 64-bit lanes: the facts for the 32 bytes at each address in
 *** the list as joins of the facts for their lanes in state s, before the
 *** simulation, and the facts for the lanes of the 32 bytes stored at each
 *** address in state s, after it
 ***)

let READ_MEMORY_MERGE256_TAC s addrs =
  MAP_EVERY (fun a ->
    MP_TAC(READ_MEMORY_MERGE_CONV 2
      (vsubst [a,`a:int64`; s,`s:x86state`]
              `read (memory :> bytes256 a) s`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC) addrs;;

let READ_MEMORY_SPLIT256_TAC s addrs =
  MAP_EVERY (fun a ->
    let pat = vsubst [a,`a:int64`; s,`s:x86state`]
                `read (memory :> bytes256 a) s = x` in
    FIRST_X_ASSUM(fun th ->
      if can (term_match (s::frees a) pat) (concl th)
      then MP_TAC(CONV_RULE(READ_MEMORY_SPLIT_CONV 2) th) THEN
           CONV_TAC(LAND_CONV(DEPTH_CONV(REWR_CONV WORD_SUBWORD_XOR) THENC
                              TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
           STRIP_TAC
      else NO_TAC)) addrs;;

(*** For each memory fact at an address word_add (word_add a (word k)) d,
 *** also the same fact at word_add a (word(k + d)): the simulation takes
 *** the address of a load from a register with value word_add a (word k)
 *** in that form
 ***)

let READ_MEMORY_NORMALIZE_TAC a =
  W(fun (asl,w) ->
    let nested t =
      match t with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
          Comb(Comb(Const(":>",_),Const("memory",_)),Comb(_,ad))),_)),_) ->
          (try let x,_ = dest_binary "word_add" ad in
               let y,_ = dest_binary "word_add" x in y = a
           with Failure _ -> false)
      | _ -> false in
    let ths = filter (nested o concl) (map snd asl) in
    MAP_EVERY (ASSUME_TAC o REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD])
      ths);;

(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of sha3_keccak_f1600_avx512 with the  *)
(* frame of its correctness theorem, as needed to use it as a callee (its    *)
(* safety theorems have the frame \s s'. true): the subroutine from the      *)
(* core, and in the image.                                                   *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let SHA3_KECCAK_F1600_AVX512_NOIBT_SUBROUTINE_SAFE_FRAMED_STMT =
  `exists f_events.
    forall e a rc pc stackpointer returnaddress.
        nonoverlapping (a,200) (word pc,0xd0d) /\
        nonoverlapping (a,200) (rc,192) /\
        nonoverlapping (a,200) (stackpointer,8)
        ==> ensures x86
            (\s. bytes_loaded s (word pc) sha3_keccak_f1600_avx512_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [a; rc] s /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [a,200; rc,192; stackpointer,8]
                      [a,200; stackpointer,8]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,200)])`;;

let SHA3_KECCAK_F1600_AVX512_NOIBT_SUBROUTINE_SAFE_FRAMED = assume_spec SHA3_KECCAK_F1600_AVX512_NOIBT_SUBROUTINE_SAFE_FRAMED_STMT;;

let SHA3_KECCAK_F1600_AVX512_SUBROUTINE_SAFE_FRAMED =
  ADD_IBT_RULE SHA3_KECCAK_F1600_AVX512_NOIBT_SUBROUTINE_SAFE_FRAMED;;

let SHA3_KECCAK_F1600_AVX512_IMAGE_SAFE_STMT =
  `exists f_events.
    forall e a rc pc stackpointer returnaddress.
       nonoverlapping (a,200) (word pc,mlkem_native2_avx512_image_size) /\
       nonoverlapping (a,200) (rc,192) /\
       nonoverlapping (a,200) (stackpointer,8)
       ==> ensures x86
            (\s. bytes_loaded s (word pc) mlkem_native2_avx512_image_mc /\
                 read RIP s = word(pc + sha3_keccak_f1600_avx512) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [a; rc] s /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events rc a pc stackpointer returnaddress /\
                      memaccess_inbounds e2
                      [a,200; rc,192; stackpointer,8]
                      [a,200; stackpointer,8]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(a,200)])`;;

let SHA3_KECCAK_F1600_AVX512_IMAGE_SAFE = assume_spec SHA3_KECCAK_F1600_AVX512_IMAGE_SAFE_STMT;;
