(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of a polynomial from a seed by rejection. In the gcc 12  *)
(* -O2 monolithic build, which compiles all of mlkem-native as one           *)
(* translation unit, mlkem_poly_rej_uniform has no code of its own: it is    *)
(* inlined into mlkem768_gen_matrix, for the last of the nine entries of the *)
(* matrix (the others are sampled four at a time by                          *)
(* mlkem_poly_rej_uniform_x4). This file has the lemmas about the samples,   *)
(* as in the gcc 12 -O2 build, which this build's proofs of                  *)
(* mlkem_poly_rej_uniform_x4 and of mlkem768_gen_matrix use, and the         *)
(* theorem for the inlined code in mlkem768_gen_matrix: from after the       *)
(* second call of mlkem_poly_rej_uniform_x4 to the end of the inlined code,  *)
(* with the statement of the theorem for mlkem_poly_rej_uniform in the       *)
(* gcc12_O2 build, using the theorems for mlk_keccak_absorb_once,            *)
(* mlk_keccakf1600_permute_c and mlk_rej_uniform_c in the image, the         *)
(* theorems proved here for the loops that copy the state to the buffer,     *)
(* and assuming the contract for memset. The code includes three squeezed    *)
(* blocks in a loop of calls of mlk_keccakf1600_permute_c, each followed by  *)
(* a loop that copies 168 bytes of the state, and then single blocks.        *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/rej_uniform_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/keccak_absorb_once_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/keccakf1600_permute_spec.ml";;
needs "arm/proofs/utils/keccak_fips202.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/libmlkem.ml";;

(* ------------------------------------------------------------------------- *)
(* The bytes of SHAKE128 in blocks of 168, the rate, in terms of the         *)
(* absorbed state, as for mlkem_shake256 and mlkem_shake256x4.               *)
(* ------------------------------------------------------------------------- *)

let REJ_SPONGE_STMT =
  `!(m:byte list) k n.
        n <= 168
        ==> num_of_bytelist(list_of_seq (\j. shake128 m (168 * k + j)) n) =
            val(keccak_squeeze (k + 1)
                 (word_xor
                   (keccak_absorb 168
                     (num_of_bytelist m +
                      2 EXP (8 * LENGTH m) *
                      num_of_bytelist(keccak_pad 168 0x1F (LENGTH m)))
                     (LENGTH m DIV 168))
                   (word((num_of_bytelist m +
                          2 EXP (8 * LENGTH m) *
                          num_of_bytelist(keccak_pad 168 0x1F (LENGTH m))) DIV
                         2 EXP (8 * 168 * LENGTH m DIV 168) MOD
                         2 EXP (8 * 168))))) MOD 2 EXP (8 * n)`;;

let REJ_SPONGE = assume_spec REJ_SPONGE_STMT;;

let REJ_XOF_BLOCKS_STMT =
  `!(f:num->byte) n.
        num_of_bytelist(list_of_seq f (168 * n)) =
        nsum {i | i < n}
         (\i. 2 EXP (8 * 168 * i) *
              num_of_bytelist(list_of_seq (\j. f(168 * i + j)) 168))`;;

let REJ_XOF_BLOCKS = assume_spec REJ_XOF_BLOCKS_STMT;;

let REJ_SHAKE128_BLOCKS_STMT =
  `!(m:byte list) b.
        num_of_bytelist(list_of_seq (shake128 m) (168 * b)) =
        nsum {i | i < b}
         (\i. 2 EXP (8 * 168 * i) *
              val(keccak_squeeze (i + 1)
                   (word_xor
                     (keccak_absorb 168
                       (num_of_bytelist m +
                        2 EXP (8 * LENGTH m) *
                        num_of_bytelist(keccak_pad 168 0x1F (LENGTH m)))
                       (LENGTH m DIV 168))
                     (word((num_of_bytelist m +
                            2 EXP (8 * LENGTH m) *
                            num_of_bytelist(keccak_pad 168 0x1F (LENGTH m)))
                           DIV 2 EXP (8 * 168 * LENGTH m DIV 168) MOD
                           2 EXP (8 * 168))))) MOD 2 EXP (8 * 168))`;;

let REJ_SHAKE128_BLOCKS = assume_spec REJ_SHAKE128_BLOCKS_STMT;;

let KECCAK_SQUEEZE_ADD_STMT =
  `!m n (S:1600 word).
        keccak_squeeze m (keccak_squeeze n S) = keccak_squeeze (m + n) S`;;

let KECCAK_SQUEEZE_ADD = assume_spec KECCAK_SQUEEZE_ADD_STMT;;

let REJ_NSUM_1_STMT =
  `!f. nsum {j | j < 1} f = f 0`;;

let REJ_NSUM_1 = assume_spec REJ_NSUM_1_STMT;;

(* ------------------------------------------------------------------------- *)
(* The 12-bit fields of the first 504 + 168 * j bytes, those of three blocks *)
(* and j more, and the samples from them as in the specification of          *)
(* mlk_rej_uniform_c, with REJ_SAMPLE as there.                              *)
(* ------------------------------------------------------------------------- *)

let REJ_WORDLIST_OF_NUM_ADD = prove
 (`!m n x. wordlist_of_num (m + n) x:(N word)list =
           APPEND (wordlist_of_num m x)
                  (wordlist_of_num n (x DIV 2 EXP (dimindex(:N) * m)))`,
  INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; wordlist_of_num; APPEND; MULT_CLAUSES; EXP;
              DIV_1] THEN
  ASM_REWRITE_TAC[CONS_11; DIV_DIV; GSYM EXP_ADD] THEN
  REWRITE_TAC[ARITH_RULE `d + d * m = d * SUC m`]);;

let REJ_WORDLIST_APPEND_STMT =
  `!(f:num->byte) m n.
        8 * m = 12 * n
        ==> wordlist_of_num (n + 112)
             (num_of_bytelist(list_of_seq f (m + 168))):(12 word)list =
            APPEND (wordlist_of_num n (num_of_bytelist(list_of_seq f m)))
                   (wordlist_of_num 112
                     (num_of_bytelist(list_of_seq (\i. f(m + i)) 168)))`;;

let REJ_WORDLIST_APPEND = assume_spec REJ_WORDLIST_APPEND_STMT;;

let REJ_FIELDS_SUC_STMT =
  `!(f:num->byte) j.
        wordlist_of_num (336 + 112 * (j + 1))
         (num_of_bytelist(list_of_seq f (504 + 168 * (j + 1)))):(12 word)list =
        APPEND
         (wordlist_of_num (336 + 112 * j)
           (num_of_bytelist(list_of_seq f (504 + 168 * j))))
         (wordlist_of_num 112
           (num_of_bytelist(list_of_seq (\i. f((504 + 168 * j) + i)) 168)))`;;

let REJ_FIELDS_SUC = assume_spec REJ_FIELDS_SUC_STMT;;

let REJ_FIELDS_PREFIX_STMT =
  `!(f:num->byte) j k.
        j <= k
        ==> ?t. wordlist_of_num (336 + 112 * k)
                 (num_of_bytelist(list_of_seq f (504 + 168 * k))):
                (12 word)list =
                APPEND (wordlist_of_num (336 + 112 * j)
                         (num_of_bytelist(list_of_seq f (504 + 168 * j)))) t`;;

let REJ_FIELDS_PREFIX = assume_spec REJ_FIELDS_PREFIX_STMT;;

let REJ_COUNT_MONO_STMT =
  `!(f:num->byte) j k.
        j <= k
        ==> LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
                     (num_of_bytelist(list_of_seq f (504 + 168 * j))))) <=
            LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * k)
                     (num_of_bytelist(list_of_seq f (504 + 168 * k)))))`;;

let REJ_COUNT_MONO = assume_spec REJ_COUNT_MONO_STMT;;

let REJ_SAMPLE_FINAL_STMT =
  `!(f:num->byte) j k.
        j <= k /\
        256 <= LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
                       (num_of_bytelist(list_of_seq f (504 + 168 * j)))))
        ==> SUB_LIST(0,256)
             (REJ_SAMPLE(wordlist_of_num (336 + 112 * k)
                (num_of_bytelist(list_of_seq f (504 + 168 * k))))) =
            SUB_LIST(0,256)
             (REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
                (num_of_bytelist(list_of_seq f (504 + 168 * j)))))`;;

let REJ_SAMPLE_FINAL = assume_spec REJ_SAMPLE_FINAL_STMT;;

let REJ_SAMPLE_SUC_STMT =
  `!(f:num->byte) j.
        LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
                 (num_of_bytelist(list_of_seq f (504 + 168 * j))))) <= 256
        ==> SUB_LIST(0,256)
             (REJ_SAMPLE(wordlist_of_num (336 + 112 * (j + 1))
                (num_of_bytelist(list_of_seq f (504 + 168 * (j + 1)))))) =
            APPEND
             (SUB_LIST(0,256)
               (REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
                  (num_of_bytelist(list_of_seq f (504 + 168 * j))))))
             (SUB_LIST(0,256 -
                       LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
                         (num_of_bytelist(list_of_seq f (504 + 168 * j))))))
               (REJ_SAMPLE(wordlist_of_num 112
                  (num_of_bytelist
                    (list_of_seq (\i. f((504 + 168 * j) + i)) 168)))))`;;

let REJ_SAMPLE_SUC = assume_spec REJ_SAMPLE_SUC_STMT;;

(* ------------------------------------------------------------------------- *)
(* Lists of 12-bit fields and of 16-bit samples in memory.                   *)
(* ------------------------------------------------------------------------- *)

let REJ_WORDLIST_FROM_BYTES_STMT =
  `!a m n x s:armstate.
        12 * n = 8 * m /\ read (memory :> bytes(a,m)) s = x
        ==> wordlist_from_memory(a,n) s = (wordlist_of_num n x:(12 word)list)`;;

let REJ_WORDLIST_FROM_BYTES = assume_spec REJ_WORDLIST_FROM_BYTES_STMT;;

let REJ_BYTES16_OF_WORDLIST_STMT =
  `!a n (l:int16 list) s:armstate.
        wordlist_from_memory(a,n) s = l
        ==> read (memory :> bytes(a,2 * n)) s = num_of_wordlist l`;;

let REJ_BYTES16_OF_WORDLIST = assume_spec REJ_BYTES16_OF_WORDLIST_STMT;;

let REJ_WORDLIST_OF_BYTES16_STMT =
  `!a (l:int16 list) s:armstate.
        read (memory :> bytes(a,2 * LENGTH l)) s = num_of_wordlist l
        ==> wordlist_from_memory(a,LENGTH l) s = l`;;

let REJ_WORDLIST_OF_BYTES16 = assume_spec REJ_WORDLIST_OF_BYTES16_STMT;;

let REJ_BYTES16_APPEND_N_STMT =
  `!a n (l1:int16 list) (l2:int16 list) s:armstate.
        LENGTH l1 = n /\
        read (memory :> bytes(a,2 * n)) s = num_of_wordlist l1 /\
        read (memory :> bytes(word_add a (word(2 * n)),2 * LENGTH l2)) s =
        num_of_wordlist l2
        ==> read (memory :> bytes(a,2 * (n + LENGTH l2))) s =
            num_of_wordlist(APPEND l1 l2)`;;

let REJ_BYTES16_APPEND_N = assume_spec REJ_BYTES16_APPEND_N_STMT;;

(* ------------------------------------------------------------------------- *)
(* The comparison of the number of samples with 255, as 32-bit words.        *)
(* ------------------------------------------------------------------------- *)

let REJ_HI_LEMMA_STMT =
  `!c. c < 2 EXP 32
       ==> ((&c - &255:int =
             &(val(word_sub (word_zx (word c:int64):int32) (word 255))) /\
             ~(val(word_sub (word_zx (word c:int64):int32) (word 255)) =
               0)) <=>
            255 < c)`;;

let REJ_HI_LEMMA = assume_spec REJ_HI_LEMMA_STMT;;

(* ------------------------------------------------------------------------- *)
(* The buffer for three blocks, followed by the state, is aligned to 32      *)
(* bytes within the stack frame, so its address depends on whether the stack *)
(* pointer is a multiple of 32 or just of 16.                                *)
(* ------------------------------------------------------------------------- *)

let REJ_ALIGNED_16_32_STMT =
  `(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`;;

let REJ_ALIGNED_16_32 = assume_spec REJ_ALIGNED_16_32_STMT;;

(* ------------------------------------------------------------------------- *)
(* The absorbed state of a seed of 34 bytes, and the facts from a call of    *)
(* mlk_rej_uniform_c.                                                        *)
(* ------------------------------------------------------------------------- *)

(*** The absorbed state as S0, and the minimal number k0 of blocks ***)

let REJ_ABSORBED =
 `word_xor
   (keccak_absorb 168
     (num_of_bytelist inp +
      2 EXP (8 * 34) * num_of_bytelist(keccak_pad 168 0x1F 34))
     (34 DIV 168))
   (word((num_of_bytelist inp +
          2 EXP (8 * 34) * num_of_bytelist(keccak_pad 168 0x1F 34)) DIV
         2 EXP (8 * 168 * 34 DIV 168) MOD 2 EXP (8 * 168))):1600 word`;;

let REJ_POST_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_let(concl th) then
      STRIP_ASSUME_TAC(REWRITE_RULE[GSYM REJ_SAMPLE]
        (CONV_RULE(TOP_DEPTH_CONV let_CONV) th))
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Reading words of the state and chunks of it, copying bytes.               *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES_EXTEND_STMT =
  `!d:int64 j k x s:armstate.
        read (memory :> bytes(d,j)) s = x MOD 2 EXP (8 * j) /\
        read (memory :> bytes(word_add d (word j),k)) s =
        (x DIV 2 EXP (8 * j)) MOD 2 EXP (8 * k)
        ==> read (memory :> bytes(d,j + k)) s = x MOD 2 EXP (8 * (j + k))`;;

let READ_MEMORY_BYTES_EXTEND = assume_spec READ_MEMORY_BYTES_EXTEND_STMT;;

let READ_MEMORY_BYTES128_OF_NUM_STMT =
  `!a:int64 m n k s:armstate.
        read (memory :> bytes(a,m)) s = n /\ k + 16 <= m
        ==> read (memory :> bytes128(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 2 EXP 128)`;;

let READ_MEMORY_BYTES128_OF_NUM =
  assume_spec READ_MEMORY_BYTES128_OF_NUM_STMT;;

let READ_MEMORY_BYTES_OF_BYTES128_STMT =
  `!a:int64 v s:armstate.
        read (memory :> bytes128 a) s = word v
        ==> read (memory :> bytes(a,16)) s = v MOD 2 EXP (8 * 16)`;;

let READ_MEMORY_BYTES_OF_BYTES128 =
  assume_spec READ_MEMORY_BYTES_OF_BYTES128_STMT;;

(*** n chunks of 16 bytes, each given by a 128-bit read ***)

let READ_BYTES_FROM_CHUNKS128_STMT =
  `!n a:int64 x s:armstate.
        (!k. k < n
             ==> read (memory :> bytes128(word_add a (word(16 * k)))) s =
                 word((x DIV 2 EXP (128 * k)) MOD 2 EXP 128))
        ==> read (memory :> bytes(a,16 * n)) s = x MOD 2 EXP (128 * n)`;;

let READ_BYTES_FROM_CHUNKS128 = assume_spec READ_BYTES_FROM_CHUNKS128_STMT;;

let READ_MEMORY_BYTES64_OF_NUM_STMT =
  `!a:int64 m n k s:armstate.
        read (memory :> bytes(a,m)) s = n /\ k + 8 <= m
        ==> read (memory :> bytes64(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 2 EXP 64)`;;

let READ_MEMORY_BYTES64_OF_NUM = assume_spec READ_MEMORY_BYTES64_OF_NUM_STMT;;

let READ_MEMORY_BYTES_OF_BYTES64_STMT =
  `!a:int64 v s:armstate.
        read (memory :> bytes64 a) s = word v
        ==> read (memory :> bytes(a,8)) s = v MOD 2 EXP (8 * 8)`;;

let READ_MEMORY_BYTES_OF_BYTES64 =
  assume_spec READ_MEMORY_BYTES_OF_BYTES64_STMT;;

let ZX_ZX_64_128_STMT =
  `!x:int64. word_zx(word_zx x:int128):int64 = x`;;

let ZX_ZX_64_128 = assume_spec ZX_ZX_64_128_STMT;;

let KSQ_SUC_STMT =
  `!t S:1600 word. keccak_squeeze (t + 1) S = keccak_f1600(keccak_squeeze t S)`;;

let KSQ_SUC = assume_spec KSQ_SUC_STMT;;
let NSUM_LT_STEP_STMT =
  `!(f:num->num) t. nsum {i | i < t + 1} f = nsum {i | i < t} f + f t`;;

let NSUM_LT_STEP = assume_spec NSUM_LT_STEP_STMT;;


(* ------------------------------------------------------------------------- *)
(* The code of mlkem768_gen_matrix and the PLT stub for memset.              *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_GENMAT3_REJ_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mono_mc
   [layout_range "mlkem768_gen_matrix"; layout_range "plt_memset"];;


(* ------------------------------------------------------------------------- *)
(* Copying 168 bytes of the state to the buffer, 8 bytes at a time.          *)
(* ------------------------------------------------------------------------- *)

let genmat3_copy_goal =
 `!st q (V:1600 word) pc.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    nonoverlapping (q,168) (st,200) /\
    nonoverlapping (st,200) (word pc,libmlkem_size) /\
    nonoverlapping (q,168) (word pc,libmlkem_size)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc)
                mlkem_native_libmlkem_gcc12_O2_mono_mc /\
              read PC s =
              word(pc + mlkem768_gen_matrix_after_mlk_keccakf1600_permute_c_1) /\
              read X20 s = st /\
              read X22 s = word_add q (word 168) /\
              read (memory :> wbytes st) s = V)
         (\s. read PC s = word(pc + mlkem768_gen_matrix_loop2_test) /\
              read X20 s = st /\
              read X19 s = word_add q (word 168) /\
              read X22 s = word_add q (word 336) /\
              read (memory :> wbytes st) s = V /\
              read (memory :> bytes(q,168)) s = val V MOD 2 EXP (8 * 168))
         (MAYCHANGE [PC; X0; X19; X22] ,, MAYCHANGE [Q0] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(q,168)])`;;

let GENMAT3_COPY168_STMT =
  genmat3_copy_goal;;

let GENMAT3_COPY168 = assume_spec GENMAT3_COPY168_STMT;;


(* ------------------------------------------------------------------------- *)
(* Three blocks of output: the loop of mlk_keccakf1600_permute_c and the copy. *)
(* ------------------------------------------------------------------------- *)

let LOCAL_GM3_PERMUTE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_GENMAT3_REJ_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_F1600);;

let LOCAL_GM3_COPY168_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_GENMAT3_REJ_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,
    GENMAT3_COPY168);;

let genmat3_sq3_goal =
 `!st buf (S:1600 word) bp pc.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    aligned 16 bp /\
    PAIRWISE nonoverlapping
     [(buf,504); (st,200); (word_add bp (word 64),192)] /\
    ALL (nonoverlapping (word pc,libmlkem_size))
     [(buf,504); (st,200); (word_add bp (word 64),192)]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc)
                mlkem_native_libmlkem_gcc12_O2_mono_mc /\
              read PC s = word(pc + mlkem768_gen_matrix_loop2) /\
              read SP s = word_add bp (word 256) /\
              read X20 s = st /\ read X21 s = buf /\
              read X22 s = word_add buf (word 168) /\ read X23 s = word 3 /\
              read (memory :> wbytes st) s = S)
         (\s. read PC s = word(pc + mlkem768_gen_matrix_loop2_exit) /\
              read SP s = word_add bp (word 256) /\
              read X20 s = st /\ read X21 s = buf /\ read X23 s = word 0 /\
              read (memory :> wbytes st) s = keccak_squeeze 3 S /\
              read (memory :> bytes(buf,504)) s =
              nsum {i | i < 3}
               (\i. 2 EXP (8 * 168 * i) *
                    val(keccak_squeeze (i + 1) S) MOD 2 EXP (8 * 168)))
         (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                     X12; X13; X14; X15; X16; X17; X18; X19; X22; X23;
                     X30] ,,
          MAYCHANGE [Q0] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(buf,504); memory :> bytes(st,200);
                     memory :> bytes(word_add bp (word 64),192)])`;;

let GENMAT3_SQ3_STMT =
  genmat3_sq3_goal;;

let GENMAT3_SQ3 = assume_spec GENMAT3_SQ3_STMT;;


(* ------------------------------------------------------------------------- *)
(* Copying 168 bytes with five pairs of Q registers and an X register.       *)
(* ------------------------------------------------------------------------- *)

let genmat3_copyu_goal =
 `!st buf (V:1600 word) c19 y pc.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    nonoverlapping (buf,168) (st,200) /\
    nonoverlapping (st,200) (word pc,libmlkem_size) /\
    nonoverlapping (buf,168) (word pc,libmlkem_size)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc)
                mlkem_native_libmlkem_gcc12_O2_mono_mc /\
              read PC s =
              word(pc + mlkem768_gen_matrix_after_mlk_keccakf1600_permute_c_2) /\
              read X19 s = c19 /\ read X20 s = st /\ read X21 s = buf /\
              read X25 s = y /\
              read (memory :> wbytes st) s = V)
         (\s. read PC s =
              word(pc + mlkem768_gen_matrix_in_shake128_squeezeblocks_2_end) /\
              read X19 s = c19 /\ read X20 s = st /\ read X21 s = buf /\
              read X25 s = y /\
              read X0 s = y /\ read X2 s = buf /\ read X3 s = word 168 /\
              read X1 s = word_zx(word_zx c19:int32) /\
              read (memory :> wbytes st) s = V /\
              read (memory :> bytes(buf,168)) s = val V MOD 2 EXP (8 * 168))
         (MAYCHANGE [PC; X0; X1; X2; X3; X4] ,,
          MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q17] ,,
          MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(buf,168)])`;;

let GENMAT3_COPY168U_STMT =
  genmat3_copyu_goal;;

let GENMAT3_COPY168U = assume_spec GENMAT3_COPY168U_STMT;;


(* ------------------------------------------------------------------------- *)
(* The inlined mlkem_poly_rej_uniform in mlkem768_gen_matrix.                *)
(* ------------------------------------------------------------------------- *)

(*** The fields and samples, and the blocks and samples from them ***)

let rej_fields j =
  vsubst [j,`j:num`]
   `wordlist_of_num (336 + 112 * j)
     (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * j))):
    (12 word)list`;;

let rej_count j = mk_comb(`LENGTH:(16 word)list->num`,
                          mk_comb(`REJ_SAMPLE`,rej_fields j));;

let rej_block i =
  vsubst [i,`i:num`]
   `wordlist_of_num 112
     (num_of_bytelist
       (list_of_seq (\j. shake128 inp ((504 + 168 * i) + j)) 168)):
    (12 word)list`;;

let rej_l1 i =
  mk_comb(`SUB_LIST(0,256):(16 word)list->(16 word)list`,
          mk_comb(`REJ_SAMPLE`,rej_fields i));;

let rej_l2 i =
  mk_comb(`SUB_LIST(0,256 - ci):(16 word)list->(16 word)list`,
          mk_comb(`REJ_SAMPLE`,rej_block i));;

(*** The facts at the intermediate points, with the saved registers ***)
let REJ_ABSORBED_TAC =
  let len = ASSUME `LENGTH(inp:byte list) = 34` in
  ABBREV_TAC(mk_eq(`S0:1600 word`,REJ_ABSORBED)) THEN
  ASSUME_TAC(REWRITE_RULE[len; ASSUME(mk_eq(REJ_ABSORBED,`S0:1600 word`))]
              (SPEC `inp:byte list` REJ_SPONGE)) THEN
  ASSUME_TAC(REWRITE_RULE[len; ASSUME(mk_eq(REJ_ABSORBED,`S0:1600 word`))]
              (SPEC `inp:byte list` REJ_SHAKE128_BLOCKS));;

let REJ_MINIMAL_TAC =
  let p = mk_abs(`n:num`,
           mk_comb(mk_comb(`(<=):num->num->bool`,`256`),
             mk_comb(`LENGTH:(16 word)list->num`,
               mk_comb(`REJ_SAMPLE`,rej_fields `n:num`)))) in
  MP_TAC(BETA_RULE(fst(EQ_IMP_RULE(ISPEC p MINIMAL)))) THEN
  ANTS_TAC THENL [EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC(mk_eq(`k0:num`,mk_comb(`(minimal):(num->bool)->num`,p))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `k0 <= k` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(*** Calls of mlk_rej_uniform_c and their results ***)

let REJ_INPUT0_TAC s =
  SUBGOAL_THEN
   (subst [s,`s:armstate`]
     `wordlist_from_memory(buf,336) s =
      (wordlist_of_num 336
        (num_of_bytelist(list_of_seq (shake128 inp) 504)):(12 word)list)`)
  ASSUME_TAC THENL
   [MATCH_MP_TAC REJ_WORDLIST_FROM_BYTES THEN EXISTS_TAC `504` THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `504 = 168 * 3`] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `168 * 3 = 504`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASSUME_TAC(INST_TYPE [`:12`,`:N`] (ISPECL
   [`336`; `num_of_bytelist(list_of_seq (shake128 inp) 504)`]
   LENGTH_WORDLIST_OF_NUM));;

let REJ_BLOCK_TAC s =
  SUBGOAL_THEN
   (mk_eq(list_mk_comb(`wordlist_from_memory:int64#num->armstate->
                         (12 word)list`,
                       [mk_pair(`buf:int64`,`112`); s]),
          rej_block `i:num`))
  ASSUME_TAC THENL
   [MATCH_MP_TAC REJ_WORDLIST_FROM_BYTES THEN EXISTS_TAC `168` THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th ->
      if can (term_match [] `!k n. n <= 168 ==> a = b`) (concl th) then
        MP_TAC(SPECL [`3 + i`; `168`] th) else NO_TAC) THEN
    REWRITE_TAC[LE_REFL; ARITH_RULE `168 * (3 + i) = 504 + 168 * i`;
                ARITH_RULE `(3 + i) + 1 = 3 + i + 1`] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASSUME_TAC(INST_TYPE [`:12`,`:N`]
   (ISPECL [`112`; rand(rej_block `i:num`)] LENGTH_WORDLIST_OF_NUM));;

let REJ_COMBINE_TAC sname =
  REJ_POST_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP REJ_BYTES16_OF_WORDLIST o check
   (can (term_match [] `wordlist_from_memory(a,n) s = l:int16 list`) o
    concl)) THEN
  SUBGOAL_THEN
   (mk_eq(mk_comb(`LENGTH:(16 word)list->num`,rej_l1 `i:num`),`ci:num`))
  ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST; SUB_0] THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`entry:int64`; `ci:num`; rej_l1 `i:num`; rej_l2 `i:num`;
                 mk_var(sname,`:armstate`)] REJ_BYTES16_APPEND_N) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (let th = MP (REWRITE_RULE[ASSUME(mk_eq(rej_count `i:num`,`ci:num`))]
                (ISPECL [`shake128 inp`; `i:num`] REJ_SAMPLE_SUC))
               (ASSUME `ci <= 256`) in
   RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN
   MP_TAC(AP_TERM `LENGTH:(16 word)list->num` th)) THEN
  REWRITE_TAC[LENGTH_APPEND;
    ASSUME(mk_eq(mk_comb(`LENGTH:(16 word)list->num`,rej_l1 `i:num`),
                 `ci:num`))] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [LENGTH_SUB_LIST] THEN
  REWRITE_TAC[SUB_0] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[SYM th]));;

(*** The counter and the tests of whether there are 256 samples ***)

let REJ_C0 =
  `LENGTH(REJ_SAMPLE(wordlist_of_num 336
     (num_of_bytelist(list_of_seq (shake128 inp) 504)):(12 word)list))`
and REJ_CN = mk_comb(`MIN 256`,rej_count `i + 1`);;

let REJ_ARGS_32_TAC c =
  MP_TAC(SPEC c WORD_ZX_32_SMALL) THEN
  ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN
    (ARITH_TAC ORELSE
     FIRST_ASSUM(fun th ->
      if is_binary "<" (concl th) && lhand(concl th) = c
      then MP_TAC th THEN ARITH_TAC else NO_TAC));
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))];;

let REJ_HI_TAC c =
  SUBGOAL_THEN (mk_binop `(<):num->num->bool` c `2 EXP 32`) (fun bth ->
    let th = MP (SPEC c REJ_HI_LEMMA) bth in
    RULE_ASSUM_TAC(fun th' ->
      if is_eq(concl th') && is_cond(rand(concl th'))
      then REWRITE_RULE[th] th' else th')) THENL
   [CONV_TAC NUM_REDUCE_CONV THEN
    (ARITH_TAC ORELSE
     FIRST_ASSUM(fun th ->
      if is_binary "<" (concl th) && lhand(concl th) = c
      then MP_TAC th THEN ARITH_TAC else NO_TAC));
    ALL_TAC];;

let REJ_MIN_TAC =
  FIRST_ASSUM(fun th ->
    if is_binary "<" (concl th) && rand(concl th) = `256` &&
       can (find_term (fun t -> try fst(dest_const t) = "REJ_SAMPLE"
                               with _ -> false)) (lhand(concl th))
    then REWRITE_TAC[MATCH_MP (ARITH_RULE `x < 256 ==> MIN 256 x = x`) th]
    else NO_TAC);;

let REJ_LS_TAC =
  SUBGOAL_THEN (mk_eq(mk_binop `(<):num->num->bool` `255` REJ_CN,
                      `~(i + 1 < k0)`))
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[ARITH_RULE `255 < MIN 256 x <=> 256 <= x`] THEN EQ_TAC THENL
     [DISCH_TAC THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i + 1` o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC THEN SUBGOAL_THEN `i + 1 = k0` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`i < k0`; `~(i + 1 < k0)`] THEN ARITH_TAC;
        ASM_REWRITE_TAC[]]];
    ALL_TAC];;

(*** The parts of the proof ***)

(*** The facts that hold throughout, for the state at st = buf + 768 ***)

let GM3_FRAME =
 `read SP s = word_add bp (word 256) /\
  read X20 s = word_add buf (word 768) /\
  read X21 s = buf /\
  read X24 s = word_add buf (word 512) /\
  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
  read (memory :> bytes(ea,el)) s = ev`;;

let GM3_AT t =
  let vs,bod = strip_abs t in list_mk_abs(vs,mk_conj(bod,GM3_FRAME));;

let GM3_M1 = GM3_AT
 `\s. read X22 s = word_add buf (word 168) /\
      read X23 s = word 3 /\
      read X25 s = word_sub entry (word 4096) /\
      read (memory :> wbytes (word_add buf (word 768))) s = (S0:1600 word)`;;

let GM3_M2 = GM3_AT
 `\s. read X23 s = word 0 /\
      read X25 s = word_sub entry (word 4096) /\
      read (memory :> bytes(word_add buf (word 768),200)) s =
      val(keccak_squeeze 3 (S0:1600 word)) /\
      read (memory :> bytes(buf,504)) s =
      nsum {i | i < 3}
       (\i. 2 EXP (8 * 168 * i) *
            val(keccak_squeeze (i + 1) (S0:1600 word)) MOD 2 EXP (8 * 168))`;;

let GM3_A1 = GM3_AT
 `\s. read X25 s = entry /\
      read X0 s =
      word(MIN 256 (LENGTH(REJ_SAMPLE(wordlist_of_num 336
        (num_of_bytelist(list_of_seq (shake128 inp) 504)))))) /\
      read (memory :> bytes(entry,2 * MIN 256 (LENGTH(REJ_SAMPLE
        (wordlist_of_num 336
          (num_of_bytelist(list_of_seq (shake128 inp) 504))))))) s =
      num_of_wordlist(SUB_LIST(0,256) (REJ_SAMPLE(wordlist_of_num 336
        (num_of_bytelist(list_of_seq (shake128 inp) 504))))) /\
      read (memory :> bytes(word_add buf (word 768),200)) s =
      val(keccak_squeeze 3 (S0:1600 word))`;;

let GM3_INV = GM3_AT
 `\i s. read X25 s = entry /\
        read X19 s =
        word(MIN 256 (LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * i)
          (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * i))))))) /\
        read (memory :> bytes(entry,2 * MIN 256 (LENGTH(REJ_SAMPLE
          (wordlist_of_num (336 + 112 * i)
            (num_of_bytelist(list_of_seq (shake128 inp)
                               (504 + 168 * i)))))))) s =
        num_of_wordlist(SUB_LIST(0,256) (REJ_SAMPLE(wordlist_of_num
          (336 + 112 * i)
          (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * i)))))) /\
        read (memory :> bytes(word_add buf (word 768),200)) s =
        val(keccak_squeeze (3 + i) (S0:1600 word))`;;

let GM3_A2 = GM3_AT
 `\s. read (memory :> bytes(entry,512)) s =
      num_of_wordlist(SUB_LIST(0,256) (REJ_SAMPLE(wordlist_of_num
        (336 + 112 * k)
        (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * k))))))`;;

let GM3_BYTES16_STMT =
  `!a s:armstate.
        read (memory :> bytes(a,2)) s =
        val(read (memory :> bytes16 a) s)`;;

let GM3_BYTES16 = assume_spec GM3_BYTES16_STMT;;

let GM3_INPUT_STMT =
  `!a:int64 (rho:byte list) s:armstate.
        LENGTH rho = 32 /\
        read (memory :> bytes(a,32)) s = num_of_bytelist rho /\
        read (memory :> bytes16(word_add a (word 32))) s = word 514
        ==> LENGTH(APPEND rho [word 2:byte; word 2]) = 34 /\
            read (memory :> bytes(a,34)) s =
            num_of_bytelist(APPEND rho [word 2:byte; word 2])`;;

let GM3_INPUT = assume_spec GM3_INPUT_STMT;;

let LOCAL_GM3_SQ3_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_GENMAT3_REJ_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,
    GENMAT3_SQ3);;

let LOCAL_GM3_COPYU_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_GENMAT3_REJ_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,
    GENMAT3_COPY168U);;

let LOCAL_GM3_ABSORB_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_GENMAT3_REJ_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_GM3_REJ_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_GENMAT3_REJ_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,
    MLKEM_NATIVE_REJ_UNIFORM_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT);;

let genmat3_rej_goal =
 `!entry buf (rho:byte list) (inp:byte list) k mf ea el ev pc bp.
    memset_contract mf ea el ev /\
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    aligned 16 bp /\ aligned 32 buf /\
    LENGTH rho = 32 /\ APPEND rho [word 2; word 2] = inp /\
    256 <= LENGTH(FILTER (\x. val x < 3329)
                   (MAP (word_zx:12 word->16 word)
                     (wordlist_of_num (336 + 112 * k)
                       (num_of_bytelist
                         (list_of_seq (shake128 inp) (504 + 168 * k)))))) /\
    PAIRWISE nonoverlapping
     [(entry,512); (buf,504); (word_add buf (word 512),256);
      (word_add buf (word 768),224); (bp,256)] /\
    ALLPAIRS nonoverlapping
     [(entry,512); (buf,504); (word_add buf (word 512),256);
      (word_add buf (word 768),224); (bp,256)]
     [(word pc,libmlkem_size); (word(pc + got_memset),8); (ea,el)]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc)
                mlkem_native_libmlkem_gcc12_O2_mono_mc /\
              read PC s =
              word(pc + mlkem768_gen_matrix_after_mlkem_poly_rej_uniform_x4_2) /\
              read SP s = word_add bp (word 256) /\
              read X20 s = word_add buf (word 768) /\
              read X21 s = buf /\
              read X22 s = word_add buf (word 168) /\
              read X23 s = word 3 /\
              read X24 s = word_add buf (word 512) /\
              read X25 s = word_sub entry (word 4096) /\
              read (memory :> bytes64(word(pc + got_memset))) s = mf /\
              read (memory :> bytes(ea,el)) s = ev /\
              read (memory :> bytes(word_add buf (word 512),32)) s =
              num_of_bytelist rho)
         (\s. read PC s =
              word(pc + mlkem768_gen_matrix_in_poly_rej_uniform_end) /\
              wordlist_from_memory(entry,256) s =
              SUB_LIST(0,256)
               (FILTER (\x. val x < 3329)
                 (MAP (word_zx:12 word->16 word)
                   (wordlist_of_num (336 + 112 * k)
                     (num_of_bytelist
                       (list_of_seq (shake128 inp) (504 + 168 * k)))))))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [X18; X19; X22; X23; X25; X30] ,,
          MAYCHANGE
           [memory :> bytes(entry,512);
            memory :> bytes(buf,504);
            memory :> bytes(word_add buf (word 512),256);
            memory :> bytes(word_add buf (word 768),224);
            memory :> bytes(bp,256)])`;;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_MONO_IN_MLKEM768_GEN_MATRIX_STMT =
  genmat3_rej_goal;;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_MONO_IN_MLKEM768_GEN_MATRIX =
  assume_spec MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_MONO_IN_MLKEM768_GEN_MATRIX_STMT;;


(* ------------------------------------------------------------------------- *)
(* The same with the events, for the proof of constant time and memory safety. *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;

let GM3SQ_ALLOWED =
  [`pc:num`; `st:int64`; `buf:int64`; `bp:int64`; `t:num`;
   `f_ev_loop:int64->int64->int64->num->num->(uarch_event)list`];;

let GM3SQ_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mono_mc,
       MLKEM_NATIVE_GENMAT3_REJ_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref GM3SQ_ALLOWED); LABEL_TAC name safety_th]);;

let GM3SQ_SAFE_CALL_SIDE_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mono_mc,
       MLKEM_NATIVE_GENMAT3_REJ_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,safety_th)
      ilist n THENL
     [CONJ_TAC THENL [CONV_TAC WORD_RULE; EXISTS_E2_TAC (ref GM3SQ_ALLOWED)];
      LABEL_TAC name safety_th]);;

(*** Discharge the events of a loop body with callees, when the events of the
     iteration are a left-nested APPEND in front of ENUMERATEL ***)

let GM3_LOOP_DISCHARGE_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W(fun (asl,w) ->
    (if is_conj w then
      (CONJ_TAC THENL
        [REWRITE_TAC[ENUMERATEL_ADD1; APPEND_NIL; CONJUNCT1 APPEND] THEN
         REWRITE_TAC[APPEND_ASSOC] THEN
         CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
         REPEAT(AP_THM_TAC THEN AP_TERM_TAC) THEN
         CONV_TAC(REPEATC (RAND_CONV BETA_CONV)) THEN UNIFY_F_EVENTS_TAC;
         ALL_TAC])
     else ALL_TAC) THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

let genmat3_copy_full_goal =
 `exists f_events.
   forall e st q (V:1600 word) pc.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    nonoverlapping (q,168) (st,200) /\
    nonoverlapping (st,200) (word pc,libmlkem_size) /\
    nonoverlapping (q,168) (word pc,libmlkem_size)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc)
                mlkem_native_libmlkem_gcc12_O2_mono_mc /\
              read PC s =
              word(pc + mlkem768_gen_matrix_after_mlk_keccakf1600_permute_c_1) /\
              read X20 s = st /\
              read X22 s = word_add q (word 168) /\
              read (memory :> wbytes st) s = V /\
              read events s = e)
         (\s. read PC s = word(pc + mlkem768_gen_matrix_loop2_test) /\
              read X20 s = st /\
              read X19 s = word_add q (word 168) /\
              read X22 s = word_add q (word 336) /\
              read (memory :> wbytes st) s = V /\
              read (memory :> bytes(q,168)) s = val V MOD 2 EXP (8 * 168) /\
              (exists e2. read events s = APPEND e2 e /\
                          e2 = f_events st q pc /\
                          memaccess_inbounds e2 [st,200; q,168] [q,168]))
         (MAYCHANGE [PC; X0; X19; X22] ,, MAYCHANGE [Q0] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(q,168)])`;;

let GENMAT3_COPY168_FULL_STMT =
  genmat3_copy_full_goal;;

let GENMAT3_COPY168_FULL = assume_spec GENMAT3_COPY168_FULL_STMT;;

let genmat3_copyu_full_goal =
 `exists f_events.
   forall e st buf (V:1600 word) c19 y pc.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    nonoverlapping (buf,168) (st,200) /\
    nonoverlapping (st,200) (word pc,libmlkem_size) /\
    nonoverlapping (buf,168) (word pc,libmlkem_size)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc)
                mlkem_native_libmlkem_gcc12_O2_mono_mc /\
              read PC s =
              word(pc + mlkem768_gen_matrix_after_mlk_keccakf1600_permute_c_2) /\
              read X19 s = c19 /\ read X20 s = st /\ read X21 s = buf /\
              read X25 s = y /\
              read (memory :> wbytes st) s = V /\
              read events s = e)
         (\s. read PC s =
              word(pc + mlkem768_gen_matrix_in_shake128_squeezeblocks_2_end) /\
              read X19 s = c19 /\ read X20 s = st /\ read X21 s = buf /\
              read X25 s = y /\
              read X0 s = y /\ read X2 s = buf /\ read X3 s = word 168 /\
              read X1 s = word_zx(word_zx c19:int32) /\
              read (memory :> wbytes st) s = V /\
              read (memory :> bytes(buf,168)) s = val V MOD 2 EXP (8 * 168) /\
              (exists e2. read events s = APPEND e2 e /\
                          e2 = f_events st buf pc /\
                          memaccess_inbounds e2 [st,200; buf,168] [buf,168]))
         (MAYCHANGE [PC; X0; X1; X2; X3; X4] ,,
          MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q17] ,,
          MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(buf,168)])`;;

let GENMAT3_COPY168U_FULL_STMT =
  genmat3_copyu_full_goal;;

let GENMAT3_COPY168U_FULL = assume_spec GENMAT3_COPY168U_FULL_STMT;;

let genmat3_sq3_full_goal =
 `exists f_events.
   forall e st buf (S:1600 word) bp pc.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    aligned 16 bp /\
    PAIRWISE nonoverlapping
     [(buf,504); (st,200); (word_add bp (word 64),192)] /\
    ALL (nonoverlapping (word pc,libmlkem_size))
     [(buf,504); (st,200); (word_add bp (word 64),192)]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc)
                mlkem_native_libmlkem_gcc12_O2_mono_mc /\
              read PC s = word(pc + mlkem768_gen_matrix_loop2) /\
              read SP s = word_add bp (word 256) /\
              read X20 s = st /\ read X21 s = buf /\
              read X22 s = word_add buf (word 168) /\ read X23 s = word 3 /\
              read (memory :> wbytes st) s = S /\
              read events s = e)
         (\s. read PC s = word(pc + mlkem768_gen_matrix_loop2_exit) /\
              read SP s = word_add bp (word 256) /\
              read X20 s = st /\ read X21 s = buf /\ read X23 s = word 0 /\
              read (memory :> wbytes st) s = keccak_squeeze 3 S /\
              read (memory :> bytes(buf,504)) s =
              nsum {i | i < 3}
               (\i. 2 EXP (8 * 168 * i) *
                    val(keccak_squeeze (i + 1) S) MOD 2 EXP (8 * 168)) /\
              (exists e2. read events s = APPEND e2 e /\
                          e2 = f_events st buf bp pc /\
                          memaccess_inbounds e2
                           [st,200; buf,504; word_add bp (word 64),192;
                            word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                           [buf,504; st,200; word_add bp (word 64),192]))
         (MAYCHANGE [PC; X0; X1; X2; X3; X4; X5; X6; X7; X8; X9; X10; X11;
                     X12; X13; X14; X15; X16; X17; X18; X19; X22; X23;
                     X30] ,,
          MAYCHANGE [Q0] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(buf,504); memory :> bytes(st,200);
                     memory :> bytes(word_add bp (word 64),192)])`;;

let GENMAT3_SQ3_FULL_STMT =
  genmat3_sq3_full_goal;;

let GENMAT3_SQ3_FULL = assume_spec GENMAT3_SQ3_FULL_STMT;;

(*** The events of the inlined code: the template and the helper tactics ***)

let GM3F_ARGS =
  [`entry:int64`; `buf:int64`; `inp:byte list`; `mf:int64`; `pc:num`;
   `bp:int64`];;

let GM3F_K0 =
  mk_comb(`(minimal):(num->bool)->num`,
          mk_abs(`n:num`,
           mk_comb(mk_comb(`(<=):num->num->bool`,`256`),
            mk_comb(`LENGTH:(16 word)list->num`,
             mk_comb(`REJ_SAMPLE`,rej_fields `n:num`)))));;

let GM3F_TEMPLATE =
  let args = GM3F_ARGS in
  let fty = itlist (fun a t -> mk_fun_ty (type_of a) t) args
                   `:(uarch_event)list` in
  let fv n = mk_var(n,fty) in
  let app n = list_mk_comb(fv n,args) in
  let k0 = GM3F_K0 in
  let fl = list_mk_comb(mk_var("f_ev_loop",
             itlist (fun a t -> mk_fun_ty (type_of a) t) args
                    (mk_fun_ty `:num` `:(uarch_event)list`)),args) in
  let loop = mk_abs(`i:num`,mk_comb(fl,`i:num`)) in
  let ap = `APPEND:(uarch_event)list->(uarch_event)list->(uarch_event)list` in
  let enum = list_mk_comb(`ENUMERATEL:num->(num->(uarch_event)list)->
                                     (uarch_event)list`,[k0;loop]) in
  let mid = mk_cond(mk_eq(k0,`0`),app "f_ev_skip",
              list_mk_comb(ap,[app "f_ev_exit";
                list_mk_comb(ap,[enum; app "f_ev_enter"])])) in
  let body = list_mk_comb(ap,[app "f_ev_rel";
               list_mk_comb(ap,[mid;
                list_mk_comb(ap,[app "f_ev_a1";
                 list_mk_comb(ap,[app "f_ev_sq3"; app "f_ev_m1"])])])]) in
  list_mk_abs(args,body);;

let GM3F_ALLOWED =
  [`entry:int64`; `buf:int64`; `inp:byte list`; `rho:byte list`;
   `mf:int64`; `pc:num`; `bp:int64`; `i:num`; `ci:num`; `k0:num`;
   `f_ev_loop:int64->int64->byte list->int64->num->int64->num->
              (uarch_event)list`];;

let GM3F_CALL_TAC name side ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mono_mc,
       MLKEM_NATIVE_GENMAT3_REJ_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mono_mc,safety_th)
      ilist n THENL
     [(match side with
         None -> EXISTS_E2_TAC (ref GM3F_ALLOWED)
       | Some tac -> CONJ_TAC THENL [tac; EXISTS_E2_TAC (ref GM3F_ALLOWED)]);
      LABEL_TAC name safety_th]);;

let genmat3_rej_full_goal =
 `!mf ea el ev.
   memset_full_contract mf ea el ev
   ==> exists f_events.
    forall e entry buf (rho:byte list) (inp:byte list) k pc bp.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    aligned 16 bp /\ aligned 32 buf /\
    LENGTH rho = 32 /\ APPEND rho [word 2; word 2] = inp /\
    256 <= LENGTH(FILTER (\x. val x < 3329)
                   (MAP (word_zx:12 word->16 word)
                     (wordlist_of_num (336 + 112 * k)
                       (num_of_bytelist
                         (list_of_seq (shake128 inp) (504 + 168 * k)))))) /\
    PAIRWISE nonoverlapping
     [(entry,512); (buf,504); (word_add buf (word 512),256);
      (word_add buf (word 768),224); (bp,256)] /\
    ALLPAIRS nonoverlapping
     [(entry,512); (buf,504); (word_add buf (word 512),256);
      (word_add buf (word 768),224); (bp,256)]
     [(word pc,libmlkem_size); (word(pc + got_memset),8); (ea,el)]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc)
                mlkem_native_libmlkem_gcc12_O2_mono_mc /\
              read PC s =
              word(pc + mlkem768_gen_matrix_after_mlkem_poly_rej_uniform_x4_2) /\
              read SP s = word_add bp (word 256) /\
              read X20 s = word_add buf (word 768) /\
              read X21 s = buf /\
              read X22 s = word_add buf (word 168) /\
              read X23 s = word 3 /\
              read X24 s = word_add buf (word 512) /\
              read X25 s = word_sub entry (word 4096) /\
              read (memory :> bytes64(word(pc + got_memset))) s = mf /\
              read (memory :> bytes(ea,el)) s = ev /\
              read (memory :> bytes(word_add buf (word 512),32)) s =
              num_of_bytelist rho /\
              read events s = e)
         (\s. read PC s =
              word(pc + mlkem768_gen_matrix_in_poly_rej_uniform_end) /\
              wordlist_from_memory(entry,256) s =
              SUB_LIST(0,256)
               (FILTER (\x. val x < 3329)
                 (MAP (word_zx:12 word->16 word)
                   (wordlist_of_num (336 + 112 * k)
                     (num_of_bytelist
                       (list_of_seq (shake128 inp) (504 + 168 * k)))))) /\
              (exists e2. read events s = APPEND e2 e /\
                          e2 = f_events entry buf inp mf pc bp /\
                          memaccess_inbounds e2
                           [entry,512; buf,504; word_add buf (word 512),256;
                            word_add buf (word 768),224; bp,256;
                            word(pc + rodata_mlk_KeccakF_RoundConstants),192;
                            word(pc + got_memset),8; ea,el]
                           [entry,512; buf,504; word_add buf (word 512),256;
                            word_add buf (word 768),224; bp,256]))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [X18; X19; X22; X23; X25; X30] ,,
          MAYCHANGE
           [memory :> bytes(entry,512);
            memory :> bytes(buf,504);
            memory :> bytes(word_add buf (word 512),256);
            memory :> bytes(word_add buf (word 768),224);
            memory :> bytes(bp,256)])`;;

let GM3F_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_full_contract] th) "H_MEMSET") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL
    "H_ABSORB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC GENMAT3_SQ3_FULL "H_SQ3" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_REJ_UNIFORM_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL "H_REJ" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERM" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC GENMAT3_COPY168U_FULL "H_COPYU" THEN
  CONCRETIZE_F_EVENTS_TAC GM3F_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`entry:int64`; `buf:int64`; `rho:byte list`; `inp:byte list`; `k:num`;
    `pc:num`; `bp:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; ALLPAIRS;
              PAIRWISE; NONOVERLAPPING_CLAUSES; GSYM REJ_SAMPLE] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `LENGTH(inp:byte list) = 34` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `APPEND rho [word 2:byte; word 2] = inp`)) THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  REJ_ABSORBED_TAC THEN REJ_MINIMAL_TAC;;

let GM3F_INIT_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC;;

(*** Absorbing the seed ***)

let GM3F_PART_M1_TAC =
  GM3F_INIT_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (1--8) THEN
  GM3F_CALL_TAC "H_ABSORB"
   (Some (MP_TAC(SPECL [`word_add buf (word 512):int64`; `rho:byte list`;
                        `s8:armstate`] GM3_INPUT) THEN
          ANTS_TAC THENL
           [ASM_REWRITE_TAC[] THEN
            CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
            ASM_REWRITE_TAC[];
            STRIP_TAC THEN ASM_REWRITE_TAC[]]))
   [`e:(uarch_event)list`; `read X0 s`; `168`; `read X2 s`; `34`; `31`;
    `num_of_bytelist(inp:byte list)`; `pc:num`; `read SP s`;
    `read X30 s`] 9 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The first three blocks ***)

let GM3F_PART_M2_TAC =
  GM3F_INIT_TAC THEN
  GM3F_CALL_TAC "H_SQ3" None
   [`e:(uarch_event)list`; `word_add buf (word 768):int64`; `buf:int64`;
    `S0:1600 word`; `bp:int64`; `pc:num`] 1 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The first sampling ***)

let GM3F_PART_A1_TAC =
  GM3F_INIT_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (1--6) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_add (word_sub x (word 4096)) (word 4096):int64 = x`]) THEN
  REJ_INPUT0_TAC `s6:armstate` THEN
  GM3F_CALL_TAC "H_REJ" None
   [`e:(uarch_event)list`; `read X0 s`; `0`; `read X2 s`; `504`;
    `wordlist_of_num 336
      (num_of_bytelist(list_of_seq (shake128 inp) 504)):(12 word)list`;
    `pc:num`; `read X30 s`] 7 THEN
  REJ_POST_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; MULT_CLAUSES; SUB_0; WORD_ADD_0;
                              LENGTH_SUB_LIST]) THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP REJ_BYTES16_OF_WORDLIST o check
   (can (term_match [] `wordlist_from_memory(a,n) s = l:int16 list`) o
    concl)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** No more block needed ***)

let GM3F_PART_NOLOOP_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `k0 = 0`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; ADD_CLAUSES]) THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`MIN 256`,REJ_C0),`256`))
   (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[ARITH_RULE `MIN a b = a <=> a <= b`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GM3F_INIT_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (1--3) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`shake128 inp`; `0`; `k:num`] REJ_SAMPLE_FINAL) THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The loop of further blocks ***)

let GM3F_LOOP_INIT_TAC =
  GM3F_INIT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (1--3) THEN
  REJ_ARGS_32_TAC REJ_C0 THEN REJ_HI_TAC REJ_C0 THEN
  SUBGOAL_THEN (mk_neg(mk_binop `(<):num->num->bool` `255` REJ_C0))
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [FIRST_ASSUM(fun th ->
      if is_binary "<" (concl th) && lhand(concl th) = REJ_C0
      then MP_TAC th THEN ARITH_TAC else NO_TAC);
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  REJ_MIN_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let GM3F_LOOP_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN (mk_binop `(<):num->num->bool` (rej_count `i:num`) `256`)
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[NOT_LE];
    ALL_TAC] THEN
  REJ_MIN_TAC THEN GM3F_INIT_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (1--2) THEN
  KECCAK_STATE_AT_TAC `word_add buf (word 768):int64` THEN
  GM3F_CALL_TAC "H_PERM" None
   [`e:(uarch_event)list`; `read X0 s`;
    `keccak_squeeze (3 + i) (S0:1600 word)`; `pc:num`;
    `read SP s`; `read X30 s`] 3 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM(SPECL [`3 + i`; `S0:1600 word`]
                                    KSQ_SUC)]) THEN
  ABBREV_TAC (mk_eq(`ci:num`,rej_count `i:num`)) THEN
  SUBGOAL_THEN `ci <= 256` ASSUME_TAC THENL
   [UNDISCH_TAC `ci < 256` THEN ARITH_TAC; ALL_TAC] THEN
  GM3F_CALL_TAC "H_COPYU" (Some (REWRITE_TAC[ADD_ASSOC]))
   [`e:(uarch_event)list`; `word_add buf (word 768):int64`; `buf:int64`;
    `keccak_squeeze (3 + i + 1) (S0:1600 word)`; `read X19 s`;
    `read X25 s`; `pc:num`] 4 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (5--5) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600;
                              ARITH_RULE `(3 + i) + 1 = 3 + (i + 1)`]) THEN
  REJ_ARGS_32_TAC `ci:num` THEN REJ_BLOCK_TAC `s5:armstate` THEN
  GM3F_CALL_TAC "H_REJ" None
   [`e:(uarch_event)list`; `read X0 s`; `ci:num`; `read X2 s`; `168`;
    rej_block `i:num`; `pc:num`; `read X30 s`] 6 THEN
  REJ_COMBINE_TAC "s6" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (7--9) THEN
  REJ_ARGS_32_TAC REJ_CN THEN REJ_HI_TAC REJ_CN THEN REJ_LS_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600;
                              ARITH_RULE `(3 + i) + 1 = 3 + (i + 1)`]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && rand(concl th) = `ci:num`
    then SUBST_ALL_TAC(SYM th) else NO_TAC) THEN
  GM3_LOOP_DISCHARGE_TAC;;

let GM3F_LOOP_EXIT_TAC =
  GM3F_INIT_TAC THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`MIN 256`,rej_count `k0:num`),`256`))
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  MP_TAC(ISPECL [`shake128 inp`; `k0:num`; `k:num`] REJ_SAMPLE_FINAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let GM3F_PART_LOOP_TAC =
  SUBGOAL_THEN (mk_binop `(<):num->num->bool` REJ_C0 `256`) ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (is_forall o concl)) THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; NOT_LE] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`MIN 256`,REJ_C0),REJ_C0))
   (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[ARITH_RULE `MIN a b = b <=> b <= a`] THEN
    ASM_SIMP_TAC[LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[EQF_INTRO(ASSUME `~(k0 = 0)`)] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `k0:num` `pc + mlkem768_gen_matrix_loop4`
   `pc + mlkem768_gen_matrix_loop4_exit` GM3_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    GM3F_LOOP_INIT_TAC;
    GM3F_LOOP_BODY_TAC;
    GM3F_LOOP_EXIT_TAC];;

(*** Releasing the state, zeroing the buffer ***)

let GM3F_PART_REL_TAC =
  GM3F_INIT_TAC THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
             (vsubst [mk_small_numeral(layout "got_memset"),`n:num`]
                `read (memory :> bytes64 (word (pc + n))) s = (g:int64)`))
           (concl th)
    then ASSUME_TAC(REWRITE_RULE[WORD_ADD] th) else NO_TAC) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (1--12) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC 12 THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" MLKEM_NATIVE_GENMAT3_REJ_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref GM3F_ALLOWED) 17 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   (mk_eq(mk_comb(`LENGTH:(16 word)list->num`,rej_l1 `k:num`),`256`))
  ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST; SUB_0;
                ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(fun th ->
      if concl th = mk_eq(mk_comb(`LENGTH:(16 word)list->num`,rej_l1 `k:num`),
                          `256`)
      then GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [SYM th]
      else NO_TAC) THEN
    MATCH_MP_TAC REJ_WORDLIST_OF_BYTES16 THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[];
    DISCHARGE_SAFETY_PROPERTY_TAC];;

let GM3F_MAIN_TAC =
  GM3F_INTRO_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem768_gen_matrix_loop4_exit` GM3_A2 THEN
  CONJ_TAC THENL
   [ENSURES_EVENTS_SEQUENCE_TAC
      `pc + mlkem768_gen_matrix_after_mlk_rej_uniform_c_1` GM3_A1 THEN
    CONJ_TAC THENL
     [ENSURES_EVENTS_SEQUENCE_TAC
        `pc + mlkem768_gen_matrix_loop2_exit` GM3_M2 THEN
      CONJ_TAC THENL
       [ENSURES_EVENTS_SEQUENCE_TAC
          `pc + mlkem768_gen_matrix_loop2` GM3_M1 THEN
        CONJ_TAC THENL [GM3F_PART_M1_TAC; GM3F_PART_M2_TAC];
        GM3F_PART_A1_TAC];
      ASM_CASES_TAC `k0 = 0` THENL
       [GM3F_PART_NOLOOP_TAC; GM3F_PART_LOOP_TAC]];
    GM3F_PART_REL_TAC];;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_MONO_IN_MLKEM768_GEN_MATRIX_FULL_STMT =
  genmat3_rej_full_goal;;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_MONO_IN_MLKEM768_GEN_MATRIX_FULL =
  assume_spec MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_MONO_IN_MLKEM768_GEN_MATRIX_FULL_STMT;;
