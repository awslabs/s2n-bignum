(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of the x86 mlkem_gen_matrix: SampleNTT (FIPS 203,    *)
(* Algorithm 7) as the rejection sampling of the 12-bit fields of whole      *)
(* blocks of SHAKE128 output, mlkem_rej_uniform_alt_VARIABLE_TIME and        *)
(* mlkem_unpack in the forms that the sampling of a matrix polynomial needs, *)
(* the seed of a matrix polynomial as the state of a Keccak lane, the sponge *)
(* by blocks for the hash jobs, and memory lemmas for the digests. As        *)
(* arm/proofs/utils/mlkem_native2_matrix.ml for AArch64, with the x86 forms  *)
(* of the code and the simulation.                                           *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/asm/noise_spec.ml";;
needs "x86/proofs/utils/mlkem_native_fips203.ml";;
needs "x86/proofs/mlkem_native/asm/rej_uniform_alt_VARIABLE_TIME_spec.ml";;
needs "x86/proofs/mlkem_native/asm/unpack_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* SampleNTT as the first 256 accepted 12-bit fields (those < q) of the      *)
(* first N fields of the XOF stream, when at least 256 of them are accepted, *)
(* and the fields of a later block as fields of the stream (with the fields  *)
(* of the bytes of a stream and the filters of list_of_seq of                *)
(* x86/proofs/utils/mlkem_native_fips203.ml).                                *)
(* ------------------------------------------------------------------------- *)

let CARD_RESTRICT_LT_STMT =
  `!(P:num->bool) j1 j2.
        P j1 /\ j1 < j2
        ==> CARD {i | i < j1 /\ P i} < CARD {i | i < j2 /\ P i}`;;

let CARD_RESTRICT_LT = assume_spec CARD_RESTRICT_LT_STMT;;

let CARD_RESTRICT_UNIQUE_STMT =
  `!(P:num->bool) j1 j2.
        P j1 /\ P j2 /\
        CARD {i | i < j1 /\ P i} = CARD {i | i < j2 /\ P i}
        ==> j1 = j2`;;

let CARD_RESTRICT_UNIQUE = assume_spec CARD_RESTRICT_UNIQUE_STMT;;

let LIST_OF_SEQ_APPEND_ADD = prove
 (`!(f:num->A) m n.
        list_of_seq f (m + n) =
        APPEND (list_of_seq f m) (list_of_seq (\i. f(m + i)) n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; list_of_seq; APPEND_NIL; APPEND_ASSOC]);;

let FILTER_REJ_FIELDS_STMT =
  `!(s:num->byte) N.
        FILTER (\x:int16. val x < 3329)
         (list_of_seq (\j. word(mlkem_xof_field s j)) N) =
        MAP word (FILTER (\x. x < 3329) (list_of_seq (mlkem_xof_field s) N))`;;

let FILTER_REJ_FIELDS = assume_spec FILTER_REJ_FIELDS_STMT;;

let REJ_SAMPLE_NTT_STMT =
  `!b N M t.
        12 * N <= 8 * M /\
        256 <= CARD {j | j < N /\ mlkem_xof_field (shake128 b) j < 3329} /\
        t < 256
        ==> EL t (SUB_LIST(0,256)
                   (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                       (wordlist_of_num N
                         (num_of_bytelist(list_of_seq (shake128 b) M)))))) =
            iword(mlkem_sample_ntt b t)`;;

let REJ_SAMPLE_NTT = assume_spec REJ_SAMPLE_NTT_STMT;;

let MLKEM_XOF_FIELD_SHIFT_STMT =
  `!(s:num->byte) m j.
        mlkem_xof_field (\i. s(168 * m + i)) j =
        mlkem_xof_field s (112 * m + j)`;;

let MLKEM_XOF_FIELD_SHIFT = assume_spec MLKEM_XOF_FIELD_SHIFT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The result of the rejection sampling of the first m blocks of 168 bytes,  *)
(* mlkem_rej_out b m, its extension by one block, and the number of blocks   *)
(* needed, mlkem_rej_blocks b (at least the three that the code always       *)
(* takes), for a seed b for which SampleNTT terminates                       *)
(* (mlkem_samplentt_terminates, true of the seeds of the matrix by           *)
(* MLKEM_SAMPLENTT_TERMINATES_SEED).                                         *)
(* ------------------------------------------------------------------------- *)

let mlkem_rej_out = new_definition
 `mlkem_rej_out (b:byte list) m =
    SUB_LIST(0,256)
     (FILTER (\x:int16. val x < 3329)
       (list_of_seq (\j. word(mlkem_xof_field (shake128 b) j)) (112 * m)))`;;

let MLKEM_REJ_OUT_BUF_STMT =
  `!b. SUB_LIST(0,256)
        (APPEND []
          (FILTER (\x. val x < 3329)
            (MAP (word_zx:12 word->16 word)
              (wordlist_of_num 336
                (num_of_bytelist(list_of_seq (shake128 b) 504)))))) =
       mlkem_rej_out b 3`;;

let MLKEM_REJ_OUT_BUF = assume_spec MLKEM_REJ_OUT_BUF_STMT;;

let MLKEM_REJ_OUT_BLOCK_STMT =
  `!b m. SUB_LIST(0,256)
          (APPEND (mlkem_rej_out b m)
            (FILTER (\x. val x < 3329)
              (MAP (word_zx:12 word->16 word)
                (wordlist_of_num 112
                  (num_of_bytelist
                    (list_of_seq (\j. shake128 b (168 * m + j)) 168)))))) =
         mlkem_rej_out b (m + 1)`;;

let MLKEM_REJ_OUT_BLOCK = assume_spec MLKEM_REJ_OUT_BLOCK_STMT;;

let mlkem_rej_blocks = new_definition
 `mlkem_rej_blocks (b:byte list) =
    minimal m. 3 <= m /\
               256 <= CARD {j | j < 112 * m /\
                                mlkem_xof_field (shake128 b) j < 3329}`;;

let MLKEM_REJ_BLOCKS_STMT =
  `!b. mlkem_samplentt_terminates b
       ==> 3 <= mlkem_rej_blocks b /\
           256 <= CARD {j | j < 112 * mlkem_rej_blocks b /\
                            mlkem_xof_field (shake128 b) j < 3329} /\
           !m. m < mlkem_rej_blocks b /\ 3 <= m
               ==> CARD {j | j < 112 * m /\
                             mlkem_xof_field (shake128 b) j < 3329} < 256`;;

let MLKEM_REJ_BLOCKS = assume_spec MLKEM_REJ_BLOCKS_STMT;;

let LENGTH_MLKEM_REJ_OUT_STMT =
  `!b m. LENGTH(mlkem_rej_out b m) =
         MIN 256 (CARD {j | j < 112 * m /\
                            mlkem_xof_field (shake128 b) j < 3329})`;;

let LENGTH_MLKEM_REJ_OUT = assume_spec LENGTH_MLKEM_REJ_OUT_STMT;;

let LENGTH_MLKEM_REJ_OUT_LE_STMT =
  `!b m. LENGTH(mlkem_rej_out b m) <= 256`;;

let LENGTH_MLKEM_REJ_OUT_LE = assume_spec LENGTH_MLKEM_REJ_OUT_LE_STMT;;

let LENGTH_MLKEM_REJ_OUT_LT_STMT =
  `!b m. mlkem_samplentt_terminates b /\ 3 <= m /\ m < mlkem_rej_blocks b
         ==> LENGTH(mlkem_rej_out b m) < 256`;;

let LENGTH_MLKEM_REJ_OUT_LT = assume_spec LENGTH_MLKEM_REJ_OUT_LT_STMT;;

let LENGTH_MLKEM_REJ_OUT_BLOCKS_STMT =
  `!b. mlkem_samplentt_terminates b
       ==> LENGTH(mlkem_rej_out b (mlkem_rej_blocks b)) = 256`;;

let LENGTH_MLKEM_REJ_OUT_BLOCKS = assume_spec LENGTH_MLKEM_REJ_OUT_BLOCKS_STMT;;

let MLKEM_REJ_OUT_SAMPLE_NTT_STMT =
  `!b m t.
        256 <= CARD {j | j < 112 * m /\
                         mlkem_xof_field (shake128 b) j < 3329} /\
        t < 256
        ==> EL t (mlkem_rej_out b m) = iword(mlkem_sample_ntt b t)`;;

let MLKEM_REJ_OUT_SAMPLE_NTT = assume_spec MLKEM_REJ_OUT_SAMPLE_NTT_STMT;;

(* ------------------------------------------------------------------------- *)
(* mlkem_rej_uniform_alt_VARIABLE_TIME with its lists as bytes in memory, on *)
(* the three blocks in a buffer with no entries yet and on one more block    *)
(* with the entries so far, with the results as mlkem_rej_out; and then      *)
(* mlkem_unpack of the 256 entries, which puts the coefficients of SampleNTT *)
(* in the order of the x86 kernels (coefficient t at position avx_unorder t  *)
(* of SampleNTT's).                                                          *)
(* ------------------------------------------------------------------------- *)

let WORDLIST_FROM_MEMORY_BYTES16_NUM_STMT =
  `!a (l:int16 list) s:x86state.
        wordlist_from_memory(a,LENGTH l) s = l
        ==> read (memory :> bytes(a,2 * LENGTH l)) s = num_of_wordlist l`;;

let WORDLIST_FROM_MEMORY_BYTES16_NUM = assume_spec WORDLIST_FROM_MEMORY_BYTES16_NUM_STMT;;

let LENGTH_MLKEM_REJ_UNIFORM_TABLE_STMT =
  `LENGTH mlkem_rej_uniform_table = 4096`;;

let LENGTH_MLKEM_REJ_UNIFORM_TABLE = assume_spec LENGTH_MLKEM_REJ_UNIFORM_TABLE_STMT;;

let MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_CORRECT_BYTES_STMT =
  `!res n buf buflen table curlist (inlist:(12 word)list) pc stackpointer
    returnaddress.
      24 divides val buflen /\
      8 * val buflen = 12 * LENGTH inlist /\
      LENGTH curlist = val n /\ val n <= 256 /\
      ALL (nonoverlapping (res,512))
          [(word pc,0x293); (word_sub stackpointer (word 32),40);
           (buf,val buflen); (table,4096)] /\
      ALL (nonoverlapping (word_sub stackpointer (word 32),40))
          [(word pc,0x293); (buf,val buflen); (table,4096)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_rej_uniform_alt_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [res; n; buf; buflen; table] s /\
                read (memory :> bytes(table,4096)) s =
                num_of_wordlist mlkem_rej_uniform_table /\
                read (memory :> bytes(buf,val buflen)) s =
                num_of_wordlist inlist /\
                read (memory :> bytes(res,2 * val n)) s =
                num_of_wordlist curlist)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                C_RETURN s =
                word(LENGTH(SUB_LIST (0,256)
                  (APPEND curlist (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word) inlist))))) /\
                read (memory :> bytes(res,2 * LENGTH(SUB_LIST (0,256)
                  (APPEND curlist (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word) inlist)))))) s =
                num_of_wordlist(SUB_LIST (0,256)
                  (APPEND curlist (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word) inlist)))))
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_CORRECT_BYTES = assume_spec MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_CORRECT_BYTES_STMT;;

let NUM_OF_WORDLIST_OF_NUM_BYTES_STMT =
  `!(l:byte list) n.
        8 * LENGTH l = 12 * n
        ==> num_of_wordlist(wordlist_of_num n (num_of_bytelist l):
                            (12 word)list) =
            num_of_bytelist l`;;

let NUM_OF_WORDLIST_OF_NUM_BYTES = assume_spec NUM_OF_WORDLIST_OF_NUM_BYTES_STMT;;

let MLKEM_REJ_UNIFORM_BUF_STMT =
  `!res buf table (l:byte list) pc stackpointer returnaddress.
      LENGTH l = 504 /\
      ALL (nonoverlapping (res,512))
          [(word pc,0x293); (word_sub stackpointer (word 32),40);
           (buf,504); (table,4096)] /\
      ALL (nonoverlapping (word_sub stackpointer (word 32),40))
          [(word pc,0x293); (buf,504); (table,4096)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_rej_uniform_alt_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [res; word 0; buf; word 504; table] s /\
                read (memory :> bytes(table,4096)) s =
                num_of_wordlist mlkem_rej_uniform_table /\
                read (memory :> bytes(buf,504)) s = num_of_bytelist l)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                C_RETURN s =
                word(LENGTH(SUB_LIST (0,256)
                  (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                      (wordlist_of_num 336 (num_of_bytelist l)))))) /\
                read (memory :> bytes(res,2 * LENGTH(SUB_LIST (0,256)
                  (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                      (wordlist_of_num 336 (num_of_bytelist l))))))) s =
                num_of_wordlist(SUB_LIST (0,256)
                  (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                      (wordlist_of_num 336 (num_of_bytelist l))))))
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_REJ_UNIFORM_BUF = assume_spec MLKEM_REJ_UNIFORM_BUF_STMT;;

let MLKEM_REJ_UNIFORM_BLOCK_STMT =
  `!res buf table (curlist:int16 list) (l:byte list) pc stackpointer
    returnaddress.
      LENGTH l = 168 /\ LENGTH curlist <= 256 /\
      ALL (nonoverlapping (res,512))
          [(word pc,0x293); (word_sub stackpointer (word 32),40);
           (buf,168); (table,4096)] /\
      ALL (nonoverlapping (word_sub stackpointer (word 32),40))
          [(word pc,0x293); (buf,168); (table,4096)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_rej_uniform_alt_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [res; word(LENGTH curlist); buf; word 168;
                             table] s /\
                read (memory :> bytes(table,4096)) s =
                num_of_wordlist mlkem_rej_uniform_table /\
                read (memory :> bytes(buf,168)) s = num_of_bytelist l /\
                read (memory :> bytes(res,2 * LENGTH curlist)) s =
                num_of_wordlist curlist)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                C_RETURN s =
                word(LENGTH(SUB_LIST (0,256)
                  (APPEND curlist (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                      (wordlist_of_num 112 (num_of_bytelist l))))))) /\
                read (memory :> bytes(res,2 * LENGTH(SUB_LIST (0,256)
                  (APPEND curlist (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                      (wordlist_of_num 112 (num_of_bytelist l)))))))) s =
                num_of_wordlist(SUB_LIST (0,256)
                  (APPEND curlist (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                      (wordlist_of_num 112 (num_of_bytelist l)))))))
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_REJ_UNIFORM_BLOCK = assume_spec MLKEM_REJ_UNIFORM_BLOCK_STMT;;

let MLKEM_REJ_UNIFORM_BUF_OUT_STMT =
  `!res buf table b pc stackpointer returnaddress.
      ALL (nonoverlapping (res,512))
          [(word pc,0x293); (word_sub stackpointer (word 32),40);
           (buf,504); (table,4096)] /\
      ALL (nonoverlapping (word_sub stackpointer (word 32),40))
          [(word pc,0x293); (buf,504); (table,4096)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_rej_uniform_alt_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [res; word 0; buf; word 504; table] s /\
                read (memory :> bytes(table,4096)) s =
                num_of_wordlist mlkem_rej_uniform_table /\
                read (memory :> bytes(buf,504)) s =
                num_of_bytelist(list_of_seq (shake128 b) 504))
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                C_RETURN s = word(LENGTH(mlkem_rej_out b 3)) /\
                read (memory :> bytes(res,2 * LENGTH(mlkem_rej_out b 3))) s =
                num_of_wordlist(mlkem_rej_out b 3))
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_REJ_UNIFORM_BUF_OUT = assume_spec MLKEM_REJ_UNIFORM_BUF_OUT_STMT;;

let MLKEM_REJ_UNIFORM_BLOCK_OUT_STMT =
  `!res buf table b m pc stackpointer returnaddress.
      ALL (nonoverlapping (res,512))
          [(word pc,0x293); (word_sub stackpointer (word 32),40);
           (buf,168); (table,4096)] /\
      ALL (nonoverlapping (word_sub stackpointer (word 32),40))
          [(word pc,0x293); (buf,168); (table,4096)]
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mlkem_rej_uniform_alt_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [res; word(LENGTH(mlkem_rej_out b m)); buf;
                             word 168; table] s /\
                read (memory :> bytes(table,4096)) s =
                num_of_wordlist mlkem_rej_uniform_table /\
                read (memory :> bytes(buf,168)) s =
                num_of_bytelist
                 (list_of_seq (\j. shake128 b (168 * m + j)) 168) /\
                read (memory :> bytes(res,2 * LENGTH(mlkem_rej_out b m))) s =
                num_of_wordlist(mlkem_rej_out b m))
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                C_RETURN s = word(LENGTH(mlkem_rej_out b (m + 1))) /\
                read (memory :> bytes(res,2 * LENGTH(mlkem_rej_out b (m + 1))))
                     s =
                num_of_wordlist(mlkem_rej_out b (m + 1)))
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLKEM_REJ_UNIFORM_BLOCK_OUT = assume_spec MLKEM_REJ_UNIFORM_BLOCK_OUT_STMT;;

let READ_MEMORY_BYTES16_EL_STMT =
  `!a (l:int16 list) t s:x86state.
        read (memory :> bytes(a,2 * LENGTH l)) s = num_of_wordlist l /\
        t < LENGTH l
        ==> read (memory :> bytes16(word_add a (word(2 * t)))) s = EL t l`;;

let READ_MEMORY_BYTES16_EL = assume_spec READ_MEMORY_BYTES16_EL_STMT;;

let AVX_UNORDER_LT_STMT =
  `!t. t < 256 ==> avx_unorder t < 256`;;

let AVX_UNORDER_LT = assume_spec AVX_UNORDER_LT_STMT;;

let MLKEM_UNPACK_SAMPLE_NTT_STMT =
  `!a b m pc stackpointer returnaddress.
     256 <= CARD {j | j < 112 * m /\ mlkem_xof_field (shake128 b) j < 3329} /\
     aligned 32 a /\
     nonoverlapping (word pc,LENGTH mlkem_unpack_mc) (a,512) /\
     nonoverlapping (stackpointer,8) (a,512)
     ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_unpack_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [a] s /\
               read (memory :> bytes(a,512)) s =
               num_of_wordlist(mlkem_rej_out b m))
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               !t. t < 256
                   ==> read (memory :> bytes16(word_add a (word(2 * t)))) s =
                       iword(mlkem_sample_ntt b (avx_unorder t)))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(a,512)])`;;

let MLKEM_UNPACK_SAMPLE_NTT = assume_spec MLKEM_UNPACK_SAMPLE_NTT_STMT;;

let READ_MEMORY_BYTES_PREFIX_STMT =
  `!a n m x s:x86state.
        read (memory :> bytes(a,n)) s = x /\ m <= n
        ==> read (memory :> bytes(a,m)) s = x MOD 2 EXP (8 * m)`;;

let READ_MEMORY_BYTES_PREFIX = assume_spec READ_MEMORY_BYTES_PREFIX_STMT;;

let NONOVERLAPPING_SHORTER_STMT =
  `!(a:int64) n n2 b m.
        nonoverlapping (a,n) (b,m) /\ n2 <= n ==> nonoverlapping (a,n2) (b,m)`;;

let NONOVERLAPPING_SHORTER = assume_spec NONOVERLAPPING_SHORTER_STMT;;

(* ------------------------------------------------------------------------- *)
(* The seed rho || x || y of a matrix polynomial absorbed into a lane        *)
(* (mlkem_matrix_state, one block of SHAKE128 with its padding), the lane as *)
(* the code sets it up, and the three blocks squeezed from it, as copied to  *)
(* the buffer, as the first 504 bytes of the XOF.                            *)
(* ------------------------------------------------------------------------- *)

let mlkem_matrix_state = new_definition
 `mlkem_matrix_state (rho:byte list) (x:byte) (y:byte) =
    (word(num_of_bytelist rho + 2 EXP 256 * val x + 2 EXP 264 * val y +
          2 EXP 272 * 31 + 2 EXP 1343):1600 word)`;;

let MLKEM_MATRIX_ABSORB_STMT =
  `!rho:byte list x y.
     LENGTH rho = 32
     ==> word_xor
          (keccak_absorb 168
            (num_of_bytelist(APPEND rho [x; y]) +
             2 EXP (8 * LENGTH(APPEND rho [x; y])) *
             num_of_bytelist(keccak_pad 168 31 (LENGTH(APPEND rho [x; y]))))
            (LENGTH(APPEND rho [x; y]) DIV 168))
          (word(((num_of_bytelist(APPEND rho [x; y]) +
                  2 EXP (8 * LENGTH(APPEND rho [x; y])) *
                  num_of_bytelist(keccak_pad 168 31
                                   (LENGTH(APPEND rho [x; y])))) DIV
                 2 EXP (8 * 168 * LENGTH(APPEND rho [x; y]) DIV 168)) MOD
                2 EXP (8 * 168))) =
         mlkem_matrix_state rho x y`;;

let MLKEM_MATRIX_ABSORB = assume_spec MLKEM_MATRIX_ABSORB_STMT;;

let mlkem_matrix_padded_tm =
  `num_of_bytelist(APPEND (rho:byte list) [x; y]) +
   2 EXP (8 * LENGTH(APPEND rho [x; y])) *
   num_of_bytelist(keccak_pad 168 31 (LENGTH(APPEND rho [x; y])))`;;

let MLKEM_MATRIX_SPONGE_BLOCK_STMT =
  `!rho:byte list x y t.
     LENGTH rho = 32
     ==> num_of_bytelist
          (list_of_seq (\j. shake128(APPEND rho [x; y]) (168 * t + j)) 168) =
         val(keccak_squeeze (t + 1) (mlkem_matrix_state rho x y)) MOD
         2 EXP 1344`;;

let MLKEM_MATRIX_SPONGE_BLOCK = assume_spec MLKEM_MATRIX_SPONGE_BLOCK_STMT;;

let MLKEM_MATRIX_LANE_STMT =
  `!a (rho:byte list) x y s:x86state.
     LENGTH rho = 32 /\ x < 256 /\ y < 256 /\
     read (memory :> bytes256 a) s =
     word(num_of_bytelist rho MOD 2 EXP 256) /\
     read (memory :> bytes64 (word_add a (word 32))) s =
     word(x + 256 * y + 2031616) /\
     read (memory :> bytes256 (word_add a (word 40))) s = word 0 /\
     read (memory :> bytes256 (word_add a (word 72))) s = word 0 /\
     read (memory :> bytes256 (word_add a (word 104))) s = word 0 /\
     read (memory :> bytes128 (word_add a (word 136))) s = word 0 /\
     read (memory :> bytes64 (word_add a (word 152))) s = word 0 /\
     read (memory :> bytes32 (word_add a (word 160))) s = word 0 /\
     read (memory :> bytes16 (word_add a (word 164))) s = word 0 /\
     read (memory :> bytes8 (word_add a (word 166))) s = word 0 /\
     read (memory :> bytes8 (word_add a (word 167))) s = word 128 /\
     read (memory :> bytes256 (word_add a (word 168))) s = word 0
     ==> read (memory :> wbytes a) s =
         mlkem_matrix_state rho (word x) (word y)`;;

let MLKEM_MATRIX_LANE = assume_spec MLKEM_MATRIX_LANE_STMT;;

let READ_MEMORY_BYTES_168_OF_PIECES_STMT =
  `!a x s:x86state.
     (!j. j < 5 ==> read (memory :> bytes256(word_add a (word(32 * j)))) s =
                    word((x DIV 2 EXP (256 * j)) MOD 2 EXP 256)) /\
     read (memory :> bytes64(word_add a (word 160))) s =
     word((x DIV 2 EXP 1280) MOD 2 EXP 64)
     ==> read (memory :> bytes(a,168)) s = x MOD 2 EXP 1344`;;

let READ_MEMORY_BYTES_168_OF_PIECES = assume_spec READ_MEMORY_BYTES_168_OF_PIECES_STMT;;

let MLKEM_MATRIX_BUFFER_STMT =
  `!rho:byte list x y a s:x86state.
     LENGTH rho = 32 /\
     read (memory :> bytes(a,168)) s =
     val(keccak_squeeze 1 (mlkem_matrix_state rho x y)) MOD 2 EXP 1344 /\
     read (memory :> bytes(word_add a (word 168),168)) s =
     val(keccak_squeeze 2 (mlkem_matrix_state rho x y)) MOD 2 EXP 1344 /\
     read (memory :> bytes(word_add a (word 336),168)) s =
     val(keccak_squeeze 3 (mlkem_matrix_state rho x y)) MOD 2 EXP 1344
     ==> read (memory :> bytes(a,504)) s =
         num_of_bytelist(list_of_seq (shake128(APPEND rho [x; y])) 504)`;;

let MLKEM_MATRIX_BUFFER = assume_spec MLKEM_MATRIX_BUFFER_STMT;;

(* ------------------------------------------------------------------------- *)
(* The sponge by blocks, for the hash jobs: block j of a padded message as a *)
(* 1600-bit word, keccak_absorb as the permutation of the state with each    *)
(* block XORed in, and the digests of SHA3-256 and of SHAKE256 to 32 bytes   *)
(* from the state after the last block.                                      *)
(* ------------------------------------------------------------------------- *)

let keccak_absorb_block = new_definition
 `keccak_absorb_block r p j =
    (word((p DIV 2 EXP (8 * r * j)) MOD 2 EXP (8 * r)):1600 word)`;;

let KECCAK_ABSORB_BLOCK_STEP_STMT =
  `!r p j. keccak_f1600(word_xor (keccak_absorb r p j)
                                 (keccak_absorb_block r p j)) =
           keccak_absorb r p (j + 1)`;;

let KECCAK_ABSORB_BLOCK_STEP = assume_spec KECCAK_ABSORB_BLOCK_STEP_STMT;;

let KECCAK_SPONGE_DIGEST_STMT =
  `!c d (m:byte list) n.
      (1600 - c) DIV 8 = 136 /\ n <= 136
      ==> num_of_bytelist(list_of_seq (keccak_sponge c d m) n) =
          val(keccak_f1600
               (word_xor
                 (keccak_absorb 136 (keccak_padded 136 d m) (LENGTH m DIV 136))
                 (keccak_absorb_block 136 (keccak_padded 136 d m)
                                      (LENGTH m DIV 136)))) MOD
          2 EXP (8 * n)`;;

let KECCAK_SPONGE_DIGEST = assume_spec KECCAK_SPONGE_DIGEST_STMT;;

let SHA3_256_DIGEST_STMT =
  `!m:byte list.
      num_of_bytelist(sha3_256 m) =
      val(keccak_f1600
           (word_xor
             (keccak_absorb 136 (keccak_padded 136 6 m) (LENGTH m DIV 136))
             (keccak_absorb_block 136 (keccak_padded 136 6 m)
                                  (LENGTH m DIV 136)))) MOD 2 EXP 256`;;

let SHA3_256_DIGEST = assume_spec SHA3_256_DIGEST_STMT;;

let SHAKE256_32_DIGEST_STMT =
  `!m:byte list.
      num_of_bytelist(list_of_seq (shake256 m) 32) =
      val(keccak_f1600
           (word_xor
             (keccak_absorb 136 (keccak_padded 136 31 m) (LENGTH m DIV 136))
             (keccak_absorb_block 136 (keccak_padded 136 31 m)
                                  (LENGTH m DIV 136)))) MOD 2 EXP 256`;;

let SHAKE256_32_DIGEST = assume_spec SHAKE256_32_DIGEST_STMT;;

(* ------------------------------------------------------------------------- *)
(* Memory: 32 bytes from a 256-bit word, as for the digests.                 *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES_32_OF_BYTES256_STMT =
  `!a x s:x86state.
     read (memory :> bytes256 a) s = word(x MOD 2 EXP 256)
     ==> read (memory :> bytes(a,32)) s = x MOD 2 EXP 256`;;

let READ_MEMORY_BYTES_32_OF_BYTES256 = assume_spec READ_MEMORY_BYTES_32_OF_BYTES256_STMT;;
