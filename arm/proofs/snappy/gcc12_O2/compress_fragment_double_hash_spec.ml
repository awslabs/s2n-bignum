(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::internal::CompressFragmentDoubleHash(const char* input,           *)
(* size_t input_size, char* op, uint16_t* table, int table_size,             *)
(* uint16_t* table2, int table_size2), compression level 2, as compiled by   *)
(* gcc 12 -O2 (see arm/snappy/README.md), in the whole image.                *)
(*                                                                           *)
(* For a fragment inp of at most kBlockSize = 65536 bytes at src, and two    *)
(* zeroed tables of ts = CalculateTableSize(LENGTH inp) / 2 entries, as      *)
(* InternalCompress passes them (table and table + ts; table_size2 is not    *)
(* read), the function writes snappy_compress_fragment 2 inp at op and       *)
(* returns op plus its length. It may write the MaxCompressedLength bytes at *)
(* op, the tables and its 48 bytes of stack; memcpy (the literal at the end  *)
(* of the fragment) is called through the PLT under its contract.            *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_init_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_loop1_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_loop2_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_join4_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_loop4_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_join5_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_loop5_spec.ml";;
needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_join2_spec.ml";;

(* The statement of arm/snappy/DESIGN.md section 5.1, the contract that the *)
(* proof of InternalCompress assumes. Here inp is the fragment as a byte     *)
(* list and src its address (the pieces call them src and inp, as the model  *)
(* files do).                                                                *)

let SNAPPY_COMPRESS_FRAGMENT_DOUBLE_HASH_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!src inp op table table2 pc imp ea el ev rw stackpointer returnaddress.
    aligned 4096 (word pc:int64) /\
    pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
    memcpy_contract (imp "memcpy") ea el ev /\
    elf_relocated_data (word(pc + libsnappy_rw)) rw
      (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
    aligned 16 stackpointer /\
    LENGTH inp <= 65536 /\
    val src + LENGTH inp + 65536 < 2 EXP 64 /\
    val op + (snappy_max_compressed_length (LENGTH inp) - 5) < 2 EXP 64 /\
    PAIRWISE nonoverlapping
     [op,(snappy_max_compressed_length (LENGTH inp) - 5);
      table,2 * (snappy_table_size (LENGTH inp) DIV 2);
      table2,2 * (snappy_table_size (LENGTH inp) DIV 2);
      word_sub stackpointer (word 48),48] /\
    ALLPAIRS nonoverlapping
     [op,(snappy_max_compressed_length (LENGTH inp) - 5);
      table,2 * (snappy_table_size (LENGTH inp) DIV 2);
      table2,2 * (snappy_table_size (LENGTH inp) DIV 2);
      word_sub stackpointer (word 48),48]
     [src,LENGTH inp; word pc,libsnappy_rw + libsnappy_rw_size; ea,el]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
              read PC s = word(pc + CompressFragmentDoubleHash) /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [src; word(LENGTH inp); op;
                           table; word(snappy_table_size (LENGTH inp) DIV 2);
                           table2; word(snappy_table_size (LENGTH inp) DIV 2)]
                          s /\
              read (memory :> bytes(word(pc + libsnappy_rw),
                                    libsnappy_rw_size)) s = rw /\
              read (memory :> bytes(ea,el)) s = ev /\
              read (memory :> bytelist(src,LENGTH inp)) s = inp /\
              read (memory :> bytes(table,
                      2 * (snappy_table_size (LENGTH inp) DIV 2))) s = 0 /\
              read (memory :> bytes(table2,
                      2 * (snappy_table_size (LENGTH inp) DIV 2))) s = 0)
         (\s. read PC s = returnaddress /\
              C_RETURN s =
              word_add op (word(LENGTH(snappy_compress_fragment 2 inp))) /\
              read (memory :> bytelist
                     (op,LENGTH(snappy_compress_fragment 2 inp))) s =
              snappy_compress_fragment 2 inp)
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
          MAYCHANGE [memory :> bytes(op,snappy_max_compressed_length
                                          (LENGTH inp) - 5);
                     memory :> bytes(table,
                       2 * (snappy_table_size (LENGTH inp) DIV 2));
                     memory :> bytes(table2,
                       2 * (snappy_table_size (LENGTH inp) DIV 2));
                     memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let SNAPPY_COMPRESS_FRAGMENT_DOUBLE_HASH_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
    SNAPPY_COMPRESS_FRAGMENT_DOUBLE_HASH_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* Memory safety with correctness (the correct_safe form of DESIGN.md       *)
(* section 2, as section 5.1 states it): the same with memcpy's contract     *)
(* with memory safety, and the events of the call in the regions it may      *)
(* read and write.                                                           *)

let SNAPPY_COMPRESS_FRAGMENT_DOUBLE_HASH_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e src inp op table table2 pc imp ea el ev rw stackpointer returnaddress.
    aligned 4096 (word pc:int64) /\
    pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
    memcpy_correct_safe_contract (imp "memcpy") ea el ev /\
    elf_relocated_data (word(pc + libsnappy_rw)) rw
      (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
    aligned 16 stackpointer /\
    LENGTH inp <= 65536 /\
    val src + LENGTH inp + 65536 < 2 EXP 64 /\
    val op + (snappy_max_compressed_length (LENGTH inp) - 5) < 2 EXP 64 /\
    PAIRWISE nonoverlapping
     [op,(snappy_max_compressed_length (LENGTH inp) - 5);
      table,2 * (snappy_table_size (LENGTH inp) DIV 2);
      table2,2 * (snappy_table_size (LENGTH inp) DIV 2);
      word_sub stackpointer (word 48),48] /\
    ALLPAIRS nonoverlapping
     [op,(snappy_max_compressed_length (LENGTH inp) - 5);
      table,2 * (snappy_table_size (LENGTH inp) DIV 2);
      table2,2 * (snappy_table_size (LENGTH inp) DIV 2);
      word_sub stackpointer (word 48),48]
     [src,LENGTH inp; word pc,libsnappy_rw + libsnappy_rw_size; ea,el]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
              read PC s = word(pc + CompressFragmentDoubleHash) /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [src; word(LENGTH inp); op;
                           table; word(snappy_table_size (LENGTH inp) DIV 2);
                           table2; word(snappy_table_size (LENGTH inp) DIV 2)]
                          s /\
              read (memory :> bytes(word(pc + libsnappy_rw),
                                    libsnappy_rw_size)) s = rw /\
              read (memory :> bytes(ea,el)) s = ev /\
              read (memory :> bytelist(src,LENGTH inp)) s = inp /\
              read (memory :> bytes(table,
                      2 * (snappy_table_size (LENGTH inp) DIV 2))) s = 0 /\
              read (memory :> bytes(table2,
                      2 * (snappy_table_size (LENGTH inp) DIV 2))) s = 0 /\
              read events s = e)
         (\s. read PC s = returnaddress /\
              C_RETURN s =
              word_add op (word(LENGTH(snappy_compress_fragment 2 inp))) /\
              read (memory :> bytelist
                     (op,LENGTH(snappy_compress_fragment 2 inp))) s =
              snappy_compress_fragment 2 inp /\
              ?e2. read events s = APPEND e2 e /\
                   memaccess_inbounds e2
                    [src,LENGTH inp;
                     op,(snappy_max_compressed_length (LENGTH inp) - 5);
                     table,2 * (snappy_table_size (LENGTH inp) DIV 2);
                     table2,2 * (snappy_table_size (LENGTH inp) DIV 2);
                     word_sub stackpointer (word 48),48;
                     word pc,libsnappy_rw + libsnappy_rw_size; ea,el]
                    [op,(snappy_max_compressed_length (LENGTH inp) - 5);
                     table,2 * (snappy_table_size (LENGTH inp) DIV 2);
                     table2,2 * (snappy_table_size (LENGTH inp) DIV 2);
                     word_sub stackpointer (word 48),48])
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
          MAYCHANGE [memory :> bytes(op,snappy_max_compressed_length
                                          (LENGTH inp) - 5);
                     memory :> bytes(table,
                       2 * (snappy_table_size (LENGTH inp) DIV 2));
                     memory :> bytes(table2,
                       2 * (snappy_table_size (LENGTH inp) DIV 2));
                     memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let SNAPPY_COMPRESS_FRAGMENT_DOUBLE_HASH_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
    SNAPPY_COMPRESS_FRAGMENT_DOUBLE_HASH_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
