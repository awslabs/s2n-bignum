(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::internal::CompressFragment(input, input_size, op, table,          *)
(* table_size), the level-1 fragment compressor, compiled by gcc 12 with -O2 *)
(* (see arm/snappy/README.md), verified in the whole image (libsnappy.ml):   *)
(* its output is the model snappy_compress_fragment 1 of                     *)
(* common/snappy/snappy_compress.ml. The statement is the contract of        *)
(* arm/snappy/DESIGN.md section 5.1.                                         *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/libsnappy.ml";;
needs "arm/proofs/libc.ml";;
needs "common/snappy/snappy_compress.ml";;

let SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!src inp op table pc imp ea el ev rw stackpointer returnaddress.
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
      table,2 * snappy_table_size (LENGTH inp);
      word_sub stackpointer (word 32),32] /\
    ALLPAIRS nonoverlapping
     [op,(snappy_max_compressed_length (LENGTH inp) - 5);
      table,2 * snappy_table_size (LENGTH inp);
      word_sub stackpointer (word 32),32]
     [src,LENGTH inp; word pc,libsnappy_rw + libsnappy_rw_size; ea,el]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
              read PC s = word(pc + CompressFragment) /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [src; word(LENGTH inp); op;
                           table; word(snappy_table_size (LENGTH inp))] s /\
              read (memory :> bytes(word(pc + libsnappy_rw),
                                    libsnappy_rw_size)) s = rw /\
              read (memory :> bytes(ea,el)) s = ev /\
              read (memory :> bytelist(src,LENGTH inp)) s = inp /\
              read (memory :> bytes(table,
                      2 * snappy_table_size (LENGTH inp))) s = 0)
         (\s. read PC s = returnaddress /\
              C_RETURN s =
              word_add op (word(LENGTH(snappy_compress_fragment 1 inp))) /\
              read (memory :> bytelist
                     (op,LENGTH(snappy_compress_fragment 1 inp))) s =
              snappy_compress_fragment 1 inp)
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
          MAYCHANGE [memory :> bytes(op,snappy_max_compressed_length
                                          (LENGTH inp) - 5);
                     memory :> bytes(table,
                       2 * snappy_table_size (LENGTH inp));
                     memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* Memory safety (DESIGN.md section 5.1): correctness and the events in one  *)
(* ensures, with memcpy's correct_safe contract: every access since the call *)
(* is in the input, the regions written, the library or memcpy's region, and *)
(* every write in the output, the table or the stack frame.                  *)

let SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e src inp op table pc imp ea el ev rw stackpointer returnaddress.
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
      table,2 * snappy_table_size (LENGTH inp);
      word_sub stackpointer (word 32),32] /\
    ALLPAIRS nonoverlapping
     [op,(snappy_max_compressed_length (LENGTH inp) - 5);
      table,2 * snappy_table_size (LENGTH inp);
      word_sub stackpointer (word 32),32]
     [src,LENGTH inp; word pc,libsnappy_rw + libsnappy_rw_size; ea,el]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
              read PC s = word(pc + CompressFragment) /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [src; word(LENGTH inp); op;
                           table; word(snappy_table_size (LENGTH inp))] s /\
              read (memory :> bytes(word(pc + libsnappy_rw),
                                    libsnappy_rw_size)) s = rw /\
              read (memory :> bytes(ea,el)) s = ev /\
              read (memory :> bytelist(src,LENGTH inp)) s = inp /\
              read (memory :> bytes(table,
                      2 * snappy_table_size (LENGTH inp))) s = 0 /\
              read events s = e)
         (\s. read PC s = returnaddress /\
              C_RETURN s =
              word_add op (word(LENGTH(snappy_compress_fragment 1 inp))) /\
              read (memory :> bytelist
                     (op,LENGTH(snappy_compress_fragment 1 inp))) s =
              snappy_compress_fragment 1 inp /\
              ?e2. read events s = APPEND e2 e /\
                   memaccess_inbounds e2
                    [src,LENGTH inp;
                     op,snappy_max_compressed_length (LENGTH inp) - 5;
                     table,2 * snappy_table_size (LENGTH inp);
                     word_sub stackpointer (word 32),32;
                     word pc,libsnappy_rw + libsnappy_rw_size; ea,el]
                    [op,snappy_max_compressed_length (LENGTH inp) - 5;
                     table,2 * snappy_table_size (LENGTH inp);
                     word_sub stackpointer (word 32),32])
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
          MAYCHANGE [memory :> bytes(op,snappy_max_compressed_length
                                          (LENGTH inp) - 5);
                     memory :> bytes(table,
                       2 * snappy_table_size (LENGTH inp));
                     memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
