(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::CompressionContext::~CompressionContext(), which is Reset():      *)
(* gcc 12 -O2 compiles it to a tail call of CompressionContext::Reset, so    *)
(* its theorems are those of Reset (compression_context_reset_spec.ml) at    *)
(* its own address, in the same three cases (OWNED: both heap blocks freed, *)
(* no leak; BORROWED and NULL: no heap).                                    *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/compression_context_reset_spec.ml";;

(*** The code in the image (see the listing in layout.ml):

    CompressionContext_dtor:
     +0x0  b       CompressionContext_Reset
 ***)

let SNAPPY_COMPRESSION_CONTEXT_DTOR_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "CompressionContext_dtor"];;

(* ------------------------------------------------------------------------- *)
(* The owning context.                                                       *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_COMPRESSION_CONTEXT_DTOR_OWNED_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!heap_ok heap_fp heap_room stk.
   heap_model heap_ok heap_fp heap_room stk (imp "_Znwm") (imp "_ZdlPv")
   ==> !e cc wm mem m pc rw H sp returnaddress x19 x20 x29.
     aligned 4096 (word pc:int64) /\
     pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
     elf_relocated_data (word(pc + libsnappy_rw)) rw
       (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
     aligned 16 sp /\
     MEM (wm,48) H /\ MEM (mem,m) H /\ ~(wm = mem) /\ stk <= 1024 /\
     DISJOINT (memrange(word pc,libsnappy_rw + libsnappy_rw_size))
              (heap_fp H UNION memrange(mem,m) UNION memrange(wm,48)) /\
     DISJOINT (memrange(word_sub sp (word 1056),1056))
              (heap_fp H UNION memrange(mem,m) UNION memrange(wm,48)) /\
     DISJOINT (memrange(cc,16))
              (heap_fp H UNION memrange(mem,m) UNION memrange(wm,48)) /\
     ALLPAIRS nonoverlapping [(cc,16); (word_sub sp (word 1056),1056)]
                             [(word pc,libsnappy_rw + libsnappy_rw_size)] /\
     nonoverlapping (cc,16) (word_sub sp (word 1056),1056)
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + CompressionContext_dtor) /\
           read SP s = sp /\ read X30 s = returnaddress /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
           C_ARGUMENTS [cc] s /\
           read (memory :> bytes64 cc) s = wm /\
           read (memory :> bytes8 (word_add cc (word 8))) s = word 1 /\
           read (memory :> bytes64 wm) s = mem /\
           read (memory :> bytes8 (word_add wm (word 16))) s = word 1 /\
           read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s = rw /\
           read events s = e /\
           heap_ok H (read (memory :> footprint (heap_fp H)) s))
      (\s. read PC s = returnaddress /\ read SP s = sp /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
           read (memory :> bytes64 cc) s = word 0 /\
           heap_fp (heap_remove wm (heap_remove mem H)) SUBSET
           heap_fp H UNION memrange(mem,m) UNION memrange(wm,48) /\
           heap_ok (heap_remove wm (heap_remove mem H))
             (read (memory :> footprint
                     (heap_fp (heap_remove wm (heap_remove mem H)))) s) /\
           ?e2. read events s = APPEND e2 e /\
                memaccess_inset e2
                 (heap_fp H UNION memrange(mem,m) UNION memrange(wm,48) UNION
                  memrange(word_sub sp (word 1056),1056) UNION memrange(cc,16) UNION
                  memrange(word(pc + libsnappy_rw),libsnappy_rw_size))
                 (heap_fp H UNION memrange(mem,m) UNION memrange(wm,48) UNION
                  memrange(word_sub sp (word 1056),1056) UNION memrange(cc,16)))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X18; X19; X20; X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 1056),1024)] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 32),32)] ,,
       MAYCHANGE [memory :> bytes(cc,8)] ,,
       MAYCHANGE [memory :> footprint
                   (heap_fp H UNION memrange(mem,m) UNION memrange(wm,48))])`;;

let SNAPPY_COMPRESSION_CONTEXT_DTOR_OWNED_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   SNAPPY_COMPRESSION_CONTEXT_DTOR_OWNED_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

let SNAPPY_COMPRESSION_CONTEXT_DTOR_OWNED_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!heap_ok heap_fp heap_room stk.
   heap_model heap_ok heap_fp heap_room stk (imp "_Znwm") (imp "_ZdlPv")
   ==> !cc wm mem m pc rw H sp returnaddress x19 x20 x29.
     aligned 4096 (word pc:int64) /\
     pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
     elf_relocated_data (word(pc + libsnappy_rw)) rw
       (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
     aligned 16 sp /\
     MEM (wm,48) H /\ MEM (mem,m) H /\ ~(wm = mem) /\ stk <= 1024 /\
     DISJOINT (memrange(word pc,libsnappy_rw + libsnappy_rw_size))
              (heap_fp H UNION memrange(mem,m) UNION memrange(wm,48)) /\
     DISJOINT (memrange(word_sub sp (word 1056),1056))
              (heap_fp H UNION memrange(mem,m) UNION memrange(wm,48)) /\
     DISJOINT (memrange(cc,16))
              (heap_fp H UNION memrange(mem,m) UNION memrange(wm,48)) /\
     ALLPAIRS nonoverlapping [(cc,16); (word_sub sp (word 1056),1056)]
                             [(word pc,libsnappy_rw + libsnappy_rw_size)] /\
     nonoverlapping (cc,16) (word_sub sp (word 1056),1056)
     ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
           read PC s = word (pc + CompressionContext_dtor) /\
           read SP s = sp /\ read X30 s = returnaddress /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
           C_ARGUMENTS [cc] s /\
           read (memory :> bytes64 cc) s = wm /\
           read (memory :> bytes8 (word_add cc (word 8))) s = word 1 /\
           read (memory :> bytes64 wm) s = mem /\
           read (memory :> bytes8 (word_add wm (word 16))) s = word 1 /\
           read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s = rw /\
           heap_ok H (read (memory :> footprint (heap_fp H)) s))
      (\s. read PC s = returnaddress /\ read SP s = sp /\
           read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
           read (memory :> bytes64 cc) s = word 0 /\
           heap_fp (heap_remove wm (heap_remove mem H)) SUBSET
           heap_fp H UNION memrange(mem,m) UNION memrange(wm,48) /\
           heap_ok (heap_remove wm (heap_remove mem H))
             (read (memory :> footprint
                     (heap_fp (heap_remove wm (heap_remove mem H)))) s))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [SP; X18; X19; X20; X29; X30] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 1056),1024)] ,,
       MAYCHANGE [memory :> bytes(word_sub sp (word 32),32)] ,,
       MAYCHANGE [memory :> bytes(cc,8)] ,,
       MAYCHANGE [memory :> footprint
                   (heap_fp H UNION memrange(mem,m) UNION memrange(wm,48))])`;;

let SNAPPY_COMPRESSION_CONTEXT_DTOR_OWNED_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   SNAPPY_COMPRESSION_CONTEXT_DTOR_OWNED_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The context on a workspace of the caller.                                 *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_COMPRESSION_CONTEXT_DTOR_BORROWED_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e cc wm pc sp returnaddress x19 x20 x29.
        aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
        aligned 16 sp /\ ~(wm = word 0) /\
        ALLPAIRS nonoverlapping [(cc,16); (wm,48); (word_sub sp (word 32),32)]
                                [(word pc,libsnappy_size)] /\
        ALL (nonoverlapping (word_sub sp (word 32),32)) [(cc,16); (wm,48)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + CompressionContext_dtor) /\
                  read SP s = sp /\ read X30 s = returnaddress /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  C_ARGUMENTS [cc] s /\
                  read (memory :> bytes64 cc) s = wm /\
                  read (memory :> bytes8 (word_add cc (word 8))) s = word 0 /\
                  read (memory :> bytes8 (word_add wm (word 16))) s = word 0 /\
                  read events s = e)
             (\s. read PC s = returnaddress /\ read SP s = sp /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  read (memory :> bytes64 cc) s = word 0 /\
                  ?e2. read events s = APPEND e2 e /\
                       memaccess_inset e2
                        (memrange(cc,16) UNION memrange(wm,48) UNION
                         memrange(word_sub sp (word 32),32))
                        (memrange(cc,16) UNION memrange(word_sub sp (word 32),32)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [SP; X19; X20; X29; X30] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 32),32)] ,,
              MAYCHANGE [memory :> bytes(cc,8)])`;;

let SNAPPY_COMPRESSION_CONTEXT_DTOR_BORROWED_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   SNAPPY_COMPRESSION_CONTEXT_DTOR_BORROWED_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

let SNAPPY_COMPRESSION_CONTEXT_DTOR_BORROWED_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!cc wm pc sp returnaddress x19 x20 x29.
        aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
        aligned 16 sp /\ ~(wm = word 0) /\
        ALLPAIRS nonoverlapping [(cc,16); (wm,48); (word_sub sp (word 32),32)]
                                [(word pc,libsnappy_size)] /\
        ALL (nonoverlapping (word_sub sp (word 32),32)) [(cc,16); (wm,48)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + CompressionContext_dtor) /\
                  read SP s = sp /\ read X30 s = returnaddress /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  C_ARGUMENTS [cc] s /\
                  read (memory :> bytes64 cc) s = wm /\
                  read (memory :> bytes8 (word_add cc (word 8))) s = word 0 /\
                  read (memory :> bytes8 (word_add wm (word 16))) s = word 0 /\
                  read events s = e)
             (\s. read PC s = returnaddress /\ read SP s = sp /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  read (memory :> bytes64 cc) s = word 0)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [SP; X19; X20; X29; X30] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 32),32)] ,,
              MAYCHANGE [memory :> bytes(cc,8)])`;;

let SNAPPY_COMPRESSION_CONTEXT_DTOR_BORROWED_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   SNAPPY_COMPRESSION_CONTEXT_DTOR_BORROWED_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The empty context.                                                        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_COMPRESSION_CONTEXT_DTOR_NULL_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `!e cc pc sp returnaddress x19 x20 x29.
        aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
        aligned 16 sp /\
        ALLPAIRS nonoverlapping [(cc,16); (word_sub sp (word 32),32)]
                                [(word pc,libsnappy_size)] /\
        nonoverlapping (cc,16) (word_sub sp (word 32),32)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + CompressionContext_dtor) /\
                  read SP s = sp /\ read X30 s = returnaddress /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  C_ARGUMENTS [cc] s /\
                  read (memory :> bytes64 cc) s = word 0 /\
                  read events s = e)
             (\s. read PC s = returnaddress /\ read SP s = sp /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  ?e2. read events s = APPEND e2 e /\
                       memaccess_inset e2
                        (memrange(cc,16) UNION memrange(word_sub sp (word 32),32))
                        (memrange(word_sub sp (word 32),32)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [SP; X19; X20; X29; X30] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 32),32)])`;;

let SNAPPY_COMPRESSION_CONTEXT_DTOR_NULL_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   SNAPPY_COMPRESSION_CONTEXT_DTOR_NULL_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

let SNAPPY_COMPRESSION_CONTEXT_DTOR_NULL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!cc pc sp returnaddress x19 x20 x29.
        aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64 /\
        aligned 16 sp /\
        ALLPAIRS nonoverlapping [(cc,16); (word_sub sp (word 32),32)]
                                [(word pc,libsnappy_size)] /\
        nonoverlapping (cc,16) (word_sub sp (word 32),32)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    snappy_libsnappy_gcc12_O2_mc /\
                  read PC s = word (pc + CompressionContext_dtor) /\
                  read SP s = sp /\ read X30 s = returnaddress /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29 /\
                  C_ARGUMENTS [cc] s /\
                  read (memory :> bytes64 cc) s = word 0 /\
                  read events s = e)
             (\s. read PC s = returnaddress /\ read SP s = sp /\
                  read X19 s = x19 /\ read X20 s = x20 /\ read X29 s = x29)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [SP; X19; X20; X29; X30] ,,
              MAYCHANGE [memory :> bytes(word_sub sp (word 32),32)])`;;

let SNAPPY_COMPRESSION_CONTEXT_DTOR_NULL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   SNAPPY_COMPRESSION_CONTEXT_DTOR_NULL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

