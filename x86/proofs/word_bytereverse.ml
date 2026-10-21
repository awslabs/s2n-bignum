(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reversing the order of the bytes in a single 64-bit word.                 *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/word_bytereverse.o";;
 ****)

let word_bytereverse_mc = define_assert_from_elf "word_bytereverse_mc" "x86/generic/word_bytereverse.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x89; 0xf8;        (* MOV (% rax) (% rdi) *)
  0x48; 0x0f; 0xc8;        (* BSWAP (% rax) *)
  0xc3                     (* RET *)
];;

let word_bytereverse_tmc = define_trimmed "word_bytereverse_tmc" word_bytereverse_mc;;

let WORD_BYTEREVERSE_EXEC = X86_MK_CORE_EXEC_RULE word_bytereverse_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let WORD_BYTEREVERSE_CORRECT = prove
 (`!a pc.
        ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST word_bytereverse_tmc) /\
               read RIP s = word pc /\
               C_ARGUMENTS [a] s)
          (\s. read RIP s = word(pc + 0x6) /\
               !i. i < 8
                   ==> word_subword (C_RETURN s) (8 * i,8) :byte =
                       word_subword a (8 * (7 - i),8))
          (MAYCHANGE [RIP; RAX])`,
  MAP_EVERY X_GEN_TAC [`a:int64`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  X86_SIM_TAC WORD_BYTEREVERSE_EXEC (1--2) THEN
  CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THEN
  GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  CONV_TAC(TOP_DEPTH_CONV BIT_WORD_CONV) THEN REFL_TAC);;

let WORD_BYTEREVERSE_NOIBT_SUBROUTINE_CORRECT = prove
 (`!a pc stackpointer returnaddress.
        ensures x86
          (\s. bytes_loaded s (word pc) word_bytereverse_tmc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [a] s)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               !i. i < 8
                   ==> word_subword (C_RETURN s) (8 * i,8) :byte =
                       word_subword a (8 * (7 - i),8))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC word_bytereverse_tmc WORD_BYTEREVERSE_CORRECT);;

let WORD_BYTEREVERSE_SUBROUTINE_CORRECT = prove
 (`!a pc stackpointer returnaddress.
        ensures x86
          (\s. bytes_loaded s (word pc) word_bytereverse_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [a] s)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               !i. i < 8
                   ==> word_subword (C_RETURN s) (8 * i,8) :byte =
                       word_subword a (8 * (7 - i),8))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE WORD_BYTEREVERSE_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let word_bytereverse_windows_mc = define_from_elf
   "word_bytereverse_windows_mc" "x86/generic/word_bytereverse.obj";;

let word_bytereverse_windows_tmc = define_trimmed "word_bytereverse_windows_tmc" word_bytereverse_windows_mc;;

let WORD_BYTEREVERSE_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!a pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 16),16) (word pc,LENGTH word_bytereverse_windows_tmc)
        ==> ensures x86
              (\s. bytes_loaded s (word pc) word_bytereverse_windows_tmc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [a] s)
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   !i. i < 8
                       ==> word_subword (WINDOWS_C_RETURN s) (8 * i,8) :byte =
                           word_subword a (8 * (7 - i),8))
              (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC
    word_bytereverse_windows_tmc word_bytereverse_tmc WORD_BYTEREVERSE_CORRECT);;

let WORD_BYTEREVERSE_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!a pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 16),16) (word pc,LENGTH word_bytereverse_windows_mc)
        ==> ensures x86
              (\s. bytes_loaded s (word pc) word_bytereverse_windows_mc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [a] s)
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   !i. i < 8
                       ==> word_subword (WINDOWS_C_RETURN s) (8 * i,8) :byte =
                           word_subword a (8 * (7 - i),8))
              (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE WORD_BYTEREVERSE_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;


(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* (specs generated with generate_four_variants_of_x86_safety_specs)         *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "word_bytereverse" subroutine_signatures)
    WORD_BYTEREVERSE_CORRECT
    WORD_BYTEREVERSE_EXEC;;

let WORD_BYTEREVERSE_SAFE = time prove
 (`exists f_events.
       forall e a pc.
           ensures x86
           (\s.
                bytes_loaded s (word pc) (BUTLAST word_bytereverse_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [a] s /\
                read events s = e)
           (\s.
                read RIP s = word (pc + 6) /\
                (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events pc /\
                     memaccess_inbounds e2 [] []))
           (MAYCHANGE [RIP; RAX])`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars WORD_BYTEREVERSE_EXEC);;

let WORD_BYTEREVERSE_NOIBT_SUBROUTINE_SAFE = time prove
 (`
exists f_events.
    forall e a pc stackpointer returnaddress.
        ensures x86
        (\s.
             bytes_loaded s (word pc) word_bytereverse_tmc /\
             read RIP s = word pc /\
             read RSP s = stackpointer /\
             read (memory :> bytes64 stackpointer) s = returnaddress /\
             C_ARGUMENTS [a] s /\
             read events s = e)
        (\s.
             read RIP s = returnaddress /\
             read RSP s = word_add stackpointer (word 8) /\
             (exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events pc stackpointer returnaddress /\
                  memaccess_inbounds e2 [stackpointer,8] [stackpointer,0]))
        (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC word_bytereverse_tmc WORD_BYTEREVERSE_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let WORD_BYTEREVERSE_SUBROUTINE_SAFE = time prove
 (`
exists f_events.
    forall e a pc stackpointer returnaddress.
        ensures x86
        (\s.
             bytes_loaded s (word pc) word_bytereverse_mc /\
             read RIP s = word pc /\
             read RSP s = stackpointer /\
             read (memory :> bytes64 stackpointer) s = returnaddress /\
             C_ARGUMENTS [a] s /\
             read events s = e)
        (\s.
             read RIP s = returnaddress /\
             read RSP s = word_add stackpointer (word 8) /\
             (exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events pc stackpointer returnaddress /\
                  memaccess_inbounds e2 [stackpointer,8] [stackpointer,0]))
        (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE WORD_BYTEREVERSE_NOIBT_SUBROUTINE_SAFE));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof of Windows ABI version.             *)
(* ------------------------------------------------------------------------- *)

let WORD_BYTEREVERSE_NOIBT_WINDOWS_SUBROUTINE_SAFE = time prove
 (`
exists f_events.
    forall e a pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 16),16)
        (word pc,LENGTH word_bytereverse_windows_tmc)
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) word_bytereverse_windows_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 WINDOWS_C_ARGUMENTS [a] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 =
                      f_events pc (word_sub stackpointer (word 16))
                      returnaddress /\
                      memaccess_inbounds e2
                      [word_sub stackpointer (word 16),24]
                      [word_sub stackpointer (word 16),16]))
            (MAYCHANGE [RSP] ,,
             WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes (word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC word_bytereverse_windows_tmc word_bytereverse_tmc
    WORD_BYTEREVERSE_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let WORD_BYTEREVERSE_WINDOWS_SUBROUTINE_SAFE = time prove
 (`
exists f_events.
    forall e a pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 16),16)
        (word pc,LENGTH word_bytereverse_windows_mc)
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) word_bytereverse_windows_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 WINDOWS_C_ARGUMENTS [a] s /\
                 read events s = e)
            (\s.
                 read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                      read events s = APPEND e2 e /\
                      e2 =
                      f_events pc (word_sub stackpointer (word 16))
                      returnaddress /\
                      memaccess_inbounds e2
                      [word_sub stackpointer (word 16),24]
                      [word_sub stackpointer (word 16),16]))
            (MAYCHANGE [RSP] ,,
             WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes (word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE WORD_BYTEREVERSE_NOIBT_WINDOWS_SUBROUTINE_SAFE));;
