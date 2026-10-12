(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Finding maximum of two 64-bit words.                                      *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/word_max.o";;
 ****)

let word_max_mc = define_assert_from_elf "word_max_mc" "x86/generic/word_max.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x89; 0xf8;        (* MOV (% rax) (% rdi) *)
  0x48; 0x39; 0xf7;        (* CMP (% rdi) (% rsi) *)
  0x48; 0x0f; 0x42; 0xc6;  (* CMOVB (% rax) (% rsi) *)
  0xc3                     (* RET *)
];;

let word_max_tmc = define_trimmed "word_max_tmc" word_max_mc;;

let WORD_MAX_EXEC = X86_MK_CORE_EXEC_RULE word_max_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let WORD_MAX_CORRECT = prove
 (`!a b pc.
        ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST word_max_tmc) /\
               read RIP s = word pc /\
               C_ARGUMENTS [a; b] s)
          (\s. read RIP s = word(pc + 0xa) /\
               C_RETURN s = word_umax a b)
          (MAYCHANGE [RIP; RAX] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  MAP_EVERY X_GEN_TAC [`a:int64`; `b:int64`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  X86_SIM_TAC WORD_MAX_EXEC (1--3) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_UMAX] THEN ASM_ARITH_TAC);;

let WORD_MAX_NOIBT_SUBROUTINE_CORRECT = prove
 (`!a b pc stackpointer returnaddress.
        ensures x86
          (\s. bytes_loaded s (word pc) word_max_tmc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [a; b] s)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               C_RETURN s = word_umax a b)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC word_max_tmc WORD_MAX_CORRECT);;

let WORD_MAX_SUBROUTINE_CORRECT = prove
 (`!a b pc stackpointer returnaddress.
        ensures x86
          (\s. bytes_loaded s (word pc) word_max_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [a; b] s)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               C_RETURN s = word_umax a b)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE WORD_MAX_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let word_max_windows_mc = define_from_elf
   "word_max_windows_mc" "x86/generic/word_max.obj";;

let word_max_windows_tmc = define_trimmed "word_max_windows_tmc" word_max_windows_mc;;

let WORD_MAX_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!a b pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 16),16) (word pc,LENGTH word_max_windows_tmc)
        ==> ensures x86
              (\s. bytes_loaded s (word pc) word_max_windows_tmc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [a; b] s)
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   WINDOWS_C_RETURN s = word_umax a b)
              (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC word_max_windows_tmc word_max_tmc
    WORD_MAX_CORRECT);;

let WORD_MAX_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!a b pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 16),16) (word pc,LENGTH word_max_windows_mc)
        ==> ensures x86
              (\s. bytes_loaded s (word pc) word_max_windows_mc /\
                   read RIP s = word pc /\
                   read RSP s = stackpointer /\
                   read (memory :> bytes64 stackpointer) s = returnaddress /\
                   WINDOWS_C_ARGUMENTS [a; b] s)
              (\s. read RIP s = returnaddress /\
                   read RSP s = word_add stackpointer (word 8) /\
                   WINDOWS_C_RETURN s = word_umax a b)
              (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE WORD_MAX_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;


(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* (specs generated with generate_four_variants_of_x86_safety_specs)         *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "word_max" subroutine_signatures)
    WORD_MAX_CORRECT
    WORD_MAX_EXEC;;

let WORD_MAX_SAFE = time prove
 (`exists f_events.
       forall e a b pc.
           ensures x86
           (\s.
                bytes_loaded s (word pc) (BUTLAST word_max_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [a; b] s /\
                read events s = e)
           (\s.
                read RIP s = word (pc + 10) /\
                (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events pc /\
                     memaccess_inbounds e2 [] []))
           (MAYCHANGE [RIP; RAX] ,,
            MAYCHANGE SOME_FLAGS ,,
            MAYCHANGE [events])`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars WORD_MAX_EXEC);;

let WORD_MAX_NOIBT_SUBROUTINE_SAFE = time prove
 (`
exists f_events.
    forall e a b pc stackpointer returnaddress.
        ensures x86
        (\s.
             bytes_loaded s (word pc) word_max_tmc /\
             read RIP s = word pc /\
             read RSP s = stackpointer /\
             read (memory :> bytes64 stackpointer) s = returnaddress /\
             C_ARGUMENTS [a; b] s /\
             read events s = e)
        (\s.
             read RIP s = returnaddress /\
             read RSP s = word_add stackpointer (word 8) /\
             (exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events pc stackpointer returnaddress /\
                  memaccess_inbounds e2 [stackpointer,8] [stackpointer,0]))
        (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC word_max_tmc WORD_MAX_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let WORD_MAX_SUBROUTINE_SAFE = time prove
 (`
exists f_events.
    forall e a b pc stackpointer returnaddress.
        ensures x86
        (\s.
             bytes_loaded s (word pc) word_max_mc /\
             read RIP s = word pc /\
             read RSP s = stackpointer /\
             read (memory :> bytes64 stackpointer) s = returnaddress /\
             C_ARGUMENTS [a; b] s /\
             read events s = e)
        (\s.
             read RIP s = returnaddress /\
             read RSP s = word_add stackpointer (word 8) /\
             (exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events pc stackpointer returnaddress /\
                  memaccess_inbounds e2 [stackpointer,8] [stackpointer,0]))
        (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE WORD_MAX_NOIBT_SUBROUTINE_SAFE));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof of Windows ABI version.             *)
(* ------------------------------------------------------------------------- *)

let WORD_MAX_NOIBT_WINDOWS_SUBROUTINE_SAFE = time prove
 (`
exists f_events.
    forall e a b pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 16),16)
        (word pc,LENGTH word_max_windows_tmc)
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) word_max_windows_tmc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 WINDOWS_C_ARGUMENTS [a; b] s /\
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
  WINDOWS_X86_WRAP_NOSTACK_TAC word_max_windows_tmc word_max_tmc
    WORD_MAX_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let WORD_MAX_WINDOWS_SUBROUTINE_SAFE = time prove
 (`
exists f_events.
    forall e a b pc stackpointer returnaddress.
        nonoverlapping (word_sub stackpointer (word 16),16)
        (word pc,LENGTH word_max_windows_mc)
        ==> ensures x86
            (\s.
                 bytes_loaded s (word pc) word_max_windows_mc /\
                 read RIP s = word pc /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 WINDOWS_C_ARGUMENTS [a; b] s /\
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
  MATCH_ACCEPT_TAC(ADD_IBT_RULE WORD_MAX_NOIBT_WINDOWS_SUBROUTINE_SAFE));;
