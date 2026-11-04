(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Serialization of a polynomial with 12-bit coefficients as bytes.          *)
(* This is the code for mlkem_poly_tobytes from mlkem-native's portable C    *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md).  *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;

(**** print_literal_from_elf
        "x86/mlkem_native/mlkem_native_poly_tobytes_gcc12_O2.o";;
 ****)

let mlkem_native_poly_tobytes_gcc12_O2_mc = define_assert_from_elf
  "mlkem_native_poly_tobytes_gcc12_O2_mc"
  "x86/mlkem_native/mlkem_native_poly_tobytes_gcc12_O2.o"
[
  0x4c; 0x8d; 0x87; 0x80; 0x01; 0x00; 0x00;
                           (* LEA (% r8) (%% (rdi,384)) *)
  0x66; 0x0f; 0x1f; 0x84; 0x00; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Word (%%% (rax,0,rax))) *)
  0x0f; 0xb7; 0x46; 0x02;  (* MOVZX (% eax) (Memop Word (%% (rsi,2))) *)
  0x0f; 0xb7; 0x16;        (* MOVZX (% edx) (Memop Word (%% (rsi,0))) *)
  0x48; 0x83; 0xc7; 0x03;  (* ADD (% rdi) (Imm8 (word 3)) *)
  0x48; 0x83; 0xc6; 0x04;  (* ADD (% rsi) (Imm8 (word 4)) *)
  0x89; 0xc1;              (* MOV (% ecx) (% eax) *)
  0x88; 0x57; 0xfd;        (* MOV (Memop Byte (%% (rdi,18446744073709551613)))
                                  (% dl) *)
  0x66; 0xc1; 0xea; 0x08;  (* SHR (% dx) (Imm8 (word 8)) *)
  0xc1; 0xe1; 0x04;        (* SHL (% ecx) (Imm8 (word 4)) *)
  0x66; 0xc1; 0xe8; 0x04;  (* SHR (% ax) (Imm8 (word 4)) *)
  0x09; 0xca;              (* OR (% edx) (% ecx) *)
  0x88; 0x47; 0xff;        (* MOV (Memop Byte (%% (rdi,18446744073709551615)))
                                  (% al) *)
  0x88; 0x57; 0xfe;        (* MOV (Memop Byte (%% (rdi,18446744073709551614)))
                                  (% dl) *)
  0x49; 0x39; 0xf8;        (* CMP (% r8) (% rdi) *)
  0x75; 0xd4;              (* JNE (Imm8 (word 212)) *)
  0xc3                     (* RET *)
];;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC =
  X86_MK_EXEC_RULE mlkem_native_poly_tobytes_gcc12_O2_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(*                                                                           *)
(* Unlike the hand-written kernel mlkem_tobytes, the C code relies on the    *)
(* coefficients being < 2^12, as stated in its contract (in fact requiring   *)
(* them to be < 3329), so this is an additional assumption here.             *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_CORRECT = prove
 (`!r a (l:int16 list) pc.
        ALL (nonoverlapping (r,384)) [(word pc,0x3d); (a,512)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_poly_tobytes_gcc12_O2_mc /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [r;a] s /\
                  read (memory :> bytes(a,512)) s = num_of_wordlist l)
             (\s. read RIP s = word(pc + 0x3c) /\
                  (LENGTH l = 256 /\ ALL (\x. val x < 4096) l
                   ==> read(memory :> bytes(r,384)) s =
                       num_of_wordlist (MAP word_zx l:(12 word)list)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,384)])`,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `l:int16 list`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `128` `pc + 0x10` `pc + 0x37`
   `\i s. read RDI s = word_add r (word(3 * i)) /\
          read RSI s = word_add a (word(4 * i)) /\
          read R8 s = word_add r (word 384) /\
          read (memory :> bytes(a,512)) s = num_of_wordlist(l:int16 list) /\
          (LENGTH l = 256 /\ ALL (\x. val x < 4096) l
           ==> read (memory :> bytes(r,3 * i)) s =
               num_of_wordlist
                (MAP word_zx (SUB_LIST(0,2 * i) l):(12 word)list))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization of the end pointer ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_LIST_CLAUSES; MAP;
                num_of_wordlist; READ_MEMORY_BYTES_TRIVIAL];

    (*** The loop body, processing two coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ASM_CASES_TAC `LENGTH(l:int16 list) = 256 /\ ALL (\x. val x < 4096) l`
    THENL
     [ALL_TAC;
      X86_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC (1--12) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `3 * (i + 1) = 3 * i + 3`;
                  ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
      CONV_TAC WORD_RULE] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`a:int64`; `l:int16 list`; `256`; `2 * i`; `s0:x86state`]
       READ_MEMORY_BYTES16_NUM_OF_WORDLIST) THEN
    MP_TAC(SPECL [`a:int64`; `l:int16 list`; `256`; `2 * i + 1`;
                  `s0:x86state`]
       READ_MEMORY_BYTES16_NUM_OF_WORDLIST) THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 * 256 = 512`;
                    ARITH_RULE `2 * (2 * i + 1) = 4 * i + 2`;
                    ARITH_RULE `2 * 2 * i = 4 * i`] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < 128 ==> 2 * i < 256 /\ 2 * i + 1 < 256`] THEN
    REPEAT STRIP_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC (1--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `3 * (i + 1) = 3 * i + 3`;
                  ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC]) THEN

    (*** Split the new bytes and list elements off and match them up ***)

    REWRITE_TAC[ARITH_RULE `3 * (i + 1) = ((3 * i + 1) + 1) + 1`;
                ARITH_RULE `2 * (i + 1) = 2 * i + 2`] THEN
    REWRITE_TAC[READ_MEMORY_BYTES_SNOC] THEN
    REWRITE_TAC[ARITH_RULE `(3 * i + 1) + 1 = 3 * i + 2`] THEN
    REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[SUB_LIST_0_SNOC2;
                 ARITH_RULE `i < 128 ==> 2 * i + 2 <= 256`] THEN
    REWRITE_TAC[MAP_APPEND; MAP; NUM_OF_WORDLIST_APPEND; LENGTH_MAP;
                LENGTH_SUB_LIST; num_of_wordlist] THEN
    SUBGOAL_THEN `val(EL (2 * i) (l:int16 list)) < 4096` MP_TAC THENL
     [UNDISCH_TAC `ALL (\x. val x < 4096) (l:int16 list)` THEN
      REWRITE_TAC[GSYM ALL_EL] THEN DISCH_THEN(MP_TAC o SPEC `2 * i`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[SUB_0] THEN CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
    ASM_SIMP_TAC[ARITH_RULE `i < 128 ==> MIN (2 * i) 256 = 2 * i`] THEN
    REWRITE_TAC[ARITH_RULE `8 * 3 * i = 24 * i`;
                ARITH_RULE `12 * 2 * i = 24 * i`;
                ARITH_RULE `8 * (3 * i + 1) = 24 * i + 8`;
                ARITH_RULE `8 * (3 * i + 2) = 24 * i + 16`; EXP_ADD] THEN
    DISCH_TAC THEN MATCH_MP_TAC(NUM_RING
     `v0 + 2 EXP 8 * v1 + 2 EXP 16 * v2 = w0 + 2 EXP 12 * w1
      ==> ((n + a * v0) + (a * 2 EXP 8) * v1) + (a * 2 EXP 16) * v2 =
          n + a * (w0 + 2 EXP 12 * (w1 + 2 EXP 12 * 0))`) THEN

    (*** The bit-level packing of two coefficients into three bytes ***)

    MLKEM_NATIVE_WORD_SIMP_TAC THEN
    UNDISCH_TAC `val(EL (2 * i) (l:int16 list)) < 4096` THEN
    SPEC_TAC(`EL (2 * i + 1) (l:int16 list)`, `t1:int16`) THEN
    SPEC_TAC(`EL (2 * i) (l:int16 list)`, `t0:int16`) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN BITBLAST_TAC;

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add r (word 384))
                     (word_add r (word (3 * i))):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add a x) (word_add a y) = word_sub x y`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 128 ==> 3 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 128` THEN ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MP th) THEN
                         STRIP_ASSUME_TAC th) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check
     (fun th -> concl th = `LENGTH(l:int16 list) = 256`)) THEN
    REWRITE_TAC[SUB_LIST_LENGTH]]);;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SUBROUTINE_CORRECT = prove
 (`!r a (l:int16 list) pc stackpointer returnaddress.
        ALL (nonoverlapping (r,384))
            [(word pc,0x3d); (a,512); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_poly_tobytes_gcc12_O2_mc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r;a] s /\
                  read (memory :> bytes(a,512)) s = num_of_wordlist l)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (LENGTH l = 256 /\ ALL (\x. val x < 4096) l
                   ==> read(memory :> bytes(r,384)) s =
                       num_of_wordlist (MAP word_zx l:(12 word)list)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,384)])`,
  X86_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_CORRECT);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

(*** The C signature is the same as that of mlkem_tobytes ***)

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_tobytes" subroutine_signatures)
    MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_CORRECT
    MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SAFE = time prove
 (`exists f_events.
       forall e r a pc.
           ALL (nonoverlapping (r,384)) [word pc,0x3d; a,512]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_poly_tobytes_gcc12_O2_mc /\
                    read RIP s = word pc /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = word (pc + 0x3c) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc /\
                         memaccess_inbounds e2 [a,512; r,384] [r,384]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,384)])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num).
      APPEND
        (f_ev_epil a r pc)
        (APPEND
          (ENUMERATEL 128 (\i. f_ev_loop a r pc i))
          (f_ev_prol a r pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `128` `pc + 0x10` `pc + 0x3c`
    `\i s. read RDI s = word_add r (word(3 * i)) /\
           read RSI s = word_add a (word(4 * i)) /\
           read R8 s = word_add r (word 384)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC (1--2) THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC (1--0) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC (1--14) THEN
  SUBGOAL_THEN
   `~(val(word_add r (word 384):int64) =
      val(word_add (word_add r (word (3 * i))) (word 3):int64)) <=>
    i + 1 < 128`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_EQ; GSYM WORD_ADD_ASSOC; WORD_ADD_LCANCEL_EQ] THEN
    REWRITE_TAC[GSYM WORD_ADD; WORD_EQ; DIMINDEX_64; CONG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 128 ==> 3 * i + 3 < 18446744073709551616`] THEN
    UNDISCH_TAC `i < 128` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `3 * (i + 1) = 3 * i + 3`;
                ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc stackpointer returnaddress.
           ALL (nonoverlapping (r,384))
               [word pc,0x3d; a,512; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_poly_tobytes_gcc12_O2_mc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc stackpointer returnaddress /\
                         memaccess_inbounds e2
                          [a,512; r,384; stackpointer,8] [r,384]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,384)])`,
  X86_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* The same code in the whole image, at address 0x3180 (see                  *)
(* mlkem_native_libmlkem_gcc12_O2.ml).                                       *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_CODE_RULE mlkem_native_poly_tobytes_gcc12_O2_mc
    0x3180 [];;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!r a (l:int16 list) pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        ALL (nonoverlapping (r,384))
            [(word pc,0x82a0); (a,512); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + 0x3180) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r;a] s /\
                  read (memory :> bytes(a,512)) s = num_of_wordlist l)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (LENGTH l = 256 /\ ALL (\x. val x < 4096) l
                   ==> read(memory :> bytes(r,384)) s =
                       num_of_wordlist (MAP word_zx l:(12 word)list)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,384)])`,
  MLKEM_NATIVE_IMAGE_TAC
   (INST [`pc + 0x3180`,`pc:num`]
     (SPEC_ALL MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SUBROUTINE_CORRECT))
   [MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IN_IMAGE]);;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (`exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,384)) [word pc,0x82a0; a,512; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x3180) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc stackpointer returnaddress /\
                         memaccess_inbounds e2
                          [a,512; r,384; stackpointer,8] [r,384]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,384)])`,
  MLKEM_NATIVE_IMAGE_SAFE_TAC
   MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SUBROUTINE_SAFE
   [`pc + 0x3180`,`pc:num`]
   [MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IN_IMAGE]);;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, as for       *)
(* mlkem_poly_reduce. The loop body is simulated in both cases of the        *)
(* hypothesis on the list, first in the case where it does not hold, and in  *)
(* the other case its events are then those already given, so they are       *)
(* matched directly by TOBYTES_FULL_DISCHARGE_AGAIN_TAC rather than by       *)
(* instantiation.                                                            *)
(* ------------------------------------------------------------------------- *)

let TOBYTES_FULL_DISCHARGE_AGAIN_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W(fun (asl,w) ->
    (if is_conj w then
      CONJ_TAC THENL
       [FULL_UNIFY_F_EVENTS_TAC ORELSE
        (CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
         REWRITE_TAC[ENUMERATEL_ADD1; APPEND; APPEND_NIL;
                     GSYM APPEND_ASSOC] THEN
         CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
         REWRITE_TAC[APPEND; APPEND_NIL; GSYM APPEND_ASSOC] THEN NO_TAC);
        ALL_TAC]
     else ALL_TAC) THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

let TOBYTES_FULL_TEST_TAC =
  SUBGOAL_THEN
   `~(val(word_sub (word_add r (word 384))
                   (word_add (word_add r (word (3 * i))) (word 3)):int64) =
      0) <=>
    i + 1 < 128`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[WORD_RULE
     `word_sub (word_add a x) (word_add (word_add a y) z):int64 =
      word_sub x (word_add y z)`] THEN
    REWRITE_TAC[VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 128 ==> 3 * i + 3 < 18446744073709551616`] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC];;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_FULL = time prove
 (`exists f_events.
       forall e r a (l:int16 list) pc.
           ALL (nonoverlapping (r,384)) [word pc,0x3d; a,512]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_poly_tobytes_gcc12_O2_mc /\
                    read RIP s = word pc /\
                    C_ARGUMENTS [r; a] s /\
                    read (memory :> bytes(a,512)) s = num_of_wordlist l /\
                    read events s = e)
               (\s. read RIP s = word (pc + 0x3c) /\
                    (LENGTH l = 256 /\ ALL (\x. val x < 4096) l
                     ==> read(memory :> bytes(r,384)) s =
                         num_of_wordlist (MAP word_zx l:(12 word)list)) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc /\
                         memaccess_inbounds e2 [a,512; r,384] [r,384]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,384)])`,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num).
      APPEND
        (f_ev_epil a r pc)
        (APPEND
          (ENUMERATEL 128 (\i. f_ev_loop a r pc i))
          (f_ev_prol a r pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `l:int16 list`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `128` `pc + 0x10` `pc + 0x3c`
   `\i s. read RDI s = word_add r (word(3 * i)) /\
          read RSI s = word_add a (word(4 * i)) /\
          read R8 s = word_add r (word 384) /\
          read (memory :> bytes(a,512)) s = num_of_wordlist(l:int16 list) /\
          (LENGTH l = 256 /\ ALL (\x. val x < 4096) l
           ==> read (memory :> bytes(r,3 * i)) s =
               num_of_wordlist
                (MAP word_zx (SUB_LIST(0,2 * i) l):(12 word)list))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization of the end pointer ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; SUB_LIST_CLAUSES; MAP;
                num_of_wordlist; READ_MEMORY_BYTES_TRIVIAL] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body with the loop test, in both cases ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ASM_CASES_TAC `LENGTH(l:int16 list) = 256 /\ ALL (\x. val x < 4096) l`
    THENL
     [ALL_TAC;
      X86_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC (1--14) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      TOBYTES_FULL_TEST_TAC THEN
      CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
      REPEAT(CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `3 * (i + 1) = 3 * i + 3`;
                    ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
        CONV_TAC WORD_RULE;
        ALL_TAC]) THEN
      DISCHARGE_SAFETY_PROPERTY_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`a:int64`; `l:int16 list`; `256`; `2 * i`; `s0:x86state`]
       READ_MEMORY_BYTES16_NUM_OF_WORDLIST) THEN
    MP_TAC(SPECL [`a:int64`; `l:int16 list`; `256`; `2 * i + 1`;
                  `s0:x86state`]
       READ_MEMORY_BYTES16_NUM_OF_WORDLIST) THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 * 256 = 512`;
                    ARITH_RULE `2 * (2 * i + 1) = 4 * i + 2`;
                    ARITH_RULE `2 * 2 * i = 4 * i`] THEN
    ASM_SIMP_TAC[ARITH_RULE `i < 128 ==> 2 * i < 256 /\ 2 * i + 1 < 256`] THEN
    REPEAT STRIP_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC (1--14) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    TOBYTES_FULL_TEST_TAC THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT(CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `3 * (i + 1) = 3 * i + 3`;
                  ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC]) THEN
    CONJ_TAC THENL [ALL_TAC; TOBYTES_FULL_DISCHARGE_AGAIN_TAC] THEN

    (*** Split the new bytes and list elements off and match them up ***)

    REWRITE_TAC[ARITH_RULE `3 * (i + 1) = ((3 * i + 1) + 1) + 1`;
                ARITH_RULE `2 * (i + 1) = 2 * i + 2`] THEN
    REWRITE_TAC[READ_MEMORY_BYTES_SNOC] THEN
    REWRITE_TAC[ARITH_RULE `(3 * i + 1) + 1 = 3 * i + 2`] THEN
    REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[SUB_LIST_0_SNOC2;
                 ARITH_RULE `i < 128 ==> 2 * i + 2 <= 256`] THEN
    REWRITE_TAC[MAP_APPEND; MAP; NUM_OF_WORDLIST_APPEND; LENGTH_MAP;
                LENGTH_SUB_LIST; num_of_wordlist] THEN
    SUBGOAL_THEN `val(EL (2 * i) (l:int16 list)) < 4096` MP_TAC THENL
     [UNDISCH_TAC `ALL (\x. val x < 4096) (l:int16 list)` THEN
      REWRITE_TAC[GSYM ALL_EL] THEN DISCH_THEN(MP_TAC o SPEC `2 * i`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      UNDISCH_TAC `i < 128` THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[SUB_0] THEN CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
    ASM_SIMP_TAC[ARITH_RULE `i < 128 ==> MIN (2 * i) 256 = 2 * i`] THEN
    REWRITE_TAC[ARITH_RULE `8 * 3 * i = 24 * i`;
                ARITH_RULE `12 * 2 * i = 24 * i`;
                ARITH_RULE `8 * (3 * i + 1) = 24 * i + 8`;
                ARITH_RULE `8 * (3 * i + 2) = 24 * i + 16`; EXP_ADD] THEN
    DISCH_TAC THEN MATCH_MP_TAC(NUM_RING
     `v0 + 2 EXP 8 * v1 + 2 EXP 16 * v2 = w0 + 2 EXP 12 * w1
      ==> ((n + a * v0) + (a * 2 EXP 8) * v1) + (a * 2 EXP 16) * v2 =
          n + a * (w0 + 2 EXP 12 * (w1 + 2 EXP 12 * 0))`) THEN

    (*** The bit-level packing of two coefficients into three bytes ***)

    MLKEM_NATIVE_WORD_SIMP_TAC THEN
    UNDISCH_TAC `val(EL (2 * i) (l:int16 list)) < 4096` THEN
    SPEC_TAC(`EL (2 * i + 1) (l:int16 list)`, `t1:int16`) THEN
    SPEC_TAC(`EL (2 * i) (l:int16 list)`, `t0:int16`) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN BITBLAST_TAC;

    (*** The loop exit ***)

    REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; DISCHARGE_SAFETY_PROPERTY_TAC] THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MP th) THEN
                         STRIP_ASSUME_TAC th) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check
     (fun th -> concl th = `LENGTH(l:int16 list) = 256`)) THEN
    REWRITE_TAC[SUB_LIST_LENGTH]]);;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SUBROUTINE_FULL = time prove
 (`exists f_events.
       forall e r a (l:int16 list) pc stackpointer returnaddress.
           ALL (nonoverlapping (r,384))
               [word pc,0x3d; a,512; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_poly_tobytes_gcc12_O2_mc /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read (memory :> bytes(a,512)) s = num_of_wordlist l /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (LENGTH l = 256 /\ ALL (\x. val x < 4096) l
                     ==> read(memory :> bytes(r,384)) s =
                         num_of_wordlist (MAP word_zx l:(12 word)list)) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc stackpointer returnaddress /\
                         memaccess_inbounds e2
                          [a,512; r,384; stackpointer,8] [r,384]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,384)])`,
  X86_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_FULL THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (`exists f_events.
       forall e r a (l:int16 list) pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,384)) [word pc,0x82a0; a,512; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + 0x3180) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read (memory :> bytes(a,512)) s = num_of_wordlist l /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (LENGTH l = 256 /\ ALL (\x. val x < 4096) l
                     ==> read(memory :> bytes(r,384)) s =
                         num_of_wordlist (MAP word_zx l:(12 word)list)) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc stackpointer returnaddress /\
                         memaccess_inbounds e2
                          [a,512; r,384; stackpointer,8] [r,384]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,384)])`,
  MLKEM_NATIVE_IMAGE_SAFE_TAC
   MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SUBROUTINE_FULL
   [`pc + 0x3180`,`pc:num`]
   [MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IN_IMAGE]);;
