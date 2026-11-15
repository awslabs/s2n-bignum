(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Serialization of a polynomial with 12-bit coefficients as bytes.          *)
(* This is the code for mlkem_poly_tobytes from mlkem-native's portable C    *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md).  *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/layout.ml";;

(* Names for the labels of this transcription, whose code is at pc.          *)

install_layout (layout_copies
 ["poly_tobytes","mlkem_poly_tobytes"]);;

(**** print_literal_from_elf
        "x86/mlkem_native/gcc12_O2/poly_tobytes.o";;
 ****)

let mlkem_native_poly_tobytes_gcc12_O2_mc = define_assert_from_elf
  "mlkem_native_poly_tobytes_gcc12_O2_mc"
  "x86/mlkem_native/gcc12_O2/poly_tobytes.o"
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

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_CORRECT_STMT =
  `!r a (l:int16 list) pc.
        ALL (nonoverlapping (r,384)) [(word pc,poly_tobytes_size); (a,512)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_poly_tobytes_gcc12_O2_mc /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [r;a] s /\
                  read (memory :> bytes(a,512)) s = num_of_wordlist l)
             (\s. read RIP s = word(pc + poly_tobytes_ret) /\
                  (LENGTH l = 256 /\ ALL (\x. val x < 4096) l
                   ==> read(memory :> bytes(r,384)) s =
                       num_of_wordlist (MAP word_zx l:(12 word)list)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,384)])`;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_CORRECT_STMT;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SUBROUTINE_CORRECT_STMT =
  `!r a (l:int16 list) pc stackpointer returnaddress.
        ALL (nonoverlapping (r,384))
            [(word pc,poly_tobytes_size); (a,512); (stackpointer,8)]
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
              MAYCHANGE [memory :> bytes(r,384)])`;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SUBROUTINE_CORRECT_STMT;;

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

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SAFE_STMT =
  `exists f_events.
       forall e r a pc.
           ALL (nonoverlapping (r,384)) [word pc,poly_tobytes_size; a,512]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_poly_tobytes_gcc12_O2_mc /\
                    read RIP s = word pc /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = word (pc + poly_tobytes_ret) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc /\
                         memaccess_inbounds e2 [a,512; r,384] [r,384]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,384)])`;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SAFE =
  assume_spec MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SAFE_STMT;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc stackpointer returnaddress.
           ALL (nonoverlapping (r,384))
               [word pc,poly_tobytes_size; a,512; stackpointer,8]
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
                MAYCHANGE [memory :> bytes(r,384)])`;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* The same code in the whole image (see libmlkem.ml).                       *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_CODE_RULE mlkem_native_poly_tobytes_gcc12_O2_mc
    (layout "mlkem_poly_tobytes") [];;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a (l:int16 list) pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        ALL (nonoverlapping (r,384))
            [(word pc,libmlkem_size); (a,512); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + mlkem_poly_tobytes) /\
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
              MAYCHANGE [memory :> bytes(r,384)])`;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,384)) [word pc,libmlkem_size; a,512; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_tobytes) /\
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
                MAYCHANGE [memory :> bytes(r,384)])`;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

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

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_FULL_STMT =
  `exists f_events.
       forall e r a (l:int16 list) pc.
           ALL (nonoverlapping (r,384)) [word pc,poly_tobytes_size; a,512]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_poly_tobytes_gcc12_O2_mc /\
                    read RIP s = word pc /\
                    C_ARGUMENTS [r; a] s /\
                    read (memory :> bytes(a,512)) s = num_of_wordlist l /\
                    read events s = e)
               (\s. read RIP s = word (pc + poly_tobytes_ret) /\
                    (LENGTH l = 256 /\ ALL (\x. val x < 4096) l
                     ==> read(memory :> bytes(r,384)) s =
                         num_of_wordlist (MAP word_zx l:(12 word)list)) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc /\
                         memaccess_inbounds e2 [a,512; r,384] [r,384]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,384)])`;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_FULL =
  assume_spec MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_FULL_STMT;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SUBROUTINE_FULL_STMT =
  `exists f_events.
       forall e r a (l:int16 list) pc stackpointer returnaddress.
           ALL (nonoverlapping (r,384))
               [word pc,poly_tobytes_size; a,512; stackpointer,8]
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
                MAYCHANGE [memory :> bytes(r,384)])`;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_SUBROUTINE_FULL_STMT;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
       forall e r a (l:int16 list) pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,384)) [word pc,libmlkem_size; a,512; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_tobytes) /\
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
                MAYCHANGE [memory :> bytes(r,384)])`;;

let MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_POLY_TOBYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;
