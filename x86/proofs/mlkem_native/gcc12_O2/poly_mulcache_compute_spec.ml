(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Computation of the multiplication cache of a polynomial.                  *)
(* This is the code for mlkem_poly_mulcache_compute from mlkem-native's      *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md).                                                  *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/base.ml";;
needs "x86/proofs/utils/mlkem_native.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/layout.ml";;

(* Names for the labels of this transcription, whose code is at pc.          *)

install_layout (layout_copies
 ["poly_mulcache_compute","mlkem_poly_mulcache_compute"]);;

(**** print_literal_relocs_from_elf
        "x86/mlkem_native/gcc12_O2/poly_mulcache_compute.o";;
 ****)

let mlkem_native_poly_mulcache_compute_gcc12_O2_mc,
    mlkem_native_poly_mulcache_compute_gcc12_O2_data =
  define_assert_relocs_from_elf
    ~map_symbol_name:(function
      | "WHOLE_READONLY" | "mlk_zetas" -> "mlk_zetas_data"
      | s -> failwith ("unknown symbol: " ^ s))
    "mlkem_native_poly_mulcache_compute_gcc12_O2_mc"
    "x86/mlkem_native/gcc12_O2/poly_mulcache_compute.o"
(fun b ADDR -> [b[
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x4c; 0x8d; 0x05]; ADDR ("mlk_zetas_data",(124)); b[
                           (* LEA (% r8) (Riprel (word_sx (iword
                                  (&mlk_zetas_data - (&pc + -- &119))))) *)
  0x0f; 0x1f; 0x80; 0x00; 0x00; 0x00; 0x00;
                           (* NOP_N (Memop Doubleword (%% (rax,0))) *)
  0x41; 0x0f; 0xbf; 0x04; 0x08;
                           (* MOVSX (% eax) (Memop Word (%%% (r8,0,rcx))) *)
  0x44; 0x0f; 0xbf; 0x4c; 0x8e; 0x02;
                           (* MOVSX (% r9d) (Memop Word (%%%% (rsi,2,rcx,&2)))
                                    *)
  0x44; 0x0f; 0xaf; 0xc8;  (* IMUL (% r9d) (% eax) *)
  0x89; 0xc2;              (* MOV (% edx) (% eax) *)
  0xf7; 0xda;              (* NEG (% edx) *)
  0x0f; 0xbf; 0xd2;        (* MOVSX (% edx) (% dx) *)
  0x66; 0x41; 0x69; 0xc1; 0x01; 0xf3;
                           (* IMUL3 (% ax) (% r9w,Imm16 (word 62209)) *)
  0x98;                    (* MOVSX (% eax) (% ax) *)
  0x69; 0xc0; 0xff; 0xf2; 0xff; 0xff;
                           (* IMUL3 (% eax) (% eax,Imm32 (word 4294963967)) *)
  0x44; 0x01; 0xc8;        (* ADD (% eax) (% r9d) *)
  0xc1; 0xf8; 0x10;        (* SAR (% eax) (Imm8 (word 16)) *)
  0x66; 0x89; 0x04; 0x4f;  (* MOV (Memop Word (%%% (rdi,1,rcx))) (% ax) *)
  0x0f; 0xbf; 0x44; 0x8e; 0x06;
                           (* MOVSX (% eax) (Memop Word (%%%% (rsi,2,rcx,&6)))
                                    *)
  0x0f; 0xaf; 0xd0;        (* IMUL (% edx) (% eax) *)
  0x66; 0x69; 0xc2; 0x01; 0xf3;
                           (* IMUL3 (% ax) (% dx,Imm16 (word 62209)) *)
  0x98;                    (* MOVSX (% eax) (% ax) *)
  0x69; 0xc0; 0xff; 0xf2; 0xff; 0xff;
                           (* IMUL3 (% eax) (% eax,Imm32 (word 4294963967)) *)
  0x01; 0xd0;              (* ADD (% eax) (% edx) *)
  0xc1; 0xf8; 0x10;        (* SAR (% eax) (Imm8 (word 16)) *)
  0x66; 0x89; 0x44; 0x4f; 0x02;
                           (* MOV (Memop Word (%%%% (rdi,1,rcx,&2))) (% ax) *)
  0x48; 0x83; 0xc1; 0x02;  (* ADD (% rcx) (Imm8 (word 2)) *)
  0x48; 0x81; 0xf9; 0x80; 0x00; 0x00; 0x00;
                           (* CMP (% rcx) (Imm32 (word 128)) *)
  0x75; 0xa8;              (* JNE (Imm8 (word 168)) *)
  0xc3                     (* RET *)
]]);;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC =
  X86_MK_EXEC_RULE mlkem_native_poly_mulcache_compute_gcc12_O2_mc;;

(* ------------------------------------------------------------------------- *)
(* Properties of the zetas (see utils/mlkem_native.ml for the table).        *)
(* ------------------------------------------------------------------------- *)

(*** The zetas used for the mulcache are those in the second half ***)

let MLK_ZETAS_MULCACHE_STMT =
  `!i. i < 64
       ==> abs(EL (64 + i) mlk_zetas) <= &1664 /\
           (&169 * EL (64 + i) mlk_zetas ==
            &17 pow (2 * bitreverse7 (2 * i) + 1)) (mod &3329) /\
           (&169 * --(EL (64 + i) mlk_zetas) ==
            &17 pow (2 * bitreverse7 (2 * i + 1) + 1)) (mod &3329)`;;

let MLK_ZETAS_MULCACHE =
  assume_spec MLK_ZETAS_MULCACHE_STMT;;

let MLK_ZETAS_MULCACHE_IVAL_STMT =
  `!i. i < 64
       ==> ival(iword(EL (64 + i) mlk_zetas):int16) = EL (64 + i) mlk_zetas /\
           abs(ival(iword(EL (64 + i) mlk_zetas):int16)) <= &1664 /\
           (&169 * ival(iword(EL (64 + i) mlk_zetas):int16) ==
            &17 pow (2 * bitreverse7 (2 * i) + 1)) (mod &3329) /\
           (&169 * --ival(iword(EL (64 + i) mlk_zetas):int16) ==
            &17 pow (2 * bitreverse7 (2 * i + 1) + 1)) (mod &3329)`;;

let MLK_ZETAS_MULCACHE_IVAL =
  assume_spec MLK_ZETAS_MULCACHE_IVAL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Some lemmas, tactics etc.                                                 *)
(* ------------------------------------------------------------------------- *)

let WORD_ZX_NEG_SX_STMT =
  `!z:int16. word_zx(word_neg (word_sx z:int32)):int16 = word_neg z`;;

let WORD_ZX_NEG_SX =
  assume_spec WORD_ZX_NEG_SX_STMT;;

let CONG_MONT_ZETA = INTEGER_RULE
 `!n a z p x r:int. (r == a * (x * z)) (mod n) /\ (a * z == p) (mod n)
                    ==> (r == x * p) (mod n)`;;

let CONG_MONT_ZETA_ALT = INTEGER_RULE
 `!n a z p x r:int. (r == a * (z * x)) (mod n) /\ (a * z == p) (mod n)
                    ==> (r == x * p) (mod n)`;;

(*** Prove the result for one output coefficient ***)

let MULCACHE_OUTPUT_TAC =
  UNDISCH_THEN `i < 64` (fun th ->
    ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(MATCH_MP MLK_ZETAS_MULCACHE_IVAL th)) THEN
  ASSUM_LIST(fun ths -> W(fun (asl,w) ->
    let tm = rand(rand(lhand(rator(lhand w)))) in
    let th1 = WEAKEN_INTCONG_RULE (num 3329) (GEN_CONGBOUND_RULE ths tm) in
    let th2 = MATCH_MP CONGBOUND_MONTRED_SCALAR th1 in
    let th3 = CONV_RULE(ONCE_DEPTH_CONV INVERSE_MOD_CONV)
               (MP th2 (EQT_ELIM(INT_REDUCE_CONV(lhand(concl th2))))) in
    let cth,bth = CONJ_PAIR th3 in
    let prod = rand(rand(rator(concl cth))) in
    let ZETA_TAC lemma zz =
      MATCH_MP_TAC lemma THEN MAP_EVERY EXISTS_TAC [`&169:int`; zz] THEN
      CONJ_TAC THENL [ACCEPT_TAC cth; ASM_REWRITE_TAC[]] in
    CONJ_TAC THENL
     [REWRITE_TAC[mulcache; o_THM; INT_CONG_RREM;
                  ARITH_RULE `2 * 2 * i + 1 = 4 * i + 1`;
                  ARITH_RULE `2 * (2 * i + 1) + 1 = 4 * i + 3`] THEN
      (ZETA_TAC CONG_MONT_ZETA (rand prod) ORELSE
       ZETA_TAC CONG_MONT_ZETA_ALT (lhand prod));
      MP_TAC bth THEN CONV_TAC(LAND_CONV INT_REDUCE_CONV) THEN
      INT_ARITH_TAC]));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_CORRECT_STMT =
  `!dst src zetas x pc.
    riprel32_within_bounds (zetas + 128) (pc + 9) /\
    ALL (nonoverlapping (dst,256))
        [(word pc,poly_mulcache_compute_size); (src,512); (word zetas,256)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc)
             (mlkem_native_poly_mulcache_compute_gcc12_O2_mc pc zetas) /\
           read RIP s = word pc /\
           C_ARGUMENTS [dst; src] s /\
           bytes_loaded s (word zetas) mlk_zetas_data /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add src (word (2 * i)))) s =
                    x i))
      (\s. read RIP s = word(pc + poly_mulcache_compute_ret) /\
           !i. i < 128
               ==> let z_i = read(memory :> bytes16
                                (word_add dst (word (2 * i)))) s in
                   (ival z_i == (mulcache (ival o x)) i) (mod &3329) /\
                   abs(ival z_i) <= &3328)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(dst,256)])`;;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_CORRECT_STMT;;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SUBROUTINE_CORRECT_STMT =
  `!dst src zetas x pc stackpointer returnaddress.
    riprel32_within_bounds (zetas + 128) (pc + 9) /\
    ALL (nonoverlapping (dst,256))
        [(word pc,poly_mulcache_compute_size); (src,512); (word zetas,256); (stackpointer,8)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc)
             (mlkem_native_poly_mulcache_compute_gcc12_O2_mc pc zetas) /\
           read RIP s = word pc /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [dst; src] s /\
           bytes_loaded s (word zetas) mlk_zetas_data /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add src (word (2 * i)))) s =
                    x i))
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           !i. i < 128
               ==> let z_i = read(memory :> bytes16
                                (word_add dst (word (2 * i)))) s in
                   (ival z_i == (mulcache (ival o x)) i) (mod &3329) /\
                   abs(ival z_i) <= &3328)
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(dst,256)])`;;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

(*** Unlike mlkem_mulcache_compute, this has just two arguments, and the ***)
(*** table of zetas is a read-only object.                               ***)

let mlkem_native_poly_mulcache_compute_signature =
  ([("x", "int16_t[static 128]", "false");
    ("a", "int16_t[static 256]", "true")],
   "void",
   [("a", "256", 2)],
   [("x", "128", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word zetas:int64`,`256`]
    ~keep_maychanges:true
    mlkem_native_poly_mulcache_compute_signature
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_CORRECT
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC;;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SAFE_STMT =
  `exists f_events.
       forall e dst src zetas pc.
           riprel32_within_bounds (zetas + 128) (pc + 9) /\
           ALL (nonoverlapping (dst,256))
           [word pc,poly_mulcache_compute_size; src,512; word zetas,256]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                     (mlkem_native_poly_mulcache_compute_gcc12_O2_mc
                        pc zetas) /\
                    read RIP s = word pc /\
                    bytes_loaded s (word zetas) mlk_zetas_data /\
                    C_ARGUMENTS [dst; src] s /\
                    read events s = e)
               (\s. read RIP s = word (pc + poly_mulcache_compute_ret) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events src dst zetas pc /\
                         memaccess_inbounds e2
                          [src,512; dst,256; word zetas,256]
                          [dst,256]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(dst,256)])`;;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SAFE =
  assume_spec MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SAFE_STMT;;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e dst src zetas pc stackpointer returnaddress.
           riprel32_within_bounds (zetas + 128) (pc + 9) /\
           ALL (nonoverlapping (dst,256))
           [word pc,poly_mulcache_compute_size; src,512; word zetas,256; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                     (mlkem_native_poly_mulcache_compute_gcc12_O2_mc
                        pc zetas) /\
                    read RIP s = word pc /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    bytes_loaded s (word zetas) mlk_zetas_data /\
                    C_ARGUMENTS [dst; src] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events src dst zetas pc stackpointer
                                       returnaddress /\
                         memaccess_inbounds e2
                          [src,512; dst,256; word zetas,256; stackpointer,8]
                          [dst,256]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(dst,256)])`;;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* The same code in the whole image, with the table of zetas (see            *)
(* libmlkem.ml).                                                             *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_CODE_RULE mlkem_native_poly_mulcache_compute_gcc12_O2_mc
    (layout "mlkem_poly_mulcache_compute") [layout "rodata_mlk_zetas"];;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_ZETAS_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_DATA_RULE mlk_zetas_data (layout "rodata_mlk_zetas");;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!dst src x pc stackpointer returnaddress.
    aligned 16 (word pc:int64) /\
    ALL (nonoverlapping (dst,256))
        [(word pc,libmlkem_size); (src,512); (stackpointer,8)]
    ==> ensures x86
      (\s. bytes_loaded s (word pc)
             mlkem_native_libmlkem_gcc12_O2_mc /\
           read RIP s = word (pc + mlkem_poly_mulcache_compute) /\
           read RSP s = stackpointer /\
           read (memory :> bytes64 stackpointer) s = returnaddress /\
           C_ARGUMENTS [dst; src] s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add src (word (2 * i)))) s =
                    x i))
      (\s. read RIP s = returnaddress /\
           read RSP s = word_add stackpointer (word 8) /\
           !i. i < 128
               ==> let z_i = read(memory :> bytes16
                                (word_add dst (word (2 * i)))) s in
                   (ival z_i == (mulcache (ival o x)) i) (mod &3329) /\
                   abs(ival z_i) <= &3328)
      (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(dst,256)])`;;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e dst src pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (dst,256))
               [word pc,libmlkem_size; src,512; stackpointer,8]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                     mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem_poly_mulcache_compute) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [dst; src] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events src dst pc stackpointer
                                       returnaddress /\
                         memaccess_inbounds e2
                          [src,512; dst,256; word (pc + rodata_mlk_zetas),256;
                           stackpointer,8]
                          [dst,256]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(dst,256)])`;;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
