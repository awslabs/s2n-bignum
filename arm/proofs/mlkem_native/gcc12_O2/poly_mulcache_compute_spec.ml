(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Precomputation of the mulcache for polynomial multiplication.             *)
(* This is the code for mlkem_poly_mulcache_compute from mlkem-native's      *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md). Unlike the hand-written kernel, it reads its     *)
(* own table of zetas from the read-only data rather than taking tables as   *)
(* arguments.                                                                *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/base.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/layout.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;

(* Names for the labels of this transcription, whose code is at pc.          *)

install_layout (layout_copies
 ["poly_mulcache_compute","mlkem_poly_mulcache_compute"]);;

(**** print_literal_relocs_from_elf
        "arm/mlkem_native/gcc12_O2/poly_mulcache_compute.o";;
 ****)

let mlkem_native_poly_mulcache_compute_gcc12_O2_mc,
    mlkem_native_poly_mulcache_compute_gcc12_O2_data =
  define_assert_relocs_from_elf
    ~map_symbol_name:(function
      | "WHOLE_READONLY" | "ltmp1" | "mlk_zetas" -> "mlk_zetas_data"
      | s -> failwith ("unknown symbol: " ^ s))
    "mlkem_native_poly_mulcache_compute_gcc12_O2_mc"
    "arm/mlkem_native/gcc12_O2/poly_mulcache_compute.o"
(fun w BL ADR ADRP ADD_rri64 LDR_Q_rri -> [
  ADRP (mk_var("mlk_zetas_data",`:num`),0,0,8);
  ADD_rri64 (mk_var("mlk_zetas_data",`:num`),0,8,8);
  w 0x91020105;         (* arm_ADD X5 X8 (rvalue (word 128)) *)
  w 0x91000804;         (* arm_ADD X4 X0 (rvalue (word 2)) *)
  w 0x91000822;         (* arm_ADD X2 X1 (rvalue (word 2)) *)
  w 0x91040108;         (* arm_ADD X8 X8 (rvalue (word 256)) *)
  w 0x12819fc7;         (* arm_MOVN W7 (word 3326) 0 *)
  w 0x1281a006;         (* arm_MOVN W6 (word 3328) 0 *)
  w 0x78c024a0;         (* arm_LDRSH W0 X5 (Postimmediate_Offset (word 2)) *)
  w 0x91002042;         (* arm_ADD X2 X2 (rvalue (word 8)) *)
  w 0x78df8041;         (* arm_LDRSH W1 X2 (Immediate_Offset (word
                           18446744073709551608)) *)
  w 0x4b0003e3;         (* arm_NEG W3 W0 *)
  w 0x13003c63;         (* arm_SBFM W3 W3 0 15 *)
  w 0x1b007c21;         (* arm_MUL W1 W1 W0 *)
  w 0x1b077c20;         (* arm_MUL W0 W1 W7 *)
  w 0x13003c00;         (* arm_SBFM W0 W0 0 15 *)
  w 0x1b060400;         (* arm_MADD W0 W0 W6 W1 *)
  w 0x13107c00;         (* arm_ASR W0 W0 16 *)
  w 0x781fe080;         (* arm_STRH W0 X4 (Immediate_Offset (word
                           18446744073709551614)) *)
  w 0x78dfc041;         (* arm_LDRSH W1 X2 (Immediate_Offset (word
                           18446744073709551612)) *)
  w 0x1b037c21;         (* arm_MUL W1 W1 W3 *)
  w 0x1b077c20;         (* arm_MUL W0 W1 W7 *)
  w 0x13003c00;         (* arm_SBFM W0 W0 0 15 *)
  w 0x1b060400;         (* arm_MADD W0 W0 W6 W1 *)
  w 0x13107c00;         (* arm_ASR W0 W0 16 *)
  w 0x78004480;         (* arm_STRH W0 X4 (Postimmediate_Offset (word 4)) *)
  w 0xeb05011f;         (* arm_CMP X8 X5 *)
  w 0x54fffda1;         (* arm_BNE (word 2097076) *)
  w 0xd65f03c0          (* arm_RET X30 *)
]);;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC =
  ARM_MK_EXEC_RULE mlkem_native_poly_mulcache_compute_gcc12_O2_mc;;

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

let MLK_ZETAS_MULCACHE = assume_spec MLK_ZETAS_MULCACHE_STMT;;

let MLK_ZETAS_MULCACHE_IVAL_STMT =
  `!i. i < 64
       ==> ival(iword(EL (64 + i) mlk_zetas):int16) = EL (64 + i) mlk_zetas /\
           abs(ival(iword(EL (64 + i) mlk_zetas):int16)) <= &1664 /\
           (&169 * ival(iword(EL (64 + i) mlk_zetas):int16) ==
            &17 pow (2 * bitreverse7 (2 * i) + 1)) (mod &3329) /\
           (&169 * --ival(iword(EL (64 + i) mlk_zetas):int16) ==
            &17 pow (2 * bitreverse7 (2 * i + 1) + 1)) (mod &3329)`;;

let MLK_ZETAS_MULCACHE_IVAL = assume_spec MLK_ZETAS_MULCACHE_IVAL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Some lemmas, tactics etc.                                                 *)
(* ------------------------------------------------------------------------- *)

let WORD_ZX_NEG_SX_STMT =
  `!z:int16. word_zx(word_sub (word 0) (word_sx z:int32)):int16 = word_neg z`;;

let WORD_ZX_NEG_SX = assume_spec WORD_ZX_NEG_SX_STMT;;

let CONG_MONT_ZETA = INTEGER_RULE
 `!n a z p x r:int. (r == a * (x * z)) (mod n) /\ (a * z == p) (mod n)
                    ==> (r == x * p) (mod n)`;;

let MULCACHE_ADDR_NORM_RULES =
  map ARITH_RULE
   [`2 * (64 + i) = 2 * i + 128`; `2 * (4 * i + 1) = 8 * i + 2`;
    `2 * (4 * i + 3) = 8 * i + 6`];;

(*** Instantiate a quantified input fact at a particular index ***)

let MSPEC_TAC (f,idx) =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_forall c &&
       (let b = snd(dest_forall c) in
        is_imp b && is_eq(rand b) && can (find_term ((=) f)) (rhs(rand b)))
    then MP_TAC(SPEC idx th) else failwith "MSPEC_TAC") THEN
  ANTS_TAC THENL
   [W(fun (asl,w) -> MP_TAC(ARITH_RULE (mk_imp(`i < 64`,w)))) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE MULCACHE_ADDR_NORM_RULES)];;

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
    let zz = rand(rand(rand(rator(concl cth)))) in
    CONJ_TAC THENL
     [REWRITE_TAC[mulcache; o_THM; INT_CONG_RREM;
                  ARITH_RULE `2 * 2 * i + 1 = 4 * i + 1`;
                  ARITH_RULE `2 * (2 * i + 1) + 1 = 4 * i + 3`] THEN
      MATCH_MP_TAC CONG_MONT_ZETA THEN
      MAP_EVERY EXISTS_TAC [`&169:int`; zz] THEN
      CONJ_TAC THENL [ACCEPT_TAC cth; ASM_REWRITE_TAC[]];
      MP_TAC bth THEN CONV_TAC(LAND_CONV INT_REDUCE_CONV) THEN
      INT_ARITH_TAC]));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_CORRECT_STMT =
  `!dst src zetas x pc.
    adrp_within_bounds (word zetas) (word pc) /\
    ALL (nonoverlapping (dst,256))
        [(word pc,poly_mulcache_compute_size); (src,512); (word zetas,256)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             (mlkem_native_poly_mulcache_compute_gcc12_O2_mc pc zetas) /\
           read PC s = word pc /\
           C_ARGUMENTS [dst; src] s /\
           bytes_loaded s (word zetas) mlk_zetas_data /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add src (word (2 * i)))) s =
                    x i))
      (\s. read PC s = word(pc + poly_mulcache_compute_ret) /\
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
  `!dst src zetas x pc returnaddress.
    adrp_within_bounds (word zetas) (word pc) /\
    ALL (nonoverlapping (dst,256))
        [(word pc,poly_mulcache_compute_size); (src,512); (word zetas,256)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             (mlkem_native_poly_mulcache_compute_gcc12_O2_mc pc zetas) /\
           read PC s = word pc /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [dst; src] s /\
           bytes_loaded s (word zetas) mlk_zetas_data /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add src (word (2 * i)))) s =
                    x i))
      (\s. read PC s = returnaddress /\
           !i. i < 128
               ==> let z_i = read(memory :> bytes16
                                (word_add dst (word (2 * i)))) s in
                   (ival z_i == (mulcache (ival o x)) i) (mod &3329) /\
                   abs(ival z_i) <= &3328)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(dst,256)])`;;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

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
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC;;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e dst src zetas pc returnaddress.
           adrp_within_bounds (word zetas) (word pc) /\
           ALL (nonoverlapping (dst,256))
           [word pc,116; src,512; word zetas,256]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                     (mlkem_native_poly_mulcache_compute_gcc12_O2_mc
                        pc zetas) /\
                    read PC s = word pc /\
                    bytes_loaded s (word zetas) mlk_zetas_data /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [dst; src] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events src dst zetas pc returnaddress /\
                        memaccess_inbounds e2
                         [src,512; dst,256; word zetas,256]
                         [dst,256])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(dst,256)])`;;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* The same code in the whole image, with the zetas (see                     *)
(* libmlkem.ml).                                                             *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_CODE_RULE mlkem_native_poly_mulcache_compute_gcc12_O2_mc
    (layout "mlkem_poly_mulcache_compute") [layout "rodata_mlk_zetas"];;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_ZETAS_IN_IMAGE =
  MLKEM_NATIVE_IMAGE_DATA_RULE mlk_zetas_data (layout "rodata_mlk_zetas");;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!dst src x pc returnaddress.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    ALL (nonoverlapping (dst,256)) [(word pc,libmlkem_size); (src,512)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_gcc12_O2_mc /\
           read PC s = word (pc + mlkem_poly_mulcache_compute) /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [dst; src] s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add src (word (2 * i)))) s =
                    x i))
      (\s. read PC s = returnaddress /\
           !i. i < 128
               ==> let z_i = read(memory :> bytes16
                                (word_add dst (word (2 * i)))) s in
                   (ival z_i == (mulcache (ival o x)) i) (mod &3329) /\
                   abs(ival z_i) <= &3328)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(dst,256)])`;;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e dst src pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (dst,256)) [word pc,libmlkem_size; src,512]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                     mlkem_native_libmlkem_gcc12_O2_mc /\
                    read PC s = word (pc + mlkem_poly_mulcache_compute) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [dst; src] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events src dst pc returnaddress /\
                        memaccess_inbounds e2
                         [src,512; dst,256; word (pc + rodata_mlk_zetas),256]
                         [dst,256])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(dst,256)])`;;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
