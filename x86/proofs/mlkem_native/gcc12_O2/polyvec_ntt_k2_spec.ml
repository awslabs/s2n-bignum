(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Forward number-theoretic transform of a vector of 2 polynomials. This is  *)
(* the code for mlkem512_polyvec_ntt from mlkem-native's portable C          *)
(* implementation compiled by gcc 12 with -O2 (see mlkem_native/README.md),  *)
(* which calls mlkem_poly_ntt for each of the polynomials, the last time as  *)
(* a tail call. It is verified in the whole image (see libmlkem.ml), using   *)
(* the theorems for mlkem_poly_ntt in the image.                             *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/poly_ntt_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem512_polyvec_ntt:
       +0x0: push   rbx
       +0x1: mov    rbx,rdi
       +0x4: call   <mlkem_poly_ntt>
       +0x9: lea    rdi,[rbx+0x200]
      +0x10: pop    rbx
      +0x11: jmp    <mlkem_poly_ntt>
 ***)

let MLKEM_NATIVE_POLYVEC_NTT_K2_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem512_polyvec_ntt"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_NTT_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_NTT_K2_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_NTT_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a x pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        nonoverlapping (a,1024) (word pc,libmlkem_size) /\
        ALL (nonoverlapping (word_sub stackpointer (word 68),76))
            [(word pc,libmlkem_size); (a,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + mlkem512_polyvec_ntt) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  !i. i < 512
                      ==> read(memory :> bytes16(word_add a (word(2 * i))))
                            s = x i)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !j. j < 2 /\
                      (!i. i < 256 ==> abs(ival(x(256 * j + i))) <= &8191)
                      ==> !i. i < 256
                              ==> let zi =
                                    read(memory :> bytes16
                                     (word_add a (word(512 * j + 2 * i)))) s
                                  in (ival zi ==
                                      forward_ntt (\n. ival(x(256 * j + n))) i)
                                     (mod &3329) /\
                                     abs(ival zi) <= &23594)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,1024);
                memory :> bytes(word_sub stackpointer (word 68),68)])`;;

let MLKEM_NATIVE_POLYVEC_NTT_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLYVEC_NTT_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let LOCAL_NTT_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLYVEC_NTT_K2_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read RDI s`; `pc:num`; `read RSP s`;
       `read (memory :> bytes64(read RSP s)) s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `a:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_NTT_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           nonoverlapping (a,1024) (word pc,libmlkem_size) /\
           ALL (nonoverlapping (word_sub stackpointer (word 68),76))
               [(word pc,libmlkem_size); (a,1024)]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem512_polyvec_ntt) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a pc
                                (word_sub stackpointer (word 68))
                                returnaddress /\
                         memaccess_inbounds e2
                          [a,1024; word (pc + rodata_mlk_zetas),256;
                           word_sub stackpointer (word 68),76]
                          [a,1024; word_sub stackpointer (word 68),68]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(a,1024);
                  memory :> bytes(word_sub stackpointer (word 68),68)])`;;

let MLKEM_NATIVE_POLYVEC_NTT_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLYVEC_NTT_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
