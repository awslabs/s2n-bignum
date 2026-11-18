(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a vector of 3 polynomials to 10 bits per coefficient. This *)
(* is the code for mlkem768_polyvec_compress_du from mlkem-native's portable *)
(* C implementation compiled by gcc 12 with -O2 (see                         *)
(* mlkem_native/README.md), which calls mlkem_poly_compress_d10 for each of  *)
(* the polynomials, the last time as a tail call. It is verified in the      *)
(* whole image (see libmlkem.ml), using the theorems for                     *)
(* mlkem_poly_compress_d10 in the image.                                     *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/poly_compress_d10_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem768_polyvec_compress_du:
       +0x0: push   rbp
       +0x1: mov    rbp,rsi
       +0x4: push   rbx
       +0x5: mov    rbx,rdi
       +0x8: sub    rsp,0x8
       +0xc: call   <mlkem_poly_compress_d10>
      +0x11: lea    rsi,[rbp+0x200]
      +0x18: lea    rdi,[rbx+0x140]
      +0x1f: call   <mlkem_poly_compress_d10>
      +0x24: add    rsp,0x8
      +0x28: lea    rsi,[rbp+0x400]
      +0x2f: lea    rdi,[rbx+0x280]
      +0x36: pop    rbx
      +0x37: pop    rbp
      +0x38: jmp    <mlkem_poly_compress_d10>
 ***)

let MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K3_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem768_polyvec_compress_du"];;

(* ------------------------------------------------------------------------- *)
(* The output for the vector from those for the polynomials.                 *)
(* ------------------------------------------------------------------------- *)

let NSUM_SHIFT_EXP_STMT =
  `!f m n d. nsum {i | i < n} (\i. f(m + i) * 2 EXP (d * (m + i))) =
             2 EXP (d * m) * nsum {i | i < n} (\i. f(m + i) * 2 EXP (d * i))`;;

let NSUM_SHIFT_EXP =
  assume_spec NSUM_SHIFT_EXP_STMT;;

let POLYVEC_COMPRESS_DU_JOIN_STMT =
  `!r s (g:num->num).
     read (memory :> bytes(r,320)) s =
     nsum {i | i < 256} (\i. g i * 2 EXP (10 * i)) /\
     read (memory :> bytes(word_add r (word 320),320)) s =
     nsum {i | i < 256} (\i. g(256 + i) * 2 EXP (10 * i)) /\
     read (memory :> bytes(word_add r (word 640),320)) s =
     nsum {i | i < 256} (\i. g(512 + i) * 2 EXP (10 * i))
     ==> read (memory :> bytes(r,960)) s =
         nsum {i | i < 768} (\i. g i * 2 EXP (10 * i))`;;

let POLYVEC_COMPRESS_DU_JOIN =
  assume_spec POLYVEC_COMPRESS_DU_JOIN_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_COMPRESS_D10_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K3_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_COMPRESS_D10_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a x pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        ALL (nonoverlapping (r,960)) [(word pc,libmlkem_size); (a,1536)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 72),80))
            [(word pc,libmlkem_size); (a,1536); (r,960)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + mlkem768_polyvec_compress_du) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 768
                      ==> read(memory :> bytes16(word_add a (word(2 * i))))
                            s = x i)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  ((!i. i < 768 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,960)) s =
                       nsum {i | i < 768}
                            (\i. ((2048 * val(x i) + 3329) DIV 6658) MOD 1024 *
                                 2 EXP (10 * i))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,960);
                memory :> bytes(word_sub stackpointer (word 72),72)])`;;

let MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let LOCAL_COMPRESS_D10_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K3_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `pc:num`;
       `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `r:int64`; `a:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\
           ALL (nonoverlapping (r,960)) [(word pc,libmlkem_size); (a,1536)] /\
           ALL (nonoverlapping (word_sub stackpointer (word 72),80))
               [(word pc,libmlkem_size); (a,1536); (r,960)]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem768_polyvec_compress_du) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events r a pc
                                (word_sub stackpointer (word 72))
                                returnaddress /\
                         memaccess_inbounds e2
                          [a,1536; r,960; word_sub stackpointer (word 72),80]
                          [r,960; word_sub stackpointer (word 72),72]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(r,960);
                  memory :> bytes(word_sub stackpointer (word 72),72)])`;;

let MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
