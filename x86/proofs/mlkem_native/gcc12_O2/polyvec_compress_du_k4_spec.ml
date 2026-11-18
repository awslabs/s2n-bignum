(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a vector of 4 polynomials to 11 bits per coefficient. This *)
(* is the code for mlkem1024_polyvec_compress_du from mlkem-native's         *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md), which calls mlkem_poly_compress_d11 for each of  *)
(* the polynomials, in a loop. It is verified in the whole image (see        *)
(* libmlkem.ml), using the theorems for mlkem_poly_compress_d11 in the       *)
(* image.                                                                    *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/poly_compress_d11_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem1024_polyvec_compress_du:
       +0x0: push   r12
       +0x2: lea    r12,[rdi+0x580]
       +0x9: push   rbp
       +0xa: mov    rbp,rsi
       +0xd: push   rbx
       +0xe: mov    rbx,rdi
      +0x11: mov    rsi,rbp
      +0x14: mov    rdi,rbx
      +0x17: add    rbx,0x160
      +0x1e: add    rbp,0x200
      +0x25: call   <mlkem_poly_compress_d11>
      +0x2a: cmp    rbx,r12
      +0x2d: jne    <mlkem1024_polyvec_compress_du+0x11>
      +0x2f: pop    rbx
      +0x30: pop    rbp
      +0x31: pop    r12
      +0x33: ret
 ***)

let MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem1024_polyvec_compress_du"];;

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
     read (memory :> bytes(r,352)) s =
     nsum {i | i < 256} (\i. g i * 2 EXP (11 * i)) /\
     read (memory :> bytes(word_add r (word 352),352)) s =
     nsum {i | i < 256} (\i. g(256 + i) * 2 EXP (11 * i)) /\
     read (memory :> bytes(word_add r (word 704),352)) s =
     nsum {i | i < 256} (\i. g(512 + i) * 2 EXP (11 * i)) /\
     read (memory :> bytes(word_add r (word 1056),352)) s =
     nsum {i | i < 256} (\i. g(768 + i) * 2 EXP (11 * i))
     ==> read (memory :> bytes(r,1408)) s =
         nsum {i | i < 1024} (\i. g i * 2 EXP (11 * i))`;;

let POLYVEC_COMPRESS_DU_JOIN =
  assume_spec POLYVEC_COMPRESS_DU_JOIN_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let LOCAL_COMPRESS_D11_TAC =
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_POLY_COMPRESS_D11_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a x pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\ aligned 16 a /\
        ALL (nonoverlapping (r,1408)) [(word pc,libmlkem_size); (a,2048)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 56),64))
            [(word pc,libmlkem_size); (a,2048); (r,1408)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + mlkem1024_polyvec_compress_du) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 1024
                      ==> read(memory :> bytes16(word_add a (word(2 * i))))
                            s = x i)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  ((!i. i < 1024 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,1408)) s =
                       nsum {i | i < 1024}
                            (\i. ((4096 * val(x i) + 3329) DIV 6658) MOD 2048 *
                                 2 EXP (11 * i))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,1408);
                memory :> bytes(word_sub stackpointer (word 56),56)])`;;

let MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let LOCAL_COMPRESS_D11_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,
       MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `pc:num`;
       `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `r:int64`; `a:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 16 (word pc:int64) /\ aligned 16 a /\
           ALL (nonoverlapping (r,1408)) [(word pc,libmlkem_size); (a,2048)] /\
           ALL (nonoverlapping (word_sub stackpointer (word 56),64))
               [(word pc,libmlkem_size); (a,2048); (r,1408)]
           ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O2_mc /\
                    read RIP s = word (pc + mlkem1024_polyvec_compress_du) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events r a pc
                                (word_sub stackpointer (word 56))
                                returnaddress /\
                         memaccess_inbounds e2
                          [a,2048; r,1408; word (pc + mlkem_poly_compress_d11_const1),16;
                           word (pc + mlkem_poly_compress_d11_const2),16;
                           word_sub stackpointer (word 56),64]
                          [r,1408; word_sub stackpointer (word 56),56]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(r,1408);
                  memory :> bytes(word_sub stackpointer (word 56),56)])`;;

let MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLYVEC_COMPRESS_DU_K4_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
