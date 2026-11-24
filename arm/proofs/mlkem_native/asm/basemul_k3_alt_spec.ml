(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* The contracts of mlkem_basemul_k3_alt that the proofs of the callers    *)
(* in the image of the ML-KEM API in assembly use: the correctness         *)
(* theorem of arm/proofs/mlkem_basemul_k3_alt.ml, and the safety theorem   *)
(* of that file with the frame of the correctness theorem. They are        *)
(* stated about the code of that file, mlkem_basemul_k3_alt_mc, which is   *)
(* also in the image, where ARM_SUBROUTINE_SIM_TAC uses them for it (see   *)
(* arm/mlkem_native/asm/README.md). The proof file loads the standalone    *)
(* proof, which proves the first, and makes the second from its safety     *)
(* theorem.                                                                *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "common/mlkem_mldsa.ml";;

let mlkem_basemul_k3_alt_mc = define_from_elf
 "mlkem_basemul_k3_alt_mc" "arm/mlkem/mlkem_basemul_k3_alt.o";;

let pmull = define
`pmull (x0: int) (x1 : int) (y0 : int) (y1 : int) = x1 * y1 + x0 * y0`;;

let pmull_acc3 = define
  `pmull_acc3 (x00: int) (x01 : int) (y00 : int) (y01 : int)
              (x10: int) (x11 : int) (y10 : int) (y11 : int)
              (x20: int) (x21 : int) (y20 : int) (y21 : int) =
              pmull x20 x21 y20 y21 + pmull x10 x11 y10 y11 +
              pmull x00 x01 y00 y01`;;

let pmul_acc3 = define
  `pmul_acc3 (x00: int) (x01 : int) (y00 : int) (y01 : int)
             (x10: int) (x11 : int) (y10 : int) (y11 : int)
             (x20: int) (x21 : int) (y20 : int) (y21 : int) =
             (&(inverse_mod 3329 65536) *
    pmull_acc3 x00 x01 y00 y01 x10 x11 y10 y11 x20 x21 y20 y21) rem &3329`;;

let basemul3_even = define
 `basemul3_even x0 y0 y0t x1 y1 y1t x2 y2 y2t = \i.
    pmul_acc3 (x0 (2 * i)) (x0 (2 * i + 1))
              (y0 (2 * i)) (y0t i)
              (x1 (2 * i)) (x1 (2 * i + 1))
              (y1 (2 * i)) (y1t i)
              (x2 (2 * i)) (x2 (2 * i + 1))
              (y2 (2 * i)) (y2t i)`;;

let basemul3_odd = define
 `basemul3_odd x0 y0 x1 y1 x2 y2 = \i.
   pmul_acc3 (x0 (2 * i)) (x0 (2 * i + 1))
             (y0 (2 * i + 1)) (y0 (2 * i))
             (x1 (2 * i)) (x1 (2 * i + 1))
             (y1 (2 * i + 1)) (y1 (2 * i))
             (x2 (2 * i)) (x2 (2 * i + 1))
             (y2 (2 * i + 1)) (y2 (2 * i))`;;

let MLKEM_BASEMUL_K3_ALT_SUBROUTINE_CORRECT_STMT =
 `!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t x2 y2 y2t
    pc stackpointer returnaddress.
       aligned 16 stackpointer /\
       ALLPAIRS nonoverlapping
         [(dst, 512); (word_sub stackpointer (word 64),64)]
         [(word pc, LENGTH mlkem_basemul_k3_alt_mc);
          (srcA, 1536); (srcB, 1536); (srcBt, 768)] /\
       nonoverlapping (dst,512) (word_sub stackpointer (word 64),64)
       ==>
       ensures arm
       (\s. // Assert that mlkem_basemul_k3 is loaded at PC
         aligned_bytes_loaded s (word pc) mlkem_basemul_k3_alt_mc /\
         read PC s = word pc /\
         read SP s = stackpointer /\
         read X30 s = returnaddress /\
         C_ARGUMENTS [dst; srcA; srcB; srcBt] s  /\
         // Give names to in-memory data to be
         // able to refer to them in the post-condition
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (2 * i)))) s = x0 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB  (word (2 * i)))) s = y0 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (2 * i)))) s = y0t i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (512 + 2 * i)))) s = x1 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (512 + 2 * i)))) s = y1 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (256 + 2 * i)))) s = y1t i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (1024 + 2 * i)))) s = x2 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (1024 + 2 * i)))) s = y2 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (512 + 2 * i)))) s = y2t i)
       )
       (\s. read PC s = returnaddress /\
            ((!i. i < 256
                   ==> abs(ival(x0 i)) <= &2 pow 12 /\
                       abs(ival(x1 i)) <= &2 pow 12 /\
                       abs(ival(x2 i)) <= &2 pow 12)
               ==> (!i. i < 128
                        ==> (ival(read(memory :> bytes16
                                 (word_add dst (word (4 * i)))) s) ==
                             basemul3_even
                               (ival o x0) (ival o y0) (ival o y0t)
                               (ival o x1) (ival o y1) (ival o y1t)
                               (ival o x2) (ival o y2) (ival o y2t) i)
                               (mod &3329) /\
                            (ival(read(memory :> bytes16
                                 (word_add dst (word (4 * i + 2)))) s) ==
                             basemul3_odd
                               (ival o x0) (ival o y0)
                               (ival o x1) (ival o y1)
                               (ival o x2) (ival o y2) i) (mod &3329))))
       // Register and memory footprint
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(dst, 512);
                  memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLKEM_BASEMUL_K3_ALT_SUBROUTINE_CORRECT =
  assume_spec MLKEM_BASEMUL_K3_ALT_SUBROUTINE_CORRECT_STMT;;

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_BASEMUL_K3_ALT_SUBROUTINE_SAFE_FRAMED_STMT =
 `exists f_events.
       forall e srcA srcB srcBt dst pc stackpointer returnaddress.
           aligned 16 stackpointer /\
           ALLPAIRS nonoverlapping
           [dst,512; word_sub stackpointer (word 64),64]
           [word pc,LENGTH mlkem_basemul_k3_alt_mc; srcA,1536; srcB,1536;
            srcBt,768] /\
           nonoverlapping (dst,512) (word_sub stackpointer (word 64),64)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc) mlkem_basemul_k3_alt_mc /\
                    read PC s = word pc /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [dst; srcA; srcB; srcBt] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 =
                        f_events srcA srcB srcBt dst pc
                        (word_sub stackpointer (word 64))
                        returnaddress /\
                        memaccess_inbounds e2
                        [srcA,1536; srcB,1536; srcBt,768; dst,512;
                         word_sub stackpointer (word 64),64]
                        [dst,512; word_sub stackpointer (word 64),64])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(dst, 512);
                  memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLKEM_BASEMUL_K3_ALT_SUBROUTINE_SAFE_FRAMED =
  assume_spec MLKEM_BASEMUL_K3_ALT_SUBROUTINE_SAFE_FRAMED_STMT;;
