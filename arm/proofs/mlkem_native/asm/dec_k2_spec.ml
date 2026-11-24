(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* The contracts of the function mlkem512_dec of ML-KEM-512                *)
(* (arm/mlkem_native/asm/mlkem512.S) in the image of the ML-KEM API in     *)
(* assembly: decapsulation, its correctness and its constant-time and      *)
(* memory safety, stated as in the proofs of the compiled C of mlkem-      *)
(* native (see arm/mlkem_native/asm/README.md). The proofs are in          *)
(* dec_k2_proof.ml.                                                        *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/asm/layout.ml";;
needs "arm/proofs/mlkem_native/asm/hash_g_spec.ml";;
needs "arm/proofs/mlkem_native/asm/hash_h_spec.ml";;
needs "arm/proofs/mlkem_native/asm/getnoise_spec.ml";;
needs "arm/proofs/mlkem_native/asm/gen_matrix_k2_spec.ml";;
needs "arm/proofs/mlkem_native/asm/gen_matrix_k2_safe_spec.ml";;
needs "arm/proofs/mlkem_native/asm/pke_encrypt_k2_spec.ml";;
needs "arm/proofs/mlkem_native/asm/pke_decrypt_k2_spec.ml";;
needs "common/fips203/fips203.ml";;
needs "arm/proofs/utils/mlkem_native2_cbd.ml";;
needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(* ------------------------------------------------------------------------- *)
(* ML-KEM.Decaps_internal (FIPS 203 Algorithm 18), after the hash check of   *)
(* the decapsulation key (FIPS 203 section 7.3): if the check passes, the    *)
(* shared secret at ss and the return value 0, else -5 (MLK_ERR_INVALID_SK). *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_DEC_K2_ASM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!ss ct sk (dk:byte list) (c:byte list) pc stackpointer returnaddress.
     aligned 4096 (word pc:int64) /\
     pc + mlkem_native2_image_size <= 2 EXP 64 /\
     aligned 16 stackpointer /\ LENGTH dk = 1632 /\ LENGTH c = 768 /\
     nonoverlapping (ct,768) (word pc,mlkem_native2_image_size) /\
     nonoverlapping (sk,1632) (word pc,mlkem_native2_image_size) /\
     nonoverlapping (ss,32) (word_sub stackpointer (word 10304),10304) /\
     ALLPAIRS nonoverlapping
      [(ss,32); (word_sub stackpointer (word 10304),10304)]
      [(ct,768); (sk,1632); (word pc,mlkem_native2_image_size)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
               read PC s = word(pc + mlkem512_dec) /\
               read SP s = stackpointer /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [ss; ct; sk] s /\
               read (memory :> bytes(ct,768)) s = num_of_bytelist c /\
               read (memory :> bytes(sk,1632)) s = num_of_bytelist dk)
          (\s. read PC s = returnaddress /\
               (mlkem_decaps_check mlkem512 dk c
                ==> read (memory :> bytes(ss,32)) s =
                    num_of_bytelist(mlkem_decaps_internal mlkem512 dk c)) /\
               C_RETURN s =
               (if mlkem_decaps_check mlkem512 dk c then word 0
                else word 0xfffffffb))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(ss,32);
                      memory :> bytes(word_sub stackpointer (word 10304),
                                      10304)])`;;

let MLKEM_NATIVE_DEC_K2_ASM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_DEC_K2_ASM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The constant-time and memory safety of decapsulation: the events depend   *)
(* only on the addresses and on ek and h in dk, which are public, and on     *)
(* whether h = H(ek) (the hash check). As in the proofs of the compiled C,   *)
(* there are no results in the postcondition.                                *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_DEC_K2_ASM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e ss ct sk (dk:byte list) pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\
       pc + mlkem_native2_image_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ LENGTH dk = 1632 /\
       nonoverlapping (ct,768) (word pc,mlkem_native2_image_size) /\
       nonoverlapping (sk,1632) (word pc,mlkem_native2_image_size) /\
       nonoverlapping (ss,32) (word_sub stackpointer (word 10304),10304) /\
       ALLPAIRS nonoverlapping
        [(ss,32); (word_sub stackpointer (word 10304),10304)]
        [(ct,768); (sk,1632); (word pc,mlkem_native2_image_size)]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
                 read PC s = word(pc + mlkem512_dec) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [ss; ct; sk] s /\
                 read (memory :> bytes(sk,1632)) s = num_of_bytelist dk /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events ss ct sk pc
                           (word_sub stackpointer (word 10304)) returnaddress
                           (mlkem_slice 768 800 dk)
                           (mlkem_slice 1568 32 dk) /\
                    memaccess_inbounds e2
                     [ct,768; sk,1632; ss,32;
                      word(pc + mlkem_native2_constants),6656;
                      word_sub stackpointer (word 10304),10304]
                     [ss,32; word_sub stackpointer (word 10304),10304]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(ss,32);
                        memory :> bytes(word_sub stackpointer (word 10304),
                                        10304)])`;;

let MLKEM_NATIVE_DEC_K2_ASM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_DEC_K2_ASM_IMAGE_SUBROUTINE_SAFE_STMT;;
