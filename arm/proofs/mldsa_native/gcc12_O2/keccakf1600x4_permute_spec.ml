(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Keccak-f1600 permutation of four consecutive states. This is the code for *)
(* mldsa_keccakf1600x4_permute from mldsa-native's portable C implementation *)
(* compiled by gcc 12 with -O2 (see mldsa_native/README.md), which calls     *)
(* mldsa_keccakf1600_permute for each of the four states, the last time as a *)
(* tail call. It is verified in the whole image (see                         *)
(* libmldsa.ml), using the theorems for                                      *)
(* mldsa_keccakf1600_permute in the image. The specification is the same as  *)
(* for sha3_keccak4_f1600, except that the table of round constants is not   *)
(* an argument, since it is part of the image. It is also shown to be        *)
(* constant time and memory safe.                                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_keccak.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/keccakf1600_permute_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_keccakf1600x4_permute:
       +0x0: stp     x19, x30, [sp, #-16]!
       +0x4: mov     x19, x0
       +0x8: bl      <mldsa_keccakf1600_permute>
       +0xc: add     x0, x19, #0xc8
      +0x10: bl      <mldsa_keccakf1600_permute>
      +0x14: add     x0, x19, #0x190
      +0x18: bl      <mldsa_keccakf1600_permute>
      +0x1c: add     x0, x19, #0x258
      +0x20: ldp     x19, x30, [sp], #16
      +0x24: b       <mldsa_keccakf1600_permute>
 ***)

let MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_keccakf1600x4_permute"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a A1 A2 A3 A4 pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (a,800) (word_sub stackpointer (word 208),208) /\
        ALLPAIRS nonoverlapping
          [(a,800); (word_sub stackpointer (word 208),208)]
          [(word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_keccakf1600x4_permute) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  wordlist_from_memory(a,25) s = A1 /\
                  wordlist_from_memory(word_add a (word 200),25) s = A2 /\
                  wordlist_from_memory(word_add a (word 400),25) s = A3 /\
                  wordlist_from_memory(word_add a (word 600),25) s = A4)
             (\s. read PC s = returnaddress /\
                  wordlist_from_memory(a,25) s = keccak 24 A1 /\
                  wordlist_from_memory(word_add a (word 200),25) s =
                  keccak 24 A2 /\
                  wordlist_from_memory(word_add a (word 400),25) s =
                  keccak 24 A3 /\
                  wordlist_from_memory(word_add a (word 600),25) s =
                  keccak 24 A4)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(a,800);
                memory :> bytes(word_sub stackpointer (word 208),208)])`;;

let MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The same for the states as 1600-bit words, read by wbytes, with the       *)
(* permutation keccak_f1600 of common/fips202.ml (see                        *)
(* utils/keccak_f1600.ml).                                                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600_STMT =
 `!a (S0:1600 word) (S1:1600 word) (S2:1600 word) (S3:1600 word)
    pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (a,800) (word_sub stackpointer (word 208),208) /\
        ALLPAIRS nonoverlapping
          [(a,800); (word_sub stackpointer (word 208),208)]
          [(word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_keccakf1600x4_permute) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  read (memory :> wbytes a) s = S0 /\
                  read (memory :> wbytes (word_add a (word 200))) s = S1 /\
                  read (memory :> wbytes (word_add a (word 400))) s = S2 /\
                  read (memory :> wbytes (word_add a (word 600))) s = S3)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes a) s = keccak_f1600 S0 /\
                  read (memory :> wbytes (word_add a (word 200))) s =
                  keccak_f1600 S1 /\
                  read (memory :> wbytes (word_add a (word 400))) s =
                  keccak_f1600 S2 /\
                  read (memory :> wbytes (word_add a (word 600))) s =
                  keccak_f1600 S3)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(a,800);
                memory :> bytes(word_sub stackpointer (word 208),208)])`;;

let MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600 =
  assume_spec
   MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together, for the states as  *)
(* 1600-bit words, using the FULL theorem of mldsa_keccakf1600_permute, and  *)
(* constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/utils/mldsa_native_full.ml";;

let LOCAL_KECCAK_CS_TAC sv n =
  KECCAK_STATE_WBYTES_TAC sv THEN
  REMOVE_THEN "H_KECCAK" (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mldsa_native_libmldsa_gcc12_O2_mc,
       MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_EXEC,
       0x0,mldsa_native_libmldsa_gcc12_O2_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; sv; `pc:num`; `read SP s`;
       `read X30 s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `a:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC "H_KECCAK" safety_th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

let MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_F1600_STMT =
  `exists f_events.
       forall e a (S0:1600 word) (S1:1600 word) (S2:1600 word) (S3:1600 word)
              pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           nonoverlapping (a,800) (word_sub stackpointer (word 208),208) /\
           ALLPAIRS nonoverlapping
           [a,800; word_sub stackpointer (word 208),208]
           [word pc,libmldsa_size]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa_keccakf1600x4_permute) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read (memory :> wbytes a) s = S0 /\
                    read (memory :> wbytes (word_add a (word 200))) s = S1 /\
                    read (memory :> wbytes (word_add a (word 400))) s = S2 /\
                    read (memory :> wbytes (word_add a (word 600))) s = S3 /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    read (memory :> wbytes a) s = keccak_f1600 S0 /\
                    read (memory :> wbytes (word_add a (word 200))) s =
                    keccak_f1600 S1 /\
                    read (memory :> wbytes (word_add a (word 400))) s =
                    keccak_f1600 S2 /\
                    read (memory :> wbytes (word_add a (word 600))) s =
                    keccak_f1600 S3 /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 =
                         f_events a pc (word_sub stackpointer (word 208))
                         returnaddress /\
                         memaccess_inbounds e2
                         [a,800; word_sub stackpointer (word 208),208;
                          word (pc + rodata_mld_KeccakF_RoundConstants),192]
                         [a,800; word_sub stackpointer (word 208),208]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18] ,,
                MAYCHANGE
                [memory :> bytes (a,800);
                 memory :> bytes (word_sub stackpointer (word 208),208)])`;;

let MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_F1600 =
  assume_spec MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_F1600_STMT;;

let MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e a pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           nonoverlapping (a,800) (word_sub stackpointer (word 208),208) /\
           ALLPAIRS nonoverlapping
           [a,800; word_sub stackpointer (word 208),208]
           [word pc,libmldsa_size]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa_keccakf1600x4_permute) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 =
                         f_events a pc (word_sub stackpointer (word 208))
                         returnaddress /\
                         memaccess_inbounds e2
                         [a,800; word_sub stackpointer (word 208),208;
                          word (pc + rodata_mld_KeccakF_RoundConstants),192]
                         [a,800; word_sub stackpointer (word 208),208]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18] ,,
                MAYCHANGE
                [memory :> bytes (a,800);
                 memory :> bytes (word_sub stackpointer (word 208),208)])`;;

let MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
