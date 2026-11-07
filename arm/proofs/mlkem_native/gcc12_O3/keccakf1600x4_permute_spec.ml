(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Keccak-f1600 permutation of four consecutive states. This is the code for *)
(* mlkem_keccakf1600x4_permute from mlkem-native's portable C implementation *)
(* compiled by gcc 12 with -O3 (see mlkem_native/README.md), which calls     *)
(* mlkem_keccakf1600_permute for each of the four states, the last time as a *)
(* tail call. It is verified in the whole image (see                         *)
(* libmlkem.ml), using the theorems for                                      *)
(* mlkem_keccakf1600_permute in the image. The specification is the same as  *)
(* for sha3_keccak4_f1600, except that the table of round constants is not   *)
(* an argument, since it is part of the image.                               *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/keccakf1600_permute_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_keccakf1600x4_permute:
       +0x0: stp     x19, x30, [sp, #-16]!
       +0x4: mov     x19, x0
       +0x8: bl      <mlkem_keccakf1600_permute>
       +0xc: add     x0, x19, #0xc8
      +0x10: bl      <mlkem_keccakf1600_permute>
      +0x14: add     x0, x19, #0x190
      +0x18: bl      <mlkem_keccakf1600_permute>
      +0x1c: add     x0, x19, #0x258
      +0x20: ldp     x19, x30, [sp], #16
      +0x24: b       <mlkem_keccakf1600_permute>
 ***)

let MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_keccakf1600x4_permute"];;

(* ------------------------------------------------------------------------- *)
(* The four calls of mlkem_keccakf1600_permute, keeping the states in memory *)
(* as numbers so that they are carried through the steps.                    *)
(* ------------------------------------------------------------------------- *)

let WORDLIST_FROM_MEMORY_25_STMT =
  `!a s (l:int64 list).
        wordlist_from_memory(a,25) s = l <=>
        LENGTH l = 25 /\ read (memory :> bytes(a,200)) s = num_of_wordlist l`;;

let WORDLIST_FROM_MEMORY_25 = assume_spec WORDLIST_FROM_MEMORY_25_STMT;;

let LOCAL_KECCAK_TAC =
  let tac = ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT) in
  fun atm n ->
    tac [`read X0 s`; atm; `pc:num`; `read SP s`; `read X30 s`] n THENL
     [REWRITE_TAC[WORDLIST_FROM_MEMORY_25] THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o check
       (can (term_match [] `wordlist_from_memory(a,25) s:int64 list = l`) o
        concl)) THEN
      REWRITE_TAC[WORDLIST_FROM_MEMORY_25] THEN STRIP_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a A1 A2 A3 A4 pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (a,800) (word_sub stackpointer (word 208),208) /\
        ALLPAIRS nonoverlapping
          [(a,800); (word_sub stackpointer (word 208),208)]
          [(word pc,libmlkem_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                  read PC s = word (pc + mlkem_keccakf1600x4_permute) /\
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

let MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_keccakf1600x4_permute_signature =
  ([("a", "uint64_t[static 100]", "false")],
   "void",
   [("a", "100", 8)],
   [("a", "100", 8)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:
      [`word(pc + rodata_mlk_KeccakF_RoundConstants):int64`,`192`]
    ~keep_maychanges:true
    mlkem_native_keccakf1600x4_permute_signature
    MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O3_EXEC;;

let LOCAL_KECCAK_SAFETY_TAC (assump_name:string) (n:int) =
  REMOVE_THEN assump_name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O3_mc,
       MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O3_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O3_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`;
       `read X30 s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `a:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC assump_name safety_th]);;

let MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e a pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           nonoverlapping (a,800) (word_sub stackpointer (word 208),208) /\
           ALLPAIRS nonoverlapping
           [a,800; word_sub stackpointer (word 208),208]
           [word pc,libmlkem_size]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                    read PC s = word (pc + mlkem_keccakf1600x4_permute) /\
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
                          word (pc + rodata_mlk_KeccakF_RoundConstants),192]
                         [a,800; word_sub stackpointer (word 208),208]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18] ,,
                MAYCHANGE
                [memory :> bytes (a,800);
                 memory :> bytes (word_sub stackpointer (word 208),208)])`;;

let MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* The same for the four states as 1600-bit words, read by wbytes, with the  *)
(* permutation keccak_f1600 of common/fips202.ml, as for                     *)
(* mlkem_keccakf1600_permute.                                                *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_F1600_STMT =
  `!a (S0:1600 word) (S1:1600 word) (S2:1600 word) (S3:1600 word)
    pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (a,800) (word_sub stackpointer (word 208),208) /\
        ALLPAIRS nonoverlapping
          [(a,800); (word_sub stackpointer (word 208),208)]
          [(word pc,libmlkem_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                  read PC s = word (pc + mlkem_keccakf1600x4_permute) /\
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

let MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_F1600 =
  assume_spec MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_F1600_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, using that   *)
(* of mlkem_keccakf1600_permute for the states as 1600-bit words.            *)
(* ------------------------------------------------------------------------- *)

let LOCAL_KECCAK_CS_TAC sv n =
  KECCAK_STATE_WBYTES_TAC sv THEN
  REMOVE_THEN "H_KECCAK" (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O3_mc,
       MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O3_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O3_mc,safety_th)
      [`e:(uarch_event)list`; `read X0 s`; sv; `pc:num`; `read SP s`;
       `read X30 s`] n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `a:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC "H_KECCAK" safety_th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]);;

let MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_FULL_F1600_STMT =
  `exists f_events.
       forall e a (S0:1600 word) (S1:1600 word) (S2:1600 word) (S3:1600 word)
              pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           nonoverlapping (a,800) (word_sub stackpointer (word 208),208) /\
           ALLPAIRS nonoverlapping
           [a,800; word_sub stackpointer (word 208),208]
           [word pc,libmlkem_size]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O3_mc /\
                    read PC s = word (pc + mlkem_keccakf1600x4_permute) /\
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
                          word (pc + rodata_mlk_KeccakF_RoundConstants),192]
                         [a,800; word_sub stackpointer (word 208),208]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [X18] ,,
                MAYCHANGE
                [memory :> bytes (a,800);
                 memory :> bytes (word_sub stackpointer (word 208),208)])`;;

let MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_FULL_F1600 =
  assume_spec MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_FULL_F1600_STMT;;
