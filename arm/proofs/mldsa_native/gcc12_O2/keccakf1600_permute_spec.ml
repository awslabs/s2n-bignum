(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Keccak-f1600 permutation.                                                 *)
(* This is the code for mldsa_keccakf1600_permute from mldsa-native's        *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mldsa_native/README.md). Unlike the hand-written kernels, it reads its    *)
(* own table of round constants from the read-only data rather than taking   *)
(* it as an argument, and it does two rounds in each iteration of its loop.  *)
(* At the end, the theorem for the code in the whole image is also stated    *)
(* for the state as a 1600-bit word, with keccak_f1600 of common/fips202.ml. *)
(* It is also shown to be constant time and memory safe.                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_keccak.ml";;
needs "arm/proofs/utils/keccak_spec.ml";;
needs "arm/proofs/utils/keccak_f1600.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness in the whole image (see libmldsa.ml), with the table of round *)
(* constants of the image.                                                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a A pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 192),192))
            [(word pc,libmldsa_size); (a,200)] /\
        nonoverlapping (a,200) (word pc,libmldsa_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_keccakf1600_permute) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  wordlist_from_memory(a,25) s = A)
             (\s. read PC s = returnaddress /\
                  wordlist_from_memory(a,25) s = keccak 24 A)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(a,200);
                memory :> bytes(word_sub stackpointer (word 192),192)])`;;

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* The same for the state as a 1600-bit word, read by wbytes, with the       *)
(* permutation keccak_f1600 of common/fips202.ml (see                        *)
(* utils/keccak_f1600.ml), and tactics for callers, which carry the state   *)
(* between calls as 200 bytes.                                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600_STMT =
 `!a (S:1600 word) pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 192),192))
            [(word pc,libmldsa_size); (a,200)] /\
        nonoverlapping (a,200) (word pc,libmldsa_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_keccakf1600_permute) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  read (memory :> wbytes a) s = S)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes a) s = keccak_f1600 S)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(a,200);
                memory :> bytes(word_sub stackpointer (word 192),192)])`;;

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600 =
  assume_spec MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600_STMT;;

(*** The state at a as a 1600-bit word, from it as 200 bytes ***)

let KECCAK_STATE_AT_TAC a =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),
                          Comb(Comb(Const(":>",_),Const("memory",_)),
                               Comb(Const("bytes",_),aa))),_)),
           Comb(Const("val",_),_))
        when aa = mk_pair(a,`200`) ->
          ASSUME_TAC(REWRITE_RULE[GSYM READ_MEMORY_WBYTES_1600] th)
    | _ -> NO_TAC);;

(*** Apply ttac to the 1600-bit word for the state at a ***)

let KECCAK_STATE_THEN a (ttac:term->tactic) =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),
                          Comb(Comb(Const(":>",_),Const("memory",_)),
                               Comb(Const("wbytes",_),aa))),_)),v)
        when aa = a -> ttac v
    | _ -> NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the writes within the outputs.                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a A pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 192),192))
            [(word pc,libmldsa_size); (a,200)] /\
        nonoverlapping (a,200) (word pc,libmldsa_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_keccakf1600_permute) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  wordlist_from_memory(a,25) s = A /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  wordlist_from_memory(a,25) s = keccak 24 A /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a pc (word_sub stackpointer (word 192))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [a,200; word_sub stackpointer (word 192),192;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [a,200; word_sub stackpointer (word 192),192]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(a,200);
                memory :> bytes(word_sub stackpointer (word 192),192)])`;;

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 192),192))
            [(word pc,libmldsa_size); (a,200)] /\
        nonoverlapping (a,200) (word pc,libmldsa_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_keccakf1600_permute) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a pc (word_sub stackpointer (word 192))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [a,200; word_sub stackpointer (word 192),192;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [a,200; word_sub stackpointer (word 192),192]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(a,200);
                memory :> bytes(word_sub stackpointer (word 192),192)])`;;

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* The same for the state as a 1600-bit word.                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_F1600_STMT =
 `exists f_events.
     forall e a (S:1600 word) pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 192),192))
            [(word pc,libmldsa_size); (a,200)] /\
        nonoverlapping (a,200) (word pc,libmldsa_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_keccakf1600_permute) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  read (memory :> wbytes a) s = S /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes a) s = keccak_f1600 S /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a pc (word_sub stackpointer (word 192))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [a,200; word_sub stackpointer (word 192),192;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [a,200; word_sub stackpointer (word 192),192]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(a,200);
                memory :> bytes(word_sub stackpointer (word 192),192)])`;;

let MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_F1600 =
  assume_spec MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_F1600_STMT;;
