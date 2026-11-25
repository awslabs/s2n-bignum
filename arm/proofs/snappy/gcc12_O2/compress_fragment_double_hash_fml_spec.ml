(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The five copies of FindMatchLengthPlain(s1, s2, ip_end) that gcc inlined  *)
(* into CompressFragmentDoubleHash: each computes the length of the common  *)
(* prefix of the input from s1 and from s2 that ends at the end of the       *)
(* input, snappy_match_length src s1 s2, 8 bytes at a time, then the first   *)
(* difference from the lowest set bit of the exclusive or, or one byte at a  *)
(* time in the last 8 bytes of the input.                                    *)
(*                                                                           *)
(*   A  +0xf0  .. join3   s1 = candidate + 4, s2 = ip + 4 (table2 match)     *)
(*   B  +0x244 .. join9   s1 = candidate + 4, s2 = ip + 4 (table match)      *)
(*   C  +0x2d4 .. join10  s1 = candidate2, s2 = ip + 1                       *)
(*   D  +0x458 .. join18  s1 = candidate + 4, s2 = ip + 4 (copy loop, table) *)
(*   E  +0x59c .. join18  s1 = candidate + 4, s2 = ip + 4 (copy loop, table2) *)
(*                                                                           *)
(* The registers are given in the forms in which the proofs of the pieces   *)
(* have them (a pointer into the input as word_add inp (word k)).            *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_model_spec.ml";;

let snappy_cf2_fml_hyps =
 "aligned 4096 (word pc:int64) /\\ pc + libsnappy_size <= 2 EXP 64 /\\
  LENGTH (src:byte list) <= 65536 /\\ 15 <= LENGTH src /\\
  val (inp:int64) + LENGTH src < 2 EXP 64";;

let snappy_cf2_fml_pre =
 "aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\\
  read events s = e /\\
  read X13 s = word_add inp (word(LENGTH src)) /\\
  read (memory :> bytes(inp,LENGTH src)) s = num_of_bytelist src";;

let snappy_cf2_fml_ev =
 "?e2. read events s = APPEND e2 e /\\
       memaccess_inbounds e2 [inp,LENGTH src] []";;

let SNAPPY_CF2_GCC12_O2_FML_A_STMT = parse_term
 ("!src inp ip c pc e. " ^ snappy_cf2_fml_hyps ^ " /\\
     c < ip /\\ ip + 4 <= LENGTH src
     ==> ensures arm
          (\\s. " ^ snappy_cf2_fml_pre ^ " /\\
               read PC s = word(pc + CompressFragmentDoubleHash_loop2_exit2) /\\
               read X8 s = word_add inp (word ip) /\\
               read X14 s = word_add inp (word c))
          (\\s. read PC s = word(pc + CompressFragmentDoubleHash_join3) /\\
               read X16 s = word_add inp (word(LENGTH src - 8)) /\\
               read X4 s = word(snappy_match_length src (c + 4) (ip + 4)) /\\
               " ^ snappy_cf2_fml_ev ^ ")
          (MAYCHANGE [PC; X4; X6; X7; X15; X16; X17; X18; X19] ,,
           MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events])");;

let SNAPPY_CF2_GCC12_O2_FML_B_STMT = parse_term
 ("!src inp ip c pc e. " ^ snappy_cf2_fml_hyps ^ " /\\
     c < ip /\\ ip + 4 <= LENGTH src
     ==> ensures arm
          (\\s. " ^ snappy_cf2_fml_pre ^ " /\\
               read PC s = word(pc + 15652) /\\
               read X6 s = word_add inp (word(ip + 4)) /\\
               read X16 s = word_add inp (word(LENGTH src - 8)) /\\
               read X14 s = word_add inp (word c))
          (\\s. read PC s = word(pc + CompressFragmentDoubleHash_join9) /\\
               read X4 s = word(snappy_match_length src (c + 4) (ip + 4)) /\\
               " ^ snappy_cf2_fml_ev ^ ")
          (MAYCHANGE [PC; X4; X6; X7; X17; X18; X19; X20] ,,
           MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events])");;

let SNAPPY_CF2_GCC12_O2_FML_C_STMT = parse_term
 ("!src inp ip c pc e. " ^ snappy_cf2_fml_hyps ^ " /\\
     c <= ip /\\ ip + 9 <= LENGTH src
     ==> ensures arm
          (\\s. " ^ snappy_cf2_fml_pre ^ " /\\
               read PC s = word(pc + 15796) /\\
               read X20 s = word_add inp (word(ip + 1)) /\\
               read X6 s = word_add inp (word(ip + 1)) /\\
               read X16 s = word_add inp (word(LENGTH src - 8)) /\\
               read X30 s = word_add inp (word c))
          (\\s. read PC s = word(pc + CompressFragmentDoubleHash_join10) /\\
               read X7 s = word(snappy_match_length src c (ip + 1)) /\\
               " ^ snappy_cf2_fml_ev ^ ")
          (MAYCHANGE [PC; X6; X7; X17; X18; X19] ,,
           MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events])");;

let SNAPPY_CF2_GCC12_O2_FML_D_STMT = parse_term
 ("!src inp ip c pc e. " ^ snappy_cf2_fml_hyps ^ " /\\
     c < ip /\\ ip + 4 <= LENGTH src
     ==> ensures arm
          (\\s. " ^ snappy_cf2_fml_pre ^ " /\\
               read PC s = word(pc + CompressFragmentDoubleHash_loop5_next2) /\\
               read X1 s = word_add inp (word ip) /\\
               read X16 s = word_add inp (word(LENGTH src - 8)) /\\
               read X14 s = word_add inp (word c))
          (\\s. read PC s = word(pc + CompressFragmentDoubleHash_join18) /\\
               read X4 s = word(snappy_match_length src (c + 4) (ip + 4)) /\\
               " ^ snappy_cf2_fml_ev ^ ")
          (MAYCHANGE [PC; X4; X6; X7; X8; X15; X17; X18] ,,
           MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events])");;

let SNAPPY_CF2_GCC12_O2_FML_E_STMT = parse_term
 ("!src inp ip c pc e. " ^ snappy_cf2_fml_hyps ^ " /\\
     c < ip /\\ ip + 4 <= LENGTH src
     ==> ensures arm
          (\\s. " ^ snappy_cf2_fml_pre ^ " /\\
               read PC s = word(pc + 16508) /\\
               read X1 s = word_add inp (word ip) /\\
               read X16 s = word_add inp (word(LENGTH src - 8)) /\\
               read X14 s = word_add inp (word c))
          (\\s. read PC s = word(pc + CompressFragmentDoubleHash_join18) /\\
               read X4 s = word(snappy_match_length src (c + 4) (ip + 4)) /\\
               " ^ snappy_cf2_fml_ev ^ ")
          (MAYCHANGE [PC; X4; X6; X7; X8; X15; X17; X18] ,,
           MAYCHANGE [NF; ZF; CF; VF] ,, MAYCHANGE [events])");;

let SNAPPY_CF2_GCC12_O2_FML_A = assume_spec SNAPPY_CF2_GCC12_O2_FML_A_STMT;;
let SNAPPY_CF2_GCC12_O2_FML_B = assume_spec SNAPPY_CF2_GCC12_O2_FML_B_STMT;;
let SNAPPY_CF2_GCC12_O2_FML_C = assume_spec SNAPPY_CF2_GCC12_O2_FML_C_STMT;;
let SNAPPY_CF2_GCC12_O2_FML_D = assume_spec SNAPPY_CF2_GCC12_O2_FML_D_STMT;;
let SNAPPY_CF2_GCC12_O2_FML_E = assume_spec SNAPPY_CF2_GCC12_O2_FML_E_STMT;;
