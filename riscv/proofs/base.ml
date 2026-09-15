(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Load basic background needed for the RV32IM proofs.                       *)
(* ========================================================================= *)

loads "update_database.ml";;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Some background theory from the standard libraries.                       *)
(* ------------------------------------------------------------------------- *)

needs "Library/iter.ml";;
needs "Library/rstc.ml";;
needs "Library/bitsize.ml";;
needs "Library/pocklington.ml";;
needs "Library/integer.ml";;
needs "Library/words.ml";;
needs "Library/bitmatch.ml";;
loadt "Library/records.ml";;

(* ------------------------------------------------------------------------- *)
(* Common proof infrastructure shared with the other backends.               *)
(* ------------------------------------------------------------------------- *)

loadt "common/overlap.ml";;
loadt "common/for_hollight.ml";;
loadt "common/words2.ml";;
loadt "common/misc.ml";;
loadt "common/components.ml";;
loadt "common/alignment.ml";;
loadt "common/relational.ml";;
loadt "common/interval.ml";;
loadt "common/elf.ml";;
loadt "common/safety.ml";;
loadt "common/execution.ml";;

(* ------------------------------------------------------------------------- *)
(* The RV32IM state and instruction semantics.                               *)
(* ------------------------------------------------------------------------- *)

loadt "riscv/proofs/instruction.ml";;
loadt "riscv/proofs/decode.ml";;

(* ------------------------------------------------------------------------- *)
(* Generic memory wordlists and standard overloading.                        *)
(* ------------------------------------------------------------------------- *)

prioritize_int();;
prioritize_real();;
prioritize_num();;

loadt "common/wordlist.ml";;
