(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* VAL_WORD_NUMERAL_CONV reduces val(word n) for a numeral n, as the         *)
(* tactics that simulate calls of memset, memcpy and randombytes need it.    *)
(* The contracts for those functions are in the mlkem_native_libc.ml of      *)
(* arm/proofs/utils and x86/proofs/utils.                                    *)
(* ========================================================================= *)

needs "common/fips203/properties/mlkem_native_image.ml";;
needs "common/consttime.ml";;

let VAL_WORD_NUMERAL_CONV tm =
  match tm with
    Comb(Const("val",_),Comb(Const("word",_),n)) when is_numeral n ->
      WORD_REDUCE_CONV tm
  | _ -> failwith "VAL_WORD_NUMERAL_CONV";;
