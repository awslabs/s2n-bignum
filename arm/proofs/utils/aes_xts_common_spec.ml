(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)
 (* Common definitions between AES-XTS encrypt and decrypt specs. *)

needs "common/aes.ml";;
needs "arm/proofs/utils/aes_encrypt_spec.ml";;
(*
let pp_print_num fmt tm =
  let n = dest_numeral tm in
  pp_print_string fmt (string_of_num_hex n) in
install_user_printer("pp_print_num",pp_print_num);;
*)

(* Helper functions derived from Amanda's code:
   https://github.com/amanda-zx/s2n-bignum/blob/sha512/arm/sha512/sha512_specs.ml#L360 *)

 let bytes_to_int128 = define
  `bytes_to_int128 (bs : byte list) : int128 =
    word_join
      (word_join
        (word_join (word_join (EL 15 bs) (EL 14 bs) : int16) (word_join (EL 13 bs) (EL 12 bs) : int16) : int32)
        (word_join (word_join (EL 11 bs) (EL 10 bs) : int16) (word_join (EL 9 bs) (EL 8 bs) : int16) : int32) : int64)
      (word_join
        (word_join (word_join (EL 7 bs) (EL 6 bs) : int16) (word_join (EL 5 bs) (EL 4 bs) : int16) : int32)
        (word_join (word_join (EL 3 bs) (EL 2 bs) : int16) (word_join (EL 1 bs) (EL 0 bs) : int16) : int32) : int64)`;;

let int128_to_bytes = define
  `int128_to_bytes (w : int128) : byte list =
     [word_subword w (0, 8); word_subword w (8, 8); word_subword w (16, 8); word_subword w (24, 8);
      word_subword w (32, 8); word_subword w (40, 8); word_subword w (48, 8); word_subword w (56, 8);
      word_subword w (64, 8); word_subword w (72, 8); word_subword w (80, 8); word_subword w (88, 8);
      word_subword w (96, 8); word_subword w (104, 8); word_subword w (112, 8); word_subword w (120, 8)]`;;

(* XTS tweak initialization - encrypt the IV with key2 *)
let xts_init_tweak = new_definition
  `xts_init_tweak (iv:int128) (key2:int128 list) =
     aes256_encrypt iv key2`;;

(* Note: the implementation sequences the calculation of the tweak for each block,
   however, the specification will calculate the tweak from the very beginning for each block.
   We write the specification in the sequenced version for proof simplicity. *)

(* Multiplication by the primitive element \alpha in GF(2^128) *)
(* Same as the pseudo code of multiplying by \alpha in Annex C of the spec. *)
let GF_128_mult_by_primitive = new_definition
  `GF_128_mult_by_primitive (tweak:(128)word) =
     let shifted = word_shl tweak 1 in
     let mask = word_ishr tweak 127 in
     word_xor (word_and mask (word 0x87)) shifted`;;

let calculate_tweak = new_recursive_definition num_RECURSION
  `calculate_tweak 0 (iv:(128)word) (key2:int128 list) = xts_init_tweak iv key2 /\
   calculate_tweak (SUC n) (iv:(128)word) (key2:int128 list) =
     GF_128_mult_by_primitive (calculate_tweak n iv key2)`;;

(***********************************************)
(* Conversions and test vectors *)

let EL_16_8_CLAUSES =
  let pat = `EL n [x0;x1;x2;x3;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14;x15]:byte` in
  map (fun n -> EL_CONV(subst [mk_small_numeral n,`n:num`] pat)) (0--15);;

let BYTES_TO_INT128_CONV =
  REWR_CONV bytes_to_int128 THENC
  REWRITE_CONV EL_16_8_CLAUSES THENC
  DEPTH_CONV WORD_RED_CONV;;
(*
let ptext = new_definition
  `ptext =
   int128_to_bytes (word 0x0F0E0D0C0B0A09080706050403020100 : int128)`;;

time prove(`bytes_to_int128 ptext
            = (word 0x0f0e0d0c0b0a09080706050403020100 :int128)`,
            CONV_TAC(REWRITE_CONV [ptext;int128_to_bytes] THENC
               LAND_CONV BYTES_TO_INT128_CONV) THEN
            REFL_TAC
          );;
*)

let INT128_TO_BYTES_CONV =
  REWRITE_CONV [int128_to_bytes] THENC
  DEPTH_CONV WORD_RED_CONV;;
(* INT128_TO_BYTES_CONV `int128_to_bytes (word 0x0102030405060708090a0b0c0d0e0f)`;; *)

let GF_128_MULT_BY_PRIMITIVE_CONV =
  REWRITE_CONV [GF_128_mult_by_primitive] THENC
  REPEATC let_CONV THENC
  DEPTH_CONV WORD_RED_CONV;;
(* GF_128_MULT_BY_PRIMITIVE_CONV
  `GF_128_mult_by_primitive (word 0x8b2b4a71228e98aed6aa0ca97775261a)`;; *)

time prove(`GF_128_mult_by_primitive (word 0x8b2b4a71228e98aed6aa0ca97775261a)
            = (word 0x165694e2451d315dad541952eeea4cb3 : int128)`,
            CONV_TAC(LAND_CONV GF_128_MULT_BY_PRIMITIVE_CONV) THEN REFL_TAC
          );;

let XTS_INIT_TWEAK_CONV =
  REWR_CONV xts_init_tweak THENC AESENC_HELPER_CONV;;

let iv1 = new_definition
  `iv1 = (word 0x000000000000000000000000000000FF) : int128`;;

let tweak_key_schedule = new_definition `tweak_key_schedule:int128 list =
  [ word 0x95278333646284239397585326594131
  ; word 0x92459474098205513799931697418802
  ; word 0xD6C4705143E3F36227817741B4162F12
  ; word 0xCD03DBE05F464F9456C44AC5615DD9D3
  ; word 0xE70DA0DB31C9D08A722A23E855AB54A9
  ; word 0x310BE7DBFC083C3BA34E73AFF58A396A
  ; word 0x48822C80AF8F8C5B9E465CD1EC6C7F39
  ; word 0xC9D4E0E8F8DF073304D73B08A79948A7
  ; word 0x0EFACBDA4678E75AE9F76B0177B137D0
  ; word 0x39688B23F0BC6BCB08636CF80CB457F0
  ; word 0xF0D6357CFE2CFEA6B85419FC51A372FD
  ; word 0x41F54DF0789DC6D38821AD188042C1E0
  ; word 0x6B8E46189B58736465748DC2DD20943E
  ; word 0x4E12BD760FE7F086777A3655FF5B9B4D
  ; word 0x70ADE5BA1B23A3A2807BD0C6E50F5D04
  ]`;;

(*
let tmp_xts_tweak = (REWRITE_CONV [iv1; tweak_key_schedule] THENC XTS_INIT_TWEAK_CONV)
    `xts_init_tweak iv1
            tweak_key_schedule`;;
(* Or the following: 36 sec on M3 *)
time prove(`xts_init_tweak iv1
            tweak_key_schedule
            = word 0x8b2b4a71228e98aed6aa0ca97775261a`,
            CONV_TAC(REWRITE_CONV [iv1; tweak_key_schedule] THENC
              LAND_CONV XTS_INIT_TWEAK_CONV)
            THEN REFL_TAC
          );;
*)

let rec CALCULATE_TWEAK_CONV tm =
  let BASE_CONV =
    ONCE_REWRITE_CONV [calculate_tweak] THENC
    XTS_INIT_TWEAK_CONV in
  let INDUCT_CONV =
    RATOR_CONV(LAND_CONV num_CONV) THENC (* ((calculate_tweak 1) iv) key2 *)
        (* PRINT_TERM_CONV THENC*)
    ONCE_REWRITE_CONV [CONJUNCT2 calculate_tweak] THENC
    RAND_CONV CALCULATE_TWEAK_CONV THENC
    GF_128_MULT_BY_PRIMITIVE_CONV in
  match tm with
  | Comb
     (Comb
       (Comb
         (Const ("calculate_tweak",_), n),
       _),
     _) ->
    if dest_numeral n =/ num 0
    then BASE_CONV tm
    else INDUCT_CONV tm
  | _ -> failwith "CALCULATE_TWEAK_CONV: inapplicable";;
(*
(* result: word 0x8b2b4a71228e98aed6aa0ca97775261a, same as xts_init_tweak test above *)
(REWRITE_CONV [iv1;tweak_key_schedule] THENC CALCULATE_TWEAK_CONV) `calculate_tweak 0 iv1 tweak_key_schedule`;;

(* result: word 0x165694e2451d315dad541952eeea4cb3, same as GF_128_mult_by_primitive test above *)
(REWRITE_CONV [iv1;tweak_key_schedule] THENC CALCULATE_TWEAK_CONV) `calculate_tweak 1 iv1 tweak_key_schedule`;;
*)

(*
The following conversion (in its second form) is included directly where it's used in
aes_xts_encrypt.ml and
aes_xts_decrypt.ml

let TWEAK_UPDATE_CONV =
  let ADD_SUC_1 = ARITH_RULE `!n. n + 1 = SUC(n)` in
  let ADD_SUC_2 = ARITH_RULE `!n. n + 2 = SUC(n + 1)` in
  let ADD_SUC_3 = ARITH_RULE `!n. n + 3 = SUC(n + 2)` in
  let ADD_SUC_4 = ARITH_RULE `!n. n + 4 = SUC(n + 3)` in
  let ADD_SUC_5 = ARITH_RULE `!n. n + 5 = SUC(n + 4)` in
  let ADD_SUC_6 = ARITH_RULE `!n. n + 6 = SUC(n + 5)` in
  let ADD_SUC_7 = ARITH_RULE `!n. n + 7 = SUC(n + 6)` in
  let ADD_SUC_8 = ARITH_RULE `!n. n + 8 = SUC(n + 7)` in
  let ADD_SUC_9 = ARITH_RULE `!n. n + 9 = SUC(n + 8)` in
  NUM_REDUCE_CONV THENC
  RATOR_CONV (LAND_CONV (num_CONV ORELSEC
    FIRST_CONV
    [ CHANGED_CONV (ONCE_REWRITE_CONV [ADD_SUC_1]);
      CHANGED_CONV (ONCE_REWRITE_CONV [ADD_SUC_2]);
      CHANGED_CONV (ONCE_REWRITE_CONV [ADD_SUC_3]);
      CHANGED_CONV (ONCE_REWRITE_CONV [ADD_SUC_4]);
      CHANGED_CONV (ONCE_REWRITE_CONV [ADD_SUC_5]);
      CHANGED_CONV (ONCE_REWRITE_CONV [ADD_SUC_6]);
      CHANGED_CONV (ONCE_REWRITE_CONV [ADD_SUC_7]);
      CHANGED_CONV (ONCE_REWRITE_CONV [ADD_SUC_8]);
      CHANGED_CONV (ONCE_REWRITE_CONV [ADD_SUC_9]);])) THENC
  REWRITE_CONV [CONJUNCT2 calculate_tweak] THENC
  GF_128_MULT_BY_PRIMITIVE_CONV;;

let TWEAK_UPDATE_CONV =
 let thms = CONJUNCTS
  ((REWRITE_RULE[ARITH; ADD_0] o
    CONV_RULE EXPAND_CASES_CONV o ARITH_RULE)
    `forall i. i < 9 ==> forall n. n + SUC i = SUC (n + i)`) in
  NUM_REDUCE_CONV THENC
  RATOR_CONV (LAND_CONV (num_CONV ORELSEC
    FIRST_CONV
    (map (fun th -> CHANGED_CONV (ONCE_REWRITE_CONV [th])) thms))) THENC
  REWRITE_CONV [CONJUNCT2 calculate_tweak] THENC
  GF_128_MULT_BY_PRIMITIVE_CONV;;
*)