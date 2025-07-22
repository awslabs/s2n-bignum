use_file_raise_failure := true;;
needs "common/aes.ml";;
loadt "arm/proofs/aes_encrypt_spec.ml";;
loadt "arm/proofs/aes_decrypt_spec.ml";;

let pp_print_num fmt tm =
  let n = dest_numeral tm in
  pp_print_string fmt (string_of_num_hex n) in
install_user_printer("pp_print_num",pp_print_num);;

(*
IEEE Standard for Cryptographic Protection of
Data on Block-Oriented Storage Devices
https://ieeexplore.ieee.org/stamp/stamp.jsp?tp=&arnumber=8637988

Section 5.4.1

a) T ← AES-enc(Key2, i) ⊗ αj
b) CC ← C ⊕ T
c) PP ← AES-dec(Key1, CC)
d) P ← PP ⊕ T

*)

let xts_init_tweak = new_definition
  `xts_init_tweak (iv:int128) (key_schedule:int128 list) =
    aes256_encrypt iv key_schedule`;;

let aes256_xts_decrypt_round = new_definition
  `aes256_xts_decrypt_round (C:int128) (tk:int128) (key_schedule:int128 list) =
    let CC = word_xor C tk in
    let PP = aes256_decrypt CC key_schedule in
    word_xor PP tk`;;

let aes256_xts_decrypt_1block = new_definition
  `aes256_xts_decrypt_1block
    (C:int128) (iv:int128) (key1:int128 list) (key2:int128 list) =
    let tk = xts_init_tweak iv key2 in
    aes256_xts_decrypt_round C tk key1`;;


(* Test vector:
key1:
c70a951e84370d1836bdd387607e94e5
7ead95d6f74bf6b3103340cce21b473d
298c296cdf3241d53d0757ddbebda060
89e66365e778b67ff22807f1cdc91c8f
f6be68b9e235160883baf7bd2340b902
6e9ed51a1550b18e3fe11b7e185c513e
148b7eb1618fe1b5a0fa4ebf336ae76e
7bce64942ab1aaf027bd4a40982968cd
75049f04c175af0a9390a9d1d91a6526
517fce640d0ce0b0bf94228de7e3085d
b471300e52e506db4a8accf7a81afe26
5c732ed4b298c23d58772ad0be94ce31
e69436d5186fca2ce29032d11463c620
eeebece9eaefe8ede6e3e4e1e2e7e0e5
f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff

key2:
b0b1b2b3b4b5b6b7b8b9babbbcbdbebf
a0a1a2a3a4a5a6a7a8a9aaabacadaeaf
0ae0323bba5180880ee4363fb65d8c84
67e123e2c740814163e527e6cb4c8d4d
908df02c9a6dc217203c429f2ed874a0
685584790fb4a79bc8f426daab11013c
b241f85f22cc0873b8a1ca64989d88fb
338745cb5bd2c1b2546666299c9240f3
af72a5d51d335d8a3fff55f9875e9f9d
d9e1a4a0ea66e16bb1b420d9e5d246f0
ead5ca6245a76fb75894323d676b67c4
e0e257483903f3e8d365128362d1325a
c26c685728b9a2356d1ecd82358affbf
4d05c122ade7966a94e4658247817701
21a29367e3cefb30cb775905a6699487

iv: 0000000000000000000000123456789a

out: 88c87a8644e587dc7e3057edf2a80cc3

in: 0f0e0d0c0b0a09080706050403020100
 *)

 let KEY1 = new_definition `KEY1:int128 list =
  [ word 0xc70a951e84370d1836bdd387607e94e5
  ; word 0x7ead95d6f74bf6b3103340cce21b473d
  ; word 0x298c296cdf3241d53d0757ddbebda060
  ; word 0x89e66365e778b67ff22807f1cdc91c8f
  ; word 0xf6be68b9e235160883baf7bd2340b902
  ; word 0x6e9ed51a1550b18e3fe11b7e185c513e
  ; word 0x148b7eb1618fe1b5a0fa4ebf336ae76e
  ; word 0x7bce64942ab1aaf027bd4a40982968cd
  ; word 0x75049f04c175af0a9390a9d1d91a6526
  ; word 0x517fce640d0ce0b0bf94228de7e3085d
  ; word 0xb471300e52e506db4a8accf7a81afe26
  ; word 0x5c732ed4b298c23d58772ad0be94ce31
  ; word 0xe69436d5186fca2ce29032d11463c620
  ; word 0xeeebece9eaefe8ede6e3e4e1e2e7e0e5
  ; word 0xf0f1f2f3f4f5f6f7f8f9fafbfcfdfeff
  ]`;;

let KEY2 = new_definition `KEY2:int128 list =
  [ word 0xb0b1b2b3b4b5b6b7b8b9babbbcbdbebf
  ; word 0xa0a1a2a3a4a5a6a7a8a9aaabacadaeaf
  ; word 0x0ae0323bba5180880ee4363fb65d8c84
  ; word 0x67e123e2c740814163e527e6cb4c8d4d
  ; word 0x908df02c9a6dc217203c429f2ed874a0
  ; word 0x685584790fb4a79bc8f426daab11013c
  ; word 0xb241f85f22cc0873b8a1ca64989d88fb
  ; word 0x338745cb5bd2c1b2546666299c9240f3
  ; word 0xaf72a5d51d335d8a3fff55f9875e9f9d
  ; word 0xd9e1a4a0ea66e16bb1b420d9e5d246f0
  ; word 0xead5ca6245a76fb75894323d676b67c4
  ; word 0xe0e257483903f3e8d365128362d1325a
  ; word 0xc26c685728b9a2356d1ecd82358affbf
  ; word 0x4d05c122ade7966a94e4658247817701
  ; word 0x21a29367e3cefb30cb775905a6699487
  ]`;;

let XTSDEC_1BLOCK_HELPER_CONV =
  REWR_CONV aes256_xts_decrypt_1block THENC
  REWRITE_CONV [xts_init_tweak] THENC
  SUBLET_CONV (AESENC_HELPER_CONV KEY2) THENC
  let_CONV THENC
  REWRITE_CONV [aes256_xts_decrypt_round] THENC
  SUBLET_CONV (DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV)) THENC
  PRINT_TERM_CONV THENC
  let_CONV THENC
  SUBLET_CONV (AESDEC_HELPER_CONV KEY1) THENC
  let_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV)
  ;;

(*162 seconds
time prove (`aes256_xts_decrypt_1block
  (word 0x88c87a8644e587dc7e3057edf2a80cc3)
  (word 0x0000000000000000000000123456789a)
  KEY1 KEY2 = word 0x0f0e0d0c0b0a09080706050403020100`,
  CONV_TAC(LAND_CONV XTSDEC_1BLOCK_HELPER_CONV) THEN REFL_TAC);;
*)

(*******************************************)
(* AES-XTS decryption full *)
(* Note: the implementation sequences the calculation of the tweak
   for each block, however, the specification will calculate the tweak
   from the very beginning for each block. We write the specification
   in the sequenced version for proof simplicity.
*)

(* Helper functions derived from Amanda's code:
  https://github.com/amanda-zx/s2n-bignum/blob/sha512/arm/sha512/sha512_specs.ml#L360
*)
let bytes_to_int128 = define
  `bytes_to_int128 (bs : byte list) : int128 =
    word_join
      (word_join
        (word_join (word_join (EL 7 bs) (EL 6 bs) : int16) (word_join (EL 5 bs) (EL 4 bs) : int16) : int32)
        (word_join (word_join (EL 3 bs) (EL 2 bs) : int16) (word_join (EL 1 bs) (EL 8 bs) : int16) : int32) : int64)
      (word_join
        (word_join (word_join (EL 7 bs) (EL 6 bs) : int16) (word_join (EL 5 bs) (EL 4 bs) : int16) : int32)
        (word_join (word_join (EL 3 bs) (EL 2 bs) : int16) (word_join (EL 1 bs) (EL 0 bs) : int16) : int32) : int64)`;;

let int128_to_bytes = define
  `int128_to_bytes (w : int128) : byte list =
    [word_subword w (0, 1);
     word_subword w (1, 1);
     word_subword w (2, 1);
     word_subword w (3, 1);
     word_subword w (4, 1);
     word_subword w (5, 1);
     word_subword w (6, 1);
     word_subword w (7, 1);
     word_subword w (8, 1);
     word_subword w (9, 1);
     word_subword w (10, 1);
     word_subword w (11, 1);
     word_subword w (12, 1);
     word_subword w (13, 1);
     word_subword w (14, 1);
     word_subword w (15, 1)]`;;

(* Multiplication by the primitive element \alpha in GF(2^128) *)
let GF_128_mult_by_primitive = new_definition
  `GF_128_mult_by_primitive
    (tweak:(128)word) =
    let shifted = word_shl tweak 1 in
    let mask = word_ishr tweak 127 in
    word_xor (word_and mask (word 0x87)) shifted`;;

let FST3 = define
  `FST3 (x:a#b#c) = FST x`;;
let SND3 = define
  `SND3 (x:a#b#c) = FST (SND x)`;;
let THD3 = define
  `THD3 (x:a#b#c) = SND (SND x)`;;

let eth = prove_general_recursive_function_exists
 `?aes256_xts_decrypt_rec.
    ! (i:num) (m:num) (C:byte list) (iv:int128) (key1:int128 list) (key2:int128 list).
    aes256_xts_decrypt_rec i m C iv key1 key2 : (byte list)#int128#num =
    if m < i then ([], iv, i)
    else
      let current_block = bytes_to_int128 (SUB_LIST (i * 16, 16) C) in
      let curr = int128_to_bytes (aes256_xts_decrypt_round current_block iv key1) in
      let iv = GF_128_mult_by_primitive iv in
      let res = aes256_xts_decrypt_rec (i + 1) m C iv key1 key2 in
      (APPEND curr (FST3 res), SND3 res, THD3 res)`;;

let wfth = prove(hd(hyp eth),
  EXISTS_TAC `MEASURE (\(i:num,m:num,C:byte list,iv:int128,key1:int128 list,key2:int128 list). (m + 1) - i)` THEN
  REWRITE_TAC[WF_MEASURE; MEASURE] THEN ARITH_TAC);;

let exists_lemma = PROVE_HYP wfth eth;;

(* Note: results are stored in LSByte to MSByte *)
let aes256_xts_decrypt_rec = new_specification ["aes256_xts_decrypt_rec"] exists_lemma;;

(* Note: last block is padded to make it suitable for int128_to_bytes *)
let cipher_stealing = new_definition
  `cipher_stealing (block:int128) (tail:int128) (tail_len:num) (iv:int128) : int128#int128 =
    let iv_last = GF_128_mult_by_primitive iv in
    let PP = aes256_xts_decrypt_round block iv_last key1 in
    let Pm = word_subword PP (0, tail_len) in
    let CP = word_subword PP (tail_len, 16 - tail_len) in
    let CC = word_join (word_subword tail (0,tail_len)) CP in
    let Pm1 = aes256_xts_decrypt_round CC iv key1 in
    (Pm1, (word_zx Pm))`;;

(* Depending on the tail, either do one block decryption or do cipher stealing *)
let aes256_xts_decrypt_tail = new_definition
  `aes256_xts_decrypt_tail (i:num) (m:num) (tail:num) 
    (C:byte list) (iv:int128) (key1:int128 list) (key2:int128 list) : byte list =
    if tail = 0 then
      let Cm1 = bytes_to_int128 (SUB_LIST (i * 16, 16) C) in
      int128_to_bytes (aes256_xts_decrypt_round Cm1 iv key1)
    else
      let Cm1 = bytes_to_int128 (SUB_LIST (i * 16, 16) C) in
      let padded_tail = APPEND (SUB_LIST ((i + 1) * 16, tail) C) (REPLICATE (16 - tail) (word 0)) in
      let Ctail = bytes_to_int128 padded_tail in

      let res_cs = cipher_stealing Cm1 Ctail tail iv in
      let Pm1 = int128_to_bytes (FST res_cs) in
      let Ptail = SUB_LIST (0, tail) (int128_to_bytes (SND res_cs)) in
      APPEND Pm1 Ptail`;;

(* The main decryption function *)
(* Note: the specification does not handle the case of len < 16, which is
   handled in the implementation. *)

(* AES256-XTS assumes there is at least one block in input *)
(*
   C: Input ciphertext represented as a byte list
   len: Length of C
   iv: Initialization vector (tweak) as an int128
   key1: Key schedule for AES-256 decryption
   key2: Key schedule for AES-256 encryption for the tweak
   P_error: Error output plaintext in case of invalid input length

   return: Output plaintext as a byte list

   When input len < 16, the function returns P_error,
   which will be the initial value stored in output address.
*)
(* TODO: Challenge lemma: proving that the output is of same length as input *)
(* TODO: Double check if NIST spec talks about the error case len < 16 *)
(* TODO: Double check the pseudo code in the spec for tweak caculation in ANEX c *)
let aes256_xts_decrypt = new_definition
  `aes256_xts_decrypt
    (C:byte list) (len:num) (iv:int128) (key1:int128 list) (key2:int128 list) (P_error:byte list) : byte list =
    if len < 16 then
      P_error
    else
      let tail = len MOD 16 in
      let m = (len - tail) DIV 16 in
      let i = 0 in

      let iv = xts_init_tweak iv key2 in
      if m < 2 then
        aes256_xts_decrypt_tail i m tail C iv key1 key2
      else
        let res = aes256_xts_decrypt_rec 0 (m - 2) C iv key1 key2 in
        let Ptail = aes256_xts_decrypt_tail (THD3 res) m tail C (SND3 res) key1 key2 in
        APPEND (FST3 res) Ptail`;;
      `;;
