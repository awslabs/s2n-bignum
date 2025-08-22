use_file_raise_failure := true;;
needs "common/aes.ml";;
loadt "arm/proofs/aes_encrypt_spec.ml";;
loadt "arm/proofs/aes_decrypt_spec.ml";;

let pp_print_num fmt tm =
  let n = dest_numeral tm in
  pp_print_string fmt (string_of_num_hex n) in
install_user_printer("pp_print_num",pp_print_num);;

(*******************************************)
(* Specification *)

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
        (word_join (word_join (EL 15 bs) (EL 14 bs) : int16) (word_join (EL 13 bs) (EL 12 bs) : int16) : int32)
        (word_join (word_join (EL 11 bs) (EL 10 bs) : int16) (word_join (EL 9 bs) (EL 8 bs) : int16) : int32) : int64)
      (word_join
        (word_join (word_join (EL 7 bs) (EL 6 bs) : int16) (word_join (EL 5 bs) (EL 4 bs) : int16) : int32)
        (word_join (word_join (EL 3 bs) (EL 2 bs) : int16) (word_join (EL 1 bs) (EL 0 bs) : int16) : int32) : int64)`;;

let int128_to_bytes = define
  `int128_to_bytes (w : int128) : byte list =
    [word_subword w (0, 8);
     word_subword w (8, 8);
     word_subword w (16, 8);
     word_subword w (24, 8);
     word_subword w (32, 8);
     word_subword w (40, 8);
     word_subword w (48, 8);
     word_subword w (56, 8);
     word_subword w (64, 8);
     word_subword w (72, 8);
     word_subword w (80, 8);
     word_subword w (88, 8);
     word_subword w (96, 8);
     word_subword w (104, 8);
     word_subword w (112, 8);
     word_subword w (120, 8)]`;;

(* Multiplication by the primitive element \alpha in GF(2^128) *)
let GF_128_mult_by_primitive = new_definition
  `GF_128_mult_by_primitive
    (tweak:(128)word) =
    let shifted = word_shl tweak 1 in
    let mask = word_ishr tweak 127 in
    word_xor (word_and mask (word 0x87)) shifted`;;

let FST3 = define `FST3 (x:a#b#c) = FST x`;;
let SND3 = define `SND3 (x:a#b#c) = FST (SND x)`;;
let THD3 = define `THD3 (x:a#b#c) = SND (SND x)`;;

let eth = prove_general_recursive_function_exists
 `?aes256_xts_decrypt_rec.
    ! (i:num) (m:num) (C:byte list) (iv:int128) (key1:int128 list).
    aes256_xts_decrypt_rec i m C iv key1 : (byte list)#int128#num =
    if m < i then ([], iv, i)
    else
      let current_block = bytes_to_int128 (SUB_LIST (i * 16, 16) C) in
      let curr = int128_to_bytes (aes256_xts_decrypt_round current_block iv key1) in
      let iv = GF_128_mult_by_primitive iv in
      let res = aes256_xts_decrypt_rec (i + 1) m C iv key1 in
      (APPEND curr (FST3 res), SND3 res, THD3 res)`;;

let wfth = prove(hd(hyp eth),
  EXISTS_TAC `MEASURE (\(i:num,m:num,C:byte list,iv:int128,key1:int128 list). (m + 1) - i)` THEN
  REWRITE_TAC[WF_MEASURE; MEASURE] THEN ARITH_TAC);;

let exists_lemma = PROVE_HYP wfth eth;;

(* Note: results are stored in LSByte to MSByte *)
let aes256_xts_decrypt_rec = new_specification ["aes256_xts_decrypt_rec"] exists_lemma;;

let cipher_stealing = new_definition
  `cipher_stealing (block:byte list) (tail:byte list) (tail_len:num)
    (iv:int128) (key1:int128 list): (byte list)#(byte list) =
    let iv_last = GF_128_mult_by_primitive iv in
    let PP = int128_to_bytes (aes256_xts_decrypt_round (bytes_to_int128 block) iv_last key1) in
    let Pm = SUB_LIST (0, tail_len) PP in
    let CP = SUB_LIST (tail_len, 16 - tail_len) PP in
    let CC = bytes_to_int128 (APPEND tail CP) in
    let Pm1 = int128_to_bytes (aes256_xts_decrypt_round CC iv key1) in
    (Pm1, Pm)`;;

(* Depending on the tail, either do one block decryption or do cipher stealing *)
let aes256_xts_decrypt_tail = new_definition
  `aes256_xts_decrypt_tail (i:num) (tail_len:num) (C:byte list) (iv:int128) (key1:int128 list) : byte list =
    if tail_len = 0 then
      let Cm1 = bytes_to_int128 (SUB_LIST (i * 16, 16) C) in
      int128_to_bytes (aes256_xts_decrypt_round Cm1 iv key1)
    else
      let Cm1 = SUB_LIST (i * 16, 16) C in
      let Ctail = SUB_LIST ((i + 1) * 16, tail_len) C in

      let res_cs = cipher_stealing Cm1 Ctail tail_len iv key1 in
      APPEND (FST res_cs) (SND res_cs)`;;

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
   perror: Error output plaintext in case of invalid input length

   return: Output plaintext as a byte list

   When input len < 16, the function returns perror,
   which will be the initial value stored in output address.
*)
(* TODO: Challenge lemma: proving that the output is of same length as input *)
(* TODO: Double check if IEEE and NIST spec talks about the error case len < 16 *)
(* TODO: Double check the pseudo code in the spec for tweak caculation in ANEX c *)
let aes256_xts_decrypt = new_definition
  `aes256_xts_decrypt
    (C:byte list) (len:num) (iv:int128) (key1:int128 list) (key2:int128 list) (err:byte list) : byte list =
    if len < 16 then
      err
    else
      let tail = len MOD 16 in
      let m = (len - tail) DIV 16 in
      let i = 0 in

      let iv = xts_init_tweak iv key2 in
      if m < 2 then
        aes256_xts_decrypt_tail i tail C iv key1
      else
        let res = aes256_xts_decrypt_rec 0 (m - 2) C iv key1 in
        let Ptail = aes256_xts_decrypt_tail (THD3 res) tail C (SND3 res) key1 in
        APPEND (FST3 res) Ptail`;;

(*******************************************)
(* Test vectors *)

(*
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

1 block
iv: 0000000000000000000000123456789a
out: 88c87a8644e587dc7e3057edf2a80cc3
in: 0f0e0d0c0b0a09080706050403020100

1 block + 6 bytes
iv: 0000000000000000000000123456789a
out: 57edf2a80cc389a4b92cde579f93da9ae5cc8b18e875
in: 1514131211100f0e0d0c0b0a0908070605040302010

3 blocks + 3 bytes
iv: 0000000000000000000000123456789a
out: 41c2e1e4a22c106ace4c926e3725aa6877a4be5b7b62cb514595696240d72889208c3488c87a8644e587dc7e3057edf2a80cc3
in: 3231302f2e2d2c2b2a292827262524232221201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a09080706050403020100

*)

let c0 = new_definition
  `c0 = [word 0xc3; word 0x0c; word 0xa8; word 0xf2
  ; word 0xed; word 0x57; word 0x30; word 0x7e
  ; word 0xdc; word 0x87; word 0xe5; word 0x44
  ; word 0x86; word 0x7a; word 0xc8; word 0x88] : byte list`;;
let p0 = new_definition
  `p0 = [word 0x00; word 0x01; word 0x02; word 0x03
  ; word 0x04; word 0x05; word 0x06; word 0x07
  ; word 0x08; word 0x09; word 0x0a; word 0x0b
  ; word 0x0c; word 0x0d; word 0x0e; word 0x0f] : byte list`;;

let c1 = new_definition
  `c1 = [ word 0x75; word 0xe8; word 0x18; word 0x8b;
      word 0xcc; word 0xe5; word 0x9a; word 0xda;
      word 0x93; word 0x9f; word 0x57; word 0xde;
      word 0x2c; word 0xb9; word 0xa4; word 0x89;
      word 0xc3; word 0x0c; word 0xa8; word 0xf2;
      word 0xed; word 0x57 ] : byte list`;;
let p1 = new_definition
  `p1 = [word 0x0; word 0x1; word 0x2; word 0x3;
      word 0x4; word 0x5; word 0x6; word 0x7;
      word 0x8; word 0x9; word 0xa; word 0xb;
      word 0xc; word 0xd; word 0xe; word 0xf;
      word 0x10; word 0x11; word 0x12; word 0x13;
      word 0x14; word 0x15] : byte list`;;

let c2 = new_definition
  `c2 = [ word 0xc3; word 0x0c; word 0xa8; word 0xf2;
      word 0xed; word 0x57; word 0x30; word 0x7e;
      word 0xdc; word 0x87; word 0xe5; word 0x44;
      word 0x86; word 0x7a; word 0xc8; word 0x88;
      word 0x34; word 0x8c; word 0x20; word 0x89;
      word 0x28; word 0xd7; word 0x40; word 0x62;
      word 0x69; word 0x95; word 0x45; word 0x51;
      word 0xcb; word 0x62; word 0x7b; word 0x5b;
      word 0xbe; word 0xa4; word 0x77; word 0x68;
      word 0xaa; word 0x25; word 0x37; word 0x6e;
      word 0x92; word 0x4c; word 0xce; word 0x6a;
      word 0x10; word 0x2c; word 0xa2; word 0xe4;
      word 0xe1; word 0xc2; word 0x41 ] : byte list`;;
let p2 = new_definition
  `p2 = [word 0x0; word 0x1; word 0x2; word 0x3;
      word 0x4; word 0x5; word 0x6; word 0x7;
      word 0x8; word 0x9; word 0xa; word 0xb;
      word 0xc; word 0xd; word 0xe; word 0xf;
      word 0x10; word 0x11; word 0x12; word 0x13;
      word 0x14; word 0x15; word 0x16; word 0x17;
      word 0x18; word 0x19; word 0x1a; word 0x1b;
      word 0x1c; word 0x1d; word 0x1e; word 0x1f;
      word 0x20; word 0x21; word 0x22; word 0x23;
      word 0x24; word 0x25; word 0x26; word 0x27;
      word 0x28; word 0x29; word 0x2a; word 0x2b;
      word 0x2c; word 0x2d; word 0x2e; word 0x2f;
      word 0x30; word 0x31; word 0x32] : byte list`;;

let iv_tweak = new_definition
  `iv_tweak = (word 0x0000000000000000000000123456789a) : int128`;;

let perror = new_definition
  `perror = [ word 0; word 0; word 0; word 0
   ; word 0; word 0; word 0; word 0
   ; word 0; word 0; word 0; word 0
   ; word 0; word 0; word 0; word 0] : byte list`;;

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

(*******************************************)
(* Conversions *)
let XTS_INIT_TWEAK_CONV =
  REWR_CONV xts_init_tweak THENC AESENC_HELPER_CONV;;

(* (REWRITE_CONV [iv_tweak;KEY2] THENC XTS_INIT_TWEAK_CONV)
  `xts_init_tweak iv_tweak KEY2`;; *)

let AES256_XTS_DECRYPT_ROUND_CONV =
  REWRITE_CONV [aes256_xts_decrypt_round] THENC
  SUBLET_CONV WORD_RED_CONV THENC
  let_CONV THENC
  SUBLET_CONV AESDEC_HELPER_CONV THENC
  let_CONV THENC WORD_RED_CONV;;

(* (REWRITE_CONV [iv_tweak; KEY2] THENC AES256_XTS_DECRYPT_ROUND_CONV)
  `aes256_xts_decrypt_round iv_tweak iv_tweak KEY2`;; *)

let XTSDEC_1BLOCK_HELPER_CONV =
  REWR_CONV aes256_xts_decrypt_1block THENC
  REWRITE_CONV [xts_init_tweak] THENC
  SUBLET_CONV AESENC_HELPER_CONV THENC
  let_CONV THENC
  AES256_XTS_DECRYPT_ROUND_CONV;;

(*162 seconds
time prove (`aes256_xts_decrypt_1block
  (word 0x88c87a8644e587dc7e3057edf2a80cc3)
  (word 0x0000000000000000000000123456789a)
  KEY1 KEY2 = word 0x0f0e0d0c0b0a09080706050403020100`,
  CONV_TAC(LAND_CONV XTSDEC_1BLOCK_HELPER_CONV) THEN REFL_TAC);;
*)

let EL_16_8_CLAUSES =
  let pat = `EL n [x0;x1;x2;x3;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14;x15]:byte` in
  map (fun n -> EL_CONV(subst [mk_small_numeral n,`n:num`] pat)) (0--15);;

let BYTES_TO_INT128_CONV =
  REWRITE_CONV [bytes_to_int128] THENC
  REWRITE_CONV EL_16_8_CLAUSES THENC
  DEPTH_CONV WORD_RED_CONV;;

(* (REWRITE_CONV [c0] THENC BYTES_TO_INT128_CONV) `bytes_to_int128 c0`;; *)

let INT128_TO_BYTES_CONV =
  REWRITE_CONV [int128_to_bytes] THENC
  DEPTH_CONV WORD_RED_CONV;;

(* INT128_TO_BYTES_CONV `int128_to_bytes (word 0x0102030405060708090a0b0c0d0e0f)`;; *)

let GF_128_MULT_BY_PRIMITIVE_CONV =
  REWRITE_CONV [GF_128_mult_by_primitive] THENC
  REPEATC let_CONV THENC
  DEPTH_CONV WORD_RED_CONV;;

(* GF_128_MULT_BY_PRIMITIVE_CONV
  `GF_128_mult_by_primitive (word 0xffffffffffffffffffffffffffffffff)`;; *)

let rec AES256_XTS_DECRYPT_REC_CONV tm =
  let BASE_CONV =
    REWR_CONV aes256_xts_decrypt_rec THENC
    DEPTH_CONV NUM_RED_CONV in
  let INDUCT_CONV =
    REWR_CONV aes256_xts_decrypt_rec THENC
    DEPTH_CONV NUM_RED_CONV THENC
    ONCE_DEPTH_CONV SUB_LIST_CONV THENC
    ONCE_DEPTH_CONV BYTES_TO_INT128_CONV THENC let_CONV THENC
    SUBLET_CONV (RAND_CONV AES256_XTS_DECRYPT_ROUND_CONV) THENC
    SUBLET_CONV INT128_TO_BYTES_CONV THENC let_CONV THENC
    SUBLET_CONV GF_128_MULT_BY_PRIMITIVE_CONV THENC let_CONV THENC
    SUBLET_CONV AES256_XTS_DECRYPT_REC_CONV THENC let_CONV THENC
    REWRITE_CONV [FST3;SND3;THD3;APPEND] in
  match tm with
  | Comb
       (Comb
         (Comb
           (Comb
             (Comb (Const ("aes256_xts_decrypt_rec", _), i), m),
            _),
          _),
        _) ->
    if dest_numeral m </ dest_numeral i
    then BASE_CONV tm
    else INDUCT_CONV tm
  | _ -> failwith "AES256_XTS_DECRYPT_REC_CONV: inapplicable";;

(*
(REWRITE_CONV [iv_tweak;KEY1;KEY2;c0] THENC AES256_XTS_DECRYPT_REC_CONV)
  `aes256_xts_decrypt_rec 0 0 c0 iv_tweak KEY1`;;
  *)

let CIPHER_STEALING_CONV =
  REWRITE_CONV [cipher_stealing] THENC
  SUBLET_CONV GF_128_MULT_BY_PRIMITIVE_CONV THENC let_CONV THENC
  SUBLET_CONV (ONCE_DEPTH_CONV BYTES_TO_INT128_CONV) THENC
  SUBLET_CONV (RAND_CONV AES256_XTS_DECRYPT_ROUND_CONV) THENC
  SUBLET_CONV INT128_TO_BYTES_CONV THENC let_CONV THENC
  SUBLET_CONV SUB_LIST_CONV THENC let_CONV THENC
  SUBLET_CONV (DEPTH_CONV NUM_RED_CONV) THENC (* For evaluating 16 - tail_len *)
  SUBLET_CONV SUB_LIST_CONV THENC let_CONV THENC
  SUBLET_CONV (ONCE_DEPTH_CONV (REWRITE_CONV [APPEND])) THENC
  SUBLET_CONV BYTES_TO_INT128_CONV THENC let_CONV THENC
  SUBLET_CONV (RAND_CONV AES256_XTS_DECRYPT_ROUND_CONV) THENC
  SUBLET_CONV INT128_TO_BYTES_CONV THENC let_CONV;;

(*
(REWRITE_CONV [c0;iv_tweak;KEY1] THENC CIPHER_STEALING_CONV)
  `cipher_stealing c0 [(word 0x0)] 1 iv_tweak KEY1`;;
  *)

let AES256_XTS_DECRYPT_TAIL_CONV tm =
  let ONE_BLOCK_CONV =
    REWR_CONV aes256_xts_decrypt_tail THENC
    DEPTH_CONV NUM_RED_CONV THENC
    SUBLET_CONV (RAND_CONV SUB_LIST_CONV) THENC
    SUBLET_CONV BYTES_TO_INT128_CONV THENC let_CONV THENC
    RAND_CONV AES256_XTS_DECRYPT_ROUND_CONV THENC
    INT128_TO_BYTES_CONV in
  let ONE_BLOCK_AND_TAIL_CONV =
    REWR_CONV aes256_xts_decrypt_tail THENC
    DEPTH_CONV NUM_RED_CONV THENC
    SUBLET_CONV SUB_LIST_CONV THENC let_CONV THENC
    SUBLET_CONV SUB_LIST_CONV THENC let_CONV THENC
    SUBLET_CONV CIPHER_STEALING_CONV THENC let_CONV THENC
    REWRITE_CONV [FST;SND] THENC REWRITE_CONV [APPEND] in
  match tm with
  | Comb
       (Comb
         (Comb
           (Comb
             (Comb
               (Const ("aes256_xts_decrypt_tail", _), _), tail_len),
            _),
          _),
        _) ->
    if dest_numeral tail_len =/ num 0
    then ONE_BLOCK_CONV tm
    else ONE_BLOCK_AND_TAIL_CONV tm
  | _ -> failwith "AES256_XTS_DECRYPT_TAIL_CONV: inapplicable";;

(*
(REWRITE_CONV [c0;iv_tweak;KEY1;KEY2] THENC AES256_XTS_DECRYPT_TAIL_CONV)
  `aes256_xts_decrypt_tail 0 0 c0 iv_tweak KEY1`;;

(REWRITE_CONV [c1;iv_tweak;KEY1;KEY2] THENC AES256_XTS_DECRYPT_TAIL_CONV)
  `aes256_xts_decrypt_tail 0 6 c1 iv_tweak KEY1`;;
*)

let AES256_XTS_DECRYPT_CONV tm =
  let ERROR_CONV =
    REWR_CONV aes256_xts_decrypt THENC
    DEPTH_CONV NUM_RED_CONV in
  let MORE_THAN_2_CONV =
    REWRITE_CONV [FST3;SND3;THD3] THENC
    SUBLET_CONV AES256_XTS_DECRYPT_REC_CONV THENC let_CONV THENC
    SUBLET_CONV AES256_XTS_DECRYPT_TAIL_CONV THENC let_CONV THENC
    REWRITE_CONV [APPEND] in
  let BODY_CONV =
    REWR_CONV aes256_xts_decrypt THENC
    DEPTH_CONV NUM_RED_CONV THENC let_CONV THENC
    DEPTH_CONV NUM_RED_CONV THENC let_CONV THENC let_CONV THENC
    SUBLET_CONV XTS_INIT_TWEAK_CONV THENC let_CONV THENC
    DEPTH_CONV NUM_RED_CONV THENC
    (AES256_XTS_DECRYPT_TAIL_CONV ORELSEC MORE_THAN_2_CONV) in
  match tm with
  | Comb
   (Comb
     (Comb
       (Comb
         (Comb
           (Comb
             (Const ("aes256_xts_decrypt", _), _), len),
         _),
       _),
     _),
   _) ->
    if dest_numeral len </ num 16
    then ERROR_CONV tm
    else BODY_CONV tm
  | _ -> failwith "AES256_XTS_DECRYPT_CONV: inapplicable";;

(*
(REWRITE_CONV [perror] THENC AES256_XTS_DECRYPT_CONV)
  `aes256_xts_decrypt c0 5 iv_tweak KEY1 KEY2 perror`;;

(REWRITE_CONV [c0;iv_tweak;KEY1;KEY2;perror] THENC AES256_XTS_DECRYPT_CONV)
  `aes256_xts_decrypt c0 16 iv_tweak KEY1 KEY2 perror`;;

(* 165 seconds *)
time (REWRITE_CONV [iv_tweak;KEY1;KEY2;perror] THENC AES256_XTS_DECRYPT_CONV)
  `aes256_xts_decrypt [word 0xc3; word 0x0c; word 0xa8; word 0xf2
  ; word 0xed; word 0x57; word 0x30; word 0x7e
  ; word 0xdc; word 0x87; word 0xe5; word 0x44
  ; word 0x86; word 0x7a; word 0xc8; word 0x88
  ; word 0xc3; word 0x0c; word 0xa8; word 0xf2
  ; word 0xed; word 0x57; word 0x30; word 0x7e
  ; word 0xdc; word 0x87; word 0xe5; word 0x44
  ; word 0x86; word 0x7a; word 0xc8; word 0x88
  ; word 0x00]
  33 iv_tweak KEY1 KEY2 perror`;;
*)

(*******************************************)
(* Tests *)

(* 1 block : 81 second *)
time prove (`aes256_xts_decrypt c0 16 iv_tweak KEY1 KEY2 perror = p0`,
  CONV_TAC(LAND_CONV (REWRITE_CONV [c0;iv_tweak;KEY1;KEY2;perror] THENC AES256_XTS_DECRYPT_CONV)) THEN
  REWRITE_TAC [p0] THEN REFL_TAC);;

(* 1 block + 6 bytes : 121 seconds *)
time prove(`aes256_xts_decrypt c1 22 iv_tweak KEY1 KEY2 perror = p1`,
  CONV_TAC(LAND_CONV (REWRITE_CONV [c1;iv_tweak;KEY1;KEY2;perror;p1] THENC AES256_XTS_DECRYPT_CONV)) THEN
  REWRITE_TAC [p1] THEN REFL_TAC);;

(* 3 blocks + 3 bytes : 206 seconds *)
time prove(`aes256_xts_decrypt c2 51 iv_tweak KEY1 KEY2 perror = p2`,
  CONV_TAC(LAND_CONV (REWRITE_CONV [c2;iv_tweak;KEY1;KEY2;perror;p2] THENC AES256_XTS_DECRYPT_CONV)) THEN
  REWRITE_TAC [p2] THEN REFL_TAC);;
