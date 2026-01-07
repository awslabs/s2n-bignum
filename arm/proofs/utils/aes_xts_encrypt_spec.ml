(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "common/aes.ml";;
needs "arm/proofs/utils/aes_encrypt_spec.ml";;

(*
AES-256-XTS Encryption Algorithm for Any Input Length
Based on IEEE 1619-2007 Standard

This specification implements the complete AES-XTS encryption algorithm
as described in IEEE 1619-2007, Section 5.3, supporting arbitrary input lengths.

Key components:
- Key = Key1 (256-bit data key) || Key2 (256-bit tweak key)
- P is the plaintext of arbitrary length (>= 128 bits)
- i is the value of the 128-bit tweak
- C is the resulting ciphertext

The algorithm processes data in 128-bit blocks with special handling for
the final partial block (if any) using ciphertext stealing.

For each complete block j:
  T_j := AES-enc(Key2, i) MUL alpha^j
  PP_j := P_j XOR T_j
  CC_j := AES-enc(Key1, PP_j)
  C_j := CC_j XOR T_j

Where alpha is the primitive element in GF(2^128) and MUL denotes multiplication
in the Galois field.

For partial final blocks, ciphertext stealing is used as per Section 5.3.2.
*)

(*****************************************)
(* AES-XTS encryption full *)

(* Note: the implementation sequences the calculation of the tweak for each block,
   however, the specification will calculate the tweak from the very beginning for each block.
   We write the specification in the sequenced version for proof simplicity. *)

(* Helper functions derived from Amanda's code:
   https://github.com/amanda-zx/s2n-bignum/blob/sha512/arm/sha512/sha512_specs.ml#L360 *)

(* TODO: put it in a common place to be used with decrypt
     Start *)
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

(* Multiplication by the primitive element \alpha in GF(2^128) *)
let GF_128_mult_by_primitive = new_definition
  `GF_128_mult_by_primitive (tweak:(128)word) =
     let shifted = word_shl tweak 1 in
     let mask = word_ishr tweak 127 in
     word_xor (word_and mask (word 0x87)) shifted`;;

let calculate_tweak = new_recursive_definition num_RECURSION
  `calculate_tweak 0 (iv:(128)word) (key2:int128 list) = xts_init_tweak iv key2 /\
   calculate_tweak (SUC n) (iv:(128)word) (key2:int128 list) =
     GF_128_mult_by_primitive (calculate_tweak n iv key2)`;;

(* TODO: put it in a common place to be used with decrypt
     End *)
(* AES-XTS encryption round function *)
let aes256_xts_encrypt_round = new_definition
  `aes256_xts_encrypt_round (P:int128) (tk:int128) (key1:int128 list) =
     let PP = word_xor P tk in
     let CC = aes256_encrypt PP key1 in
     word_xor CC tk`;;

(* Single block AES-XTS encryption *)
let aes256_xts_encrypt_1block = new_definition
  `aes256_xts_encrypt_1block (P:int128) (iv:int128) (key1:int128 list) (key2:int128 list) =
     let tk = xts_init_tweak iv key2 in
     aes256_xts_encrypt_round P tk key1`;;

(* Recursive encryption function for multiple blocks *)
let eth = prove_general_recursive_function_exists
  `?aes256_xts_encrypt_rec.
     ! (i:num) (m:num) (P:byte list) (iv:int128) (key1:int128 list) (key2:int128 list).
       aes256_xts_encrypt_rec i m P iv key1 key2 : (byte list) =
         if m < i then []
         else
           let current_block = bytes_to_int128 (SUB_LIST (i * 16, 16) P) in
           let twk = calculate_tweak i iv key2 in
           let curr = int128_to_bytes (aes256_xts_encrypt_round current_block twk key1) in
           let res = aes256_xts_encrypt_rec (i + 1) m P iv key1 key2 in
           APPEND curr res`;;

let wfth = prove(hd(hyp eth),
  EXISTS_TAC `MEASURE (\(i:num,m:num,P:byte list,iv:int128,key1:int128 list,key2:int128 list). (m + 1) - i)` THEN
  REWRITE_TAC[WF_MEASURE; MEASURE] THEN ARITH_TAC);;

let exists_lemma = PROVE_HYP wfth eth;;

(* Note: results are stored in LSByte to MSByte *)
let aes256_xts_encrypt_rec = new_specification ["aes256_xts_encrypt_rec"] exists_lemma;;

(* Cipher stealing for encryption (note: encryption cipher stealing is different from decryption)
  Pm1 : last full block; P_{m-1} in the standard
  Pm  : tail; P_m
*)
let cipher_stealing_encrypt = new_definition
  `cipher_stealing_encrypt (Pm1:byte list) (Pm:byte list) (tail_len:num)
     (iv:int128) (i:num) (key1:int128 list) (key2:int128 list): (byte list)#(byte list) =
     let twk = calculate_tweak i iv key2 in
     let CC = int128_to_bytes (aes256_xts_encrypt_round (bytes_to_int128 Pm1) twk key1) in
     let Cm = SUB_LIST (0, tail_len) CC in
     let CP = SUB_LIST (tail_len, 16 - tail_len) CC in
     let PP = bytes_to_int128 (APPEND Pm CP) in
     let twk_last = GF_128_mult_by_primitive twk in
     let Cm1 = int128_to_bytes (aes256_xts_encrypt_round PP twk_last key1) in
     (Cm1, Cm)`;;

(* Encryption tail handling - either single block or cipher stealing *)
let aes256_xts_encrypt_tail = new_definition
  `aes256_xts_encrypt_tail (i:num) (tail_len:num) (P:byte list) (iv:int128)
    (key1:int128 list) (key2:int128 list) : byte list =
     if tail_len = 0 then
       let Pm1 = bytes_to_int128 (SUB_LIST (i * 16, 16) P) in
       let twk = calculate_tweak i iv key2 in
       int128_to_bytes (aes256_xts_encrypt_round Pm1 twk key1)
     else
       let Pm1 = SUB_LIST (i * 16, 16) P in
       let Pm = SUB_LIST ((i + 1) * 16, tail_len) P in
       let res_cs = cipher_stealing_encrypt Pm1 Pm tail_len iv i key1 key2 in
       APPEND (FST res_cs) (SND res_cs)`;;

(* The main encryption function *)
(* Note: the specification does not handle the case of len < 16, which is
   handled in the implementation. *)
(* AES256-XTS assumes there is at least one block in input *)
(*
  P: Input plaintext represented as a byte list
  len: Byte length of P
  iv: Initialization vector (tweak) as an int128
  key1: Key schedule for AES-256 encryption
  key2: Key schedule for AES-256 encryption for the tweak
  return: Output ciphertext as a byte list
  When input len < 16, the function returns [].
*)
(* TODO: Double check if NIST spec talks about the error case len < 16 *)
(* TODO: Double check the pseudo code in the spec for tweak calculation in ANEX c *)
let aes256_xts_encrypt = new_definition
  `aes256_xts_encrypt
     (P:byte list) (len:num) (iv:int128) (key1:int128 list) (key2:int128 list) : byte list =
     if len < 16 then
       []
     else
       let tail_len = len MOD 16 in
       let m = (len - tail_len) DIV 16 in
       if m < 2 then
         aes256_xts_encrypt_tail 0 tail_len P iv key1 key2
       else
         let res = aes256_xts_encrypt_rec 0 (m - 2) P iv key1 key2 in
         let Ctail = aes256_xts_encrypt_tail (m - 1) tail_len P iv key1 key2 in
         APPEND res Ctail`;;

(***********************************************)
(* Conversions and test vectors *)
(* Test case: Basic XTS encryption *)
(*
Test Vector:
Plaintext:  000102030405060708090a0b0c0d0e0f
Data Key:   2718281828459045235360287471352662497757247093699959574966967627
Tweak Key:  3141592653589793238462643383279502884197169399375105820974944592
Tweak:      FF000000000000000000000000000000
Expected:   1C3B3A102F770386E4836C99E370CF9B
  Plaintext (reversed):  0F0E0D0C0B0A09080706050403020100
  Ciphertext (reversed): 9BCF70E3996C83E48603772F103A3B1C

The test vector values appear in reverse byte order to be little endian.
*)
(* Test vectors based on our Python implementation results *)
let data_key_schedule = new_definition `data_key_schedule:int128 list =
  [ word 0x26357174286053234590452818281827
  ; word 0x27769666495759996993702457774962
  ; word 0x602147C9461436BD6E74659E2BE420B6
  ; word 0x80385664A74EC002EE19999B878AE9BF
  ; word 0x206833EF40497426065D429B68292705
  ; word 0xF9A0259D799873F9DED6B3FB30CF2A60
  ; word 0x50CCC26C70A4F18330ED85A536B0C73E
  ; word 0x3D6AEAAFC4CACF32BD52BCCB63840F30
  ; word 0x5F1273FB0FDEB1977F7A40144F97C5B1
  ; word 0xE8BF1969D5D5F3C6111F3CF4AC4D803F
  ; word 0x99BA4F0DC6A83CF6C9768D61B60CCD75
  ; word 0x6ECCD2B38673CBDA53A6381C42B904E8
  ; word 0x4DF7787AD44D377712E50B81DB9386E0
  ; word 0x1AC8994774044BF4F277802EA1D1B832
  ; word 0xF06E2AC2BD9952B869D465CF7B316E4E
  ]`;;

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
  Two-block test vector (same key and tweak as single block)
  Plaintext:  000102030405060708090a0b0c0d0e0f 101112131415161718191a1b1c1d1e1f
  Data Key:   2718281828459045235360287471352662497757247093699959574966967627
  Tweak Key:  3141592653589793238462643383279502884197169399375105820974944592
  Tweak:      FF000000000000000000000000000000
  Ciphertext: 1C3B3A102F770386E4836C99E370CF9B EA00803F5E482357A4AE12D414A3E63B
  Plaintext (reversed):  0F0E0D0C0B0A09080706050403020100 1F1E1D1C1B1A19181716151413121110
  Ciphertext (reversed): 9BCF70E3996C83E48603772F103A3B1C 3BE6A314D412AEA45723485E3F8000EA
*)

(* Convert reversed plaintext and ciphertext to byte lists using int128_to_bytes *)
let ptext = new_definition
  `ptext =
   int128_to_bytes (word 0x0F0E0D0C0B0A09080706050403020100 : int128)`;;

let ctext = new_definition
  `ctext =
   int128_to_bytes (word 0x9BCF70E3996C83E48603772F103A3B1C : int128 )`;;

let iv1 = new_definition
  `iv1 = (word 0x000000000000000000000000000000FF) : int128`;;

let ptext2 = new_definition
  `ptext2 =
   APPEND (int128_to_bytes (word 0x0F0E0D0C0B0A09080706050403020100))
          (int128_to_bytes (word 0x1F1E1D1C1B1A19181716151413121110))`;;

(*
(REWR_CONV ptext2 THENC
 RAND_CONV INT128_TO_BYTES_CONV THENC
 RATOR_CONV(RAND_CONV INT128_TO_BYTES_CONV) THENC
 REWRITE_CONV [APPEND]) `ptext2`;;
*)
 (* loops indefinitely
 (REWR_CONV ptext2 THENC
 DEPTH_CONV INT128_TO_BYTES_CONV THENC
 (*RATOR_CONV(RAND_CONV INT128_TO_BYTES_CONV) THENC*)
 REWRITE_CONV [APPEND]) `ptext2`;;
*)

(* Test values from aes_xts_decrypt_spec.ml *)
      let iv_tweak = new_definition
  `iv_tweak = (word 0x0000000000000000000000123456789a) : int128`;;

(* p0 = pm1 = ptext *)
let pm1 = new_definition
  `pm1 = [word 0x0; word 0x1; word 0x2; word 0x3;
          word 0x4; word 0x5; word 0x6; word 0x7;
          word 0x8; word 0x9; word 0xa; word 0xb;
          word 0xc; word 0xd; word 0xe; word 0xf] : byte list`;;
let pm = new_definition
  `pm = [word 0x10; word 0x11; word 0x12; word 0x13;
         word 0x14; word 0x15] : byte list`;;

let cm1 = new_definition
  `cm1 = [word 0x75; word 0xe8; word 0x18; word 0x8b; word 0xcc; word 0xe5;
      word 0x9a; word 0xda; word 0x93; word 0x9f; word 0x57; word 0xde;
      word 0x2c; word 0xb9; word 0xa4; word 0x89] : byte list`;;
let cm = new_definition
  `cm = [word 0xc3; word 0xc; word 0xa8; word 0xf2; word 0xed; word 0x57] : byte list`;;

let c0 = new_definition
  `c0 = [word 0xc3; word 0x0c; word 0xa8; word 0xf2
  ; word 0xed; word 0x57; word 0x30; word 0x7e
  ; word 0xdc; word 0x87; word 0xe5; word 0x44
  ; word 0x86; word 0x7a; word 0xc8; word 0x88] : byte list`;;

let p1 = new_definition
  `p1 = [word 0x0; word 0x1; word 0x2; word 0x3;
      word 0x4; word 0x5; word 0x6; word 0x7;
      word 0x8; word 0x9; word 0xa; word 0xb;
      word 0xc; word 0xd; word 0xe; word 0xf;
      word 0x10; word 0x11; word 0x12; word 0x13;
      word 0x14; word 0x15] : byte list`;;
let c1 = new_definition
  `c1 = [ word 0x75; word 0xe8; word 0x18; word 0x8b;
      word 0xcc; word 0xe5; word 0x9a; word 0xda;
      word 0x93; word 0x9f; word 0x57; word 0xde;
      word 0x2c; word 0xb9; word 0xa4; word 0x89;
      word 0xc3; word 0x0c; word 0xa8; word 0xf2;
      word 0xed; word 0x57 ] : byte list`;;

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

(*
(* This key schedule is from aes_xts_decrypt_spec.ml
  It is used in EQINVCIPHER found in Sec 5.3.5 of
  https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197-upd1.pdf
  which is implemented in AWS-LC as the AES decryption algorithm.
  It's different from the encryption key scheduling. *)
let key_1 = new_definition `key_1:int128 list =
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
*)
let key_1 = new_definition `key_1:int128 list =
  [ word 0xF0F1F2F3F4F5F6F7F8F9FAFBFCFDFEFF
  ; word 0xE0E1E2E3E4E5E6E7E8E9EAEBECEDEEEF
  ; word 0x11E1F899E1100A6A15E5FC9DED1C0666
  ; word 0x82F841EE6219A30D86FC45EA6E15AF01
  ; word 0x201B498931FAB110D0EABB7AC50F47E7
  ; word 0xBFA733AF3D5F72415F46D14CD9BA94A6
  ; word 0x7D0C58C35D17114A6CEDA05ABC071B20
  ; word 0xFBFA6E2A445D5D8579022FC42644FE88
  ; word 0x15FEDF6468F287A735E596ED590836B7
  ; word 0xB95A7CA042A0128A06FD4F0F7FFF60CB
  ; word 0xF1B74699E44999FD8CBB1E5AB95E88B7
  ; word 0x23511B009A0B67A0D8AB752ADE563A25
  ; word 0x433D9806B28ADE9F56C34762DA785938
  ; word 0xA58075C086D16EC01CDA0960C4717C4A
  ; word 0xC70A951E84370D1836BDD387607E94E5
  ]`;;

let key_2 = new_definition `key_2:int128 list =
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


(* Common with decrypt *)
let XTS_INIT_TWEAK_CONV =
  REWR_CONV xts_init_tweak THENC AESENC_HELPER_CONV;;
(*
let tmp_xts_tweak = (REWRITE_CONV [iv1; tweak_key_schedule] THENC XTS_INIT_TWEAK_CONV)
    `xts_init_tweak iv1
            tweak_key_schedule`;;
(* Or the following: 33 sec *)
time prove(`xts_init_tweak iv1
            tweak_key_schedule
            = word 0x8b2b4a71228e98aed6aa0ca97775261a`,
            CONV_TAC(REWRITE_CONV [iv1; tweak_key_schedule] THENC LAND_CONV XTS_INIT_TWEAK_CONV)
            THEN REFL_TAC
          );;
*)

(*
let AES_XTS_ENC_1BLK_HELPER_CONV =
(*    PRINT_TERM_CONV THENC *)
  REWR_CONV aes256_xts_encrypt_1block THENC
    PRINT_TERM_CONV THENC
  REWRITE_CONV [data_key_schedule; tweak_key_schedule] THENC
   (* PRINT_TERM_CONV THENC *)
  REWRITE_CONV [xts_init_tweak; aes256_xts_encrypt_round] THENC
  REPEATC let_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV) THENC
  DEPTH_CONV AESENC_HELPER_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV)
  ;;
*)
let AES256_XTS_ENCRYPT_ROUND_CONV =
  REWR_CONV aes256_xts_encrypt_round THENC
  REPEATC let_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV) THENC
  DEPTH_CONV AESENC_HELPER_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;
(*
(* 32 sec *)
time prove(`aes256_xts_encrypt_round
            (word 0x0F0E0D0C0B0A09080706050403020100)
            (word 0x8b2b4a71228e98aed6aa0ca97775261a)
            data_key_schedule
            = word 0x9BCF70E3996C83E48603772F103A3B1C`,
            CONV_TAC(REWRITE_CONV[data_key_schedule] THENC LAND_CONV AES256_XTS_ENCRYPT_ROUND_CONV) THEN
            REFL_TAC
          );;
*)
(*
time prove(`aes256_xts_encrypt_round
            (word 0x1F1E1D1C1B1A19181716151413121110)
            (word 0x165694e2451d315dad541952eeea4cb3)
            data_key_schedule
            = word 0x3BE6A314D412AEA45723485E3F8000EA`,
            CONV_TAC(REWRITE_CONV[data_key_schedule] THENC LAND_CONV AES256_XTS_ENCRYPT_ROUND_CONV) THEN
            REFL_TAC
          );;
*)

let AES_XTS_ENC_1BLK_HELPER_CONV =
  REWR_CONV aes256_xts_encrypt_1block THENC
  REWRITE_CONV [xts_init_tweak] THENC
  SUBLET_CONV AESENC_HELPER_CONV THENC
  let_CONV THENC
  AES256_XTS_ENCRYPT_ROUND_CONV;;

(*
(* Proven in about 73 sec on M3 *)
time prove(`aes256_xts_encrypt_1block
        (word 0x0F0E0D0C0B0A09080706050403020100)
        (word 0x000000000000000000000000000000FF)
        data_key_schedule
        tweak_key_schedule
      = word 0x9BCF70E3996C83E48603772F103A3B1C`,  (* expected result in little endian *)
      CONV_TAC(REWRITE_CONV [data_key_schedule; tweak_key_schedule] THENC LAND_CONV AES_XTS_ENC_1BLK_HELPER_CONV)
      THEN REFL_TAC
    );;
*)

(*
let tmp_xts = AES_XTS_ENC_1BLK_HELPER_CONV
  `aes256_xts_encrypt_1block
    (word 0x0F0E0D0C0B0A09080706050403020100)
    (word 0x000000000000000000000000000000FF)
    data_key_schedule
    tweak_key_schedule
  `;;

prove(list_mk_comb (`(=):((128)word->(128)word->bool)`,
      [rand (concl tmp_xts);`(word 0x9BCF70E3996C83E48603772F103A3B1C):(128)word`]),
      REFL_TAC);;
*)
(*
 (* 67 sec on M3 *)
time prove(`aes256_xts_encrypt_1block
        (word 0x0F0E0D0C0B0A09080706050403020100)
        (word 0x0000000000000000000000123456789a)
        key_1
        key_2
      = word 0x88c87a8644e587dc7e3057edf2a80cc3`,  (* expected result in little endian *)
      CONV_TAC(REWRITE_CONV [key_1; key_2] THENC LAND_CONV AES_XTS_ENC_1BLK_HELPER_CONV)
      THEN REFL_TAC
    );;
*)

(* Common with decrypt *)
let EL_16_8_CLAUSES =
  let pat = `EL n [x0;x1;x2;x3;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14;x15]:byte` in
  map (fun n -> EL_CONV(subst [mk_small_numeral n,`n:num`] pat)) (0--15);;

let BYTES_TO_INT128_CONV =
  REWR_CONV bytes_to_int128 THENC
  REWRITE_CONV EL_16_8_CLAUSES THENC
  DEPTH_CONV WORD_RED_CONV;;
(*
time prove(`bytes_to_int128 ptext
            = (word 0x0f0e0d0c0b0a09080706050403020100 :int128)`,
            CONV_TAC(REWRITE_CONV [ptext;int128_to_bytes] THENC
               LAND_CONV BYTES_TO_INT128_CONV) THEN
            REFL_TAC
          );;
*)

(* Common with decrypt *)
let INT128_TO_BYTES_CONV =
  REWRITE_CONV [int128_to_bytes] THENC
  DEPTH_CONV WORD_RED_CONV;;
(* INT128_TO_BYTES_CONV `int128_to_bytes (word 0x0102030405060708090a0b0c0d0e0f)`;; *)

(* Common with decrypt *)
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

let rec CALCULATE_TWEAK_CONV tm =
  let BASE_CONV =
    ONCE_REWRITE_CONV [calculate_tweak] THENC
    XTS_INIT_TWEAK_CONV in
  let INDUCT_CONV =
    RATOR_CONV(LAND_CONV num_CONV) THENC (* ((calculate_tweak 1) iv_tweak) key_2 *)
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
(* result: word 0x8b2b4a71228e98aed6aa0ca97775261a, confirmed by input to first encrypt_round above *)
(REWRITE_CONV [iv1;tweak_key_schedule] THENC CALCULATE_TWEAK_CONV) `calculate_tweak 0 iv1 tweak_key_schedule`;;
*)(*
(* result: word 0x165694e2451d315dad541952eeea4cb3, confirmed by input to second encrypt_round above *)
(REWRITE_CONV [iv1;tweak_key_schedule] THENC CALCULATE_TWEAK_CONV) `calculate_tweak 1 iv1 tweak_key_schedule`;;
*)

let rec AES256_XTS_ENCRYPT_REC_CONV tm =
  let BASE_CONV =
    REWR_CONV aes256_xts_encrypt_rec THENC
    DEPTH_CONV NUM_RED_CONV in
  let INDUCT_CONV =
    REWR_CONV aes256_xts_encrypt_rec THENC
    DEPTH_CONV NUM_RED_CONV THENC
    ONCE_DEPTH_CONV SUB_LIST_CONV THENC
    ONCE_DEPTH_CONV BYTES_TO_INT128_CONV THENC let_CONV THENC
    SUBLET_CONV CALCULATE_TWEAK_CONV THENC let_CONV THENC
    SUBLET_CONV (RAND_CONV AES256_XTS_ENCRYPT_ROUND_CONV) THENC
    SUBLET_CONV INT128_TO_BYTES_CONV THENC let_CONV THENC
    SUBLET_CONV AES256_XTS_ENCRYPT_REC_CONV THENC let_CONV THENC
    REWRITE_CONV [APPEND] in
  match tm with
  | Comb
      (Comb
       (Comb
         (Comb
           (Comb
             (Comb (Const ("aes256_xts_encrypt_rec", _), i), m),
            _),
          _),
        _),
      _) ->
    if dest_numeral m </ dest_numeral i
    then BASE_CONV tm
    else INDUCT_CONV tm
  | _ -> failwith "AES256_XTS_ENCRYPT_REC_CONV: inapplicable";;

(*
(REWRITE_CONV [iv1; data_key_schedule; tweak_key_schedule; ptext; int128_to_bytes] THENC
      AES256_XTS_ENCRYPT_REC_CONV)
  `aes256_xts_encrypt_rec 0 0 ptext iv1 data_key_schedule tweak_key_schedule`;;
*) (*
(REWRITE_CONV [iv_tweak; pm1; key_1; key_2] THENC
      AES256_XTS_ENCRYPT_REC_CONV)
  `aes256_xts_encrypt_rec 0 0 pm1 iv_tweak key_1 key_2`;;
*)
(*
(REWRITE_CONV [iv1; data_key_schedule; tweak_key_schedule; ptext2; int128_to_bytes; APPEND] THENC
      AES256_XTS_ENCRYPT_REC_CONV)
  `aes256_xts_encrypt_rec 0 1 ptext2 iv1 data_key_schedule tweak_key_schedule`;;
*)

let CIPHER_STEALING_ENCRYPT_CONV =
  REWR_CONV cipher_stealing_encrypt THENC
  SUBLET_CONV CALCULATE_TWEAK_CONV THENC let_CONV THENC
  SUBLET_CONV (ONCE_DEPTH_CONV BYTES_TO_INT128_CONV) THENC
  SUBLET_CONV (RAND_CONV AES256_XTS_ENCRYPT_ROUND_CONV) THENC
  SUBLET_CONV INT128_TO_BYTES_CONV THENC let_CONV THENC
  SUBLET_CONV SUB_LIST_CONV THENC let_CONV THENC
  SUBLET_CONV (DEPTH_CONV NUM_RED_CONV) THENC (* For evaluating 16 - tail_len *)
  SUBLET_CONV SUB_LIST_CONV THENC let_CONV THENC
  SUBLET_CONV (ONCE_DEPTH_CONV (REWRITE_CONV [APPEND])) THENC
  SUBLET_CONV BYTES_TO_INT128_CONV THENC let_CONV THENC
  SUBLET_CONV GF_128_MULT_BY_PRIMITIVE_CONV THENC let_CONV THENC
  SUBLET_CONV (RAND_CONV AES256_XTS_ENCRYPT_ROUND_CONV) THENC
  SUBLET_CONV INT128_TO_BYTES_CONV THENC let_CONV;;

(* (REWRITE_CONV [ptext; int128_to_bytes; iv1; data_key_schedule; tweak_key_schedule] THENC CIPHER_STEALING_ENCRYPT_CONV)
  `cipher_stealing_encrypt ptext [(word 0x0)] 1 iv1 0 data_key_schedule tweak_key_schedule`;;*)
(*
(REWRITE_CONV [pm1; pm; iv_tweak; key_1; key_2] THENC CIPHER_STEALING_ENCRYPT_CONV)
  `cipher_stealing_encrypt pm1 pm 6 iv_tweak 0 key_1 key_2`;;
*)

let AES256_XTS_ENCRYPT_TAIL_CONV tm =
  let ONE_BLOCK_CONV =
    REWR_CONV aes256_xts_encrypt_tail THENC
    DEPTH_CONV NUM_RED_CONV THENC
    SUBLET_CONV (RAND_CONV SUB_LIST_CONV) THENC
    SUBLET_CONV BYTES_TO_INT128_CONV THENC let_CONV THENC
    SUBLET_CONV CALCULATE_TWEAK_CONV THENC let_CONV THENC
    RAND_CONV AES256_XTS_ENCRYPT_ROUND_CONV THENC
    INT128_TO_BYTES_CONV in
  let ONE_BLOCK_AND_TAIL_CONV =
    REWR_CONV aes256_xts_encrypt_tail THENC
    DEPTH_CONV NUM_RED_CONV THENC
    SUBLET_CONV SUB_LIST_CONV THENC let_CONV THENC
    SUBLET_CONV SUB_LIST_CONV THENC let_CONV THENC
    SUBLET_CONV CIPHER_STEALING_ENCRYPT_CONV THENC let_CONV THENC
    REWRITE_CONV [FST;SND] THENC REWRITE_CONV [APPEND] in
  match tm with
  | Comb
      (Comb
       (Comb
         (Comb
           (Comb
             (Comb
               (Const ("aes256_xts_encrypt_tail", _), _), tail_len),
            _),
          _),
        _),
      _) ->
    if dest_numeral tail_len =/ num 0
    then ONE_BLOCK_CONV tm
    else ONE_BLOCK_AND_TAIL_CONV tm
  | _ -> failwith "AES256_XTS_ENCRYPT_TAIL_CONV: inapplicable";;
(*
(REWRITE_CONV [ptext; int128_to_bytes; iv1; data_key_schedule; tweak_key_schedule] THENC AES256_XTS_ENCRYPT_TAIL_CONV)
  `aes256_xts_encrypt_tail 0 0 ptext iv1 data_key_schedule tweak_key_schedule`;;
*)(*
(REWRITE_CONV [p1;iv_tweak;key_1;key_2] THENC AES256_XTS_ENCRYPT_TAIL_CONV)
  `aes256_xts_encrypt_tail 0 6 p1 iv_tweak key_1 key_2`;;
*)(*
(REWRITE_CONV [p0;iv_tweak;key_1;key_2] THENC AES256_XTS_ENCRYPT_TAIL_CONV)
  `aes256_xts_encrypt_tail 0 0 p0 iv_tweak key_1 key_2`;;
*)

let AES256_XTS_ENCRYPT_CONV tm =
  let ERROR_CONV =
    REWR_CONV aes256_xts_encrypt THENC
    DEPTH_CONV NUM_RED_CONV in
  let MORE_THAN_2_CONV =
    SUBLET_CONV AES256_XTS_ENCRYPT_REC_CONV THENC let_CONV THENC
    SUBLET_CONV AES256_XTS_ENCRYPT_TAIL_CONV THENC let_CONV THENC
    REWRITE_CONV [APPEND] in
  let BODY_CONV =
    REWR_CONV aes256_xts_encrypt THENC
    DEPTH_CONV NUM_RED_CONV THENC let_CONV THENC
    DEPTH_CONV NUM_RED_CONV THENC let_CONV THENC
    DEPTH_CONV NUM_RED_CONV THENC
    (AES256_XTS_ENCRYPT_TAIL_CONV ORELSEC MORE_THAN_2_CONV) in
  match tm with
  | Comb
     (Comb
       (Comb
         (Comb
           (Comb
             (Const ("aes256_xts_encrypt", _), _), len),
         _),
       _),
     _) ->
    if dest_numeral len </ num 16
    then ERROR_CONV tm
    else BODY_CONV tm
  | _ -> failwith "AES256_XTS_ENCRYPT_CONV: inapplicable";;

(*
(REWRITE_CONV [int128_to_bytes] THENC AES256_XTS_ENCRYPT_CONV)
  `aes256_xts_encrypt p0 5 iv_tweak key_1 key_2`;;

(*(REWRITE_CONV [ptext; int128_to_bytes; iv_tweak; key_1; key_2] THENC AES256_XTS_ENCRYPT_CONV)
  `aes256_xts_encrypt ptext 16 iv_tweak key_1 key_2`;;*)

(* 1 block : 70 sec on M3 *)
time prove (`aes256_xts_encrypt ptext 16 iv_tweak key_1 key_2 = c0`,
  CONV_TAC(LAND_CONV (REWRITE_CONV [ptext; int128_to_bytes; iv_tweak; key_1; key_2]
           THENC AES256_XTS_ENCRYPT_CONV)) THEN
  REWRITE_TAC [c0] THEN REFL_TAC);;

(* 1 block + 6 bytes : 104 sec on M3 *)
time prove (`aes256_xts_encrypt p1 22 iv_tweak key_1 key_2 = c1`,
  CONV_TAC(LAND_CONV (REWRITE_CONV [p1; int128_to_bytes; iv_tweak; key_1; key_2]
           THENC AES256_XTS_ENCRYPT_CONV)) THEN
  REWRITE_TAC [c1] THEN REFL_TAC);;

(* 3 blocks + 3 bytes : 243 sec on M3 *)
time prove (`aes256_xts_encrypt p2 51 iv_tweak key_1 key_2 = c2`,
  CONV_TAC(LAND_CONV (REWRITE_CONV [p2; int128_to_bytes; iv_tweak; key_1; key_2]
           THENC AES256_XTS_ENCRYPT_CONV)) THEN
  REWRITE_TAC [c2] THEN REFL_TAC);;
*)
(*****************************************)



