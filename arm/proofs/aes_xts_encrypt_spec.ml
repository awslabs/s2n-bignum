needs "arm/proofs/base.ml";;
needs "arm/proofs/aes_encrypt_spec.ml";;
(*
AES-256-XTS Encryption Algorithm for One Block
Based on IEEE 1619-2007 Standard

Sec 5.3.1 Encryption of a single block

Key = Key1 256-bit data key
      Key2 256-bit tweak key
P is a block of 128 bits (i.e., the plaintext)
i is the value of the 128-bit tweak (see 5.1)
j is the sequential number of the 128-bit block inside the data unit
C is the block of 128 bits of ciphertext resulting from the operation

T := AES-enc(Key2 , i) MUL α^j
PP := P XOR T
CC := AES-enc(Key1 , PP)
C := CC XOR T

j=0 => alpha^j = unity transformation,
   i.e. no change to the encrypted tweak for the the first block
*)

(* XTS encryption function definition *)
let aes256_xts_encrypt_one_block = new_definition
  `aes256_xts_encrypt_one_block (plaintext:int128) (data_key_schedule:int128 list)
                                (tweak_key_schedule:int128 list) (tweak:int128) =
     let T = aes256_encrypt tweak tweak_key_schedule in
     let pre_encrypt = word_xor plaintext T in
     let encrypted = aes256_encrypt pre_encrypt data_key_schedule in
     word_xor encrypted T`;;

(* Test case: Basic XTS encryption *)
(*
Test Vector:
Plaintext:  000102030405060708090a0b0c0d0e0f
Data Key:   2718281828459045235360287471352662497757247093699959574966967627
Tweak Key:  3141592653589793238462643383279502884197169399375105820974944592
Tweak:      FF000000000000000000000000000000
Expected:   1C3B3A102F770386E4836C99E370CF9B

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
AES-256-XTS Encryption Algorithm for Any Input Length
Based on IEEE 1619-2007 Standard

This specification implements the complete AES-XTS encryption algorithm
as described in IEEE 1619-2007, Section 5.3, supporting arbitrary input lengths.

Key components:
- Key = Key1 (256-bit data key) || Key2 (256-bit tweak key)
- P is the plaintext of arbitrary length (≥ 128 bits)
- i is the value of the 128-bit tweak
- C is the resulting ciphertext

The algorithm processes data in 128-bit blocks with special handling for
the final partial block (if any) using ciphertext stealing.

For each complete block j:
  T_j := AES-enc(Key2, i) MUL α^j
  PP_j := P_j XOR T_j
  CC_j := AES-enc(Key1, PP_j)
  C_j := CC_j XOR T_j

Where α is the primitive element in GF(2^128) and MUL denotes multiplication
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

(* XTS tweak initialization - encrypt the IV with key2 *)
(* TODO: put it in a common place to be used with decrypt
     Start *)
let xts_init_tweak = new_definition
  `xts_init_tweak (iv:int128) (key_schedule:int128 list) =
     aes256_encrypt iv key_schedule`;;

let bytes_to_int128 = define
  `bytes_to_int128 (bs : byte list) : int128 =
     word_join
       (word_join
         (word_join
           (word_join (EL 15 bs) (EL 14 bs) : int16)
           (word_join (EL 13 bs) (EL 12 bs) : int16) : int32)
         (word_join
           (word_join (EL 11 bs) (EL 10 bs) : int16)
           (word_join (EL 9 bs) (EL 8 bs) : int16) : int32) : int64)
       (word_join
         (word_join
           (word_join (EL 7 bs) (EL 6 bs) : int16)
           (word_join (EL 5 bs) (EL 4 bs) : int16) : int32)
         (word_join
           (word_join (EL 3 bs) (EL 2 bs) : int16)
           (word_join (EL 1 bs) (EL 0 bs) : int16) : int32) : int64)`;;

let int128_to_bytes = define
  `int128_to_bytes (w : int128) : byte list =
     [word_subword w (0, 8); word_subword w (8, 8); word_subword w (16, 8); word_subword w (24, 8);
      word_subword w (32, 8); word_subword w (40, 8); word_subword w (48, 8); word_subword w (56, 8);
      word_subword w (64, 8); word_subword w (72, 8); word_subword w (80, 8); word_subword w (88, 8);
      word_subword w (96, 8); word_subword w (104, 8); word_subword w (112, 8); word_subword w (120, 8)]`;;

(* Multiplication by the primitive element \alpha in GF(2^128) *)
let GF_128_mult_by_primitive = new_definition
  `GF_128_mult_by_primitive (tweak:(128)word) =
     let shifted = word_shl tweak 1 in
     let mask = word_ishr tweak 127 in
     word_xor (word_and mask (word 0x87)) shifted`;;

(* TODO: put it in a common place to be used with decrypt
     End *)
let calculate_tweak = new_recursive_definition num_RECURSION
  `calculate_tweak 0 (iv:(128)word) (key2:int128 list) = xts_init_tweak iv key2 /\
   calculate_tweak (SUC n) (iv:(128)word) (key2:int128 list) =
     GF_128_mult_by_primitive (calculate_tweak n iv key2)`;;

(* AES-XTS encryption round function *)
let aes256_xts_encrypt_round = new_definition
  `aes256_xts_encrypt_round (P:int128) (tk:int128) (key_schedule:int128 list) =
     let PP = word_xor P tk in
     let CC = aes256_encrypt PP key_schedule in
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
       aes256_xts_encrypt_rec i m P iv key1 key2 : (byte list)#num =
         if m < i then ([], i)
         else
           let current_block = bytes_to_int128 (SUB_LIST (i * 16, 16) P) in
           let twk = calculate_tweak i iv key2 in
           let curr = int128_to_bytes (aes256_xts_encrypt_round current_block twk key1) in
           let res = aes256_xts_encrypt_rec (i + 1) m P iv key1 key2 in
           (APPEND curr (FST res), SND res)`;;

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
     let iv_last = GF_128_mult_by_primitive iv in
     let Cm1 = int128_to_bytes (aes256_xts_encrypt_round PP iv_last key1) in
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
  C_error: Error output ciphertext in case of invalid input length
  return: Output ciphertext as a byte list
  When input len < 16, the function returns C_error,
  which will be the initial value stored in output address.
*)
(* TODO: Challenge lemma: proving that the output is of same length as input *)
(* TODO: Double check if NIST spec talks about the error case len < 16 *)
(* TODO: Double check the pseudo code in the spec for tweak calculation in ANEX c *)
let aes256_xts_encrypt = new_definition
  `aes256_xts_encrypt
     (P:byte list) (len:num) (iv:int128) (key1:int128 list) (key2:int128 list) (err:byte list) : byte list =
     if len < 16 then
       err
     else
       let tail_len = len MOD 16 in
       let m = (len - tail_len) DIV 16 in
       if m < 2 then
         aes256_xts_encrypt_tail 0 tail_len P iv key1 key2
       else
         let res = aes256_xts_encrypt_rec 0 (m - 2) P iv key1 key2 in
         let Ctail = aes256_xts_encrypt_tail (SND res) tail_len P iv key1 key2 in
         APPEND (FST res) Ctail`;;

(****)
(* Conversions and test vectors *)
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

(*
(* Proven in about 100 sec on M3 *)
time prove(`aes256_xts_encrypt_1block
        (word 0x0F0E0D0C0B0A09080706050403020100)
        (word 0x000000000000000000000000000000FF)
        data_key_schedule
        tweak_key_schedule
      = word 0x9BCF70E3996C83E48603772F103A3B1C`,  (* expected result in little endian *)
      CONV_TAC(LAND_CONV AES_XTS_ENC_1BLK_HELPER_CONV)
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
  Two-block test vector (same key and tweak as single block)
  Plaintext:  000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f
  Data Key:   2718281828459045235360287471352662497757247093699959574966967627
  Tweak Key:  3141592653589793238462643383279502884197169399375105820974944592
  Tweak:      FF000000000000000000000000000000
  Ciphertext: 1C3B3A102F770386E4836C99E370CF9BEA00803F5E482357A4AE12D414A3E63B
  Plaintext (reversed):  1F1E1D1C1B1A191817161514131211100F0E0D0C0B0A09080706050403020100
  Ciphertext (reversed): 3BE6A314D412AEA45723485E3F8000EA9BCF70E3996C83E48603772F103A3B1C
*)

(* Convert reversed plaintext and ciphertext to byte lists using int128_to_bytes *)
let plaintext = new_definition
  `plaintext =
   int128_to_bytes (word 0x1F1E1D1C1B1A191817161514131211100F0E0D0C0B0A09080706050403020100)`;;

let ciphertext = new_definition
  `ciphertext =
   int128_to_bytes (word 0x3BE6A314D412AEA45723485E3F8000EA9BCF70E3996C83E48603772F103A3B1C)`;;

let cerr = new_definition
  `cerr =
   int128_to_bytes (word 0x0)`;;

(* Generated by Cline but not needed
(* Two-block plaintext for testing *)
let two_block_plaintext = new_definition
  `two_block_plaintext =
   APPEND (int128_to_bytes (word 0x0F0E0D0C0B0A09080706050403020100))
          (int128_to_bytes (word 0x1F1E1D1C1B1A19181716151413121110))`;;
*)

(* This was generated by Cline, to review *)
(* Conversion for aes256_xts_encrypt using the byte lists *)
let AES_XTS_ENC_HELPER_CONV =
(*    PRINT_TERM_CONV THENC *)
  REWR_CONV aes256_xts_encrypt THENC
    PRINT_TERM_CONV THENC
  REWRITE_CONV [data_key_schedule; tweak_key_schedule; plaintext; ciphertext; C_err] THENC
   (* PRINT_TERM_CONV THENC *)
  REWRITE_CONV [xts_init_tweak; aes256_xts_encrypt_round; aes256_xts_encrypt_tail;
                aes256_xts_encrypt_rec; cipher_stealing_encrypt] THENC
  REWRITE_CONV [int128_to_bytes; bytes_to_int128; SUB_LIST; APPEND; EL] THENC
  REPEATC let_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV) THENC
  DEPTH_CONV AESENC_HELPER_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV)
  ;;

  let tmp_xts_enc = AES_XTS_ENC_HELPER_CONV
    `aes256_xts_encrypt plaintext 32 (word 0x000000000000000000000000000000FF)
            data_key_schedule
            tweak_key_schedule C_error
    `;;
(*****************************************)
(* Test key schedules from the decryption spec *)

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

(*****************************************)
(* Conversions *)

let plaintext = new_definition
  `[word 0x0f; word 0x0e; word 0x0d; word 0x0c
  ; word 0x0b; word 0x0a; word 0x09; word 0x08
  ; word 0x07; word 0x06; word 0x05; word 0x04
  ; word 0x03; word 0x02; word 0x01; word 0x00] : byte list`;;

let iv = new_definition
  `(word 0x0000000000000000000000123456789a) : int128`;;

let C_error = new_definition
  `[ word 0; word 0; word 0; word 0
  ; word 0; word 0; word 0; word 0
  ; word 0; word 0; word 0; word 0
  ; word 0; word 0; word 0; word 0] : byte list`;;

let ciphertext = new_definition
  `[word 0xc3; word 0x0c; word 0xa8; word 0xf2
  ; word 0xed; word 0x57; word 0x30; word 0x7e
  ; word 0xdc; word 0x87; word 0xe5; word 0x44
  ; word 0x86; word 0x7a; word 0xc8; word 0x88] : byte list`;;

let rw = Compute.bool_compset();;
word_compute_add_convs rw;;
num_compute_add_convs rw;;
Compute.add_thms [aes256_xts_encrypt;KEY1;KEY2;plaintext;iv;C_error;ciphertext] rw;;
let my_conv = Compute.WEAK_CBV_CONV rw;;
my_conv `aes256_xts_encrypt P 16 iv KEY1 KEY2 C_error`;;
