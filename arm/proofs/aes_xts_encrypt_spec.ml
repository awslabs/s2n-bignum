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

T := AES-enc(Key2 , i) XOR α^j
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
let AES_XTS_ENC_HELPER_CONV =
    PRINT_TERM_CONV THENC
  REWR_CONV aes256_xts_encrypt_one_block THENC
    PRINT_TERM_CONV THENC
  REWRITE_CONV [aes256_encrypt; data_key_schedule; tweak_key_schedule] THENC
    PRINT_TERM_CONV THENC
  REWRITE_CONV EL_15_128_CLAUSES THENC
(*  PRINT_TERM_CONV THENC *)
  REPEATC let_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV) THENC
  DEPTH_CONV AESENC_REDUCE_CONV (*THENC
  AES_SHIFT_ROWS_CONV THENC
  AES_SUB_BYTES_CONV THENC
  PRINT_TERM_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV)
  *)
  ;;
*)
let AES_XTS_ENC_HELPER_CONV =
(*    PRINT_TERM_CONV THENC *)
  REWR_CONV aes256_xts_encrypt_one_block THENC
(*    PRINT_TERM_CONV THENC*)
  REWRITE_CONV [data_key_schedule; tweak_key_schedule] THENC
(*  PRINT_TERM_CONV THENC *)
  REPEATC let_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV) THENC
  DEPTH_CONV AESENC_HELPER_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV)
  ;;

(*
(* Takes about a 100 sec on M3 *)
let tmp_xts = AES_XTS_ENC_HELPER_CONV
  `aes256_xts_encrypt_one_block
    (word 0x0F0E0D0C0B0A09080706050403020100)
    data_key_schedule
    tweak_key_schedule
    (word 0x000000000000000000000000000000FF)
  `;;

prove(list_mk_comb (`(=):((128)word->(128)word->bool)`,
      [rand (concl tmp_xts);`(word 0x9BCF70E3996C83E48603772F103A3B1C):(128)word`]),
      REFL_TAC);;
*)

(*
(* Takes about a 100 sec on M3 *)
time prove(`aes256_xts_encrypt_one_block
        (word 0x0F0E0D0C0B0A09080706050403020100)
        data_key_schedule
        tweak_key_schedule
        (word 0x000000000000000000000000000000FF)
      = word 0x9BCF70E3996C83E48603772F103A3B1C`,  (* expected result in little endian *)
      CONV_TAC(LAND_CONV AES_XTS_ENC_HELPER_CONV)
      THEN REFL_TAC
       );;
*)