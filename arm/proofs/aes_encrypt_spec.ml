use_file_raise_failure := true;;
needs "common/aes.ml";;

let pp_print_num fmt tm =
  let n = dest_numeral tm in
  pp_print_string fmt (string_of_num_hex n) in
install_user_printer("pp_print_num",pp_print_num);;

(*
Cipher(byte in[4*Nb], byte out[4*Nb], word w[Nb*(Nr+1)])

begin

byte state[4,Nb]
state = in

AddRoundKey(state, w[0, Nb-1]) // See Sec. 5.1.4

for round = 1 step 1 to Nr–1

SubBytes(state) // See Sec. 5.1.1
ShiftRows(state) // See Sec. 5.1.2
MixColumns(state) // See Sec. 5.1.3
AddRoundKey(state, w[round*Nb, (round+1)*Nb-1])

end for

SubBytes(state)
ShiftRows(state)
AddRoundKey(state, w[Nr*Nb, (Nr+1)*Nb-1])

out = state

end
*)
(* TODO: Nevine will finish writing this spec *)
(* Note: In the spec, SubBytes precedes ShiftRows, but the instruction
         definition of aese in arm/proofs/aes.ml has them interchanged.
         This is possible but requires a modified lookup table, joined_GF2,
         from the specs.
         We will follow the same pattern below as the instruction definition
         TODO: prove the equivalence with the spec later.*)

let aes256_encrypt_round = new_definition
  `aes256_encrypt_round (block:int128) (round_key:int128) =
     let res2 = aes_shift_rows block in
     let res3 = aes_sub_bytes joined_GF2 res2 in
     let res1 = aes_mix_columns res3 in
     word_xor res1 round_key
    `;;

let aes256_encrypt = new_definition
  `aes256_encrypt (block:int128) (key_schedule:int128 list) =
     let res0 = word_xor block (EL 0 key_schedule) in
     let res1 = aes256_encrypt_round res0 (EL 1 key_schedule) in
     let res2 = aes256_encrypt_round res1 (EL 2 key_schedule) in
     let res3 = aes256_encrypt_round res2 (EL 3 key_schedule) in
     let res4 = aes256_encrypt_round res3 (EL 4 key_schedule) in
     let res5 = aes256_encrypt_round res4 (EL 5 key_schedule) in
     let res6 = aes256_encrypt_round res5 (EL 6 key_schedule) in
     let res7 = aes256_encrypt_round res6 (EL 7 key_schedule) in
     let res8 = aes256_encrypt_round res7 (EL 8 key_schedule) in
     let res9 = aes256_encrypt_round res8 (EL 9 key_schedule) in
     let res10 = aes256_encrypt_round res9 (EL 10 key_schedule) in
     let res11 = aes256_encrypt_round res10 (EL 11 key_schedule) in
     let res12 = aes256_encrypt_round res11 (EL 12 key_schedule) in
     let res13 = aes256_encrypt_round res12 (EL 13 key_schedule) in
     let res14 = aes_shift_rows res13 in
     let res15 = aes_sub_bytes joined_GF2 res14 in
     word_xor res15 (EL 14 key_schedule)
  `;;

let AESENC_ROUND_HELPER_CONV =
  REWRITE_CONV [aes256_encrypt_round] THENC
  AES_SHIFT_ROWS_CONV THENC
  AES_SUB_BYTES_CONV THENC
  AES_MIX_COLUMNS_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let AESENC_ROUND_REDUCE_CONV tm =
  match tm with
    Comb(Comb(Const("aes256_encrypt_round",_),
         Comb(Const("word",_),state)),
         Comb(Const("word",_),roundkey))
    when is_numeral state && is_numeral roundkey -> AESENC_ROUND_HELPER_CONV tm
    | _ -> failwith "AESENC_ROUND_REDUCE_CONV: inapplicable";;

prove(`aes256_encrypt_round (word 0x7b5b54657374566563746f725d53475d)
              (word 0x48692853686179295b477565726f6e5d) =
       word 0xa8311c2f9fdba3c58b104b58ded7e595`,
       CONV_TAC(LAND_CONV AESENC_ROUND_REDUCE_CONV) THEN REFL_TAC);;

prove(`aes256_encrypt_round (word 0xAB60EEF6E1D04EC228EE8A3BF255FC0B)
              (word 0xF4DF1409A310982DD708613B072C351F) =
       word 0x416EAD9670A2C6D71CFE3FCCB03F10D9`,
       CONV_TAC(LAND_CONV AESENC_ROUND_REDUCE_CONV) THEN REFL_TAC);;

(*
https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/AES_Core256.pdf
has the same test vector as
https://www.intel.com/content/dam/doc/white-paper/advanced-encryption-standard-new-instructions-set-paper.pdf
The vector values appear in the code in reverse byte order to be little endian.

AES256_TEST_KEY[] =
603DEB1015CA71BE2B73AEF0857D77811F352C073B6108D72D9810A30914DFF4
AES_TEST_VECTOR[] =
6BC1BEE22E409F96E93D7E117393172A
ECB256_EXPECTED[] =
F3EED1BDB5D2A03C064B5A7E3DB181F8

Round keys in big endian generated from the key via a python code
Round  0: 603DEB1015CA71BE2B73AEF0857D7781
Round  1: 1F352C073B6108D72D9810A30914DFF4
Round  2: 9BA354118E6925AFA51A8B5F2067FCDE
Round  3: A8B09C1A93D194CDBE49846EB75D5B9A
Round  4: D59AECB85BF3C917FEE94248DE8EBE96
Round  5: B5A9328A2678A647983122292F6C79B3
Round  6: 812C81ADDADF48BA24360AF2FAB8B464
Round  7: 98C5BFC9BEBD198E268C3BA709E04214
Round  8: 68007BACB2DF331696E939E46C518D80
Round  9: C814E20476A9FB8A5025C02D59C58239
Round 10: DE1369676CCC5A71FA2563959674EE15
Round 11: 5886CA5D2E2F31D77E0AF1FA27CF73C3
Round 12: 749C47AB18501DDAE2757E4F7401905A
Round 13: CAFAAAE3E4D59B349ADF6ACEBD10190D
Round 14: FE4890D1E6188D0B046DF344706C631E
*)

(* These are the ound keys with the bytes reversed to become little endian *)
let ROUND_KEYS = new_definition `ROUND_KEYS:int128 list =
  [ word 0x81777D85F0AE732BBE71CA1510EB3D60
  ; word 0xF4DF1409A310982DD708613B072C351F
  ; word 0xDEFC67205F8B1AA5AF25698E1154A39B
  ; word 0x9A5B5DB76E8449BECD94D1931A9CB0A8
  ; word 0x96BE8EDE4842E9FE17C9F35BB8EC9AD5
  ; word 0xB3796C2F2922319847A678268A32A9B5
  ; word 0x64B4B8FAF20A3624BA48DFDAAD812C81
  ; word 0x1442E009A73B8C268E19BDBEC9BFC598
  ; word 0x808D516CE439E9961633DFB2AC7B0068
  ; word 0x3982C5592DC025508AFBA97604E214C8
  ; word 0x15EE7496956325FA715ACC6C676913DE
  ; word 0xC373CF27FAF10A7ED7312F2E5DCA8658
  ; word 0x5A9001744F7E75E2DA1D5018AB479C74
  ; word 0x0D1910BDCE6ADF9A349BD5E4E3AAFACA
  ; word 0x1E636C7044F36D040B8D18E6D19048FE
  ]`;;


let EL_15_128_CLAUSES =
  let pat = `EL n [x0;x1;x2;x3;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14]:128 word` in
  map (fun n -> EL_CONV(subst [mk_small_numeral n,`n:num`] pat)) (0--14);;

let AESENC_HELPER_CONV KEYS =
  REWRITE_CONV [aes256_encrypt] THENC
  REWRITE_CONV [KEYS] THENC
  REWRITE_CONV EL_15_128_CLAUSES THENC
  REPEATC let_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV) THENC
  DEPTH_CONV AESENC_ROUND_REDUCE_CONV THENC
  AES_SHIFT_ROWS_CONV THENC
  AES_SUB_BYTES_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

(*
time prove (`aes256_encrypt
    (word 0x2A179373117E3DE9969F402EE2BEC16B)
    ROUND_KEYS = word 0xF881B13D7E5A4B063CA0D2B5BDD1EEF3`,
    CONV_TAC(LAND_CONV AESENC_HELPER_CONV) THEN REFL_TAC);;
*)
