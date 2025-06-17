use_file_raise_failure := true;;
needs "common/aes.ml";;

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

let PRINT_TERM_CONV t = Format.printf "%a\n" pp_print_qterm t; ALL_CONV t;;

let AESENC_ROUND_HELPER_CONV =
  PRINT_TERM_CONV THENC
  REWRITE_CONV [aes256_encrypt_round] THENC
  PRINT_TERM_CONV THENC
  AES_SHIFT_ROWS_CONV THENC
  PRINT_TERM_CONV THENC
  AES_SUB_BYTES_CONV THENC
  AES_MIX_COLUMNS_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let AESENC_REDUCE_CONV tm =
  match tm with
    Comb(Comb(Const("aes256_encrypt_round",_),
         Comb(Const("word",_),state)),
         Comb(Const("word",_),roundkey))
    when is_numeral state && is_numeral roundkey -> AESENC_ROUND_HELPER_CONV tm
    | _ -> failwith "AESENC_REDUCE_CONV: inapplicable";;

prove(`aes256_encrypt_round (word 0x7b5b54657374566563746f725d53475d)
              (word 0x48692853686179295b477565726f6e5d) =
       word 0xa8311c2f9fdba3c58b104b58ded7e595`,
       CONV_TAC(LAND_CONV AESENC_REDUCE_CONV) THEN REFL_TAC);;

(*
https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/AES_Core256.pdf
has the same test vector as
https://www.intel.com/content/dam/doc/white-paper/advanced-encryption-standard-new-instructions-set-paper.pdf:
AES256_TEST_KEY[] =
603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4
AES_TEST_VECTOR[] =
6bc1bee22e409f96e93d7e117393172aae2d8a571e03ac9c9eb76fac45af8e5130c81c46a35ce411e5fbc1191a0a52eff69f2445df4f9b17ad2b417be66c3710
ECB256_EXPECTED[] =
f3eed1bdb5d2a03c064b5a7e3db181f8591ccb10d410ed26dc5ba74a31362870b6ed21b99ca6f4f9f153e7b1beafed1d23304b7a39f9f3ff067d8d8f9e24ecc7
*)

let ROUND_KEYS = new_definition `ROUND_KEYS:int128 list =
  [ word 0x603DEB1015CA71BE2B73AEF0857D7781
  ; word 0x1F352C073B6108D72D9810A30914DFF4
  ; word 0x9BA354118E6925AFA51A8B5F2067FCDE
  ; word 0xA8B09C1A93D194CDBE49846EB75D5B9A
  ; word 0xD59AECB85BF3C917FEE94248DE8EBE96
  ; word 0xB5A9328A2678A647983122292F6C79B3
  ; word 0x812C81ADDADF48BA24360AF2FAB8B464
  ; word 0x98C5BFC9BEBD198E268C3BA709E04214
  ; word 0x68007BACB2DF331696E939E46C518D80
  ; word 0xC814E20476A9FB8A5025C02D59C58239
  ; word 0xDE1369676CCC5A71FA2563959674EE15
  ; word 0x5886CA5D2E2F31D77E0AF1FA27CF73C3
  ; word 0x749C47AB18501DDAE2757E4F7401905A
  ; word 0xCAFAAAE3E4D59B349ADF6ACEBD10190D
  ; word 0xFE4890D1E6188D0B046DF344706C631E
  ]`;;

let EL_15_128_CLAUSES =
  let pat = `EL n [x0;x1;x2;x3;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14]:128 word` in
  map (fun n -> EL_CONV(subst [mk_small_numeral n,`n:num`] pat)) (0--14);;

REWRITE_CONV [ROUND_KEYS]
  `let res0 =
      word_xor (word 143233380420387077518460912116591433514) (EL 0 ROUND_KEYS) in
  let res1 = aes256_encrypt_round res0 (EL 1 ROUND_KEYS) in
  let res2 = aes256_encrypt_round res1 (EL 2 ROUND_KEYS) in
  let res3 = aes256_encrypt_round res2 (EL 3 ROUND_KEYS) in
  let res4 = aes256_encrypt_round res3 (EL 4 ROUND_KEYS) in
  let res5 = aes256_encrypt_round res4 (EL 5 ROUND_KEYS) in
  let res6 = aes256_encrypt_round res5 (EL 6 ROUND_KEYS) in
  let res7 = aes256_encrypt_round res6 (EL 7 ROUND_KEYS) in
  let res8 = aes256_encrypt_round res7 (EL 8 ROUND_KEYS) in
  let res9 = aes256_encrypt_round res8 (EL 9 ROUND_KEYS) in
  let res10 = aes256_encrypt_round res9 (EL 10 ROUND_KEYS) in
  let res11 = aes256_encrypt_round res10 (EL 11 ROUND_KEYS) in
  let res12 = aes256_encrypt_round res11 (EL 12 ROUND_KEYS) in
  let res13 = aes256_encrypt_round res12 (EL 13 ROUND_KEYS) in
  let res14 = aes_shift_rows res13 in
  let res15 = aes_sub_bytes joined_GF2 res14 in
  word_xor res15 (EL 14 ROUND_KEYS)`;;

let AESENC_HELPER_CONV =
  PRINT_TERM_CONV THENC
  REWR_CONV aes256_encrypt THENC
  PRINT_TERM_CONV THENC
  REWRITE_CONV [ROUND_KEYS] THENC
  PRINT_TERM_CONV THENC
  REWRITE_CONV EL_15_128_CLAUSES THENC
  PRINT_TERM_CONV THENC
  (*REPEATC let_CONV THENC*)
  PRINT_TERM_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV) THENC
  ONCE_DEPTH_CONV AESENC_ROUND_HELPER_CONV
  ;;

(*
let AESENC_HELPER_CONV =
  PRINT_TERM_CONV THENC
  REWR_CONV aes256_encrypt THENC
  PRINT_TERM_CONV THENC
  REWRITE_CONV [ROUND_KEYS] THENC
  PRINT_TERM_CONV THENC
  REWRITE_CONV EL_15_128_CLAUSES THENC
  PRINT_TERM_CONV THENC
  REPEATC let_CONV THENC
  PRINT_TERM_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV) THENC
  ;;
evaluates to
`
word_xor
(aes_sub_bytes joined_GF2
(aes_shift_rows
(aes256_encrypt_round
 (aes256_encrypt_round
  (aes256_encrypt_round
   (aes256_encrypt_round
    (aes256_encrypt_round
     (aes256_encrypt_round
      (aes256_encrypt_round
       (aes256_encrypt_round
        (aes256_encrypt_round
         (aes256_encrypt_round
          (aes256_encrypt_round
           (aes256_encrypt_round
            (aes256_encrypt_round
             (word_xor (word 143233380420387077518460912116591433514)
             (word 127927385344373932012120245488993531777))
            (word 41482152601831359329908363118012325876))
           (word 206878388847962593259677505409113390302))
          (word 224227313700546055987490685253953870746))
         (word 283929978073507663308377981111166221974))
        (word 241468790472035055121896954896908581299))
       (word 171701502723078332096379282178375726180))
      (word 203069427764564296087722130005204943380))
     (word 138242219980614615854290912811605396864))
    (word 265954029272361673955751890726720733753))
   (word 295189406551744036947605646357814373909))
  (word 117671935837368680518160876205111210947))
 (word 155001899427603818862311956147060445274))
(word 269805595428433041131718239175312414989))))
(word 338000693600063263164096359463337616158)`
*)

let tmp = AESENC_HELPER_CONV
  `aes256_encrypt
    (word 0x6bc1bee22e409f96e93d7e117393172a)
    ROUND_KEYS`;;
(*
let AESENC_REDUCE_CONV tm =
  match tm with
    Comb(Comb(Const("aes256_encrypt",_),
         Comb(Const("word",_),state)),
         Comb(Const("word",_),roundkey))
    when is_numeral state && is_numeral roundkey -> AESENC_HELPER_CONV tm
    | _ -> failwith "AESENC_REDUCE_CONV: inapplicable";;
*)
(*
let aes256_encrypt = new_definition
  `aes256_encrypt (block:int128) (key_schedule:int128 list) =
     let res1 = word_xor block (EL 0 key_schedule) in
     let res2 = aes_shift_rows res1 in
     let res3 = aes_sub_bytes joined_GF2 res2 in
     let res4 = aes_mix_columns res3 in
     let res5 = word_xor res4 (EL 1 key_schedule) in
     let res6 = aes_shift_rows res5 in
     let res7 = aes_sub_bytes joined_GF2 res6 in
     let res8 = aes_mix_columns res7 in
     let res9 = word_xor res8 (EL 2 key_schedule) in
     let res10 = aes_shift_rows res9 in
     let res11 = aes_sub_bytes joined_GF2 res10 in
     let res12 = aes_mix_columns res11 in
     let res13 = word_xor res12 (EL 3 key_schedule) in
     let res14 = aes_shift_rows res13 in
     let res15 = aes_sub_bytes joined_GF2 res14 in
     let res16 = aes_mix_columns res15 in
     let res17 = word_xor res16 (EL 4 key_schedule) in
     let res18 = aes_shift_rows res17 in
     let res19 = aes_sub_bytes joined_GF2 res18 in
     let res20 = aes_mix_columns res19 in
     let res21 = word_xor res20 (EL 5 key_schedule) in
     let res22 = aes_shift_rows res21 in
     let res23 = aes_sub_bytes joined_GF2 res22 in
     let res24 = aes_mix_columns res23 in
     let res25 = word_xor res24 (EL 6 key_schedule) in
     let res26 = aes_shift_rows res25 in
     let res27 = aes_sub_bytes joined_GF2 res26 in
     let res28 = aes_mix_columns res27 in
     let res29 = word_xor res28 (EL 7 key_schedule) in
     let res30 = aes_shift_rows res29 in
     let res31 = aes_sub_bytes joined_GF2 res30 in
     let res32 = aes_mix_columns res31 in
     let res33 = word_xor res32 (EL 8 key_schedule) in
     let res34 = aes_shift_rows res33 in
     let res35 = aes_sub_bytes joined_GF2 res34 in
     let res36 = aes_mix_columns res35 in
     let res37 = word_xor res36 (EL 9 key_schedule) in
     let res38 = aes_shift_rows res37 in
     let res39 = aes_sub_bytes joined_GF2 res38 in
     let res40 = aes_mix_columns res39 in
     let res41 = word_xor res40 (EL 10 key_schedule) in
     let res42 = aes_shift_rows res41 in
     let res43 = aes_sub_bytes joined_GF2 res42 in
     let res44 = aes_mix_columns res43 in
     let res45 = word_xor res44 (EL 11 key_schedule) in
     let res46 = aes_shift_rows res45 in
     let res47 = aes_sub_bytes joined_GF2 res46 in
     let res48 = aes_mix_columns res47 in
     let res49 = word_xor res48 (EL 12 key_schedule) in
     let res50 = aes_shift_rows res49 in
     let res51 = aes_sub_bytes joined_GF2 res50 in
     let res52 = aes_mix_columns res51 in
     let res53 = word_xor res52 (EL 13 key_schedule) in
     let res54 = aes_shift_rows res53 in
     let res55 = aes_sub_bytes joined_GF2 res54 in
     word_xor res55 (EL 14 key_schedule)
  `;;
*)
