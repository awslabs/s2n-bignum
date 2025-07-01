use_file_raise_failure := true;;
needs "common/aes.ml";;

let pp_print_num fmt tm =
  let n = dest_numeral tm in
  pp_print_string fmt (string_of_num_hex n) in
install_user_printer("pp_print_num",pp_print_num);;

(*
NIST: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.197-upd1.pdf

procedure EQINVCIPHER(in, Nr, dw)
2: state ← in
3: state ← ADDROUNDKEY(state,dw[4 ∗Nr..4 ∗Nr +3])
4: for round from Nr −1 downto 1 do
5: state ← INVSUBBYTES(state)
6: state ← INVSHIFTROWS(state)
7: state ← INVMIXCOLUMNS(state)
8: state ← ADDROUNDKEY(state,dw[4 ∗ round..4 ∗ round +3])
9: end for
10: state ← INVSUBBYTES(state)
11: state ← INVSHIFTROWS(state)
12: state ← ADDROUNDKEY(state,dw[0..3])
13: return state
14: end procedure
*)

let aes256_decrypt_round = new_definition
  `aes256_decrypt_round (block:int128) (round_key:int128) =
     let res2 = aes_inv_shift_rows block in
     let res3 = aes_sub_bytes joined_GF2_inv res2 in
     let res1 = aes_inv_mix_columns res3 in
     word_xor res1 round_key
    `;;

let aes256_decrypt = new_definition
  `aes256_decrypt (block:int128) (key_schedule:int128 list) =
     let res0 = word_xor block (EL 0 key_schedule) in
     let res1 = aes256_decrypt_round res0 (EL 1 key_schedule) in
     let res2 = aes256_decrypt_round res1 (EL 2 key_schedule) in
     let res3 = aes256_decrypt_round res2 (EL 3 key_schedule) in
     let res4 = aes256_decrypt_round res3 (EL 4 key_schedule) in
     let res5 = aes256_decrypt_round res4 (EL 5 key_schedule) in
     let res6 = aes256_decrypt_round res5 (EL 6 key_schedule) in
     let res7 = aes256_decrypt_round res6 (EL 7 key_schedule) in
     let res8 = aes256_decrypt_round res7 (EL 8 key_schedule) in
     let res9 = aes256_decrypt_round res8 (EL 9 key_schedule) in
     let res10 = aes256_decrypt_round res9 (EL 10 key_schedule) in
     let res11 = aes256_decrypt_round res10 (EL 11 key_schedule) in
     let res12 = aes256_decrypt_round res11 (EL 12 key_schedule) in
     let res13 = aes256_decrypt_round res12 (EL 13 key_schedule) in
     let res14 = aes_inv_shift_rows res13 in
     let res15 = aes_sub_bytes joined_GF2_inv res14 in
     word_xor res15 (EL 14 key_schedule)
  `;;

let AESDEC_ROUND_HELPER_CONV =
  REWRITE_CONV [aes256_decrypt_round] THENC
  AES_INV_SHIFT_ROWS_CONV THENC
  AES_SUB_BYTES_CONV THENC
  AES_INV_MIX_COLUMNS_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let AESDEC_ROUND_REDUCE_CONV tm =
  match tm with
    Comb(Comb(Const("aes256_decrypt_round",_),
         Comb(Const("word",_),state)),
         Comb(Const("word",_),roundkey))
    when is_numeral state && is_numeral roundkey -> AESDEC_ROUND_HELPER_CONV tm
    | _ -> failwith "AESDEC_ROUND_REDUCE_CONV: inapplicable";;

(*
Test case from AWS-LC

Round keys:
0x36DE686D3CC21A37E97909BFCC79FC24
0x6E0158255FE2E9FC2FAACEBFFFD1F134
0x84E680DC46B771750A354C38EB48165E
0x31E3B1D970482743D07B3F8B8005A3C8
0xC251F1A94C823D4DE17D5A66138E70B5
0x41AB969AA03318C8507E9C43A37BDA74
0x8ED3CCE4ADFF672BF2F32AD31597A63C
0xE1988E52F04D848BF3054637F3C45FF8
0x232CABCF5F0C4DF8E7648CEF9A4069DE
0x11D50AD90348C2BC00C119CF1658D5AE
0x7C20E637B868C1177D24E531BD68C615
0x129DC8650389DB731699CC610F85D77F
0xC4482720C54C2426C04C2324C940282A
0x1114131615101712191C1B1E1D181F1A
0x0F0E0D0C0B0A09080706050403020100

ciphertext:
0x8960494b9049fceabf456751cab7a28e

plaintext:
0xffeeddccbbaa99887766554433221100
*)

(* These are the round keys with the bytes reversed to become little endian *)
let DEC_ROUND_KEYS = new_definition `DEC_ROUND_KEYS:int128 list =
  [ word 0x36DE686D3CC21A37E97909BFCC79FC24
  ; word 0x6E0158255FE2E9FC2FAACEBFFFD1F134
  ; word 0x84E680DC46B771750A354C38EB48165E
  ; word 0x31E3B1D970482743D07B3F8B8005A3C8
  ; word 0xC251F1A94C823D4DE17D5A66138E70B5
  ; word 0x41AB969AA03318C8507E9C43A37BDA74
  ; word 0x8ED3CCE4ADFF672BF2F32AD31597A63C
  ; word 0xE1988E52F04D848BF3054637F3C45FF8
  ; word 0x232CABCF5F0C4DF8E7648CEF9A4069DE
  ; word 0x11D50AD90348C2BC00C119CF1658D5AE
  ; word 0x7C20E637B868C1177D24E531BD68C615
  ; word 0x129DC8650389DB731699CC610F85D77F
  ; word 0xC4482720C54C2426C04C2324C940282A
  ; word 0x1114131615101712191C1B1E1D181F1A
  ; word 0x0F0E0D0C0B0A09080706050403020100
  ]`;;

let EL_15_128_CLAUSES =
  let pat = `EL n [x0;x1;x2;x3;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14]:128 word` in
  map (fun n -> EL_CONV(subst [mk_small_numeral n,`n:num`] pat)) (0--14);;

let AESDEC_HELPER_CONV KEYS =
  REWR_CONV aes256_decrypt THENC
  REWRITE_CONV [KEYS] THENC
  REWRITE_CONV EL_15_128_CLAUSES THENC
  REPEATC let_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV) THENC
  DEPTH_CONV AESDEC_ROUND_REDUCE_CONV THENC
  AES_INV_SHIFT_ROWS_CONV THENC
  AES_SUB_BYTES_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV)
  ;;

(*
time prove (`aes256_decrypt
    (word 0x8960494b9049fceabf456751cab7a28e)
    DEC_ROUND_KEYS = word 0xffeeddccbbaa99887766554433221100`,
    CONV_TAC(LAND_CONV (AESDEC_HELPER_CONV DEC_ROUND_KEYS)) THEN REFL_TAC);;
*)