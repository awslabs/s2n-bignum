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
let aes256_encrypt = new_definition
  `aes256_encrypt (block:int128) (key_schedule:int128 list) =
     let res1 = word_xor block (EL 0 key_schedule) in
     let res2 = aes_sub_bytes joined_GF2 res1 in
     word_xor res2 (EL 14 key_schedule)
  `;;
