use_file_raise_failure := true;;
needs "common/aes.ml";;
loadt "arm/proofs/aes_encrypt_spec.ml";;
loadt "arm/proofs/aes_decrypt_spec.ml";;

let pp_print_num fmt tm =
  let n = dest_numeral tm in
  pp_print_string fmt (string_of_num_hex n) in
install_user_printer("pp_print_num",pp_print_num);;

(*
https://ieeexplore.ieee.org/stamp/stamp.jsp?tp=&arnumber=8637988

*)

let xts_init_tweak = new_definition
  `xts_init_tweak (iv:int128) (key_schedule:int128 list) =
    aes256_encrypt iv key_schedule`;;

let aes256_xts_decrypt_round = new_definition
  ``;;
