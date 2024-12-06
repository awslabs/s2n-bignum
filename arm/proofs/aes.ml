(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "Library/words.ml";;
needs "compute.ml";;

(** TODO:define a recursive definition for word_join_list and its CONV *)

let pp_print_num fmt tm =
  let n = dest_numeral tm in
  pp_print_string fmt (string_of_num_hex n) in
install_user_printer("pp_print_num",pp_print_num);;

let TEST thms =
  let rw = Compute.bool_compset () in
  (* avoid folding the branches of conditional expression 
     before evaluating its condition *)
  let _ = Compute.set_skip rw `COND: bool -> A -> A -> A` (Some 1) in
  let _ = num_compute_add_convs rw in
  let _ = word_compute_add_convs rw in
  let _ = Compute.add_thms [EL_CONS;LET_END_DEF] rw in
  let _ = Compute.add_thms thms rw in
  Compute.WEAK_CBV_CONV rw;;

let input = new_definition
  `input:128 word = word 0xdee0b81ebfb441275d52119830aef1e5`;;

(*
bits(16*16*8) GF2 = (
        /*       F E D C B A 9 8 7 6 5 4 3 2 1 0       */
        /*F*/ 0x16bb54b00f2d99416842e6bf0d89a18c<127:0> :
        /*E*/ 0xdf2855cee9871e9b948ed9691198f8e1<127:0> :
        /*D*/ 0x9e1dc186b95735610ef6034866b53e70<127:0> :
        /*C*/ 0x8a8bbd4b1f74dde8c6b4a61c2e2578ba<127:0> :
        /*B*/ 0x08ae7a65eaf4566ca94ed58d6d37c8e7<127:0> :
        /*A*/ 0x79e4959162acd3c25c2406490a3a32e0<127:0> :
        /*9*/ 0xdb0b5ede14b8ee4688902a22dc4f8160<127:0> :
        /*8*/ 0x73195d643d7ea7c41744975fec130ccd<127:0> :
        /*7*/ 0xd2f3ff1021dab6bcf5389d928f40a351<127:0> :
        /*6*/ 0xa89f3c507f02f94585334d43fbaaefd0<127:0> :
        /*5*/ 0xcf584c4a39becb6a5bb1fc20ed00d153<127:0> :
        /*4*/ 0x842fe329b3d63b52a05a6e1b1a2c8309<127:0> :
        /*3*/ 0x75b227ebe28012079a059618c323c704<127:0> :
        /*2*/ 0x1531d871f1e5a534ccf73f362693fdb7<127:0> :
        /*1*/ 0xc072a49cafa2d4adf04759fa7dc982ca<127:0> :
        /*0*/ 0x76abd7fe2b670130c56f6bf27b777c63<127:0>
    );
*)
let GF2 = new_definition `GF2:((128)word) list =
  [ word 0x16bb54b00f2d99416842e6bf0d89a18c
  ; word 0xdf2855cee9871e9b948ed9691198f8e1
  ; word 0x9e1dc186b95735610ef6034866b53e70
  ; word 0x8a8bbd4b1f74dde8c6b4a61c2e2578ba
  ; word 0x08ae7a65eaf4566ca94ed58d6d37c8e7
  ; word 0x79e4959162acd3c25c2406490a3a32e0
  ; word 0xdb0b5ede14b8ee4688902a22dc4f8160
  ; word 0x73195d643d7ea7c41744975fec130ccd
  ; word 0xd2f3ff1021dab6bcf5389d928f40a351
  ; word 0xa89f3c507f02f94585334d43fbaaefd0
  ; word 0xcf584c4a39becb6a5bb1fc20ed00d153
  ; word 0x842fe329b3d63b52a05a6e1b1a2c8309
  ; word 0x75b227ebe28012079a059618c323c704
  ; word 0x1531d871f1e5a534ccf73f362693fdb7
  ; word 0xc072a49cafa2d4adf04759fa7dc982ca
  ; word 0x76abd7fe2b670130c56f6bf27b777c63
  ]`;;

TEST [GF2] `GF2`;;

let joined_GF2 = new_definition `joined_GF2:(2048)word =
  ((word_join:128 word->1920 word->2048 word) (EL 0 GF2)
    ((word_join:128 word->1792 word->1920 word) (EL 1 GF2)
     ((word_join:128 word->1664 word->1792 word) (EL 2 GF2)
      ((word_join:128 word->1536 word->1664 word) (EL 3 GF2)
       ((word_join:128 word->1408 word->1536 word) (EL 4 GF2)
        ((word_join:128 word->1280 word->1408 word) (EL 5 GF2)
         ((word_join:128 word->1152 word->1280 word) (EL 6 GF2)
          ((word_join:128 word->1024 word->1152 word) (EL 7 GF2)
           ((word_join:128 word->896 word->1024 word) (EL 8 GF2)
            ((word_join:128 word->768 word->896 word) (EL 9 GF2)
             ((word_join:128 word->640 word->768 word) (EL 10 GF2)
              ((word_join:128 word->512 word->640 word) (EL 11 GF2)
               ((word_join:128 word->384 word->512 word) (EL 12 GF2)
                ((word_join:128 word->256 word->384 word) (EL 13 GF2)
                 ((word_join:128 word->128 word->256 word) (EL 14 GF2) 
                  (EL 15 GF2))))))))))))))))`;;

TEST [joined_GF2; GF2] `joined_GF2`;;

let aes_sub_bytes_select = new_definition 
`aes_sub_bytes_select (op:128 word) (i : num) : 8 word =
  let pos = (val ((word_subword:128 word->(num#num)->8 word) op (i*8, 8)))*8 in
  (word_subword:2048 word->(num#num)->8 word) joined_GF2 (pos, 8)`;;

TEST [joined_GF2; GF2; aes_sub_bytes_select; input] 
`aes_sub_bytes_select input 0`;;

let aes_sub_bytes = new_definition 
`aes_sub_bytes (op:(128)word) : (128)word =
  ((word_join:8 word->120 word->128 word) (aes_sub_bytes_select op 15)
    ((word_join:8 word->112 word->120 word) (aes_sub_bytes_select op 14)
      ((word_join:8 word->104 word->112 word) (aes_sub_bytes_select op 13)
        ((word_join:8 word->96 word->104 word) (aes_sub_bytes_select op 12)
          ((word_join:8 word->88 word->96 word) (aes_sub_bytes_select op 11)
            ((word_join:8 word->80 word->88 word) (aes_sub_bytes_select op 10)
              ((word_join:8 word->72 word->80 word) (aes_sub_bytes_select op 9)
                ((word_join:8 word->64 word->72 word) (aes_sub_bytes_select op 8)
                  ((word_join:8 word->56 word->64 word) (aes_sub_bytes_select op 7)
                    ((word_join:8 word->48 word->56 word) (aes_sub_bytes_select op 6)
                      ((word_join:8 word->40 word->48 word) (aes_sub_bytes_select op 5)
                        ((word_join:8 word->32 word->40 word) (aes_sub_bytes_select op 4)
                          ((word_join:8 word->24 word->32 word) (aes_sub_bytes_select op 3)
                            ((word_join:8 word->16 word->24 word) (aes_sub_bytes_select op 2)
                              ((word_join:8 word->8 word->16 word) (aes_sub_bytes_select op 1)
                                (aes_sub_bytes_select op 0)))))))))))))))) `;;

TEST [joined_GF2; GF2; aes_sub_bytes_select; aes_sub_bytes; input] 
`aes_sub_bytes input`;;

let aes_shift_rows = new_definition `aes_shift_rows (op:(128)word) : (128)word =
  ((word_join:8 word->120 word->128 word) (word_subword op (88, 8))
    ((word_join:8 word->112 word->120 word) (word_subword op (48, 8))
      ((word_join:8 word->104 word->112 word) (word_subword op (8, 8))
        ((word_join:8 word->96 word->104 word) (word_subword op (96, 8))
          ((word_join:8 word->88 word->96 word) (word_subword op (56, 8))
            ((word_join:8 word->80 word->88 word) (word_subword op (16, 8))
              ((word_join:8 word->72 word->80 word) (word_subword op (104, 8))
                ((word_join:8 word->64 word->72 word) (word_subword op (64, 8))
                  ((word_join:8 word->56 word->64 word) (word_subword op (24, 8))
                    ((word_join:8 word->48 word->56 word) (word_subword op (112, 8))
                      ((word_join:8 word->40 word->48 word) (word_subword op (72, 8))
                        ((word_join:8 word->32 word->40 word) (word_subword op (32, 8))
                          ((word_join:8 word->24 word->32 word) (word_subword op (120, 8))
                            ((word_join:8 word->16 word->24 word) (word_subword op (80, 8))
                              ((word_join:8 word->8 word->16 word) (word_subword op (40, 8))
                                (word_subword op (0, 8))))))))))))))))) `;;

TEST [aes_shift_rows; input] `aes_shift_rows input`;;

let FFmul_02 = new_definition `FFmul_02:(((128)word) list) = [
    word 0xE5E7E1E3EDEFE9EBF5F7F1F3FDFFF9FB
  ; word 0xC5C7C1C3CDCFC9CBD5D7D1D3DDDFD9DB
  ; word 0xA5A7A1A3ADAFA9ABB5B7B1B3BDBFB9BB
  ; word 0x858781838D8F898B959791939D9F999B
  ; word 0x656761636D6F696B757771737D7F797B
  ; word 0x454741434D4F494B555751535D5F595B
  ; word 0x252721232D2F292B353731333D3F393B
  ; word 0x050701030D0F090B151711131D1F191B
  ; word 0xFEFCFAF8F6F4F2F0EEECEAE8E6E4E2E0
  ; word 0xDEDCDAD8D6D4D2D0CECCCAC8C6C4C2C0
  ; word 0xBEBCBAB8B6B4B2B0AEACAAA8A6A4A2A0
  ; word 0x9E9C9A98969492908E8C8A8886848280
  ; word 0x7E7C7A78767472706E6C6A6866646260
  ; word 0x5E5C5A58565452504E4C4A4846444240
  ; word 0x3E3C3A38363432302E2C2A2826242220
  ; word 0x1E1C1A18161412100E0C0A0806040200 ]`;;

let joined_FFmul_02 = new_definition `joined_FFmul_02:2048 word =
  ((word_join:128 word->1920 word->2048 word) (EL 0 FFmul_02)
    ((word_join:128 word->1792 word->1920 word) (EL 1 FFmul_02)
     ((word_join:128 word->1664 word->1792 word) (EL 2 FFmul_02)
      ((word_join:128 word->1536 word->1664 word) (EL 3 FFmul_02)
       ((word_join:128 word->1408 word->1536 word) (EL 4 FFmul_02)
        ((word_join:128 word->1280 word->1408 word) (EL 5 FFmul_02)
         ((word_join:128 word->1152 word->1280 word) (EL 6 FFmul_02)
          ((word_join:128 word->1024 word->1152 word) (EL 7 FFmul_02)
           ((word_join:128 word->896 word->1024 word) (EL 8 FFmul_02)
            ((word_join:128 word->768 word->896 word) (EL 9 FFmul_02)
             ((word_join:128 word->640 word->768 word) (EL 10 FFmul_02)
              ((word_join:128 word->512 word->640 word) (EL 11 FFmul_02)
               ((word_join:128 word->384 word->512 word) (EL 12 FFmul_02)
                ((word_join:128 word->256 word->384 word) (EL 13 FFmul_02)
                 ((word_join:128 word->128 word->256 word) (EL 14 FFmul_02) 
                  (EL 15 FFmul_02))))))))))))))))`;;

let FFmul02 = new_definition `FFmul02 (b : 8 word) : 8 word = 
  (word_subword:2048 word->(num#num)->8 word) joined_FFmul_02 ((val b)*8, 8) `;;

TEST [FFmul02; FFmul_02; joined_FFmul_02] `FFmul02 (word 0x2a)`;;

let FFmul_03 = new_definition `FFmul_03:(((128)word) list) = [
    word 0x1A191C1F16151013020104070E0D080B
  ; word 0x2A292C2F26252023323134373E3D383B
  ; word 0x7A797C7F76757073626164676E6D686B
  ; word 0x4A494C4F46454043525154575E5D585B
  ; word 0xDAD9DCDFD6D5D0D3C2C1C4C7CECDC8CB
  ; word 0xEAE9ECEFE6E5E0E3F2F1F4F7FEFDF8FB
  ; word 0xBAB9BCBFB6B5B0B3A2A1A4A7AEADA8AB
  ; word 0x8A898C8F86858083929194979E9D989B
  ; word 0x818287848D8E8B88999A9F9C95969390
  ; word 0xB1B2B7B4BDBEBBB8A9AAAFACA5A6A3A0
  ; word 0xE1E2E7E4EDEEEBE8F9FAFFFCF5F6F3F0
  ; word 0xD1D2D7D4DDDEDBD8C9CACFCCC5C6C3C0
  ; word 0x414247444D4E4B48595A5F5C55565350
  ; word 0x717277747D7E7B78696A6F6C65666360
  ; word 0x212227242D2E2B28393A3F3C35363330
  ; word 0x111217141D1E1B18090A0F0C05060300 ]`;;

let joined_FFmul_03 = new_definition `joined_FFmul_03:2048 word =
  ((word_join:128 word->1920 word->2048 word) (EL 0 FFmul_03)
    ((word_join:128 word->1792 word->1920 word) (EL 1 FFmul_03)
     ((word_join:128 word->1664 word->1792 word) (EL 2 FFmul_03)
      ((word_join:128 word->1536 word->1664 word) (EL 3 FFmul_03)
       ((word_join:128 word->1408 word->1536 word) (EL 4 FFmul_03)
        ((word_join:128 word->1280 word->1408 word) (EL 5 FFmul_03)
         ((word_join:128 word->1152 word->1280 word) (EL 6 FFmul_03)
          ((word_join:128 word->1024 word->1152 word) (EL 7 FFmul_03)
           ((word_join:128 word->896 word->1024 word) (EL 8 FFmul_03)
            ((word_join:128 word->768 word->896 word) (EL 9 FFmul_03)
             ((word_join:128 word->640 word->768 word) (EL 10 FFmul_03)
              ((word_join:128 word->512 word->640 word) (EL 11 FFmul_03)
               ((word_join:128 word->384 word->512 word) (EL 12 FFmul_03)
                ((word_join:128 word->256 word->384 word) (EL 13 FFmul_03)
                 ((word_join:128 word->128 word->256 word) (EL 14 FFmul_03) 
                  (EL 15 FFmul_03))))))))))))))))`;;

let FFmul03 = new_definition `FFmul03 (b : 8 word) : 8 word =
  (word_subword:2048 word->(num#num)->8 word) joined_FFmul_03 ((val b)*8, 8) `;;

TEST [FFmul03; FFmul_03; joined_FFmul_03] `FFmul03 (word 0x2a)`;;

let aes_mix_word = new_definition 
`aes_mix_word (op:(128)word) (a:num) (b:num) (c:num) (d:num) : (8)word =
  word_xor (FFmul02 (word_subword op (a, 8)))
    (word_xor (FFmul03 (word_subword op (b, 8)))
      (word_xor (word_subword op (c, 8))
        (word_subword op (d, 8)))) `;;

TEST [aes_mix_word; FFmul02; FFmul03; input] `aes_mix_word input 0 8 16 24`;;

let aes_mix_columns = new_definition `aes_mix_columns (op:(128)word) : (128)word =
    let out00 = aes_mix_word op 0 8 16 24 in
    let out10 = aes_mix_word op 8 16 24 0 in
    let out20 = aes_mix_word op 16 24 0 8 in
    let out30 = aes_mix_word op 24 0 8 16 in
    let out01 = aes_mix_word op 32 40 48 56 in
    let out11 = aes_mix_word op 40 48 56 32 in
    let out21 = aes_mix_word op 48 56 32 40 in
    let out31 = aes_mix_word op 56 32 40 48 in
    let out02 = aes_mix_word op 64 72 80 88 in
    let out12 = aes_mix_word op 72 80 88 64 in
    let out22 = aes_mix_word op 80 88 64 72 in
    let out32 = aes_mix_word op 88 64 72 80 in
    let out03 = aes_mix_word op 96 104 112 120 in
    let out13 = aes_mix_word op 104 112 120 96 in
    let out23 = aes_mix_word op 112 120 96 104 in
    let out33 = aes_mix_word op 120 96 104 112 in
    (word_join:8 word->120 word->128 word) out33
      ((word_join:8 word->112 word->120 word) out23
        ((word_join:8 word->104 word->112 word) out13
          ((word_join:8 word->96 word->104 word) out03
            ((word_join:8 word->88 word->96 word) out32
              ((word_join:8 word->80 word->88 word) out22
                ((word_join:8 word->72 word->80 word) out12
                  ((word_join:8 word->64 word->72 word) out02
                    ((word_join:8 word->56 word->64 word) out31
                      ((word_join:8 word->48 word->56 word) out21
                        ((word_join:8 word->40 word->48 word) out11
                          ((word_join:8 word->32 word->40 word) out01
                            ((word_join:8 word->24 word->32 word) out30
                              ((word_join:8 word->16 word->24 word) out20
                                ((word_join:8 word->8 word->16 word) out10 out00)))))))))))))) `;;

time (TEST [aes_mix_columns; aes_mix_word; FFmul02; FFmul03; input])
`aes_mix_columns input`;;

(* ========================================================================= *)
(* AESE                                                                      *)
(* ========================================================================= *)
let aese = new_definition `aese (d:128 word) (n:128 word) =
  aes_sub_bytes (aes_shift_rows (word_xor d n)) `;;

TEST [aese; aes_shift_rows; aes_sub_bytes; aes_sub_bytes_select; joined_GF2; GF2]
`aese (word 0xae6910a45715645a02502baaf5a826c9) (word 0xec882f3270973907d69635eea82d71)`;;

(* ========================================================================= *)
(* AESMC                                                                     *)
(* ========================================================================= *)
let aesmc = new_definition `aesmc (n: 128 word) = aes_mix_columns n`;;


(************************************************)
(** CONVERSIONS FOR AESE and AESMC             **)
(************************************************)

let EL_CONV =
  let conv0 = GEN_REWRITE_CONV I [CONJUNCT1 EL] THENC GEN_REWRITE_CONV I [HD]
  and conv1 = GEN_REWRITE_CONV I [CONJUNCT2 EL]
  and convt = GEN_REWRITE_CONV I [TL] in
  let convs = LAND_CONV num_CONV THENC conv1 THENC RAND_CONV convt in
  let rec conv tm = (conv0 ORELSEC (convs THENC conv)) tm in
  conv;;
let EL_CLAUSES =
  let pat = `EL n [x0;x1;x2;x3;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14;x15]:128 word` in
  map (fun n -> EL_CONV(subst [mk_small_numeral n,`n:num`] pat)) (0--15);;

(** Compute EL n x in which x is a constant before-hand. 
    This allows conversions on subsequent functions to be 
    faster, because it avoids the expensive computation of ELs. *)
let joined_GF2_CONV =
  GEN_REWRITE_CONV I [joined_GF2] THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [GF2] THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV EL_CLAUSES THENC
  DEPTH_CONV WORD_JOIN_CONV;;

let joined_FFmul_02_CONV =
  GEN_REWRITE_CONV I [joined_FFmul_02] THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [FFmul_02] THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV EL_CLAUSES THENC
  DEPTH_CONV WORD_JOIN_CONV;;

let joined_FFmul_03_CONV =
  GEN_REWRITE_CONV I [joined_FFmul_03] THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [FFmul_03] THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV EL_CLAUSES THENC
  DEPTH_CONV WORD_JOIN_CONV;;

let aes_sub_bytes_select_CONV = REWRITE_CONV [aes_sub_bytes_select]
  THENC GEN_REWRITE_CONV ONCE_DEPTH_CONV [joined_GF2_CONV `joined_GF2`]
  THENC TOP_DEPTH_CONV let_CONV
  THENC DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;
let aes_sub_bytes_CONV = REWRITE_CONV [aes_sub_bytes]
  THENC aes_sub_bytes_select_CONV
  THENC DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;
let aes_shift_rows_CONV = REWRITE_CONV [aes_shift_rows]
  THENC DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;
let FFmul02_CONV = REWRITE_CONV [FFmul02]
  THENC GEN_REWRITE_CONV ONCE_DEPTH_CONV [joined_FFmul_02_CONV `joined_FFmul_02`]
  THENC DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;
let FFmul03_CONV = REWRITE_CONV [FFmul03]
  THENC GEN_REWRITE_CONV ONCE_DEPTH_CONV [joined_FFmul_03_CONV `joined_FFmul_03`]
  THENC DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;
let aes_mix_word_CONV = REWRITE_CONV [aes_mix_word]
  THENC FFmul02_CONV
  THENC FFmul03_CONV
  THENC DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;
let aes_mix_columns_CONV = REWRITE_CONV [aes_mix_columns]
  THENC aes_mix_word_CONV
  THENC TOP_DEPTH_CONV let_CONV
  THENC DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;
let aese_helper_CONV = REWRITE_CONV [aese]
  THENC aes_shift_rows_CONV
  THENC aes_sub_bytes_CONV
  THENC DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;
let aesmc_helper_CONV = REWRITE_CONV [aesmc]
  THENC aes_mix_columns_CONV;;

(** Stop early if unmatched. Conversions will become extremely expensive if we don't stop early *)
let aese_CONV tm =
    match tm with
      Comb(Comb(Const("aese",_),
           Comb(Const("word",_),d)),
           Comb(Const("word",_),n))
    when is_numeral d && is_numeral n -> aese_helper_CONV tm
  | _ -> failwith "aese_CONV: inapplicable";;
let aesmc_CONV tm =
    match tm with
      Comb(Const("aesmc",_), Comb(Const("word",_),n))
    when is_numeral n -> aesmc_helper_CONV tm
  | _ -> failwith "aesmc_CONV: inapplicable";;

joined_GF2_CONV `joined_GF2`;;
(REWRITE_CONV [input] THENC aes_sub_bytes_select_CONV) `aes_sub_bytes_select input 0`;;
(REWRITE_CONV [input] THENC aes_sub_bytes_CONV) `aes_sub_bytes input`;;
(REWRITE_CONV [input] THENC aes_shift_rows_CONV) `aes_shift_rows input`;;
time FFmul02_CONV `FFmul02 (word 0x2a)`;;
time FFmul03_CONV `FFmul03 (word 0x2a)`;;
time (REWRITE_CONV [input] THENC aes_mix_word_CONV) `aes_mix_word input 0 8 16 24`;;
time (REWRITE_CONV [input] THENC aes_mix_columns_CONV) `aes_mix_columns input`;;
time (REWRITE_CONV [input] THENC aese_CONV) `aese (word 0xae6910a45715645a02502baaf5a826c9) (word 0xec882f3270973907d69635eea82d71)`;;
time (REWRITE_CONV [input] THENC aesmc_CONV) `aesmc (word 0xae6910a45715645a02502baaf5a826c9)`;;



(* let aes_inv_sub_bytes = new_definition ``;;

let aes_inv_shift_rows = new_definition ``;;

let aes_inv_mix_columns = new_definition ``;; *)

(* ========================================================================= *)
(* AESD                                                                      *)
(* ========================================================================= *)

(* ========================================================================= *)
(* AESIMC                                                                    *)
(* ========================================================================= *)




