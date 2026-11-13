(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The rho offsets of common/fips202/fips202.ml come from FIPS 202            *)
(* Algorithm 2.                                                               *)
(* ========================================================================= *)

needs "common/fips202/fips202.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The rho offsets come from FIPS 202 Algorithm 2: starting at (x,y) = (1,0) *)
(* and stepping (x,y) -> (y,2x+3y mod 5), the t-th lane visited (t < 24) is  *)
(* rotated by (t+1)(t+2)/2; lane (0,0) is not rotated.                       *)
(* ------------------------------------------------------------------------- *)

let keccak_rho_pos = define
 `keccak_rho_pos 0 = (1,0) /\
  keccak_rho_pos (SUC t) =
    (SND(keccak_rho_pos t),
     (2 * FST(keccak_rho_pos t) + 3 * SND(keccak_rho_pos t)) MOD 5)`;;

let KECCAK_RHO_OFFSET_ALGORITHM = prove
 (`keccak_rho_offset 0 0 = 0 /\
   !t. t < 24
       ==> keccak_rho_offset (FST(keccak_rho_pos t)) (SND(keccak_rho_pos t)) =
           (((t + 1) * (t + 2)) DIV 2) MOD 64`,
  let posconv =
    let th0,th1 = CONJ_PAIR keccak_rho_pos in
    let cache = ref [0,th0] in
    let rec get n =
      try assoc n (!cache) with Failure _ ->
      let thp = get (n - 1) in
      let tm = mk_comb(`keccak_rho_pos`,mk_small_numeral n) in
      let th = (RAND_CONV num_CONV THENC REWR_CONV th1 THENC
                PURE_REWRITE_CONV[thp] THENC REWRITE_CONV[] THENC
                NUM_REDUCE_CONV) tm in
      cache := (n,th)::(!cache); th in
    fun tm -> match tm with
        Comb(Const("keccak_rho_pos",_),n) when is_numeral n ->
          get (Num.int_of_num(dest_numeral n))
      | _ -> failwith "posconv" in
  CONJ_TAC THENL
   [REWRITE_TAC[keccak_rho_offset] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV;
    CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV posconv) THEN
    REWRITE_TAC[keccak_rho_offset] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN CONV_TAC NUM_REDUCE_CONV]);;

(* Restore the default setting for anything loaded later.                    *)

type_invention_error := false;;
