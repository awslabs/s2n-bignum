(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* A functional specification of the top level of mldsa-native's portable C  *)
(* implementation (sign.c): key generation, signing and verification, in the *)
(* style of the other common/mldsa_native_*.ml files, following the C code.  *)
(* ========================================================================= *)

needs "common/mldsa_native_sampling.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "common/mldsa_native_hints.ml";;
needs "common/mldsa_native_challenge.ml";;

(* ------------------------------------------------------------------------- *)
(* The vector t = A * s1 + s2 of key generation as mld_compute_pack_t0_t1    *)
(* computes it, row by row: polynomial k is the inverse NTT of the product   *)
(* of row k of the matrix with s1hat (s1 in the NTT domain), plus            *)
(* polynomial k of s2, unpacked from its p bytes with unpack, reduced and    *)
(* made nonnegative. The matrix has l columns and is expanded from rho.      *)
(* ------------------------------------------------------------------------- *)

let mld_compute_t = new_definition
 `mld_compute_t l (unpack:(num->byte)->num->int32) p rho (s1hat:num->int32)
                (s2:num->byte) =
    mld_polyvec
     (\k. mld_poly_caddq
           (mld_poly_reduce
             (mld_poly_add
               (mld_poly_invntt_tomont
                 (mld_polyvec_pointwise_acc_montgomery l
                   (\j. mld_polyvec_matrix_expand l rho ((256 * l) * k + j))
                   s1hat))
               (unpack (\t. s2(p * k + t))))))`;;

(* ------------------------------------------------------------------------- *)
(* Byte j of the packing of polynomial k of t1 or t0 depends only on the     *)
(* coefficients of the polynomial (those below 256), so that it is the       *)
(* packing of the polynomial as the code computes it.                        *)
(* ------------------------------------------------------------------------- *)

let MLD_POLYT1_PACK_LOCAL = prove
 (`!(a:num->int32) b j.
        (!i. i < 256 ==> a i = b i) /\ j < 320
        ==> mld_polyt1_pack a j = mld_polyt1_pack b j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_polyt1_pack] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `!m. m < 4 ==> (a:num->int32)(4 * j DIV 5 + m) =
                              b(4 * j DIV 5 + m)` MP_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `j DIV 5 < 64` MP_TAC THENL
     [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]]);;

let MLD_POLYT0_PACK_LOCAL = prove
 (`!(a:num->int32) b j.
        (!i. i < 256 ==> a i = b i) /\ j < 416
        ==> mld_polyt0_pack a j = mld_polyt0_pack b j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_polyt0_pack] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `!m. m < 8 ==> (a:num->int32)(8 * j DIV 13 + m) =
                              b(8 * j DIV 13 + m)` MP_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `j DIV 13 < 32` MP_TAC THENL
     [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]]);;

let MLD_COMPUTE_T_PACK_T1 = prove
 (`!l (unpack:(num->byte)->num->int32) p r sh s2b i k.
        k < 320
        ==> mld_polyvec_pack 320 mld_polyt1_pack
             (mld_polyvec_map mld_poly_power2round_hi
               (mld_compute_t l unpack p r sh s2b)) (320 * i + k) =
            mld_polyt1_pack
             (mld_poly_power2round_hi
               (mld_poly_caddq
                 (mld_poly_reduce
                   (mld_poly_add
                     (mld_poly_invntt_tomont
                       (mld_polyvec_pointwise_acc_montgomery l
                         (\j. mld_polyvec_matrix_expand l r
                                ((256 * l) * i + j))
                         sh))
                     (unpack (\t. s2b(p * i + t))))))) k`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLD_POLYVEC_PACK_COEFF] THEN
  MATCH_MP_TAC MLD_POLYT1_PACK_LOCAL THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[MLD_POLY_OF_POLYVEC_MAP; mld_poly_power2round_hi; mld_compute_t;
           MLD_POLY_OF_POLYVEC]);;

let MLD_COMPUTE_T_PACK_T0 = prove
 (`!l (unpack:(num->byte)->num->int32) p r sh s2b i k.
        k < 416
        ==> mld_polyvec_pack 416 mld_polyt0_pack
             (mld_polyvec_map mld_poly_power2round_lo
               (mld_compute_t l unpack p r sh s2b)) (416 * i + k) =
            mld_polyt0_pack
             (mld_poly_power2round_lo
               (mld_poly_caddq
                 (mld_poly_reduce
                   (mld_poly_add
                     (mld_poly_invntt_tomont
                       (mld_polyvec_pointwise_acc_montgomery l
                         (\j. mld_polyvec_matrix_expand l r
                                ((256 * l) * i + j))
                         sh))
                     (unpack (\t. s2b(p * i + t))))))) k`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLD_POLYVEC_PACK_COEFF] THEN
  MATCH_MP_TAC MLD_POLYT0_PACK_LOCAL THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[MLD_POLY_OF_POLYVEC_MAP; mld_poly_power2round_lo; mld_compute_t;
           MLD_POLY_OF_POLYVEC]);;

(* ------------------------------------------------------------------------- *)
(* mld_ct_memcmp (ct.h): 0 if the first len bytes of a and b are equal, and  *)
(* 255 otherwise.                                                            *)
(* ------------------------------------------------------------------------- *)

let mld_ct_memcmp = new_definition
 `mld_ct_memcmp (a:num->byte) (b:num->byte) len =
    if !i. i < len ==> a i = b i then word 0 else word 255:byte`;;

(* ------------------------------------------------------------------------- *)
(* mld_sign_pk_from_sk (sign.c): the public key of a secret key sk of k, l   *)
(* and eta, given byte by byte as sk, with rho in bytes 0 to 31, the key in  *)
(* 32 to 63, tr in 64 to 127, then s1 and s2 (l and k polynomials packed in  *)
(* p bytes each with unpack) and t0 (k polynomials of 416 bytes). The code   *)
(* recomputes t from rho, s1 and s2 as key generation does (mld_compute_t),  *)
(* packs rho and t1 into pk, and checks that s1 and s2 are within the bound  *)
(* eta + 1, that t0 is the one recomputed and tr the SHAKE256 hash of pk;    *)
(* only the result of the check is declassified.                             *)
(* ------------------------------------------------------------------------- *)

let mld_sk_rho = new_definition
 `mld_sk_rho (sk:num->byte) = num_of_bytelist(list_of_seq sk 32)`;;

let mld_sk_s1 = new_definition
 `mld_sk_s1 (unpack:(num->byte)->num->int32) p (sk:num->byte) =
    mld_polyvec_unpack p unpack (\j. sk(128 + j))`;;

let mld_sk_s2 = new_definition
 `mld_sk_s2 l (unpack:(num->byte)->num->int32) p (sk:num->byte) =
    mld_polyvec_unpack p unpack (\j. sk(128 + l * p + j))`;;

let mld_pk_from_sk_t = new_definition
 `mld_pk_from_sk_t l (unpack:(num->byte)->num->int32) p (sk:num->byte) =
    mld_compute_t l unpack p (mld_sk_rho sk)
     (mld_polyvec_map mld_poly_ntt (mld_sk_s1 unpack p sk))
     (\j. sk(128 + l * p + j))`;;

let mld_pk_from_sk_pk = new_definition
 `mld_pk_from_sk_pk l (unpack:(num->byte)->num->int32) p (sk:num->byte) =
    \j. if j < 32 then sk j
        else mld_polyvec_pack 320 mld_polyt1_pack
              (mld_polyvec_map mld_poly_power2round_hi
                (mld_pk_from_sk_t l unpack p sk)) (j - 32)`;;

let mld_pk_from_sk_valid = new_definition
 `mld_pk_from_sk_valid k l eta (unpack:(num->byte)->num->int32) p
                       (sk:num->byte) <=>
    word_zx(word_or (mld_polyvec_chknorm l (mld_sk_s1 unpack p sk)
                       (word(eta + 1)))
                    (mld_polyvec_chknorm k (mld_sk_s2 l unpack p sk)
                       (word(eta + 1)))):byte = word 0 /\
    mld_ct_memcmp
     (mld_polyvec_pack 416 mld_polyt0_pack
       (mld_polyvec_map mld_poly_power2round_lo
         (mld_pk_from_sk_t l unpack p sk)))
     (\j. sk(128 + (l + k) * p + j)) (416 * k) = word 0 /\
    mld_ct_memcmp (\j. sk(64 + j))
     (mld_shake256_byte (32 + 320 * k)
       (num_of_bytelist
         (list_of_seq (mld_pk_from_sk_pk l unpack p sk) (32 + 320 * k))))
     64 = word 0`;;

(* ------------------------------------------------------------------------- *)
(* mld_sign_verify_internal (sign.c) for k, l and the other parameters (see  *)
(* the statements for the values): mu is either given (external mu) or       *)
(* mld_verify_mu, H(H(pk, 64) || pre || m, 64) with the byte strings as      *)
(* numbers (as for mld_H); row i of w1' is mld_verify_w1 before packing, the *)
(* use of the hint of the signature on the high part of A z - c t1 2^d; and  *)
(* the signature sig (c~, z, the hints) is accepted (mld_verify_internal_ok) *)
(* if z is within the bound bnd = gamma1 - beta, the hints unpack, and c~ is *)
(* H(mu || w1 packed, ctlen). The code returns 0 if it is accepted, and      *)
(* MLD_ERR_INVALID_SIGNATURE (-6) otherwise.                                 *)
(* ------------------------------------------------------------------------- *)

let mld_verify_mu = new_definition
 `mld_verify_mu pklen (pk:num->byte) prelen pre mlen m =
    num_of_bytelist(list_of_seq
     (mld_shake256_byte (64 + prelen + mlen)
       (num_of_bytelist(list_of_seq
          (mld_shake256_byte pklen (num_of_bytelist(list_of_seq pk pklen)))
          64) +
        2 EXP 512 * (pre + 2 EXP (8 * prelen) * m)))
     64)`;;

let mld_verify_w1 = new_definition
 `mld_verify_w1 l (usehint:(num->int32)->(num->int32)->num->int32) rho
                (zhat:num->int32) (cphat:num->int32) (pk:num->byte)
                omega (hb:num->byte) i =
    usehint
     (mld_poly_caddq
       (mld_poly_invntt_tomont
         (mld_poly_reduce
           (mld_poly_sub
             (mld_polyvec_pointwise_acc_montgomery l
               (\j. mld_polyvec_matrix_expand l rho ((256 * l) * i + j)) zhat)
             (mld_poly_pointwise_montgomery
               (mld_poly_ntt
                 (mld_poly_shiftl
                   (mld_polyt1_unpack (\j. pk(32 + 320 * i + j)))))
               cphat)))))
     (mld_unpack_hints omega hb i)`;;

let mld_verify_internal_ok = new_definition
 `mld_verify_internal_ok k l ctlen (zunpack:(num->byte)->num->int32) zp bnd
                         (usehint:(num->int32)->(num->int32)->num->int32)
                         (w1pack:(num->int32)->num->byte) w1p omega tau
                         (sig:num->byte) (pk:num->byte) mu <=>
    let z = mld_polyvec_unpack zp zunpack (\j. sig(ctlen + j)) in
    let hb = \t. sig(ctlen + l * zp + t) in
    let rho = num_of_bytelist(list_of_seq pk 32) in
    let c = num_of_bytelist(list_of_seq sig ctlen) in
    let zhat = mld_polyvec_map mld_poly_ntt z in
    let cphat = mld_poly_ntt (mld_poly_challenge tau ctlen c) in
    let w1b = mld_polyvec_pack w1p w1pack
               (mld_polyvec (mld_verify_w1 l usehint rho zhat cphat pk
                                           omega hb)) in
    mld_polyvec_chknorm l z (word bnd) = word 0 /\
    (!i. i < k ==> mld_unpack_hints_ret omega k hb i = word 0) /\
    (!j. j < ctlen
         ==> sig j =
             mld_shake256_byte (64 + k * w1p)
              (mu + 2 EXP 512 * num_of_bytelist(list_of_seq w1b (k * w1p)))
              j)`;;

(* ------------------------------------------------------------------------- *)
(* Signing (mld_sign_signature_internal and mld_attempt_signature_generation *)
(* in sign.c). mu is either given (external mu) or mld_sign_mu,              *)
(* H(tr || pre || m, 64), and rho'' is mld_sign_rhoprime,                    *)
(* H(key || rnd || mu, 64), with the byte strings as numbers. The attempt    *)
(* with counter kappa samples y (polynomial j from rho'' and kappa + j, with *)
(* g1), computes w = A * y, made nonnegative (mld_sign_w), w1 packed         *)
(* (mld_sign_w1, w1enc packing the high part of a polynomial in w1p bytes),  *)
(* c~ = H(mu || w1 packed, ctlen) (mld_sign_ctilde) and the challenge        *)
(* (mld_sign_cphat, in the NTT domain), and then, in the order of the code,  *)
(* z_i = y_i + c s1_i (mld_sign_z), checked against bndz = gamma1 - beta,    *)
(* and for each row j, w0_j - c s2_j (mld_sign_r0, w0_j being the low part   *)
(* dlo of w_j) against bndw = gamma2 - beta and c t0_j (mld_sign_ct0)        *)
(* against bndh = gamma2, and finally the number of hints of the k rows of   *)
(* w0 - c s2 + c t0 (mld_sign_hint_x) and w1 packed (mld_sign_hint_w1),      *)
(* zero elsewhere, against omega.                                            *)
(* ------------------------------------------------------------------------- *)

let mld_sign_mu = new_definition
 `mld_sign_mu (tr:num->byte) prelen pre mlen m =
    num_of_bytelist(list_of_seq
     (mld_shake256_byte (64 + prelen + mlen)
       (num_of_bytelist(list_of_seq tr 64) +
        2 EXP 512 * (pre + 2 EXP (8 * prelen) * m)))
     64)`;;

let mld_sign_rhoprime = new_definition
 `mld_sign_rhoprime (key:num->byte) rnd mu =
    num_of_bytelist(list_of_seq
     (mld_shake256_byte 128
       (num_of_bytelist(list_of_seq key 32) +
        2 EXP 256 * (rnd + 2 EXP 256 * mu)))
     64)`;;

let mld_sign_y = new_definition
 `mld_sign_y (g1:num->int16->num->int32) rhoprime kappa =
    mld_polyvec (\j. g1 rhoprime (word(kappa + j)))`;;

let mld_sign_w = new_definition
 `mld_sign_w l (A:num->int32) (y:num->int32) =
    mld_polyvec_map mld_poly_caddq
     (mld_polyvec_map mld_poly_invntt_tomont
       (mld_polyvec_matrix_pointwise_montgomery l A
         (mld_polyvec_map mld_poly_ntt y)))`;;

let mld_sign_w1 = new_definition
 `mld_sign_w1 (w1enc:(num->int32)->num->byte) w1p (w:num->int32) =
    mld_polyvec_pack w1p w1enc w`;;

let mld_sign_ctilde = new_definition
 `mld_sign_ctilde k w1p mu (w1:num->byte) =
    mld_shake256_byte (64 + k * w1p)
     (mu + 2 EXP 512 * num_of_bytelist(list_of_seq w1 (k * w1p)))`;;

let mld_sign_cphat = new_definition
 `mld_sign_cphat tau ctlen (ct:num->byte) =
    mld_poly_ntt
     (mld_poly_challenge tau ctlen (num_of_bytelist(list_of_seq ct ctlen)))`;;

let mld_sign_z = new_definition
 `mld_sign_z (s1hat:num->int32) (cphat:num->int32) (y:num->int32) i =
    mld_poly_reduce
     (mld_poly_add
       (mld_poly_invntt_tomont
         (mld_poly_pointwise_montgomery (mld_poly_of s1hat i) cphat))
       (mld_poly_of y i))`;;

let mld_sign_r0 = new_definition
 `mld_sign_r0 (dlo:(num->int32)->num->int32) (w:num->int32)
              (s2hat:num->int32) (cphat:num->int32) j =
    mld_poly_reduce
     (mld_poly_sub (dlo (mld_poly_of w j))
       (mld_poly_invntt_tomont
         (mld_poly_pointwise_montgomery (mld_poly_of s2hat j) cphat)))`;;

let mld_sign_ct0 = new_definition
 `mld_sign_ct0 (t0hat:num->int32) (cphat:num->int32) j =
    mld_poly_reduce
     (mld_poly_invntt_tomont
       (mld_poly_pointwise_montgomery (mld_poly_of t0hat j) cphat))`;;

let mld_sign_hint_x = new_definition
 `mld_sign_hint_x k dlo (w:num->int32) s2hat t0hat cphat =
    \i. if i < 256 * k
        then mld_poly_add (mld_sign_r0 dlo w s2hat cphat (i DIV 256))
                          (mld_sign_ct0 t0hat cphat (i DIV 256)) (i MOD 256)
        else word 0`;;

let mld_sign_hint_w1 = new_definition
 `mld_sign_hint_w1 k w1p (w1:num->byte) =
    \j. if j < k * w1p then w1 j else word 0`;;

(* ------------------------------------------------------------------------- *)
(* The result of the checks of an attempt (mld_sign_rej) is the first that   *)
(* fails: i < l for that of z_i, l + 2 * j and l + 2 * j + 1 for the two of  *)
(* row j, and l + 2 * k for the number of hints, or l + 2 * k + 1 if none    *)
(* fails, in which case the signature is mld_sign_attempt_sig: c~, then z    *)
(* packed by zpack in zp bytes per polynomial, then the hints. What the C    *)
(* code declassifies in the attempt (mld_sign_attempt_declass) is c~ (as a   *)
(* number), the results of the checks up to the first that fails (given by   *)
(* mld_sign_rej) and, if all the norm checks pass, the arguments of the      *)
(* hints, w0 - c s2 + c t0 and w1 packed (zero otherwise).                   *)
(* ------------------------------------------------------------------------- *)

let mld_sign_rej = new_definition
 `mld_sign_rej k l bndz bndw bndh omega
               (mkhint:(num->int32)->(num->byte)->num->bool)
               (z:num->num->int32) (r0:num->num->int32) (ct0:num->num->int32)
               (x:num->int32) (w1:num->byte) =
    let zbad = \i. ~(mld_poly_chknorm (z i) (word bndz) = word 0) in
    let wbad = \j. ~(mld_poly_chknorm
                      (if EVEN j then r0 (j DIV 2) else ct0 (j DIV 2))
                      (word(if EVEN j then bndw else bndh)) = word 0) in
    if ?i. i < l /\ zbad i then minimal i. i < l /\ zbad i
    else if ?j. j < 2 * k /\ wbad j then l + (minimal j. j < 2 * k /\ wbad j)
    else if omega < mld_hint_count (mkhint x w1) (256 * k) then l + 2 * k
    else l + 2 * k + 1`;;

let mld_sign_attempt_rej = new_definition
 `mld_sign_attempt_rej k l ctlen tau (g1:num->int16->num->int32)
     bndz bndw bndh (w1enc:(num->int32)->num->byte) w1p
     (dlo:(num->int32)->num->int32)
     (mkhint:(num->int32)->(num->byte)->num->bool) omega
     (A:num->int32) s1hat s2hat t0hat mu rhoprime kappa =
    let y = mld_sign_y g1 rhoprime kappa in
    let w = mld_sign_w l A y in
    let w1 = mld_sign_w1 w1enc w1p w in
    let cphat = mld_sign_cphat tau ctlen (mld_sign_ctilde k w1p mu w1) in
    mld_sign_rej k l bndz bndw bndh omega mkhint
     (mld_sign_z s1hat cphat y) (mld_sign_r0 dlo w s2hat cphat)
     (mld_sign_ct0 t0hat cphat) (mld_sign_hint_x k dlo w s2hat t0hat cphat)
     (mld_sign_hint_w1 k w1p w1)`;;

let mld_sign_attempt_sig = new_definition
 `mld_sign_attempt_sig k l ctlen tau (g1:num->int16->num->int32)
     (zpack:(num->int32)->num->byte) zp (w1enc:(num->int32)->num->byte) w1p
     (dlo:(num->int32)->num->int32)
     (mkhint:(num->int32)->(num->byte)->num->bool) omega
     (A:num->int32) s1hat s2hat t0hat mu rhoprime kappa =
    let y = mld_sign_y g1 rhoprime kappa in
    let w = mld_sign_w l A y in
    let w1 = mld_sign_w1 w1enc w1p w in
    let ct = mld_sign_ctilde k w1p mu w1 in
    let cphat = mld_sign_cphat tau ctlen ct in
    \t. if t < ctlen then ct t
        else if t < ctlen + l * zp
        then mld_polyvec_pack zp zpack (mld_polyvec (mld_sign_z s1hat cphat y))
              (t - ctlen)
        else mld_pack_hints omega k
              (mkhint (mld_sign_hint_x k dlo w s2hat t0hat cphat)
                      (mld_sign_hint_w1 k w1p w1))
              (t - (ctlen + l * zp))`;;

let mld_sign_attempt_declass = new_definition
 `mld_sign_attempt_declass k l ctlen tau (g1:num->int16->num->int32)
     bndz bndw bndh (w1enc:(num->int32)->num->byte) w1p
     (dlo:(num->int32)->num->int32)
     (mkhint:(num->int32)->(num->byte)->num->bool) omega
     (A:num->int32) s1hat s2hat t0hat mu rhoprime kappa =
    let y = mld_sign_y g1 rhoprime kappa in
    let w = mld_sign_w l A y in
    let w1 = mld_sign_w1 w1enc w1p w in
    let ct = mld_sign_ctilde k w1p mu w1 in
    let cphat = mld_sign_cphat tau ctlen ct in
    let x = mld_sign_hint_x k dlo w s2hat t0hat cphat in
    let hw1 = mld_sign_hint_w1 k w1p w1 in
    let r = mld_sign_rej k l bndz bndw bndh omega mkhint
             (mld_sign_z s1hat cphat y) (mld_sign_r0 dlo w s2hat cphat)
             (mld_sign_ct0 t0hat cphat) x hw1 in
    num_of_bytelist(list_of_seq ct ctlen),r,
    (if l + 2 * k <= r then x else \i. word 0),
    (if l + 2 * k <= r then hw1 else \j. word 0)`;;

(* ------------------------------------------------------------------------- *)
(* The whole of mld_sign_signature_internal, for the secret key sk (s1 and   *)
(* s2 unpacked by unpack from p bytes per polynomial), mu and the 32 bytes   *)
(* rnd as a number: the matrix A is expanded from rho, s1, s2 and t0 are put *)
(* in the NTT domain, and attempt n, for n < maxatt, has kappa = l * n       *)
(* (mld_sign_rejn gives the result of its checks). mld_sign_ok holds if one  *)
(* succeeds, and the signature mld_sign_sig is then that of the first that   *)
(* does; otherwise the code returns MLD_ERR_SIGN_ATTEMPTS_EXHAUSTED (-4) and *)
(* zeroes the signature. mld_sign_nattempts is the number of attempts made,  *)
(* mld_sign_declass gives what is declassified in each of them (and zeros    *)
(* for n beyond), and mld_sign_terminates says that the sampling of the      *)
(* challenge terminates in each.                                             *)
(* ------------------------------------------------------------------------- *)

let mld_sk_t0 = new_definition
 `mld_sk_t0 k l p (sk:num->byte) =
    mld_polyvec_unpack 416 mld_polyt0_unpack (\j. sk(128 + (l + k) * p + j))`;;

let mld_sign_rejn = new_definition
 `mld_sign_rejn k l (unpack:(num->byte)->num->int32) p ctlen tau
     (g1:num->int16->num->int32) bndz bndw bndh
     (w1enc:(num->int32)->num->byte) w1p (dlo:(num->int32)->num->int32)
     (mkhint:(num->int32)->(num->byte)->num->bool) omega (sk:num->byte)
     mu rnd n =
    mld_sign_attempt_rej k l ctlen tau g1 bndz bndw bndh w1enc w1p dlo
     mkhint omega (mld_polyvec_matrix_expand l (mld_sk_rho sk))
     (mld_polyvec_map mld_poly_ntt (mld_sk_s1 unpack p sk))
     (mld_polyvec_map mld_poly_ntt (mld_sk_s2 l unpack p sk))
     (mld_polyvec_map mld_poly_ntt (mld_sk_t0 k l p sk))
     mu (mld_sign_rhoprime (\j. sk(32 + j)) rnd mu) (l * n)`;;

let mld_sign_ok = new_definition
 `mld_sign_ok k l (unpack:(num->byte)->num->int32) p ctlen tau
     (g1:num->int16->num->int32) bndz bndw bndh
     (w1enc:(num->int32)->num->byte) w1p (dlo:(num->int32)->num->int32)
     (mkhint:(num->int32)->(num->byte)->num->bool) omega maxatt
     (sk:num->byte) mu rnd <=>
    ?n. n < maxatt /\
        mld_sign_rejn k l unpack p ctlen tau g1 bndz bndw bndh w1enc w1p dlo
         mkhint omega sk mu rnd n = l + 2 * k + 1`;;

let mld_sign_nattempts = new_definition
 `mld_sign_nattempts k l (unpack:(num->byte)->num->int32) p ctlen tau
     (g1:num->int16->num->int32) bndz bndw bndh
     (w1enc:(num->int32)->num->byte) w1p (dlo:(num->int32)->num->int32)
     (mkhint:(num->int32)->(num->byte)->num->bool) omega maxatt
     (sk:num->byte) mu rnd =
    if mld_sign_ok k l unpack p ctlen tau g1 bndz bndw bndh w1enc w1p dlo
        mkhint omega maxatt sk mu rnd
    then (minimal n. n < maxatt /\
                     mld_sign_rejn k l unpack p ctlen tau g1 bndz bndw bndh
                      w1enc w1p dlo mkhint omega sk mu rnd n =
                     l + 2 * k + 1) + 1
    else maxatt`;;

let mld_sign_sig = new_definition
 `mld_sign_sig k l (unpack:(num->byte)->num->int32) p ctlen tau
     (g1:num->int16->num->int32) (zpack:(num->int32)->num->byte) zp
     bndz bndw bndh (w1enc:(num->int32)->num->byte) w1p
     (dlo:(num->int32)->num->int32)
     (mkhint:(num->int32)->(num->byte)->num->bool) omega maxatt
     (sk:num->byte) mu rnd =
    if mld_sign_ok k l unpack p ctlen tau g1 bndz bndw bndh w1enc w1p dlo
        mkhint omega maxatt sk mu rnd
    then mld_sign_attempt_sig k l ctlen tau g1 zpack zp w1enc w1p dlo
          mkhint omega (mld_polyvec_matrix_expand l (mld_sk_rho sk))
          (mld_polyvec_map mld_poly_ntt (mld_sk_s1 unpack p sk))
          (mld_polyvec_map mld_poly_ntt (mld_sk_s2 l unpack p sk))
          (mld_polyvec_map mld_poly_ntt (mld_sk_t0 k l p sk))
          mu (mld_sign_rhoprime (\j. sk(32 + j)) rnd mu)
          (l * (mld_sign_nattempts k l unpack p ctlen tau g1 bndz bndw bndh
                 w1enc w1p dlo mkhint omega maxatt sk mu rnd - 1))
    else \t. word 0`;;

let mld_sign_declass = new_definition
 `mld_sign_declass k l (unpack:(num->byte)->num->int32) p ctlen tau
     (g1:num->int16->num->int32) bndz bndw bndh
     (w1enc:(num->int32)->num->byte) w1p (dlo:(num->int32)->num->int32)
     (mkhint:(num->int32)->(num->byte)->num->bool) omega maxatt
     (sk:num->byte) mu rnd n =
    if n < mld_sign_nattempts k l unpack p ctlen tau g1 bndz bndw bndh
            w1enc w1p dlo mkhint omega maxatt sk mu rnd
    then mld_sign_attempt_declass k l ctlen tau g1 bndz bndw bndh w1enc w1p
          dlo mkhint omega (mld_polyvec_matrix_expand l (mld_sk_rho sk))
          (mld_polyvec_map mld_poly_ntt (mld_sk_s1 unpack p sk))
          (mld_polyvec_map mld_poly_ntt (mld_sk_s2 l unpack p sk))
          (mld_polyvec_map mld_poly_ntt (mld_sk_t0 k l p sk))
          mu (mld_sign_rhoprime (\j. sk(32 + j)) rnd mu) (l * n)
    else 0,0,(\i. word 0),(\j. word 0)`;;

let mld_sign_terminates = new_definition
 `mld_sign_terminates k l (unpack:(num->byte)->num->int32) p ctlen tau
     (g1:num->int16->num->int32) bndz bndw bndh
     (w1enc:(num->int32)->num->byte) w1p (dlo:(num->int32)->num->int32)
     (mkhint:(num->int32)->(num->byte)->num->bool) omega maxatt
     (sk:num->byte) mu rnd <=>
    !n. n < mld_sign_nattempts k l unpack p ctlen tau g1 bndz bndw bndh
             w1enc w1p dlo mkhint omega maxatt sk mu rnd
        ==> mld_poly_challenge_terminates tau ctlen
             (FST(mld_sign_declass k l unpack p ctlen tau g1 bndz bndw bndh
                   w1enc w1p dlo mkhint omega maxatt sk mu rnd n))`;;

(* ------------------------------------------------------------------------- *)
(* The functions for the three parameter sets (params.h), with the bound     *)
(* maxatt = MLD_MAX_KAPPA / l = (65535 - l) DIV l on the number of attempts. *)
(* ML-DSA-44: k = 4, l = 4, eta = 2 (s1 and s2 unpacked by                   *)
(* mld_polyeta_unpack_2 from 96 bytes per polynomial), c~ of 32 bytes,       *)
(* tau = 39, gamma1 = 2^17 (y sampled by mld_poly_uniform_gamma1_17, z       *)
(* packed by mld_polyz_pack_17 in 576 bytes), beta = 78, gamma2 =            *)
(* (q - 1) / 88 = 95232 (w1 packed by mld_polyw1_pack_88 in 192 bytes, and   *)
(* the _88 decomposition and hints), omega = 80 and maxatt = 16382.          *)
(* ML-DSA-65: k = 6, l = 5, eta = 4 (mld_polyeta_unpack_4, 128 bytes), c~ of *)
(* 48 bytes, tau = 49, gamma1 = 2^19 (the _19 functions, 640 bytes),         *)
(* beta = 196, gamma2 = (q - 1) / 32 = 261888 (the _32 functions, 128        *)
(* bytes), omega = 55 and maxatt = 13106. ML-DSA-87: k = 8, l = 7, eta = 2,  *)
(* c~ of 64 bytes, tau = 60, gamma1 = 2^19, beta = 120, gamma2 =             *)
(* (q - 1) / 32, omega = 75 and maxatt = 9361. The bounds are                *)
(* bndz = gamma1 - beta, bndw = gamma2 - beta and bndh = gamma2.             *)
(* ------------------------------------------------------------------------- *)

let mld_sign_ok_44 = new_definition
 `mld_sign_ok_44 =
    mld_sign_ok 4 4 mld_polyeta_unpack_2 96 32 39
     mld_poly_uniform_gamma1_17 130994 95154 95232
     (mld_polyw1_pack_88 o mld_poly_decompose_hi_88) 192
     mld_poly_decompose_lo_88 mld_polyvec_make_hint_88 80 16382`;;

let mld_sign_sig_44 = new_definition
 `mld_sign_sig_44 =
    mld_sign_sig 4 4 mld_polyeta_unpack_2 96 32 39
     mld_poly_uniform_gamma1_17 mld_polyz_pack_17 576 130994 95154 95232
     (mld_polyw1_pack_88 o mld_poly_decompose_hi_88) 192
     mld_poly_decompose_lo_88 mld_polyvec_make_hint_88 80 16382`;;

let mld_sign_declass_44 = new_definition
 `mld_sign_declass_44 =
    mld_sign_declass 4 4 mld_polyeta_unpack_2 96 32 39
     mld_poly_uniform_gamma1_17 130994 95154 95232
     (mld_polyw1_pack_88 o mld_poly_decompose_hi_88) 192
     mld_poly_decompose_lo_88 mld_polyvec_make_hint_88 80 16382`;;

let mld_sign_terminates_44 = new_definition
 `mld_sign_terminates_44 =
    mld_sign_terminates 4 4 mld_polyeta_unpack_2 96 32 39
     mld_poly_uniform_gamma1_17 130994 95154 95232
     (mld_polyw1_pack_88 o mld_poly_decompose_hi_88) 192
     mld_poly_decompose_lo_88 mld_polyvec_make_hint_88 80 16382`;;

let mld_sign_ok_65 = new_definition
 `mld_sign_ok_65 =
    mld_sign_ok 6 5 mld_polyeta_unpack_4 128 48 49
     mld_poly_uniform_gamma1_19 524092 261692 261888
     (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
     mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 55 13106`;;

let mld_sign_sig_65 = new_definition
 `mld_sign_sig_65 =
    mld_sign_sig 6 5 mld_polyeta_unpack_4 128 48 49
     mld_poly_uniform_gamma1_19 mld_polyz_pack_19 640 524092 261692 261888
     (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
     mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 55 13106`;;

let mld_sign_declass_65 = new_definition
 `mld_sign_declass_65 =
    mld_sign_declass 6 5 mld_polyeta_unpack_4 128 48 49
     mld_poly_uniform_gamma1_19 524092 261692 261888
     (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
     mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 55 13106`;;

let mld_sign_terminates_65 = new_definition
 `mld_sign_terminates_65 =
    mld_sign_terminates 6 5 mld_polyeta_unpack_4 128 48 49
     mld_poly_uniform_gamma1_19 524092 261692 261888
     (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
     mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 55 13106`;;

let mld_sign_ok_87 = new_definition
 `mld_sign_ok_87 =
    mld_sign_ok 8 7 mld_polyeta_unpack_2 96 64 60
     mld_poly_uniform_gamma1_19 524168 261768 261888
     (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
     mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 75 9361`;;

let mld_sign_sig_87 = new_definition
 `mld_sign_sig_87 =
    mld_sign_sig 8 7 mld_polyeta_unpack_2 96 64 60
     mld_poly_uniform_gamma1_19 mld_polyz_pack_19 640 524168 261768 261888
     (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
     mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 75 9361`;;

let mld_sign_declass_87 = new_definition
 `mld_sign_declass_87 =
    mld_sign_declass 8 7 mld_polyeta_unpack_2 96 64 60
     mld_poly_uniform_gamma1_19 524168 261768 261888
     (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
     mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 75 9361`;;

let mld_sign_terminates_87 = new_definition
 `mld_sign_terminates_87 =
    mld_sign_terminates 8 7 mld_polyeta_unpack_2 96 64 60
     mld_poly_uniform_gamma1_19 524168 261768 261888
     (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) 128
     mld_poly_decompose_lo_32 mld_polyvec_make_hint_32 75 9361`;;

(* ------------------------------------------------------------------------- *)
(* Key generation (mld_sign_keypair_internal in sign.c) from the 32 bytes of *)
(* the seed as a number: the first 128 bytes of SHAKE256 of seed || k || l   *)
(* (mld_keypair_seedbuf) are rho, rho' and the key; polynomial i of the      *)
(* vector s of s1 (l polynomials) followed by s2 (k) is sampled from rho'    *)
(* with nonce i (mld_poly_uniform_eta) and packed by pack in p bytes into    *)
(* the secret key, t is computed from rho, s1 in the NTT domain and s2       *)
(* unpacked by unpack from the secret key (mld_compute_t), the public key is *)
(* rho || t1 packed (mld_keypair_pk) and the secret key rho || key || tr ||  *)
(* s1 || s2 || t0 packed (mld_keypair_sk), with tr = H(pk, 64). The code     *)
(* returns 0. It declassifies rho and, for the sampling of each polynomial,  *)
(* whether each nibble that it reads is accepted (mld_keypair_declass, as a  *)
(* function of the nonce), for the nonces n with used n: those of s1 and s2  *)
(* and the irrelevant nonce 255 of the polynomial that one call of           *)
(* mld_poly_uniform_eta_4x samples in vain for ML-DSA-65 and -87.            *)
(* mld_keypair_terminates says that these samplings terminate.               *)
(* ------------------------------------------------------------------------- *)

let mld_keypair_seedbuf = new_definition
 `mld_keypair_seedbuf k l seed =
    mld_shake256_byte 34 (seed + 2 EXP 256 * (k + 256 * l))`;;

let mld_keypair_rho = new_definition
 `mld_keypair_rho k l seed =
    num_of_bytelist(list_of_seq (mld_keypair_seedbuf k l seed) 32)`;;

let mld_keypair_rhoprime = new_definition
 `mld_keypair_rhoprime k l seed =
    num_of_bytelist
     (list_of_seq (\j. mld_keypair_seedbuf k l seed (32 + j)) 64)`;;

let mld_keypair_s = new_definition
 `mld_keypair_s eta k l seed =
    mld_polyvec
     (\i. mld_poly_uniform_eta eta (mld_keypair_rhoprime k l seed) (word i))`;;

let mld_keypair_t = new_definition
 `mld_keypair_t eta k l (pack:(num->int32)->num->byte)
                (unpack:(num->byte)->num->int32) p seed =
    mld_compute_t l unpack p (mld_keypair_rho k l seed)
     (mld_polyvec_map mld_poly_ntt (mld_keypair_s eta k l seed))
     (\j. mld_polyvec_pack p pack (mld_keypair_s eta k l seed) (l * p + j))`;;

let mld_keypair_pk = new_definition
 `mld_keypair_pk eta k l (pack:(num->int32)->num->byte)
                 (unpack:(num->byte)->num->int32) p seed =
    \j. if j < 32 then mld_keypair_seedbuf k l seed j
        else mld_polyvec_pack 320 mld_polyt1_pack
              (mld_polyvec_map mld_poly_power2round_hi
                (mld_keypair_t eta k l pack unpack p seed)) (j - 32)`;;

let mld_keypair_sk = new_definition
 `mld_keypair_sk eta k l (pack:(num->int32)->num->byte)
                 (unpack:(num->byte)->num->int32) p seed =
    let tr = mld_shake256_byte (32 + 320 * k)
              (num_of_bytelist
                (list_of_seq (mld_keypair_pk eta k l pack unpack p seed)
                             (32 + 320 * k))) in
    \j. if j < 32 then mld_keypair_seedbuf k l seed j
        else if j < 64 then mld_keypair_seedbuf k l seed (j + 64)
        else if j < 128 then tr (j - 64)
        else if j < 128 + (l + k) * p
        then mld_polyvec_pack p pack (mld_keypair_s eta k l seed) (j - 128)
        else mld_polyvec_pack 416 mld_polyt0_pack
              (mld_polyvec_map mld_poly_power2round_lo
                (mld_keypair_t eta k l pack unpack p seed))
              (j - (128 + (l + k) * p))`;;

let mld_keypair_declass = new_definition
 `mld_keypair_declass eta k l (used:num->bool) seed n =
    if used n
    then mld_poly_uniform_eta_declass eta
          (mld_shake256_stream 66
            (mld_keypair_rhoprime k l seed + 2 EXP 512 * n))
    else []`;;

let mld_keypair_terminates = new_definition
 `mld_keypair_terminates eta k l (used:num->bool) seed <=>
    !n. used n
        ==> mld_rej_eta_terminates eta
             (mld_shake256_stream 66
               (mld_keypair_rhoprime k l seed + 2 EXP 512 * n))`;;

(* ------------------------------------------------------------------------- *)
(* The functions for the three parameter sets: eta = 2, k = 4, l = 4 and 96  *)
(* bytes per polynomial of s for ML-DSA-44, with the nonces 0 to 7; eta = 4, *)
(* k = 6, l = 5 and 128 bytes for ML-DSA-65, with 0 to 10 and 255; and       *)
(* eta = 2, k = 8, l = 7 and 96 bytes for ML-DSA-87, with 0 to 14 and 255.   *)
(* ------------------------------------------------------------------------- *)

let mld_keypair_pk_44 = new_definition
 `mld_keypair_pk_44 =
    mld_keypair_pk 2 4 4 mld_polyeta_pack_2 mld_polyeta_unpack_2 96`;;

let mld_keypair_sk_44 = new_definition
 `mld_keypair_sk_44 =
    mld_keypair_sk 2 4 4 mld_polyeta_pack_2 mld_polyeta_unpack_2 96`;;

let mld_keypair_declass_44 = new_definition
 `mld_keypair_declass_44 = mld_keypair_declass 2 4 4 (\n. n < 8)`;;

let mld_keypair_terminates_44 = new_definition
 `mld_keypair_terminates_44 = mld_keypair_terminates 2 4 4 (\n. n < 8)`;;

let mld_keypair_pk_65 = new_definition
 `mld_keypair_pk_65 =
    mld_keypair_pk 4 6 5 mld_polyeta_pack_4 mld_polyeta_unpack_4 128`;;

let mld_keypair_sk_65 = new_definition
 `mld_keypair_sk_65 =
    mld_keypair_sk 4 6 5 mld_polyeta_pack_4 mld_polyeta_unpack_4 128`;;

let mld_keypair_declass_65 = new_definition
 `mld_keypair_declass_65 = mld_keypair_declass 4 6 5 (\n. n < 11 \/ n = 255)`;;

let mld_keypair_terminates_65 = new_definition
 `mld_keypair_terminates_65 =
    mld_keypair_terminates 4 6 5 (\n. n < 11 \/ n = 255)`;;

let mld_keypair_pk_87 = new_definition
 `mld_keypair_pk_87 =
    mld_keypair_pk 2 8 7 mld_polyeta_pack_2 mld_polyeta_unpack_2 96`;;

let mld_keypair_sk_87 = new_definition
 `mld_keypair_sk_87 =
    mld_keypair_sk 2 8 7 mld_polyeta_pack_2 mld_polyeta_unpack_2 96`;;

let mld_keypair_declass_87 = new_definition
 `mld_keypair_declass_87 = mld_keypair_declass 2 8 7 (\n. n < 15 \/ n = 255)`;;

let mld_keypair_terminates_87 = new_definition
 `mld_keypair_terminates_87 =
    mld_keypair_terminates 2 8 7 (\n. n < 15 \/ n = 255)`;;
