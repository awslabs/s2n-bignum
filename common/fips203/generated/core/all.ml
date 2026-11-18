(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Load every equivalence proof in dependency order and check that each     *)
(* interface lemma is proved exactly as stated. Load from the repository    *)
(* root: loadt "common/fips203/generated/core/all.ml";;                *)
(* stubs.ml is deliberately not loaded.                                      *)
(* ========================================================================= *)

loadt "common/fips203/generated/core/base.ml";;
loadt "common/fips203/generated/core/interface.ml";;
loadt "common/fips203/generated/core/foundation.ml";;
loadt "common/fips203/generated/core/bytes.ml";;
loadt "common/fips203/generated/core/rq.ml";;
loadt "common/fips203/generated/core/ntt.ml";;
loadt "common/fips203/generated/core/nttinv.ml";;
loadt "common/fips203/generated/core/sample_ntt.ml";;
loadt "common/fips203/generated/core/tq.ml";;
loadt "common/fips203/generated/core/kpke.ml";;
loadt "common/fips203/generated/core/mlkem.ml";;
loadt "common/fips203/generated/core/final.ml";;
loadt "common/fips203/generated/core/check.ml";;
