(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* Loads the two specifications and the whole equivalence proof, from the    *)
(* repository root, in a fresh HOL Light session.                            *)

loadt "common/fips204/generated/core/base.ml";;
let CONSTANTS_AFTER_SPECS = map fst (constants());;
loadt "common/fips204/generated/core/common.ml";;
loadt "common/fips204/generated/core/equivalence.ml";;
