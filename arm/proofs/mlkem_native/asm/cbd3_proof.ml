(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* Proofs of the contracts of mlkem_cbd3 (see cbd3_spec.ml). The           *)
(* standalone proof of arm/proofs/mlkem_cbd3.ml runs here, in the job of   *)
(* this file, so that it runs once. The contracts are made from its        *)
(* theorems: the correctness theorem with the coefficients of              *)
(* SamplePolyCBD, and the safety with the frame of the correctness         *)
(* theorem.                                                                *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/asm/cbd3_spec.ml";;

loadt "arm/proofs/mlkem_cbd3.ml";;

let MLKEM_CBD3_SUBROUTINE_CORRECT_COEFF = prove
 (`!r a (b:byte list) pc returnaddress.
        ALL (nonoverlapping (r,512)) [(word pc,0xd4); (a,192)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) mlkem_cbd3_mc /\
                  read PC s = word pc /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,192)) s = num_of_bytelist b)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(mlkem_cbd_coeff 3 b i))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MLKEM_CBD_COEFF_3] THEN
  ACCEPT_TAC(SPECL [`r:int64`; `a:int64`; `num_of_bytelist(b:byte list)`;
                    `pc:num`; `returnaddress:int64`]
                   MLKEM_CBD3_SUBROUTINE_CORRECT));;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_cbd3" subroutine_signatures)
    MLKEM_CBD3_NOIBT_SUBROUTINE_CORRECT
    MLKEM_CBD3_EXEC;;

let MLKEM_CBD3_NOIBT_SUBROUTINE_SAFE_FRAMED = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,512)) [word pc,0xd0; a,192]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_cbd3_tmc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2 [a,192; r,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512)])`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLKEM_CBD3_EXEC);;

let MLKEM_CBD3_SUBROUTINE_SAFE_FRAMED = time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           ALL (nonoverlapping (r,512)) [word pc,0xd4; a,192]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc) mlkem_cbd3_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2 [a,192; r,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(r,512)])`,
  MATCH_ACCEPT_TAC(ARM_ADD_IBT_RULE
    mlkem_cbd3_mc mlkem_cbd3_tmc MLKEM_CBD3_NOIBT_SUBROUTINE_SAFE_FRAMED));;
