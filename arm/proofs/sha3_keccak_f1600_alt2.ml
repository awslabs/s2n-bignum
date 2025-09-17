(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compiler-generated "naive" Keccak-f1600 code not using lazy rotations.    *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/keccak_spec.ml";;

(**** print_literal_from_elf "arm/sha3/sha3_keccak_f1600_alt2.o";;
 ****)

let sha3_keccak_f1600_alt2_mc = define_assert_from_elf
  "sha3_keccak_f1600_alt2_mc" "arm/sha3/sha3_keccak_f1600_alt2.o"
[
  0xa9b37bfd;       (* arm_STP X29 X30 SP (Preimmediate_Offset (iword (-- &208))) *)
  0xaa0003e2;       (* arm_MOV X2 X0 *)
  0x910003fd;       (* arm_ADD X29 SP (rvalue (word 0)) *)
  0xf9400000;       (* arm_LDR X0 X0 (Immediate_Offset (word 0)) *)
  0xa9433c46;       (* arm_LDP X6 X15 X2 (Immediate_Offset (iword (&48))) *)
  0xa90153f3;       (* arm_STP X19 X20 SP (Immediate_Offset (iword (&16))) *)
  0xf9003be0;       (* arm_STR X0 SP (Immediate_Offset (word 112)) *)
  0xf9400440;       (* arm_LDR X0 X2 (Immediate_Offset (word 8)) *)
  0xa9025bf5;       (* arm_STP X21 X22 SP (Immediate_Offset (iword (&32))) *)
  0xf9400c5e;       (* arm_LDR X30 X2 (Immediate_Offset (word 24)) *)
  0xf9004fe0;       (* arm_STR X0 SP (Immediate_Offset (word 152)) *)
  0xf9400840;       (* arm_LDR X0 X2 (Immediate_Offset (word 16)) *)
  0xa90363f7;       (* arm_STP X23 X24 SP (Immediate_Offset (iword (&48))) *)
  0xa9046bf9;       (* arm_STP X25 X26 SP (Immediate_Offset (iword (&64))) *)
  0xf90053e0;       (* arm_STR X0 SP (Immediate_Offset (word 160)) *)
  0xf9401040;       (* arm_LDR X0 X2 (Immediate_Offset (word 32)) *)
  0xa90573fb;       (* arm_STP X27 X28 SP (Immediate_Offset (iword (&80))) *)
  0xf9402459;       (* arm_LDR X25 X2 (Immediate_Offset (word 72)) *)
  0xf9003fe0;       (* arm_STR X0 SP (Immediate_Offset (word 120)) *)
  0xf9401440;       (* arm_LDR X0 X2 (Immediate_Offset (word 40)) *)
  0xf9004bff;       (* arm_STR XZR SP (Immediate_Offset (word 144)) *)
  0xf90063e1;       (* arm_STR X1 SP (Immediate_Offset (word 192)) *)
  0xf90057e0;       (* arm_STR X0 SP (Immediate_Offset (word 168)) *)
  0xf9402040;       (* arm_LDR X0 X2 (Immediate_Offset (word 64)) *)
  0xf90043e0;       (* arm_STR X0 SP (Immediate_Offset (word 128)) *)
  0xa9453440;       (* arm_LDP X0 X13 X2 (Immediate_Offset (iword (&80))) *)
  0xa9464045;       (* arm_LDP X5 X16 X2 (Immediate_Offset (iword (&96))) *)
  0xa9476851;       (* arm_LDP X17 X26 X2 (Immediate_Offset (iword (&112))) *)
  0xaa1003f7;       (* arm_MOV X23 X16 *)
  0xaa0f03f0;       (* arm_MOV X16 X15 *)
  0xa9485844;       (* arm_LDP X4 X22 X2 (Immediate_Offset (iword (&128))) *)
  0xaa0003ef;       (* arm_MOV X15 X0 *)
  0xaa1103f3;       (* arm_MOV X19 X17 *)
  0xa949605c;       (* arm_LDP X28 X24 X2 (Immediate_Offset (iword (&144))) *)
  0xa94a2443;       (* arm_LDP X3 X9 X2 (Immediate_Offset (iword (&160))) *)
  0xa94b6c4a;       (* arm_LDP X10 X27 X2 (Immediate_Offset (iword (&176))) *)
  0xf90047fe;       (* arm_STR X30 SP (Immediate_Offset (word 136)) *)
  0xaa1603fe;       (* arm_MOV X30 X22 *)
  0xf9406048;       (* arm_LDR X8 X2 (Immediate_Offset (word 192)) *)
  0xf90067e2;       (* arm_STR X2 SP (Immediate_Offset (word 200)) *)
  0xaa0303e2;       (* arm_MOV X2 X3 *)
  0xaa0403e3;       (* arm_MOV X3 X4 *)
  0xaa0a03e4;       (* arm_MOV X4 X10 *)
  0xaa0803e7;       (* arm_MOV X7 X8 *)
  0xaa0603e8;       (* arm_MOV X8 X6 *)
  0xaa1c03e6;       (* arm_MOV X6 X28 *)
  0xaa1903fc;       (* arm_MOV X28 X25 *)
  0xaa0d03f9;       (* arm_MOV X25 X13 *)
  0xa94957f1;       (* arm_LDP X17 X21 SP (Immediate_Offset (iword (&144))) *)
  0xca1a01eb;       (* arm_EOR X11 X15 X26 *)
  0xca1e00ac;       (* arm_EOR X12 X5 X30 *)
  0xa94a5bed;       (* arm_LDP X13 X22 SP (Immediate_Offset (iword (&160))) *)
  0xf94063e1;       (* arm_LDR X1 SP (Immediate_Offset (word 192)) *)
  0xca1001aa;       (* arm_EOR X10 X13 X16 *)
  0xf9403be0;       (* arm_LDR X0 SP (Immediate_Offset (word 112)) *)
  0xca0c014a;       (* arm_EOR X10 X10 X12 *)
  0xca0602ec;       (* arm_EOR X12 X23 X6 *)
  0xca04014a;       (* arm_EOR X10 X10 X4 *)
  0xf94043f4;       (* arm_LDR X20 SP (Immediate_Offset (word 128)) *)
  0xf8717821;       (* arm_LDR X1 X1 (Shiftreg_Offset X17 3) *)
  0xca16000e;       (* arm_EOR X14 X0 X22 *)
  0xca030320;       (* arm_EOR X0 X25 X3 *)
  0xca0b01ce;       (* arm_EOR X14 X14 X11 *)
  0xf94047eb;       (* arm_LDR X11 SP (Immediate_Offset (word 136)) *)
  0xca0201ce;       (* arm_EOR X14 X14 X2 *)
  0xf90053e1;       (* arm_STR X1 SP (Immediate_Offset (word 160)) *)
  0xca0802a1;       (* arm_EOR X1 X21 X8 *)
  0xca000021;       (* arm_EOR X1 X1 X0 *)
  0xf9403fe0;       (* arm_LDR X0 SP (Immediate_Offset (word 120)) *)
  0xca14016b;       (* arm_EOR X11 X11 X20 *)
  0xca090021;       (* arm_EOR X1 X1 X9 *)
  0xcacafdd4;       (* arm_EOR X20 X14 (Shiftedreg X10 ROR 63) *)
  0xca0c016b;       (* arm_EOR X11 X11 X12 *)
  0xca18026c;       (* arm_EOR X12 X19 X24 *)
  0xca1b016b;       (* arm_EOR X11 X11 X27 *)
  0xca190299;       (* arm_EOR X25 X20 X25 *)
  0xcacefd6e;       (* arm_EOR X14 X11 (Shiftedreg X14 ROR 63) *)
  0xca030283;       (* arm_EOR X3 X20 X3 *)
  0xca1c0000;       (* arm_EOR X0 X0 X28 *)
  0xcacbfc2b;       (* arm_EOR X11 X1 (Shiftedreg X11 ROR 63) *)
  0x93c34c63;       (* arm_ROR X3 X3 19 *)
  0xca0c0000;       (* arm_EOR X0 X0 X12 *)
  0x9100062c;       (* arm_ADD X12 X17 (rvalue (word 1)) *)
  0xca070000;       (* arm_EOR X0 X0 X7 *)
  0xca150291;       (* arm_EOR X17 X20 X21 *)
  0xcac1fc01;       (* arm_EOR X1 X0 (Shiftedreg X1 ROR 63) *)
  0xca080295;       (* arm_EOR X21 X20 X8 *)
  0xca090294;       (* arm_EOR X20 X20 X9 *)
  0xcac0fd40;       (* arm_EOR X0 X10 (Shiftedreg X0 ROR 63) *)
  0xf9403fea;       (* arm_LDR X10 SP (Immediate_Offset (word 120)) *)
  0xca1e017e;       (* arm_EOR X30 X11 X30 *)
  0xca0d0168;       (* arm_EOR X8 X11 X13 *)
  0xca050165;       (* arm_EOR X5 X11 X5 *)
  0xf90037f1;       (* arm_STR X17 SP (Immediate_Offset (word 104)) *)
  0xf94047e9;       (* arm_LDR X9 SP (Immediate_Offset (word 136)) *)
  0xca10016d;       (* arm_EOR X13 X11 X16 *)
  0xca1c01d1;       (* arm_EOR X17 X14 X28 *)
  0xca0f0030;       (* arm_EOR X16 X1 X15 *)
  0xca040164;       (* arm_EOR X4 X11 X4 *)
  0xf9004bec;       (* arm_STR X12 SP (Immediate_Offset (word 144)) *)
  0xca16002b;       (* arm_EOR X11 X1 X22 *)
  0xca0701c7;       (* arm_EOR X7 X14 X7 *)
  0xca1801d6;       (* arm_EOR X22 X14 X24 *)
  0xca0a01cc;       (* arm_EOR X12 X14 X10 *)
  0xca1301ca;       (* arm_EOR X10 X14 X19 *)
  0xca17000e;       (* arm_EOR X14 X0 X23 *)
  0x93d552b7;       (* arm_ROR X23 X21 20 *)
  0x93d9db35;       (* arm_ROR X21 X25 54 *)
  0xa946e7ef;       (* arm_LDP X15 X25 SP (Immediate_Offset (iword (&104))) *)
  0xca1a0038;       (* arm_EOR X24 X1 X26 *)
  0xca090013;       (* arm_EOR X19 X0 X9 *)
  0xca020022;       (* arm_EOR X2 X1 X2 *)
  0xca060006;       (* arm_EOR X6 X0 X6 *)
  0x93c80908;       (* arm_ROR X8 X8 2 *)
  0x93d85f18;       (* arm_ROR X24 X24 23 *)
  0xf90037f5;       (* arm_STR X21 SP (Immediate_Offset (word 104)) *)
  0xf94053fa;       (* arm_LDR X26 SP (Immediate_Offset (word 160)) *)
  0x93c6acc6;       (* arm_ROR X6 X6 43 *)
  0x93c554a5;       (* arm_ROR X5 X5 21 *)
  0xca190021;       (* arm_EOR X1 X1 X25 *)
  0x93c7c8e7;       (* arm_ROR X7 X7 50 *)
  0xa90b63e8;       (* arm_STP X8 X24 SP (Immediate_Offset (iword (&176))) *)
  0x8a2500dc;       (* arm_BIC X28 X6 X5 *)
  0x93dec7d5;       (* arm_ROR X21 X30 49 *)
  0x8a3700be;       (* arm_BIC X30 X5 X23 *)
  0x93c40c84;       (* arm_ROR X4 X4 3 *)
  0xf94043e9;       (* arm_LDR X9 SP (Immediate_Offset (word 128)) *)
  0x93d1b231;       (* arm_ROR X17 X17 44 *)
  0x93d39273;       (* arm_ROR X19 X19 36 *)
  0xca1a0038;       (* arm_EOR X24 X1 X26 *)
  0x8a2600fa;       (* arm_BIC X26 X7 X6 *)
  0xf9404bf9;       (* arm_LDR X25 SP (Immediate_Offset (word 144)) *)
  0xca050345;       (* arm_EOR X5 X26 X5 *)
  0x93d0f610;       (* arm_ROR X16 X16 61 *)
  0x93d6e2d6;       (* arm_ROR X22 X22 56 *)
  0x93ce9dce;       (* arm_ROR X14 X14 39 *)
  0xca1803de;       (* arm_EOR X30 X30 X24 *)
  0x93cde9ad;       (* arm_ROR X13 X13 58 *)
  0xca090009;       (* arm_EOR X9 X0 X9 *)
  0xca1b0000;       (* arm_EOR X0 X0 X27 *)
  0x8a2102fb;       (* arm_BIC X27 X23 X1 *)
  0xca170397;       (* arm_EOR X23 X28 X23 *)
  0xf9003bfe;       (* arm_STR X30 SP (Immediate_Offset (word 112)) *)
  0x8a270021;       (* arm_BIC X1 X1 X7 *)
  0xf100633f;       (* arm_CMP X25 (rvalue (word 24)) *)
  0xca070367;       (* arm_EOR X7 X27 X7 *)
  0x8a310219;       (* arm_BIC X25 X16 X17 *)
  0xa90997f7;       (* arm_STP X23 X5 SP (Immediate_Offset (iword (&152))) *)
  0x8a240277;       (* arm_BIC X23 X19 X4 *)
  0xca130325;       (* arm_EOR X5 X25 X19 *)
  0xca060021;       (* arm_EOR X1 X1 X6 *)
  0xca0302f7;       (* arm_EOR X23 X23 X3 *)
  0x93cb716b;       (* arm_ROR X11 X11 28 *)
  0x8a330238;       (* arm_BIC X24 X17 X19 *)
  0xf9003fe7;       (* arm_STR X7 SP (Immediate_Offset (word 120)) *)
  0x93cc958c;       (* arm_ROR X12 X12 37 *)
  0x8a230087;       (* arm_BIC X7 X4 X3 *)
  0xf90043f7;       (* arm_STR X23 SP (Immediate_Offset (word 128)) *)
  0x8a300068;       (* arm_BIC X8 X3 X16 *)
  0xf94037e3;       (* arm_LDR X3 SP (Immediate_Offset (word 104)) *)
  0x93cffdef;       (* arm_ROR X15 X15 63 *)
  0x8a2e02c6;       (* arm_BIC X6 X22 X14 *)
  0x93c02000;       (* arm_ROR X0 X0 8 *)
  0xf90047e1;       (* arm_STR X1 SP (Immediate_Offset (word 136)) *)
  0x8a2f01b3;       (* arm_BIC X19 X13 X15 *)
  0x8a2d01c1;       (* arm_BIC X1 X14 X13 *)
  0xf90057e5;       (* arm_STR X5 SP (Immediate_Offset (word 168)) *)
  0xca04031c;       (* arm_EOR X28 X24 X4 *)
  0xca0d00d9;       (* arm_EOR X25 X6 X13 *)
  0xf9405fed;       (* arm_LDR X13 SP (Immediate_Offset (word 184)) *)
  0x8a2c0178;       (* arm_BIC X24 X11 X12 *)
  0x8a200186;       (* arm_BIC X6 X12 X0 *)
  0xf9405be4;       (* arm_LDR X4 SP (Immediate_Offset (word 176)) *)
  0x8a35001e;       (* arm_BIC X30 X0 X21 *)
  0xca000318;       (* arm_EOR X24 X24 X0 *)
  0x93c2b842;       (* arm_ROR X2 X2 46 *)
  0x93d4fa94;       (* arm_ROR X20 X20 62 *)
  0xf94037e0;       (* arm_LDR X0 SP (Immediate_Offset (word 104)) *)
  0x93ca654a;       (* arm_ROR X10 X10 25 *)
  0x93c92529;       (* arm_ROR X9 X9 9 *)
  0x8a2b007a;       (* arm_BIC X26 X3 X11 *)
  0x8a2302a3;       (* arm_BIC X3 X21 X3 *)
  0x8a360045;       (* arm_BIC X5 X2 X22 *)
  0xca110108;       (* arm_EOR X8 X8 X17 *)
  0x8a34009b;       (* arm_BIC X27 X4 X20 *)
  0x8a2201f1;       (* arm_BIC X17 X15 X2 *)
  0xca1000f0;       (* arm_EOR X16 X7 X16 *)
  0xca0f002f;       (* arm_EOR X15 X1 X15 *)
  0x8a240127;       (* arm_BIC X7 X9 X4 *)
  0xca020273;       (* arm_EOR X19 X19 X2 *)
  0x8a2a01a1;       (* arm_BIC X1 X13 X10 *)
  0x8a290142;       (* arm_BIC X2 X10 X9 *)
  0xca0b0063;       (* arm_EOR X3 X3 X11 *)
  0xaa0403eb;       (* arm_MOV X11 X4 *)
  0x8a2d0284;       (* arm_BIC X4 X20 X13 *)
  0xca1500c6;       (* arm_EOR X6 X6 X21 *)
  0xca0c035a;       (* arm_EOR X26 X26 X12 *)
  0xca160237;       (* arm_EOR X23 X17 X22 *)
  0xca0e00a5;       (* arm_EOR X5 X5 X14 *)
  0xca0003de;       (* arm_EOR X30 X30 X0 *)
  0xca0b0042;       (* arm_EOR X2 X2 X11 *)
  0xca090029;       (* arm_EOR X9 X1 X9 *)
  0xca1400e7;       (* arm_EOR X7 X7 X20 *)
  0xca0d037b;       (* arm_EOR X27 X27 X13 *)
  0xca0a0084;       (* arm_EOR X4 X4 X10 *)
  0x54ffec61;       (* arm_BNE (word 2096524) *)
  0xf9403be0;       (* arm_LDR X0 SP (Immediate_Offset (word 112)) *)
  0xaa0403ea;       (* arm_MOV X10 X4 *)
  0xaa0303e4;       (* arm_MOV X4 X3 *)
  0xaa0203e3;       (* arm_MOV X3 X2 *)
  0xaa1e03f6;       (* arm_MOV X22 X30 *)
  0xf94067e2;       (* arm_LDR X2 SP (Immediate_Offset (word 200)) *)
  0xaa1903ed;       (* arm_MOV X13 X25 *)
  0xaa1c03f9;       (* arm_MOV X25 X28 *)
  0xf94047fe;       (* arm_LDR X30 SP (Immediate_Offset (word 136)) *)
  0xf9000040;       (* arm_STR X0 X2 (Immediate_Offset (word 0)) *)
  0xf9404fe0;       (* arm_LDR X0 SP (Immediate_Offset (word 152)) *)
  0xf9000c5e;       (* arm_STR X30 X2 (Immediate_Offset (word 24)) *)
  0xa9034048;       (* arm_STP X8 X16 X2 (Immediate_Offset (iword (&48))) *)
  0xf9000440;       (* arm_STR X0 X2 (Immediate_Offset (word 8)) *)
  0xf94053e0;       (* arm_LDR X0 SP (Immediate_Offset (word 160)) *)
  0xa904bc59;       (* arm_STP X25 X15 X2 (Immediate_Offset (iword (&72))) *)
  0xa905944d;       (* arm_STP X13 X5 X2 (Immediate_Offset (iword (&88))) *)
  0xf9000840;       (* arm_STR X0 X2 (Immediate_Offset (word 16)) *)
  0xf9403fe0;       (* arm_LDR X0 SP (Immediate_Offset (word 120)) *)
  0xa906cc57;       (* arm_STP X23 X19 X2 (Immediate_Offset (iword (&104))) *)
  0xa907905a;       (* arm_STP X26 X4 X2 (Immediate_Offset (iword (&120))) *)
  0xf9001040;       (* arm_STR X0 X2 (Immediate_Offset (word 32)) *)
  0xf94057e0;       (* arm_LDR X0 SP (Immediate_Offset (word 168)) *)
  0xa9089856;       (* arm_STP X22 X6 X2 (Immediate_Offset (iword (&136))) *)
  0xa9098c58;       (* arm_STP X24 X3 X2 (Immediate_Offset (iword (&152))) *)
  0xf9001440;       (* arm_STR X0 X2 (Immediate_Offset (word 40)) *)
  0xf94043e0;       (* arm_LDR X0 SP (Immediate_Offset (word 128)) *)
  0xa90aa849;       (* arm_STP X9 X10 X2 (Immediate_Offset (iword (&168))) *)
  0xf9005c5b;       (* arm_STR X27 X2 (Immediate_Offset (word 184)) *)
  0xf9002040;       (* arm_STR X0 X2 (Immediate_Offset (word 64)) *)
  0xf9006047;       (* arm_STR X7 X2 (Immediate_Offset (word 192)) *)
  0xa94153f3;       (* arm_LDP X19 X20 SP (Immediate_Offset (iword (&16))) *)
  0xa9425bf5;       (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&32))) *)
  0xa94363f7;       (* arm_LDP X23 X24 SP (Immediate_Offset (iword (&48))) *)
  0xa9446bf9;       (* arm_LDP X25 X26 SP (Immediate_Offset (iword (&64))) *)
  0xa94573fb;       (* arm_LDP X27 X28 SP (Immediate_Offset (iword (&80))) *)
  0xa8cd7bfd;       (* arm_LDP X29 X30 SP (Postimmediate_Offset (iword (&208))) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let SHA3_KECCAK_F1600_ALT2_EXEC = ARM_MK_EXEC_RULE sha3_keccak_f1600_alt2_mc;;

(* ------------------------------------------------------------------------- *)
(* Additional tactic used in proof.                                          *)
(* ------------------------------------------------------------------------- *)

(*** Introduce ghost variables for the state reads in a list ***)

let GHOST_STATELIST_TAC =
  W(fun (asl,w) ->
        let regreads = dest_list(find_term is_list w) in
        let ghostvars = make_args "Ai_" [] (map type_of regreads) in
        EVERY(map2 GHOST_INTRO_TAC ghostvars (map rator regreads)));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, for whole subroutine without separate core.            *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK_F1600_ALT2_SUBROUTINE_CORRECT = prove
 (`!a rc A pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 208),208))
            [(word pc,0x3d0); (a,200); (rc,192)] /\
        nonoverlapping (a,200) (word pc,0x3d0)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) sha3_keccak_f1600_alt2_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; rc] s /\
                  wordlist_from_memory(a,25) s = A /\
                  wordlist_from_memory(rc,24) s = round_constants)
             (\s. read PC s = returnaddress /\
                  wordlist_from_memory(a,25) s = keccak 24 A)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,200);
                memory :> bytes (word_sub stackpointer (word 208),208)])`,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `rc:int64`; `A:int64 list`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 208 THEN X_GEN_TAC `stackpointer:int64` THEN
  STRIP_TAC THEN

  REWRITE_TAC[fst SHA3_KECCAK_F1600_ALT2_EXEC] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Register saves - we include this since they are mixed up in the
   *** main code by the compiler; this does mean we then need to state
   *** this in our loop invariant, and it means we don't follow the
   *** usual methodology of separating the core from the save/restore.
   ***)

  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  ENSURES_PRESERVED_TAC "x24_init" `X24` THEN
  ENSURES_PRESERVED_TAC "x25_init" `X25` THEN
  ENSURES_PRESERVED_TAC "x26_init" `X26` THEN
  ENSURES_PRESERVED_TAC "x27_init" `X27` THEN
  ENSURES_PRESERVED_TAC "x28_init" `X28` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29` THEN

  (*** Set up the loop invariant ***)

  ENSURES_WHILE_PUP_TAC `24` `pc + 0xc0` `pc + 0x334`
   `\i s.
    (read SP s = stackpointer /\
     read (memory :> bytes64(word_add stackpointer (word 8))) s =
     returnaddress /\
     wordlist_from_memory(rc,24) s = round_constants /\
     read (memory :> bytes64 stackpointer) s = x29_init /\
     read (memory :> bytes64(word_add stackpointer (word 16))) s = x19_init /\
     read (memory :> bytes64(word_add stackpointer (word 24))) s = x20_init /\
     read (memory :> bytes64(word_add stackpointer (word 32))) s = x21_init /\
     read (memory :> bytes64(word_add stackpointer (word 40))) s = x22_init /\
     read (memory :> bytes64(word_add stackpointer (word 48))) s = x23_init /\
     read (memory :> bytes64(word_add stackpointer (word 56))) s = x24_init /\
     read (memory :> bytes64(word_add stackpointer (word 64))) s = x25_init /\
     read (memory :> bytes64(word_add stackpointer (word 72))) s = x26_init /\
     read (memory :> bytes64(word_add stackpointer (word 80))) s = x27_init /\
     read (memory :> bytes64(word_add stackpointer (word 88))) s = x28_init /\
     read (memory :> bytes64(word_add stackpointer (word 144))) s = word i /\
     read (memory :> bytes64(word_add stackpointer (word 200))) s = a /\
     read (memory :> bytes64(word_add stackpointer (word 192))) s = rc /\
     [read (memory :> bytes64 (word_add stackpointer (word 112))) s;
      read (memory :> bytes64 (word_add stackpointer (word 152))) s;
      read (memory :> bytes64 (word_add stackpointer (word 160))) s;
      read (memory :> bytes64 (word_add stackpointer (word 136))) s;
      read (memory :> bytes64 (word_add stackpointer (word 120))) s;
      read (memory :> bytes64 (word_add stackpointer (word 168))) s;
      read X8 s;
      read X16 s;
      read (memory :> bytes64 (word_add stackpointer (word 128))) s;
      read X28 s;
      read X15 s;
      read X25 s;
      read X5 s;
      read X23 s;
      read X19 s;
      read X26 s;
      read X3 s;
      read X30 s;
      read X6 s;
      read X24 s;
      read X2 s;
      read X9 s;
      read X4 s;
      read X27 s;
      read X7 s] =
     keccak i A) /\
   (read ZF s <=> i = 24)` THEN
  REWRITE_TAC[condition_semantics] THEN REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initial holding of the invariant ***)

    REWRITE_TAC[round_constants; CONS_11; GSYM CONJ_ASSOC;
     WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc,24) s:int64 list`] THEN
    ENSURES_INIT_TAC "s0" THEN
    BIGNUM_DIGITIZE_TAC "A_" `read (memory :> bytes (a,8 * 25)) s0` THEN
    FIRST_ASSUM(MP_TAC o CONV_RULE(LAND_CONV WORDLIST_FROM_MEMORY_CONV)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ARM_STEPS_TAC SHA3_KECCAK_F1600_ALT2_EXEC (1--48) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[keccak];

    (*** Preservation of the invariant including end condition code ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[round_constants; CONS_11; GSYM CONJ_ASSOC;
     WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc,24) s:int64 list`] THEN
    GHOST_STATELIST_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read (memory :> bytes64(word_add rc (word(8 * i)))) s0 =
      EL i round_constants`
    ASSUME_TAC THENL
     [UNDISCH_TAC `i < 24` THEN SPEC_TAC(`i:num`,`i:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
      ASM_REWRITE_TAC[round_constants; WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[];
      ALL_TAC] THEN
    ARM_STEPS_TAC SHA3_KECCAK_F1600_ALT2_EXEC (1--157) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [ALL_TAC;
      UNDISCH_TAC `i < 24` THEN SPEC_TAC(`i:num`,`i:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV)] THEN
    REWRITE_TAC[keccak] THEN FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
    REWRITE_TAC[keccak_round] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[CONS_11] THEN REPEAT CONJ_TAC THEN BITBLAST_TAC;

    (*** The trivial loop-back goal ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[round_constants; CONS_11; GSYM CONJ_ASSOC;
     WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc,24) s:int64 list`] THEN
    ARM_SIM_TAC SHA3_KECCAK_F1600_ALT2_EXEC [1] THEN
    VAL_INT64_TAC `i:num` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    ASM_SIMP_TAC[LT_IMP_NE];

    (*** The writeback tail ***)

    REWRITE_TAC[DREG_EXPAND_CLAUSES; READ_ZEROTOP_64] THEN
    GHOST_STATELIST_TAC THEN
    ARM_SIM_TAC SHA3_KECCAK_F1600_ALT2_EXEC (1--39) THEN
    CONV_TAC(LAND_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec = mk_safety_spec
    (assoc "sha3_keccak_f1600_alt2" subroutine_signatures)
    SHA3_KECCAK_F1600_ALT2_SUBROUTINE_CORRECT
    SHA3_KECCAK_F1600_ALT2_EXEC;;

let SHA3_KECCAK_F1600_ALT2_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall a rc pc stackpointer returnaddress.
           aligned 16 stackpointer /\
           ALL (nonoverlapping (word_sub stackpointer (word 208),208))
           [word pc,976; a,200; rc,192] /\
           nonoverlapping (a,200) (word pc,976)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    sha3_keccak_f1600_alt2_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    read SP s = stackpointer /\
                    C_ARGUMENTS [a; rc] s /\
                    read events s = e)
               (\s.
                    exists e2.
                        read PC s = returnaddress /\
                        read events s = APPEND e2 e /\
                        e2 =
                        f_events rc a pc (word_sub stackpointer (word 208))
                        returnaddress /\
                        memaccess_inbounds e2
                        [a,200; rc,192; a,200;
                         word_sub stackpointer (word 208),208]
                        [a,200; word_sub stackpointer (word 208),208])
               (\s s'. true)`,
  ASSERT_GOAL_TAC full_spec THEN
  PROVE_SAFETY_SPEC SHA3_KECCAK_F1600_ALT2_EXEC);;
