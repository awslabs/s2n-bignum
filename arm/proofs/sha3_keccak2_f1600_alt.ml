(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* 2-way batch Keccak-f1600 vector code.                                     *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/utils/keccak_spec.ml";;

(**** print_literal_from_elf "arm/sha3/sha3_keccak2_f1600_alt.o";;
 ****)

let sha3_keccak2_f1600_alt_mc = define_assert_from_elf
  "sha3_keccak2_f1600_alt_mc" "arm/sha3/sha3_keccak2_f1600_alt.o"
[
  0xd10103ff;       (* arm_SUB SP SP (rvalue (word 64)) *)
  0x6d0027e8;       (* arm_STP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0x6d012fea;       (* arm_STP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d0237ec;       (* arm_STP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d033fee;       (* arm_STP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x91032002;       (* arm_ADD X2 X0 (rvalue (word 200)) *)
  0xad406418;       (* arm_LDP Q24 Q25 X0 (Immediate_Offset (iword (&0))) *)
  0xad406c5a;       (* arm_LDP Q26 Q27 X2 (Immediate_Offset (iword (&0))) *)
  0x4eda2b00;       (* arm_TRN1 Q0 Q24 Q26 64 128 *)
  0x4eda6b01;       (* arm_TRN2 Q1 Q24 Q26 64 128 *)
  0x4edb2b22;       (* arm_TRN1 Q2 Q25 Q27 64 128 *)
  0x4edb6b23;       (* arm_TRN2 Q3 Q25 Q27 64 128 *)
  0xad416418;       (* arm_LDP Q24 Q25 X0 (Immediate_Offset (iword (&32))) *)
  0xad416c5a;       (* arm_LDP Q26 Q27 X2 (Immediate_Offset (iword (&32))) *)
  0x4eda2b04;       (* arm_TRN1 Q4 Q24 Q26 64 128 *)
  0x4eda6b05;       (* arm_TRN2 Q5 Q24 Q26 64 128 *)
  0x4edb2b26;       (* arm_TRN1 Q6 Q25 Q27 64 128 *)
  0x4edb6b27;       (* arm_TRN2 Q7 Q25 Q27 64 128 *)
  0xad426418;       (* arm_LDP Q24 Q25 X0 (Immediate_Offset (iword (&64))) *)
  0xad426c5a;       (* arm_LDP Q26 Q27 X2 (Immediate_Offset (iword (&64))) *)
  0x4eda2b08;       (* arm_TRN1 Q8 Q24 Q26 64 128 *)
  0x4eda6b09;       (* arm_TRN2 Q9 Q24 Q26 64 128 *)
  0x4edb2b2a;       (* arm_TRN1 Q10 Q25 Q27 64 128 *)
  0x4edb6b2b;       (* arm_TRN2 Q11 Q25 Q27 64 128 *)
  0xad436418;       (* arm_LDP Q24 Q25 X0 (Immediate_Offset (iword (&96))) *)
  0xad436c5a;       (* arm_LDP Q26 Q27 X2 (Immediate_Offset (iword (&96))) *)
  0x4eda2b0c;       (* arm_TRN1 Q12 Q24 Q26 64 128 *)
  0x4eda6b0d;       (* arm_TRN2 Q13 Q24 Q26 64 128 *)
  0x4edb2b2e;       (* arm_TRN1 Q14 Q25 Q27 64 128 *)
  0x4edb6b2f;       (* arm_TRN2 Q15 Q25 Q27 64 128 *)
  0xad446418;       (* arm_LDP Q24 Q25 X0 (Immediate_Offset (iword (&128))) *)
  0xad446c5a;       (* arm_LDP Q26 Q27 X2 (Immediate_Offset (iword (&128))) *)
  0x4eda2b10;       (* arm_TRN1 Q16 Q24 Q26 64 128 *)
  0x4eda6b11;       (* arm_TRN2 Q17 Q24 Q26 64 128 *)
  0x4edb2b32;       (* arm_TRN1 Q18 Q25 Q27 64 128 *)
  0x4edb6b33;       (* arm_TRN2 Q19 Q25 Q27 64 128 *)
  0xad456418;       (* arm_LDP Q24 Q25 X0 (Immediate_Offset (iword (&160))) *)
  0xad456c5a;       (* arm_LDP Q26 Q27 X2 (Immediate_Offset (iword (&160))) *)
  0x4eda2b14;       (* arm_TRN1 Q20 Q24 Q26 64 128 *)
  0x4eda6b15;       (* arm_TRN2 Q21 Q24 Q26 64 128 *)
  0x4edb2b36;       (* arm_TRN1 Q22 Q25 Q27 64 128 *)
  0x4edb6b37;       (* arm_TRN2 Q23 Q25 Q27 64 128 *)
  0xfd406018;       (* arm_LDR D24 X0 (Immediate_Offset (word 192)) *)
  0xfd406059;       (* arm_LDR D25 X2 (Immediate_Offset (word 192)) *)
  0x4ed92b18;       (* arm_TRN1 Q24 Q24 Q25 64 128 *)
  0xd2800302;       (* arm_MOV X2 (rvalue (word 24)) *)
  0x6e251c1e;       (* arm_EOR_VEC Q30 Q0 Q5 128 *)
  0x6e2a1fde;       (* arm_EOR_VEC Q30 Q30 Q10 128 *)
  0xce0f53de;       (* arm_EOR3 Q30 Q30 Q15 Q20 *)
  0x6e261c3d;       (* arm_EOR_VEC Q29 Q1 Q6 128 *)
  0x6e2b1fbd;       (* arm_EOR_VEC Q29 Q29 Q11 128 *)
  0xce1057bd;       (* arm_EOR3 Q29 Q29 Q16 Q21 *)
  0x6e271c5c;       (* arm_EOR_VEC Q28 Q2 Q7 128 *)
  0x6e2c1f9c;       (* arm_EOR_VEC Q28 Q28 Q12 128 *)
  0xce115b9c;       (* arm_EOR3 Q28 Q28 Q17 Q22 *)
  0x6e281c7b;       (* arm_EOR_VEC Q27 Q3 Q8 128 *)
  0x6e2d1f7b;       (* arm_EOR_VEC Q27 Q27 Q13 128 *)
  0xce125f7b;       (* arm_EOR3 Q27 Q27 Q18 Q23 *)
  0x6e291c9a;       (* arm_EOR_VEC Q26 Q4 Q9 128 *)
  0x6e2e1f5a;       (* arm_EOR_VEC Q26 Q26 Q14 128 *)
  0xce13635a;       (* arm_EOR3 Q26 Q26 Q19 Q24 *)
  0x4efc879f;       (* arm_ADD_VEC Q31 Q28 Q28 64 128 *)
  0x6f41479f;       (* arm_SRI_VEC Q31 Q28 63 64 128 *)
  0x6e3e1ff9;       (* arm_EOR_VEC Q25 Q31 Q30 128 *)
  0xce7a8f9c;       (* arm_RAX1 Q28 Q28 Q26 *)
  0x4efd87bf;       (* arm_ADD_VEC Q31 Q29 Q29 64 128 *)
  0x6f4147bf;       (* arm_SRI_VEC Q31 Q29 63 64 128 *)
  0x6e3a1ffa;       (* arm_EOR_VEC Q26 Q31 Q26 128 *)
  0xce7b8fbd;       (* arm_RAX1 Q29 Q29 Q27 *)
  0x4efe87df;       (* arm_ADD_VEC Q31 Q30 Q30 64 128 *)
  0x6f4147df;       (* arm_SRI_VEC Q31 Q30 63 64 128 *)
  0x6e3b1ffb;       (* arm_EOR_VEC Q27 Q31 Q27 128 *)
  0x6e3a1c1e;       (* arm_EOR_VEC Q30 Q0 Q26 128 *)
  0xce9d0840;       (* arm_XAR Q0 Q2 Q29 (word 2) *)
  0x6e3d1d9f;       (* arm_EOR_VEC Q31 Q12 Q29 128 *)
  0x4f6b57e2;       (* arm_SHL_VEC Q2 Q31 43 64 128 *)
  0x6f6b47e2;       (* arm_SRI_VEC Q2 Q31 21 64 128 *)
  0xce9c9dac;       (* arm_XAR Q12 Q13 Q28 (word 39) *)
  0x6e3b1e7f;       (* arm_EOR_VEC Q31 Q19 Q27 128 *)
  0x4f4857ed;       (* arm_SHL_VEC Q13 Q31 8 64 128 *)
  0x6f4847ed;       (* arm_SRI_VEC Q13 Q31 56 64 128 *)
  0xce9c22f3;       (* arm_XAR Q19 Q23 Q28 (word 8) *)
  0x6e3a1dff;       (* arm_EOR_VEC Q31 Q15 Q26 128 *)
  0x4f6957f7;       (* arm_SHL_VEC Q23 Q31 41 64 128 *)
  0x6f6947f7;       (* arm_SRI_VEC Q23 Q31 23 64 128 *)
  0xce99fc2f;       (* arm_XAR Q15 Q1 Q25 (word 63) *)
  0x6e3c1d1f;       (* arm_EOR_VEC Q31 Q8 Q28 128 *)
  0x4f7757e1;       (* arm_SHL_VEC Q1 Q31 55 64 128 *)
  0x6f7747e1;       (* arm_SRI_VEC Q1 Q31 9 64 128 *)
  0xce994e08;       (* arm_XAR Q8 Q16 Q25 (word 19) *)
  0x6e3d1cff;       (* arm_EOR_VEC Q31 Q7 Q29 128 *)
  0x4f4657f0;       (* arm_SHL_VEC Q16 Q31 6 64 128 *)
  0x6f4647f0;       (* arm_SRI_VEC Q16 Q31 58 64 128 *)
  0xce9af547;       (* arm_XAR Q7 Q10 Q26 (word 61) *)
  0x6e3c1c7f;       (* arm_EOR_VEC Q31 Q3 Q28 128 *)
  0x4f5c57ea;       (* arm_SHL_VEC Q10 Q31 28 64 128 *)
  0x6f5c47ea;       (* arm_SRI_VEC Q10 Q31 36 64 128 *)
  0xce9cae43;       (* arm_XAR Q3 Q18 Q28 (word 43) *)
  0x6e3d1e3f;       (* arm_EOR_VEC Q31 Q17 Q29 128 *)
  0x4f4f57f2;       (* arm_SHL_VEC Q18 Q31 15 64 128 *)
  0x6f4f47f2;       (* arm_SRI_VEC Q18 Q31 49 64 128 *)
  0xce99d971;       (* arm_XAR Q17 Q11 Q25 (word 54) *)
  0x6e3b1d3f;       (* arm_EOR_VEC Q31 Q9 Q27 128 *)
  0x4f5457eb;       (* arm_SHL_VEC Q11 Q31 20 64 128 *)
  0x6f5447eb;       (* arm_SRI_VEC Q11 Q31 44 64 128 *)
  0xce9d0ec9;       (* arm_XAR Q9 Q22 Q29 (word 3) *)
  0x6e3b1ddf;       (* arm_EOR_VEC Q31 Q14 Q27 128 *)
  0x4f6757f6;       (* arm_SHL_VEC Q22 Q31 39 64 128 *)
  0x6f6747f6;       (* arm_SRI_VEC Q22 Q31 25 64 128 *)
  0xce9aba8e;       (* arm_XAR Q14 Q20 Q26 (word 46) *)
  0x6e3b1c9f;       (* arm_EOR_VEC Q31 Q4 Q27 128 *)
  0x4f5b57f4;       (* arm_SHL_VEC Q20 Q31 27 64 128 *)
  0x6f5b47f4;       (* arm_SRI_VEC Q20 Q31 37 64 128 *)
  0xce9bcb04;       (* arm_XAR Q4 Q24 Q27 (word 50) *)
  0x6e391ebf;       (* arm_EOR_VEC Q31 Q21 Q25 128 *)
  0x4f4257f8;       (* arm_SHL_VEC Q24 Q31 2 64 128 *)
  0x6f4247f8;       (* arm_SRI_VEC Q24 Q31 62 64 128 *)
  0xce9a70b5;       (* arm_XAR Q21 Q5 Q26 (word 28) *)
  0x6e391cdf;       (* arm_EOR_VEC Q31 Q6 Q25 128 *)
  0x4f6c57fb;       (* arm_SHL_VEC Q27 Q31 44 64 128 *)
  0x6f6c47fb;       (* arm_SRI_VEC Q27 Q31 20 64 128 *)
  0x4ddfcc3c;       (* arm_LD1R Q28 X1 (Postimmediate_Offset (word 8)) 64 128 *)
  0xce272d45;       (* arm_BCAX Q5 Q10 Q7 Q11 *)
  0x4e671d1f;       (* arm_BIC_VEC Q31 Q8 Q7 128 *)
  0x6e2b1fe6;       (* arm_EOR_VEC Q6 Q31 Q11 128 *)
  0xce2920e7;       (* arm_BCAX Q7 Q7 Q9 Q8 *)
  0x4e691d5f;       (* arm_BIC_VEC Q31 Q10 Q9 128 *)
  0x6e281fe8;       (* arm_EOR_VEC Q8 Q31 Q8 128 *)
  0xce2b2929;       (* arm_BCAX Q9 Q9 Q11 Q10 *)
  0x4e701d9f;       (* arm_BIC_VEC Q31 Q12 Q16 128 *)
  0x6e2f1fea;       (* arm_EOR_VEC Q10 Q31 Q15 128 *)
  0xce2d320b;       (* arm_BCAX Q11 Q16 Q13 Q12 *)
  0x4e6d1ddf;       (* arm_BIC_VEC Q31 Q14 Q13 128 *)
  0x6e2c1fec;       (* arm_EOR_VEC Q12 Q31 Q12 128 *)
  0xce2f39ad;       (* arm_BCAX Q13 Q13 Q15 Q14 *)
  0x4e6f1e1f;       (* arm_BIC_VEC Q31 Q16 Q15 128 *)
  0x6e2e1fee;       (* arm_EOR_VEC Q14 Q31 Q14 128 *)
  0xce31568f;       (* arm_BCAX Q15 Q20 Q17 Q21 *)
  0x4e711e5f;       (* arm_BIC_VEC Q31 Q18 Q17 128 *)
  0x6e351ff0;       (* arm_EOR_VEC Q16 Q31 Q21 128 *)
  0xce334a31;       (* arm_BCAX Q17 Q17 Q19 Q18 *)
  0x4e731e9f;       (* arm_BIC_VEC Q31 Q20 Q19 128 *)
  0x6e321ff2;       (* arm_EOR_VEC Q18 Q31 Q18 128 *)
  0xce355273;       (* arm_BCAX Q19 Q19 Q21 Q20 *)
  0x4e611edf;       (* arm_BIC_VEC Q31 Q22 Q1 128 *)
  0x6e201ff4;       (* arm_EOR_VEC Q20 Q31 Q0 128 *)
  0xce375835;       (* arm_BCAX Q21 Q1 Q23 Q22 *)
  0x4e771f1f;       (* arm_BIC_VEC Q31 Q24 Q23 128 *)
  0x6e361ff6;       (* arm_EOR_VEC Q22 Q31 Q22 128 *)
  0xce2062f7;       (* arm_BCAX Q23 Q23 Q0 Q24 *)
  0x4e601c3f;       (* arm_BIC_VEC Q31 Q1 Q0 128 *)
  0x6e381ff8;       (* arm_EOR_VEC Q24 Q31 Q24 128 *)
  0xce226fc0;       (* arm_BCAX Q0 Q30 Q2 Q27 *)
  0x4e621c7f;       (* arm_BIC_VEC Q31 Q3 Q2 128 *)
  0x6e3b1fe1;       (* arm_EOR_VEC Q1 Q31 Q27 128 *)
  0xce240c42;       (* arm_BCAX Q2 Q2 Q4 Q3 *)
  0x4e641fdf;       (* arm_BIC_VEC Q31 Q30 Q4 128 *)
  0x6e231fe3;       (* arm_EOR_VEC Q3 Q31 Q3 128 *)
  0xce3b7884;       (* arm_BCAX Q4 Q4 Q27 Q30 *)
  0x6e3c1c00;       (* arm_EOR_VEC Q0 Q0 Q28 128 *)
  0xd1000442;       (* arm_SUB X2 X2 (rvalue (word 1)) *)
  0xb5fff1a2;       (* arm_CBNZ X2 (word 2096692) *)
  0x91032002;       (* arm_ADD X2 X0 (rvalue (word 200)) *)
  0x4ec12819;       (* arm_TRN1 Q25 Q0 Q1 64 128 *)
  0x4ec3285a;       (* arm_TRN1 Q26 Q2 Q3 64 128 *)
  0xad006819;       (* arm_STP Q25 Q26 X0 (Immediate_Offset (iword (&0))) *)
  0x4ec16819;       (* arm_TRN2 Q25 Q0 Q1 64 128 *)
  0x4ec3685a;       (* arm_TRN2 Q26 Q2 Q3 64 128 *)
  0xad006859;       (* arm_STP Q25 Q26 X2 (Immediate_Offset (iword (&0))) *)
  0x4ec52899;       (* arm_TRN1 Q25 Q4 Q5 64 128 *)
  0x4ec728da;       (* arm_TRN1 Q26 Q6 Q7 64 128 *)
  0xad016819;       (* arm_STP Q25 Q26 X0 (Immediate_Offset (iword (&32))) *)
  0x4ec56899;       (* arm_TRN2 Q25 Q4 Q5 64 128 *)
  0x4ec768da;       (* arm_TRN2 Q26 Q6 Q7 64 128 *)
  0xad016859;       (* arm_STP Q25 Q26 X2 (Immediate_Offset (iword (&32))) *)
  0x4ec92919;       (* arm_TRN1 Q25 Q8 Q9 64 128 *)
  0x4ecb295a;       (* arm_TRN1 Q26 Q10 Q11 64 128 *)
  0xad026819;       (* arm_STP Q25 Q26 X0 (Immediate_Offset (iword (&64))) *)
  0x4ec96919;       (* arm_TRN2 Q25 Q8 Q9 64 128 *)
  0x4ecb695a;       (* arm_TRN2 Q26 Q10 Q11 64 128 *)
  0xad026859;       (* arm_STP Q25 Q26 X2 (Immediate_Offset (iword (&64))) *)
  0x4ecd2999;       (* arm_TRN1 Q25 Q12 Q13 64 128 *)
  0x4ecf29da;       (* arm_TRN1 Q26 Q14 Q15 64 128 *)
  0xad036819;       (* arm_STP Q25 Q26 X0 (Immediate_Offset (iword (&96))) *)
  0x4ecd6999;       (* arm_TRN2 Q25 Q12 Q13 64 128 *)
  0x4ecf69da;       (* arm_TRN2 Q26 Q14 Q15 64 128 *)
  0xad036859;       (* arm_STP Q25 Q26 X2 (Immediate_Offset (iword (&96))) *)
  0x4ed12a19;       (* arm_TRN1 Q25 Q16 Q17 64 128 *)
  0x4ed32a5a;       (* arm_TRN1 Q26 Q18 Q19 64 128 *)
  0xad046819;       (* arm_STP Q25 Q26 X0 (Immediate_Offset (iword (&128))) *)
  0x4ed16a19;       (* arm_TRN2 Q25 Q16 Q17 64 128 *)
  0x4ed36a5a;       (* arm_TRN2 Q26 Q18 Q19 64 128 *)
  0xad046859;       (* arm_STP Q25 Q26 X2 (Immediate_Offset (iword (&128))) *)
  0x4ed52a99;       (* arm_TRN1 Q25 Q20 Q21 64 128 *)
  0x4ed72ada;       (* arm_TRN1 Q26 Q22 Q23 64 128 *)
  0xad056819;       (* arm_STP Q25 Q26 X0 (Immediate_Offset (iword (&160))) *)
  0x4ed56a99;       (* arm_TRN2 Q25 Q20 Q21 64 128 *)
  0x4ed76ada;       (* arm_TRN2 Q26 Q22 Q23 64 128 *)
  0xad056859;       (* arm_STP Q25 Q26 X2 (Immediate_Offset (iword (&160))) *)
  0xfd006018;       (* arm_STR D24 X0 (Immediate_Offset (word 192)) *)
  0x4ed86b18;       (* arm_TRN2 Q24 Q24 Q24 64 128 *)
  0xfd006058;       (* arm_STR D24 X2 (Immediate_Offset (word 192)) *)
  0x6d4027e8;       (* arm_LDP D8 D9 SP (Immediate_Offset (iword (&0))) *)
  0x6d412fea;       (* arm_LDP D10 D11 SP (Immediate_Offset (iword (&16))) *)
  0x6d4237ec;       (* arm_LDP D12 D13 SP (Immediate_Offset (iword (&32))) *)
  0x6d433fee;       (* arm_LDP D14 D15 SP (Immediate_Offset (iword (&48))) *)
  0x910103ff;       (* arm_ADD SP SP (rvalue (word 64)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let SHA3_KECCAK2_F1600_ALT_EXEC = ARM_MK_EXEC_RULE sha3_keccak2_f1600_alt_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof                                                         *)
(* ------------------------------------------------------------------------- *)

let SHA3_KECCAK2_F1600_ALT_CORRECT = prove
 (`!a rc A A' pc.
      ALL (nonoverlapping (a,400)) [(word pc,0x340); (rc,192)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) sha3_keccak2_f1600_alt_mc /\
                read PC s = word (pc + 0x14) /\
                C_ARGUMENTS [a; rc] s /\
                wordlist_from_memory(a,25) s = A /\
                wordlist_from_memory(word_add a (word 200),25) s = A' /\
                wordlist_from_memory(rc,24) s = round_constants)
           (\s. read PC s = word(pc + 0x328) /\
                wordlist_from_memory(a,25) s = keccak 24 A /\
                wordlist_from_memory(word_add a (word 200),25) s = keccak 24 A')
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
            MAYCHANGE [memory :> bytes(a,400)])`,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `rc:int64`; `A:int64 list`; `A':int64 list`; `pc:num`] THEN
  REWRITE_TAC[fst SHA3_KECCAK2_F1600_ALT_EXEC] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Establish once and for all that A and A' have length 25 ***)

  ASM_CASES_TAC
   `LENGTH(A:int64 list) = 25 /\ LENGTH(A':int64 list) = 25`
  THENL
   [ALL_TAC;
    ENSURES_INIT_TAC "s0" THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM `LENGTH:int64 list->num`)) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN
    REWRITE_TAC[LENGTH; ARITH] THEN ASM_MESON_TAC[]] THEN

  ENSURES_WHILE_UP_TAC `24` `pc + 0xb8` `pc + 0x284`
   `\i s.
      wordlist_from_memory(rc,24) s = round_constants /\
      read X0 s = a /\
      read X1 s = word_add rc (word(8 * i)) /\
      read X2 s = word_sub (word 24) (word i) /\
      [read Q0 s; read Q1 s; read Q2 s; read Q3 s; read Q4 s;
       read Q5 s; read Q6 s; read Q7 s; read Q8 s; read Q9 s;
       read Q10 s; read Q11 s; read Q12 s; read Q13 s; read Q14 s;
       read Q15 s; read Q16 s; read Q17 s; read Q18 s; read Q19 s;
       read Q20 s; read Q21 s; read Q22 s; read Q23 s; read Q24 s] =
      MAP2 word_join (keccak i A') (keccak i A)` THEN
  REWRITE_TAC[condition_semantics] THEN REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initial holding of the invariant ***)

    REWRITE_TAC[round_constants; CONS_11; GSYM CONJ_ASSOC;
     WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc,24) s:int64 list`] THEN
    ENSURES_INIT_TAC "s0" THEN
    BIGNUM_DIGITIZE_TAC "A_" `read (memory :> bytes (a,8 * 50)) s0` THEN
    REPEAT(FIRST_X_ASSUM
     (MP_TAC o CONV_RULE(LAND_CONV WORDLIST_FROM_MEMORY_CONV))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MEMORY_128_FROM_64_TAC "a" 0 12 THEN
    MEMORY_128_FROM_64_TAC "a" 200 12 THEN
    ASM_REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN STRIP_TAC THEN
    ARM_STEPS_TAC SHA3_KECCAK2_F1600_ALT_EXEC (1--41) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
    MAP_EVERY EXPAND_TAC ["A"; "A'"] THEN
    REWRITE_TAC[MAP2; keccak; CONS_11] THEN CONV_TAC WORD_BLAST;

    (*** Preservation of the invariant including end condition code ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[round_constants; CONS_11; GSYM CONJ_ASSOC;
     WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc,24) s:int64 list`] THEN
    MP_TAC(ISPECL [`A:int64 list`; `i:num`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A':int64 list`; `i:num`] LENGTH_KECCAK) THEN
    ASM_REWRITE_TAC[IMP_IMP] THEN REWRITE_TAC[LENGTH_EQ_25] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[MAP2; CONS_11; GSYM CONJ_ASSOC] THEN
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
    ARM_STEPS_TAC SHA3_KECCAK2_F1600_ALT_EXEC (1--115) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
    REWRITE_TAC[keccak; keccak_round] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[MAP2; CONS_11] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT CONJ_TAC THEN BITBLAST_TAC;

    (*** The trivial loop-back goal ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[round_constants; CONS_11; GSYM CONJ_ASSOC;
     WORDLIST_FROM_MEMORY_CONV `wordlist_from_memory(rc,24) s:int64 list`] THEN
    ARM_SIM_TAC SHA3_KECCAK2_F1600_ALT_EXEC [1] THEN
    VAL_INT64_TAC `i:num` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
    ASM_SIMP_TAC[LT_IMP_NE];

    (*** The writeback tail ***)

    MP_TAC(ISPECL [`A:int64 list`; `24`] LENGTH_KECCAK) THEN
    MP_TAC(ISPECL [`A':int64 list`; `24`] LENGTH_KECCAK) THEN
    ASM_REWRITE_TAC[IMP_IMP] THEN REWRITE_TAC[LENGTH_EQ_25] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[MAP2; CONS_11; GSYM CONJ_ASSOC] THEN

    ARM_SIM_TAC SHA3_KECCAK2_F1600_ALT_EXEC (1--41) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN

    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 1) o
      check (can (term_match [] `read qqq s:int128 = xxx`) o concl))) THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONS_11] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST]);;

let SHA3_KECCAK2_F1600_ALT_SUBROUTINE_CORRECT = prove
(`!a rc A A' pc stackpointer returnaddress.
        aligned 16 stackpointer /\
        nonoverlapping (a,400) (word_sub stackpointer (word 64),64) /\
        ALLPAIRS nonoverlapping
          [(a,400); (word_sub stackpointer (word 64),64)]
          [(word pc,0x340); (rc,192)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc) sha3_keccak2_f1600_alt_mc /\
                  read PC s = word pc /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; rc] s /\
                  wordlist_from_memory(a,25) s = A /\
                  wordlist_from_memory (word_add a (word 200),25) s = A' /\
                  wordlist_from_memory(rc,24) s = round_constants)
             (\s. read PC s = returnaddress /\
                  wordlist_from_memory(a,25) s = keccak 24 A /\
                  wordlist_from_memory (word_add a (word 200),25) s =
                  keccak 24 A')
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,400);
                  memory :> bytes(word_sub stackpointer (word 64),64)])`,
  let TWEAK_CONV =
   ONCE_DEPTH_CONV
    (WORDLIST_FROM_MEMORY_CONV THENC
     ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) in
  CONV_TAC TWEAK_CONV THEN
  ARM_ADD_RETURN_STACK_TAC ~pre_post_nsteps:(5,5) SHA3_KECCAK2_F1600_ALT_EXEC
   (CONV_RULE TWEAK_CONV SHA3_KECCAK2_F1600_ALT_CORRECT)
  `[D8; D9; D10; D11; D12; D13; D14; D15]` 64);;


(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    (assoc "sha3_keccak2_f1600_alt" subroutine_signatures)
    SHA3_KECCAK2_F1600_ALT_SUBROUTINE_CORRECT
    SHA3_KECCAK2_F1600_ALT_EXEC;;

let SHA3_KECCAK2_F1600_ALT_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e a rc pc stackpointer returnaddress.
           aligned 16 stackpointer /\
           nonoverlapping (a,400) (word_sub stackpointer (word 64),64) /\
           ALLPAIRS nonoverlapping
           [a,400; word_sub stackpointer (word 64),64]
           [word pc,832; rc,192]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    sha3_keccak2_f1600_alt_mc /\
                    read PC s = word pc /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; rc] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 =
                        f_events rc a pc (word_sub stackpointer (word 64))
                        returnaddress /\
                        memaccess_inbounds e2
                        [a,400; rc,192; a,400;
                         word_sub stackpointer (word 64),64]
                        [a,400; word_sub stackpointer (word 64),64])
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC ~public_vars:public_vars SHA3_KECCAK2_F1600_ALT_EXEC);;
