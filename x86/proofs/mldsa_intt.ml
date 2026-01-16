(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ML-DSA Inverse number theoretic transform.                                *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(*** print_literal_from_elf "x86/mldsa/mldsa_intt.o";;
 ***)

needs "x86/proofs/mldsa_intt_mc.ml";;

let mldsa_intt_tmc = define_trimmed "mldsa_intt_tmc" mldsa_intt_mc;;
let MLDSA_INTT_TMC_EXEC = X86_MK_CORE_EXEC_RULE mldsa_intt_tmc;;

(* ------------------------------------------------------------------------- *)
(* Data tables that are assumed in the precondition.                         *)
(* ------------------------------------------------------------------------- *)

(*** ML-DSA NTT zeta array: 624 elements total
 *** - [0-31]: ML-DSA constants (q=8380417, qinv=58728449, etc.)
 *** - [32-39]: Initial twiddle factors
 *** - [40-367]: 4x replicated twiddles for SIMD (82 unique values × 4 copies)
 *** - [368-623]: Final twiddle section with 2x replication (128 unique values × 2 copies)
 *** Follows bit-reversed indexing per FIPS 204 Appendix B with AVX2 optimization
 ***)
let mldsa_complete_qdata = define
 `mldsa_complete_qdata:int list =
   [
   &8380417; &8380417; &8380417; &8380417; &8380417; &8380417; &8380417; &8380417;
   &58728449; &58728449; &58728449; &58728449; &58728449; &58728449; &58728449; &58728449;
   -- &8395782; -- &8395782; -- &8395782; -- &8395782; -- &8395782; -- &8395782; -- &8395782; -- &8395782;
   &41978; &41978; &41978; &41978; &41978; &41978; &41978; &41978;
   -- &151046689;
   &1830765815; -- &1929875198; -- &1927777021; &1640767044; &1477910808; &1612161320; &1640734244; &308362795;
   &308362795; &308362795; &308362795; -- &1815525077; -- &1815525077; -- &1815525077; -- &1815525077;
   -- &1374673747; -- &1374673747; -- &1374673747; -- &1374673747; -- &1091570561; -- &1091570561; -- &1091570561;
   -- &1091570561; -- &1929495947; -- &1929495947; -- &1929495947; -- &1929495947; &515185417; &515185417;
   &515185417; &515185417; -- &285697463; -- &285697463; -- &285697463; -- &285697463; &625853735; &625853735;
   &625853735; &625853735; &1727305304; &1727305304; &2082316400; &2082316400; -- &1364982364; -- &1364982364;
   &858240904; &858240904; &1806278032; &1806278032; &222489248; &222489248; -- &346752664; -- &346752664;
   &684667771; &684667771; &1654287830; &1654287830; -- &878576921; -- &878576921; -- &1257667337; -- &1257667337;
   -- &748618600; -- &748618600; &329347125; &329347125; &1837364258; &1837364258; -- &1443016191; -- &1443016191;
   -- &1170414139; -- &1170414139; -- &1846138265; -- &1631226336; -- &1404529459; &1838055109; &1594295555;
   -- &1076973524; -- &1898723372; -- &594436433; -- &202001019; -- &475984260; -- &561427818; &1797021249;
   -- &1061813248; &2059733581; -- &1661512036; -- &1104976547; -- &1750224323; -- &901666090; &418987550;
   &1831915353; -- &1925356481; &992097815; &879957084; &2024403852; &1484874664; -- &1636082790; -- &285388938;
   -- &1983539117; -- &1495136972; -- &950076368; -- &1714807468; -- &952438995; -- &1574918427; &1350681039;
   -- &2143979939; &1599739335; -- &1285853323; -- &993005454; -- &1440787840; &568627424; -- &783134478;
   -- &588790216; &289871779; -- &1262003603; &2135294594; -- &1018755525; -- &889861155; &1665705315; &1321868265;
   &1225434135; -- &1784632064; &666258756; &675310538; -- &1555941048; -- &1999506068; -- &1499481951;
   -- &695180180; -- &1375177022; &1777179795; &334803717; -- &178766299; -- &518252220; &1957047970; &1146323031;
   -- &654783359; -- &1974159335; &1651689966; &140455867; -- &1039411342; &1955560694; &1529189038;
   -- &2131021878; -- &247357819; &1518161567; -- &86965173; &1708872713; &1787797779; &1638590967; -- &120646188;
   -- &1669960606; -- &916321552; &1155548552; &2143745726; &1210558298; -- &1261461890; -- &318346816; &628664287;
   -- &1729304568; &1422575624; &1424130038; -- &1185330464; &235321234; &168022240; &1206536194; &985155484;
   -- &894060583; -- &898413; -- &1363460238; -- &605900043; &2027833504; &14253662; &1014493059; &863641633;
   &1819892093; &2124962073; -- &1223601433; -- &1920467227; -- &1637785316; -- &1536588520; &694382729;
   &235104446; -- &1045062172; &831969619; -- &300448763; &756955444; -- &260312805; &1554794072; &1339088280;
   -- &2040058690; -- &853476187; -- &2047270596; -- &1723816713; -- &1591599803; -- &440824168; &1119856484;
   &1544891539; &155290192; -- &973777462; &991903578; &912367099; -- &44694137; &1176904444; -- &421552614;
   -- &818371958; &1747917558; -- &325927722; &908452108; &1851023419; -- &1176751719; -- &1354528380; -- &72690498;
   -- &314284737; &985022747; &963438279; -- &1078959975; &604552167; -- &1021949428; &608791570; &173440395;
   -- &2126092136; -- &1316619236; -- &1039370342; &6087993; -- &110126092; &565464272; -- &1758099917; -- &1600929361;
   &879867909; -- &1809756372; &400711272; &1363007700; &30313375; -- &326425360; &1683520342; -- &517299994;
   &2027935492; -- &1372618620; &128353682; -- &1123881663; &137583815; -- &635454918; -- &642772911; &45766801;
   &671509323; -- &2070602178; &419615363; &1216882040; -- &270590488; -- &1276805128; &371462360; -- &1357098057;
   -- &384158533; &827959816; -- &596344473; &702390549; -- &279505433; -- &260424530; -- &71875110; -- &1208667171;
   -- &1499603926; &2036925262; -- &540420426; &746144248; -- &1420958686; &2032221021; &1904936414; &1257750362;
   &1926727420; &1931587462; &1258381762; &885133339; &1629985060; &1967222129; &6363718; -- &1287922800;
   &1136965286; &1779436847; &1116720494; &1042326957; &1405999311; &713994583; &940195359; -- &1542497137;
   &2061661095; -- &883155599; &1726753853; -- &1547952704; &394851342; &283780712; &776003547; &1123958025;
   &201262505; &1934038751; &374860238;
   -- &3975713; &25847; -- &2608894; -- &518909; &237124; -- &777960; -- &876248; &466468; &1826347; &1826347; &1826347;
   &1826347; &2353451; &2353451; &2353451; &2353451; -- &359251; -- &359251; -- &359251; -- &359251; -- &2091905;
   -- &2091905; -- &2091905; -- &2091905; &3119733; &3119733; &3119733; &3119733; -- &2884855; -- &2884855; -- &2884855;
   -- &2884855; &3111497; &3111497; &3111497; &3111497; &2680103; &2680103; &2680103; &2680103; &2725464;
   &2725464; &1024112; &1024112; -- &1079900; -- &1079900; &3585928; &3585928; -- &549488; -- &549488; -- &1119584;
   -- &1119584; &2619752; &2619752; -- &2108549; -- &2108549; -- &2118186; -- &2118186; -- &3859737; -- &3859737;
   -- &1399561; -- &1399561; -- &3277672; -- &3277672; &1757237; &1757237; -- &19422; -- &19422; &4010497; &4010497;
   &280005; &280005; &2706023; &95776; &3077325; &3530437; -- &1661693; -- &3592148; -- &2537516; &3915439;
   -- &3861115; -- &3043716; &3574422; -- &2867647; &3539968; -- &300467; &2348700; -- &539299; -- &1699267;
   -- &1643818; &3505694; -- &3821735; &3507263; -- &2140649; -- &1600420; &3699596; &811944; &531354; &954230;
   &3881043; &3900724; -- &2556880; &2071892; -- &2797779; -- &3930395; -- &3677745; -- &1452451; &2176455;
   -- &1257611; -- &4083598; -- &3190144; -- &3632928; &3412210; &2147896; -- &2967645; -- &411027; -- &671102;
   -- &22981; -- &381987; &1852771; -- &3343383; &508951; &44288; &904516; -- &3724342; &1653064; &2389356;
   &759969; &189548; &3159746; -- &2409325; &1315589; &1285669; -- &812732; -- &3019102; -- &3628969; -- &1528703;
   -- &3041255; &3475950; -- &1585221; &1939314; -- &1000202; -- &3157330; &126922; -- &983419; &2715295;
   -- &3693493; -- &2477047; -- &1228525; -- &1308169; &1349076; -- &1430430; &264944; &3097992; -- &1100098;
   &3958618; -- &8578; -- &3249728; -- &210977; -- &1316856; -- &3553272; -- &1851402; -- &177440; &1341330;
   -- &1584928; -- &1439742; -- &3881060; &3839961; &2091667; -- &3342478; &266997; -- &3520352; &900702;
   &495491; -- &655327; -- &3556995; &342297; &3437287; &2842341; &4055324; -- &3767016; -- &2994039; -- &1333058;
   -- &451100; -- &1279661; &1500165; -- &542412; -- &2584293; -- &2013608; &1957272; -- &3183426; &810149;
   -- &3038916; &2213111; -- &426683; -- &1667432; -- &2939036; &183443; -- &554416; &3937738; &3407706;
   &2244091; &2434439; -- &3759364; &1859098; -- &1613174; -- &3122442; -- &525098; &286988; -- &3342277;
   &2691481; &1247620; &1250494; &1869119; &1237275; &1312455; &1917081; &777191; -- &2831860; -- &3724270;
   &2432395; &3369112; &162844; &1652634; &3523897; -- &975884; &1723600; -- &1104333; -- &2235985; -- &976891;
   &3919660; &1400424; &2316500; -- &2446433; -- &1235728; -- &1197226; &909542; -- &43260; &2031748; -- &768622;
   -- &2437823; &1735879; -- &2590150; &2486353; &2635921; &1903435; -- &3318210; &3306115; -- &2546312;
   &2235880; -- &1671176; &594136; &2454455; &185531; &1616392; -- &3694233; &3866901; &1717735; -- &1803090;
   -- &260646; -- &420899; &1612842; -- &48306; -- &846154; &3817976; -- &3562462; &3513181; -- &3193378;
   &819034; -- &522500; &3207046; -- &3595838; &4108315; &203044; &1265009; &1595974; -- &3548272; -- &1050970;
   -- &1430225; -- &1962642; -- &1374803; &3406031; -- &1846953; -- &3776993; -- &164721; -- &1207385; &3014001;
   -- &1799107; &269760; &472078; &1910376; -- &3833893; -- &2286327; -- &3545687; -- &1362209; &1976782
   ]`;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)


(*** getting PC length/size:
let len_thm = REWRITE_CONV[mldsa_intt_tmc] `LENGTH mldsa_intt_tmc` in
let len_computed = LENGTH_CONV (rhs (concl len_thm)) in
let final_value = rhs (concl len_computed) in
dest_small_numeral final_value;;

val it : int = 12129
pc + 0x2F61 ***)

(*** let MLDSA_INTT_CORRECT = prove ***)
 g(`!a zetas x pc.
    aligned 32 a /\
    aligned 32 zetas /\
    nonoverlapping (word pc,0x2F61) (a, 1024) /\
    nonoverlapping (word pc,0x2F61) (zetas, 2496) /\
    nonoverlapping (a, 1024) (zetas, 2496)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST mldsa_intt_tmc) /\
              read RIP s = word pc /\
              C_ARGUMENTS [a; zetas] s /\
              wordlist_from_memory(zetas,624) s = MAP (iword: int -> 32 word) mldsa_complete_qdata /\
              (!i. i < 256 ==> abs(ival(x i)) <= &42035261) /\
              !i. i < 256
                  ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                      x i)
          (\s. read RIP s = word(pc + 0x2F60) /\
              (!i. i < 256
                        ==> let zi =
                      read(memory :> bytes32(word_add a (word(4 * i)))) s in
                      (ival zi == mldsa_inverse_ntt (ival o x) i) (mod &8380417) /\
                      abs(ival zi) <= &6135312))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
          MAYCHANGE [RAX] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [memory :> bytes(a,1024)])`);;

(*** Setup - introduce variables and break down assumptions ***)    

e(MAP_EVERY X_GEN_TAC [`a:int64`; `zetas:int64`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL]);;

e(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC));;

e(GLOBALIZE_PRECONDITION_TAC);;

e(CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC);;

e(REWRITE_TAC [SOME_FLAGS; fst MLDSA_INTT_TMC_EXEC]);;  

e(GHOST_INTRO_TAC `init_ymm0:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `init_ymm1:int256` `read YMM1` THEN
  GHOST_INTRO_TAC `init_ymm2:int256` `read YMM2` THEN
  GHOST_INTRO_TAC `init_ymm3:int256` `read YMM3` THEN
  GHOST_INTRO_TAC `init_ymm4:int256` `read YMM4` THEN
  GHOST_INTRO_TAC `init_ymm5:int256` `read YMM5` THEN
  GHOST_INTRO_TAC `init_ymm6:int256` `read YMM6` THEN
  GHOST_INTRO_TAC `init_ymm7:int256` `read YMM7` THEN
  GHOST_INTRO_TAC `init_ymm8:int256` `read YMM8` THEN
  GHOST_INTRO_TAC `init_ymm9:int256` `read YMM9` THEN
  GHOST_INTRO_TAC `init_ymm10:int256` `read YMM10` THEN
  GHOST_INTRO_TAC `init_ymm11:int256` `read YMM11` THEN
  GHOST_INTRO_TAC `init_ymm12:int256` `read YMM12` THEN
  GHOST_INTRO_TAC `init_ymm13:int256` `read YMM13` THEN
  GHOST_INTRO_TAC `init_ymm14:int256` `read YMM14` THEN
  GHOST_INTRO_TAC `init_ymm15:int256` `read YMM15` THEN
  ENSURES_INIT_TAC "s0");;

(*** First restructure all the loads from the a pointer ***)

e(MP_TAC(end_itlist CONJ (map (fun n ->
    READ_MEMORY_MERGE_CONV 3 (subst[mk_small_numeral(32*n),`n:num`]
      `read (memory :> bytes256(word_add a (word n))) s0`)) (0--31))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`] THEN
  CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN STRIP_TAC);;

(*** Expand the qdata table ***)
e(FIRST_X_ASSUM(MP_TAC o CONV_RULE (LAND_CONV WORDLIST_FROM_MEMORY_CONV)) THEN
  REWRITE_TAC[mldsa_complete_qdata; MAP; CONS_11] THEN
  STRIP_TAC);;

(*** Restructure zeta entries, as before but with WORD_REDUCE_CONV to simplify ***)
e(MP_TAC(end_itlist CONJ (map (fun n ->
    READ_MEMORY_MERGE_CONV 3 (subst[mk_small_numeral(32*n),`n:num`]
      `read (memory :> bytes256(word_add zetas (word n))) s0`)) (0--77))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`] THEN
  CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN STRIP_TAC);;

(*** resurrect some of them here starting at zetas+1312 ***)
e(FIRST_ASSUM(MP_TAC o check
  (can (term_match [] `read (memory :> bytes256 (word_add zetas (word 1312))) s0 = xxx`) o concl)) THEN
  CONV_TAC(LAND_CONV(READ_MEMORY_SPLIT_CONV 3)) THEN
  CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN STRIP_TAC);;

(*** Do the simulation ***)

e(MAP_EVERY (fun n -> X86_STEPS_TAC MLDSA_INTT_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_ABBREV_TAC[mldsa_montmul]
                        [WORD_ADD_MLDSA_MONTMUL;
                         WORD_ADD_MLDSA_MONTMUL_ALT; WORD_SUB_MLDSA_MONTMUL])
        (1--2265) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

(*** Reverse the restructuring by splitting the 256-bit words up ***)

e(REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
  CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
  CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
  check (can (term_match [] `read qqq s:int256 = xxx`) o concl))));;

(*** Expand the cases in the conclusion ***)
 e(CONV_TAC(TOP_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV THENC
           DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[INT_ABS_BOUNDS; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[WORD_ADD_0]);;

e(ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s2265");;

(* 
  W(fun (asl,w) ->
     let asms =
        map snd (filter (is_local_definition
          [mldsa_montmul] o concl o snd) asl) in
     MP_TAC(end_itlist CONJ (rev asms)) THEN
     MAP_EVERY (fun t -> UNDISCH_THEN (concl t) (K ALL_TAC)) asms) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;
*)

e(REWRITE_TAC[WORD_BLAST `word_subword (x:int32) (0, 32) = x`] THEN
  REWRITE_TAC[WORD_BLAST `word_subword (x:int64) (0, 64) = x`] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV));;

e(CONV_TAC(DEPTH_CONV let_CONV));;

e(REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  REPEAT(GEN_REWRITE_TAC I
   [TAUT `p /\\ q /\\ r /\\ s <=> (p /\\ q /\\ r) /\\ s`] THEN CONJ_TAC));;

e(POP_ASSUM_LIST(K ALL_TAC));;

(*** Try splitting into 256 subgoals and applying GEN_CONGBOUND with input bounds ***)

e(CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  REPEAT(GEN_REWRITE_TAC I
   [TAUT `p /\ q /\ r /\ s <=> (p /\ q /\ r) /\ s`] THEN CONJ_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o CONV_RULE EXPAND_CASES_CONV) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  DISCH_THEN(fun aboth ->
    W(MP_TAC o GEN_CONGBOUND_RULE (CONJUNCTS aboth) o
      rand o lhand o rator o lhand o snd)) THEN
  (MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
   [REWRITE_TAC[INVERSE_MOD_CONV `inverse_mod 8380417 4294967296`] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
    CONV_TAC(ONCE_DEPTH_CONV MLDSA_INVERSE_NTT_CONV) THEN
    REWRITE_TAC[GSYM INT_REM_EQ; o_THM] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    REWRITE_TAC[INT_REM_EQ] THEN
    REWRITE_TAC[REAL_INT_CONGRUENCE; INT_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC;
    MATCH_MP_TAC(INT_ARITH
     `l':int <= l /\ u <= u'
      ==> l <= x /\ x <= u ==> l' <= x /\ x <= u'`) THEN
    CONV_TAC INT_REDUCE_CONV]));;

(* full version:

let MLDSA_INTT_CORRECT = prove
  (`!a zetas x pc.
    aligned 32 a /\
    aligned 32 zetas /\
    nonoverlapping (word pc,0x2F61) (a, 1024) /\
    nonoverlapping (word pc,0x2F61) (zetas, 2496) /\
    nonoverlapping (a, 1024) (zetas, 2496)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST mldsa_intt_tmc) /\
              read RIP s = word pc /\
              C_ARGUMENTS [a; zetas] s /\
              wordlist_from_memory(zetas,624) s = MAP (iword: int -> 32 word) mldsa_complete_qdata /\
              (!i. i < 256 ==> abs(ival(x i)) <= &42035261) /\
              !i. i < 256
                  ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                      x i)
          (\s. read RIP s = word(pc + 0x2F60) /\
              (!i. i < 256
                        ==> let zi =
                      read(memory :> bytes32(word_add a (word(4 * i)))) s in
                      (ival zi == mldsa_inverse_ntt (ival o x) i) (mod &8380417) /\
                      abs(ival zi) <= &6135312))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [ZMM0; ZMM1; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10; ZMM11; ZMM12; ZMM13; ZMM14; ZMM15] ,,
          MAYCHANGE [RAX] ,, MAYCHANGE SOME_FLAGS ,,
          MAYCHANGE [memory :> bytes(a,1024)])`,

(*** Setup - introduce variables and break down assumptions ***)
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `zetas:int64`; `x:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

(*** Pull out the bounds assumption since we don't need to expand it
 *** until much later, and it keeps things a bit smaller and simpler
 ***)

  GLOBALIZE_PRECONDITION_TAC THEN

(*** But do expand all the input[i] = x i assumptions ***)

  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN

  REWRITE_TAC [SOME_FLAGS; fst MLDSA_INTT_TMC_EXEC] THEN

  GHOST_INTRO_TAC `init_ymm0:int256` `read YMM0` THEN
  GHOST_INTRO_TAC `init_ymm1:int256` `read YMM1` THEN
  GHOST_INTRO_TAC `init_ymm2:int256` `read YMM2` THEN

  ENSURES_INIT_TAC "s0" THEN

(*** First restructure all the loads from the a pointer ***)

  MP_TAC(end_itlist CONJ (map (fun n ->
    READ_MEMORY_MERGE_CONV 3 (subst[mk_small_numeral(32*n),`n:num`]
      `read (memory :> bytes256(word_add a (word n))) s0`)) (0--31))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`] THEN
  CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN STRIP_TAC THEN

(*** Expand the qdata table ***)

  FIRST_X_ASSUM(MP_TAC o CONV_RULE (LAND_CONV WORDLIST_FROM_MEMORY_CONV)) THEN
  REWRITE_TAC[mldsa_complete_qdata; MAP; CONS_11] THEN
  STRIP_TAC THEN

(*** Restructure zeta entries, as before but with WORD_REDUCE_CONV to simplify ***)

  MP_TAC(end_itlist CONJ (map (fun n ->
    READ_MEMORY_MERGE_CONV 3 (subst[mk_small_numeral(32*n),`n:num`]
      `read (memory :> bytes256(word_add zetas (word n))) s0`)) (0--77))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`] THEN
  CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN STRIP_TAC THEN

  FIRST_ASSUM(MP_TAC o check
   (can (term_match [] `read (memory :> bytes256 (word_add zetas (word 128))) s0 = xxx`) o concl)) THEN
  CONV_TAC(LAND_CONV(READ_MEMORY_SPLIT_CONV 3)) THEN
  CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN STRIP_TAC THEN

(*** Do the simulation ***)

  MAP_EVERY (fun n -> X86_STEPS_TAC MLDSA_INTT_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[mldsa_montmul; WORD_ADD_MLDSA_MONTMUL;
                      WORD_ADD_MLDSA_MONTMUL_ALT; WORD_SUB_MLDSA_MONTMUL])
        (1--2265) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

(*** Reverse the restructuring by splitting the 256-bit words up ***)

  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
    CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
    check (can (term_match [] `read qqq s:int256 = xxx`) o concl))) THEN

(*** Expand the cases in the conclusion ***)

  CONV_TAC(TOP_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[INT_ABS_BOUNDS; WORD_ADD_0] THEN

(*** Rewrite with assumptions then throw them away ***)

  ASM_REWRITE_TAC[] THEN DISCARD_STATE_TAC "s2265" THEN

(*** Remove one other non-arithmetical oddity ***)

  REWRITE_TAC[WORD_BLAST `word_subword (x:int32) (0, 32) = x`] THEN
  REWRITE_TAC[WORD_BLAST `word_subword (x:int64) (0, 64) = x`] THEN
  CONV_TAC(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN

(*** Try splitting into 256 subgoals and applying GEN_CONGBOUND with input bounds ***)

  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  REPEAT(GEN_REWRITE_TAC I
   [TAUT `p /\ q /\ r /\ s <=> (p /\ q /\ r) /\ s`] THEN CONJ_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o CONV_RULE EXPAND_CASES_CONV) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  DISCH_THEN(fun aboth ->
    W(MP_TAC o GEN_CONGBOUND_RULE (CONJUNCTS aboth) o
      rand o lhand o rator o lhand o snd)) THEN
  (MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
   [REWRITE_TAC[INVERSE_MOD_CONV `inverse_mod 8380417 4294967296`] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
    CONV_TAC(ONCE_DEPTH_CONV MLDSA_INVERSE_NTT_CONV) THEN
    REWRITE_TAC[GSYM INT_REM_EQ; o_THM] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    REWRITE_TAC[INT_REM_EQ] THEN
    REWRITE_TAC[REAL_INT_CONGRUENCE; INT_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC;
    MATCH_MP_TAC(INT_ARITH
     `l':int <= l /\ u <= u'
      ==> l <= x /\ x <= u ==> l' <= x /\ x <= u'`) THEN
    CONV_TAC INT_REDUCE_CONV]));;

let MLDSA_INTT_NOIBT_SUBROUTINE_CORRECT = prove
  (`!a zetas x pc stackpointer returnaddress.
    aligned 32 a /\
    aligned 32 zetas /\
    nonoverlapping (word pc, LENGTH mldsa_intt_tmc) (a, 1024) /\
    nonoverlapping (word pc, LENGTH mldsa_intt_tmc) (zetas, 2496) /\
    nonoverlapping (a, 1024) (zetas, 2496) /\
    nonoverlapping (a, 1024) (stackpointer, 8) /\
    nonoverlapping (zetas, 2496) (stackpointer, 8)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mldsa_intt_tmc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [a; zetas] s /\
              wordlist_from_memory(zetas,624) s = MAP (iword: int -> 32 word) mldsa_complete_qdata /\
              !i. i < 256
                  ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                      x i)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
              (!i. i < 256
                        ==> let zi =
                      read(memory :> bytes32(word_add a (word(4 * i)))) s in
                      (ival zi == mldsa_inverse_ntt (ival o x) i) (mod &8380417) /\
                      abs(ival zi) <= &6135312))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(a,1024)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_intt_tmc (CONV_RULE TWEAK_CONV MLDSA_INTT_CORRECT));;

let MLDSA_INTT_SUBROUTINE_CORRECT = prove
  (`!a zetas x pc stackpointer returnaddress.
    aligned 32 a /\
    aligned 32 zetas /\
    nonoverlapping (word pc, LENGTH mldsa_intt_mc) (a, 1024) /\
    nonoverlapping (word pc, LENGTH mldsa_intt_mc) (zetas, 2496) /\
    nonoverlapping (a, 1024) (zetas, 2496) /\
    nonoverlapping (a, 1024) (stackpointer, 8) /\
    nonoverlapping (zetas, 2496) (stackpointer, 8)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mldsa_intt_mc /\
              read RIP s = word pc /\
              read RSP s = stackpointer /\
              read (memory :> bytes64 stackpointer) s = returnaddress /\
              C_ARGUMENTS [a; zetas] s /\
              wordlist_from_memory(zetas,624) s = MAP (iword: int -> 32 word) mldsa_complete_qdata /\
              !i. i < 256
                  ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                      x i)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
              (!i. i < 256
                        ==> let zi =
                      read(memory :> bytes32(word_add a (word(4 * i)))) s in
                      (ival zi == mldsa_inverse_ntt (ival o x) i) (mod &8380417) /\
                      abs(ival zi) <= &6135312))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(a,1024)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
  (CONV_RULE TWEAK_CONV MLDSA_INTT_NOIBT_SUBROUTINE_CORRECT)));;
*)
