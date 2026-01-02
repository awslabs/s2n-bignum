needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(* print_literal_from_elf "x86/mlkem/mlkem_mulcache_compute.o";; *)

let mlkem_mulcache_compute_mc = define_assert_from_elf "mlkem_mulcache_compute_mc" "x86/mlkem/mlkem_mulcache_compute.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xb8; 0x01; 0x0d; 0x01; 0x0d;
                           (* MOV (% eax) (Imm32 (word 218172673)) *)
  0xc5; 0xf9; 0x6e; 0xc0;  (* VMOVD (%_% xmm0) (% eax) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xc0;
                           (* VPBROADCASTD (%_% ymm0) (%_% xmm0) *)
  0xc5; 0xfd; 0x6f; 0x56; 0x20;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,32))) *)
  0xc5; 0xfd; 0x6f; 0x5e; 0x60;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,96))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0xe0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,992))) *)
  0xc5; 0xfd; 0x6f; 0x8a; 0x60; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rdx,1120))) *)
  0xc5; 0xf5; 0xd5; 0xea;  (* VPMULLW (%_% ymm5) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0xf5; 0xd5; 0xf3;  (* VPMULLW (%_% ymm6) (%_% ymm1) (%_% ymm3) *)
  0xc5; 0xdd; 0xe5; 0xfa;  (* VPMULHW (%_% ymm7) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x5d; 0xe5; 0xc3;  (* VPMULHW (%_% ymm8) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0x7d; 0xe5; 0xcd;  (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm5) *)
  0xc5; 0x7d; 0xe5; 0xd6;  (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm6) *)
  0xc4; 0xc1; 0x45; 0xf9; 0xf9;
                           (* VPSUBW (%_% ymm7) (%_% ymm7) (%_% ymm9) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc2;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0xc5; 0xfd; 0x7f; 0x3f;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x47; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm8) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,160))) *)
  0xc5; 0xfd; 0x6f; 0x9e; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,224))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0x00; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,1024))) *)
  0xc5; 0xfd; 0x6f; 0x8a; 0x80; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rdx,1152))) *)
  0xc5; 0xf5; 0xd5; 0xea;  (* VPMULLW (%_% ymm5) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0xf5; 0xd5; 0xf3;  (* VPMULLW (%_% ymm6) (%_% ymm1) (%_% ymm3) *)
  0xc5; 0xdd; 0xe5; 0xfa;  (* VPMULHW (%_% ymm7) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x5d; 0xe5; 0xc3;  (* VPMULHW (%_% ymm8) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0x7d; 0xe5; 0xcd;  (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm5) *)
  0xc5; 0x7d; 0xe5; 0xd6;  (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm6) *)
  0xc4; 0xc1; 0x45; 0xf9; 0xf9;
                           (* VPSUBW (%_% ymm7) (%_% ymm7) (%_% ymm9) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc2;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0xc5; 0xfd; 0x7f; 0x7f; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rdi,64))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x47; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rdi,96))) (%_% ymm8) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,288))) *)
  0xc5; 0xfd; 0x6f; 0x9e; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,352))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0x20; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,1056))) *)
  0xc5; 0xfd; 0x6f; 0x8a; 0xa0; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rdx,1184))) *)
  0xc5; 0xf5; 0xd5; 0xea;  (* VPMULLW (%_% ymm5) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0xf5; 0xd5; 0xf3;  (* VPMULLW (%_% ymm6) (%_% ymm1) (%_% ymm3) *)
  0xc5; 0xdd; 0xe5; 0xfa;  (* VPMULHW (%_% ymm7) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x5d; 0xe5; 0xc3;  (* VPMULHW (%_% ymm8) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0x7d; 0xe5; 0xcd;  (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm5) *)
  0xc5; 0x7d; 0xe5; 0xd6;  (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm6) *)
  0xc4; 0xc1; 0x45; 0xf9; 0xf9;
                           (* VPSUBW (%_% ymm7) (%_% ymm7) (%_% ymm9) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc2;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,128))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,160))) (%_% ymm8) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,416))) *)
  0xc5; 0xfd; 0x6f; 0x9e; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm3) (Memop Word256 (%% (rsi,480))) *)
  0xc5; 0xfd; 0x6f; 0xa2; 0x40; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdx,1088))) *)
  0xc5; 0xfd; 0x6f; 0x8a; 0xc0; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rdx,1216))) *)
  0xc5; 0xf5; 0xd5; 0xea;  (* VPMULLW (%_% ymm5) (%_% ymm1) (%_% ymm2) *)
  0xc5; 0xf5; 0xd5; 0xf3;  (* VPMULLW (%_% ymm6) (%_% ymm1) (%_% ymm3) *)
  0xc5; 0xdd; 0xe5; 0xfa;  (* VPMULHW (%_% ymm7) (%_% ymm4) (%_% ymm2) *)
  0xc5; 0x5d; 0xe5; 0xc3;  (* VPMULHW (%_% ymm8) (%_% ymm4) (%_% ymm3) *)
  0xc5; 0x7d; 0xe5; 0xcd;  (* VPMULHW (%_% ymm9) (%_% ymm0) (%_% ymm5) *)
  0xc5; 0x7d; 0xe5; 0xd6;  (* VPMULHW (%_% ymm10) (%_% ymm0) (%_% ymm6) *)
  0xc4; 0xc1; 0x45; 0xf9; 0xf9;
                           (* VPSUBW (%_% ymm7) (%_% ymm7) (%_% ymm9) *)
  0xc4; 0x41; 0x3d; 0xf9; 0xc2;
                           (* VPSUBW (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,192))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,224))) (%_% ymm8) *)
  0xc3                     (* RET *)
];;

let mlkem_mulcache_compute_tmc = define_trimmed "mlkem_mulcache_compute_tmc" mlkem_mulcache_compute_mc;;
let MLKEM_MULCACHE_COMPUTE_TMC_EXEC = X86_MK_CORE_EXEC_RULE mlkem_mulcache_compute_tmc;;

let qdata_full = define
`qdata_full:int list =
   [&3854; &3340; &2826; &2312; &1798; &1284; &770; &256;
    &3854; &3340; &2826; &2312; &1798; &1284; &770; &256;
    &7;    &0;    &6;    &0;    &5;    &0;    &4;   &0;
    &3;    &0;    &2;    &0;    &1;    &0;    &0;   &0;
&31498; &31498; &31498; &31498; -- &758; -- &758; -- &758; -- &758; &0; &0; &0; &0; &0; &0; &0; &0;
    &14745; &14745; &14745; &14745; &14745; &14745; &14745; &14745; &14745; &14745; &14745;
    &14745; &14745; &14745; &14745; &14745; -- &359; -- &359; -- &359; -- &359; -- &359; -- &359; -- &359;
    -- &359; -- &359; -- &359; -- &359; -- &359; -- &359; -- &359; -- &359; -- &359; &13525; &13525; &13525;
    &13525; &13525; &13525; &13525; &13525; -- &12402; -- &12402; -- &12402; -- &12402; -- &12402;
    -- &12402; -- &12402; -- &12402; &1493; &1493; &1493; &1493; &1493; &1493; &1493; &1493;
    &1422; &1422; &1422; &1422; &1422; &1422; &1422; &1422; -- &20907; -- &20907; -- &20907;
    -- &20907; &27758; &27758; &27758; &27758; -- &3799; -- &3799; -- &3799; -- &3799; -- &15690;
    -- &15690; -- &15690; -- &15690; -- &171; -- &171; -- &171; -- &171; &622; &622; &622; &622; &1577;
    &1577; &1577; &1577; &182; &182; &182; &182; -- &5827; -- &5827; &17363; &17363; -- &26360;
    -- &26360; -- &29057; -- &29057; &5571; &5571; -- &1102; -- &1102; &21438; &21438; -- &26242;
    -- &26242; &573; &573; -- &1325; -- &1325; &264; &264; &383; &383; -- &829; -- &829; &1458; &1458;
    -- &1602; -- &1602; -- &130; -- &130; -- &5689; -- &6516; &1496; &30967; -- &23565; &20179; &20710;
    &25080; -- &12796; &26616; &16064; -- &12442; &9134; -- &650; -- &25986; &27837; &1223; &652;
    -- &552; &1015; -- &1293; &1491; -- &282; -- &1544; &516; -- &8; -- &320; -- &666; -- &1618; -- &1162;
    &126; &1469; -- &335; -- &11477; -- &32227; &20494; -- &27738; &945; -- &14883; &6182; &32010;
    &10631; &29175; -- &28762; -- &18486; &17560; -- &14430; -- &5276; -- &1103; &555; -- &1251; &1550;
    &422; &177; -- &291; &1574; -- &246; &1159; -- &777; -- &602; -- &1590; -- &872; &418; -- &156; &11182;
    &13387; -- &14233; -- &21655; &13131; -- &4587; &23092; &5493; -- &32502; &30317; -- &18741;
    &12639; &20100; &18525; &19529; -- &12619; &430; &843; &871; &105; &587; -- &235; -- &460;
    &1653; &778; -- &147; &1483; &1119; &644; &349; &329; -- &75; &787; &787; &787; &787; &787;
    &787; &787; &787; &787; &787; &787; &787; &787; &787; &787; &787; -- &1517; -- &1517; -- &1517;
    -- &1517; -- &1517; -- &1517; -- &1517; -- &1517; -- &1517; -- &1517; -- &1517; -- &1517; -- &1517; -- &1517;
    -- &1517; -- &1517; &28191; &28191; &28191; &28191; &28191; &28191; &28191; &28191;
    -- &16694; -- &16694; -- &16694; -- &16694; -- &16694; -- &16694; -- &16694; -- &16694; &287; &287;
    &287; &287; &287; &287; &287; &287; &202; &202; &202; &202; &202; &202; &202; &202; &10690;
    &10690; &10690; &10690; &1358; &1358; &1358; &1358; -- &11202; -- &11202; -- &11202; -- &11202;
    &31164; &31164; &31164; &31164; &962; &962; &962; &962; -- &1202; -- &1202; -- &1202; -- &1202;
    -- &1474; -- &1474; -- &1474; -- &1474; &1468; &1468; &1468; &1468; -- &28073; -- &28073; &24313;
    &24313; -- &10532; -- &10532; &8800; &8800; &18426; &18426; &8859; &8859; &26675; &26675;
    -- &16163; -- &16163; -- &681; -- &681; &1017; &1017; &732; &732; &608; &608; -- &1542; -- &1542;
    &411; &411; -- &205; -- &205; -- &1571; -- &1571; &19883; -- &28250; -- &15887; -- &8898; -- &28309;
    &9075; -- &30199; &18249; &13426; &14017; -- &29156; -- &12757; &16832; &4311; -- &24155;
    -- &17915; -- &853; -- &90; -- &271; &830; &107; -- &1421; -- &247; -- &951; -- &398; &961; -- &1508;
    -- &725; &448; -- &1065; &677; -- &1275; -- &31183; &25435; -- &7382; &24391; -- &20927; &10946;
    &24214; &16989; &10335; -- &7934; -- &22502; &10906; &31636; &28644; &23998; -- &17422; &817;
    &603; &1322; -- &1465; -- &1215; &1218; -- &874; -- &1187; -- &1185; -- &1278; -- &1510; -- &870; -- &108;
    &996; &958; &1522; &20297; &2146; &15355; -- &32384; -- &6280; -- &14903; -- &11044; &14469;
    -- &21498; -- &20198; &23210; -- &17442; -- &23860; -- &20257; &7756; &23132; &1097; &610;
    -- &1285; &384; -- &136; -- &1335; &220; -- &1659; -- &1530; &794; -- &854; &478; -- &308; &991;
    -- &1460; &1628;
 -- &1103;
    &555; -- &1251; &1550; &422; &177; -- &291; &1574; -- &246; &1159; -- &777; -- &602; -- &1590; -- &872;
    &418; -- &156; &430; &843; &871; &105; &587; -- &235; -- &460; &1653; &778; -- &147; &1483; &1119;
    &644; &349; &329; -- &75; &817; &603; &1322; -- &1465; -- &1215; &1218; -- &874; -- &1187; -- &1185;
    -- &1278; -- &1510; -- &870; -- &108; &996; &958; &1522; &1097; &610; -- &1285; &384; -- &136;
    -- &1335; &220; -- &1659; -- &1530; &794; -- &854; &478; -- &308; &991; -- &1460; &1628; -- &335;
    -- &11477; -- &32227; &20494; -- &27738; &945; -- &14883; &6182; &32010; &10631; &29175;
    -- &28762; -- &18486; &17560; -- &14430; -- &5276; &11182; &13387; -- &14233; -- &21655; &13131;
    -- &4587; &23092; &5493; -- &32502; &30317; -- &18741; &12639; &20100; &18525; &19529;
    -- &12619; -- &31183; &25435; -- &7382; &24391; -- &20927; &10946; &24214; &16989; &10335;
    -- &7934; -- &22502; &10906; &31636; &28644; &23998; -- &17422; &20297; &2146; &15355;
    -- &32384; -- &6280; -- &14903; -- &11044; &14469; -- &21498; -- &20198; &23210; -- &17442; -- &23860;
    -- &20257; &7756; &23132]`;;

let avx2_mulcache = define
 `avx2_mulcache f k =
   let r = k DIV 64 in
   let q = k MOD 64 in
   let s = r * 128 + 32 * (q DIV 16) + (q MOD 16) + 16 in
   let t = 64 * r + 2 * (q DIV 32) + 4 * (q MOD 16) in
   (f s * (&17 pow (2 * bitreverse7 t + 1))) rem &3329`;;

let MLKEM_MULCACHE_COMPUTE_CORRECT = prove(
 `!r a zetas (zetas_list:int16 list) x pc.
    aligned 32 r /\
    aligned 32 a /\
    aligned 32 zetas /\
    nonoverlapping (r, 256) (word pc, 323) /\
    nonoverlapping (r, 256) (a, 512) /\
    nonoverlapping (r, 256) (zetas, 1248)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST mlkem_mulcache_compute_tmc) /\
              read RIP s = word pc /\
              C_ARGUMENTS [r; a; zetas] s /\
              wordlist_from_memory(zetas, 624) s = MAP (iword: int -> 16 word) qdata_full /\
              (!i. i < 256 ==> read(memory :> bytes16(word_add a (word(2 * i)))) s = x i))
          (\s. read RIP s = word(pc + 323) /\
               !i. i < 128
                   ==> let zi =
                      read(memory :> bytes16(word_add r (word(2 * i)))) s in
                      (ival zi == avx2_mulcache (ival o x) i) (mod &3329) /\
                      (abs(ival zi) <= &3328))
          (MAYCHANGE [events] ,,
           MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6; ZMM7; ZMM8; ZMM9; ZMM10] ,,
           MAYCHANGE [RIP] ,, MAYCHANGE [RAX] ,,
           MAYCHANGE [memory :> bytes(r, 256)])`,

  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `zetas:int64`; `zetas_list:int16 list`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN

  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN

  REWRITE_TAC [SOME_FLAGS; fst MLKEM_MULCACHE_COMPUTE_TMC_EXEC] THEN

  GHOST_INTRO_TAC `init_ymm0:int256` `read YMM0` THEN

  ENSURES_INIT_TAC "s0" THEN

  MEMORY_256_FROM_16_TAC "a" 16 THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
  CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN STRIP_TAC THEN

  FIRST_X_ASSUM(MP_TAC o CONV_RULE (LAND_CONV WORDLIST_FROM_MEMORY_CONV)) THEN
  REWRITE_TAC[qdata_full; MAP; CONS_11] THEN
  STRIP_TAC THEN

  MP_TAC(end_itlist CONJ (map (fun n -> READ_MEMORY_MERGE_CONV 4
            (subst[mk_small_numeral(32*n),`n:num`]
                  `read (memory :> bytes256(word_add zetas (word n))) s0`))
            (0--38))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
  CONV_TAC(LAND_CONV WORD_REDUCE_CONV) THEN STRIP_TAC THEN

  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_MULCACHE_COMPUTE_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[ntt_montmul_alt])
        (1--59) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (* Reverse restructuring *)
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
  CONV_RULE(SIMD_SIMPLIFY_CONV[]) o
  CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
  check (can (term_match [] `read qqq s:int256 = xxx`) o concl))) THEN

  (* Split quantified post-condition into separate cases *)
  CONV_TAC(EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC [WORD_ADD_0] THEN

  (* Forget all assumptions *)
  POP_ASSUM_LIST (K ALL_TAC) THEN

  (* Split into one congruence goals per index. *)
  (* Split into pairs of congruence and absolute value goals *)
  REPEAT(W(fun (asl,w) ->
  if length(conjuncts w) > 3 then CONJ_TAC else NO_TAC)) THEN

  REWRITE_TAC[avx2_mulcache; avx2_ntt_order] THEN
  CONV_TAC(DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN

  (* Instantiate general congruence and bounds rule for Montgomery multiplication
   * so it matches the current goal, and add as new assumption. *)
  W (MP_TAC o CONGBOUND_RULE o rand o rand o rator o rator o lhand o snd) THEN
  ASM_REWRITE_TAC [o_THM] THEN

  MATCH_MP_TAC MONO_AND THEN (CONJ_TAC THENL [
    (* Correctness *)
    REWRITE_TAC[INVERSE_MOD_CONV `inverse_mod 3329 65536`] THEN
    REWRITE_TAC [GSYM INT_REM_EQ] THEN
    CONV_TAC INT_REM_DOWN_CONV THEN
    STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
    CONV_TAC ((GEN_REWRITE_CONV DEPTH_CONV [BITREVERSE7_CLAUSES])
              THENC (REPEATC (CHANGED_CONV (ONCE_DEPTH_CONV NUM_RED_CONV)))) THEN
    REWRITE_TAC[INT_REM_EQ] THEN
    REWRITE_TAC [REAL_INT_CONGRUENCE; INT_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN REAL_INTEGER_TAC

    ;

    (* Bounds *)
    REWRITE_TAC [INT_ABS_BOUNDS] THEN
    MATCH_MP_TAC(INT_ARITH
      `l':int <= l /\ u <= u'
       ==> l <= x /\ x <= u ==> l' <= x /\ x <= u'`) THEN
    CONV_TAC INT_REDUCE_CONV])
);;

let MLKEM_MULCACHE_COMPUTE_NOIBT_SUBROUTINE_CORRECT  = prove(
 `!r a zetas (zetas_list:int16 list) x pc stackpointer returnaddress.
    aligned 32 r /\
    aligned 32 a /\
    aligned 32 zetas /\
    nonoverlapping (r, 256) (word pc, LENGTH mlkem_mulcache_compute_tmc) /\
    nonoverlapping (r, 256) (a, 512) /\
    nonoverlapping (r, 256) (zetas, 1248) /\
    nonoverlapping (r, 256) (stackpointer, 8)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_mulcache_compute_tmc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [r; a; zetas] s /\
               wordlist_from_memory(zetas, 624) s = MAP (iword: int -> 16 word) qdata_full /\
               (!i. i < 256 ==> read(memory :> bytes16(word_add a (word(2 * i)))) s = x i))
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               !i. i < 128
                   ==> let zi =
                      read(memory :> bytes16(word_add r (word(2 * i)))) s in
                      (ival zi == avx2_mulcache (ival o x) i) (mod &3329) /\
                      (abs(ival zi) <= &3328))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(r, 256)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_mulcache_compute_tmc (CONV_RULE TWEAK_CONV MLKEM_MULCACHE_COMPUTE_CORRECT));;

let MLKEM_MULCACHE_COMPUTE_SUBROUTINE_CORRECT = prove(
 `!r a zetas (zetas_list:int16 list) x pc stackpointer returnaddress.
    aligned 32 r /\
    aligned 32 a /\
    aligned 32 zetas /\
    nonoverlapping (r, 256) (word pc, LENGTH mlkem_mulcache_compute_mc) /\
    nonoverlapping (r, 256) (a, 512) /\
    nonoverlapping (r, 256) (zetas, 1248) /\
    nonoverlapping (r, 256) (stackpointer, 8)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_mulcache_compute_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [r; a; zetas] s /\
               wordlist_from_memory(zetas, 624) s = MAP (iword: int -> 16 word) qdata_full /\
               (!i. i < 256 ==> read(memory :> bytes16(word_add a (word(2 * i)))) s = x i))
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               !i. i < 128
                   ==> let zi =
                      read(memory :> bytes16(word_add r (word(2 * i)))) s in
                      (ival zi == avx2_mulcache (ival o x) i) (mod &3329) /\
                      (abs(ival zi) <= &3328))
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(r, 256)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
  (CONV_RULE TWEAK_CONV MLKEM_MULCACHE_COMPUTE_NOIBT_SUBROUTINE_CORRECT)));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let mlkem_mulcache_compute_windows_mc = define_from_elf
    "mlkem_mulcache_compute_windows_mc" "x86/mlkem/mlkem_mulcache_compute.obj";;

let mlkem_mulcache_compute_windows_tmc = define_trimmed
    "mlkem_mulcache_compute_windows_tmc" mlkem_mulcache_compute_windows_mc;;

let MLKEM_MULCACHE_COMPUTE_WINDOWS_TMC_EXEC = X86_MK_EXEC_RULE mlkem_mulcache_compute_windows_tmc;;

let MLKEM_MULCACHE_COMPUTE_NOIBT_WINDOWS_SUBROUTINE_CORRECT  = prove(
 `!r a zetas (zetas_list:int16 list) x pc stackpointer returnaddress.
    aligned 32 r /\
    aligned 32 a /\
    aligned 32 zetas /\
    nonoverlapping (r, 256) (word pc, LENGTH mlkem_mulcache_compute_windows_tmc) /\
    nonoverlapping (r, 256) (a, 512) /\
    nonoverlapping (r, 256) (zetas, 1248) /\
    nonoverlapping (word_sub stackpointer (word 104), 112)
                   (word pc, LENGTH mlkem_mulcache_compute_windows_tmc) /\
    nonoverlapping (word_sub stackpointer (word 104), 112) (a, 512) /\
    nonoverlapping (word_sub stackpointer (word 104), 112) (zetas, 1248) /\
    nonoverlapping (word_sub stackpointer (word 104), 112) (r, 256)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_mulcache_compute_windows_tmc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               WINDOWS_C_ARGUMENTS [r; a; zetas] s /\
               wordlist_from_memory(zetas, 624) s = MAP (iword: int -> 16 word) qdata_full /\
               (!i. i < 256 ==> read(memory :> bytes16(word_add a (word(2 * i)))) s = x i))
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               !i. i < 128
                   ==> let zi =
                      read(memory :> bytes16(word_add r (word(2 * i)))) s in
                      (ival zi == avx2_mulcache (ival o x) i) (mod &3329) /\
                      (abs(ival zi) <= &3328))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 104), 104)] ,,
           MAYCHANGE [memory :> bytes(r, 256)])`,

(*** Expand away the wordlist_from_memory ***)
  CONV_TAC(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV) THEN

(*** Handle initial quantifiers and set up stack offset management ***)
  REPLICATE_TAC 6 GEN_TAC THEN
  WORD_FORALL_OFFSET_TAC 104 THEN REPEAT GEN_TAC THEN

(*** Set up basic Windows ABI framework and rewrite with Windows calling convention ***)
  REWRITE_TAC[fst MLKEM_MULCACHE_COMPUTE_WINDOWS_TMC_EXEC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[WINDOWS_C_ARGUMENTS] THEN
  REWRITE_TAC[WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN

(*** Set up register preservation for Windows ABI compliance
 *** Windows ABI requires preserving RDI, RSI, and XMM6-XMM15 across function calls ***)
  ENSURES_PRESERVED_TAC "rdi_init" `RDI` THEN
  ENSURES_PRESERVED_TAC "rsi_init" `RSI` THEN
  ENSURES_PRESERVED_TAC "init_xmm6" `ZMM6 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm7" `ZMM7 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm8" `ZMM8 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm9" `ZMM9 :> bottomhalf :> bottomhalf` THEN
  ENSURES_PRESERVED_TAC "init_xmm10" `ZMM10 :> bottomhalf :> bottomhalf` THEN

(*** Handle the ZMM/YMM register notation conversion ***)
  REWRITE_TAC[READ_ZMM_BOTTOM_QUARTER'] THEN
  REWRITE_TAC(map GSYM
    [YMM6;YMM7;YMM8;YMM9;YMM10]) THEN

(*** Introduce ghost variables for initial XMM register values
 *** These will track the register states for restoration in the epilogue ***)
  GHOST_INTRO_TAC `init_ymm6:int256` `read YMM6` THEN
  GHOST_INTRO_TAC `init_ymm7:int256` `read YMM7` THEN
  GHOST_INTRO_TAC `init_ymm8:int256` `read YMM8` THEN
  GHOST_INTRO_TAC `init_ymm9:int256` `read YMM9` THEN
  GHOST_INTRO_TAC `init_ymm10:int256` `read YMM10` THEN

(*** Globalize preconditions and substitute preserved register values ***)
  GLOBALIZE_PRECONDITION_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN

(*** Initialize execution and simulate the prologue (register saves)
 *** Steps 1-15 cover the Windows prologue that saves XMM registers to stack ***)
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_MULCACHE_COMPUTE_WINDOWS_TMC_EXEC (1--12) THEN

(*** Apply the main Unix correctness theorem to the core computation ***)
  MP_TAC(SPECL [`r:int64`; `a:int64`; `zetas:int64`; `zetas_list:int16 list`; `x:num->int16`; `pc + 55`]
    MLKEM_MULCACHE_COMPUTE_CORRECT) THEN
  ASM_REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
  ANTS_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN

(*** Expand wordlist_from_memory again ****)
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV)) THEN

(*** Expand MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ****)
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN

(*** Execute the main computation as a single big step
 *** This handles the core algorithm while preserving the register save/restore wrapper ***)
  X86_BIGSTEP_TAC MLKEM_MULCACHE_COMPUTE_WINDOWS_TMC_EXEC "s13" THENL
   [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP
     (BYTES_LOADED_SUBPROGRAM_RULE mlkem_mulcache_compute_windows_tmc
     (REWRITE_RULE[BUTLAST_CLAUSES]
      (AP_TERM `BUTLAST:byte list->byte list` mlkem_mulcache_compute_tmc))
     55));
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV))] THEN

(*** Capture the final YMM register states after main computation ***)
  MAP_EVERY ABBREV_TAC
   [`ymm6_epilog = read YMM6 s13`;
    `ymm7_epilog = read YMM7 s13`;
    `ymm8_epilog = read YMM8 s13`;
    `ymm9_epilog = read YMM9 s13`;
    `ymm10_epilog = read YMM10 s13`] THEN

(*** Simulate the epilogue (register restoration and return)
 *** Steps 17-30 cover the Windows epilogue that restores XMM registers from stack ***)
  X86_STEPS_TAC MLKEM_MULCACHE_COMPUTE_WINDOWS_TMC_EXEC (14--23) THEN

(*** Handle the MAYCHANGE clauses for ZMM register components ***)
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_ZMM_QUARTER]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_YMM_SSE_QUARTER]) THEN

(*** Finalize the proof by establishing the final state conditions ***)
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

let MLKEM_MULCACHE_COMPUTE_WINDOWS_SUBROUTINE_CORRECT  = prove(
 `!r a zetas (zetas_list:int16 list) x pc stackpointer returnaddress.
    aligned 32 r /\
    aligned 32 a /\
    aligned 32 zetas /\
    nonoverlapping (r, 256) (word pc, LENGTH mlkem_mulcache_compute_windows_mc) /\
    nonoverlapping (r, 256) (a, 512) /\
    nonoverlapping (r, 256) (zetas, 1248) /\
    nonoverlapping (word_sub stackpointer (word 104), 112)
                   (word pc, LENGTH mlkem_mulcache_compute_windows_mc) /\
    nonoverlapping (word_sub stackpointer (word 104), 112) (a, 512) /\
    nonoverlapping (word_sub stackpointer (word 104), 112) (zetas, 1248) /\
    nonoverlapping (word_sub stackpointer (word 104), 112) (r, 256)
    ==> ensures x86
          (\s. bytes_loaded s (word pc) mlkem_mulcache_compute_windows_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               WINDOWS_C_ARGUMENTS [r; a; zetas] s /\
               wordlist_from_memory(zetas, 624) s = MAP (iword: int -> 16 word) qdata_full /\
               (!i. i < 256 ==> read(memory :> bytes16(word_add a (word(2 * i)))) s = x i))
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               !i. i < 128
                   ==> let zi =
                      read(memory :> bytes16(word_add r (word(2 * i)))) s in
                      (ival zi == avx2_mulcache (ival o x) i) (mod &3329) /\
                      (abs(ival zi) <= &3328))
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(word_sub stackpointer (word 104), 104)] ,,
           MAYCHANGE [memory :> bytes(r, 256)])`,
  let TWEAK_CONV = ONCE_DEPTH_CONV WORDLIST_FROM_MEMORY_CONV in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
  (CONV_RULE TWEAK_CONV MLKEM_MULCACHE_COMPUTE_NOIBT_WINDOWS_SUBROUTINE_CORRECT)));;
