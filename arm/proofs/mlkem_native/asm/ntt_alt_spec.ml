(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* The contracts of mlkem_ntt_alt that the proofs of the callers in the    *)
(* image of the ML-KEM API in assembly use: the correctness theorem of     *)
(* arm/proofs/mlkem_ntt_alt.ml, and the safety theorem of that file with   *)
(* the frame of the correctness theorem. They are stated about the code    *)
(* of that file, mlkem_ntt_alt_mc, which is also in the image, where       *)
(* ARM_SUBROUTINE_SIM_TAC uses them for it (see                            *)
(* arm/mlkem_native/asm/README.md). The proof file loads the standalone    *)
(* proof, which proves the first, and makes the second from its safety     *)
(* theorem.                                                                *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "common/mlkem_mldsa.ml";;
needs "common/int_linear.ml";;

let mlkem_ntt_alt_mc = define_from_elf
 "mlkem_ntt_alt_mc" "arm/mlkem/mlkem_ntt_alt.o";;

let ntt_zetas_layer01234 = define
 `ntt_zetas_layer01234:int list =
   [-- &1600; -- &15749; -- &749; -- &7373; -- &40; -- &394; -- &687; -- &6762;
    &630; &6201; -- &1432; -- &14095; &848; &8347; &0; &0; &1062; &10453; &296;
    &2914; -- &882; -- &8682; &0; &0; -- &1410; -- &13879; &1339; &13180;
    &1476;
    &14529; &0; &0; &193; &1900; -- &283; -- &2786; &56; &551; &0; &0; &797;
    &7845; -- &1089; -- &10719; &1333; &13121; &0; &0; -- &543; -- &5345;
    &1426; &14036; -- &1235; -- &12156; &0; &0; -- &69; -- &679; &535; &5266;
    -- &447; -- &4400; &0; &0; &569; &5601; -- &936; -- &9213; -- &450;
    -- &4429; &0; &0; -- &1583; -- &15582; -- &1355; -- &13338; &821;
    &8081; &0; &0]`;;

let ntt_zetas_layer56 = define
`ntt_zetas_layer56:int list =
  [&289; &289; &331; &331; -- &76; -- &76; -- &1573; -- &1573; &2845;
   &2845; &3258; &3258; -- &748; -- &748; -- &15483; -- &15483; &17; &17;
   &583; &583; &1637; &1637; -- &1041; -- &1041; &167; &167; &5739;
   &5739; &16113; &16113; -- &10247; -- &10247; -- &568; -- &568;
   -- &680; -- &680; &723; &723; &1100; &1100; -- &5591; -- &5591; -- &6693;
   -- &6693; &7117; &7117; &10828; &10828; &1197; &1197; -- &1025;
   -- &1025; -- &1052; -- &1052; -- &1274; -- &1274; &11782; &11782;
   -- &10089; -- &10089; -- &10355; -- &10355; -- &12540; -- &12540; &1409;
   &1409; -- &48; -- &48; &756; &756; -- &314; -- &314; &13869; &13869;
   -- &472; -- &472; &7441; &7441; -- &3091; -- &3091; -- &667; -- &667;
   &233; &233; -- &1173; -- &1173; -- &279; -- &279; -- &6565; -- &6565;
   &2293; &2293; -- &11546; -- &11546; -- &2746; -- &2746; &650; &650;
   -- &1352; -- &1352; -- &816; -- &816; &632; &632; &6398; &6398;
   -- &13308; -- &13308; -- &8032; -- &8032; &6221; &6221; -- &1626;
   -- &1626; -- &540; -- &540; -- &1482; -- &1482; &1461; &1461; -- &16005;
   -- &16005; -- &5315; -- &5315; -- &14588; -- &14588; &14381; &14381;
   &1651; &1651; -- &1540; -- &1540; &952; &952; -- &642; -- &642;
   &16251; &16251; -- &15159; -- &15159; &9371; &9371; -- &6319;
   -- &6319; -- &464; -- &464; &33; &33; &1320; &1320; -- &1414; -- &1414;
   -- &4567; -- &4567; &325; &325; &12993; &12993; -- &13918; -- &13918;
   &939; &939; -- &892; -- &892; &733; &733; &268; &268; &9243; &9243;
   -- &8780; -- &8780; &7215; &7215; &2638; &2638; -- &1021; -- &1021;
   -- &941; -- &941; -- &992; -- &992; &641; &641; -- &10050; -- &10050;
   -- &9262; -- &9262; -- &9764; -- &9764; &6309; &6309; -- &1010; -- &1010;
   &1435; &1435; &807; &807; &452; &452; -- &9942; -- &9942; &14125;
   &14125; &7943; &7943; &4449; &4449; &1584; &1584; -- &1292; -- &1292;
   &375; &375; -- &1239; -- &1239; &15592; &15592; -- &12717; -- &12717;
   &3691; &3691; -- &12196; -- &12196; -- &1031; -- &1031; -- &109;
   -- &109; -- &780; -- &780; &1645; &1645; -- &10148; -- &10148; -- &1073;
   -- &1073; -- &7678; -- &7678; &16192; &16192; &1438; &1438; -- &461;
   -- &461; &1534; &1534; -- &927; -- &927; &14155; &14155; -- &4538;
   -- &4538; &15099; &15099; -- &9125; -- &9125; &1063; &1063; -- &556;
   -- &556; -- &1230; -- &1230; -- &863; -- &863; &10463; &10463; -- &5473;
   -- &5473; -- &12107; -- &12107; -- &8495; -- &8495; &319; &319; &757;
   &757; &561; &561; -- &735; -- &735; &3140; &3140; &7451; &7451; &5522;
   &5522; -- &7235; -- &7235; -- &682; -- &682; -- &712; -- &712; &1481;
   &1481; &648; &648; -- &6713; -- &6713; -- &7008; -- &7008; &14578;
   &14578; &6378; &6378; -- &525; -- &525; &403; &403; &1143; &1143;
   -- &554; -- &554; -- &5168; -- &5168; &3967; &3967; &11251; &11251;
   -- &5453; -- &5453; &1092; &1092; &1026; &1026; -- &1179; -- &1179; &886;
   &886; &10749; &10749; &10099; &10099; -- &11605; -- &11605; &8721;
   &8721; -- &855; -- &855; -- &219; -- &219; &1227; &1227; &910; &910;
   -- &8416; -- &8416; -- &2156; -- &2156; &12078; &12078; &8957; &8957;
   -- &1607; -- &1607; -- &1455; -- &1455; -- &1219; -- &1219; &885;
   &885; -- &15818; -- &15818; -- &14322; -- &14322; -- &11999;
   -- &11999; &8711; &8711; &1212; &1212; &1029; &1029; -- &394; -- &394;
   -- &1175; -- &1175; &11930; &11930; &10129; &10129; -- &3878; -- &3878;
   -- &11566; -- &11566]`;;

let MLKEM_NTT_ALT_SUBROUTINE_CORRECT_STMT =
 `!a z_01234 z_56 zetas_01234 zetas_56 x pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
       [(a,512); (word_sub stackpointer (word 64),64)]
       [(word pc,0x754); (z_01234,160); (z_56,768)] /\
      nonoverlapping (a,512) (word_sub stackpointer (word 64),64)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_ntt_alt_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a; z_01234; z_56] s /\
                wordlist_from_memory(z_01234,80) s:int16 list = zetas_01234 /\
                wordlist_from_memory(z_56,384) s:int16 list = zetas_56 /\
                !i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i)
           (\s. read PC s = returnaddress /\
                (zetas_01234 = MAP iword ntt_zetas_layer01234 /\
                 zetas_56 = MAP iword ntt_zetas_layer56 /\
                 (!i. i < 256 ==> abs(ival(x i)) <= &8191)
                 ==> !i. i < 256
                         ==> let zi =
                        read(memory :> bytes16(word_add a (word(2 * i)))) s in
                        (ival zi == forward_ntt (ival o x) i) (mod &3329) /\
                        abs(ival zi) <= &23594))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(a,512);
                       memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLKEM_NTT_ALT_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NTT_ALT_SUBROUTINE_CORRECT_STMT;;

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NTT_ALT_SUBROUTINE_SAFE_FRAMED_STMT =
 `exists f_events.
       forall e a z_01234 z_56 pc stackpointer returnaddress.
           aligned 16 stackpointer /\
           ALLPAIRS nonoverlapping
           [a,512; word_sub stackpointer (word 64),64]
           [word pc,0x754; z_01234,160; z_56,768] /\
           nonoverlapping (a,512) (word_sub stackpointer (word 64),64)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc) mlkem_ntt_alt_mc /\
                    read PC s = word pc /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; z_01234; z_56] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 =
                        f_events z_01234 z_56 a pc
                        (word_sub stackpointer (word 64))
                        returnaddress /\
                        memaccess_inbounds e2
                        [a,512; z_01234,160; z_56,768;
                         word_sub stackpointer (word 64),64]
                        [a,512; word_sub stackpointer (word 64),64])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(a,512);
                       memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLKEM_NTT_ALT_SUBROUTINE_SAFE_FRAMED =
  assume_spec MLKEM_NTT_ALT_SUBROUTINE_SAFE_FRAMED_STMT;;
