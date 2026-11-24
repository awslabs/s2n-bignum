(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* The contracts of mlkem_intt_alt that the proofs of the callers in the   *)
(* image of the ML-KEM API in assembly use: the correctness theorem of     *)
(* arm/proofs/mlkem_intt_alt.ml, and the safety theorem of that file with  *)
(* the frame of the correctness theorem. They are stated about the code    *)
(* of that file, mlkem_intt_alt_mc, which is also in the image, where      *)
(* ARM_SUBROUTINE_SIM_TAC uses them for it (see                            *)
(* arm/mlkem_native/asm/README.md). The proof file loads the standalone    *)
(* proof, which proves the first, and makes the second from its safety     *)
(* theorem.                                                                *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "common/mlkem_mldsa.ml";;
needs "common/int_linear.ml";;

let mlkem_intt_alt_mc = define_from_elf
 "mlkem_intt_alt_mc" "arm/mlkem/mlkem_intt_alt.o";;

let intt_zetas_layer01234 = define
 `intt_zetas_layer01234:int list =
   [&1583; &15582; -- &821; -- &8081; &1355; &13338; &0; &0; -- &569; -- &5601;
    &450; &4429; &936; &9213; &0; &0; &69; &679; &447; &4400; -- &535;
    -- &5266; &0; &0; &543; &5345; &1235; &12156; -- &1426; -- &14036; &0;
    &0; -- &797; -- &7845; -- &1333; -- &13121; &1089; &10719; &0; &0;
    -- &193; -- &1900; -- &56; -- &551; &283; &2786; &0; &0; &1410; &13879;
    -- &1476; -- &14529; -- &1339; -- &13180; &0; &0; -- &1062; -- &10453;
    &882; &8682; -- &296; -- &2914; &0; &0; &1600; &15749; &40; &394;
    &749; &7373; -- &848; -- &8347; &1432; &14095; -- &630; -- &6201;
    &687; &6762; &0; &0]`;;

let intt_zetas_layer56 = define
 `intt_zetas_layer56:int list =
   [-- &910; -- &910; -- &1227; -- &1227; &219; &219; &855; &855; -- &8957;
    -- &8957; -- &12078; -- &12078; &2156; &2156; &8416; &8416; &1175;
    &1175; &394; &394; -- &1029; -- &1029; -- &1212; -- &1212; &11566;
    &11566; &3878; &3878; -- &10129; -- &10129; -- &11930; -- &11930;
    -- &885; -- &885; &1219; &1219; &1455; &1455; &1607; &1607; -- &8711;
    -- &8711; &11999; &11999; &14322; &14322; &15818; &15818; -- &648;
    -- &648; -- &1481; -- &1481; &712; &712; &682; &682; -- &6378; -- &6378;
    -- &14578; -- &14578; &7008; &7008; &6713; &6713; -- &886; -- &886;
    &1179; &1179; -- &1026; -- &1026; -- &1092; -- &1092; -- &8721;
    -- &8721; &11605; &11605; -- &10099; -- &10099; -- &10749; -- &10749;
    &554; &554; -- &1143; -- &1143; -- &403; -- &403; &525; &525; &5453;
    &5453; -- &11251; -- &11251; -- &3967; -- &3967; &5168; &5168; &927;
    &927; -- &1534; -- &1534; &461; &461; -- &1438; -- &1438; &9125;
    &9125; -- &15099; -- &15099; &4538; &4538; -- &14155; -- &14155; &735;
    &735; -- &561; -- &561; -- &757; -- &757; -- &319; -- &319; &7235;
    &7235; -- &5522; -- &5522; -- &7451; -- &7451; -- &3140; -- &3140;
    &863; &863; &1230; &1230; &556; &556; -- &1063; -- &1063; &8495;
    &8495; &12107; &12107; &5473; &5473; -- &10463; -- &10463; -- &452;
    -- &452; -- &807; -- &807; -- &1435; -- &1435; &1010; &1010; -- &4449;
    -- &4449; -- &7943; -- &7943; -- &14125; -- &14125; &9942; &9942;
    -- &1645; -- &1645; &780; &780; &109; &109; &1031; &1031; -- &16192;
    -- &16192; &7678; &7678; &1073; &1073; &10148; &10148; &1239; &1239;
    -- &375; -- &375; &1292; &1292; -- &1584; -- &1584; &12196; &12196;
    -- &3691; -- &3691; &12717; &12717; -- &15592; -- &15592; &1414; &1414;
    -- &1320; -- &1320; -- &33; -- &33; &464; &464; &13918; &13918;
    -- &12993; -- &12993; -- &325; -- &325; &4567; &4567; -- &641; -- &641;
    &992; &992; &941; &941; &1021; &1021; -- &6309; -- &6309; &9764;
    &9764; &9262; &9262; &10050; &10050; -- &268; -- &268; -- &733;
    -- &733; &892; &892; -- &939; -- &939; -- &2638; -- &2638; -- &7215;
    -- &7215; &8780; &8780; -- &9243; -- &9243; -- &632; -- &632; &816; &816;
    &1352; &1352; -- &650; -- &650; -- &6221; -- &6221; &8032; &8032;
    &13308; &13308; -- &6398; -- &6398; &642; &642; -- &952; -- &952;
    &1540; &1540; -- &1651; -- &1651; &6319; &6319; -- &9371; -- &9371;
    &15159; &15159; -- &16251; -- &16251; -- &1461; -- &1461; &1482;
    &1482; &540; &540; &1626; &1626; -- &14381; -- &14381; &14588; &14588;
    &5315; &5315; &16005; &16005; &1274; &1274; &1052; &1052; &1025;
    &1025; -- &1197; -- &1197; &12540; &12540; &10355; &10355; &10089;
    &10089; -- &11782; -- &11782; &279; &279; &1173; &1173; -- &233;
    -- &233; &667; &667; &2746; &2746; &11546; &11546; -- &2293; -- &2293;
    &6565; &6565; &314; &314; -- &756; -- &756; &48; &48; -- &1409;
    -- &1409; &3091; &3091; -- &7441; -- &7441; &472; &472; -- &13869;
    -- &13869; &1573; &1573; &76; &76; -- &331; -- &331; -- &289; -- &289;
    &15483; &15483; &748; &748; -- &3258; -- &3258; -- &2845; -- &2845;
    -- &1100; -- &1100; -- &723; -- &723; &680; &680; &568; &568; -- &10828;
    -- &10828; -- &7117; -- &7117; &6693; &6693; &5591; &5591; &1041;
    &1041; -- &1637; -- &1637; -- &583; -- &583; -- &17; -- &17; &10247;
    &10247; -- &16113; -- &16113; -- &5739; -- &5739; -- &167; -- &167]`;;

let MLKEM_INTT_ALT_SUBROUTINE_CORRECT_STMT =
 `!a z_01234 z_56 zetas_01234 zetas_56 x pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALLPAIRS nonoverlapping
       [(a,512); (word_sub stackpointer (word 64),64)]
       [(word pc,0x85c); (z_01234,160); (z_56,768)] /\
      nonoverlapping (a,512) (word_sub stackpointer (word 64),64)
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_intt_alt_mc /\
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
                (zetas_01234 = MAP iword intt_zetas_layer01234 /\
                 zetas_56 = MAP iword intt_zetas_layer56
                 ==> !i. i < 256
                         ==> let zi =
                        read(memory :> bytes16(word_add a (word(2 * i)))) s in
                        (ival zi == inverse_ntt (ival o x) i) (mod &3329) /\
                         abs(ival zi) <= &26624))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(a,512);
                       memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLKEM_INTT_ALT_SUBROUTINE_CORRECT =
  assume_spec MLKEM_INTT_ALT_SUBROUTINE_CORRECT_STMT;;

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_INTT_ALT_SUBROUTINE_SAFE_FRAMED_STMT =
 `exists f_events.
       forall e a z_01234 z_56 pc stackpointer returnaddress.
           aligned 16 stackpointer /\
           ALLPAIRS nonoverlapping
           [a,512; word_sub stackpointer (word 64),64]
           [word pc,0x85c; z_01234,160; z_56,768] /\
           nonoverlapping (a,512) (word_sub stackpointer (word 64),64)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc) mlkem_intt_alt_mc /\
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

let MLKEM_INTT_ALT_SUBROUTINE_SAFE_FRAMED =
  assume_spec MLKEM_INTT_ALT_SUBROUTINE_SAFE_FRAMED_STMT;;
