(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* The contracts of mlkem_mulcache_compute that the proofs of the callers  *)
(* in the image of the ML-KEM API in assembly use: the correctness         *)
(* theorem of arm/proofs/mlkem_mulcache_compute.ml, and the safety         *)
(* theorem of that file with the frame of the correctness theorem. They    *)
(* are stated about the code of that file, mlkem_mulcache_compute_mc,      *)
(* which is also in the image, where ARM_SUBROUTINE_SIM_TAC uses them for  *)
(* it (see arm/mlkem_native/asm/README.md). The proof file loads the       *)
(* standalone proof, which proves the first, and makes the second from     *)
(* its safety theorem.                                                     *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "common/mlkem_mldsa.ml";;

let mlkem_mulcache_compute_mc = define_from_elf
 "mlkem_mulcache_compute_mc" "arm/mlkem/mlkem_mulcache_compute.o";;

let mulcache_zetas = define
   `mulcache_zetas:int list =
     [
       &17; -- &17; -- &568; &568; &583; -- &583; -- &680; &680;
       &1637; -- &1637; &723; -- &723; -- &1041; &1041; &1100; -- &1100;
       &1409; -- &1409; -- &667; &667; -- &48; &48; &233; -- &233;
       &756; -- &756; -- &1173; &1173; -- &314; &314; -- &279; &279;
       -- &1626; &1626; &1651; -- &1651; -- &540; &540; -- &1540; &1540;
       -- &1482; &1482; &952; -- &952; &1461; -- &1461; -- &642; &642;
       &939; -- &939; -- &1021; &1021; -- &892; &892; -- &941; &941;
       &733; -- &733; -- &992; &992; &268; -- &268; &641; -- &641;
       &1584; -- &1584; -- &1031; &1031; -- &1292; &1292; -- &109; &109;
       &375; -- &375; -- &780; &780; -- &1239; &1239; &1645; -- &1645;
       &1063; -- &1063; &319; -- &319; -- &556; &556; &757; -- &757;
       -- &1230; &1230; &561; -- &561; -- &863; &863; -- &735; &735;
       -- &525; &525; &1092; -- &1092; &403; -- &403; &1026; -- &1026;
       &1143; -- &1143; -- &1179; &1179; -- &554; &554; &886; -- &886;
       -- &1607; &1607; &1212; -- &1212; -- &1455; &1455; &1029; -- &1029;
       -- &1219; &1219; -- &394; &394; &885; -- &885; -- &1175; &1175
     ]`;;

let mulcache_zetas_twisted = define
  `mulcache_zetas_twisted: int list =
  [
   &167; -- &167; -- &5591; &5591; &5739; -- &5739; -- &6693; &6693;
   &16113; -- &16113; &7117; -- &7117; -- &10247; &10247; &10828; -- &10828;
   &13869; -- &13869; -- &6565; &6565; -- &472; &472; &2293; -- &2293;
   &7441; -- &7441; -- &11546; &11546; -- &3091; &3091; -- &2746; &2746;
   -- &16005; &16005; &16251; -- &16251; -- &5315; &5315; -- &15159; &15159;
   -- &14588; &14588; &9371; -- &9371; &14381; -- &14381; -- &6319; &6319;
   &9243; -- &9243; -- &10050; &10050; -- &8780; &8780; -- &9262; &9262;
   &7215; -- &7215; -- &9764; &9764; &2638; -- &2638; &6309; -- &6309;
   &15592; -- &15592; -- &10148; &10148; -- &12717; &12717; -- &1073; &1073;
   &3691; -- &3691; -- &7678; &7678; -- &12196; &12196; &16192; -- &16192;
   &10463; -- &10463; &3140; -- &3140; -- &5473; &5473; &7451; -- &7451;
   -- &12107; &12107; &5522; -- &5522; -- &8495; &8495; -- &7235; &7235;
   -- &5168; &5168; &10749; -- &10749; &3967; -- &3967; &10099; -- &10099;
   &11251; -- &11251; -- &11605; &11605; -- &5453; &5453; &8721; -- &8721;
   -- &15818; &15818; &11930; -- &11930; -- &14322; &14322; &10129; -- &10129;
   -- &11999; &11999; -- &3878; &3878; &8711; -- &8711; -- &11566; &11566
  ]`;;

let have_mulcache_zetas = define
 `have_mulcache_zetas zetas zetas_twisted s <=>
     (!i. i < 128
          ==> read(memory :> bytes16(word_add zetas (word (2*i)))) s =
              iword (EL i mulcache_zetas)) /\
     (!i. i < 128
          ==> read(memory :> bytes16(word_add zetas_twisted (word (2*i)))) s =
             iword (EL i mulcache_zetas_twisted))`;;

let MLKEM_MULCACHE_COMPUTE_SUBROUTINE_CORRECT_STMT =
 `!dst src zetas zetas_twisted x pc returnaddress.
    ALL (nonoverlapping (dst, 256))
        [(word pc, LENGTH mlkem_mulcache_compute_mc);
         (src, 512); (zetas, 256); (zetas_twisted, 256)]
    ==>
    ensures arm
      (\s. // Assert that poly_mulcache_compute is loaded at PC
           aligned_bytes_loaded s (word pc) mlkem_mulcache_compute_mc /\
           read PC s = word pc  /\
           // Remember LR as point-to-stop
           read X30 s = returnaddress /\
           C_ARGUMENTS [dst; src; zetas; zetas_twisted] s  /\
           // Give name to 16-bit coefficients stored at src to be
           // able to refer to them in the post-condition
           (!i. i < 256
                ==> read(memory :> bytes16(word_add src (word (2 * i)))) s =
                    x i) /\
           // Assert that zetas are correct
           have_mulcache_zetas zetas zetas_twisted s)
      (\s. // We have reached the LR
           read PC s = returnaddress /\
           // Odd coefficients have been multiplied with
           // respective root of unity
           !i. i < 128
               ==> let z_i = read(memory :> bytes16
                                (word_add dst (word (2 * i)))) s in
                   (ival z_i == (mulcache (ival o x)) i) (mod &3329) /\
                   (abs(ival z_i) <= &3328))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(dst, 256)])`;;

let MLKEM_MULCACHE_COMPUTE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_MULCACHE_COMPUTE_SUBROUTINE_CORRECT_STMT;;

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_MULCACHE_COMPUTE_SUBROUTINE_SAFE_FRAMED_STMT =
 `exists f_events.
       forall e dst src zetas zetas_twisted pc returnaddress.
           ALL (nonoverlapping (dst,256))
           [word pc,LENGTH mlkem_mulcache_compute_mc; src,512; zetas,256;
            zetas_twisted,256]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_mulcache_compute_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [dst; src; zetas; zetas_twisted] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 =
                        f_events src zetas zetas_twisted dst pc returnaddress /\
                        memaccess_inbounds e2
                        [src,512; zetas,256; zetas_twisted,256; dst,256]
                        [dst,256])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(dst, 256)])`;;

let MLKEM_MULCACHE_COMPUTE_SUBROUTINE_SAFE_FRAMED =
  assume_spec MLKEM_MULCACHE_COMPUTE_SUBROUTINE_SAFE_FRAMED_STMT;;
