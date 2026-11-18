(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Squeezing whole blocks from four SHAKE128 states. This is the code for    *)
(* mlkem_shake128x4_squeezeblocks from mlkem-native's portable C             *)
(* implementation compiled by gcc 12 with -Os (see mlkem_native/README.md),  *)
(* which calls mlk_keccak_squeezeblocks_x4 with the rate 168 of SHAKE128, as *)
(* a tail call. It is verified in the whole image (see libmlkem.ml), using   *)
(* the theorems for mlk_keccak_squeezeblocks_x4 in the image.                *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/keccak_squeezeblocks_x4_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_Os/libmlkem.ml";;

(*** The code in the image:

    mlkem_shake128x4_squeezeblocks:
       +0x0: mov     w6, #0xa8
       +0x4: b       <mlk_keccak_squeezeblocks_x4>
 ***)

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_Os_mc
   [layout_range "mlkem_shake128x4_squeezeblocks"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_shake128_squeezeblocks, for each of the   *)
(* four states S, block i of its output, as a number, is the first 168       *)
(* bytes of keccak_squeeze (i + 1) S, and the state becomes                  *)
(* keccak_squeeze nblocks S.                                                 *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!out0 out1 out2 out3 nblocks st
    (S0:1600 word) (S1:1600 word) (S2:1600 word) (S3:1600 word)
    pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(out0,168 * nblocks); (out1,168 * nblocks); (out2,168 * nblocks);
          (out3,168 * nblocks); (st,800);
          (word_sub stackpointer (word 320),320)] /\
        ALL (nonoverlapping (word pc,libmlkem_size))
         [(out0,168 * nblocks); (out1,168 * nblocks); (out2,168 * nblocks);
          (out3,168 * nblocks); (st,800);
          (word_sub stackpointer (word 320),320)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_Os_mc /\
                  read PC s = word (pc + mlkem_shake128x4_squeezeblocks) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out0; out1; out2; out3; word nblocks; st] s /\
                  read (memory :> wbytes st) s = S0 /\
                  read (memory :> wbytes (word_add st (word 200))) s = S1 /\
                  read (memory :> wbytes (word_add st (word 400))) s = S2 /\
                  read (memory :> wbytes (word_add st (word 600))) s = S3)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out0,168 * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * 168 * i) *
                        val(keccak_squeeze (i + 1) S0) MOD 2 EXP (8 * 168)) /\
                  read (memory :> bytes(out1,168 * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * 168 * i) *
                        val(keccak_squeeze (i + 1) S1) MOD 2 EXP (8 * 168)) /\
                  read (memory :> bytes(out2,168 * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * 168 * i) *
                        val(keccak_squeeze (i + 1) S2) MOD 2 EXP (8 * 168)) /\
                  read (memory :> bytes(out3,168 * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * 168 * i) *
                        val(keccak_squeeze (i + 1) S3) MOD 2 EXP (8 * 168)) /\
                  read (memory :> wbytes st) s = keccak_squeeze nblocks S0 /\
                  read (memory :> wbytes (word_add st (word 200))) s =
                  keccak_squeeze nblocks S1 /\
                  read (memory :> wbytes (word_add st (word 400))) s =
                  keccak_squeeze nblocks S2 /\
                  read (memory :> wbytes (word_add st (word 600))) s =
                  keccak_squeeze nblocks S3)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out0,168 * nblocks);
                memory :> bytes(out1,168 * nblocks);
                memory :> bytes(out2,168 * nblocks);
                memory :> bytes(out3,168 * nblocks);
                memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 320),320)])`;;

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e out0 out1 out2 out3 nblocks st pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [out0,168 * nblocks; out1,168 * nblocks; out2,168 * nblocks;
         out3,168 * nblocks; st,800; word_sub stackpointer (word 320),320] /\
       ALL (nonoverlapping (word pc,libmlkem_size))
        [out0,168 * nblocks; out1,168 * nblocks; out2,168 * nblocks;
         out3,168 * nblocks; st,800; word_sub stackpointer (word 320),320]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_Os_mc /\
                 read PC s = word (pc + mlkem_shake128x4_squeezeblocks) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [out0; out1; out2; out3; word nblocks; st] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events out0 out1 out2 out3 nblocks st pc
                           (word_sub stackpointer (word 320)) returnaddress /\
                    memaccess_inbounds e2
                     [out0,168 * nblocks; out1,168 * nblocks;
                      out2,168 * nblocks; out3,168 * nblocks; st,800;
                      word_sub stackpointer (word 320),320;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [out0,168 * nblocks; out1,168 * nblocks;
                      out2,168 * nblocks; out3,168 * nblocks; st,800;
                      word_sub stackpointer (word 320),320]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(out0,168 * nblocks);
               memory :> bytes(out1,168 * nblocks);
               memory :> bytes(out2,168 * nblocks);
               memory :> bytes(out3,168 * nblocks);
               memory :> bytes(st,800);
               memory :> bytes(word_sub stackpointer (word 320),320)])`;;

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, using those  *)
(* of mlk_keccak_squeezeblocks_x4.                                           *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
     forall e out0 out1 out2 out3 nblocks st
            (S0:1600 word) (S1:1600 word) (S2:1600 word) (S3:1600 word)
            pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [out0,168 * nblocks; out1,168 * nblocks; out2,168 * nblocks;
         out3,168 * nblocks; st,800; word_sub stackpointer (word 320),320] /\
       ALL (nonoverlapping (word pc,libmlkem_size))
        [out0,168 * nblocks; out1,168 * nblocks; out2,168 * nblocks;
         out3,168 * nblocks; st,800; word_sub stackpointer (word 320),320]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_Os_mc /\
                 read PC s = word (pc + mlkem_shake128x4_squeezeblocks) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [out0; out1; out2; out3; word nblocks; st] s /\
                 read (memory :> wbytes st) s = S0 /\
                 read (memory :> wbytes (word_add st (word 200))) s = S1 /\
                 read (memory :> wbytes (word_add st (word 400))) s = S2 /\
                 read (memory :> wbytes (word_add st (word 600))) s = S3 /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 read (memory :> bytes(out0,168 * nblocks)) s =
                 nsum {i | i < nblocks}
                  (\i. 2 EXP (8 * 168 * i) *
                       val(keccak_squeeze (i + 1) S0) MOD 2 EXP (8 * 168)) /\
                 read (memory :> bytes(out1,168 * nblocks)) s =
                 nsum {i | i < nblocks}
                  (\i. 2 EXP (8 * 168 * i) *
                       val(keccak_squeeze (i + 1) S1) MOD 2 EXP (8 * 168)) /\
                 read (memory :> bytes(out2,168 * nblocks)) s =
                 nsum {i | i < nblocks}
                  (\i. 2 EXP (8 * 168 * i) *
                       val(keccak_squeeze (i + 1) S2) MOD 2 EXP (8 * 168)) /\
                 read (memory :> bytes(out3,168 * nblocks)) s =
                 nsum {i | i < nblocks}
                  (\i. 2 EXP (8 * 168 * i) *
                       val(keccak_squeeze (i + 1) S3) MOD 2 EXP (8 * 168)) /\
                 read (memory :> wbytes st) s = keccak_squeeze nblocks S0 /\
                 read (memory :> wbytes (word_add st (word 200))) s =
                 keccak_squeeze nblocks S1 /\
                 read (memory :> wbytes (word_add st (word 400))) s =
                 keccak_squeeze nblocks S2 /\
                 read (memory :> wbytes (word_add st (word 600))) s =
                 keccak_squeeze nblocks S3 /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events out0 out1 out2 out3 nblocks st pc
                           (word_sub stackpointer (word 320)) returnaddress /\
                    memaccess_inbounds e2
                     [out0,168 * nblocks; out1,168 * nblocks;
                      out2,168 * nblocks; out3,168 * nblocks; st,800;
                      word_sub stackpointer (word 320),320;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [out0,168 * nblocks; out1,168 * nblocks;
                      out2,168 * nblocks; out3,168 * nblocks; st,800;
                      word_sub stackpointer (word 320),320]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(out0,168 * nblocks);
               memory :> bytes(out1,168 * nblocks);
               memory :> bytes(out2,168 * nblocks);
               memory :> bytes(out3,168 * nblocks);
               memory :> bytes(st,800);
               memory :> bytes(word_sub stackpointer (word 320),320)])`;;

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;
