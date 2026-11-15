(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA3-512. This is the code for mlkem_sha3_512 from mlkem-native's         *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md), which absorbs the input into a state on the      *)
(* stack with mlk_keccak_absorb_once, permutes it and extracts the 64 bytes  *)
(* of the hash, and then zeroes the state with REP STOSQ. It is verified in  *)
(* the whole image (see libmlkem.ml), using the theorems for                 *)
(* mlk_keccak_absorb_once, mlkem_keccakf1600_permute and                     *)
(* mlkem_keccakf1600_extract_bytes in the image. The result is sha3_512 of   *)
(* common/fips202/fips202.ml.                                                *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/keccak_absorb_once_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/keccakf1600_extract_bytes_spec.ml";;
needs "x86/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_sha3_512:
       +0x0: push   rbp
       +0x1: mov    rcx,rdx
       +0x4: mov    r8d,0x6
       +0xa: mov    rdx,rsi
       +0xd: push   rbx
       +0xe: mov    rbp,rdi
      +0x11: mov    esi,0x48
      +0x16: sub    rsp,0xd8
      +0x1d: mov    rbx,rsp
      +0x20: mov    rdi,rbx
      +0x23: call   <mlk_keccak_absorb_once>
      +0x28: mov    rdi,rbx
      +0x2b: call   <mlkem_keccakf1600_permute>
      +0x30: mov    rdi,rbx
      +0x33: mov    ecx,0x40
      +0x38: xor    edx,edx
      +0x3a: mov    rsi,rbp
      +0x3d: call   <mlkem_keccakf1600_extract_bytes>
      +0x42: xor    eax,eax
      +0x44: mov    rdi,rbx
      +0x47: mov    ecx,0x19
      +0x4c: rep    stos QWORD PTR es:[rdi],rax
      +0x4f: add    rsp,0xd8
      +0x56: pop    rbx
      +0x57: pop    rbp
      +0x58: ret
 ***)

let MLKEM_NATIVE_SHA3_512_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [layout_range "mlkem_sha3_512"];;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, using those  *)
(* of mlk_keccak_absorb_once, mlkem_keccakf1600_permute and                  *)
(* mlkem_keccakf1600_extract_bytes. The input is a list of bytes, and the 64 *)
(* bytes of the output, as a number, are those of sha3_512 in                *)
(* common/fips202/fips202.ml. The stack is the 232 bytes of the function,    *)
(* the return address of a call and the 320 bytes used by                    *)
(* mlk_keccak_absorb_once below that.                                        *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;

let SHA3_512_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,MLKEM_NATIVE_SHA3_512_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `m:int64`; `out:int64`; `inlen:num`;
                          `stackpointer:int64`; `returnaddress:int64`]);
      LABEL_TAC name safety_th]);;

let MLKEM_NATIVE_SHA3_512_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
     forall e out m (inp:byte list) inlen pc stackpointer returnaddress.
       aligned 16 (word pc:int64) /\ LENGTH inp = inlen /\
       PAIRWISE nonoverlapping
        [out,64; m,inlen; word_sub stackpointer (word 560),568] /\
       ALL (nonoverlapping (word pc,libmlkem_size))
        [out,64; word_sub stackpointer (word 560),568]
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + mlkem_sha3_512) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [out; m; word inlen] s /\
                 (read DF s <=> false) /\
                 read (memory :> bytes(m,inlen)) s = num_of_bytelist inp /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 read (memory :> bytes(out,64)) s =
                 num_of_bytelist(sha3_512 inp) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m out inlen pc
                           (word_sub stackpointer (word 560)) returnaddress /\
                    memaccess_inbounds e2
                     [m,inlen; out,64; word_sub stackpointer (word 560),568;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [out,64; word_sub stackpointer (word 560),560]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(out,64);
               memory :> bytes(word_sub stackpointer (word 560),560)])`;;

let MLKEM_NATIVE_SHA3_512_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_SHA3_512_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem alone, from the combined one.                     *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHA3_512_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!out m (inp:byte list) pc stackpointer returnaddress.
        aligned 16 (word pc:int64) /\
        PAIRWISE nonoverlapping
         [(out,64); (m,LENGTH inp); (word_sub stackpointer (word 560),568)] /\
        ALL (nonoverlapping (word pc,libmlkem_size))
         [(out,64); (word_sub stackpointer (word 560),568)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read RIP s = word (pc + mlkem_sha3_512) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [out; m; word(LENGTH inp)] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(m,LENGTH inp)) s =
                  num_of_bytelist inp)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> bytes(out,64)) s =
                  num_of_bytelist(sha3_512 inp))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(out,64);
                memory :> bytes(word_sub stackpointer (word 560),560)])`;;

let MLKEM_NATIVE_SHA3_512_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_SHA3_512_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, for any input.                     *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHA3_512_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e out m inlen pc stackpointer returnaddress.
       aligned 16 (word pc:int64) /\
       PAIRWISE nonoverlapping
        [out,64; m,inlen; word_sub stackpointer (word 560),568] /\
       ALL (nonoverlapping (word pc,libmlkem_size))
        [out,64; word_sub stackpointer (word 560),568]
       ==> ensures x86
            (\s. bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read RIP s = word (pc + mlkem_sha3_512) /\
                 read RSP s = stackpointer /\
                 read (memory :> bytes64 stackpointer) s = returnaddress /\
                 C_ARGUMENTS [out; m; word inlen] s /\
                 (read DF s <=> false) /\
                 read events s = e)
            (\s. read RIP s = returnaddress /\
                 read RSP s = word_add stackpointer (word 8) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m out inlen pc
                           (word_sub stackpointer (word 560)) returnaddress /\
                    memaccess_inbounds e2
                     [m,inlen; out,64; word_sub stackpointer (word 560),568;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [out,64; word_sub stackpointer (word 560),560]))
            (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE
              [memory :> bytes(out,64);
               memory :> bytes(word_sub stackpointer (word 560),560)])`;;

let MLKEM_NATIVE_SHA3_512_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_SHA3_512_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
