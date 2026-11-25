(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* A check of the API of common/elf_image.ml and arm/proofs/libc.ml on the   *)
(* snappy image: the relocated slots that the proofs use (the GOT slot of    *)
(* memcpy, the GOT slot with the address of ByteArraySource's vtable, and a  *)
(* slot of that vtable), and the PLT stub of memcpy with the contract of     *)
(* memcpy at the address in its GOT slot, both with ARM_STEPS_TAC and with   *)
(* bstep. These are the forms that the proofs of the functions use: the     *)
(* relocated data as a region of libsnappy_rw_size bytes at                 *)
(* pc + libsnappy_rw with contents rw, and elf_relocated_data for rw.        *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/libsnappy.ml";;
needs "arm/proofs/libc.ml";;

let SNAPPY_LIBSNAPPY_GCC12_O2_SLOTS_WITHIN = prove
 (`!pc imp.
     elf_slots_within (word(pc + libsnappy_rw)) libsnappy_rw_size
                      (snappy_libsnappy_gcc12_O2_relocated pc imp)`,
  REPEAT GEN_TAC THEN
  CONV_TAC(ELF_SLOTS_WITHIN_CONV
    ~defs:[snappy_libsnappy_gcc12_O2_relocated]));;

(* The slots: memcpy's GOT slot, the GOT slot that ByteArraySource's         *)
(* constructor loads (the address of _ZTV, to which it adds 16), and the     *)
(* vtable slot of ByteArraySource::Peek, the fourth after the vptr.          *)

let SNAPPY_LIBSNAPPY_GCC12_O2_SLOTS = prove
 (`!pc imp rw s:armstate.
        elf_relocated_data (word(pc + libsnappy_rw)) rw
          (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
        read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s =
        rw
        ==> read (memory :> bytes64 (word_add (word pc) (word got_memcpy))) s =
            imp "memcpy" /\
            read (memory :> bytes64
                   (word_add (word pc) (word got_ztv_ByteArraySource))) s =
            word(pc + ztv_ByteArraySource) /\
            read (memory :> bytes64
                   (word_add (word pc) (word(vtable_ByteArraySource + 24)))) s =
            word(pc + ByteArraySource_Peek)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
    ~select:(elf_slots_at [layout "got_memcpy";
                           layout "got_ztv_ByteArraySource";
                           layout "vtable_ByteArraySource" + 24]) THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A call of plt_memcpy behaves as memcpy.                                   *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_PLT_MEMCPY_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "plt_memcpy"];;

let SNAPPY_PLT_MEMCPY_STMT =
 `!dst src len x pc imp ea el ev rw returnaddress.
    memcpy_contract (imp "memcpy") ea el ev /\
    aligned 4096 (word pc:int64) /\
    pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
    elf_relocated_data (word(pc + libsnappy_rw)) rw
      (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
    nonoverlapping (dst,val len) (src,val len) /\
    ALLPAIRS nonoverlapping
     [dst,val(len:int64)]
     [word pc,libsnappy_rw + libsnappy_rw_size; ea,el]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
              read PC s = word(pc + plt_memcpy) /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [dst; src; len] s /\
              read (memory :> bytes(word(pc + libsnappy_rw),
                                    libsnappy_rw_size)) s = rw /\
              read (memory :> bytes(ea,el)) s = ev /\
              read (memory :> bytes(src,val len)) s = x)
         (\s. read PC s = returnaddress /\ C_RETURN s = dst /\
              read (memory :> bytes(dst,val len)) s = x)
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
          MAYCHANGE [memory :> bytes(dst,val len)])`;;

let SNAPPY_PLT_MEMCPY_START_TAC =
  MAP_EVERY X_GEN_TAC
   [`dst:int64`; `src:int64`; `len:int64`; `x:num`; `pc:num`;
    `imp:string->int64`; `ea:int64`; `el:num`; `ev:num`; `rw:num`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS; C_RETURN;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (LABEL_TAC "H_MEMCPY" o REWRITE_RULE[memcpy_contract])
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  ENSURES_INIT_TAC "s0" THEN
  ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
    ~select:(elf_slots_importing ["memcpy"]);;

let SNAPPY_PLT_MEMCPY = prove
 (SNAPPY_PLT_MEMCPY_STMT,
  SNAPPY_PLT_MEMCPY_START_TAC THEN
  ARM_PLT_STUB_TAC SNAPPY_PLT_MEMCPY_EXEC 0 THEN
  ARM_PLT_CALL_TAC "H_MEMCPY" SNAPPY_PLT_MEMCPY_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `x:num`; `read X30 s`] 5 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

let SNAPPY_PLT_MEMCPY_BSTEP = prove
 (SNAPPY_PLT_MEMCPY_STMT,
  SNAPPY_PLT_MEMCPY_START_TAC THEN
  USE_THEN "H_MEMCPY" (fun th ->
    ARM_BSTEP_PLT_TAC SNAPPY_PLT_MEMCPY_EXEC th
     [`read X0 s`; `read X1 s`; `read X2 s`; `x:num`; `read X30 s`] "s5") THEN
  BSTEP_FINAL_TAC THEN ASM_REWRITE_TAC[]);;
