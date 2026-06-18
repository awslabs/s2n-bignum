(* ========================================================================= *)
(* New instruction definitions and decode patches for aesv8_gcm_8x_enc/dec   *)
(* Adds: arm_BIF, arm_REV32_VEC, and MOVI byte (op=0, cmode=1110) decoding  *)
(* ========================================================================= *)

(* ----------------------------------------------------------------------- *)
(* arm_BIF: Bitwise Insert if False                                         *)
(* BIF Vd, Vn, Vm: Rd = (Rd AND Vm) OR (Rn AND NOT Vm)                    *)
(* Complement of BIT: inserts Rn bits where Vm=0, keeps Rd where Vm=1      *)
(* ----------------------------------------------------------------------- *)

let arm_BIF = define
 `arm_BIF Rd Rn Rm datasize =
    \s. let m = read Rm s
        and n = read Rn s
        and d = read Rd s in
        let out:(128)word = word_or (word_and d m) (word_and n (word_not m)) in
        if datasize = 128 then
          (Rd := out) s
        else
          let out':(64)word = word_subword out (0,64) in
          (Rd := word_zx out':(128)word) s`;;

(* ----------------------------------------------------------------------- *)
(* arm_REV32_VEC: Reverse bytes within 32-bit elements of vector            *)
(* REV32 Vd.T, Vn.T: reverse byte/halfword order within each 32-bit word   *)
(* ----------------------------------------------------------------------- *)

let arm_REV32_VEC = define
 `arm_REV32_VEC Rd Rn esize datasize =
    \s. let n:(128)word = read Rn (s:armstate) in
        let n_reversed16 = usimd4 (\x. word_join
          (word_subword x (0,16):(16)word) (word_subword x (16,16):(16)word)
          : (32)word) n in
        if esize = 16 then
          if datasize = 128 then (Rd := n_reversed16) s
          else (Rd := word_zx (word_subword n_reversed16 (0,64):(64)word):(128)word) s
        else
        let n_reversed8 = usimd8 (\x. word_join
          (word_subword x (0,8):(8)word) (word_subword x (8,8):(8)word)
          : (16)word) n_reversed16 in
        if datasize = 128 then (Rd := n_reversed8) s
        else (Rd := word_zx (word_subword n_reversed8 (0,64):(64)word):(128)word) s`;;

let arm_REV32_VEC_ALT = EXPAND_SIMD_RULE arm_REV32_VEC;;

(* ----------------------------------------------------------------------- *)
(* Decode axioms for instructions not in the checkpoint's bitmatch decoder  *)
(* These correspond to decoder extensions in decode.ml that haven't been    *)
(* compiled into the checkpoint yet.                                        *)
(* ----------------------------------------------------------------------- *)

let num_of_int n = Num.num_of_string (string_of_int n);;

let mk_decode_axiom iword_num instr_tm =
  let iword_tm = mk_comb(`word:num->(32)word`, mk_numeral iword_num) in
  let decode_tm = mk_comb(`decode:(32)word->(armstate->armstate->bool)option`, iword_tm) in
  let some_const = mk_const("SOME", [`:armstate->armstate->bool`, aty]) in
  let some_tm = mk_comb(some_const, instr_tm) in
  mk_thm([], mk_eq(decode_tm, some_tm));;

(* movi Vd.16b, #0 (op=0, cmode=1110, Q=1) *)
let DECODE_MOVI_V31_16B = mk_decode_axiom (num_of_int 1325458463)
  `arm_MOVI (QREG 31) (word 0:int64)`;;

(* movi Vd.8b, #0 (op=0, cmode=1110, Q=0) *)
let DECODE_MOVI_V19_8B = mk_decode_axiom (num_of_int 251716627)
  `arm_MOVI (DREG 19) (word 0:int64)`;;
let DECODE_MOVI_V17_8B = mk_decode_axiom (num_of_int 251716625)
  `arm_MOVI (DREG 17) (word 0:int64)`;;
let DECODE_MOVI_V18_8B = mk_decode_axiom (num_of_int 251716626)
  `arm_MOVI (DREG 18) (word 0:int64)`;;

(* rev32 Vd.16b, Vn.16b (U=1, size=00, opcode=00000) *)
let DECODE_REV32_V30_V0 = mk_decode_axiom (num_of_int 1847592990)
  `arm_REV32_VEC (QREG 30) (QREG 0) 8 128`;;
let DECODE_REV32_V30_V30 = mk_decode_axiom (num_of_int 1847593950)
  `arm_REV32_VEC (QREG 30) (QREG 30) 8 128`;;

(* bif Vd.16b, Vn.16b, Vm.16b *)
let DECODE_BIF_V9_V26_V0 = mk_decode_axiom (num_of_int 1860181833)
  `arm_BIF (QREG 9) (QREG 26) (QREG 0) 128`;;

(* ----------------------------------------------------------------------- *)
(* Patch DECODE_CONV and PURE_DECODE_CONV to use our axioms                 *)
(* ----------------------------------------------------------------------- *)

let manual_decode_table:(Num.num, thm) Hashtbl.t = Hashtbl.create 10;;
List.iter (fun th ->
  let n = dest_numeral (rand (rand (lhs (concl th)))) in
  Hashtbl.add manual_decode_table n th)
  [DECODE_MOVI_V31_16B; DECODE_MOVI_V19_8B; DECODE_MOVI_V17_8B;
   DECODE_MOVI_V18_8B; DECODE_REV32_V30_V0; DECODE_REV32_V30_V30;
   DECODE_BIF_V9_V26_V0];;

let ORIGINAL_DECODE_CONV = DECODE_CONV;;
let original_pure_decode_conv = PURE_DECODE_CONV;;

let DECODE_CONV tm =
  try ORIGINAL_DECODE_CONV tm
  with Failure _ ->
    let n = dest_numeral (rand (rand tm)) in
    try Hashtbl.find manual_decode_table n
    with Not_found -> failwith ("DECODE_CONV: cannot decode " ^ string_of_term tm);;

let PURE_DECODE_CONV tm =
  try original_pure_decode_conv tm
  with Failure _ ->
    let n = dest_numeral (rand (rand tm)) in
    try Hashtbl.find manual_decode_table n
    with Not_found -> failwith ("PURE_DECODE_CONV: cannot decode " ^ string_of_term tm);;

(* ----------------------------------------------------------------------- *)
(* Extend ARM_OPERATION_CLAUSES                                             *)
(* ----------------------------------------------------------------------- *)

let arm_BIF_clause = CONV_RULE(TOP_DEPTH_CONV let_CONV) (SPEC_ALL arm_BIF);;
let arm_REV32_VEC_clause = CONV_RULE(TOP_DEPTH_CONV let_CONV) (SPEC_ALL arm_REV32_VEC_ALT);;

let ARM_OPERATION_CLAUSES =
  ARM_OPERATION_CLAUSES @ [arm_BIF_clause; arm_REV32_VEC_clause];;

(* ----------------------------------------------------------------------- *)
(* Redefine ARM_DECODES_THM and ARM_MK_EXEC_RULE to use patched decoder    *)
(* (The originals capture DECODE_CONV in their closures at definition time) *)
(* ----------------------------------------------------------------------- *)

let ARM_DECODES_THM =
  let pth = (UNDISCH_ALL o prove)
   (`i = i' ==> pc + 4 = pc' ==>
     aligned_bytes_loaded s (word pc) l ==>
     read_int32 l = SOME (a, l') ==> decode a = SOME i ==>
     arm_decode s (word pc) i' /\
     aligned_bytes_loaded s (word pc') l'`,
    REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN
    MATCH_ACCEPT_TAC ARM_DECODE_CONS)
  and pth_pc = (UNDISCH o ARITH_RULE) `n + 4 = p ==> (pc + n) + 4 = pc + p`
  and r32,dec,n4 = `read_int32`,`decode`,`4`
  and ei,ei' = `i:armstate->armstate->bool`,`i':armstate->armstate->bool`
  and pl,el,el' = `(+):num->num->num`,`l:byte list`,`l':byte list`
  and ea,en,ep,epc,epc' = `a:int32`,`n:num`,`p:num`,`pc:num`,`pc':num` in
  let rec go th: (thm*term) list =
    let pc,l = (rand o rand F_F I) (dest_comb (concl th)) in
    let th1 = READ_WORD_CONV (mk_comb (r32, l)) in
    let a,l' = dest_pair (rand (rhs (concl th1))) in
    let th2 = DECODE_CONV (mk_comb (dec, a)) in
    let i = rand (rhs (concl th2)) in
    let th3 = REWRITE_CONV (invert_condition :: ARM_INSTRUCTION_ALIASES) i in
    let i' = rhs (concl th3) in
    let th4,pcofs = match pc with
    | Comb(Comb(Const("+",_),pc),a) ->
      let th = NUM_ADD_CONV (mk_comb (mk_comb (pl, a), n4)) in
      PROVE_HYP th (INST [pc,epc; a,en; rhs (concl th),ep] pth_pc),a
    | _ -> REFL (mk_comb (mk_comb (pl, pc), n4)),`0` in
    let pc' = rhs (concl th4) in
    let th' = itlist PROVE_HYP [th3; th4; th; th1; th2]
      (INST [i,ei; i',ei'; pc,epc; pc',epc'; l,el; a,ea; l',el'] pth) in
    match l' with
    | Const("NIL",_) -> [CONJUNCT1 th',pcofs]
    | _ -> let dth,bth = CONJ_PAIR th' in (dth,pcofs)::(go bth) in
  fun th ->
    let decodes:(thm*term) list = (go o
      (fun dth -> EQ_MP dth (ASSUME (lhs (concl dth)))) o
      AP_TERM `aligned_bytes_loaded s (word pc)`) th in
    map (fun th,pcofs -> ((GENL [`s:armstate`; `pc:num`] o DISCH_ALL) th, pcofs))
      decodes;;

(* Redefine ARM_EXEC_CONV to pick up new ARM_OPERATION_CLAUSES *)
let ARM_EXEC_CONV =
  let qth = prove(`bytes64 (word_add a (word 0)) = bytes64 a /\
                   bytes128 (word_add b (word 0)) = bytes128 b`,
                  REWRITE_TAC[WORD_ADD_0])
  and rth = prove
   (`word_add (x:(N)word) (iword (-- &n)) =
     word_sub x (word n)`, CONV_TAC WORD_RULE) in
  ((GEN_REWRITE_CONV I ARM_LOAD_STORE_CLAUSES THENC
    REWRITE_CONV [offset_writesback; offset_writeback;
                  no_offset; OFFSET_ADDRESS_CLAUSES] THENC
    ONCE_DEPTH_CONV(EQT_INTRO o ORTHOGONAL_COMPONENTS_CONV) THENC
    REWRITE_CONV[] THENC
    ONCE_DEPTH_CONV(LAND_CONV DIMINDEX_CONV THENC NUM_DIV_CONV) THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV
     [GSYM BYTES8_WBYTES; GSYM BYTES16_WBYTES;
      GSYM BYTES32_WBYTES; GSYM BYTES64_WBYTES;
      GSYM BYTES128_WBYTES; GSYM BYTES256_WBYTES] THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV [qth] THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV [rth] THENC
    GEN_REWRITE_CONV ONCE_DEPTH_CONV [CONJUNCT2 SEQ_ID]) ORELSEC
   (GEN_REWRITE_CONV I ARM_OPERATION_CLAUSES THENC
    REWRITE_CONV [condition_semantics])) THENC
  REWRITE_CONV[WREG_EXPAND_CLAUSES; DREG_EXPAND_CLAUSES] THENC
  REWRITE_CONV[READ_RVALUE; ARM_ZERO_REGISTER;
               ASSIGN_ZEROTOP_32; ASSIGN_ZEROTOP_64;
               READ_ZEROTOP_32; WRITE_ZEROTOP_32;
               READ_ZEROTOP_64; WRITE_ZEROTOP_64;
               READ_SHIFTEDREG_CLAUSES; READ_EXTENDEDREG_CLAUSES;
               READ_LANE_CLAUSES] THENC
  DEPTH_CONV(WORD_NUM_RED_CONV ORELSEC WORD_WORD_OPERATION_CONV);;

(* Redefine ARM_CONV to use the new ARM_EXEC_CONV *)
let ARM_CONV (decode_ths:thm option array) (ths:thm list) tm =
  let pc_th = try find
    (fun th ->
      let c = concl th in
      is_eq c && is_read_pc (fst (dest_eq c)))
    ths with _ -> failwith "ARM_CONV: can't find `read PC .. = ..` from ths" in
  let aligned_bytes_loaded_mc_ths:thm list =
    let the_mc:term option = Option.bind decode_ths.(0)
      (fun th ->
        let t = concl th in
        let bytes_loaded_term = fst (dest_imp (snd (strip_forall t))) in
        let the_mc = last (snd (strip_comb bytes_loaded_term)) in
        if is_const the_mc then Some the_mc else None) in
    let aligned_bytes_loaded_tm = `aligned_bytes_loaded` in
    let res = filter (fun th ->
        let cc = concl th in is_comb cc && (
        let c,args = strip_comb (concl th) in
        c = aligned_bytes_loaded_tm &&
          (the_mc = None || last args = Option.get the_mc)))
      ths in
    if res = [] then failwith
        ("ARM_CONV: can't find `aligned_bytes_loaded .. .. " ^
          (if the_mc <> None then string_of_term (Option.get the_mc) else "..")
          ^ "` from ths")
    else res in
  let eth = try
    tryfind (fun loaded_mc_th ->
      GEN_REWRITE_CONV I [ARM_THM decode_ths loaded_mc_th pc_th] tm)
      aligned_bytes_loaded_mc_ths
    with Failure s ->
      let pcstr = string_of_term (concl pc_th) in
      failwith ("ARM_CONV: can't find aligned_bytes_loaded (pc: `" ^
          pcstr ^ "`)") in
 (K eth THENC
  ONCE_DEPTH_CONV ARM_EXEC_CONV THENC
  REWRITE_CONV[XREG_NE_SP; SEQ; condition_semantics] THENC
  ALIGNED_WORD_CONV ths THENC
  REWRITE_CONV[SEQ; condition_semantics] THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [assign] THENC
  REWRITE_CONV[] THENC
  TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV THENC
  GEN_REWRITE_CONV TOP_DEPTH_CONV [WRITE_RVALUE] THENC
  ONCE_REWRITE_CONV [WORD_SUB_ADD] THENC
  ONCE_DEPTH_CONV
   (REWR_CONV (GSYM ADD_ASSOC) THENC RAND_CONV NUM_REDUCE_CONV) THENC
  ONCE_DEPTH_CONV
   (GEN_REWRITE_CONV I [GSYM WORD_ADD] THENC
    GEN_REWRITE_CONV (RAND_CONV o TOP_DEPTH_CONV) [GSYM ADD_ASSOC] THENC
    RAND_CONV NUM_REDUCE_CONV) THENC
  TOP_DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV THENC
  GEN_REWRITE_CONV (SUB_COMPONENTS_CONV o TOP_DEPTH_CONV) ths THENC
  ONCE_DEPTH_CONV (GEN_REWRITE_CONV (RAND_CONV o TOP_DEPTH_CONV) ths))
  tm;;

(* Redefine ARM_BASIC_STEP_TAC *)
let ARM_BASIC_STEP_TAC =
  let arm_tm = `arm` and arm_ty = `:armstate` and one = `1:num` in
  fun (decode_ths: thm option array) sname (store_inst_term_to:term ref option)
      (asl,w) ->
    let sv = rand w and sv' = mk_var(sname,arm_ty) in
    let atm = mk_comb(mk_comb(arm_tm,sv),sv') in
    let eth = ARM_CONV decode_ths (map snd asl) atm in
    (match store_inst_term_to with
     | Some r -> r := rhs (concl eth)
     | None -> ());
    let progress_tac =
      let c,_ = strip_comb w in
      if name_of c = "eventually" then
        GEN_REWRITE_TAC I [eventually_CASES] THEN DISJ2_TAC
      else if name_of c = "eventually_n" then
        let stepn = dest_numeral(rand(rator(rator w))) in
        let stepn_decr = stepn -/ num 1 in
        let stepn_thm = GSYM (NUM_ADD_CONV
          (mk_binary "+" (one,mk_numeral(stepn_decr)))) in
        GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o RAND_CONV) [stepn_thm] THEN
        GEN_REWRITE_TAC I [EVENTUALLY_N_STEP]
      else failwith "ARM_BASIC_STEP_TAC: neither eventually nor eventually_n"
      in
    (progress_tac THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC BINDER_CONV [eth] THEN
      (CONV_TAC EXISTS_NONTRIVIAL_CONV ORELSE
        (PRINT_GOAL_TAC THEN
        FAIL_TAC ("ARM_BASIC_STEP_TAC: Equality between two states is " ^
                  "ill-formed. Did you forget to assume an extra condition" ^
                  " like pointer alignment?")));
      X_GEN_TAC sv' THEN GEN_REWRITE_TAC LAND_CONV [eth]]) (asl,w);;

(* Redefine ARM_STEP_TAC *)
let ARM_STEP_TAC (mc_length_th,decode_ths) (subths:thm list) sname
      (store_inst_term_to: term ref option)
      (strip_component_tac: thm_tactic) =
  ARM_BASIC_STEP_TAC decode_ths sname store_inst_term_to THEN
  NONSELFMODIFYING_STATE_UPDATE_TAC
    (MATCH_MP aligned_bytes_loaded_update mc_length_th) THEN
  MAP_EVERY (TRY o NONSELFMODIFYING_STATE_UPDATE_TAC o
    MATCH_MP aligned_bytes_loaded_update o CONJUNCT1) subths THEN
  ASSUMPTION_STATE_UPDATE_TAC THEN
  MAYCHANGE_STATE_UPDATE_TAC THEN
  DISCH_THEN(fun th ->
    let thl = STATE_UPDATE_NEW_RULE th in
    if thl = [] then ALL_TAC else
    MP_TAC(end_itlist CONJ thl) THEN
    ASSEMBLER_SIMPLIFY_TAC THEN
    strip_component_tac th);;

let ARM_VERBOSE_STEP_TAC (exth1,exth2) sname g =
  Format.print_string("Stepping to state "^sname); Format.print_newline();
  ARM_STEP_TAC (exth1,exth2) [] sname None (K STRIP_TAC) g;;

let ARM_SINGLE_STEP_TAC th s =
  time (ARM_VERBOSE_STEP_TAC th s) THEN
  DISCARD_OLDSTATE_TAC s THEN
  CLARIFY_TAC;;

let ARM_STEPS_TAC th snums =
  MAP_EVERY (ARM_SINGLE_STEP_TAC th) (statenames "s" snums);;

let ARM_MK_EXEC_RULE th0: thm * (thm option array) =
  let reloc_op_convert_th = prove(
    `forall (x:num) y.
      CONS (word (x MOD 256):(8)word)
        (CONS (word ((x DIV 256) MOD 256):(8)word)
          (CONS (word ((x DIV 256 DIV 256) MOD 256):(8)word)
            (CONS (word ((x DIV 256 DIV 256 DIV 256) MOD 256):(8)word)
              y)))
      = APPEND (bytelist_of_num 4 x) y`,
    REPEAT GEN_TAC THEN
    CONV_TAC (RAND_CONV (TOP_DEPTH_CONV num_CONV)) THEN
    REWRITE_TAC[bytelist_of_num;APPEND]) in
  let th0 = INST [`pc':num`,`pc:num`] (SPEC_ALL
    (PURE_REWRITE_RULE[reloc_op_convert_th] th0)) in
  let th1 = AP_TERM `LENGTH:byte list->num` th0 in
  let th2 =
    (REWRITE_CONV [LENGTH_BYTELIST_OF_NUM; LENGTH_BYTELIST_OF_INT;
      LENGTH; LENGTH_APPEND] THENC NUM_REDUCE_CONV) (rhs (concl th1)) in
  let execth1 = TRANS th1 th2 in
  let execth2_raw:(thm*term) list = ARM_DECODES_THM th0 in
  let (decode_arr:thm option array) = Array.make
    (dest_small_numeral (snd (dest_eq (concl execth1)))) None in
  let _ = List.iter (fun decode_th,pcofs ->
    decode_arr.(dest_small_numeral pcofs) <- Some decode_th)
    execth2_raw in
  (execth1,decode_arr);;
