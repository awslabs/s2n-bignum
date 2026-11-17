(* All eight SHA256/SHA512 instructions. Claims retain all vector register
   fields and overlaps under the declared register boundary; compiler and
   full-platform preservation are not proved. *)
loadt "arm/proofs/base.ml";;
needs "tools/sail/proofs/report.ml";;
loadt "tools/sail/_build/arm-sha2.ml";;
(* Bitvector representation facts, not SHA instruction semantics. *)
let SAIL_HL_ARM_SHA2_ROTATE = prove
 (`!x:N word. !count:num. count <= dimindex(:N) ==>
    word_or (word_ushr x count)
      (word_shl x (dimindex(:N) - count)) = word_ror x count`,
  SIMP_TAC[WORD_ROR_SHIFTS]);;

let SAIL_HL_ARM_SHA2_ROTATE32 =
  REWRITE_RULE[DIMINDEX_32]
    (INST_TYPE[`:32`,`:N`] SAIL_HL_ARM_SHA2_ROTATE);;
let SAIL_HL_ARM_SHA2_ROTATE64 =
  REWRITE_RULE[DIMINDEX_64]
    (INST_TYPE[`:64`,`:N`] SAIL_HL_ARM_SHA2_ROTATE);;
let SAIL_HL_ARM_SHA2_ROTATE256 =
  REWRITE_RULE[DIMINDEX_256]
    (INST_TYPE[`:256`,`:N`] SAIL_HL_ARM_SHA2_ROTATE);;

(* Normalize static counts in the theorem before matching an emitted
   word_shl by a computed numeral, rather than a syntactic width-count. *)
let SAIL_HL_ARM_SHA2_ROTATE_COUNTS theorem word_type counts =
  map (fun count ->
    GEN_ALL(REWRITE_RULE[IMP_CLAUSES] (CONV_RULE NUM_REDUCE_CONV
      (SPECL [mk_var("x",word_type); mk_small_numeral count] theorem))))
    counts;;

let SAIL_HL_ARM_SHA2_ROTATE32_COUNTS =
  SAIL_HL_ARM_SHA2_ROTATE_COUNTS SAIL_HL_ARM_SHA2_ROTATE32
    `:32 word` (0--32);;
let SAIL_HL_ARM_SHA2_ROTATE64_COUNTS =
  SAIL_HL_ARM_SHA2_ROTATE_COUNTS SAIL_HL_ARM_SHA2_ROTATE64
    `:64 word` (0--64);;
let SAIL_HL_ARM_SHA2_ROTATE256_COUNTS =
  SAIL_HL_ARM_SHA2_ROTATE_COUNTS SAIL_HL_ARM_SHA2_ROTATE256
    `:256 word` [224];;

let SAIL_HL_ARM_SHA2_READ_HIGH = prove
 (`!x:128 word. !y:64 word.
    (word_subword (word_insert x (64,64) y:128 word) (64,64):64 word) = y`,
  CONV_TAC WORD_BLAST);;
let SAIL_HL_ARM_SHA2_READ_LOW = prove
 (`!x:128 word. !y:64 word.
    (word_subword (word_insert x (0,64) y:128 word) (0,64):64 word) = y`,
  CONV_TAC WORD_BLAST);;
let SAIL_HL_ARM_SHA2_HIGH_KEEPS_LOW = prove
 (`!x:128 word. !y:64 word.
    (word_subword (word_insert x (64,64) y:128 word) (0,64):64 word) =
    word_subword x (0,64)`,
  CONV_TAC WORD_BLAST);;
let SAIL_HL_ARM_SHA2_LOW_KEEPS_HIGH = prove
 (`!x:128 word. !y:64 word.
    (word_subword (word_insert x (0,64) y:128 word) (64,64):64 word) =
    word_subword x (64,64)`,
  CONV_TAC WORD_BLAST);;
let SAIL_HL_ARM_SHA2_OVERWRITE_HIGH = prove
 (`!x:128 word. !y:64 word. !z:64 word.
    word_insert (word_insert x (64,64) y:128 word) (64,64) z =
    (word_insert x (64,64) z:128 word)`,
  CONV_TAC WORD_BLAST);;
let SAIL_HL_ARM_SHA2_OVERWRITE_LOW = prove
 (`!x:128 word. !y:64 word. !z:64 word.
    word_insert (word_insert x (0,64) y:128 word) (0,64) z =
    (word_insert x (0,64) z:128 word)`,
  CONV_TAC WORD_BLAST);;
let SAIL_HL_ARM_SHA2_COMPLETE_HIGH_LOW = prove
 (`!x:128 word. !hi:64 word. !lo:64 word.
    word_insert (word_insert x (64,64) hi:128 word) (0,64) lo =
    (word_join hi lo:128 word)`,
  CONV_TAC WORD_BLAST);;
let SAIL_HL_ARM_SHA2_COMPLETE_LOW_HIGH = prove
 (`!x:128 word. !hi:64 word. !lo:64 word.
    word_insert (word_insert x (0,64) lo:128 word) (64,64) hi =
    (word_join hi lo:128 word)`,
  CONV_TAC WORD_BLAST);;
(* The source rotates y@x then splits y,x; HOL rotates x@y then splits
   x,y. Half swapping commutes with the fixed 32-bit word rotation. *)
let SAIL_HL_ARM_SHA256_PROJECT_X = prove
 (`!x:128 word. !y:128 word.
    (word_subword (word_ror (word_join y x:256 word) 224) (0,128):128 word) =
    word_subword (word_rol (word_join x y:256 word) 32) (128,128)`,
  CONV_TAC WORD_BLAST);;

let SAIL_HL_ARM_SHA256_PROJECT_Y = prove
 (`!x:128 word. !y:128 word.
    (word_subword (word_ror (word_join y x:256 word) 224) (128,128):128 word) =
    word_subword (word_rol (word_join x y:256 word) 32) (0,128)`,
  CONV_TAC WORD_BLAST);;

let SAIL_HL_ARM_SHA256_FULL32 = prove
 (`!x:32 word. (word_subword x (0,32):32 word) = x`,
  CONV_TAC WORD_BLAST);;
let SAIL_HL_ARM_SHA256_FULL64 = prove
 (`!x:64 word. (word_subword x (0,64):64 word) = x`,
  CONV_TAC WORD_BLAST);;
let SAIL_HL_ARM_SHA256_FULL128 = prove
 (`!x:128 word. (word_subword x (0,128):128 word) = x`,
  CONV_TAC WORD_BLAST);;

let SAIL_HL_ARM_SHA2_COMPLETE_FOUR = prove
 (`!x:128 word. !a:32 word. !b:32 word. !c:32 word. !d:32 word.
    word_insert (word_insert (word_insert (word_insert x (0,32) a:128 word)
      (32,32) b:128 word) (64,32) c:128 word) (96,32) d =
    (word_join d (word_join c (word_join b a:64 word):96 word):128 word)`,
  CONV_TAC WORD_BLAST);;
let SAIL_HL_ARM_SHA2_FIRST_TWO = prove
 (`!x:128 word. !a:32 word. !b:32 word.
    (word_subword (word_insert (word_insert x (0,32) a:128 word) (32,32) b:128 word)
      (0,64):64 word) = word_join b a`,
  CONV_TAC WORD_BLAST);;
let SAIL_HL_ARM_SHA2_TOP_WORD = prove
 (`!x:128 word. !hi32:32 word.
    (word_insert x (96,32) hi32:128 word) =
    word_join hi32 (word_subword x (0,96):96 word)`,
  CONV_TAC WORD_BLAST);;
(* Keep the actual exported round bodies intact while proving their
   observable tuple projections. No instruction model is synthesized. *)
let SAIL_HL_ARM_SHA256_ROUND_TYPE =
  `:armstate#32 word#32 word#32 word#128 word#128 word`;;

let rec SAIL_HL_ARM_SHA256_EXPORTED_ROUNDS tm =
  if is_let tm then
    let assignments,body = dest_let tm in
    let here = mapfilter (fun (_,value) ->
      if type_of value = SAIL_HL_ARM_SHA256_ROUND_TYPE
      then value else failwith "not a round tuple") assignments in
    here @ SAIL_HL_ARM_SHA256_EXPORTED_ROUNDS body @
      flat(map (SAIL_HL_ARM_SHA256_EXPORTED_ROUNDS o snd) assignments)
  else if is_abs tm then SAIL_HL_ARM_SHA256_EXPORTED_ROUNDS (body tm)
  else if is_comb tm then
    SAIL_HL_ARM_SHA256_EXPORTED_ROUNDS (rator tm) @
    SAIL_HL_ARM_SHA256_EXPORTED_ROUNDS (rand tm)
  else [];;

(* Each instruction passes its output selector to the shared execution
   function as a literal, so its unfolded definition keeps the one branch
   that selector takes, with four upstream rounds. Prove the four bodies
   of each instruction. *)
let SAIL_HL_ARM_SHA256_SOURCE_ROUNDS =
  flat(map (fun definition ->
    SAIL_HL_ARM_SHA256_EXPORTED_ROUNDS (rhs(concl(SPEC_ALL definition))))
    [sail_hl_ARM_5fSHA256H128; sail_hl_ARM_5fSHA256H2128]);;
assert(length SAIL_HL_ARM_SHA256_SOURCE_ROUNDS = 8);;

let SAIL_HL_ARM_SHA256_TUPLE_PROJECTION index value =
  let rec drop n tm =
    if n = 0 then tm else drop (n-1) (mk_icomb(`SND`,tm)) in
  let tail = drop index value in
  if index = 5 then tail else mk_icomb(`FST`,tail);;

let SAIL_HL_ARM_SHA256_HALF position value =
  list_mk_comb
    (`word_subword:256 word->num#num->128 word`,
     [value; mk_pair(mk_small_numeral position,mk_small_numeral 128)]);;

let SAIL_HL_ARM_SHA256_ROUND_TAC =
  REWRITE_TAC[LET_DEF; LET_END_DEF; FST; SND;
    sha256hash_loop; sha_choose; sha_maj; sha_hash_sigma_0;
    sha_hash_sigma_1; elem; NUM_OF_INT_OF_NUM;
    DIMINDEX_32; DIMINDEX_64; DIMINDEX_128; DIMINDEX_256] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC INT_REDUCE_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC(SAIL_HL_ARM_SHA2_ROTATE32_COUNTS @
    SAIL_HL_ARM_SHA2_ROTATE256_COUNTS) THEN
  SIMP_TAC[WORD_SUBWORD_INSERT_INNER; WORD_SUBWORD_INSERT_OUTER;
    DIMINDEX_128; ARITH] THEN
  REWRITE_TAC[SAIL_HL_ARM_SHA256_FULL32; SAIL_HL_ARM_SHA256_FULL128;
    SAIL_HL_ARM_SHA2_TOP_WORD; SAIL_HL_ARM_SHA256_PROJECT_X;
    SAIL_HL_ARM_SHA256_PROJECT_Y; WORD_XOR_ASSOC; WORD_ADD_ASSOC];;

let SAIL_HL_ARM_SHA256_PROVE_ROUND index value =
  let variables = frees value in
  let state = find (fun v -> type_of v = `:armstate`) variables
  and words = filter (fun v -> type_of v = `:128 word`) variables in
  assert(length variables = 4 && length words = 3);
  let state_theorem = GEN_ALL(prove
    (mk_eq(SAIL_HL_ARM_SHA256_TUPLE_PROJECTION 0 value,state),
     SAIL_HL_ARM_SHA256_ROUND_TAC)) in
  let candidates =
    flat(map (fun x ->
      mapfilter (fun y ->
        if x = y then failwith "repeated round input" else
        let w = find (fun v -> v <> x && v <> y) words in x,y,w)
        words) words) in
  let rec try_inputs = function
    | [] -> failwith "exported round does not match any input ordering"
    | (x,y,w)::rest ->
      let target = list_mk_comb
        (`sha256hash_loop`,
         [mk_small_numeral index; x; y; w]) in
      let claim = mk_conj
        (mk_eq(SAIL_HL_ARM_SHA256_TUPLE_PROJECTION 4 value,
               SAIL_HL_ARM_SHA256_HALF 128 target),
         mk_eq(SAIL_HL_ARM_SHA256_TUPLE_PROJECTION 5 value,
               SAIL_HL_ARM_SHA256_HALF 0 target)) in
      try let theorem = prove(claim,SAIL_HL_ARM_SHA256_ROUND_TAC) in
          [state_theorem; GEN_ALL(CONJUNCT1 theorem);
           GEN_ALL(CONJUNCT2 theorem)]
      with Failure _ -> try_inputs rest in
  try_inputs candidates;;

let SAIL_HL_ARM_SHA256_ROUND_PROJECTIONS =
  flat(mapi (fun index value ->
    SAIL_HL_ARM_SHA256_PROVE_ROUND (index mod 4) value)
    SAIL_HL_ARM_SHA256_SOURCE_ROUNDS);;
(* Reconstruct each actual exported tuple using proved observable
   projections. The other three fields retain their original projections;
   no instruction effect or temporary calculation is replaced in the model. *)
let SAIL_HL_ARM_SHA256_SIX_ETA = prove
 (`!p:S#A#B#C#D#E.
   p = (FST p,FST(SND p),FST(SND(SND p)),FST(SND(SND(SND p))),
        FST(SND(SND(SND(SND p)))),SND(SND(SND(SND(SND p)))))`,
  REWRITE_TAC[PAIR]);;

let rec SAIL_HL_ARM_SHA256_TUPLE_EQUALITY = function
  | [theorem] -> theorem
  | theorem::rest ->
      let tail = SAIL_HL_ARM_SHA256_TUPLE_EQUALITY rest in
      let pair = mk_pair(lhs(concl theorem),lhs(concl tail)) in
      let constructor = rator(rator pair) in
      MK_COMB(AP_TERM constructor theorem,tail)
  | [] -> failwith "empty round tuple";;

let SAIL_HL_ARM_SHA256_RECONSTRUCT value =
  let fields = map (fun index ->
    let projection = SAIL_HL_ARM_SHA256_TUPLE_PROJECTION index value in
    if mem index [0;4;5] then
      GEN_REWRITE_CONV I SAIL_HL_ARM_SHA256_ROUND_PROJECTIONS projection
    else REFL projection) [0;1;2;3;4;5] in
  GEN_ALL(TRANS (ISPEC value SAIL_HL_ARM_SHA256_SIX_ETA)
    (SAIL_HL_ARM_SHA256_TUPLE_EQUALITY fields));;

let SAIL_HL_ARM_SHA256_RECONSTRUCTIONS =
  map SAIL_HL_ARM_SHA256_RECONSTRUCT SAIL_HL_ARM_SHA256_SOURCE_ROUNDS;;
assert(length SAIL_HL_ARM_SHA256_RECONSTRUCTIONS = 8);;

let SAIL_HL_ARM_SHA256_RECONSTRUCT_LET_CONV tm =
  let assignments,_ = dest_let tm in
  if length assignments = 1 &&
     type_of(fst(hd assignments)) = SAIL_HL_ARM_SHA256_ROUND_TYPE
  then (SUBLET_CONV(GEN_REWRITE_CONV I SAIL_HL_ARM_SHA256_RECONSTRUCTIONS)
          THENC let_CONV) tm
  else let_CONV tm;;

let SAIL_HL_ARM_SHA256_RECONSTRUCT_CONV =
  TOP_DEPTH_CONV(CHANGED_CONV(FIRST_CONV
    [SAIL_HL_ARM_SHA256_RECONSTRUCT_LET_CONV; BETA_CONV;
     GEN_REWRITE_CONV I [FST;SND]]));;

let SAIL_HL_ARM_SHA256_RECONSTRUCT_TAC definitions =
  REPEAT GEN_TAC THEN
  (* Unfold only the applied source definition. REWRITE_TAC also applies
     global basic rewrites inside its body, changing source assertions
     such as T /\ T before the actual-round equalities can match. *)
  CONV_TAC (LAND_CONV
    (RATOR_CONV(RATOR_CONV(GEN_REWRITE_CONV I [hd definitions])) THENC
     RATOR_CONV BETA_CONV THENC BETA_CONV)) THEN
  CONV_TAC (LAND_CONV SAIL_HL_ARM_SHA256_RECONSTRUCT_CONV) THEN
  REWRITE_TAC(tl definitions @ [assign; QREG'; sha256h; sha256h2;
    sha256hash; NUM_OF_INT_OF_NUM; LET_DEF; LET_END_DEF]);;
(* Prove SHA512 hash-round and schedule agreement with the generated model.
   Claims retain all vector register fields and overlaps under the declared
   register boundary; compiler and full-platform preservation are not proved. *)
let SAIL_HL_ARM_SHA512_TAC definitions =
  REPEAT GEN_TAC THEN
  REWRITE_TAC(definitions @
    [assign; LET_DEF; LET_END_DEF; FST; SND; QREG'; NUM_OF_INT_OF_NUM;
     DIMINDEX_32; DIMINDEX_64; DIMINDEX_128; DIMINDEX_256]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC INT_REDUCE_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC SAIL_HL_ARM_SHA2_ROTATE64_COUNTS THEN
  REWRITE_TAC[SAIL_HL_ARM_SHA2_READ_HIGH; SAIL_HL_ARM_SHA2_READ_LOW;
    SAIL_HL_ARM_SHA2_HIGH_KEEPS_LOW; SAIL_HL_ARM_SHA2_LOW_KEEPS_HIGH;
    SAIL_HL_ARM_SHA2_OVERWRITE_HIGH; SAIL_HL_ARM_SHA2_OVERWRITE_LOW;
    SAIL_HL_ARM_SHA2_COMPLETE_HIGH_LOW; SAIL_HL_ARM_SHA2_COMPLETE_LOW_HIGH;
    WORD_XOR_ASSOC; WORD_ADD_ASSOC];;

let SAIL_HL_ARM_SHA512H128_EQ = prove
 (`!d n m:5 word. !s t:armstate.
    sail_hl_ARM_5fSHA512H128 d n m s t <=>
    arm_SHA512H (QREG' d) (QREG' n) (QREG' m) s t`,
  SAIL_HL_ARM_SHA512_TAC
    [sail_hl_ARM_5fSHA512H128; arm_SHA512H; sha512h]);;

let SAIL_HL_ARM_SHA512H2128_EQ = prove
 (`!d n m:5 word. !s t:armstate.
    sail_hl_ARM_5fSHA512H2128 d n m s t <=>
    arm_SHA512H2 (QREG' d) (QREG' n) (QREG' m) s t`,
  SAIL_HL_ARM_SHA512_TAC
    [sail_hl_ARM_5fSHA512H2128; arm_SHA512H2; sha512h2]);;

let SAIL_HL_ARM_SHA512SU0128_EQ = prove
 (`!d n:5 word. !s t:armstate.
    sail_hl_ARM_5fSHA512SU0128 d n s t <=>
    arm_SHA512SU0 (QREG' d) (QREG' n) s t`,
  SAIL_HL_ARM_SHA512_TAC
    [sail_hl_ARM_5fSHA512SU0128; arm_SHA512SU0; sha512su0]);;

let SAIL_HL_ARM_SHA512SU1128_EQ = prove
 (`!d n m:5 word. !s t:armstate.
    sail_hl_ARM_5fSHA512SU1128 d n m s t <=>
    arm_SHA512SU1 (QREG' d) (QREG' n) (QREG' m) s t`,
  SAIL_HL_ARM_SHA512_TAC
    [sail_hl_ARM_5fSHA512SU1128; arm_SHA512SU1; sha512su1]);;

List.iter sail_hl_report [
  "SAIL_HL_ARM_SHA512H128_EQ", SAIL_HL_ARM_SHA512H128_EQ;
  "SAIL_HL_ARM_SHA512H2128_EQ", SAIL_HL_ARM_SHA512H2128_EQ;
  "SAIL_HL_ARM_SHA512SU0128_EQ", SAIL_HL_ARM_SHA512SU0128_EQ;
  "SAIL_HL_ARM_SHA512SU1128_EQ", SAIL_HL_ARM_SHA512SU1128_EQ;
];;

(* All instruction calculations come from the original typed exports.
   Native representation facts expose the same four-round/lane structure. *)
let SAIL_HL_ARM_SHA256_TAC definitions =
  REPEAT GEN_TAC THEN
  REWRITE_TAC(definitions @
    [assign; LET_DEF; LET_END_DEF; FST; SND; QREG'; NUM_OF_INT_OF_NUM;
     sha_choose; sha_maj; sha_hash_sigma_0; sha_hash_sigma_1; elem;
     DIMINDEX_32; DIMINDEX_64; DIMINDEX_128; DIMINDEX_256]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC INT_REDUCE_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC(SAIL_HL_ARM_SHA2_ROTATE32_COUNTS @
    SAIL_HL_ARM_SHA2_ROTATE256_COUNTS) THEN
  SIMP_TAC[WORD_SUBWORD_INSERT_INNER; WORD_SUBWORD_INSERT_OUTER;
    DIMINDEX_128; ARITH] THEN
  REWRITE_TAC[SAIL_HL_ARM_SHA256_FULL32; SAIL_HL_ARM_SHA256_FULL64;
    SAIL_HL_ARM_SHA256_FULL128; SAIL_HL_ARM_SHA2_FIRST_TWO;
    SAIL_HL_ARM_SHA2_COMPLETE_FOUR; SAIL_HL_ARM_SHA2_TOP_WORD;
    SAIL_HL_ARM_SHA256_PROJECT_X; SAIL_HL_ARM_SHA256_PROJECT_Y;
    WORD_XOR_ASSOC; WORD_ADD_ASSOC];;

let SAIL_HL_ARM_SHA256SU0128_EQ = prove
 (`!d n:5 word. !s t:armstate.
    sail_hl_ARM_5fSHA256SU0128 d n s t <=>
    arm_SHA256SU0 (QREG' d) (QREG' n) s t`,
  SAIL_HL_ARM_SHA256_TAC
    [sail_hl_ARM_5fSHA256SU0128; arm_SHA256SU0;
     sha256su0; sha256su0_loop]);;

let SAIL_HL_ARM_SHA256SU1128_EQ = prove
 (`!d n m:5 word. !s t:armstate.
    sail_hl_ARM_5fSHA256SU1128 d n m s t <=>
    arm_SHA256SU1 (QREG' d) (QREG' n) (QREG' m) s t`,
  SAIL_HL_ARM_SHA256_TAC
    [sail_hl_ARM_5fSHA256SU1128; arm_SHA256SU1;
     sha256su1; sha256su1_loop0; sha256su1_loop1]);;

let SAIL_HL_ARM_SHA256H128_EQ = prove
 (`!d n m:5 word. !s t:armstate.
    sail_hl_ARM_5fSHA256H128 d n m s t <=>
    arm_SHA256H (QREG' d) (QREG' n) (QREG' m) s t`,
  SAIL_HL_ARM_SHA256_RECONSTRUCT_TAC
    [sail_hl_ARM_5fSHA256H128; arm_SHA256H]);;

let SAIL_HL_ARM_SHA256H2128_EQ = prove
 (`!d n m:5 word. !s t:armstate.
    sail_hl_ARM_5fSHA256H2128 d n m s t <=>
    arm_SHA256H2 (QREG' d) (QREG' n) (QREG' m) s t`,
  SAIL_HL_ARM_SHA256_RECONSTRUCT_TAC
    [sail_hl_ARM_5fSHA256H2128; arm_SHA256H2]);;

List.iter sail_hl_report [
  "SAIL_HL_ARM_SHA256H128_EQ", SAIL_HL_ARM_SHA256H128_EQ;
  "SAIL_HL_ARM_SHA256H2128_EQ", SAIL_HL_ARM_SHA256H2128_EQ;
  "SAIL_HL_ARM_SHA256SU0128_EQ", SAIL_HL_ARM_SHA256SU0128_EQ;
  "SAIL_HL_ARM_SHA256SU1128_EQ", SAIL_HL_ARM_SHA256SU1128_EQ;
];;
check_axioms ();;
print_endline "SAIL_HOL_LIGHT_ARM_SHA2_PROOFS_OK";;
