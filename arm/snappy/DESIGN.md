# Design notes for the snappy proofs

Companion to `README.md` (status, build, interfaces, what the theorems
say). This file records the designs of the proofs and the pitfalls met.
Anything marked **contract** is an interface between proofs (a statement
that other proofs assume, or a convention that they rely on): change it only
together with them. The labels DECOMP-A, DECOMP-B, COMP1, COMP2 name the
parts of the work as they were split up while the proofs were developed:
DECOMP-A the validator side of the decompressor (header, RefillTag, the
validator, the C entry points other than `snappy_uncompress`), DECOMP-B the
array writer (the fast loop, `DecompressAllTags<SnappyArrayWriter>`,
`RawUncompress`, `snappy_uncompress`; B2 IncrementalCopy, B3 the callers),
COMP1 `InternalCompress` and above with `CompressFragment`, COMP2
`CompressFragmentDoubleHash`.

## 0. Base and environment

- The work is based on s2n-bignum's `main` with `common/par.ml` (the
  parallel proof jobs), the bstep symbolic execution engine
  (`common/bstep.ml`), and from the mlkem-native / mldsa-native work the
  AArch64 instruction models it added, `common/relative.ml`,
  `common/layout.ml`, `tools/native_*.py` and `tools/link_costs.py`. What
  the snappy proofs needed from the mlkem-specific files was generalized
  into generic files rather than copied.
- Toolchain: OCaml 5 with camlp5, zarith and num, and HOL Light built with
  `HOLLIGHT_USE_MODULE=1` and a kernel that is safe on several domains
  (jrh13/hol-light PR 214). In `arm/`:
  `make HOLDIR=<hol-light> HOL_PAR=1 <target>.correct`, with
  `S2N_PAR_DOMAINS=N` for the link (`snappy/gcc12_O2/link.correct`). Do not
  force parallelism inside a proof; use `par_run_jobs`/`PAR_THENL` where
  parts are independent (see the header of `common/par.ml`).
- The snappy binary: `libsnappy.so` as built by `build.sh` from snappy at
  tag 1.3.1 (sha256 in `gcc12_O2/SHA256SUMS`); it is not in the
  repository.

## 1. Loaded images and relocations

The ELF file has two loadable segments:

```
 0                                   0x92dc        0x1fbb0          0x20010
 | ELF hdr | .plt | .text | .rodata |   ...   | .data.rel.ro .got .data .bss |
 +---------- RX segment -------------+         +----- RW segment (RELRO) ----+
```

The loader maps both at `pc + vaddr` for one base `pc` (aligned to the
segment alignment, at least 4096), applies the dynamic relocations, and
(with `-z now -z relro`) resolves every GOT slot before any code of the
library runs and then makes the RELRO part read-only.

**Generic part.** HOL side `common/elf_image.ml` (the predicate and the
rules to extract slots); generators in `tools/`:

- `define_from_elf` turns the transcription into a byte list. The RX
  segment from 0 to the end of `.rodata` is "the image"
  (`aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc`,
  `arm/proofs/snappy/gcc12_O2/libsnappy.ml`), transcribed by
  `tools/elf_transcribe.py` into `arm/snappy/gcc12_O2/libsnappy.S` and
  checked byte for byte by `tools/elf_check_transcription.py`.
- **contract**: the RW segment is described by the generated definition
  (`tools/elf_relocs.py`, output `arm/proofs/snappy/gcc12_O2/relocs.ml`)

  ```
  snappy_libsnappy_gcc12_O2_relocated (pc:num) (imp:string->int64)
    : (int64 # int64) list
    = [(word (pc + 0x1fbb0):int64, word (pc + 0x30f0):int64);   (* RELATIVE *)
       (word (pc + 0x1fc18):int64, imp "__cxa_pure_virtual":int64);  (* ABS64 + 0 *)
       (word (pc + 0x1ff48):int64, imp "memcpy":int64);   (* JUMP_SLOT *)
       ...]
  ```

  one pair (address of the slot, value written by the loader) per dynamic
  relocation, sorted by address: `word (pc + A)` for RELATIVE, `imp "sym"`
  for GLOB_DAT/JUMP_SLOT, `imp "sym"` or `word_add (imp "sym") (word A)`
  (`word_sub ... (word (-A))` if A < 0) for ABS64. `"sym"` is the name in
  the dynamic symbol table without its version, so mangled for C++
  (`imp "_Znwm"` is operator new). This changes the first draft here,
  which had `(num # int64)` pairs of offsets: the slot addresses are given
  as the `word (pc + off)` terms that the step tactics produce for an
  ADRP+LDR, so a slot fact is used without arithmetic. The predicate of
  `common/elf_image.ml` (CONTRACTS) over such a list `l` says that every
  slot holds its value. It has two forms (both generic in the state type
  and the memory component `m`):

  ```
  elf_relocated m s l <=> ALL (\(a,v). read (m :> bytes64 a) s = v) l
  elf_relocated_data b d l <=>
    ALL (\(a,v). word(d DIV 2 EXP (8 * val(word_sub a b))) = v) l
  ```

  The first is the plain statement, for the theorems of the entry points.
  The proofs use the second: `elf_relocated_data (word(pc + libsnappy_rw))
  rw (snappy_libsnappy_gcc12_O2_relocated pc imp)` as a hypothesis and
  `read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s =
  rw` in the precondition, the same pattern as the region `(ea,el)` with
  contents `ev` of the external contracts. *Reason for the change from
  the first draft* (`elf_relocated` in the precondition): it would have
  to be proved again in the state of every call of an in-image function
  whose theorem has it, slot by slot from facts that every step would
  have to carry; the one fact about `rw` is carried by the step tactics
  like any other and matches the callee's precondition as it is, and the
  hypothesis is state-free. `ENSURES_ELF_RELOCATED` (or
  `ENSURES_ELF_RELOCATED_TAC b n`) turns a theorem in the second form into
  one in the first, given `elf_slots_within b n l` (proved by
  `ELF_SLOTS_WITHIN_CONV ~defs:[<lib>_relocated]`), so the entry points
  are stated with `elf_relocated memory s (<lib>_relocated pc imp)`.

  `ELF_RELOCATED_DATA_TAC ~defs:[<lib>_relocated] ~select` (or
  `ELF_RELOCATED_TAC` for the first form) adds the selected slots as
  facts `read (memory :> bytes64 (word_add (word pc) (word off))) s0 = v`,
  the address form in which `ARM_STEPS_TAC` and bstep look memory up
  (the normal form of the ADRP+LDR address); `elf_slots_importing
  ["memcpy"]` and `elf_slots_at [off]` select (each fact costs at every
  step of `ARM_STEPS_TAC`, so select only the slots the code reads).

  The list says nothing about the unrelocated bytes of the segment
  (vtable offset-to-top and RTTI words, which are 0 with -fno-rtti, and
  `.dynamic`); no code of the library reads them.
- Every theorem that reads the RW segment also assumes it is disjoint from
  every region the code writes (as the precedent does for the GOT); RELRO
  is the justification, stated in the README's trusted base. Its extent
  is `libsnappy_rw`/`libsnappy_rw_size` (0x1fbb0, 0x460 as loaded) and
  `libsnappy_relro`/`libsnappy_relro_size` (0x1fbb0, 0x450) in the layout.
  State it as disjointness of the written regions from `(word pc,
  libsnappy_rw + libsnappy_rw_size)`, the whole span of the library (it
  covers the image, the gap between the segments, which the loader
  reserves, and the slots): the step tactics then carry the slot facts
  across every write by the nonoverlapping facts that they derive for a
  subregion `word_add (word pc) (word off)` of an assumption about
  `word pc`.
- ADRP under bstep: when the goal has `aligned 4096 (word pc)`, bstep's
  step theorems (made once per address for the goals with that fact,
  `arch_base_facts` in `arm/proofs/bstep.ml`) give the page that ADRP
  computes as `word_add (word pc) (word k')`, the form of
  `IMAGE_ADRP_TAC`, so a block goes on through an ADRP and the LDR from
  its page (e.g. through a PLT stub to the GOT slot). `ARM_ADRP_FACT_TAC`
  is only for a fact made otherwise.
- Calls under bstep: `ARM_BSTEP_CALL_TAC` goes through a contract after a
  block, also for a tail call (`b` to a function whose contract returns to
  X30), and composes the frames when they are given by name
  (`MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`, `bstep_frame_defs`), so
  neither the caller nor the contract needs to unfold the frame.

**Layout names** (`tools/elf_layout.py`, output
`arm/proofs/snappy/gcc12_O2/layout.ml`; **contract** for all proofs):

- C++ functions: demangled, without `snappy::`/`snappy::internal::`,
  parts joined by `_`: `ByteArraySource_Peek`, `SnappyDecompressor_RefillTag`,
  `CompressionContext_ctor__voidp_ulong`, `Sink_dtor`,
  `Sink_deleting_dtor`; template arguments appended:
  `SnappyDecompressor_DecompressAllTags_SnappyArrayWriter` (also
  `_SnappyIOVecWriter`, `_SnappyDecompressionValidator`,
  `_SnappyScatteredWriter_SnappySinkAllocator`), `DecompressBranchless_charp`,
  `DecompressBranchless_ulong`; overloads only get `__` and their parameter
  types: `RawCompress__charp_ulong_charp_ulongp`,
  `RawCompress__charp_ulong_charp_ulongp_CompressionOptions`,
  `GetUncompressedLength__charp_ulong_ulongp`,
  `GetUncompressedLength__Sourcep_uintp`, `Compress__Sourcep_Sinkp`, ...
  (the full scheme is in the header of `tools/elf_names.py`; the listing of
  each function in layout.ml gives its C++ name).
- C functions get the prefix `c_` (`c_snappy_uncompress`,
  `c_snappy_max_compressed_length`, ...), so that `snappy_*` stays free for
  the HOL constants of the specification (a layout name cannot also be a
  constant).
- `f` and `f_size` for each function, labels `f_loopK`, `f_loopK_exit`,
  `f_joinK`, `f_after_<callee>[_N]`, `f_after_blr[K]` (after an indirect
  call), `f_adrpK`, `f_ret[K]`, ... (header of layout.ml).
- `plt_<g>` (16 bytes) and `got_<g>` for the imports, with C++ imports
  named the same way: `plt_memcpy`, `plt_memmove`, `plt_memset`,
  `plt_operator_new`, `plt_operator_new_array`, `plt_operator_delete`,
  `plt_operator_delete_array`, `plt_string_resize`, `plt_string_M_append`,
  `plt_throw_bad_alloc`, `plt_throw_length_error`,
  `plt_throw_out_of_range_fmt`, `plt_cxa_pure_virtual`.
- `ztv_<C>` (address and size of the `_ZTV` symbol) and `vtable_<C>` =
  `ztv_<C>` + 16, the vptr value, for `C` in `ByteArraySource`,
  `UncheckedByteArraySink`, `SnappyIOVecReader`, `Source`, `Sink`.
- `got_ztv_<C>`: the GOT slot holding `word (pc + ztv_<C>)`, and
  `got_SnappySinkAllocator_Deleter`.
- `rodata_<d>` for the tables (`rodata_kLengthMinusOffset`,
  `rodata_pattern_generation_masks`, ...), `libsnappy_size`, and
  `libsnappy_<sec>`/`libsnappy_<sec>_size` for `init`, `plt`, `text`,
  `fini`, `rodata`.

**Consequences for proofs**

- A call `bl plt_memcpy` executes the PLT stub (`adrp x16; ldr x17,[x16,..];
  add x16..; br x17`); the `ldr` reads `got_memcpy`, which is `imp "memcpy"`
  by the hypothesis, and the contract of memcpy is stated about the
  function at `imp "memcpy"`.
- A virtual call on a snappy-owned object (`ByteArraySource` on the stack):
  the constructor stores `word (pc + vtable_ByteArraySource)`. This is not
  computed by ADRP/ADD, as the first draft here said: the -fPIC code loads
  `word (pc + ztv_ByteArraySource)` from the RELATIVE slot
  `got_ztv_ByteArraySource` (`adrp; ldr x, [x, #4056]`) and adds 16. The
  call loads a slot of the vtable, which by the hypothesis is
  `word (pc + <method offset>)`, and the proof continues into the
  in-image method (or uses its proved contract) after `blr`
  (`f_after_blrK` is the return address).

**Image tools** (`arm/proofs/utils/loaded_image.ml`, `common/loaded_image.ml`):
`ARM_MK_EXEC_RANGES_RULE <image> [layout_range "f"]` (decode only the code
simulated), `ADRP_WITHIN_BOUNDS_ALIGNED`, `IMAGE_CONST_RULE_FOR` (as
`SNAPPY_IMAGE_CONST_RULE` in libsnappy.ml) and `IMAGE_ADRP_TAC` for tables in
`.rodata`. `snappy/gcc12_O2/image_decodes.correct` checks that every word of
`.init`, `.plt`, `.text` and `.fini` decodes.

**Proof files** (scheme of `common/relative.ml`): `arm/proofs/snappy/gcc12_O2/
<f>_spec.ml` and `<f>_proof.ml`, with `<f>` a lower-case snake name of the
function (`max_compressed_length`, `c_max_compressed_length`); theorems
`SNAPPY_<F>_GCC12_O2_IMAGE_SUBROUTINE_CORRECT` (and `_SAFE`), stated with
`aligned 4096 (word pc:int64) /\ pc + libsnappy_size <= 2 EXP 64` and
`read PC s = word (pc + <layout name>)`. After adding files, in `arm/`:
`python3 ../tools/native_proofs_mk.py snappy gcc12_O2 >
snappy/gcc12_O2/proofs.mk` and `python3 ../tools/native_link.py snappy
gcc12_O2 > proofs/snappy/gcc12_O2/link.ml`; `make
snappy/gcc12_O2/link.correct` checks the build (every proof file's theorems
are closed, as the snappy family has no designated API list).

## 2. External function contracts

Generic, in `common/libc_contracts.ml` (the five forms of a contract, made
from one description of a function and an ABI record, with the
implications between them) and `arm/proofs/libc.ml` (the AArch64 ABI,
`memcpy`, `memmove`, `memset`, and the call tactics).

- `memcpy`, `memset` as in `mlkem_native_libc.ml`, plus `memmove` (overlap
  allowed: the destination gets the source's old contents); all three
  also state the result `C_RETURN s = dst`.
- For each function `<f>`: `<f>_contract` (correctness), `<f>_safe_contract`
  (memory safety only: `?e2. read events s = APPEND e2 e /\
  memaccess_inbounds e2 R W` with no claim that `e2` is a function of
  public values), `<f>_correct_safe_contract` (both in one ensures, for
  callers whose accesses depend on the outputs), `<f>_safety_contract`
  (the precedent's constant-time form) and `<f>_full_contract` (all);
  `<F>_FULL_CONTRACT`, `<F>_CORRECT_SAFE_CONTRACT`, `<F>_SAFETY_CONTRACT`
  give the weaker ones from the stronger.
- Assumption stated in `arm/proofs/libc.ml`: the implementations use no
  stack (true of glibc's, musl's and bionic's AArch64 memcpy, memmove and
  memset); they may change X0-X17, X18, X30, the flags and the
  caller-saved SIMD state.
- Call tactics through the PLT: `ARM_PLT_STUB_TAC` + `ARM_PLT_CALL_TAC`
  (`ARM_STEPS_TAC`, generalizing `LIBC_PLT_TAC`/`LIBC_CALL_TAC`),
  `ARM_PLT_CT_CALL_TAC` (constant-time contracts), and with bstep
  `ARM_BSTEP_PLT_TAC execth th ilist sname` (stub, then the contract `th`
  through `ARM_BSTEP_CALL_TAC`); `MEMSAFE_EVENTS_TAC` ends a memory-safety
  proof.
- Contracts are stated for a function at an address `f` (`imp "memcpy"`,
  read from the GOT slot) and, as in the precedent, for a fixed region
  `(ea,el)` of the callee's own code/data with fixed contents `ev` that
  callers do not write.
- Usage, as in `arm/proofs/snappy/gcc12_O2/plt_calls.ml` (and
  `arm/proofs/plt_demo.ml` for a whole function with two calls and its
  memory safety): hypotheses `memcpy_contract (imp "memcpy") ea el ev`
  and `elf_relocated_data (word(pc + libsnappy_rw)) rw
  (snappy_libsnappy_gcc12_O2_relocated pc imp)`, precondition facts
  `read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s =
  rw` and `read (memory :> bytes(ea,el)) s = ev`; in the proof, after
  `ENSURES_INIT_TAC "s0"`,
  `ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
  ~select:(elf_slots_importing ["memcpy"])`, then bstep up to and
  including the `bl`, then `USE_THEN "H_MEMCPY" (fun th ->
  ARM_BSTEP_PLT_TAC EXEC th [`read X0 s`; `read X1 s`; `read X2 s`;
  `x:num`; `read X30 s`] "s<n>")` with the contract unfolded
  (`REWRITE_RULE[memcpy_contract]`) and labelled `H_MEMCPY`; `EXEC` must
  decode the stub (`layout_range "plt_memcpy"`). The regions written must
  be disjoint from `(word pc, libsnappy_rw + libsnappy_rw_size)` and
  `(ea,el)`.

## 3. The heap

Interface for `operator new`, `operator new[]`, `operator delete`,
`operator delete[]` (and `malloc`/`free`), generic so any binary can use
it. Implemented and proved (see the files below); this section is the
**contract**.

**Abstract model** (`common/heap.ml`). An allocator is three parameters
that client theorems quantify over, plus a stack bound:

- `H : (int64 # num) list`, the live blocks (address, size), ghost state.
  `new` puts the new block in front; `heap_remove p H` drops the first
  block at address `p`, so allocating and then freeing a block gives back
  `H` itself (`HEAP_REMOVE_CONS`): "no leak" is `H' = H`.
- `heap_ok : (int64 # num) list -> (int64 -> byte) -> bool`, the
  invariant, applied to **the memory at the footprint**:
  `heap_ok H (read (memory :> footprint (heap_fp H)) s)`. So it depends
  only on the memory in `heap_fp H` by construction, and it is a fact of
  the form `P (read c s)` that bstep (and `frame_keeps`) carry through any
  code or call whose writes are outside `heap_fp H`: there is no separate
  "depends only on" property and no per-instruction or per-segment lemma.
- `heap_fp : (int64 # num) list -> int64 -> bool`, the addresses the
  allocator owns when `H` is live: its code and static data (so there is
  no separate `(ea,el,ev)` region as for memcpy: `heap_ok` asserts them),
  its metadata, the free memory and any memory it may obtain later (mmap,
  sbrk: for glibc, everything not used by the rest of the process). It is a
  function of `H` only.
- `heap_room : (int64 # num) list -> num -> bool`, "an allocation of `n`
  bytes succeeds when `H` is live" (D3 made precise), a function of `H` and
  `n` only.
- `stk : num`, a bound on the stack the functions use below the SP of the
  call (glibc's malloc has frames and may call sysmalloc; the proposal had
  no stack in the frames, which no real allocator meets).

`heap_props heap_ok heap_fp`: when `heap_ok H m`, the blocks of `H` are
well formed (`heap_blocks`: nonzero, `val p + n < 2^64`, distinct
addresses, pairwise disjoint) and each is outside `heap_fp H`. Clients
whose inputs are live blocks get the disjointness from it
(`HEAP_BLOCK_DISJOINT`).

**Contracts** (`arm/proofs/heap.ml`), each one `ensures arm` with
correctness and memory safety together:

- `heap_new_contract heap_ok heap_fp heap_room stk f_new`: for all `H sz sp
  ra e`, if `heap_room H (val sz)` and
  `DISJOINT (memrange(word_sub sp (word stk),stk)) (heap_fp H)`: from
  `PC = f_new, SP = sp, X30 = ra, X0 = sz, events = e, heap_ok H (...)`
  it reaches `PC = ra` with `?p. X0 = p`, `p <> 0`, `aligned 16 p`,
  `val p + val sz < 2^64`, `~MEM p (MAP FST H)`,
  `memrange(p,val sz) SUBSET heap_fp H`,
  `heap_fp ((p,val sz)::H) SUBSET heap_fp H`,
  `heap_ok ((p,val sz)::H) (...)` and `?e2. events = APPEND e2 e /\
  memaccess_inset e2 R R` with `R = heap_fp H UNION stack`; frame
  `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
  MAYCHANGE [memory :> bytes(stack)] ,, MAYCHANGE [memory :> footprint
  (heap_fp H)]`.
- `heap_delete_contract heap_ok heap_fp stk f_delete`: (i) for `MEM (p,n)
  H` and the stack outside `heap_fp H UNION memrange(p,n)`, from `X0 = p`
  it returns with `heap_ok (heap_remove p H) (...)`,
  `heap_fp (heap_remove p H) SUBSET heap_fp H UNION memrange(p,n)` and the
  events within `heap_fp H UNION memrange(p,n) UNION stack`; the frame is
  that of new plus `MAYCHANGE [memory :> bytes(p,n)]` (free-list links in
  the freed block). (ii) From `X0 = 0` it keeps `heap_ok H`.
- `heap_model heap_ok heap_fp heap_room stk f_new f_delete` = `heap_props`
  and the two contracts. Client theorems take it as a hypothesis,
  universally quantified over `heap_ok heap_fp heap_room stk`, with a
  numeral bound `stk <= K` of their choice. `new[]`/`delete[]` and
  `malloc`/`free` are further `heap_model`s with the same `heap_ok`,
  `heap_fp`, `heap_room`; sized `operator delete(void*, size_t)` meets the
  delete contract (it does not read X1).
- Memory safety is the set form `memaccess_inset e rs ws`
  (`common/footprint.ml`: every load within `rs`, every store within
  `ws`), with `MEMACCESS_INBOUNDS_INSET` from the list form. There is no
  `e2 = f_events ...` clause: the allocator's events depend on its state,
  not only on public values, so client theorems are safety-only.

**Frames** (`common/footprint.ml`). The proposed `MAYCHANGE_SET fp` is the
component `footprint t` of a memory (`read` gives the memory at `t` and a
fixed value elsewhere, `write` changes only `t`):
`MAYCHANGE [memory :> footprint t]` is an ordinary clause, so `,,`,
`MAYCHANGE_STARTER`, `SUBSUMED_*`, `frame_keeps`, `maychange_absorb`,
bstep's per-write frame check and `GEN_BSTEP_CALL_TAC` all apply. A new
relation would have needed a parallel version of each. Two extension
points (`orthogonality_extensions` in `common/components.ml`,
`maychange_absorb_extensions` in `common/relational.ml`, the only changes
to existing files) let the frame machinery prove, from the set facts among
the component assumptions (`memrange(a,k) SUBSET t`, `s SUBSET t`,
`DISJOINT (memrange(a,k)) t`, `DISJOINT s t`; chains of SUBSET; UNION;
parts of regions at numeral offsets):

- a byte region (`bytes`, `bytes8..256`, `bytelist`) outside `t` is
  orthogonal to `memory :> footprint t`; two footprints of disjoint sets
  are orthogonal; two regions on the two sides of a set are orthogonal;
- a write to a region inside `t` or to a footprint of a subset of `t` is
  absorbed into the clause `MAYCHANGE [memory :> footprint t]`.

So facts about the stack, the code and earlier blocks cross calls of new
and delete, block writes are allowed by the client's footprint clause, and
`heap_ok` crosses client code that writes only outside the footprint. With
the classic tactics, `HEAP_OK_KEEP` with `MAYCHANGE_KEEPS_TAC` does the
same from the frame of a simulated segment.

**Client view.** Hypotheses `heap_model ...`, `heap_room H n` for its
allocations, `stk <= K`, and its stack (own frame and `K` bytes for the
callees), code and inputs outside `heap_fp H` (for inputs that are live
blocks, `MEM (q,m) H` and `HEAP_BLOCK_DISJOINT`). Precondition
`heap_ok H (read (memory :> footprint (heap_fp H)) s)`, postcondition
`heap_ok H' (...)` with `H' = H` for no leak, frame with `MAYCHANGE [memory :> footprint (heap_fp H)]` (last
is cheapest) and separate stack clauses for its own frame and the
callees'. Tactics: `ARM_HEAP_NEW_TAC execth model_th "p" "s<n>"`,
`ARM_HEAP_DELETE_TAC execth model_th "s<n>"`, `ARM_HEAP_DELETE_NULL_TAC`
(they find SP, X30, X0, events and `heap_ok` in the assumptions, discharge
the side conditions, weaken the callee's stack clause to the client's
clause of the `K` bytes, go through the contract with `ARM_BSTEP_CALL_TAC`,
name the block, reduce its size to a numeral, add `DISJOINT
(memrange(p,n)) (heap_fp ((p,n)::H))`, and simplify `heap_remove`), and
`MEMACCESS_INSET_TAC` for the final events. A client allocating several
blocks in sequence states `heap_room` for the later ones over all
addresses, `!p. heap_room ((p,n1)::H) n2` (`heap_demo2`), since it cannot
name the address of the first block.

**Non-vacuity.** `?heap_ok heap_fp heap_room. heap_model ...` alone is
vacuous (`heap_ok = \H m. F` meets it, as does `heap_room = \H n. F` for
new), so the witness also shows that the invariant holds initially and
that the room allows allocations: `HEAP_MODEL_NONVACUOUS` in
`arm/heap/heap_slab.ml` for `arm/heap/heap_slab.S`, 64 slots of 64 bytes
with a bitmap, new taking a free slot (63 - clz of the complement),
delete clearing its bit; `heap_ok [] (...)` when the code is loaded and the
bitmap is 0, `heap_room H n` whenever `n <= 64 /\ LENGTH H < 64`. A bump
allocator with a no-op delete cannot meet a nontrivial `heap_room`: after
an allocation and a free `H` is `[]` again, so `heap_room [] n` must stay
true for ever, and memory must be reused. `arm/heap/heap_demo.S` is a
client (allocate 16 bytes, write, read, free) proved against the abstract
model with bstep (`HEAP_DEMO_SUBROUTINE_CORRECT`) and instantiated with
the slab allocator (`HEAP_DEMO_SLAB`); `arm/heap/heap_demo2.S` keeps two
blocks live, carries the contents of the first across the second
allocation and of the second across the release of the first
(`HEAP_DEMO2_SUBROUTINE_CORRECT`). `make heap` in `arm/` runs the three.

**Trusted base** (to state in the README): the real `operator new`/`delete`
(libstdc++ over glibc malloc) meet `heap_model` for some `heap_ok`,
`heap_fp`, `heap_room` and `stk <= K`; single thread (no other thread
calls the allocator: glibc's per-thread arenas and tcache are within
`heap_fp`, their TLS pointer is a fixed parameter); no signal handler that
allocates; allocation failure (bad_alloc) excluded by `heap_room` (D3).

**Changes from the first proposal**, and why:

1. `heap_ok` takes the memory at the footprint, not the state: property 1
   ("depends only on `heap_fp H`") holds by construction, and the fact is
   carried by bstep's general mechanism, which needs facts of the form
   `P (read c s)`; an opaque `heap_ok H s` would need a lemma at each
   block of code.
2. `MAYCHANGE_SET` became the component `footprint`, so that all the frame
   machinery applies through two extension points instead of a parallel
   frame relation.
3. The contracts allow the stack below SP (bound `stk`): glibc's malloc
   uses the stack, so the proposal's frames were not met by real code.
4. The allocator's code and data are inside `heap_fp`, which replaces the
   `(ea,el,ev)` region of the stateless contracts for it.
5. New facts in the contract of new that clients need: freshness of `p`
   (blocks of size 0 make it not follow from disjointness), no
   wrap-around (pointer comparisons), alignment; `heap_props` for inputs
   that are live blocks and for the disjointness of the new block from the
   new footprint; delete by address (`heap_remove`) and of the null
   pointer.
6. Memory safety in a set form, and without `f_events` (the allocator's
   accesses depend on its state).
7. Non-vacuity strengthened (the existential alone is vacuous), and the
   witness reuses memory (a bump allocator cannot have a nontrivial
   `heap_room` that depends on `H` only).

**Limits.** `heap_room` depends on `H` only: for an allocator with
fragmentation it must be conservative. The stack bound needs a numeral
`K` in the client. The classic tactics get the orthogonality and
`HEAP_OK_KEEP`, but no call tactic for the contracts (bstep only); the
classic frame-subsumption tactics do not know footprints.
`ARM_HEAP_DELETE_NULL_TAC` is not used by a proof yet.

**Later instances** of the same pattern (not for the first wave):
libstdc++ `std::string` (layout: data pointer, size, 16-byte local buffer
or capacity) whose `resize`/`_M_append` change `H`; snappy `Source`/`Sink`
objects with an abstract state of their streams.

## 4. Specification

`common/snappy/` (ISA-independent HOL):

- `snappy_varint`: the header (at most 5 bytes, value < 2^32) as in
  `Varint::Parse32WithLimit`.
- `snappy_decode : byte list -> byte list option`, the format of
  `format_description.txt` as this implementation accepts it, fixed by
  reading `snappy.cc` (`SnappyDecompressor::DecompressAllTags`, `RefillTag`,
  `SnappyArrayWriter`, `SnappyDecompressionValidator`): define it as a
  tag-by-tag step function over (remaining input, output so far) so the
  loop invariants of the machine-code proofs are "the code has executed
  the first k tags of the decoding".
- `snappy_max_compressed_length n` as `MaxCompressedLength`.
- HOL models of `CompressFragment` and `CompressFragmentDoubleHash` (with
  the hash function, table sizes from `CalculateTableSize`, `EmitLiteral`,
  `EmitCopy`, `FindMatchLength`) and of the block loop of `Compress`;
  lemmas: the output of the model decodes to the input (round trip), and
  its length is at most `snappy_max_compressed_length n`.

## 5. Machine-code proofs

In the scheme of `common/relative.ml`: per function, `<f>_spec.ml` and
`<f>_proof.ml` in `arm/proofs/snappy/gcc12_O2/`, one `link.ml`, generated
`proofs.mk`. Correctness was proved first, then memory safety.

### 5.1 The fragment compressors — **contract**

`InternalCompress` calls the two fragment compressors directly (`bl`), so
their theorems are contracts between the proofs: the proof of
`InternalCompress` assumes the statement of `CompressFragmentDoubleHash`
exactly as written here, and the proof of `CompressFragmentDoubleHash`
proves exactly this statement (it is closed at link time by `relative_close`, which
matches the assumption up to alpha-conversion and instantiation).

Files `compress_fragment_spec.ml` (level 1) and
`compress_fragment_double_hash_spec.ml` (level 2), each loading
`arm/proofs/snappy/relative.ml`, `arm/proofs/snappy/gcc12_O2/libsnappy.ml`,
`arm/proofs/libc.ml` and `common/snappy/snappy_compress.ml`.

The fragment is `inp` (at most 65536 bytes, `kBlockSize`), at `src`. The
model's tables have `snappy_table_size (LENGTH inp)` entries (level 1) and
two tables of half that (level 2), as `InternalCompress` passes them
(`GetHashTable` zeroes them; `table_size >> 1` for level 2, the second table
at `table + 2 * (table_size >> 1)`, but the contract allows any disjoint
second table). The output region is `snappy_max_compressed_length (LENGTH
inp) - 5` bytes at `op` (the code's over-long stores stay in it, F9): the
caller's output buffer has `snappy_max_compressed_length n` bytes for the
whole input of n bytes, and the first fragment starts after the varint of up
to 5 bytes, so a fragment region of `snappy_max_compressed_length m` bytes
would not fit in it for a single fragment (m = n); the writes of both
compressors stay below `LENGTH inp + LENGTH inp DIV 30 + 20` bytes. The
fragment compressors call `memcpy` through the PLT (the final literal), hence
the hypotheses of section 2. Pointers do not wrap (the code compares them
unsigned): the search loops compute the next probe position
`ip + (skip >> 5)` (level 1; `skip >> 9` for level 2) before comparing it
with `ip_limit`, so it may lie up to about 2 KiB beyond the end of the
input; `val src + LENGTH inp + 65536 < 2 EXP 64` covers that (FINDINGS
F10). Each function saves registers in a frame below SP (32 bytes for
level 1, 48 for level 2).

Level 2, `SNAPPY_COMPRESS_FRAGMENT_DOUBLE_HASH_GCC12_O2_IMAGE_SUBROUTINE_CORRECT`:

```
`!src inp op table table2 pc imp ea el ev rw stackpointer returnaddress.
    aligned 4096 (word pc:int64) /\
    pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\
    memcpy_contract (imp "memcpy") ea el ev /\
    elf_relocated_data (word(pc + libsnappy_rw)) rw
      (snappy_libsnappy_gcc12_O2_relocated pc imp) /\
    aligned 16 stackpointer /\
    LENGTH inp <= 65536 /\
    val src + LENGTH inp + 65536 < 2 EXP 64 /\
    val op + (snappy_max_compressed_length (LENGTH inp) - 5) < 2 EXP 64 /\
    PAIRWISE nonoverlapping
     [op,(snappy_max_compressed_length (LENGTH inp) - 5);
      table,2 * (snappy_table_size (LENGTH inp) DIV 2);
      table2,2 * (snappy_table_size (LENGTH inp) DIV 2);
      word_sub stackpointer (word 48),48] /\
    ALLPAIRS nonoverlapping
     [op,(snappy_max_compressed_length (LENGTH inp) - 5);
      table,2 * (snappy_table_size (LENGTH inp) DIV 2);
      table2,2 * (snappy_table_size (LENGTH inp) DIV 2);
      word_sub stackpointer (word 48),48]
     [src,LENGTH inp; word pc,libsnappy_rw + libsnappy_rw_size; ea,el]
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
              read PC s = word(pc + CompressFragmentDoubleHash) /\
              read SP s = stackpointer /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [src; word(LENGTH inp); op;
                           table; word(snappy_table_size (LENGTH inp) DIV 2);
                           table2; word(snappy_table_size (LENGTH inp) DIV 2)]
                          s /\
              read (memory :> bytes(word(pc + libsnappy_rw),
                                    libsnappy_rw_size)) s = rw /\
              read (memory :> bytes(ea,el)) s = ev /\
              read (memory :> bytelist(src,LENGTH inp)) s = inp /\
              read (memory :> bytes(table,
                      2 * (snappy_table_size (LENGTH inp) DIV 2))) s = 0 /\
              read (memory :> bytes(table2,
                      2 * (snappy_table_size (LENGTH inp) DIV 2))) s = 0)
         (\s. read PC s = returnaddress /\
              C_RETURN s =
              word_add op (word(LENGTH(snappy_compress_fragment 2 inp))) /\
              read (memory :> bytelist
                     (op,LENGTH(snappy_compress_fragment 2 inp))) s =
              snappy_compress_fragment 2 inp)
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
          MAYCHANGE [memory :> bytes(op,snappy_max_compressed_length
                                          (LENGTH inp) - 5);
                     memory :> bytes(table,
                       2 * (snappy_table_size (LENGTH inp) DIV 2));
                     memory :> bytes(table2,
                       2 * (snappy_table_size (LENGTH inp) DIV 2));
                     memory :> bytes(word_sub stackpointer (word 48),48)])`
```

Level 1, `SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT`, is the
same with one table: drop `table2` (quantifier, regions, argument, zero
fact, frame), the table has `2 * snappy_table_size (LENGTH inp)` bytes,
`C_ARGUMENTS [src; word(LENGTH inp); op; table;
word(snappy_table_size (LENGTH inp))]`, PC `CompressFragment`, the stack
frame is `word_sub stackpointer (word 32),32` and the result is
`snappy_compress_fragment 1 inp`.

Memory safety, `..._IMAGE_SUBROUTINE_SAFE` (both levels): the caller's
later accesses depend on the returned end pointer, so this is correctness
and safety in one `ensures` (the `correct_safe` form of section 2): the
same statement with `!e` added in front of the quantifiers,
`memcpy_correct_safe_contract` in place of `memcpy_contract`, `read events s
= e` as the last conjunct of the precondition and, as the last conjunct of
the postcondition,

```
?e2. read events s = APPEND e2 e /\
     memaccess_inbounds e2
      [src,LENGTH inp; <the written regions, in the order above>;
       word pc,libsnappy_rw + libsnappy_rw_size; ea,el]
      [<the written regions, in the order above>]
```

where the written regions are those of the frame (output, table(s),
stack).

### 5.2 The proof of CompressFragment

By cut points with a measure (`common/ensures_measure.ml`,
`ENSURES_MEASURE_INDUCT`), in `compress_fragment_lib.ml` (definitions,
tactics, statements), `compress_fragment_seg{15,2,4,6}_proof.ml` (one
theorem per cut point, each stated in its `_spec.ml` and a job of its own in
the link) and `compress_fragment_proof.ml` (the contract of 5.1).

- The cut points are the loop headers that correspond to the phases of the
  model `snappy_cf1_step`: loop1 (phase 1), loop3 (6, one probe of the
  unrolled search), loop4 (2, after the check against ip_limit), loop6 (4)
  and join4 (5). `snappy_cf1_mach ... st s`: s is at the cut point of the
  model state st (registers as functions of st, the input, the table as
  `!j. j < ts ==> read (memory :> bytes16 (table + 2 j)) s = word(t1 j)`,
  the output so far as `bytes(op,LENGTH out) = num_of_bytelist out`).
  `snappy_cf1_cut ... n s`: s is at the cut point of the model state after
  some k steps, with potential `snappy_cf1_pot` n. A segment goes from a cut
  point to the end or to the cut point of a state j >= 1 steps later
  (`SNAPPY_CF1_CUT_INTRO`; the potential decreases by the model's
  `SNAPPY_CF1_STEP`), so the measure rule applies and the end is
  `snappy_compress_fragment 1 inp` by `SNAPPY_COMPRESS_FRAGMENT_1`.
- Inner loops that are not phases of the model (loop5, the 16-byte copy of
  a literal; loop7/loop8 of FindMatchLength; loop9 of EmitCopy) are lemmas
  from their header to their exit with a narrow frame, gone through with
  `ARM_BSTEP_CALL_TAC`.
- The level-2 compressor can follow the same scheme with
  `snappy_cf2_step` and its potential.

Practical points of bstep found on the way (also in the tactics of the
lib): abbreviations must be made in the assumptions too
(`SNAPPY_ABBREV_TAC`); a load from the input needs its fact before the
block (`SNAPPY_LOAD_TAC`), else its value reads the state at the start of
the block, whose input fact is gone after it; a table entry at a computed
index needs the index register rewritten to `word(2 * h)` (end the block
after the `and`) and the table fact split at h before and joined after a
store (`SNAPPY_TABLE_SPLIT_TAC`, `SNAPPY_TABLE_JOIN_TAC`); the frame check
of a store at an offset uses the arithmetic assumptions only if the offset
has a free variable of type num, so abbreviate `LENGTH out`; terms in
SUBGOAL_THEN need type annotations for variables shared with the goal.

### 5.3 The proof of CompressFragmentDoubleHash

The model `snappy_cf2_step` (`common/snappy/snappy_compress.ml`) is a small-step
machine; `SNAPPY_COMPRESS_FRAGMENT_2` says that the fragment's output is the
output of any run of it that has reached phase 0. The proof relates the code
to the reachable states of the model (`snappy_cf2_reach`), at seven points:

| point | offset | phase | what holds besides the common state |
|---|---|---|---|
| `loop1` | +0x44 | 1 | `x1` = ip |
| `loop2` | +0x68 | 2 | the probe's bound checked: `x8` = ip, `x16` = Load64(ip), `x4` = its table2 entry, `x17` = ip + skip/512, `w18` = skip + 1, `x1` = next_emit |
| `join4` | +0x158 | 7 | `x8` = ip, `x14` = candidate, `w4` = length, `x1` = next_emit, `x16` = ip_end - 8 |
| `loop4` | +0x180 | 7 | the same, the backtracking's bound checked |
| `join5` | +0x190 | 3 | the same |
| `loop5` | +0x1e0 | 4 | `x8` = ip, `x14` = candidate, `w4` = length, `x16` = ip_end - 8 |
| `join2` | +0xdc | 5 | `x0` = `x2` = op, `x1` = ip |

`snappy_cf2_at ... pt st s` (`compress_fragment_double_hash_model_spec.ml`)
is the machine state at point `pt` for the model state `st`: the stack frame
with the caller's x29, x30, x19, x20 (and x21 in its register), the constants
of the main loop (base, mask, ip_limit, ip_end, the multipliers), the input,
the two tables as `snappy_tval ts t` (the 2 * ts bytes as a number, entry j
at bits 16j), the output so far, the relocated data and memcpy's region, and
the events since the start within the regions of the SAFE statement. Each
piece of code from a point (other than `join2`) is proved to reach a point
whose model state is reachable and has a smaller potential
`snappy_cf2_pot` (it does one or more steps of the model); `join2` returns
with the output of the model. The pieces put together by
`ENSURES_MEASURE_INDUCT` and the start (`init`) give the theorems; the same
pieces serve both, since the events are in the invariant, and only `join2`
(memcpy) has two forms, with `memcpy_contract` and with
`memcpy_correct_safe_contract`. The five inlined copies of
FindMatchLengthPlain are proved once each (`..._fml_spec.ml`) and used by the
pieces through their contracts.

Files (`arm/proofs/snappy/gcc12_O2/`): `compress_fragment_double_hash_model_spec.ml`
(the definitions and the tactics of the pieces), `..._fml_spec.ml` /
`..._fml_proof.ml`, `..._<point>_spec.ml` / `..._<point>_proof.ml` for the
points and `init`, and `compress_fragment_double_hash_{spec,proof}.ml` for
the two theorems of section 5.1. The word-level lemmas are in
`common/snappy/snappy_compress_word.ml` (tables, hashes as the code computes
them, FindMatchLength's 8-byte comparisons, the model's reachable states).

## 6. Clients of the heap

The functions of snappy that use the allocator, proved against the model of
section 3 through the PLT, and the conventions that their callers (COMP, T2)
rely on. **contract** where marked.

**Glue** (`arm/proofs/heap_plt.ml`, generic):

- `ARM_BSTEP_PLT_HEAP_NEW_TAC execth model_th "p" "s<n>"`,
  `ARM_BSTEP_PLT_HEAP_DELETE_TAC`, `ARM_BSTEP_PLT_HEAP_DELETE_NULL_TAC`:
  from the goal at the PLT stub (after the block that ended with `bl
  plt_operator_new`, or the `b` of a tail call), the stub
  (`ARM_BSTEP_PLT_STUB_TAC`, which reads the GOT slot fact of `_Znwm` /
  `_ZdlPv` from `ELF_RELOCATED_DATA_TAC`) and the contract of new or
  delete (`ARM_HEAP_NEW_TAC`, ...). The client's hypothesis is
  `heap_model heap_ok heap_fp heap_room stk (imp "_Znwm") (imp "_ZdlPv")`
  (**contract**; the array forms would be a second model with `_Znam`,
  `_ZdaPv`; snappy's code uses only the scalar ones). The delete tactic
  first adds `DISJOINT (memrange(p,n)) (heap_fp H)` for the blocks with a
  `MEM (p,n) H` assumption (`HEAP_BLOCK_DISJOINT_TAC`): a frame with the
  clauses of delete's frame, `footprint (heap_fp H) ,, bytes(p,n)`, needs it
  to absorb the frame of a call (found by the first client, the destructor).
- `ARM_BSTEP_CONTRACT_TAC execth th ilist "s<n>"`: `ARM_BSTEP_PLT_CALL_TAC`
  for callees with heap hypotheses (SUBSET/DISJOINT by the footprint rules,
  `nonoverlapping` in the DISJOINT form, alignment at a numeral offset,
  numeric bounds), with the assumptions `val x = t` rewritten into the
  instance, and with the byte regions of the callee's frame weakened to the
  caller's clauses that contain them (`arm_frame_weaken`): bstep absorbs a
  region only into a clause of the same region or a footprint.
- `HEAP_BLOCK_NONZERO_TAC` (live blocks are not 0, for a `cbz`),
  `MEMACCESS_INBOUNDS_TO_INSET_TAC` (libc events in the set form),
  `FOOTPRINT_SUBSET_TAC`, `ENSURES_DROP_EVENTS_TAC` (a `_CORRECT` from the
  `_SAFE` of the same statement), `CMP_HI_TAC` (`arm/proofs/utils/
  compare_branch.ml`: the flag conditions of `cmp #imm; b.hi/b.ls` as `k <
  val x`, so that a case split decides the branch).
- `memrange_subset_rule` (`common/footprint.ml`) now reduces lengths that
  are sums of numerals: a slot `word_add (word pc) (word 130944)` is inside
  `memrange(word pc, libsnappy_rw + libsnappy_rw_size)` only after the sum is
  a numeral, and without that a GOT slot or the RW segment did not cross a
  call of new or delete.

**Statements** (**contract** for callers):

- The heap's footprint is disjoint from the whole library
  `memrange(word pc, libsnappy_rw + libsnappy_rw_size)` (image, gap, RW
  segment and slots), from the stack (own frame and callees' area), and from
  the objects that the function writes; blocks that the function frees are
  in the same hypotheses as `heap_fp H UNION memrange(p,n)`.
- Saved registers are ghosts: the frame has `MAYCHANGE [SP; X19; ...; X30]`
  (and `X18` with the allocator or libc in it) and the postcondition
  `read SP s = sp /\ read X19 s = x19 /\ ...`; callers instantiate them
  with the values at the call.
- The stack of a function that calls the allocator is two clauses, its own
  frame `bytes(word_sub sp (word F),F)` and the callees' area
  `bytes(word_sub sp (word (F+C)),C)`, so that the facts about its own frame
  cross the calls; the allocator's stack is `stk <= 1024` (part of the
  trusted base, section 3).
- `_SAFE` theorems are correctness and memory safety in one `ensures`
  (`read events s = e` in the precondition, `?e2. ... memaccess_inset e2 R W`
  in the postcondition), as the heap contracts are; `_CORRECT` is derived
  from it by `ENSURES_DROP_EVENTS_TAC`. Callers use the `_SAFE` forms.
- The objects (`arm/proofs/snappy/objects.ml`, LP64 C++ ABI):
  `snappy_working_memory wm mem n owns s` (mem_, size_ =
  `snappy_working_memory_size n`, owns_mem_, table_ = mem, input_ = mem +
  `snappy_working_memory_input n`, output_ = mem +
  `snappy_working_memory_output n`) and `snappy_compression_context cc wm
  owns s`; preconditions give only the fields that the code reads.
  The sizes are in `common/snappy/snappy_working_memory.ml`, on
  `snappy_table_size` and `snappy_max_compressed_length` of the SPEC model.

**Results** (in `arm/proofs/snappy/gcc12_O2/`, all with `_SAFE` and
`_CORRECT` unless noted):

| Function | Theorem(s) | Heap |
|---|---|---|
| `WorkingMemory::RequiredSize` | `SNAPPY_WORKING_MEMORY_REQUIRED_SIZE_...` | none |
| `WorkingMemory(size_t, char*)` | `..._CTOR_ULONG_CHARP_...` | none |
| `WorkingMemory(size_t)` | `..._CTOR_ULONG_...` | `(mem, snappy_working_memory_size n)` added in front of H |
| `~WorkingMemory` | `..._DTOR_OWNED_...`, `..._DTOR_BORROWED_...` | owned: `heap_remove mem H` |
| `WorkingMemory::GetHashTable` | `..._GET_HASH_TABLE_...` (memset through the PLT) | none |
| `MaxCompressedLength` | `..._SAFE` added | none |
| `CompressionContext::WorkspaceSize` | `..._WORKSPACE_SIZE_...` = 48 + size 65536 | none |
| `CompressionContext(void*, size_t)` | `..._CTOR_VOIDP_ULONG_...` | none |
| `CompressionContext()` | `..._CTOR_VOID_...` | `(mem,size 65536) :: (wm,48) :: H` |
| `CompressionContext::Reset`, `~CompressionContext` | `_OWNED_`, `_BORROWED_`, `_NULL_` | owned: `heap_remove wm (heap_remove mem H)` |
| `CompressionContext(CompressionContext&&)` | `..._CTOR_MOVE_...` | none (ownership moves) |
| `CompressionContext::operator=(&&)` | `_SELF_`, `_NULL_` (to an empty context) | none |

CalculateTableSize is inlined (no separate function). `WorkingMemory(size_t)`
calls `std::__throw_bad_alloc` only if RequiredSize(n) >= 2^63; RequiredSize
is at most 207562 for every n (`SNAPPY_WORKING_MEMORY_SIZE_BOUND`), so the
path is unreachable for every input (proved: the branch is decided by
`~bit 63`), and the failure of operator new is excluded by `heap_room` (D3).
GetHashTable's CalculateTableSize takes a `uint32_t`: the table has
`snappy_table_size (val n MOD 2 EXP 32)` entries.

**T2: compression with the heap.** Proved (`_CORRECT`, relative
to the contracts of the callees, closed at link; files in
`arm/proofs/snappy/gcc12_O2/`):

| Function | File | Theorem(s) |
|---|---|---|
| `Compress(Source*, Sink*, CompressionOptions)` | `compress_options` | `SNAPPY_COMPRESS_OPTIONS_..._CORRECT` |
| `RawCompress(const char*, size_t, char*, size_t*, CompressionOptions)` | `raw_compress_options` | `SNAPPY_RAW_COMPRESS_OPTIONS_..._CORRECT` |
| `RawCompress(const char*, size_t, char*, size_t*)` (level 1) | `raw_compress` | `SNAPPY_RAW_COMPRESS_..._CORRECT` |
| `snappy_compress` | `c_compress` | `SNAPPY_C_COMPRESS_..._CORRECT`, `..._TOO_SMALL_..._CORRECT` |
| `snappy_compress_with_level` | `c_compress_with_level` | `..._CORRECT`, `..._INVALID_LEVEL_...`, `..._TOO_SMALL_...` |

The statements (**contract** for callers): the hypothesis `heap_model heap_ok
heap_fp heap_room stk (imp "_Znwm") (imp "_ZdlPv")`, `stk <= 1024`,
`heap_room H (snappy_working_memory_size (LENGTH inp))` (D3), level 1 or 2,
`LENGTH inp < 2 EXP 32`, the output region of `snappy_max_compressed_length`
bytes; `heap_fp H` disjoint from the library, the whole stack area, the
output, the length cell, the input and `(ea,el)`; precondition `heap_ok H`,
postcondition the output `snappy_compress level inp`, the length, and
`heap_ok H` with the same `H` (no leak). Frames: standard ABI registers (the
callee-saved ones and SP are preserved, by `ENSURES_MAYCHANGE_PRESERVED`, not
ghosts), the output, the length, the stack as the own frame plus the
callees' area, and `footprint (heap_fp H)` last. Stack: Compress 96 + 1056,
RawCompress 96 + 1152, the C functions 64 + 1248. The C theorems for a
too-small buffer or an invalid level have no heap, no output and only the
64-byte frame; the level is the int in the low 32 bits of x2 (`word_zx lv:
int32`, any upper bits). The output corollaries (round trip and bound) are
`SNAPPY_C_COMPRESS_OUTPUT` and `SNAPPY_C_COMPRESS_WITH_LEVEL_OUTPUT`;
`SNAPPY_COMPRESS_NONEMPTY` shows the result is never INVALID_INPUT from the
length check after RawCompress.

How the heap is carried in `Compress`: the block `(p,n)` of
`WorkingMemory(size_t)` gets `MEM (p,n) ((p,n)::H)` and
`HEAP_BLOCK_DISJOINT_TAC` (so `heap_ok ((p,n)::H)` crosses InternalCompress,
whose theorem has no heap terms and writes the block), then `~WorkingMemory`
(OWNED) and `HEAP_REMOVE_CONS`.

Practical points: `ARM_BSTEP_CONTRACT_TAC` weakens a callee's stack regions
only when the goal's frame is a list of `MAYCHANGE` clauses (rewrite
`MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI` in the goal first), only for
clauses with one region (`MAYCHANGE_CONS_SEQ` on the callee's frame), and
into the first clause of the goal that contains the region, so a frame whose
facts must survive must be a clause apart (Compress: saved registers at
sp - 96 and the WorkingMemory at sp - 48 are two clauses). A callee instance
with objects at offsets of SP needs `NORMALIZE_RELATIVE_ADDRESS_CONV` (bstep
keeps facts as `word_add base (word n)`). Facts that must cross a frame with
`footprint (heap_fp ((p,n)::H))` and `bytes(p,n)` need their DISJOINT facts
stated directly (the search does not chain two SUBSET steps). Branches:
`BSTEP_SPLIT_PC_TAC` and the case closed by rewriting its condition with the
state-free facts (the 64-bit and 32-bit carry lemmas `SNAPPY_CC_CARRY`,
`SNAPPY_CCL_CARRY32_1`).

Not done: `Compress(Source*, Sink*)` (a tail call with level 1, not on
the path of these entry points); `RawCompressFromIOVec`.

### 6.1 Memory safety of the compressor

`_SAFE` theorems (correctness and the events in one `ensures`, section 2's
correct_safe form) of `CompressFragment` (5.1, list form
`memaccess_inbounds`), `InternalCompress`, `Compress(ctx)`, `RawCompress(ctx)`,
`snappy_max_compressed_length` and the heap clients `Compress(opts)`,
`RawCompress(opts)`, `RawCompress`, `snappy_compress`,
`snappy_compress_with_level` (set form `memaccess_inset`, the read set
containing the write set; with the heap, `heap_fp H` is in both, and the
working memory's block is in it by the contract of new). The callees' `_SAFE`
contracts are used, the level-2 one being the statement of 5.1. The `_CORRECT` statements are unchanged: they assume
`memcpy_contract`, which says nothing about memcpy's accesses, so they cannot
come from the `_SAFE` ones (which assume `memcpy_correct_safe_contract`):

- CompressFragment: the cut-point predicates always carry the events
  (`snappy_cf1_ev` in `snappy_cf1_mach`); only the segment that calls memcpy
  (SEG5, emit_remainder) is proved twice (`_CORRECT` with the end
  `snappy_cf1_done`, `_SAFE` with `snappy_cf1_done_safe`), the other segments
  are stated for any end predicate `D`; `_CORRECT` is then derived from a
  version with `read events s = e` in the precondition
  (`SNAPPY_CF1_CORRECT_EVENTS`) by `ENSURES_DROP_EVENTS_TAC`.
- The other functions run the same tactics twice; a call takes the `_SAFE`
  contract of the callee when the hypotheses have memcpy's correct_safe
  contract (InternalCompress: `SNAPPY_IC_MP_SPEC_TAC`).

Tactics (`arm/proofs/snappy/events.ml`, `events_inset.ml`): at the end of a
path, `SNAPPY_EVENTS_TAC` (list form) / `SNAPPY_INSET_EVENTS_TAC` (set form)
prove `?e2. read events s = APPEND e2 e /\ ...`: each address of a step is
split into a base and a numeric offset (`snappy_addr_split`, also
`word_add t (word (2^64 - m))` as offset `x - m`), and is inside the region of
the same base by arithmetic on the facts that share atoms with the bound, in
stages (`SNAPPY_EV_ARITH_TAC`; `snappy_ev_bounds` adds facts for terms of the
goal); the list of a callee is within by its own regions
(`MEMACCESS_INBOUNDS_CONTAINED`, `MEMACCESS_INSET_MONO`).
`SNAPPY_EV_FIRST_TAC`/`SNAPPY_INSET_FIRST_TAC` prove the events conjuncts of a
goal first and rewrite them to `T`, so that the tactics of the correctness
proof run on the goal as before. In long paths (CompressFragment's loop6
segment) the events grow into large terms (the jumps hold the branch
conditions) and the proof ran out of memory: `SNAPPY_EV_CHECKPOINT_TAC` after
each block proves the events so far and replaces them by a new variable.
The decision procedure for linear arithmetic numbers the atoms by genvar,
so with many facts its cost depends on what the proof did before: the
`_SAFE` proof of the loop6 segment, unchanged otherwise, took more than 48 GB
in an `ARITH_TAC` with 38 facts that the `_CORRECT` proof had passed. The
arithmetic of the CompressFragment tactics now uses the facts that share
atoms with the goal first (`SNAPPY_ARITH_TAC` of the lib, all facts only as
a last try, not in seg4), and the branch refutation of seg4 only those facts.
A callee instance that is normalized (`NORMALIZE_RELATIVE_ADDRESS_CONV`,
rewrites) must have the events of the call put in after the normalization
(a variable first), else its precondition `read events s = e` no longer
matches the fact.

## 7. Decompressor interfaces

**contract** between the proofs of DECOMP-A and DECOMP-B. Files: `arm/proofs/snappy/decompressor_objects.ml`
(objects), `common/snappy/snappy_decompressor.ml` (notions and their
relation to `snappy_format.ml`), spec files in
`arm/proofs/snappy/gcc12_O2/`. Only the flat-buffer case is covered: the
reader is snappy's own `ByteArraySource`, built on the stack by the
`const char*` entry points (a user `Source`, tier T4, is not covered).

**Objects** (offsets read off the code of gcc 12 -O2, and as the LP64
Itanium ABI gives them):

- `ByteArraySource` (24 bytes): +0 vptr = `word(pc + vtable_ByteArraySource)`,
  +8 `ptr_`, +16 `left_`. Built by `IsValidCompressedBuffer`/`RawUncompress`
  as `stp x2, x0, [sp, #56]; str x3, [sp, #72]` with x2 = the RELATIVE slot
  `got_ztv_ByteArraySource` + 16. Vtable slots (relocs.ml, 0x1fc80..):
  +0 dtor, +8 deleting dtor, +16 `Available` (0x75c0), +24 `Peek` (0x75d0),
  +32 `Skip` (0x75e0). Predicate
  `snappy_byte_array_source src vptr p l s`.
- `SnappyDecompressor` (48 bytes): +0 `reader_`, +8 `ip_`, +16 `ip_limit_`,
  +24 `ip_limit_min_maxtaglen_`, +32 `peeked_`, +40 `eof_` (byte), +41
  `scratch_[5]` (RefillTag: `ldp x1, x20, [x0, #8]`, `ldr x1, [x21, #32]`,
  `strb w0, [x21, #40]`, `add x23, x21, #0x29`; DecompressAllTags: `str x2,
  [x0, #24]`). The constructor and `ReadUncompressedLength` are inlined:
  `InternalUncompress<Validator>` builds it at sp+96 (`stp x0, xzr, [sp, #96];
  str xzr, [sp, #112]; str xzr, [sp, #128]; strb wzr, [sp, #136]`), i.e.
  reader_ = r, ip_ = ip_limit_ = 0, peeked_ = 0, eof_ = false (the +24 field
  is not initialized). Predicate
  `snappy_decompressor d reader ip lim peeked eof s` (without +24 and the
  scratch).
- `SnappyDecompressionValidator` (16 bytes): +0 `expected_`, +8 `produced_`
  (`str x20, [x23]` in InternalUncompress; `ldr x22, [x19, #8]`, `ldr x1,
  [x19]` in DecompressAllTags).
- `SnappyArrayWriter` (32 bytes, built by `RawUncompress(Source*, char*)` at
  sp+96): +0 `base_`, +8 `op_`, +16 `op_limit_`, +24 `op_limit_min_slop_`
  (`stp x1, x1, [sp, #96]; stp x1, x1, [sp, #112]`, later `stp x21, x20,
  [sp, #112]`). DECOMP-B owns this one.

**Notions** (`common/snappy/snappy_decompressor.ml`):
`snappy_tag_needed c` = CalculateNeeded(c) (1 for a literal of at most 60
bytes, `c DIV 4 - 58` for c >= 240 with c MOD 4 = 0, 2, 3, 5 for the
copies); `snappy_refill_ok rest <=> ~(rest = []) /\ snappy_tag_needed (HD
rest) <= LENGTH rest`. Lemmas: `SNAPPY_TAG_NEEDED_BOUNDS` (1..5),
`SNAPPY_TAG_STEP_SHORT`, `SNAPPY_DECODE_TAGS_SHORT` (`~(rest = []) /\
~snappy_refill_ok rest ==> snappy_decode_tags m rest out = NONE`).

**ByteArraySource methods** (`byte_array_source_{available,peek,skip}_spec.ml`,
`SNAPPY_BYTE_ARRAY_SOURCE_{AVAILABLE,PEEK,SKIP}_GCC12_O2_IMAGE_SUBROUTINE_{SAFE,CORRECT}`),
leaf functions, frame `MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI` plus the
memory written, no stack; the memory written must not overlap the image
(`nonoverlapping (np,8) (word pc,libsnappy_size)` for Peek, `(src+8,16)` for
Skip):

- `Available`: `C_ARGUMENTS [src]`, `bytes64(src+16) = l` ==> `C_RETURN = l`;
  reads `(src+16,8)`, writes nothing.
- `Peek`: `C_ARGUMENTS [src; np]`, `bytes64(src+8) = p`, `bytes64(src+16) =
  l` ==> `C_RETURN = p`, `bytes64 np = l`; reads `(src+8,16)`, writes
  `(np,8)`.
- `Skip`: `C_ARGUMENTS [src; n]` ==> `bytes64(src+8) = word_add p n`,
  `bytes64(src+16) = word_sub l n`; reads and writes `(src+8,16)`.

A caller reaches them with `blr` through the vtable: the slot is in the RW
segment, so `ELF_RELOCATED_DATA_TAC ~select:(elf_slots_at [0x1fc90;
0x1fc98; 0x1fca0])` gives the slot facts. Their code is short enough to be
stepped through instead (include `layout_range "ByteArraySource_Peek"`
etc. in the EXEC theorem).

**RefillTag** (`snappy_decompressor_refill_tag_spec.ml`, read the header
there for the full statement), two theorems, correctness and memory
safety in one `ensures`, frame 80 bytes, saved registers as ghosts
(`MAYCHANGE [SP; X18; X19; ...; X24; X29; X30]`), memmove through the PLT
with the hypothesis `memmove_correct_safe_contract (imp "memmove") ea el
ev`, writes `bytes(d,41)` (the fields), `bytes(d+41,5)` (scratch_; two
clauses so that facts about the fields cross a call of memmove into
scratch_), `bytes(src+8,16)` and the frame:

The vptr in both is stated as `word_add (word pc) (word
vtable_ByteArraySource)`, the normal form of addresses of bstep, so that
the loads of the vtable slots (`ldr x2, [x2, #24]`) meet the slot facts of
`ELF_RELOCATED_DATA_TAC` (with `word (pc + vtable_ByteArraySource)` they do
not); a caller that has the vptr as the constructor stores it (`word_add
(word (pc + 0x1fc70)) (word 16)`) rewrites it with `WORD_RULE`.

- `SNAPPY_DECOMPRESSOR_REFILL_TAG_EMPTY_GCC12_O2_IMAGE_SUBROUTINE_SAFE`:
  `ip_ = ip_limit_ = ip`, `peeked_ = word k`, the source at `(p, word n)`,
  `k <= n < 2^64`, `rest` = the `n - k` bytes at `p + k`. Returns
  `word(bitval(snappy_refill_ok rest))`, `eof_ = word(bitval(rest = []))`;
  for `r = n - k`: if `r < 5` the source is at `(p + n, 0)`, `peeked_ = 0`,
  scratch_ holds rest, and on success `ip_ = d + 41`, `ip_limit_ = d + 41 +
  r`; if `r >= 5`, `ip_ = p + k`, `ip_limit_ = p + n`, `peeked_ = r`, the
  source at `(p + k, r)`.
- `SNAPPY_DECOMPRESSOR_REFILL_TAG_WINDOW_GCC12_O2_IMAGE_SUBROUTINE_SAFE`:
  `ip_ = ip`, `ip_limit_ = ip + LENGTH w` holding the bytes `w <> []`,
  `peeked_ = left_ = n` (all peeked), `eof_ = 0`. Returns
  `word(bitval(snappy_refill_ok w))`, `eof_` stays 0; if `LENGTH w >= 5`
  nothing changes; else as EMPTY with `rest = w` (the source at `(p + n,
  0)`, `peeked_ = 0`, scratch_ = w, on success `ip_ = d + 41`).

With a ByteArraySource the stitching loop of RefillTag (memcpy) only runs
its test: after the peeked bytes are skipped the source is empty. So with
the flat input `(q, len)` (the bytes after the header) the decompressor is
always in one of these states, which are the loop states of
DecompressAllTags:

| state | ip_, ip_limit_ | peeked_ | source | RefillTag |
|---|---|---|---|---|
| start | 0, 0 | 0 | (q, len) | EMPTY with k = 0 |
| buffer | q + i, q + len | len | (q, len) | WINDOW if i < len, EMPTY (k = n, eof) if i = len |
| scratch | d + 41 + j, d + 41 + r | 0 | (q + len, 0) | WINDOW if j < r, EMPTY (eof) if j = r |

(buffer is entered when at least 5 bytes are left, scratch with the last
r < 5 bytes; after a false return the decompressor is only used for eof_
and the destructor.) The slow literal loop of DecompressAllTags (`while
(avail < literal_length)`: Skip(peeked_), Peek) finds the source empty in
both states and exits; the destructor (inlined) is `reader_->Skip(peeked_)`.

**ReadUncompressedLength** is inlined (into `InternalUncompress<Validator>`,
`RawUncompress(Source*, char*)` and `GetUncompressedLength(Source*,
uint32_t*)`): a loop of at most 5 iterations, each a virtual Peek (fail if
it gives 0 bytes), a load of the byte c, a virtual Skip(1), the check
`(c & 0x7f) & LeftShiftOverflows_masks[shift]` (the table is
`rodata_LeftShiftOverflows_masks` = 0x7dc0, reached as
`rodata_pattern_generation_masks + 0x200`; entries 0 for shift 0, 7, 14, 21
and 0xf0 for 28), `result |= (c & 0x7f) << shift`, exit if c < 128, fail
after 5 bytes. With a ByteArraySource at `(p, l)` holding the bytes `b`:
it succeeds iff `snappy_varint b = SOME(m, b')` (F5), then `*result = m`
and the source is at `(p + h, l - h)` with `h = LENGTH b - LENGTH b'`; on
failure the source has moved by at most 5 bytes and the result is not
used. There is no separate contract (no function); each caller proves the
loop (DECOMP-A for the validator and GetUncompressedLength(Source*),
DECOMP-B for RawUncompress).

**Fast path of the validator.** `DecompressAllTags<SnappyDecompressionValidator>`
calls `DecompressBranchless_ulong` (0x67a0, the `size_t` instance, with
op_base = 1 and op_limit_min_slop = 2^63 - 64, FINDINGS F1, F2); it is in
DECOMP-A's scope (DECOMP-B does `DecompressBranchless_charp`).

**Other theorems of DECOMP-A**:
`SNAPPY_GET_UNCOMPRESSED_LENGTH_CHARP_ULONG_ULONGP_GCC12_O2_IMAGE_SUBROUTINE_{SAFE,CORRECT}`
(input `bytelist(inp, LENGTH l) = l`, `val n = LENGTH l`, `val inp + LENGTH
l < 2^64`, `(res,8)` outside the image: returns `word(bitval(~(snappy_header
l = NONE)))`, `!m. snappy_header l = SOME m ==> *res = word m` and
`snappy_header l = NONE ==> *res = r0`, the old value) and `SNAPPY_C_UNCOMPRESSED_LENGTH_...`
(`C_RETURN = word(snappy_uncompressed_length_status l)`).

**Results of DECOMP-A** (in `arm/proofs/snappy/gcc12_O2/`, `_SAFE` =
correctness and memory safety in one `ensures`, `_CORRECT` derived):

| Function | Theorem(s) | Status |
|---|---|---|
| `ByteArraySource::Available/Peek/Skip` | `SNAPPY_BYTE_ARRAY_SOURCE_{AVAILABLE,PEEK,SKIP}_...` | proved |
| `GetUncompressedLength(const char*, size_t, size_t*)` | `SNAPPY_GET_UNCOMPRESSED_LENGTH_CHARP_ULONG_ULONGP_...` | proved (cases L = 0..4, L >= 5; branches on the bytes split by `ARM_BSTEP_RUN_TAC`) |
| `snappy_uncompressed_length` | `SNAPPY_C_UNCOMPRESSED_LENGTH_...` | proved |
| `SnappyDecompressor::RefillTag` (ByteArraySource reader) | `SNAPPY_DECOMPRESSOR_REFILL_TAG_{EMPTY,WINDOW}_GCC12_O2_IMAGE_SUBROUTINE_SAFE` | proved (cases r = 0..4 with the tag short or not, r >= 5; memmove through the PLT, Skip/Peek stepped through the vtable) |
| `IsValidCompressedBuffer`, `snappy_validate_compressed_buffer` | `SNAPPY_IS_VALID_COMPRESSED_BUFFER_...`, `SNAPPY_C_VALIDATE_COMPRESSED_BUFFER_...` | proved relative to the contract of `InternalUncompress<Validator>`, which needs `DecompressAllTags<Validator>` (spec files stated) |
| `DecompressBranchless<size_t>` (with `MemCopy64__long_voidp_ulong`, `ClearDeferred`, `DeferMemCopy` stepped through) | `SNAPPY_DECOMPRESS_BRANCHLESS_ULONG_GCC12_O2_IMAGE_SUBROUTINE_{SAFE,CORRECT}` | proved: cut points 0x6890/0x6940 with the measure 2 (L - h) + 2/1, exit state 0x6988; per segment five tag classes, branches on data split with the case as an integer fact; model states `snappy_fast_reach` (common/snappy/snappy_validator.ml) |
| `DecompressBranchless<char*>` (MemCopy64 by its contract, `ClearDeferred`, `DeferMemCopy` stepped through) | `SNAPPY_DECOMPRESS_BRANCHLESS_CHARP_GCC12_O2_IMAGE_SUBROUTINE_{SAFE,CORRECT}` | proved (7d): cut points TAG/J/E with a measure, 33 tag leaves |

Proof tools added for this (`arm/proofs/snappy/decompressor_objects.ml`):
`ARM_BSTEP_RUN_TAC`/`ARM_BSTEP_RUN_GEN_TAC` (step one instruction at a time,
split branches on data with `BSTEP_SPLIT_PC_TAC`, close impossible cases with
`BSTEP_ARITH_KILL_TAC`, normalize values after each step, go through calls
by PC), `READ_MEMORY_BYTELIST_EL`, byte-test lemmas. Two pitfalls met:
`ARM_BSTEP_CONTRACT_TAC` weakens a callee's region to the caller's frame
clause containing it, so a callee writing part of an object loses the facts
about the rest of it unless the frame splits the object (hence the two
clauses for the decompressor); and `BITBLAST_TAC` must not see the other
assumptions (it blows up on the events).

### 7b. DECOMP-B: the array writer (status and analysis)

**Proved or stated** (`arm/proofs/snappy/gcc12_O2/`):

- `MemCopy64<64>(dst, src, size)` (`mem_copy64_{spec,proof}.ml`,
  `SNAPPY_MEM_COPY64_GCC12_O2_IMAGE_SUBROUTINE_{SAFE,CORRECT}`):
  memmove(dst, src, 32) and, if size > 32, the tail call memmove(dst + 32,
  src + 32, 32), both through the PLT. For `val size <= 64` and
  `nonoverlapping (dst,val size) (src,val size)`: the first `size` bytes at
  dst are those that were at src. It always writes 32 or 64 bytes; the
  frame is `bytes(dst,32) ,, bytes(dst + 32,32)` (one clause per memmove:
  a single `bytes(dst,64)` clause makes bstep weaken the frame of the first
  call to it, and the bytes at src + 32 then do not cross that call).
- `IncrementalCopy(op - off, op, op + n, op + b)`
  (`incremental_copy_{spec,proof}.ml`,
  `SNAPPY_INCREMENTAL_COPY_GCC12_O2_IMAGE_SUBROUTINE_{SAFE,CORRECT}`, proved,
  `_CORRECT` from `_SAFE` by `ENSURES_DROP_EVENTS_TAC`): the output so far `out` at base, op = base + LENGTH out,
  `1 <= off <= LENGTH out`, `1 <= n <= 64`, `n <= b`, `17 <= val base +
  LENGTH out + b < 2^64` and `val base + LENGTH out + 64 < 2^64`; the output
  becomes `snappy_copy off n out`, returns op + n, writes only
  `bytes(op,b)`, reads `(op - off, off + b)` and the masks in the image.
  (The bounds `< 2^64`, not `<=`: with buf_limit = 2^64 the code's pointer
  compares wrap; and for op_limit <= buf_limit - 15 the code compares
  op_limit with op + 16, op + 32, op + 48 whatever b is, so op + 64 must not
  wrap either.) The proof goes path by path with addresses relative to
  base (LENGTH out = r + off, op = base + (r + off), src = base + r) and
  carries `bytelist(base,(r + off) + c) = snappy_copy off c out` for the c
  bytes done, extended per chunk by `SNAPPY_COPY_CHUNK_STEP` (k <= off
  bytes equal to those off before) or `SNAPPY_COPY_PATTERN_STEP` (16 bytes
  of the pattern, off <= 16), cut to n by `SNAPPY_COPY_TRUNC`
  (common/snappy/snappy_memory.ml). A bstep block ends after each load that
  may read an earlier store (16-byte copies for off >= 16): the value loaded
  is then a read of the state at the start of the block, and bstep moves
  that fact to the end, so the chunk is compared within one state. The
  16-byte loops run at most 4 times there (b < n + 15 <= 79) and are
  unrolled by the range of b; the two byte loops are lemmas from their entry
  to the return (`SNAPPY_INCREMENTAL_COPY_BYTE_LOOP_A/B`, ENSURES_WHILE_UP)
  used through `ARM_BSTEP_CALL_TAC`. The masks are read from the image by
  `SNAPPY_PATTERN_MASKS_LOADED`; TBL is folded into `snappy_tbl` by giving
  `EXPAND_SIMD_RULE snappy_tbl` as a fold. Memory safety: each event's
  region, with base-relative addresses in a normal form (`IC_NORM_CONV`), is
  shown inside the regions of the spec by offset arithmetic
  (`IC_SUBSET_LEMMA`); `MEMACCESS_INSET_TAC`'s rule only knows numeral
  offsets. The loop lemmas carry the events in their invariant.

**Writes of the fast path** (from the code of `DecompressBranchless<char*>`,
0x6050; confirms FINDINGS F4 for the array writer). With `lim` =
op_limit_min_slop = m - min(63, m) (SnappyArrayWriter) the loop runs while
`op + deferred_length < lim - 64` (checked every two tags), and each tag
appends at most 64 bytes. Every write is a 64-byte store at op or at
op + deferred_length (MemCopy64 of the deferred copy, 32 or 64 bytes, and
the 64-byte pattern stores of Copy64BytesWithPatternExtension / the 4 x 16
byte copy loop for offset > 16), and every such op is below lim, so all
writes are in `[base, base + lim + 63) = [base, base + m)` when m >= 63; for
m < 63, lim = 0 and the loop is not entered (nothing is written: the
deferred length is 0). Reads of the input stay below ip_limit - 4 (the loop
runs while ip < ip_limit - 129, two tags advance ip by at most 122, and a
deferred literal reads 64 bytes from its start). The deferred-copy source
is the input, the output (a copy with offset >= length, flushed before
anything else is written), or the 64-byte uninitialized `safe_source` on
the stack with length 0 (MemCopy64 then copies 32 of its bytes as slop).
So **no write outside [out, out + m) was found**; the fast path only
decodes tags that `snappy_tag_step` accepts (offset 0 and offset >
produced break out to the slow path, the output never passes m).

**Statement of DecompressBranchless<char*>**: see 7c.

**Tools**: `arm/proofs/snappy/bstep_decide.ml` (`ARM_BSTEP_DECIDE_TAC`):
bstep through branches whose condition follows from arithmetic facts (the
pointer and length compares of compiled code); it recovers the condition
from bstep's message, proves it or its negation (`BSTEP_ARITH_DECIDE_TAC`:
values of words as numbers where there is no wrap-around, ARITH_TAC) and
reruns the block, and fails with the condition when the facts do not
decide it (a real path split).

### 7c. The fast-path contract (DECOMP-B for DECOMP-B3)

`arm/proofs/snappy/gcc12_O2/decompress_branchless_spec.ml`,
`SNAPPY_DECOMPRESS_BRANCHLESS_CHARP_GCC12_O2_IMAGE_SUBROUTINE_{SAFE,CORRECT}`
(**contract**). The call in `DecompressAllTags<SnappyArrayWriter>` (0x6420)
is `DecompressBranchless(ip, ip_limit_, op - base_, base_,
op_limit_min_slop_ - base_)`, done only if `base_ != 0`; it returns
`(ip', op' - base_)` in (X0, X1) and the caller sets `op = base_ + X1`.

- Arguments: `C_ARGUMENTS [ip; ip + LENGTH inp; word(LENGTH out); base;
  word(m - MIN 63 m)]` with the input `bytelist(ip,LENGTH inp) = inp` (the
  buffered bytes `[ip_, ip_limit_)`, in either state of the table of 7, the
  input or scratch_) and the output so far `bytelist(base,LENGTH out) = out`;
  m is the writer's buffer size (op_limit_ - base_, the uncompressed length
  of the header), `LENGTH out <= m < 2^32`, `val ip + LENGTH inp < 2^64`,
  `val base + m < 2^64`.
- Result: `?k inp' out'. snappy_steps k m (inp,out) = SOME(inp',out') /\ X0
  = ip + (LENGTH inp - LENGTH inp') /\ X1 = word(LENGTH out') /  bytelist(base,LENGTH out') = out'`. `SNAPPY_STEPS_SOME` gives inp' a
  suffix of inp (so ip <= ip' <= ip_limit_) and `SNAPPY_STEPS_DECODE_TAGS`
  that the decode from (inp', out') is that from (inp, out); the caller
  then runs its slow path from there (k may be 0).
- No deferred-copy state crosses the call: DecompressBranchless flushes its
  deferred copy (frame slots sp+160/168) before it returns; the ghost state
  of the deferred copy is only in its own proof.
- Frame: `bytes(base,m)` (slop beyond out' inside the buffer), its frame
  `bytes(sp - 240,240)` and MemCopy64's `bytes(sp - 288,48)`, `MAYCHANGE
  [SP; X18; X19..X30]` with X19..X29 and SP given back (ghosts x19..x29).
  Hypotheses: memmove's contract `(ea,el,ev)` and the RW segment `rw` as for
  MemCopy64; `(base,m)` and `(sp - 288,288)` disjoint from each other, from
  the library and from (ea,el); the input disjoint from both.
- `_SAFE`: reads in the input, `(base,m)`, the 288 bytes of stack, the image
  (`(word pc,libsnappy_size)`: kLengthMinusOffset, the pattern masks), the
  RW segment and (ea,el); writes in `(base,m)` and the 288 bytes of stack.

### 7d. The proof of DecompressBranchless<char*>

Status: **proved**. The proof was first assembled from development files by
a script; it is now maintained by hand, and split into jobs of the link:
`decompress_branchless_lib.ml` (the lemmas, the cut points, the tactics and
the statements of the leaves of the tag segment), the pattern-copy leaves
by offset in `decompress_branchless_near{1,2a,2b}_proof.ml`, a slow lemma
in `decompress_branchless_lemmas_proof.ml`, the rest and the theorems in
`decompress_branchless_proof.ml`; the table kLengthMinusOffset is
`length_minus_offset_lib.ml`'s (shared with the other decompressor
proofs). Cut points TAG (0x6140 / 0x61f0, measure 2 (L - h) + 1), J
(0x61e4, 2 (L - h) + 2) and E (0x6238, 0), the model `snappy_steps k m
(inp,out) = SOME(SUB_LIST(h,L - h) inp, APPEND ob db)` with the output ob
at base and the deferred copy db at dsrc; the tag segment from 33 leaves
(by class, and for near copies by the offset: TBL pattern copies for
offsets 1..16 with the masks of the image, the 16-byte chunk loop for
17..63); MemCopy64 by its contract. The branches that the facts decide only
by arithmetic are decided by `ARM_BSTEP_DECIDE_TAC`
(`arm/proofs/snappy/bstep_decide.ml`). The pieces it builds on: the model
of one tag at a position of the input (`SNAPPY_TAG_STEP_{LITERAL,COPY1,
COPY2}_AT`, common/snappy/snappy_decompress.ml), the in-memory copy lemmas
of 7b (the pattern path of the fast loop is the same TBL pattern as
IncrementalCopy's), and bstep runs of the prologue (ClearDeferred is
stepped through: it is in the EXEC ranges of the spec).

The design, as first written (the proof follows it):

- Cut points: 0x6140 (first tag of an iteration, w26 := 2) and 0x61f0
  (second tag, w26 := 1); measure LENGTH inp - h for the tag at position h.
  State: X19 = ip + h + 1, X27 = the tag byte EL h inp, X28 = op (bytes
  written), X8 = [sp+168] = dl (deferred length), [sp+160] = dsrc,
  [sp+104] = the table kLengthMinusOffset (pc + 0x7e00), [sp+112] =
  safe_source (sp - 64), [sp+120] = ip_limit - 129, X20 = base, X21 = lim
  - 64, X23/X24 = &dsrc/&dl, the saved registers in the frame; the model
  `snappy_steps k m (inp,out) = SOME(SUB_LIST(h,LENGTH inp - h) inp,outm)`
  with LENGTH outm = op + dl, `bytelist(base,op) = SUB_LIST(0,op) outm` and
  the deferred bytes `bytelist(dsrc,dl) = SUB_LIST(op,dl) outm`, dsrc in the
  input, in [base, base + op) (a copy with offset >= length) or the
  safe_source with dl = 0. Bounds: at 0x6140 h + 130 < LENGTH inp and op +
  dl < lim - 64; at 0x61f0 the same after one tag (ip advanced by at most
  62, op + dl < lim).
- Segments per tag (the code is branch-free up to the type dispatch):
  literal x < 60 (two code paths for delta < 0 and >= 0, both flush and
  defer the literal from the input); copy-1/2 with offset >= length (flush,
  defer the copy from base + op + dl - offset; break if that is negative);
  copy-1/2 with offset < length (flush, then the 64-byte pattern store:
  offset 1 (dup), 2/4/8/16 (one TBL), other <= 15 (TBL chain of
  IncrementalCopy, `SNAPPY_COPY_PATTERN_STEP`), > 16 (4 chunks of 16,
  `SNAPPY_COPY_CHUNK_STEP`); break for offset 0 or offset > produced);
  long literal / copy-4 (bit 7 of the table entry: break). Branch
  conditions are signed (b.gt, b.mi, ccmp): decided by the equivalences
  `WORD_SGT_FLAGS` (BITBLAST) and their numeric forms.
- One exit lemma from 0x6238 (x22 = the pointer past the tag to stop at):
  flush the deferred copy with MemCopy64 if dl > 0, ClearDeferred, restore,
  return (ip + h, op + dl).
- The kLengthMinusOffset entry of a tag byte c is `iword(snappy_lmo c)`
  with `snappy_lmo` the formula of LengthMinusOffset (checked against the
  table in the binary); a lemma over the 256 entries as for the masks.
- MemCopy64 calls write `bytes(dst,32)`, `bytes(dst+32,32)`: to keep the
  facts about the output prefix across them the internal frame should be
  `memory :> footprint(memrange(base,m))` (absorption by the SUBSET fact of
  the call's regions), weakened to `bytes(base,m)` at the end;
  `ARM_BSTEP_CONTRACT_TAC`'s weakening to the clause `bytes(base,m)` would
  drop those facts (DESIGN 7, DECOMP-A).
- The sibling `DecompressBranchless<unsigned long>` (0x67a0, 0x290 bytes,
  the validator's) has the same tag decoding and limits on numbers
  (op_base = 1; its MemCopy64 overload at 0x4670 is a bare ret): its proof
  (`decompress_branchless_ulong_proof.ml`) has the same cut points and tag
  lemmas, with the tools of the validator's segments
  (`arm/proofs/snappy/validator_segment_tools.ml`); only the output side is
  different (no memory, op only counts).

### 7e. DECOMP-B3: RawUncompress, snappy_uncompress (status)

Spec files (`arm/proofs/snappy/gcc12_O2/`), all for a flat input read by
snappy's own ByteArraySource:

- `snappy_decompressor_decompress_all_tags_snappy_array_writer_spec.ml`:
  `DecompressAllTags<SnappyArrayWriter>` from a fresh decompressor
  (`ip_ = ip_limit_`, `peeked_ = 0`, `eof_ = 0`) and writer for m bytes at
  out: at the return `?ok. eof_ = word(bitval ok) /\ (ok /\ op_ = out + m
  <=> snappy_decode_tags m inp [] <> NONE)`, and on success the m bytes at
  out are the result. Frame: the output, the decompressor's fields (d, 41)
  and scratch_ (d + 41, 5), ptr_/left_ of the source, only op_ of the
  writer, its frame (112) and the callees' area (288). **Proved** (_SAFE,
  relative to RefillTag, DecompressBranchless<char*>, IncrementalCopy,
  MemCopy64 and memcpy/memmove; see the end of this section).
- `raw_uncompress_sourcep_charp_spec.ml` (**proved** relative to
  DecompressAllTags, 3279 s: one call of its contract per header length),
  `raw_uncompress_charp_ulong_charp_spec.ml` (**proved** relative to it),
  `c_uncompress_spec.ml` (**proved** relative to GetUncompressedLength and
  RawUncompress(const char*, ...)): for any input bytes l and an output
  buffer of `*uncompressed_length = ulen` bytes, `C_RETURN =
  word(snappy_uncompress_status l (val ulen))`; on OK the output holds x
  and `*uncompressed_length = LENGTH x`; otherwise `*uncompressed_length`
  is not written; writes only `(out, val ulen)`, `(ulenp, 8)` and 704
  bytes of stack.

Hypotheses beyond the usual ones (and why):

- `17 <= val out`: IncrementalCopy (DECOMP-B2's statement) computes
  `op_limit - 17` as a pointer and needs `17 <= val base + LENGTH out + b`;
  it also makes `base_ != 0`, so DecompressAllTags always takes the fast
  path first (no `cbz base_` case).
- `LENGTH l < 2^63` (DAT: `LENGTH inp < 2^63`): ResetLimit computes
  `min<ptrdiff_t>(ip_limit_ - ip, 4)` signed; for a window of 2^63 bytes
  or more it picks the (negative) length, `ip_limit_min_maxtaglen_` becomes
  the start of the window and every tag goes through RefillTag's WINDOW
  case. The code still works, but the loop invariant of the proof (buffer
  state with `ip_limit_min_maxtaglen_ = ip_limit_ - 4`) assumes the bound.
- the input and the output do not reach the top of the address space;
  for the output `val out + m + 64 < 2 EXP 64` (DAT; the callers have
  the same with outlen/ulen): the copy fast path computes `op + 64` (and
  IncrementalCopy `op + 32`) before comparing with the limit, and with
  `op = out + m` and `out + m + 64 = 2^64` that sum wraps to 0. The
  original statement (no such bound) was false.
- `aligned 8 d` (DAT): the code compares pointers into scratch_ (d + 41
  ... d + 46), which is wrong if they wrap at 2^64; with d 8-aligned and
  the 48 bytes at d in memory they do not. RawUncompress has its
  decompressor on its own 16-aligned stack.

Conventions found necessary:

- bstep absorbs a direct store into a frame clause only if the clause's
  address has the same base as the store's (e.g. `word_add (word_sub sp
  (word 176)) (word 96)`, not `word_sub sp (word 80)`), so the frames give
  the regions on the own stack in that form.
- A callee that writes part of an object on the caller's stack: its frame
  clause is weakened to the caller's clause that contains it
  (arm_frame_weaken), so the caller's frame lists those objects as separate
  clauses (RawUncompress: saved registers, writer base_/op_, writer
  op_limit_/op_limit_min_slop_, decompressor fields, scratch_).
- A callee's postcondition fact that is not `read c s = v` (an `!x.
  ... ==> read c s = x`, an iff with a read) does not cross later code:
  either split the case first (snappy_decode l = NONE / SOME x) and
  specialize the contract (instantiate the variables in it before
  rewriting: REWRITE_RULE on a closed contract does not rewrite under its
  quantifiers), or name the reads by variables (BSTEP_GHOST_READS_TAC).
- A region whose length is not a numeral inside a caller's clause
  (`(out, m)` in `(out, outlen)`): ARM_BSTEP_CONTRACT_SUB_TAC weakens the
  callee's frame by given subset theorems. For DecompressAllTags, whose
  callees write `(op, len)` inside `(out, m)` while the facts about the
  output so far must be kept, the proof uses the frame clause
  `memory :> footprint (memrange(out,m))` (with SUBSET and DISJOINT facts
  for each write) and MAYCHANGE_FOOTPRINT_MEMRANGE_SUBSUMED at the end.

Tools in `arm/proofs/snappy/array_writer.ml`: SNAPPY_VARINT_BYTES,
READ_BYTELIST_SUFFIX, NONOVERLAPPING_{SUFFIX,PREFIX,PREFIX_RIGHT,
SUFFIX_PREFIX}, MAYCHANGE_FOOTPRINT_MEMRANGE_SUBSUMED,
ENSURES_{DISJ,EXISTS}_PRECONDITION (cut points with
ENSURES_MEASURE_INDUCT), BSTEP_GHOST_READS_TAC, BSTEP_KILL_TAC (closes the impossible case of a
branch split by ARM_BSTEP_RUN_GEN_TAC); ARM_BSTEP_CONTRACT_SUB_TAC (calls of
contracts whose frame regions are inside the caller's by SUBSET facts) is in
`arm/proofs/heap_plt.ml`. Note for goal-stack debugging of
proofs that use assume_spec contracts: `e` fails with "VALID: Invalid
tactic" (the contract hypotheses are not assumptions of the goal); use
`refine(by tac)`.

**The proof of DecompressAllTags<SnappyArrayWriter>** (done as planned;
`common/snappy/snappy_slow_path.ml` has the tag step by kind:
SNAPPY_TAG_STEP_{LITERAL,LONG_LITERAL,COPY1,COPY2,COPY4}, and the SOME/NONE
cases of snappy_literal and snappy_copy_tag). With a ByteArraySource the
decompressor is in one of two states at the cut points (DESIGN 7):
buffer (ip = q + i in the input, `ip_limit_ = q + len`,
`ip_limit_min_maxtaglen_ = q + len - 4`, `peeked_ = left_ = len`, at
least 5 bytes left) or scratch (ip = d + 41, the last r <= 4 bytes in
scratch_, `ip_limit_min_maxtaglen_ = d + 41`, the source at (q + len, 0)).
Cut points, with the model `snappy_decode_tags m inp [] =
snappy_decode_tags m rest out`, `rest` the bytes at ip (refill_ok), out the
output so far at base:

- E (entry), measure 2 len + 2: the prologue, RefillTag EMPTY (k = 0),
  then L (buffer if len >= 5, scratch otherwise) or the exit.
- L = 0x63fc (loop1), measure 2 LENGTH rest + 1: DecompressBranchless
  (always, base_ = out != 0), then (ip' < ip_limit_min_maxtaglen_) T, or
  RefillTag at 0x668c (WINDOW if ip' < ip_limit_, EMPTY at the end) then T
  or the exit.
- T = 0x6440 (the tag byte in w2/w26), measure 2 LENGTH rest: one tag of
  the slow path: literal (TryFastAppend 16-byte store; memcpy; a literal
  past the input: memcpy of what is there, Skip, Peek = 0, exit), long
  literal (1-4 length bytes, ldur + mask), copy-1/2 (kLengthMinusOffset at
  pc + 0x7e00, ldrsh), copy-4: memmove of 64 bytes when op <
  op_limit_min_slop_ and offset >= length, IncrementalCopy otherwise; then
  L directly (ip < ip_limit_min_maxtaglen_) or RefillTag at 0x64c4 / 0x66ec
  (scratch state, or the exit).

ENSURES_MEASURE_INDUCT needs `C ,, C = C` for the frame. MAYCHANGE_IDEMPOT_TAC
fails on the spec frame (ASSIGNS_SEQ_ABSORB_CONV: the byte regions of d,
wr, src, out are not provably orthogonal). Used: an internal frame with
one memory clause `memory :> footprint W`, W the union of the regions
written (stack, callees' area, d fields, scratch_, src + 8, wr + 8, out),
idempotent like a register list; bstep absorbs each write and callee
frame into it with SUBSET facts, and keeps facts across writes with
DISJOINT facts (`common/footprint.ml`); at the end a lemma
`MAYCHANGE [m :> footprint (s UNION t)] subsumed MAYCHANGE [m :> footprint
s] ,, MAYCHANGE [m :> footprint t]` (MAYCHANGE_FOOTPRINT_UNION_SUBSUMED,
FOOTPRINT_UNION_SUBSUMED_SEQ in `common/footprint.ml`) and
MAYCHANGE_FOOTPRINT_MEMRANGE_SUBSUMED give the spec frame.

The proof was first assembled from development pieces by a script; it is
now maintained by hand, as `..._snappy_array_writer_lib.ml` and one job per
segment T and tag class (`..._snappy_array_writer_t_{b,s}_<class>_proof.ml`).
One theorem per segment (E, L buffer, L scratch, T buffer,
T scratch; T is split by tag kind: literal, long literal 240/244/248/252,
copy-1, copy-2, copy-4; the scratch state cannot hold a copy-4 or a
4-byte long literal). Lessons:

- run one instruction at a time, normalise the X registers after each
  step, and decide each branch condition by arithmetic on the state-free
  facts; use only the atomic facts first (disjunctive facts make ARITH
  exponential, and can overflow the stack).
- a generic leaf tactic closes every exit and cut point: the model fact
  `snappy_decode_tags m rest out = ...` gives ok and the output; the
  memory-safety events are discharged from SUBSET facts of each access,
  derived once per region (input, output, d, stack, image).
- memcpy/memmove: state their source fact on the raw X1 address after the
  PLT stub; build the output facts with an append lemma, not by rewriting.
