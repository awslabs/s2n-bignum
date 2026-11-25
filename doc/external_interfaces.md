# Proving compiled code that calls things outside it

A shared library calls code that is not part of it (the C library, the
allocator) and relies on the dynamic loader to fill in addresses. We do not
model that code. Instead each outside thing gets a *contract*: a statement of
what it does that our theorems take as a hypothesis. This file says how each
kind of outside dependency is handled. Everything here is generic: it is used
by the snappy proofs (`arm/snappy`) but mentions nothing specific to them.

## 1. The loader and relocations

**Decision:** state, as a hypothesis, the memory contents the loader leaves
behind, generated mechanically from the ELF file.

- The code and read-only data are loaded at a base address `pc` (aligned to
  4096). The proofs are about the bytes of the binary at `pc`.
- The loader also fills in the writable data segment: table slots holding
  addresses inside the library (e.g. vtables), and slots holding the
  addresses of imported functions (the GOT). `tools/elf_relocs.py` reads the
  relocation table and writes the list of all these slots as (address,
  value) pairs, the value being `pc + offset` or `imp "name"` (the address of
  the imported function `name`, left as an unknown).
- `common/elf_image.ml` states "memory holds these values" and gives each
  slot as a fact to the proof tactics.
- We require the library to be linked with `-z now -z relro`: then every slot
  is filled before any library code runs and is read-only afterwards, so the
  hypothesis is true from the start and nothing in the library can change it.
  Theorems also assume the program writes nothing there.

## 2. Calls to imported functions

**Decision:** step through the PLT stub, then use the callee's contract.

A call `bl memcpy@plt` jumps to a three-instruction stub that loads the GOT
slot and jumps there. The proof runs the stub, reads the slot's value
`imp "memcpy"` from the fact of section 1, and then applies the contract of
the function at that address. Tactics: `arm/proofs/libc.ml`
(`ARM_BSTEP_PLT_TAC` and friends).

## 3. C library functions (memcpy, memmove, memset)

**Decision:** a fixed contract per function, in three strengths.

A contract says: given arguments that satisfy its conditions (e.g. memcpy's
buffers do not overlap), the function returns to the caller with the right
bytes in the destination, and changes nothing except the destination and the
registers the calling convention lets it clobber. It also says the function
uses no stack and reads only its arguments and its own code and data, a
region the caller promises not to write. The three forms
(`common/libc_contracts.ml`, `arm/proofs/libc.ml`):

- correctness only;
- correctness plus memory safety: every memory access is inside the buffers
  given and the function's own region;
- additionally, constant time: which addresses are accessed depends only on
  the public inputs.

A caller's theorem assumes the form it needs. memcpy, memmove and memset of
glibc, musl and bionic on AArch64 meet these (no stack use, no other memory).

## 4. The heap (malloc/free, new/delete)

**Decision:** an abstract allocator described by a few properties, with
hidden state, shown satisfiable by a small allocator we prove.

The allocator keeps private data in memory, and blocks it hands out live in
the same address space, so a fixed list of "memory it may change" does not
work. Instead (`common/heap.ml`, `common/footprint.ml`, `arm/proofs/heap.ml`):

- The proof tracks the list `H` of blocks currently handed out (it exists
  only in the proof).
- The allocator owns a set of addresses `heap_fp H` (its private data and
  free memory). It is left unknown; we only know it never overlaps a block
  in `H`.
- Its internal consistency is an unknown property `heap_ok H` of the
  contents of `heap_fp H`. Since it depends only on that memory, any write
  the caller makes elsewhere, including into its own blocks, preserves it
  automatically.
- `new n` (when `heap_room H n` says there is room) returns a fresh block of
  n bytes taken from `heap_fp H`, aligned and non-zero, adds it to `H`, and
  changes only memory in `heap_fp H`, the ABI-volatile registers, and at most
  `stk` bytes of stack. `delete p` needs `p` in `H`, removes it, and changes
  only `heap_fp H` and the freed block.
- These properties are bundled as `heap_model ...`, which a caller's theorem
  takes as a hypothesis. To make sure the hypothesis is not impossible to
  meet (which would make the theorem empty), `arm/heap/heap_slab.S` is a real
  allocator proved to satisfy it, with a non-trivial `heap_room`.
- A caller's result states `heap_ok` with its new `H`; returning with the
  same `H` means nothing leaked.

## 5. Calls through function pointers and vtables

**Decision:** no separate abstraction. The pointer's value comes from a slot
of section 1 (or from a register the proof already knows), so the target is
a known address in the image, and the proof continues into that code or uses
its proved contract.

## 6. Code that never returns (error and exception helpers)

**Decision:** prove the call unreachable under the theorem's hypotheses,
rather than model it.

## Supporting tools

- `common/relative.ml`, `tools/native_link.py`: each function is proved
  against the contracts of its callees, and a link step replaces each
  contract by its proof. Contracts not yet proved can be left open only by
  naming them (`--open`), and the link prints them, so a theorem never
  silently depends on an unproved one.
- `tools/elf_layout.py`, `tools/elf_names.py`, `tools/elf_transcribe.py`,
  `tools/elf_check_transcription.py`: names for the addresses in a binary and
  a byte-for-byte checked transcription of it.
