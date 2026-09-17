# Instruction cosimulation tests

The instruction cosimulation tests compare one or more instructions executed
by an external backend with the corresponding HOL Light architecture model.
Each HOL worker owns one persistent backend process, so emulators are started
once per worker rather than once per instruction.

## Executor protocol

Executors use a line-oriented protocol on standard input and standard output.
Diagnostics must go to standard error.

The executor first reports its architecture and state-word count:

```text
READY 1 <architecture> <state-words> [key=value ...]
```

The client then sends requests containing hexadecimal instruction bytes and
unsigned decimal state words:

```text
RUN <hex-bytes> <state-word> ...
```

The executor answers with one of:

```text
OK <state-word> ...
TRAP [details ...]
ERROR <details ...>
```

For example, an AArch64 NOP with an all-zero input state is exchanged as
follows:

```text
HOL client                                 executor
    |                                          |
    |<--- READY 1 aarch64 128 -----------------|
    |                                          |
    |--- RUN 1f2003d5 0 ... ------------------>|
    |                                          |
    |<--- OK 0 ... ----------------------------|
    |                                          |
    |--- QUIT -------------------------------->|
    |                                          |
```

`1f2003d5` is the little-endian byte encoding of the instruction. The
ellipses abbreviate the remaining state words; they are not sent literally.

`QUIT` ends the session. The current architectures use these state vectors:

| Architecture | State words | Word size | Default executor            |
| ------------ | ----------: | --------: | --------------------------- |
| AArch64      |         128 |   64 bits | `arm/proofs/cosim-runner`   |
| x86-64       |         112 |   64 bits | `x86/proofs/cosim-runner`   |

The Arm and x86 C runners patch a bounded executable slot for every request.
They catch synchronous execution traps and remain available for the next
request.

## Test controls

The following environment variables apply to every architecture:

- `S2N_BIGNUM_SEMATEST_SECONDS` sets the wall-clock campaign limit.
- `S2N_BIGNUM_SEMATEST_CASES` sets a deterministic case-count limit.
- `S2N_BIGNUM_SEMATEST_SEED` initializes the OCaml random generator.
- `S2N_BIGNUM_EXECUTOR_TIMEOUT` sets the per-request backend timeout.

The backend command is selected independently for each architecture:

- `S2N_BIGNUM_AARCH64_EXECUTOR`
- `S2N_BIGNUM_X86_64_EXECUTOR`

Without an override, `make sematest` uses the default executor in the table
above. An override is the complete shell command used to start the executor,
not just the executable name. This permits an emulator or another execution
prefix to be placed before the runner. For example:

```sh
export S2N_BIGNUM_X86_64_EXECUTOR='qemu-x86_64 -cpu max x86/proofs/cosim-runner'
```

If the host is configured to execute foreign binaries transparently, for
example through `binfmt_misc`, no override is needed.

## Native Arm and x86-64

On a native host, build and run the corresponding test in the architecture
directory:

```sh
make -C arm HOLDIR=/path/to/hol-light sematest
make -C x86 HOLDIR=/path/to/hol-light sematest
```

`tools/run-sematest.sh` starts the configured number of HOL workers. Every
worker starts one executor session.

## Cross-building the x86-64 executor

The Arm and x86 runner rules honor `CC`, `COSIM_CFLAGS`, and
`COSIM_LDFLAGS`. Generating the x86 instruction corpus also honors `AS` and
`OBJDUMP`. To run the HOL driver on a non-x86 host, generate the corpus and
build the executor with x86-64 tools:

```sh
make -C x86 \
  CC=x86_64-linux-gnu-gcc \
  AS=x86_64-linux-gnu-as \
  'OBJDUMP=x86_64-linux-gnu-objdump --insn-width=16' \
  COSIM_LDFLAGS=-static \
  x86-insns.ml proofs/cosim-runner

make -C x86 HOLDIR=/path/to/hol-light proofs/simulator.native
```

`COSIM_LDFLAGS=-static` avoids a dependency on a target dynamic loader when
using a user-mode emulator. It can be omitted when the execution environment
provides the required x86-64 runtime.

If the host cannot execute the runner transparently, set the executor command
to the required prefix followed by the runner path:

```sh
S2N_BIGNUM_X86_64_EXECUTOR='qemu-x86_64 -cpu max x86/proofs/cosim-runner' \
  make -C x86 HOLDIR=/path/to/hol-light sematest
```

The override can likewise name another emulator or a wrapper for a remote or
hardware executor. It must eventually start a process that speaks the executor
protocol on standard input and standard output.
