## X86_64 Instruction Modeling

The s2n-bignum symbolic simulator contains models of x86_64 instructions. The instructions are modeled by need. Often when verifying new programs, new instructions need to be added to s2n-bignum. This is a tutorial for adding new x86_64 instructions.

The instruction modeling is composed of three basic steps: instruction decoding, instruction semantics modeling and instruction cosimulation test.

### Instruction Decoding

[Location: x86/proofs/decode.ml](proofs/decode.ml)

The x86 instructions are variable length, therefore could not be decoded by a simple bitmatch as is done in Arm. Instead, the decoding step is composed of several smaller steps: reading instruction prefix, reading the REX prefix and reading the rest of instructions starting with opcode. The main decoding function `decode_aux` is written in a monadic style. The `>>=` function binds the output from previous function call to the inputs to the function after it.

The codebase supports various functions for handling each part of the instruction, namely: `read_prefixes` for reading prefix, `read_REX_prefix` for reading the REX prefix bytes, `decode_aux` for taking care of the opcode decoding, `read_ModRM` for reading the ModR/M byte, `read_SIB` for reading the SIB byte, `read_displacement` for reading the displacement and `read_imm` for reading the immediate. AVX instructions are also supported by `read_VEX` for reading the VEX bytes.

#### Instruction Abstract Syntax

[Location: x86/proofs/instruction.ml](proofs/instruction.ml)

The `instruction` data type defines the abstract syntax for x86_64 instructions. The decoding step will dispatch instructions to their corresponding abstract syntax.

#### Registers

s2n-bignum supports general-purpose registers, as well as SIMD registers for AVX and SSE instructions. These definitions specify the behaviour when read from or write to these registers. See *x86/proofs/x86.ml*.

### Instruction Semantics

[Location: x86/proofs/x86.ml](proofs/x86.ml)

After transforming binary instructions to its abstract syntax, the `x86_execute` function dispatches each syntax to their corresponding semantics function with appropriate operand size.

The following is an example for the `AND` instruction:
```
let x86_AND = new_definition
 `x86_AND dest src s =
        let x = read dest s and y = read src s in
        let z = word_and x y in
        (dest := (z:N word) ,,
         ZF := (val z = 0) ,,
         SF := (ival z < &0) ,,
         PF := word_evenparity(word_zx z:byte) ,,
         CF := F ,,
         OF := F ,,
         UNDEFINED_VALUES[AF]) s`;;
```
Note that the following
```
(... ,, ... ,, ...) s
```
is a way of assigning values to the state variables in *x86state* `s` to create a new state. The `,,` function called `seq` sequence a list of assignments. For more detail, check *common/relational.ml*.

In addition to the destination register and the flags that should be assigned, note that there is a `UNDEFINED_VALUES[AF]` at the end of state assignment. This allows the `AF` flag to be arbitrarily assigned in the newly created state.

Often, one will need access to supported word functions for implementing the semantics. Usually it is enough to read the [HOL Light word library](https://github.com/jrh13/hol-light/blob/master/Library/words.ml) for this purpose.

#### Conversions

s2n-bignum supports generic framework for adding conversion rules or tactics for new instructions. The `X86_OPERATION_CLAUSES` defintion stores clauses that specify rewrite rules for instruction semantic definitions. They are used in the symbolic simulation and cosimulation testing for supporting definition expansion of these instructions.

More complex instructions that are defined with a deeper chain of functions will require dedicated conversion rules. Check the modeling of AESNI instructions in this case.

### Cosimulation Test

[Location: x86/proofs/simulator.ml](proofs/simulator.ml)

s2n-bignum conducts cosimulation tests against real machines to ensure correctness of instruction modeling. Instead of randomly generating instructions, s2n-bignum scans all assembly files for instructions to be tested in cosimulation. For the cosimulation testing, it generates random values for PC, registers, flags, and memory in the *x86state*, run the instruction on the actual machine with state values pre-set to the randomly generated values and then compare the resulting *x86state* on the machine against the model.

There are two sources of instructions tested. The *x86/x86-insns.ml* file is a generated file that contains instructions automatically read from existing assembly files. These are instructions that do not involve memory accesses. In addition to that, there are some manually added test instructions that are not in existing assembly files. These can be found in the definition of `iclasses` in *x86/proofs/simulator.ml*.

Note that lots of x86_64 instructions can take memory operands. And they are tested in a slightly different way. This is because accessing random memory locations is not permitted by the OS. As a workaround, the cosimulation testing framework allocates a 256-byte memory on the stack for the purpose of testing instructions with memory operands. Special harness functions need to be defined for pointing memory address to the right location in the 256-byte memory on stack. Check *x86/proofs/simulator.ml* for detail.

### Constant Time

[Location: x86/proofs/allowed_asm](allowed_asm)

To assist constant time verification, the `allowed_asm` file contains instructions that are known to be constant time. We refer to the [Data Operand Independent Timing instructions table](https://www.intel.com/content/www/us/en/developer/articles/technical/software-security-guidance/resources/data-operand-independent-timing-instructions.html) from Intel for deciding whether an instruction is constant time.

### Examples

Here are some examples of adding instructions:
* A simple example: [Add x86_64 XCHG instruction](https://github.com/awslabs/s2n-bignum/pull/184/files)
* Adding cosimulation tests for instructions with memory operands: [Enable testing of instructions with memory operands in x86_64 simulator](https://github.com/awslabs/s2n-bignum/pull/212)
* Modeling complex instructions that require dedicated conversions: [Add AESNI instructions for x86_64](https://github.com/awslabs/s2n-bignum/pull/208)

### Resources

* [x86 and amd64 instruction reference](https://www.felixcloutier.com/x86/)
* [Intel 64 and IA-32 Architectures Software Developer Manuals](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html)
