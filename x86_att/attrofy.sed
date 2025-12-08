#############################################################################
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
#############################################################################

 ############################################################################
 #                         * * * NOTE * * *                                 #
 #                                                                          #
 # This is a primitive script to automate conversion of certain particular  #
 # x86 assembler files from Intel to AT&T syntax. It is *not* a general     #
 # conversion and is very tied to the specific limitations and conventions  #
 # in the intended targets. Even in that setting we only use it with an     #
 # additional sanity check that the object code generated is the same in    #
 # both original and translated code according to the GNU assembler.        #
 ############################################################################

s/\.intel_syntax *noprefix//
s/_internal_s2n_bignum_x86/_internal_s2n_bignum_x86_att/

# Don't make any transforms on lines with the argument-taking macros

/ addrow .+,/b
/ mulpadd .+,/b
/ mulpadda .+,/b
/ mulpade .+,/b
/ mulrow .+,/b

# SPECIFIC AVX2 MACRO INSTRUCTION CONVERSIONS - MUST BE BEFORE GENERAL RULES

# Don't transform macro definitions and calls
/^\.macro/b
/^\.endm/b

# 4-operand instructions: dest,src1,src2,imm -> $imm,%src2,%src1,%dest
s/[ \t]*vperm2i128[ \t]+ymm([a-z_0-9]+),ymm([a-z_0-9]+),ymm([a-z_0-9]+),(0x[0-9A-Fa-f]+)$/vperm2i128\t$\4,%ymm\3,%ymm\2,%ymm\1/
s/^vperm2i128[ \t]+ymm\\([a-z_0-9]+),ymm\\([a-z_0-9]+),ymm\\([a-z_0-9]+),(0x[0-9A-Fa-f]+)$/vperm2i128\t$\4,%ymm\\\3,%ymm\\\2,%ymm\\\1/
s/^vpblendd[ \t]+ymm\\([a-z_0-9]+),ymm\\([a-z_0-9]+),ymm\\([a-z_0-9]+),(0x[0-9A-Fa-f]+)$/vpblendd\t$\4,%ymm\\\3,%ymm\\\2,%ymm\\\1/

# 3-operand instructions: dest,src1,src2 -> %src2,%src1,%dest
s/^vpunpcklqdq[ \t]+ymm\\([a-z_0-9]+),ymm\\([a-z_0-9]+),ymm\\([a-z_0-9]+)$/vpunpcklqdq\t%ymm\\\3,%ymm\\\2,%ymm\\\1/
s/^vpunpckhqdq[ \t]+ymm\\([a-z_0-9]+),ymm\\([a-z_0-9]+),ymm\\([a-z_0-9]+)$/vpunpckhqdq\t%ymm\\\3,%ymm\\\2,%ymm\\\1/

# 3-operand with immediate: dest,src,imm -> $imm,%src,%dest
s/^vpsrlq[ \t]+ymm\\([a-z_0-9]+),ymm\\([a-z_0-9]+),([0-9]+)$/vpsrlq\t\t$\3,%ymm\\\2,%ymm\\\1/

# 2-operand instructions: dest,src -> %src,%dest
s/^vmovsldup[ \t]+ymm\\([a-z_0-9]+),ymm\\([a-z_0-9]+)$/vmovsldup\t%ymm\\\2,%ymm\\\1/
s/^vmovshdup[ \t]+ymm\\([a-z_0-9]+),ymm\\([a-z_0-9]+)$/vmovshdup\t%ymm\\\2,%ymm\\\1/

# Handle mixed cases: vmovshdup ymm12,%ymm\h -> vmovshdup %ymm\h,%ymm12
s/^vmovshdup[ \t]+ymm([0-9]+),%ymm\\([a-z_0-9]+)$/vmovshdup\t%ymm\\\2,%ymm\1/

# BUTTERFLY MACRO SPECIFIC CONVERSIONS
# Based on diff: vpmuldq ymm13,ymm\h,ymm\zl0 -> vpmuldq %ymm\zl0,%ymm\h,%ymm13
s/^vpmuldq[ \t]+ymm([0-9]+),ymm\\([a-z_0-9]+),ymm\\([a-z_0-9]+)$/vpmuldq\t\t%ymm\\\3,%ymm\\\2,%ymm\1/
s/^vpmuldq[ \t]+ymm\\([a-z_0-9]+),ymm\\([a-z_0-9]+),ymm\\([a-z_0-9]+)$/vpmuldq\t\t%ymm\\\3,%ymm\\\2,%ymm\\\1/
s/^vpmuldq[ \t]+ymm\\([a-z_0-9]+),ymm\\([a-z_0-9]+),ymm([0-9]+)$/vpmuldq\t\t%ymm\3,%ymm\\\2,%ymm\\\1/

# vpsubd ymm12,ymm\l,ymm\h -> vpsubd %ymm\h,%ymm\l,%ymm12
s/^vpsubd[ \t]+ymm([0-9]+),ymm\\([a-z_0-9]+),ymm\\([a-z_0-9]+)$/vpsubd\t\t%ymm\\\3,%ymm\\\2,%ymm\1/
s/^vpsubd[ \t]+ymm\\([a-z_0-9]+),ymm\\([a-z_0-9]+),ymm\\([a-z_0-9]+)$/vpsubd\t\t%ymm\\\3,%ymm\\\2,%ymm\\\1/

# vpaddd ymm\l,ymm\l,ymm\h -> vpaddd %ymm\h,%ymm\l,%ymm\l
s/^vpaddd[ \t]+ymm\\([a-z_0-9]+),ymm\\([a-z_0-9]+),ymm\\([a-z_0-9]+)$/vpaddd\t\t%ymm\\\3,%ymm\\\2,%ymm\\\1/
s/^vpaddd[ \t]+ymm\\([a-z_0-9]+),ymm([0-9]+),ymm([0-9]+)$/vpaddd\t\t%ymm\3,%ymm\2,%ymm\\\1/

# MEMORY OPERATIONS BASED ON DIFF ANALYSIS

# Memory loads for levels0t1: [rdi+0+32*\off] -> 0+32*\off(%rdi) (offset first for 32-byte scale)
s/^vmovdqa[ \t]+ymm([0-9]+),\[([a-z_0-9]+)\+([0-9]+)\+32\*\\([a-z_0-9]+)\]$/vmovdqa\t\t\3+32*\\\4(\2),%ymm\1/
s/^vmovdqa[ \t]+ymm\\([a-z_0-9]+),\[([a-z_0-9]+)\+([0-9]+)\+32\*\\([a-z_0-9]+)\]$/vmovdqa\t\t\3+32*\\\4(\2),%ymm\\\1/

# Memory loads for levels2t7: [rdi+0+256*\off] -> 256*\off+0(%rdi) (scale*macro first for 256-byte scale)
s/^vmovdqa[ \t]+ymm([0-9]+),\[([a-z_0-9]+)\+([0-9]+)\+256\*\\([a-z_0-9]+)\]$/vmovdqa\t\t256*\\\4+\3(\2),%ymm\1/
s/^vmovdqa[ \t]+ymm\\([a-z_0-9]+),\[([a-z_0-9]+)\+([0-9]+)\+256\*\\([a-z_0-9]+)\]$/vmovdqa\t\t256*\\\4+\3(\2),%ymm\\\1/

# Memory stores for levels0t1: [rdi+0+32*\off],ymm4 -> %ymm4,0+32*\off(%rdi)
s/^vmovdqa[ \t]+\[([a-z_0-9]+)\+([0-9]+)\+32\*\\([a-z_0-9]+)\],ymm([0-9]+)$/vmovdqa\t\t%ymm\4,\2+32*\\\3(\1)/
s/^vmovdqa[ \t]+\[([a-z_0-9]+)\+([0-9]+)\+32\*\\([a-z_0-9]+)\],ymm\\([a-z_0-9]+)$/vmovdqa\t\t%ymm\\\4,\2+32*\\\3(\1)/

# Memory stores for levels2t7: [rdi+0+256*\off],ymm4 -> %ymm4,256*\off+0(%rdi)
s/^vmovdqa[ \t]+\[([a-z_0-9]+)\+([0-9]+)\+256\*\\([a-z_0-9]+)\],ymm([0-9]+)$/vmovdqa\t\t%ymm\4,256*\\\3+\2(\1)/
s/^vmovdqa[ \t]+\[([a-z_0-9]+)\+([0-9]+)\+256\*\\([a-z_0-9]+)\],ymm\\([a-z_0-9]+)$/vmovdqa\t\t%ymm\\\4,256*\\\3+\2(\1)/

# Fallback for other memory operations
s/^vmovdqa[ \t]+ymm([0-9]+),([^,]+)$/vmovdqa\t\t\2,%ymm\1/
s/^vmovdqa[ \t]+ymm\\([a-z_0-9]+),([^,]+)$/vmovdqa\t\t\2,%ymm\\\1/
s/^vmovdqa[ \t]+([^,]+),ymm([0-9]+)$/vmovdqa\t\t%ymm\2,\1/
s/^vmovdqa[ \t]+([^,]+),ymm\\([a-z_0-9]+)$/vmovdqa\t\t%ymm\\\2,\1/

# Broadcast instructions: vpbroadcastd ymm1,[rsi+...] -> vpbroadcastd ...(%rsi),%ymm1
s/^vpbroadcastd[ \t]+ymm([0-9]+),([^,]+)$/vpbroadcastd\t\2,%ymm\1/

# Reverse the argument order for binary and ternary instructions

s/^(([a-z_0-9]+\:)* +[a-z_0-9]+ +)([^ (][^,/]*), *([^ ][^/,;]*)([/;].*)*$/\1\4, \3 \5/
s/^(([a-z_0-9]+\:)* +[a-z_0-9]+ +)([^ (][^,/]*), *([^ ][^/,]*), *([^ ][^/,;]*)([/;].*)*$/\1\5, \4, \3 \6/

# Fix up whitespace just in case

s/ +,/,/

# Decorate literals with $

s/^(([a-z_0-9]+\:)* +[a-z_0-9]+ +)(([-~+*/()A-Z0-9]*(0x[a-zA-Z0-9]*)*)* *\,)/\1$\3/

# Translate relative addresses with uppercase base variable
# Turn defined offset fields into explicit indirections to match

s/^([^/][^[]+)[[]([A-Z_0-9]+)[]]/\1\2/
s/^([^/][^[]+)[[]([A-Z][A-Z_0-9]*) *\+ *([^]]+)[]]/\1\3\+\2/

s/^\#define *([a-z][a-z_0-9]*) *([a-z][a-z_0-9]*) *\+(.*)/\#define \1 \3\(\2\)/

# Translate relative addresses

# Handle [offset + register] and [offset - register] patterns
s/^([^/][^[]+)[[]([A-Z0-9* ]+) *\+ *([a-z][a-z_0-9]*)[]]/\1\2\(\3\)/
s/^([^/][^[]+)[[]([A-Z0-9* ]+) *\- *([a-z][a-z_0-9]*)[]]/\1-\2\(\3\)/
s/^([^/][^[]+)[[]([0-9]+) *\+ *([a-z][a-z_0-9]*)[]]/\1\2\(\3\)/
s/^([^/][^[]+)[[]([0-9]+) *\- *([a-z][a-z_0-9]*)[]]/\1-\2\(\3\)/

s/^([^/][^[]+)[[]([a-z_0-9]+)[]]/\1\(\2\)/
s/^([^/][^[]+)[[]([a-z][a-z_0-9]*) *\+ *8\*([a-z][a-z_0-9]*) *\+ *([a-z_A-Z0-9]+)[]]/\1\4\(\2,\3,8\)/
s/^([^/][^[]+)[[]([a-z][a-z_0-9]*) *\+ *([a-z][a-z_0-9]*) *\+ *([a-z_A-Z0-9]+)[]]/\1\4\(\2,\3,1\)/
s/^([^/][^[]+)[[]([a-z][a-z_0-9]*) *\+ *8\*([a-z][a-z_0-9]*) *\- *([a-z_A-Z0-9]+)[]]/\1\-\4\(\2,\3,8\)/
s/^([^/][^[]+)[[](rip) *\+ *([a-z_A-Z0-9* ]+)[]]/\1\3\(\2\)/
s/^([^/][^[]+)[[]([a-z][a-z_0-9]*) *\+ *([A-Z0-9* ]+)[]]/\1\3\(\2\)/
s/^([^/][^[]+)[[]([a-z][a-z_0-9]*) *\- *([A-Z0-9* ]+)[]]/\1\-\3\(\2\)/
s/^([^/][^[]+)[[]([a-z][a-z_0-9]*) *\+ *8\*([a-z][a-z_0-9]*)[]]/\1\(\2,\3,8\)/
s/^([^/][^[]+)[[]([a-z][a-z_0-9]*) *\+ *4\*([a-z][a-z_0-9]*)[]]/\1\(\2,\3,4\)/
s/^([^/][^[]+)[[]([a-z][a-z_0-9]*) *\+ *2\*([a-z][a-z_0-9]*)[]]/\1\(\2,\3,2\)/
s/^([^/][^[]+)[[]([a-z][a-z_0-9]*) *\+ *([a-z][a-z_0-9]*)[]]/\1\(\2,\3\)/
s/^([^/][^[]+)[[]([a-z][a-z_0-9]*) *\+ *([^]]+)[]]/\1\3\(\2\)/
s/^([^/][^[]+)[[]([a-z][a-z_0-9]*) *\- *([^]]+)[]]/\1-\3\(\2\)/
s/^([^/][^[]+)[[]([^]]+)[]]/\1\(\2\)/

# Put % in front of register names

s/ ax *$/ %ax/
s/ ax,/ %ax,/
s/ cl *$/ %cl/
s/ cl,/ %cl,/
s/([[(,.;: ])([re][abcd]x)/\1\%\2/g
s/([[(,.;: ])([re]sp)/\1\%\2/g
s/([[(,.;: ])([re]bp)/\1\%\2/g
s/([[(,.;: ])([re]si)/\1\%\2/g
s/([[(,.;: ])([re]si)/\1\%\2/g
s/([[(,.;: ])([re]di)/\1\%\2/g
s/([[(,.;: ])(r8d*)/\1\%\2/g
s/([[(,.;: ])(r9d*)/\1\%\2/g
s/([[(,.;: ])(r1[0-5]d*)/\1\%\2/g
s/([[(,.;: ])([re]ip)/\1\%\2/g
s/([[(,.;: ])([xyz]mm[0-9]*)/\1\%\2/g

# Handle macro parameter registers like ymm\r0, ymm\r1, etc.
s/ymm\\([a-z_0-9]+)/\%ymm\\\1/g

# Add explicit sizes to instructions

s/QWORD PTR//g

s/ adc  / adcq /g
s/ adcx  / adcxq /g
s/ add  / addq /g
s/ adox  / adoxq /g
s/ and  / andq /g
s/ bsf  / bsfq /g
s/ bsr  / bsrq /g
s/ bswap  / bswapq /g
s/ bt  / btq /g
s/ call  / callq /g
s/ cmovae  / cmovaeq /g
s/ cmovb  / cmovbq /g
s/ cmovc  / cmovcq /g
s/ cmove  / cmoveq /g
s/ cmovnc  / cmovncq /g
s/ cmovne  / cmovneq /g
s/ cmovnz  / cmovnzq /g
s/ cmovz  / cmovzq /g
s/ cmp  / cmpq /g
s/ dec  / decq /g
s/ imul  / imulq /g
s/ inc  / incq /g
s/ lea  / leaq /g
s/ mov  / movq /g
s/ movabs  / movabsq /g
s/ mul  / mulq /g
s/ mulx  / mulxq /g
s/ neg  / negq /g
s/ not  / notq /g
s/ or  / orq /g
s/ pop  / popq /g
s/ push  / pushq /g
s/ sar  / sarq /g
s/ sbb  / sbbq /g
s/ shl  / shlq /g
s/ shld  / shldq /g
s/ shr  / shrq /g
s/ shrd  / shrdq /g
s/ sub  / subq /g
s/ test  / testq /g
s/ xor  / xorq /g

s/q(  .*zeroe)/l\1/
s/q(  .*plus2e)/l\1/
s/q(  .*short)/l\1/
s/q( .*%e)/l\1/
s/q( .*%r[0-9]+d)/l\1/
s/q( .*%ax)/w\1/

# Clean up double percent signs that may result from macro expansion
s/%%ymm/%ymm/g

# Fix vmovshdup operand order after register prefixing: vmovshdup %ymm12,%ymm\h -> vmovshdup %ymm\h,%ymm12
s/^vmovshdup[ \t]+%ymm([0-9]+),%ymm\\([a-z_0-9]+)$/vmovshdup\t%ymm\\\2,%ymm\1/

# Fix vmovshdup without % prefix: vmovshdup ymm12,%ymm\h -> vmovshdup %ymm\h,%ymm12
s/^vmovshdup[ \t]+ymm([0-9]+),%ymm\\([a-z_0-9]+)$/vmovshdup\t%ymm\\\2,%ymm\1/

# Fix missing % prefixes on regular registers in butterfly macro
s/^vpmuldq[ \t]+ymm([0-9]+),/vpmuldq\t\t%ymm\1,/
s/^vmovshdup[ \t]+ymm([0-9]+),/vmovshdup\t%ymm\1,/
s/[ \t]*vpblendd[ \t]+ymm([0-9]+),/vpblendd\t%ymm\1,/
s/[ \t]*vpblendw[ \t]+ymm([0-9]+),/vpblendw\t%ymm\1,/

# Fix specific operand order issues that got reversed by general rules
# vpsrlq should be: vpsrlq $32,%ymm1,%ymm10 not vpsrlq ymm10,%ymm1,32
s/^vpsrlq[ \t]+ymm([0-9]+),%ymm([0-9]+),([0-9]+)$/vpsrlq\t\t$\3,%ymm\2,%ymm\1/
s/^vpsrlq[ \t]+%ymm([0-9]+),%ymm([0-9]+),([0-9]+)$/vpsrlq\t\t$\3,%ymm\2,%ymm\1/

# vmovshdup should be: vmovshdup %ymm2,%ymm15 not vmovshdup %ymm15,%ymm2
s/^vmovshdup[ \t]+%ymm([0-9]+),%ymm([0-9]+)$/vmovshdup\t%ymm\2,%ymm\1/

# vpblendd should be: vpblendd $0xAA,%ymm12,%ymm\h,%ymm\h not vpblendd %ymm\h,%ymm\h,%ymm12,0xAA
s/[ \t]*vpblendd[ \t]+%ymm\\([a-z_0-9]+),%ymm\\([a-z_0-9]+),%ymm([0-9]+),(0x[0-9A-Fa-f]+)$/vpblendd\t$\4,%ymm\3,%ymm\\\2,%ymm\\\1/
s/[ \t]*vpblendd[ \t]+%ymm([0-9]+),%ymm([0-9]+),%ymm([0-9]+),(0x[0-9A-Fa-f]+)$/vpblendd\t$\4,%ymm\3,%ymm\2,%ymm\1/
s/[ \t]*vpblendw[ \t]+%ymm([0-9]+),%ymm([0-9]+),%ymm([0-9]+),(0x[0-9A-Fa-f]+)$/vpblendw\t$\4,%ymm\3,%ymm\2,%ymm\1/

# Fix remaining butterfly macro operand order issues
# vpmuldq %ymm14,%ymm12,%ymm\zl1 should be vpmuldq %ymm\zl1,%ymm12,%ymm14
s/^vpmuldq[ \t]+%ymm([0-9]+),%ymm([0-9]+),%ymm\\([a-z_0-9]+)$/vpmuldq\t\t%ymm\\\3,%ymm\2,%ymm\1/

# vpmuldq %ymm13,%ymm13,%ymm0 should be vpmuldq %ymm0,%ymm13,%ymm13
s/^vpmuldq[ \t]+%ymm([0-9]+),%ymm\1,%ymm([0-9]+)$/vpmuldq\t\t%ymm\2,%ymm\1,%ymm\1/

# vpsubd %ymm\l,%ymm\l,%ymm13 should be vpsubd %ymm13,%ymm\l,%ymm\l
s/^vpsubd[ \t]+%ymm\\([a-z_0-9]+),%ymm\\\1,%ymm([0-9]+)$/vpsubd\t\t%ymm\2,%ymm\\\1,%ymm\\\1/

# Eliminate any trailing spaces, just to be tidy

s/ +$//
