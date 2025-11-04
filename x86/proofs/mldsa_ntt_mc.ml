let mldsa_ntt_mc = define_assert_from_elf "mldsa_ntt_mc" "x86/mldsa/mldsa_ntt.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0xc5; 0xfd; 0x6f; 0x06;  (* VMOVDQA (%_% ymm0) (Memop Word256 (%% (rsi,0))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x84; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,132))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x24; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1316))) *)
  0xc5; 0xfd; 0x6f; 0x27;  (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,0))) *)
  0xc5; 0xfd; 0x6f; 0xaf; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,128))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,256))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,384))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,512))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0x80; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,640))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0x00; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,768))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0x80; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,896))) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0xc1; 0x5d; 0xfe; 0xe0;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x35; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm9) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe1;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x35; 0x28; 0xca;
                           (* VPMULDQ (%_% ymm9) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc9;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x43; 0x35; 0x02; 0xcc; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm9) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x55; 0xfa; 0xe1;
                           (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0xc1; 0x55; 0xfe; 0xe9;
                           (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xcd;
                           (* VPADDD (%_% ymm9) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0xc1; 0x4d; 0xfe; 0xf2;
                           (* VPADDD (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfa; 0xf5;
                           (* VPSUBD (%_% ymm6) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0xc1; 0x45; 0xfe; 0xfb;
                           (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x88; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,136))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x28; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1320))) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x5d; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm6) *)
  0xc5; 0xdd; 0xfe; 0xe6;  (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x45; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm7) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe7;  (* VMOVSHDUP (%_% ymm12) (%_% ymm7) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x45; 0x28; 0xfa;
                           (* VPMULDQ (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xff;  (* VMOVSHDUP (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc3; 0x45; 0x02; 0xfc; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm7) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe7;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm7) *)
  0xc5; 0xd5; 0xfe; 0xef;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xfd;
                           (* VPADDD (%_% ymm7) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x8c; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,140))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x2c; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1324))) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0xfe; 0xc2;
                           (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0xfe; 0xcb;
                           (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc5; 0xfd; 0x7f; 0x27;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,128))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,256))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,384))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,512))) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0x80; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,640))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x97; 0x00; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,768))) (%_% ymm10) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0x80; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,896))) (%_% ymm11) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x84; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,132))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x24; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1316))) *)
  0xc5; 0xfd; 0x6f; 0x67; 0x20;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,32))) *)
  0xc5; 0xfd; 0x6f; 0xaf; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,160))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,288))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,416))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,544))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xa0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,672))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0x20; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,800))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0xa0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,928))) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0xc1; 0x5d; 0xfe; 0xe0;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x35; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm9) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe1;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x35; 0x28; 0xca;
                           (* VPMULDQ (%_% ymm9) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc9;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x43; 0x35; 0x02; 0xcc; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm9) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x55; 0xfa; 0xe1;
                           (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0xc1; 0x55; 0xfe; 0xe9;
                           (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xcd;
                           (* VPADDD (%_% ymm9) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0xc1; 0x4d; 0xfe; 0xf2;
                           (* VPADDD (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfa; 0xf5;
                           (* VPSUBD (%_% ymm6) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0xc1; 0x45; 0xfe; 0xfb;
                           (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x88; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,136))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x28; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1320))) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x5d; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm6) *)
  0xc5; 0xdd; 0xfe; 0xe6;  (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x45; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm7) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe7;  (* VMOVSHDUP (%_% ymm12) (%_% ymm7) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x45; 0x28; 0xfa;
                           (* VPMULDQ (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xff;  (* VMOVSHDUP (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc3; 0x45; 0x02; 0xfc; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm7) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe7;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm7) *)
  0xc5; 0xd5; 0xfe; 0xef;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xfd;
                           (* VPADDD (%_% ymm7) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x8c; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,140))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x2c; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1324))) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0xfe; 0xc2;
                           (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0xfe; 0xcb;
                           (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc5; 0xfd; 0x7f; 0x67; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,160))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,288))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,416))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,544))) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xa0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,672))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x97; 0x20; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,800))) (%_% ymm10) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0xa0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,928))) (%_% ymm11) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x84; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,132))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x24; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1316))) *)
  0xc5; 0xfd; 0x6f; 0x67; 0x40;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,64))) *)
  0xc5; 0xfd; 0x6f; 0xaf; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,192))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,320))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,448))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,576))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xc0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,704))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0x40; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,832))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0xc0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,960))) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0xc1; 0x5d; 0xfe; 0xe0;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x35; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm9) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe1;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x35; 0x28; 0xca;
                           (* VPMULDQ (%_% ymm9) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc9;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x43; 0x35; 0x02; 0xcc; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm9) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x55; 0xfa; 0xe1;
                           (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0xc1; 0x55; 0xfe; 0xe9;
                           (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xcd;
                           (* VPADDD (%_% ymm9) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0xc1; 0x4d; 0xfe; 0xf2;
                           (* VPADDD (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfa; 0xf5;
                           (* VPSUBD (%_% ymm6) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0xc1; 0x45; 0xfe; 0xfb;
                           (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x88; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,136))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x28; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1320))) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x5d; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm6) *)
  0xc5; 0xdd; 0xfe; 0xe6;  (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x45; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm7) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe7;  (* VMOVSHDUP (%_% ymm12) (%_% ymm7) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x45; 0x28; 0xfa;
                           (* VPMULDQ (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xff;  (* VMOVSHDUP (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc3; 0x45; 0x02; 0xfc; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm7) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe7;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm7) *)
  0xc5; 0xd5; 0xfe; 0xef;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xfd;
                           (* VPADDD (%_% ymm7) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x8c; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,140))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x2c; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1324))) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0xfe; 0xc2;
                           (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0xfe; 0xcb;
                           (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc5; 0xfd; 0x7f; 0x67; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rdi,64))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,192))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,320))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,448))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,576))) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xc0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,704))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x97; 0x40; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,832))) (%_% ymm10) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0xc0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,960))) (%_% ymm11) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x84; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,132))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x24; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1316))) *)
  0xc5; 0xfd; 0x6f; 0x67; 0x60;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,96))) *)
  0xc5; 0xfd; 0x6f; 0xaf; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,224))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,352))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,480))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x60; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,608))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xe0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,736))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0x60; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,864))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0xe0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,992))) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0xc1; 0x5d; 0xfe; 0xe0;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x35; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm9) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe1;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x35; 0x28; 0xca;
                           (* VPMULDQ (%_% ymm9) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc9;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x43; 0x35; 0x02; 0xcc; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm9) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x55; 0xfa; 0xe1;
                           (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0xc1; 0x55; 0xfe; 0xe9;
                           (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xcd;
                           (* VPADDD (%_% ymm9) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0xc1; 0x4d; 0xfe; 0xf2;
                           (* VPADDD (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfa; 0xf5;
                           (* VPSUBD (%_% ymm6) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0xc1; 0x45; 0xfe; 0xfb;
                           (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x88; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,136))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x28; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1320))) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x5d; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm6) *)
  0xc5; 0xdd; 0xfe; 0xe6;  (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x45; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm7) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe7;  (* VMOVSHDUP (%_% ymm12) (%_% ymm7) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x45; 0x28; 0xfa;
                           (* VPMULDQ (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xff;  (* VMOVSHDUP (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc3; 0x45; 0x02; 0xfc; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm7) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe7;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm7) *)
  0xc5; 0xd5; 0xfe; 0xef;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xfd;
                           (* VPADDD (%_% ymm7) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x8c; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,140))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x2c; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1324))) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0xfe; 0xc2;
                           (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0xfe; 0xcb;
                           (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc5; 0xfd; 0x7f; 0x67; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rdi,96))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,224))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,352))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,480))) (%_% ymm7) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x60; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,608))) (%_% ymm8) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0xe0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,736))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x97; 0x60; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,864))) (%_% ymm10) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0xe0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,992))) (%_% ymm11) *)
  0xc5; 0xfd; 0x6f; 0x27;  (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,0))) *)
  0xc5; 0xfd; 0x6f; 0x6f; 0x20;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,32))) *)
  0xc5; 0xfd; 0x6f; 0x77; 0x40;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,64))) *)
  0xc5; 0xfd; 0x6f; 0x7f; 0x60;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,96))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,128))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,160))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,192))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,224))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x90; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,144))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x30; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1328))) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0xc1; 0x5d; 0xfe; 0xe0;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x35; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm9) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe1;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x35; 0x28; 0xca;
                           (* VPMULDQ (%_% ymm9) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc9;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x43; 0x35; 0x02; 0xcc; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm9) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x55; 0xfa; 0xe1;
                           (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0xc1; 0x55; 0xfe; 0xe9;
                           (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xcd;
                           (* VPADDD (%_% ymm9) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0xc1; 0x4d; 0xfe; 0xf2;
                           (* VPADDD (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfa; 0xf5;
                           (* VPSUBD (%_% ymm6) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0xc1; 0x45; 0xfe; 0xfb;
                           (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0xc3; 0x5d; 0x46; 0xd8; 0x20;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm4) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x5d; 0x46; 0xc0; 0x31;
                           (* VPERM2I128 (%_% ymm8) (%_% ymm4) (%_% ymm8) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x55; 0x46; 0xe1; 0x20;
                           (* VPERM2I128 (%_% ymm4) (%_% ymm5) (%_% ymm9) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x55; 0x46; 0xc9; 0x31;
                           (* VPERM2I128 (%_% ymm9) (%_% ymm5) (%_% ymm9) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xea; 0x20;
                           (* VPERM2I128 (%_% ymm5) (%_% ymm6) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x4d; 0x46; 0xd2; 0x31;
                           (* VPERM2I128 (%_% ymm10) (%_% ymm6) (%_% ymm10) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x45; 0x46; 0xf3; 0x20;
                           (* VPERM2I128 (%_% ymm6) (%_% ymm7) (%_% ymm11) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x45; 0x46; 0xdb; 0x31;
                           (* VPERM2I128 (%_% ymm11) (%_% ymm7) (%_% ymm11) (Imm8 (word 49)) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,160))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x40; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1344))) *)
  0xc4; 0x62; 0x55; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe5;  (* VMOVSHDUP (%_% ymm12) (%_% ymm5) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x55; 0x28; 0xea;
                           (* VPMULDQ (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xed;  (* VMOVSHDUP (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc3; 0x55; 0x02; 0xec; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm5) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x65; 0xfa; 0xe5;  (* VPSUBD (%_% ymm12) (%_% ymm3) (%_% ymm5) *)
  0xc5; 0xe5; 0xfe; 0xdd;  (* VPADDD (%_% ymm3) (%_% ymm3) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xed;
                           (* VPADDD (%_% ymm5) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xdd;
                           (* VPSUBD (%_% ymm3) (%_% ymm3) (%_% ymm13) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0xfe; 0xc2;
                           (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x5d; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm6) *)
  0xc5; 0xdd; 0xfe; 0xe6;  (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0xfe; 0xcb;
                           (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc5; 0xe5; 0x6c; 0xfd;  (* VPUNPCKLQDQ (%_% ymm7) (%_% ymm3) (%_% ymm5) *)
  0xc5; 0xe5; 0x6d; 0xed;  (* VPUNPCKHQDQ (%_% ymm5) (%_% ymm3) (%_% ymm5) *)
  0xc4; 0xc1; 0x3d; 0x6c; 0xda;
                           (* VPUNPCKLQDQ (%_% ymm3) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0x6d; 0xd2;
                           (* VPUNPCKHQDQ (%_% ymm10) (%_% ymm8) (%_% ymm10) *)
  0xc5; 0x5d; 0x6c; 0xc6;  (* VPUNPCKLQDQ (%_% ymm8) (%_% ymm4) (%_% ymm6) *)
  0xc5; 0xdd; 0x6d; 0xf6;  (* VPUNPCKHQDQ (%_% ymm6) (%_% ymm4) (%_% ymm6) *)
  0xc4; 0xc1; 0x35; 0x6c; 0xe3;
                           (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0x6d; 0xdb;
                           (* VPUNPCKHQDQ (%_% ymm11) (%_% ymm9) (%_% ymm11) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,288))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xc0; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1472))) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0xc1; 0x45; 0xfe; 0xf8;
                           (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm6) *)
  0xc5; 0xd5; 0xfe; 0xee;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x5d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc3; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x65; 0xfa; 0xe4;  (* VPSUBD (%_% ymm12) (%_% ymm3) (%_% ymm4) *)
  0xc5; 0xe5; 0xfe; 0xdc;  (* VPADDD (%_% ymm3) (%_% ymm3) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xe5;
                           (* VPADDD (%_% ymm4) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xdd;
                           (* VPSUBD (%_% ymm3) (%_% ymm3) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xfe; 0xd3;
                           (* VPADDD (%_% ymm10) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xd5;
                           (* VPSUBD (%_% ymm10) (%_% ymm10) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x12; 0xc8;
                           (* VMOVSLDUP (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x43; 0x45; 0x02; 0xc9; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm7) (%_% ymm9) (Imm8 (word 170)) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x20;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x45; 0x02; 0xc0; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm7) (%_% ymm8) (Imm8 (word 170)) *)
  0xc5; 0xfe; 0x12; 0xfe;  (* VMOVSLDUP (%_% ymm7) (%_% ymm6) *)
  0xc4; 0xe3; 0x55; 0x02; 0xff; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm5) (%_% ymm7) (Imm8 (word 170)) *)
  0xc5; 0xd5; 0x73; 0xd5; 0x20;
                           (* VPSRLQ (%_% ymm5) (%_% ymm5) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x55; 0x02; 0xf6; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm5) (%_% ymm6) (Imm8 (word 170)) *)
  0xc5; 0xfe; 0x12; 0xec;  (* VMOVSLDUP (%_% ymm5) (%_% ymm4) *)
  0xc4; 0xe3; 0x65; 0x02; 0xed; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm3) (%_% ymm5) (Imm8 (word 170)) *)
  0xc5; 0xe5; 0x73; 0xd3; 0x20;
                           (* VPSRLQ (%_% ymm3) (%_% ymm3) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x65; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm3) (%_% ymm4) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x7e; 0x12; 0xdb;
                           (* VMOVSLDUP (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xe3; 0x2d; 0x02; 0xdb; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm10) (%_% ymm3) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x2d; 0x02; 0xdb; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm10) (%_% ymm11) (Imm8 (word 170)) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,416))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x40; 0x06; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1600))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x55; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe5;  (* VMOVSHDUP (%_% ymm12) (%_% ymm5) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x55; 0x28; 0xea;
                           (* VPMULDQ (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xed;  (* VMOVSHDUP (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc3; 0x55; 0x02; 0xec; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm5) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x35; 0xfa; 0xe5;  (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm5) *)
  0xc5; 0x35; 0xfe; 0xcd;  (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xed;
                           (* VPADDD (%_% ymm5) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0x62; 0x5d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc3; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x3d; 0xfa; 0xe4;  (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0x3d; 0xfe; 0xc4;  (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xe5;
                           (* VPADDD (%_% ymm4) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x62; 0x65; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe3;  (* VMOVSHDUP (%_% ymm12) (%_% ymm3) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x65; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm3) (%_% ymm3) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xdb;  (* VMOVSHDUP (%_% ymm3) (%_% ymm3) *)
  0xc4; 0xc3; 0x65; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm3) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x45; 0xfa; 0xe3;  (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xc5; 0xfe; 0xfb;  (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm3) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm3) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm6) (%_% ymm11) *)
  0xc4; 0xc1; 0x4d; 0xfe; 0xf3;
                           (* VPADDD (%_% ymm6) (%_% ymm6) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfa; 0xf5;
                           (* VPSUBD (%_% ymm6) (%_% ymm6) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,544))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xc0; 0x06; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1728))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x45; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm7) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe7;  (* VMOVSHDUP (%_% ymm12) (%_% ymm7) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x45; 0x28; 0xfa;
                           (* VPMULDQ (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xff;  (* VMOVSHDUP (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc3; 0x45; 0x02; 0xfc; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm7) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x35; 0xfa; 0xe7;  (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm7) *)
  0xc5; 0x35; 0xfe; 0xcf;  (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xfd;
                           (* VPADDD (%_% ymm7) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x3d; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm6) *)
  0xc5; 0x3d; 0xfe; 0xc6;  (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xa0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,672))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x40; 0x07; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1856))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x65; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe3;  (* VMOVSHDUP (%_% ymm12) (%_% ymm3) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x65; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm3) (%_% ymm3) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xdb;  (* VMOVSHDUP (%_% ymm3) (%_% ymm3) *)
  0xc4; 0xc3; 0x65; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm3) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe3;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm3) *)
  0xc5; 0xd5; 0xfe; 0xeb;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm3) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm3) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm11) *)
  0xc4; 0xc1; 0x5d; 0xfe; 0xe3;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x20; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,800))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xc0; 0x07; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1984))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x41; 0x35; 0xfe; 0xc8;
                           (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xa0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,928))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x40; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2112))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x45; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm6) *)
  0xc5; 0xc5; 0xfe; 0xfe;  (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x20; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,1056))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xc0; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2240))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x5d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc3; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe4;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm4) *)
  0xc5; 0xd5; 0xfe; 0xec;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xe5;
                           (* VPADDD (%_% ymm4) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xa0; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,1184))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x40; 0x09; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2368))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x65; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xc1; 0x65; 0xfe; 0xdb;
                           (* VPADDD (%_% ymm3) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xdd;
                           (* VPSUBD (%_% ymm3) (%_% ymm3) (%_% ymm13) *)
  0xc5; 0x7d; 0x7f; 0x0f;  (* VMOVDQA (Memop Word256 (%% (rdi,0))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x47; 0x20;
                           (* VMOVDQA (Memop Word256 (%% (rdi,32))) (%_% ymm8) *)
  0xc5; 0xfd; 0x7f; 0x7f; 0x40;
                           (* VMOVDQA (Memop Word256 (%% (rdi,64))) (%_% ymm7) *)
  0xc5; 0xfd; 0x7f; 0x77; 0x60;
                           (* VMOVDQA (Memop Word256 (%% (rdi,96))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0x80; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,128))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0xa0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,160))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0x9f; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,192))) (%_% ymm3) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,224))) (%_% ymm11) *)
  0xc5; 0xfd; 0x6f; 0xa7; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,256))) *)
  0xc5; 0xfd; 0x6f; 0xaf; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,288))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,320))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,352))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,384))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,416))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,448))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,480))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x94; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,148))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x34; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1332))) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0xc1; 0x5d; 0xfe; 0xe0;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x35; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm9) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe1;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x35; 0x28; 0xca;
                           (* VPMULDQ (%_% ymm9) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc9;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x43; 0x35; 0x02; 0xcc; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm9) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x55; 0xfa; 0xe1;
                           (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0xc1; 0x55; 0xfe; 0xe9;
                           (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xcd;
                           (* VPADDD (%_% ymm9) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0xc1; 0x4d; 0xfe; 0xf2;
                           (* VPADDD (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfa; 0xf5;
                           (* VPSUBD (%_% ymm6) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0xc1; 0x45; 0xfe; 0xfb;
                           (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0xc3; 0x5d; 0x46; 0xd8; 0x20;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm4) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x5d; 0x46; 0xc0; 0x31;
                           (* VPERM2I128 (%_% ymm8) (%_% ymm4) (%_% ymm8) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x55; 0x46; 0xe1; 0x20;
                           (* VPERM2I128 (%_% ymm4) (%_% ymm5) (%_% ymm9) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x55; 0x46; 0xc9; 0x31;
                           (* VPERM2I128 (%_% ymm9) (%_% ymm5) (%_% ymm9) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xea; 0x20;
                           (* VPERM2I128 (%_% ymm5) (%_% ymm6) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x4d; 0x46; 0xd2; 0x31;
                           (* VPERM2I128 (%_% ymm10) (%_% ymm6) (%_% ymm10) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x45; 0x46; 0xf3; 0x20;
                           (* VPERM2I128 (%_% ymm6) (%_% ymm7) (%_% ymm11) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x45; 0x46; 0xdb; 0x31;
                           (* VPERM2I128 (%_% ymm11) (%_% ymm7) (%_% ymm11) (Imm8 (word 49)) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xc0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,192))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x60; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1376))) *)
  0xc4; 0x62; 0x55; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe5;  (* VMOVSHDUP (%_% ymm12) (%_% ymm5) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x55; 0x28; 0xea;
                           (* VPMULDQ (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xed;  (* VMOVSHDUP (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc3; 0x55; 0x02; 0xec; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm5) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x65; 0xfa; 0xe5;  (* VPSUBD (%_% ymm12) (%_% ymm3) (%_% ymm5) *)
  0xc5; 0xe5; 0xfe; 0xdd;  (* VPADDD (%_% ymm3) (%_% ymm3) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xed;
                           (* VPADDD (%_% ymm5) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xdd;
                           (* VPSUBD (%_% ymm3) (%_% ymm3) (%_% ymm13) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0xfe; 0xc2;
                           (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x5d; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm6) *)
  0xc5; 0xdd; 0xfe; 0xe6;  (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0xfe; 0xcb;
                           (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc5; 0xe5; 0x6c; 0xfd;  (* VPUNPCKLQDQ (%_% ymm7) (%_% ymm3) (%_% ymm5) *)
  0xc5; 0xe5; 0x6d; 0xed;  (* VPUNPCKHQDQ (%_% ymm5) (%_% ymm3) (%_% ymm5) *)
  0xc4; 0xc1; 0x3d; 0x6c; 0xda;
                           (* VPUNPCKLQDQ (%_% ymm3) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0x6d; 0xd2;
                           (* VPUNPCKHQDQ (%_% ymm10) (%_% ymm8) (%_% ymm10) *)
  0xc5; 0x5d; 0x6c; 0xc6;  (* VPUNPCKLQDQ (%_% ymm8) (%_% ymm4) (%_% ymm6) *)
  0xc5; 0xdd; 0x6d; 0xf6;  (* VPUNPCKHQDQ (%_% ymm6) (%_% ymm4) (%_% ymm6) *)
  0xc4; 0xc1; 0x35; 0x6c; 0xe3;
                           (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0x6d; 0xdb;
                           (* VPUNPCKHQDQ (%_% ymm11) (%_% ymm9) (%_% ymm11) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,320))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xe0; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1504))) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0xc1; 0x45; 0xfe; 0xf8;
                           (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm6) *)
  0xc5; 0xd5; 0xfe; 0xee;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x5d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc3; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x65; 0xfa; 0xe4;  (* VPSUBD (%_% ymm12) (%_% ymm3) (%_% ymm4) *)
  0xc5; 0xe5; 0xfe; 0xdc;  (* VPADDD (%_% ymm3) (%_% ymm3) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xe5;
                           (* VPADDD (%_% ymm4) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xdd;
                           (* VPSUBD (%_% ymm3) (%_% ymm3) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xfe; 0xd3;
                           (* VPADDD (%_% ymm10) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xd5;
                           (* VPSUBD (%_% ymm10) (%_% ymm10) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x12; 0xc8;
                           (* VMOVSLDUP (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x43; 0x45; 0x02; 0xc9; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm7) (%_% ymm9) (Imm8 (word 170)) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x20;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x45; 0x02; 0xc0; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm7) (%_% ymm8) (Imm8 (word 170)) *)
  0xc5; 0xfe; 0x12; 0xfe;  (* VMOVSLDUP (%_% ymm7) (%_% ymm6) *)
  0xc4; 0xe3; 0x55; 0x02; 0xff; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm5) (%_% ymm7) (Imm8 (word 170)) *)
  0xc5; 0xd5; 0x73; 0xd5; 0x20;
                           (* VPSRLQ (%_% ymm5) (%_% ymm5) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x55; 0x02; 0xf6; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm5) (%_% ymm6) (Imm8 (word 170)) *)
  0xc5; 0xfe; 0x12; 0xec;  (* VMOVSLDUP (%_% ymm5) (%_% ymm4) *)
  0xc4; 0xe3; 0x65; 0x02; 0xed; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm3) (%_% ymm5) (Imm8 (word 170)) *)
  0xc5; 0xe5; 0x73; 0xd3; 0x20;
                           (* VPSRLQ (%_% ymm3) (%_% ymm3) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x65; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm3) (%_% ymm4) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x7e; 0x12; 0xdb;
                           (* VMOVSLDUP (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xe3; 0x2d; 0x02; 0xdb; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm10) (%_% ymm3) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x2d; 0x02; 0xdb; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm10) (%_% ymm11) (Imm8 (word 170)) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,448))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x60; 0x06; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1632))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x55; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe5;  (* VMOVSHDUP (%_% ymm12) (%_% ymm5) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x55; 0x28; 0xea;
                           (* VPMULDQ (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xed;  (* VMOVSHDUP (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc3; 0x55; 0x02; 0xec; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm5) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x35; 0xfa; 0xe5;  (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm5) *)
  0xc5; 0x35; 0xfe; 0xcd;  (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xed;
                           (* VPADDD (%_% ymm5) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0x62; 0x5d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc3; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x3d; 0xfa; 0xe4;  (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0x3d; 0xfe; 0xc4;  (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xe5;
                           (* VPADDD (%_% ymm4) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x62; 0x65; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe3;  (* VMOVSHDUP (%_% ymm12) (%_% ymm3) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x65; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm3) (%_% ymm3) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xdb;  (* VMOVSHDUP (%_% ymm3) (%_% ymm3) *)
  0xc4; 0xc3; 0x65; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm3) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x45; 0xfa; 0xe3;  (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xc5; 0xfe; 0xfb;  (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm3) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm3) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm6) (%_% ymm11) *)
  0xc4; 0xc1; 0x4d; 0xfe; 0xf3;
                           (* VPADDD (%_% ymm6) (%_% ymm6) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfa; 0xf5;
                           (* VPSUBD (%_% ymm6) (%_% ymm6) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,576))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xe0; 0x06; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1760))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x45; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm7) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe7;  (* VMOVSHDUP (%_% ymm12) (%_% ymm7) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x45; 0x28; 0xfa;
                           (* VPMULDQ (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xff;  (* VMOVSHDUP (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc3; 0x45; 0x02; 0xfc; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm7) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x35; 0xfa; 0xe7;  (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm7) *)
  0xc5; 0x35; 0xfe; 0xcf;  (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xfd;
                           (* VPADDD (%_% ymm7) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x3d; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm6) *)
  0xc5; 0x3d; 0xfe; 0xc6;  (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xc0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,704))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x60; 0x07; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1888))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x65; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe3;  (* VMOVSHDUP (%_% ymm12) (%_% ymm3) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x65; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm3) (%_% ymm3) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xdb;  (* VMOVSHDUP (%_% ymm3) (%_% ymm3) *)
  0xc4; 0xc3; 0x65; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm3) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe3;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm3) *)
  0xc5; 0xd5; 0xfe; 0xeb;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm3) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm3) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm11) *)
  0xc4; 0xc1; 0x5d; 0xfe; 0xe3;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x40; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,832))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xe0; 0x07; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2016))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x41; 0x35; 0xfe; 0xc8;
                           (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xc0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,960))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x60; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2144))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x45; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm6) *)
  0xc5; 0xc5; 0xfe; 0xfe;  (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x40; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,1088))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xe0; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2272))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x5d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc3; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe4;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm4) *)
  0xc5; 0xd5; 0xfe; 0xec;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xe5;
                           (* VPADDD (%_% ymm4) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xc0; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,1216))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x60; 0x09; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2400))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x65; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xc1; 0x65; 0xfe; 0xdb;
                           (* VPADDD (%_% ymm3) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xdd;
                           (* VPSUBD (%_% ymm3) (%_% ymm3) (%_% ymm13) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,256))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x20; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,288))) (%_% ymm8) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x40; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,320))) (%_% ymm7) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,352))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,384))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0xa0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,416))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0x9f; 0xc0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,448))) (%_% ymm3) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,480))) (%_% ymm11) *)
  0xc5; 0xfd; 0x6f; 0xa7; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,512))) *)
  0xc5; 0xfd; 0x6f; 0xaf; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,544))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,576))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0x60; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,608))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x80; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,640))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xa0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,672))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0xc0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,704))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0xe0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,736))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x98; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,152))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x38; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1336))) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0xc1; 0x5d; 0xfe; 0xe0;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x35; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm9) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe1;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x35; 0x28; 0xca;
                           (* VPMULDQ (%_% ymm9) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc9;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x43; 0x35; 0x02; 0xcc; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm9) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x55; 0xfa; 0xe1;
                           (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0xc1; 0x55; 0xfe; 0xe9;
                           (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xcd;
                           (* VPADDD (%_% ymm9) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0xc1; 0x4d; 0xfe; 0xf2;
                           (* VPADDD (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfa; 0xf5;
                           (* VPSUBD (%_% ymm6) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0xc1; 0x45; 0xfe; 0xfb;
                           (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0xc3; 0x5d; 0x46; 0xd8; 0x20;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm4) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x5d; 0x46; 0xc0; 0x31;
                           (* VPERM2I128 (%_% ymm8) (%_% ymm4) (%_% ymm8) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x55; 0x46; 0xe1; 0x20;
                           (* VPERM2I128 (%_% ymm4) (%_% ymm5) (%_% ymm9) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x55; 0x46; 0xc9; 0x31;
                           (* VPERM2I128 (%_% ymm9) (%_% ymm5) (%_% ymm9) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xea; 0x20;
                           (* VPERM2I128 (%_% ymm5) (%_% ymm6) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x4d; 0x46; 0xd2; 0x31;
                           (* VPERM2I128 (%_% ymm10) (%_% ymm6) (%_% ymm10) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x45; 0x46; 0xf3; 0x20;
                           (* VPERM2I128 (%_% ymm6) (%_% ymm7) (%_% ymm11) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x45; 0x46; 0xdb; 0x31;
                           (* VPERM2I128 (%_% ymm11) (%_% ymm7) (%_% ymm11) (Imm8 (word 49)) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xe0; 0x00; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,224))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x80; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1408))) *)
  0xc4; 0x62; 0x55; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe5;  (* VMOVSHDUP (%_% ymm12) (%_% ymm5) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x55; 0x28; 0xea;
                           (* VPMULDQ (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xed;  (* VMOVSHDUP (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc3; 0x55; 0x02; 0xec; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm5) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x65; 0xfa; 0xe5;  (* VPSUBD (%_% ymm12) (%_% ymm3) (%_% ymm5) *)
  0xc5; 0xe5; 0xfe; 0xdd;  (* VPADDD (%_% ymm3) (%_% ymm3) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xed;
                           (* VPADDD (%_% ymm5) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xdd;
                           (* VPSUBD (%_% ymm3) (%_% ymm3) (%_% ymm13) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0xfe; 0xc2;
                           (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x5d; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm6) *)
  0xc5; 0xdd; 0xfe; 0xe6;  (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0xfe; 0xcb;
                           (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc5; 0xe5; 0x6c; 0xfd;  (* VPUNPCKLQDQ (%_% ymm7) (%_% ymm3) (%_% ymm5) *)
  0xc5; 0xe5; 0x6d; 0xed;  (* VPUNPCKHQDQ (%_% ymm5) (%_% ymm3) (%_% ymm5) *)
  0xc4; 0xc1; 0x3d; 0x6c; 0xda;
                           (* VPUNPCKLQDQ (%_% ymm3) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0x6d; 0xd2;
                           (* VPUNPCKHQDQ (%_% ymm10) (%_% ymm8) (%_% ymm10) *)
  0xc5; 0x5d; 0x6c; 0xc6;  (* VPUNPCKLQDQ (%_% ymm8) (%_% ymm4) (%_% ymm6) *)
  0xc5; 0xdd; 0x6d; 0xf6;  (* VPUNPCKHQDQ (%_% ymm6) (%_% ymm4) (%_% ymm6) *)
  0xc4; 0xc1; 0x35; 0x6c; 0xe3;
                           (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0x6d; 0xdb;
                           (* VPUNPCKHQDQ (%_% ymm11) (%_% ymm9) (%_% ymm11) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x60; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,352))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x00; 0x06; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1536))) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0xc1; 0x45; 0xfe; 0xf8;
                           (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm6) *)
  0xc5; 0xd5; 0xfe; 0xee;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x5d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc3; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x65; 0xfa; 0xe4;  (* VPSUBD (%_% ymm12) (%_% ymm3) (%_% ymm4) *)
  0xc5; 0xe5; 0xfe; 0xdc;  (* VPADDD (%_% ymm3) (%_% ymm3) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xe5;
                           (* VPADDD (%_% ymm4) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xdd;
                           (* VPSUBD (%_% ymm3) (%_% ymm3) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xfe; 0xd3;
                           (* VPADDD (%_% ymm10) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xd5;
                           (* VPSUBD (%_% ymm10) (%_% ymm10) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x12; 0xc8;
                           (* VMOVSLDUP (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x43; 0x45; 0x02; 0xc9; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm7) (%_% ymm9) (Imm8 (word 170)) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x20;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x45; 0x02; 0xc0; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm7) (%_% ymm8) (Imm8 (word 170)) *)
  0xc5; 0xfe; 0x12; 0xfe;  (* VMOVSLDUP (%_% ymm7) (%_% ymm6) *)
  0xc4; 0xe3; 0x55; 0x02; 0xff; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm5) (%_% ymm7) (Imm8 (word 170)) *)
  0xc5; 0xd5; 0x73; 0xd5; 0x20;
                           (* VPSRLQ (%_% ymm5) (%_% ymm5) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x55; 0x02; 0xf6; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm5) (%_% ymm6) (Imm8 (word 170)) *)
  0xc5; 0xfe; 0x12; 0xec;  (* VMOVSLDUP (%_% ymm5) (%_% ymm4) *)
  0xc4; 0xe3; 0x65; 0x02; 0xed; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm3) (%_% ymm5) (Imm8 (word 170)) *)
  0xc5; 0xe5; 0x73; 0xd3; 0x20;
                           (* VPSRLQ (%_% ymm3) (%_% ymm3) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x65; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm3) (%_% ymm4) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x7e; 0x12; 0xdb;
                           (* VMOVSLDUP (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xe3; 0x2d; 0x02; 0xdb; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm10) (%_% ymm3) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x2d; 0x02; 0xdb; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm10) (%_% ymm11) (Imm8 (word 170)) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xe0; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,480))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x80; 0x06; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1664))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x55; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe5;  (* VMOVSHDUP (%_% ymm12) (%_% ymm5) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x55; 0x28; 0xea;
                           (* VPMULDQ (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xed;  (* VMOVSHDUP (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc3; 0x55; 0x02; 0xec; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm5) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x35; 0xfa; 0xe5;  (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm5) *)
  0xc5; 0x35; 0xfe; 0xcd;  (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xed;
                           (* VPADDD (%_% ymm5) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0x62; 0x5d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc3; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x3d; 0xfa; 0xe4;  (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0x3d; 0xfe; 0xc4;  (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xe5;
                           (* VPADDD (%_% ymm4) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x62; 0x65; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe3;  (* VMOVSHDUP (%_% ymm12) (%_% ymm3) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x65; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm3) (%_% ymm3) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xdb;  (* VMOVSHDUP (%_% ymm3) (%_% ymm3) *)
  0xc4; 0xc3; 0x65; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm3) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x45; 0xfa; 0xe3;  (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xc5; 0xfe; 0xfb;  (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm3) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm3) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm6) (%_% ymm11) *)
  0xc4; 0xc1; 0x4d; 0xfe; 0xf3;
                           (* VPADDD (%_% ymm6) (%_% ymm6) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfa; 0xf5;
                           (* VPSUBD (%_% ymm6) (%_% ymm6) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x60; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,608))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x00; 0x07; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1792))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x45; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm7) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe7;  (* VMOVSHDUP (%_% ymm12) (%_% ymm7) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x45; 0x28; 0xfa;
                           (* VPMULDQ (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xff;  (* VMOVSHDUP (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc3; 0x45; 0x02; 0xfc; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm7) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x35; 0xfa; 0xe7;  (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm7) *)
  0xc5; 0x35; 0xfe; 0xcf;  (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xfd;
                           (* VPADDD (%_% ymm7) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x3d; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm6) *)
  0xc5; 0x3d; 0xfe; 0xc6;  (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xe0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,736))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x80; 0x07; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1920))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x65; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe3;  (* VMOVSHDUP (%_% ymm12) (%_% ymm3) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x65; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm3) (%_% ymm3) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xdb;  (* VMOVSHDUP (%_% ymm3) (%_% ymm3) *)
  0xc4; 0xc3; 0x65; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm3) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe3;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm3) *)
  0xc5; 0xd5; 0xfe; 0xeb;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm3) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm3) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm11) *)
  0xc4; 0xc1; 0x5d; 0xfe; 0xe3;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x60; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,864))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x00; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2048))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x41; 0x35; 0xfe; 0xc8;
                           (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xe0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,992))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x80; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2176))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x45; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm6) *)
  0xc5; 0xc5; 0xfe; 0xfe;  (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x60; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,1120))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x00; 0x09; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2304))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x5d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc3; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe4;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm4) *)
  0xc5; 0xd5; 0xfe; 0xec;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xe5;
                           (* VPADDD (%_% ymm4) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0xe0; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,1248))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x80; 0x09; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2432))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x65; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xc1; 0x65; 0xfe; 0xdb;
                           (* VPADDD (%_% ymm3) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xdd;
                           (* VPSUBD (%_% ymm3) (%_% ymm3) (%_% ymm13) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,512))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x20; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,544))) (%_% ymm8) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x40; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,576))) (%_% ymm7) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x60; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,608))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0x80; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,640))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0xa0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,672))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0x9f; 0xc0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,704))) (%_% ymm3) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0xe0; 0x02; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,736))) (%_% ymm11) *)
  0xc5; 0xfd; 0x6f; 0xa7; 0x00; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm4) (Memop Word256 (%% (rdi,768))) *)
  0xc5; 0xfd; 0x6f; 0xaf; 0x20; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm5) (Memop Word256 (%% (rdi,800))) *)
  0xc5; 0xfd; 0x6f; 0xb7; 0x40; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm6) (Memop Word256 (%% (rdi,832))) *)
  0xc5; 0xfd; 0x6f; 0xbf; 0x60; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm7) (Memop Word256 (%% (rdi,864))) *)
  0xc5; 0x7d; 0x6f; 0x87; 0x80; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm8) (Memop Word256 (%% (rdi,896))) *)
  0xc5; 0x7d; 0x6f; 0x8f; 0xa0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm9) (Memop Word256 (%% (rdi,928))) *)
  0xc5; 0x7d; 0x6f; 0x97; 0xc0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm10) (Memop Word256 (%% (rdi,960))) *)
  0xc5; 0x7d; 0x6f; 0x9f; 0xe0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm11) (Memop Word256 (%% (rdi,992))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x8e; 0x9c; 0x00; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm1) (Memop Doubleword (%% (rsi,156))) *)
  0xc4; 0xe2; 0x7d; 0x58; 0x96; 0x3c; 0x05; 0x00; 0x00;
                           (* VPBROADCASTD (%_% ymm2) (Memop Doubleword (%% (rsi,1340))) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0xc1; 0x5d; 0xfe; 0xe0;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x35; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm9) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe1;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm9) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x35; 0x28; 0xca;
                           (* VPMULDQ (%_% ymm9) (%_% ymm9) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc9;
                           (* VMOVSHDUP (%_% ymm9) (%_% ymm9) *)
  0xc4; 0x43; 0x35; 0x02; 0xcc; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm9) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x55; 0xfa; 0xe1;
                           (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0xc1; 0x55; 0xfe; 0xe9;
                           (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm9) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xcd;
                           (* VPADDD (%_% ymm9) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0xc1; 0x4d; 0xfe; 0xf2;
                           (* VPADDD (%_% ymm6) (%_% ymm6) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfa; 0xf5;
                           (* VPSUBD (%_% ymm6) (%_% ymm6) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0xc1; 0x45; 0xfe; 0xfb;
                           (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0xc3; 0x5d; 0x46; 0xd8; 0x20;
                           (* VPERM2I128 (%_% ymm3) (%_% ymm4) (%_% ymm8) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x5d; 0x46; 0xc0; 0x31;
                           (* VPERM2I128 (%_% ymm8) (%_% ymm4) (%_% ymm8) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x55; 0x46; 0xe1; 0x20;
                           (* VPERM2I128 (%_% ymm4) (%_% ymm5) (%_% ymm9) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x55; 0x46; 0xc9; 0x31;
                           (* VPERM2I128 (%_% ymm9) (%_% ymm5) (%_% ymm9) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x4d; 0x46; 0xea; 0x20;
                           (* VPERM2I128 (%_% ymm5) (%_% ymm6) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x4d; 0x46; 0xd2; 0x31;
                           (* VPERM2I128 (%_% ymm10) (%_% ymm6) (%_% ymm10) (Imm8 (word 49)) *)
  0xc4; 0xc3; 0x45; 0x46; 0xf3; 0x20;
                           (* VPERM2I128 (%_% ymm6) (%_% ymm7) (%_% ymm11) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x45; 0x46; 0xdb; 0x31;
                           (* VPERM2I128 (%_% ymm11) (%_% ymm7) (%_% ymm11) (Imm8 (word 49)) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x00; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,256))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xa0; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1440))) *)
  0xc4; 0x62; 0x55; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe5;  (* VMOVSHDUP (%_% ymm12) (%_% ymm5) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x55; 0x28; 0xea;
                           (* VPMULDQ (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xed;  (* VMOVSHDUP (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc3; 0x55; 0x02; 0xec; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm5) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x65; 0xfa; 0xe5;  (* VPSUBD (%_% ymm12) (%_% ymm3) (%_% ymm5) *)
  0xc5; 0xe5; 0xfe; 0xdd;  (* VPADDD (%_% ymm3) (%_% ymm3) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xed;
                           (* VPADDD (%_% ymm5) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xdd;
                           (* VPSUBD (%_% ymm3) (%_% ymm3) (%_% ymm13) *)
  0xc4; 0x62; 0x2d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm10) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe2;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x2d; 0x28; 0xd2;
                           (* VPMULDQ (%_% ymm10) (%_% ymm10) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xd2;
                           (* VMOVSHDUP (%_% ymm10) (%_% ymm10) *)
  0xc4; 0x43; 0x2d; 0x02; 0xd4; 0xaa;
                           (* VPBLENDD (%_% ymm10) (%_% ymm10) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xe2;
                           (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0xfe; 0xc2;
                           (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xd5;
                           (* VPADDD (%_% ymm10) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x5d; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm6) *)
  0xc5; 0xdd; 0xfe; 0xe6;  (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0xfe; 0xcb;
                           (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc5; 0xe5; 0x6c; 0xfd;  (* VPUNPCKLQDQ (%_% ymm7) (%_% ymm3) (%_% ymm5) *)
  0xc5; 0xe5; 0x6d; 0xed;  (* VPUNPCKHQDQ (%_% ymm5) (%_% ymm3) (%_% ymm5) *)
  0xc4; 0xc1; 0x3d; 0x6c; 0xda;
                           (* VPUNPCKLQDQ (%_% ymm3) (%_% ymm8) (%_% ymm10) *)
  0xc4; 0x41; 0x3d; 0x6d; 0xd2;
                           (* VPUNPCKHQDQ (%_% ymm10) (%_% ymm8) (%_% ymm10) *)
  0xc5; 0x5d; 0x6c; 0xc6;  (* VPUNPCKLQDQ (%_% ymm8) (%_% ymm4) (%_% ymm6) *)
  0xc5; 0xdd; 0x6d; 0xf6;  (* VPUNPCKHQDQ (%_% ymm6) (%_% ymm4) (%_% ymm6) *)
  0xc4; 0xc1; 0x35; 0x6c; 0xe3;
                           (* VPUNPCKLQDQ (%_% ymm4) (%_% ymm9) (%_% ymm11) *)
  0xc4; 0x41; 0x35; 0x6d; 0xdb;
                           (* VPUNPCKHQDQ (%_% ymm11) (%_% ymm9) (%_% ymm11) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x80; 0x01; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,384))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x20; 0x06; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1568))) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x45; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0xc1; 0x45; 0xfe; 0xf8;
                           (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm6) *)
  0xc5; 0xd5; 0xfe; 0xee;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x5d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc3; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x65; 0xfa; 0xe4;  (* VPSUBD (%_% ymm12) (%_% ymm3) (%_% ymm4) *)
  0xc5; 0xe5; 0xfe; 0xdc;  (* VPADDD (%_% ymm3) (%_% ymm3) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xe5;
                           (* VPADDD (%_% ymm4) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xdd;
                           (* VPSUBD (%_% ymm3) (%_% ymm3) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x62; 0x1d; 0x28; 0xf1;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm1) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x62; 0x1d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm2) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x2d; 0xfe; 0xd3;
                           (* VPADDD (%_% ymm10) (%_% ymm10) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x2d; 0xfa; 0xd5;
                           (* VPSUBD (%_% ymm10) (%_% ymm10) (%_% ymm13) *)
  0xc4; 0x41; 0x7e; 0x12; 0xc8;
                           (* VMOVSLDUP (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x43; 0x45; 0x02; 0xc9; 0xaa;
                           (* VPBLENDD (%_% ymm9) (%_% ymm7) (%_% ymm9) (Imm8 (word 170)) *)
  0xc5; 0xc5; 0x73; 0xd7; 0x20;
                           (* VPSRLQ (%_% ymm7) (%_% ymm7) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x45; 0x02; 0xc0; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm7) (%_% ymm8) (Imm8 (word 170)) *)
  0xc5; 0xfe; 0x12; 0xfe;  (* VMOVSLDUP (%_% ymm7) (%_% ymm6) *)
  0xc4; 0xe3; 0x55; 0x02; 0xff; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm5) (%_% ymm7) (Imm8 (word 170)) *)
  0xc5; 0xd5; 0x73; 0xd5; 0x20;
                           (* VPSRLQ (%_% ymm5) (%_% ymm5) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x55; 0x02; 0xf6; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm5) (%_% ymm6) (Imm8 (word 170)) *)
  0xc5; 0xfe; 0x12; 0xec;  (* VMOVSLDUP (%_% ymm5) (%_% ymm4) *)
  0xc4; 0xe3; 0x65; 0x02; 0xed; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm3) (%_% ymm5) (Imm8 (word 170)) *)
  0xc5; 0xe5; 0x73; 0xd3; 0x20;
                           (* VPSRLQ (%_% ymm3) (%_% ymm3) (Imm8 (word 32)) *)
  0xc4; 0xe3; 0x65; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm3) (%_% ymm4) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x7e; 0x12; 0xdb;
                           (* VMOVSLDUP (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xe3; 0x2d; 0x02; 0xdb; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm10) (%_% ymm3) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x2d; 0x73; 0xd2; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm10) (Imm8 (word 32)) *)
  0xc4; 0x43; 0x2d; 0x02; 0xdb; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm10) (%_% ymm11) (Imm8 (word 170)) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x00; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,512))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xa0; 0x06; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1696))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x55; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm5) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe5;  (* VMOVSHDUP (%_% ymm12) (%_% ymm5) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x55; 0x28; 0xea;
                           (* VPMULDQ (%_% ymm5) (%_% ymm5) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xed;  (* VMOVSHDUP (%_% ymm5) (%_% ymm5) *)
  0xc4; 0xc3; 0x55; 0x02; 0xec; 0xaa;
                           (* VPBLENDD (%_% ymm5) (%_% ymm5) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x35; 0xfa; 0xe5;  (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm5) *)
  0xc5; 0x35; 0xfe; 0xcd;  (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm5) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xed;
                           (* VPADDD (%_% ymm5) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0x62; 0x5d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc3; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x3d; 0xfa; 0xe4;  (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm4) *)
  0xc5; 0x3d; 0xfe; 0xc4;  (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xe5;
                           (* VPADDD (%_% ymm4) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc4; 0x62; 0x65; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe3;  (* VMOVSHDUP (%_% ymm12) (%_% ymm3) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x65; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm3) (%_% ymm3) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xdb;  (* VMOVSHDUP (%_% ymm3) (%_% ymm3) *)
  0xc4; 0xc3; 0x65; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm3) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x45; 0xfa; 0xe3;  (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm3) *)
  0xc5; 0xc5; 0xfe; 0xfb;  (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm3) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm3) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x4d; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm6) (%_% ymm11) *)
  0xc4; 0xc1; 0x4d; 0xfe; 0xf3;
                           (* VPADDD (%_% ymm6) (%_% ymm6) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x4d; 0xfa; 0xf5;
                           (* VPSUBD (%_% ymm6) (%_% ymm6) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x80; 0x02; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,640))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x20; 0x07; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1824))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x45; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm7) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe7;  (* VMOVSHDUP (%_% ymm12) (%_% ymm7) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x45; 0x28; 0xfa;
                           (* VPMULDQ (%_% ymm7) (%_% ymm7) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xff;  (* VMOVSHDUP (%_% ymm7) (%_% ymm7) *)
  0xc4; 0xc3; 0x45; 0x02; 0xfc; 0xaa;
                           (* VPBLENDD (%_% ymm7) (%_% ymm7) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x35; 0xfa; 0xe7;  (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm7) *)
  0xc5; 0x35; 0xfe; 0xcf;  (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm7) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xfd;
                           (* VPADDD (%_% ymm7) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x3d; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm8) (%_% ymm6) *)
  0xc5; 0x3d; 0xfe; 0xc6;  (* VPADDD (%_% ymm8) (%_% ymm8) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x3d; 0xfa; 0xc5;
                           (* VPSUBD (%_% ymm8) (%_% ymm8) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x00; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,768))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xa0; 0x07; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,1952))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x65; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm3) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe3;  (* VMOVSHDUP (%_% ymm12) (%_% ymm3) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x65; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm3) (%_% ymm3) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xdb;  (* VMOVSHDUP (%_% ymm3) (%_% ymm3) *)
  0xc4; 0xc3; 0x65; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm3) (%_% ymm3) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe3;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm3) *)
  0xc5; 0xd5; 0xfe; 0xeb;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm3) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm3) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x5d; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm4) (%_% ymm11) *)
  0xc4; 0xc1; 0x5d; 0xfe; 0xe3;
                           (* VPADDD (%_% ymm4) (%_% ymm4) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x5d; 0xfa; 0xe5;
                           (* VPSUBD (%_% ymm4) (%_% ymm4) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x80; 0x03; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,896))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x20; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2080))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x3d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm8) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe0;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm8) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x3d; 0x28; 0xc2;
                           (* VPMULDQ (%_% ymm8) (%_% ymm8) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xc0;
                           (* VMOVSHDUP (%_% ymm8) (%_% ymm8) *)
  0xc4; 0x43; 0x3d; 0x02; 0xc4; 0xaa;
                           (* VPBLENDD (%_% ymm8) (%_% ymm8) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x35; 0xfa; 0xe0;
                           (* VPSUBD (%_% ymm12) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x41; 0x35; 0xfe; 0xc8;
                           (* VPADDD (%_% ymm9) (%_% ymm9) (%_% ymm8) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xc5;
                           (* VPADDD (%_% ymm8) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0x41; 0x35; 0xfa; 0xcd;
                           (* VPSUBD (%_% ymm9) (%_% ymm9) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x00; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,1024))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xa0; 0x08; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2208))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x4d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm6) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe6;  (* VMOVSHDUP (%_% ymm12) (%_% ymm6) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x4d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm6) (%_% ymm6) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xf6;  (* VMOVSHDUP (%_% ymm6) (%_% ymm6) *)
  0xc4; 0xc3; 0x4d; 0x02; 0xf4; 0xaa;
                           (* VPBLENDD (%_% ymm6) (%_% ymm6) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x45; 0xfa; 0xe6;  (* VPSUBD (%_% ymm12) (%_% ymm7) (%_% ymm6) *)
  0xc5; 0xc5; 0xfe; 0xfe;  (* VPADDD (%_% ymm7) (%_% ymm7) (%_% ymm6) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xf5;
                           (* VPADDD (%_% ymm6) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x45; 0xfa; 0xfd;
                           (* VPSUBD (%_% ymm7) (%_% ymm7) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x80; 0x04; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,1152))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0x20; 0x09; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2336))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x5d; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm4) (%_% ymm1) *)
  0xc5; 0x7e; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm12) (%_% ymm4) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0xe2; 0x5d; 0x28; 0xe2;
                           (* VPMULDQ (%_% ymm4) (%_% ymm4) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc5; 0xfe; 0x16; 0xe4;  (* VMOVSHDUP (%_% ymm4) (%_% ymm4) *)
  0xc4; 0xc3; 0x5d; 0x02; 0xe4; 0xaa;
                           (* VPBLENDD (%_% ymm4) (%_% ymm4) (%_% ymm12) (Imm8 (word 170)) *)
  0xc5; 0x55; 0xfa; 0xe4;  (* VPSUBD (%_% ymm12) (%_% ymm5) (%_% ymm4) *)
  0xc5; 0xd5; 0xfe; 0xec;  (* VPADDD (%_% ymm5) (%_% ymm5) (%_% ymm4) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0xc1; 0x1d; 0xfe; 0xe5;
                           (* VPADDD (%_% ymm4) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x55; 0xfa; 0xed;
                           (* VPSUBD (%_% ymm5) (%_% ymm5) (%_% ymm13) *)
  0xc5; 0xfd; 0x6f; 0x8e; 0x00; 0x05; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm1) (Memop Word256 (%% (rsi,1280))) *)
  0xc5; 0xfd; 0x6f; 0x96; 0xa0; 0x09; 0x00; 0x00;
                           (* VMOVDQA (%_% ymm2) (Memop Word256 (%% (rsi,2464))) *)
  0xc5; 0xad; 0x73; 0xd1; 0x20;
                           (* VPSRLQ (%_% ymm10) (%_% ymm1) (Imm8 (word 32)) *)
  0xc5; 0x7e; 0x16; 0xfa;  (* VMOVSHDUP (%_% ymm15) (%_% ymm2) *)
  0xc4; 0x62; 0x25; 0x28; 0xe9;
                           (* VPMULDQ (%_% ymm13) (%_% ymm11) (%_% ymm1) *)
  0xc4; 0x41; 0x7e; 0x16; 0xe3;
                           (* VMOVSHDUP (%_% ymm12) (%_% ymm11) *)
  0xc4; 0x42; 0x1d; 0x28; 0xf2;
                           (* VPMULDQ (%_% ymm14) (%_% ymm12) (%_% ymm10) *)
  0xc4; 0x62; 0x25; 0x28; 0xda;
                           (* VPMULDQ (%_% ymm11) (%_% ymm11) (%_% ymm2) *)
  0xc4; 0x42; 0x1d; 0x28; 0xe7;
                           (* VPMULDQ (%_% ymm12) (%_% ymm12) (%_% ymm15) *)
  0xc4; 0x62; 0x15; 0x28; 0xe8;
                           (* VPMULDQ (%_% ymm13) (%_% ymm13) (%_% ymm0) *)
  0xc4; 0x62; 0x0d; 0x28; 0xf0;
                           (* VPMULDQ (%_% ymm14) (%_% ymm14) (%_% ymm0) *)
  0xc4; 0x41; 0x7e; 0x16; 0xdb;
                           (* VMOVSHDUP (%_% ymm11) (%_% ymm11) *)
  0xc4; 0x43; 0x25; 0x02; 0xdc; 0xaa;
                           (* VPBLENDD (%_% ymm11) (%_% ymm11) (%_% ymm12) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x65; 0xfa; 0xe3;
                           (* VPSUBD (%_% ymm12) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0xc1; 0x65; 0xfe; 0xdb;
                           (* VPADDD (%_% ymm3) (%_% ymm3) (%_% ymm11) *)
  0xc4; 0x41; 0x7e; 0x16; 0xed;
                           (* VMOVSHDUP (%_% ymm13) (%_% ymm13) *)
  0xc4; 0x43; 0x15; 0x02; 0xee; 0xaa;
                           (* VPBLENDD (%_% ymm13) (%_% ymm13) (%_% ymm14) (Imm8 (word 170)) *)
  0xc4; 0x41; 0x1d; 0xfe; 0xdd;
                           (* VPADDD (%_% ymm11) (%_% ymm12) (%_% ymm13) *)
  0xc4; 0xc1; 0x65; 0xfa; 0xdd;
                           (* VPSUBD (%_% ymm3) (%_% ymm3) (%_% ymm13) *)
  0xc5; 0x7d; 0x7f; 0x8f; 0x00; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,768))) (%_% ymm9) *)
  0xc5; 0x7d; 0x7f; 0x87; 0x20; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,800))) (%_% ymm8) *)
  0xc5; 0xfd; 0x7f; 0xbf; 0x40; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,832))) (%_% ymm7) *)
  0xc5; 0xfd; 0x7f; 0xb7; 0x60; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,864))) (%_% ymm6) *)
  0xc5; 0xfd; 0x7f; 0xaf; 0x80; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,896))) (%_% ymm5) *)
  0xc5; 0xfd; 0x7f; 0xa7; 0xa0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,928))) (%_% ymm4) *)
  0xc5; 0xfd; 0x7f; 0x9f; 0xc0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,960))) (%_% ymm3) *)
  0xc5; 0x7d; 0x7f; 0x9f; 0xe0; 0x03; 0x00; 0x00;
                           (* VMOVDQA (Memop Word256 (%% (rdi,992))) (%_% ymm11) *)
  0xc3                     (* RET *)
];;