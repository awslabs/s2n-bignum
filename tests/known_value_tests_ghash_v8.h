// Known-answer vectors for gcm_ghash_v8_s2n, as (n, H, Xi_in, input, Xi_out).
//
// PROVENANCE. aws-lc has no GHASH-only test-vector file: gcm_tests.txt holds
// full AEAD vectors (key/nonce/aad/ct/tag, not GHASH state transitions) and
// gcm_test.cc's GHASH coverage is an ABI test carrying no expected values. So
// the expected Xi_out values below are COMPUTED BY the VERBATIM aws-lc
// reference `gcm_ghash_nohw` (tests/ref_gcm_nohw.c, copied byte-for-byte from
// aws-lc crypto/fipsmodule/modes/gcm_nohw.c at commit 83e7c97c6), with the
// nohw-format key table built by the equally verbatim `gcm_init_nohw` from the
// same file. No value here was invented or hand-computed: each is the output of
// unmodified aws-lc code on the stated input.
//
// The H / Xi_in / input bytes come from a splitmix64 stream seeded with
// 0x6763686173687638, so the whole table is reproducible; the block counts are
// chosen to hit every distinct trace through the assembly:
//
//   n =  1, 2, 3   the len < 64 path (three separate straight-line traces)
//   n =  4         the 4x path, zero .Loop4x iterations, .Ldone4x tail
//   n =  5, 7      the 4x path, zero .Loop4x iterations, .Lone / .Lthree tails
//   n =  8         one .Loop4x iteration, .Ldone4x tail
//   n = 11         one .Loop4x iteration, .Lthree tail
//   n = 17         multiple .Loop4x iterations, .Lone tail
//
// GHASH_KAT(n, H, Xi_in, input, Xi_out) is defined by the caller in test.c.

  GHASH_KAT( 1, "8e38a21c6073db9aa134730083bf211d",
       "4ebc8af7e6c96915a00b2f0e3d4c13d8",
       "a90d4d08a0849329613064b178889687",
       "320ad8194a20816e45949bd16c660887" )
  GHASH_KAT( 2, "d5fe4bd4ec282b49bf3463c9074461dc",
       "f9f4b0792c4a0faa0c3ef923f341d503",
       "6cfe078c67f9b2eab6d9dac583f815963852c1199f037162e84c7c6e32e1b08c",
       "6aacef6328e92518fe5d98d0b4599481" )
  GHASH_KAT( 3, "f8dcac631686b653e339380ce57ccf4b",
       "03a00195b13992558edd646cab1b3ded",
       "4da086044365d09a2c0d93dd7d2f3d1740cc007820664cc4887b852fca6f9e609fa2b3ac61dbe871bd6d0ade4c812254",
       "4899b525656daa889e75d29fd139b0fe" )
  GHASH_KAT( 4, "44195dfa6eefcb5617b4882db554e32a",
       "53e2928bc24bb37877d1292bccc08ffe",
       "ada77e1e55ca04a780ae1fb35c1cbd791b1609c62174e9f1a439c3df2d88fdfbbaf2b28a02689935bf62f76a892fa45b28016f5455024279fe3c9716f6a0ea8b",
       "204adaf598be4060b5ec2251e1c3ed8c" )
  GHASH_KAT( 5, "da2fa7ab7fc296b54435f66b90d45b75",
       "fabfd5cbda32c71fe2fbf3a50ea87f2c",
       "acca041b22557b692e84327e05e85cc3f6e1eabf15fa634c2949f6424c4de07268b633bcd4291bbc5d00c99b05ed46479773d6e29b59692a6743e68c5d302bb8622063724f047d8f4d658c77caabebe0",
       "45de0f243dbcc9d4c335ff077dc8e743" )
  GHASH_KAT( 7, "87767406db2241b9db83c33364135dfa",
       "b0f8c1985475450cdf71b9824e4f0832",
       "ab413e5c6a9fcb98e019047dd8d6cced0e69d220d94153358afee57065218037e98fbce67d6c0ea283b660784d7f3437d778a387f520a3b7bc5f6dbd2702ac4cd373cf188002d9bb1cd2942a68a02c3070400d1959516bf77da4035f16f1d9628f64fce779a672ea43d13124202830ed",
       "5f48d7f2007c473ded9c256c1ed7c498" )
  GHASH_KAT( 8, "51127d877e73fd571a6f85a6d570a0e6",
       "c11516fd1ad01a181c5e7a41637444df",
       "eb0e6781ae2ca1c67745b2a78a66130b904b9e1b5221ace7bee214028ac645a3fef046bc6af702affa3e4ed078877b4455605d2c0af7750b4bfcadc0e87ead554f5d56abb915c16f82cfe0cc29b4f40215bd4f8801c8aba61c64a199e82ae4750d091d19d5e673678f300ce0dde23d90d1258fecddc1aab865a0e475c77df7d5",
       "78e46cd52f7568920601b53062a6ebec" )
  GHASH_KAT(11, "cd2effee80b1afd5c58f51f0b6bc7f1f",
       "cabeb38e9740aa37f3677a489ce0c3c8",
       "0e328c1e1220417a2f41a5d86415b4011e1f935f2c3ab18ea9395fb6ff1fc612334f06bb1c6b2f912a473ac80dbf26893233f7c70b081128acba82cc485cd0abc8376d140800eb8e13f7460ad55d17e914d8d55db0f4b6333c1763f016bfe51fa42e6cdde9fc5e359e3c33b5b9fecd0e5cae0c75e8d6d367e17c473783017138a3853f6e25970b583b2d1ef27e036090bf6166873d51de24be80cadb8f297f0a8d679327b4db25f73fefbd007f8811df",
       "ed03bfed79e4a8803bbb8b675f62e4e1" )
  GHASH_KAT(17, "ce63501f50c1fe6edf25cb3b149cc19a",
       "d548563a422122242aecb0613e52209a",
       "a779acc8a0a8863c852cfe70183f9bdac7c89c95d8162298c97a423c068e506125f1532849974bf2167a0db49dd346d27de8bb7e0bbc263bf69bf9d396560c3f4ded7f40ef8b969f80cf8a29013812877eb320b4541e359c84872a454f667cd33a60fe1023fd266aa2178a09aa80e2e3f1f8f6bd4affe152dfb0c495a48f3a460e8c629097b0a66102a1ca0cc8c0bfefa22914a6870f934be78d568db41a7047d7334124bcc38b03b0f8a92b3ddf45b9ef427598c8d698bead1455675ebe5c314af5b927c685a09471a9499d9c7cc3e4f44bcb0fedaa2943735d146335d2d53985ea6a7f3465b2ac8b9ce27be0755bc7278b1c2515b847cf08e43c91d817a674eaf2ab3f5f9f6fa46b837b9fc3c1a3d8",
       "230024decb284076bd1a7f5dda2074a5" )
