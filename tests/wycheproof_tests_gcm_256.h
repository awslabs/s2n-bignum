// Wycheproof AES-256-GCM known-answer vectors for aesv8_gcm_8x_enc_256.
//
// Source: C2SP/wycheproof  <https://github.com/C2SP/wycheproof>
//   testvectors_v1/aes_gcm_test.json  (schema aead_test_schema_v1, "AES-GCM",
//   numberOfTests: 316), as vendored in aws-lc at commit
//   47b0bb8cb6910304c1a53c0ba941282a51ecdda3, path
//   third_party/vectors/upstream/wycheproof/testvectors_v1/aes_gcm_test.json .
//
// Filter applied (our kernel's contract): keySize==256 (32-byte key),
// ivSize==96 (12-byte IV), tagSize==128 (16-byte tag), result=="valid", and a
// plaintext that is a nonzero whole number of 16-byte blocks. Of the 316
// records this keeps 7 (the AES-256 / 12-byte-IV group has 39 valid vectors, of
// which 32 have partial-block plaintexts that are out of the whole-blocks
// contract and are therefore skipped). Each kept vector's tcId is noted.
//
// Every field is verbatim from the JSON. Driven through the same setup path as
// the aws-lc KAT vectors (derive H-table + J0 from key/IV with the C reference,
// then call the kernel) and cross-checked against the pure-C GCM reference.
//
// DO NOT EDIT: these hex strings are the exact Wycheproof test bytes.

  // tcId 97: pt=16 bytes (1 block), aad=0 bytes, iv=12 bytes, flags=Pseudorandom
  GCM_KAT("59d4eafb4de0cfc7d3db99a8f54b15d7b39f0acc8da69763b019c1699f87674a",
          "2fcb1b38a99e71b84740ad9b",
          "",
          "549b365af913f3b081131ccb6b825588",
          "f58c16690122d75356907fd96b570fca",
          "28752c20153092818faba2a334640d6e");

  // tcId 105: pt=64 bytes (4 blocks), aad=0 bytes, iv=12 bytes, flags=Pseudorandom
  GCM_KAT("5b1d1035c0b17ee0b0444767f80a25b8c1b741f4b50a4d3052226baa1c6fb701",
          "d61040a313ed492823cc065b",
          "",
          "d096803181beef9e008ff85d5ddc38ddacf0f09ee5f7e07f1e4079cb64d0dc8f5e6711cd4921a7887de76e2678fdc67618f1185586bfea9d4c685d50e4bb9a82",
          "c7d191b601f86c28b6a1bdef6a57b4f6ee3ae417bc125c381cdf1c4dac184ed1d84f1196206d62cad112b038845720e02c061179a8836f02b93fa7008379a6bf",
          "f15612f6c40f2e0db6dc76fc4822fcfe");

  // tcId 108: pt=128 bytes (8 blocks), aad=0 bytes, iv=12 bytes, flags=Pseudorandom
  GCM_KAT("d7addd3889fadf8c893eee14ba2b7ea5bf56b449904869615bd05d5f114cf377",
          "8a3ad26b28cd13ba6504e260",
          "",
          "c877a76bf595560772167c6e3bcc705305db9c6fcbeb90f4fea85116038bc53c3fa5b4b4ea0de5cc534fbe1cf9ae44824c6c2c0a5c885bd8c3cdc906f12675737e434b983e1e231a52a275db5fb1a0cac6a07b3b7dcb19482a5d3b06a9317a54826cea6b36fce452fa9b5475e2aaf25499499d8a8932a19eb987c903bd8502fe",
          "53cc8c920a85d1accb88636d08bbe4869bfdd96f437b2ec944512173a9c0fe7a47f8434133989ba77dda561b7e3701b9a83c3ba7660c666ba59fef96598eb621544c63806d509ac47697412f9564eb0a2e1f72f6599f5666af34cffca06573ffb4f47b02f59f21c64363daecb977b4415f19fdda3c9aae5066a57b669ffaa257",
          "5e63374b519e6c3608321943d790cf9a");

  // tcId 111: pt=256 bytes (16 blocks), aad=0 bytes, iv=12 bytes, flags=Pseudorandom
  GCM_KAT("dc4dbf811f9509e33a45a8a0743e9391de333f69c56ee4f0fe90ce21c238ee59",
          "1859d3ba4710cdd300baa029",
          "",
          "df91c48591f4cae8c4d659d024dfd0a3535981487764bf19b012713e6ac6d578aa0b3a51d7ac97cd503fdc8682cabdb6a5256e9890458356f39b9749f6ab158112fbe4f91acd333477998b9f0d7cc0be2d40acfa5103adc1b0d0a5cc94733d703e0d8c26e09e9d079fa6a65cf35240a16280826ab7c0d8ac5882c89e58444233c2f60aaae0cbd1a7ed850065242a9378c340232fd86f1fd52a92c960a9a86f529f431acf3aa94133785803f4ac1a22378332daa22dea3d34d2fdb7c308fa44ab93b3fb02f428be22fad6c0b10c138af97b92a199296dd947c93fbc40674c34c5623d26d9c90dc6b3357018b9f9250fb4dd5c11518191a236745a2bd42f863766",
          "9c511d08f244cb6971a39b70639c4a53ae48254fcb3d2eea4796ecc996f1fe26a8e30932258a48fe4237e5bfb0e1320dc591256dc83cd56dbf5d9b377b7805b7fac0497b2f99e3310e9e2cc8009141a82f26f8a02299d64138bb1fe8a1243df3e9fb37b52bd3c2cc19f543b3f4928e5a73730a7a6e6d75919d117d3dfe10e863a9846b2ca260de5dddba7ceac37019e615b89a2ab94df8d1a790749998cb8531fef1ef5f8a28a8ad60e813f7e78412ca4d95b9604a24a16e4a3ca8ee33bfbb7809048014943e5fd7966a7db214e052d1cc546a6da72ec89d1c3398aefdcb881dfc3d800b7323abcd7583e9c8a31f03b6995d4aeac17c5a56d8af492a2b108fe3",
          "17090ce50e35244a59bafc80eba5dae5");

  // tcId 114: pt=512 bytes (32 blocks), aad=0 bytes, iv=12 bytes, flags=Pseudorandom
  GCM_KAT("6aada828b2273ffb81dc794a8629e305cb646f9d266002bd313427d384838767",
          "00dea4505cd5396f6ba408a5",
          "",
          "1d99ee022f9576ed69af8a7f3945362ab0c4691a4d333a3f5f85cf8d7db7fb8a069b48998cf286ffa4615e87398c3c3c1295d5bee272bdeb5166470a8923f7b79dc92b2a97de34ba87db2907ac84fb23d38f2e1af835f737488fc04fac70432d3a0b02a472f851025803aac692273273e27be1dd9679a4d626997c363ba706a7db1f4cdc07fe3c67fbec0aa8619038e05607d95a5ddc4b403cd6dabc41790adb6cd76eaeac3491c3cd6a8787e0f29c042b4e2afe987674b9495ef55768c696bc6c3df1c1e9a7c0456f478a1a1cc4c3a9b0f2cd3b42db8d0b6aa36dfec3d2c08d1398eeb75db61ae902d2da5a1efac7904b8ae32af1ff942c99769504bb5c56f5819e4f899e8bbacfd4682d82f41e179a9ddf9a0820cc4316f252d1d35597aeda43ab870887e67aabe79f046b03a9a83588994058a07baedbbbf9c01d833732efac89ae8173f902e831d579d31e4a409cef5e494a27bb6367e84fc57642048e44d687ce73dd9e71384182b262d63a715698132f218fc2c3611ed0dbf814799866c8c43b4aa7c13b5a53f9a337627d76bb960f60fa891f0076a538c396500cefd2dd1e4e024f9d83275f9b2c0ce6df41bb6488398fc657dba0efdae0019dd31b03227edc5229aff60cd083c0f0b66675baaf91c3206819a0c985bc3283600e9e6d62c6fab2c6aefd69829c75063c54ad11269ac5ec563ecd870c2af4cde6cec43e",
          "75750a143887ad763c130a637e5d75fc7b53999e8a085a74a5c7e4e2658d03586f36dd67bdd0622992fc440822e63534391a435c934fa7fa19f5196695513ac812e778928a677af37a8bc36a19b7e3ab05e185429aa5e5e17cacdd8971e3c551db83c585324277843c1783771379280d1393eeb26e9e7ff7006d437b7cb0fe373b2dc3238d87badf9edd767ad7b4726a777b99cd1d11f1bc16098b1230a194bd9435caa0730276ebc0c44a923e3a14751e125aa7100cbd682202f9a71bf08e28ae36f55c6fce998a4c474dd5a5d55d25aef332c3b4640e20b222b7305dfc21f60e9f5dd97c1987120ba0b7b7e85ce810f378d401987b824679ffe45ccade89e5ed45176bab9d4a14c5a753d32e113a2aba5dfe65ac75918afed6cb2122cf24971fab932b64e104a8a01c755b4fb86afd49d0ce1a1909192551f579c3587d1a61ba5b0415cf90d572320af3b0c5d5d672d4207228e75322fffb621200fcb53d970f6a74e06bd90d8f9a1cf23c87c07deb14456dc21d84b8f6ca45b8c3af6d6d5c110488c919617c116c25baef4a7a0d47a4b247c94440176dd54a014d639a6139d83498a585b5687cea859dbb32b852690c4dcd23ae4058498ee751aec8aff3b0f1f0efd4bb50636d1182e111a6a98f95f2d55f8f4e75c1ae8a55e851c5095bcd9d1ad86fc79b0bf9ad2f58293a624c2504b30469f7ed1c645549d37177dfcd95",
          "8fba48dab18a4beaddff24252e62083a");

  // tcId 128: pt=16 bytes (1 block), aad=0 bytes, iv=12 bytes, flags=SpecialCase
  GCM_KAT("00112233445566778899aabbccddeeff102132435465768798a9bacbdcedfe0f",
          "000000000000000000000000",
          "",
          "561008fa07a68f5c61285cd013464eaf",
          "23293e9b07ca7d1b0cae7cc489a973b3",
          "ffffffffffffffffffffffffffffffff");

  // tcId 129: pt=16 bytes (1 block), aad=0 bytes, iv=12 bytes, flags=SpecialCase
  GCM_KAT("00112233445566778899aabbccddeeff102132435465768798a9bacbdcedfe0f",
          "ffffffffffffffffffffffff",
          "",
          "c6152244cea1978d3e0bc274cf8c0b3b",
          "7cb6fc7c6abc009efe9551a99f36a421",
          "00000000000000000000000000000000");

