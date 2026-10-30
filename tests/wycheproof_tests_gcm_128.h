// Wycheproof AES-128-GCM vectors whose plaintext is a whole number of
// 16-byte blocks.
//
// Source: Wycheproof (https://github.com/C2SP/wycheproof),
// testvectors_v1/aes_gcm_test.json ("numberOfTests": 316) as vendored in
// aws-lc at third_party/vectors/upstream/wycheproof/testvectors_v1/, checked
// against aws-lc commit 83e7c97c6d5d13023c65a11a79ab0e09f1b6b30a.  These are
// all 21 of its test cases with keySize 128, tagSize 128, result "valid" and a
// plaintext ("msg") that is a nonzero whole number of 16-byte blocks: 1, 2,
// 4, 8, 16 or 32 blocks, AAD of 0 to 16 bytes, and IVs of 1, 2, 4, 6, 8, 10,
// 12 or 16 bytes, including IVs shorter than 12 bytes, which the aws-lc set
// above lacks.
//
// Each record is GCM_KAT(key, iv, aad, msg, ct, tag): the fields of the test
// case with the tcId given, copied verbatim.  The including file defines
// GCM_KAT, to test encryption (msg to ct and tag) or decryption (ct to msg and
// tag).
//
// DO NOT EDIT: these hex strings are the exact Wycheproof test bytes.

  // Wycheproof tcId 1: pt=16 bytes, aad=0 bytes, iv=12 bytes
  GCM_KAT("5b9604fe14eadba931b0ccf34843dab9",
          "028318abc1824029138141a2",
          "",
          "001d0c231287c1182784554ca3a21908",
          "26073cc1d851beff176384dc9896d5ff",
          "0a3ea7a5487cb5f7d70fb6c58d038554");

  // Wycheproof tcId 2: pt=16 bytes, aad=16 bytes, iv=12 bytes
  GCM_KAT("5b9604fe14eadba931b0ccf34843dab9",
          "921d2507fa8007b7bd067d34",
          "00112233445566778899aabbccddeeff",
          "001d0c231287c1182784554ca3a21908",
          "49d8b9783e911913d87094d1f63cc765",
          "1e348ba07cca2cf04c618cb4d43a5b92");

  // Wycheproof tcId 3: pt=16 bytes, aad=8 bytes, iv=12 bytes
  GCM_KAT("aa023d0478dcb2b2312498293d9a9129",
          "0432bc49ac34412081288127",
          "aac39231129872a2",
          "2035af313d1346ab00154fea78322105",
          "eea945f3d0f98cc0fbab472a0cf24e87",
          "4bb9b4812519dadf9e1232016d068133");

  // Wycheproof tcId 8: pt=16 bytes, aad=0 bytes, iv=12 bytes
  GCM_KAT("ffdf4228361ea1f8165852136b3480f7",
          "0e1666f2dc652f7708fb8f0d",
          "",
          "25b12e28ac0ef6ead0226a3b2288c800",
          "f7bd379d130477176b8bb3cb23dbbbaa",
          "1ee6513ce30c7873f59dd4350a588f42");

  // Wycheproof tcId 16: pt=64 bytes, aad=0 bytes, iv=12 bytes
  GCM_KAT("e12260fcd355a51a0d01bb1f6fa538c2",
          "5dfc37366f5688275147d3f9",
          "",
          "d902deeab175c008329a33bfaccd5c0eb3a6a152a1510e7db04fa0aff7ce4288530db6a80fa7fea582aa7d46d7d56e708d2bb0c5edd3d26648d336c3620ea55e",
          "d33bf6722fc29384fad75f990248b9528e0959aa67ec66869dc3996c67a2d559e7d77ce5955f8cad2a4df5fdc3acccafa7bc0def53d848111256903e5add0420",
          "8bc833de510863b4b432c3cbf45aa7cc");

  // Wycheproof tcId 19: pt=128 bytes, aad=0 bytes, iv=12 bytes
  GCM_KAT("3c55f88e9faa0d68ab50d02b47161276",
          "d767c48d2037b4bd2c231bbd",
          "",
          "5d6add48e7a5704e54f9c2829a9b4283dce0d3a65b133eba3793c4fbfa1d8e3a2539d0d4f3de381598ce5b2360173fbd149476c31692c5d6e872fce40219378949c2e70b5f1b9f0a1d5f38352ad814b2a035bb3f3f26425d831a2f7a5e65c5dfcd91a315c2b24f53a662605ea40857dd980e9be5cdad000c569f2d204d4bd3b0",
          "17d72d90bd23e076d8364a87ecb9ac58acc5de4629bfd590409b8bf1fcd3a2f602731b4614cec15e773ea65a65e7210994256bf5450a25acb527269c065f2e2f2279d1fe8b3eda98dcf87b348f1528377bbdd258355d46e035330483d8097e80c7de9bbb606ddf723f2909217ffdd18e8bdbd7b08062f1dcba960e5c0d290f5f",
          "090b8c2ec98e4116186d0e5fbefeb9c2");

  // Wycheproof tcId 22: pt=256 bytes, aad=0 bytes, iv=12 bytes
  GCM_KAT("e88d95eabe88fcf158fae858af951221",
          "a65834a9d231b34709383e9a",
          "",
          "2decaccc8b424fa4963890ece15b3fc281b6215780ff6baee57edcd25afe260ff80ed4f25cc04d2802a1e90a2e6e96d1ee73a4a53dcf60025d484054d146f275ab34c33b102001a07d804cc94a40fd78c16780d1b648487fac035386e5d25c2b9edbf7a52d102d1943958c009eb6d88e00a3227c4c788e445003fabb4dbefccd3fe1716d916446fee2111615d560ecc59d7bd288268ab321e7002545887183fe023fdec2a6d3b73b94d1548cee19638d31d2c5a32b15d2aae3f42950a787115e200b00022d4929105da0b4d10ccb0b3886b3169b32ac5df7a637c23362e2d4ed9c137f35bbd578c2cda0377e0f1e64f7d31e9ef4d7603ea1363523758385c761",
          "9b3833c356f83d19f59ac4770c9586aad457810f9dc55112cc6b87e94d8dc71184b227a14500c0a8619d544435db4c001467ef2acba95007299d717fadc0c0717c4c8e748d03ffe2cf2fd06f0009b0e6590f956c212a2c926d5679bdbb79d87636ae9faefa5c8330c570e84b94626f87d6a53b121574f74c9e3211d9451811e9940db5e74d128364328fb8f40f850a25c3e7ba4fdeb0ef6a639060a11d1c32ae0531d2518f905952c9814236b00b9393fd31f8c0522f8e3072b864a3a5cebe1ceb15585c9042f3f5b95390c62d8c1b513550defd21b481fcfbd9fdd6c262ff6ed4e0a6051be309788a763e567107f039e988757f96ad95436792a3bd26f38590",
          "4f4c265edd3158c641ce9555b58650db");

  // Wycheproof tcId 25: pt=512 bytes, aad=0 bytes, iv=12 bytes
  GCM_KAT("fc8e6d2c7f42cab59375327285cc3398",
          "49e1e00c48eaf1b5b9d2cb45",
          "",
          "2121b06990dcde2885739032622fd70294174074bffdf40b01f3554d5d87242da61673fe9b1687771ff1cc330d7b8a5138f6598d8160ec90a4816a6dbab310f2c99ab19c49d8a5d04eed4b93cd76159766548e136517ecfb6aa7ad51e5ff6d083c0e53533692388e651ea9cba94693118e4699926476fea785d2cac0213aa68ae0a366923532d333ef133b490a4667606f7294db8c6a4530407409b51e803493d46638fba151b2031f8208d595b4e4ae55db66cd7c328753cfa0f644438b0bff4f87d9b7c5648e5d2e8057e0b20d550cf1d0aa13900647c332909b50f8ecb1ee148342aac705b28215900030bfd90ca1446e3a03ceb2ab71a9ceb3d8f0b4626febf1dcff3c1f5ae0fef4c0f74623ba47eb5fdc42d42a2039f45e5987624d97d0fcfb95f74c478d613b9067f03cb86d6055d5124e6ff3174d136d60fd7a54e7c8fdfff20fb5807c4e356cbfc70df4bf83997855608558dff64b3ea8854481cb24933000489f4b8e9415b22237e916653874549d7687ae71b063ace3ef7e41c705d197c3157dacd3263d61132a4f07b91cb0cd79bc7cfd85f6f8c1f507c33bb910e2e879e0e4d8fedf804134d14d5998b38376d9ac0831d1577510ef3704e3f68acfcb433aa2a751f94fa8b6b312afbeea7f3d1f38784d79db414c7799e011ca4d35779ed17aed7d96df5e1a60ace74692686ede778dfb4beeb42585c8ccdf03cf",
          "51eb448f839802e6d73c5b628eff69b1a449c5b1e709f2fd869c8ebac9725ecc3c9f426f875853cada118f846de1a52f3b36e2446680cdb44241c475b0414590f1ee4bb978db5e88c696d13cadb31ebaa897c24e8204ddaa0e9c6d7865cab9934d6f811288da285eb3a54235e232a6dbb2a7ba36ea72818218a1ed4c96e859d0ead7cc7e3d8993c1005fa55b53d752b4ca2194736d76b9253197281e0c6333048572046b20cce32940eefacdc625adc8419c6a222c61c9a8f248463c37a3c4e688a9d74e9006fd7910769e3b21c7dc0d7ed58f0eeea58e3257c40e17ea42884157e3afc9913757506bd90527dd285bda33ab5a447f90e6f8c9ecff2289fdac6cd28074c3e10bb374337f6c587dacb8cbf7bfab272fcd462c2a06b465a791eab911cab96ae6ccdf382aeb2e9d5ab07e3dc133d7f5b7402bb1b6ccf8ce4815392130073f6c03d3919d8640cd7ba9b7fbbfcb07405093ac408c4acd50d52d7cae06b9f3648b539044e49eb0d526c6323b5932d3cdf118ccb556498f24390d6d2103588c6cc4d118f52e4d66b1bde83a8b7c863e6a373c4cd65d1d1a98535810fbefa8ca38a20830e19ef8fdf8fba1d333655054e6c8a3fdc8403b13b27de07f9dbeef390ee06c058957c1f6e6dae7755090ef1d0afee347671fe69e5a280869040f4f35a6f687c37ee9e6b676a6d58ac198dc86a831ae20fa2e64f416552dfbdc4a",
          "1fba8fdad545d2443d6e79592974f355");

  // Wycheproof tcId 39: pt=16 bytes, aad=0 bytes, iv=12 bytes
  GCM_KAT("00112233445566778899aabbccddeeff",
          "000000000000000000000000",
          "",
          "ebd4a3e10cf6d41c50aeae007563b072",
          "f62d84d649e56bc8cfedc5d74a51e2f7",
          "ffffffffffffffffffffffffffffffff");

  // Wycheproof tcId 40: pt=16 bytes, aad=0 bytes, iv=12 bytes
  GCM_KAT("00112233445566778899aabbccddeeff",
          "ffffffffffffffffffffffff",
          "",
          "d593c4d8224f1b100c35e4f6c4006543",
          "431f31e6840931fd95f94bf88296ff69",
          "00000000000000000000000000000000");

  // Wycheproof tcId 68: pt=16 bytes, aad=8 bytes, iv=8 bytes
  GCM_KAT("aa023d0478dcb2b2312498293d9a9129",
          "0432bc49ac344120",
          "aac39231129872a2",
          "2035af313d1346ab00154fea78322105",
          "64c36bb3b732034e3a7d04efc5197785",
          "b7d0dd70b00d65b97cfd080ff4b819d1");

  // Wycheproof tcId 70: pt=16 bytes, aad=0 bytes, iv=8 bytes
  GCM_KAT("deb62233559b57476602b5adac57c77f",
          "d084547de55bbc15",
          "",
          "d8986df0241ed3297582c0c239c724cb",
          "03e1a168a7e377a913879b296a1b5f9c",
          "3290aa95af505a742f517fabcc9b2094");

  // Wycheproof tcId 75: pt=16 bytes, aad=0 bytes, iv=16 bytes
  GCM_KAT("cfb4c26f126f6a0acb8e4e220f6c56cd",
          "1275115499ae722268515bf0c164b49c",
          "",
          "09dfd7f080275257cf97e76f966b1ad9",
          "a780bd01c80885156c88a973264c8ee5",
          "2adeffa682c8d8a81fada7d9fcdd2ee2");

  // Wycheproof tcId 76: pt=32 bytes, aad=0 bytes, iv=16 bytes
  GCM_KAT("0b11ef3a08c02970f74281c860691c75",
          "95c1dd8c0f1705ece68937901f7add7b",
          "",
          "f693d4edd825dbb0618d91113128880dbebb23e25d00ed1f077d870be9cc7536",
          "7e47e10fe3c6fbfa381770eaf5d48d1482e71e0c44dff1e30ca6f95d92052084",
          "d01444fa5d9c499629d174ff3927a1ac");

  // Wycheproof tcId 89: pt=16 bytes, aad=0 bytes, iv=16 bytes
  GCM_KAT("00112233445566778899aabbccddeeff",
          "00000000000000000000000000000000",
          "",
          "bec6fa05c1718b9b84c47345bbed7dcb",
          "45a3f89d02918bfd0c8161658ccc9795",
          "00000000000000000000000000000000");

  // Wycheproof tcId 90: pt=16 bytes, aad=0 bytes, iv=16 bytes
  GCM_KAT("00112233445566778899aabbccddeeff",
          "ffffffffffffffffffffffffffffffff",
          "",
          "4d82639c39d3f3490ee903dd0be7afcf",
          "1cd5a06214235ceb044d4bad7b047312",
          "ffffffffffffffffffffffffffffffff");

  // Wycheproof tcId 278: pt=16 bytes, aad=0 bytes, iv=1 bytes
  GCM_KAT("fec58aa8cf06bfe05de829f27ec77693",
          "9d",
          "",
          "f2d99a9f893378e0757d27c2e3a3101b",
          "0a24612a9d1cbe967dbfe804bf8440e5",
          "96e6fd2cdc707e3ee0a1c90d34c9c36c");

  // Wycheproof tcId 280: pt=16 bytes, aad=0 bytes, iv=2 bytes
  GCM_KAT("b43967ee933e4632bd6562ba1201bf83",
          "8760",
          "",
          "5a6ad6db70591d1e520b0122f05021a0",
          "ba3e7f8b2999995c7fc4006ca4f475ff",
          "98f47a5279cebbcac214515710f6cd8a");

  // Wycheproof tcId 282: pt=16 bytes, aad=0 bytes, iv=4 bytes
  GCM_KAT("d83c1d7a97c43f182409a4aa5609c1b1",
          "7b5faeb2",
          "",
          "c8f07ba1d65554a9bd40390c30c5529c",
          "1b84baea9df1e65bee7b49e4a8cda1ec",
          "5c0bb79d8240041edce0f94bd4bb384f");

  // Wycheproof tcId 284: pt=16 bytes, aad=0 bytes, iv=6 bytes
  GCM_KAT("eba7699b56cc0aa2f66a2a5be9944413",
          "d1dafc8de3e3",
          "",
          "d021e53d9098a2df3d6b903cdad0cd9c",
          "18291aa8dc7b07448aa8f71bb8e380bf",
          "9c0e22e5c41b1039ff5661ffaefa8e0f");

  // Wycheproof tcId 286: pt=16 bytes, aad=0 bytes, iv=10 bytes
  GCM_KAT("fc93582fa1f8b58cc9e80dd583e9bf8b",
          "5d4bf58798fac351a399",
          "",
          "866d5e1b0aa29004e51ea87de86e3c05",
          "91c20598dcbd90998c9a7d6b1e57321f",
          "b071203f3da17c19ad87a40db08b65f5");
