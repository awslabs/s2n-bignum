let TWICE_EVEN = prove (`!n. EVEN (twice n)`,
  REWRITE_TAC[twice; GSYM MULT_2; EVEN_MULT; ARITH_EVEN]);;
