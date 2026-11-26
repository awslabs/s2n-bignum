needs "lib/numbers.ml";;
needs "lib/parity.ml";;
let not_odd = prove (`~ODD (twice 3)`, REWRITE_TAC[GSYM NOT_EVEN; TWICE_EVEN]);;
let () = print_thm not_odd; print_newline ();;
