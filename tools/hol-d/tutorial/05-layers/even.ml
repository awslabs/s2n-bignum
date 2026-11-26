needs "lib/numbers.ml";;
needs "lib/parity.ml";;
let even_four = prove (`EVEN (twice 2)`, REWRITE_TAC[TWICE_EVEN]);;
let () = print_thm even_four; print_newline ();;
