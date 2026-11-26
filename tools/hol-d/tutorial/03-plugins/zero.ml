let twice_zero = prove (`twice 0 = 0`, REWRITE_TAC[Base.twice; ADD_CLAUSES]);;
let () = print_thm twice_zero; print_newline ();;
