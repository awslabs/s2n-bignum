let twice_one = prove (`twice 1 = 2`, REWRITE_TAC[Base.twice] THEN ARITH_TAC);;
let () = print_thm twice_one; print_newline ();;
