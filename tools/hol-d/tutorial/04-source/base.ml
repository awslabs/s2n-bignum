let twice = new_definition `twice (n:num) = n + n`;;
let twice_two = prove (`twice 2 = 4`, REWRITE_TAC[twice] THEN ARITH_TAC);;
