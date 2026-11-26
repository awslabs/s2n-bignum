let twice_wrong = prove (`twice 1 = 3`, REWRITE_TAC[Base.twice] THEN ARITH_TAC);;
