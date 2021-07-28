---- MODULE test ---- 

EXTENDS Integers, Sequences

CONSTANT Data

Rem(i, seq) == [j \in 1..Len(seq)-1 |-> IF j<i THEN seq[j] ELSE seq[j+1]]
RemSet(i, seq) == {(IF j<i THEN seq[j] ELSE seq[j+1]) : j \in 1..Len(seq)-1}
F(S) == [x \in S |-> x+1]
====