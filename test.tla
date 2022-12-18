---- MODULE test ---- 

EXTENDS Integers, Sequences,  Naturals, FiniteSets


CONSTANT Data


\*Rem(i, seq) == [j \in 1..Len(seq)-1 |-> IF j<i THEN seq[j] ELSE seq[j+1]]
\*RemSet(i, seq) == {(IF j<i THEN seq[j] ELSE seq[j+1]) : j \in 1..Len(seq)-1}
\*F(S) == [x \in S |-> x+1]
\*
\*Q == [i \in 1..3 |-> Data]

CONSTANTS People, Animals
\*Pref == [People -> People]
\*Pref == [[person: People, animal: Animals] -> {"like", "hate"}]


Message ==
        [type: {"pre-accept"}, src: People, dst: People]

\*Pref == [message: {"Hello"}, src:People, dst:People]
                           
S(n) == {[0..m -> 0..m] : m \in 0..n}

\*Pref == {[0..1 -> 0..1]}

Pref == {[0..m -> 0..m] : m \in 0..1}
                                  
====