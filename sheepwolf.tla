---- MODULE sheepwolf ----

EXTENDS Sequences, Integers, TLC, FiniteSets

CONSTANTS Sheep, Wolves, Boat

VARIABLE A, B, M

ASSUME \A s \in Sheep: s \notin Wolves
ASSUME \A s \in Wolves: s \notin Sheep

Valid(X) == Cardinality({v \in X: v \in Sheep}) >= Cardinality({v \in X: v \in Wolves})
Count(X) == Cardinality(X \ {Boat})
CombinationSeq2(X) == {s \in X \X X: s[1] < s[2]}
Combination2(X) == { { s[1], s[2] } : s \in CombinationSeq2(X) }

Load1(X,Y) == /\ Boat \in X
              /\ Cardinality(M) < 2
              /\ \E x \in (X \ {Boat}):
                /\ Valid(X \ {x})
                  /\ X' = X \ {x}
                  /\ M' = M \union {x}
                  /\ UNCHANGED Y

Unload1(X,Y) == /\ Boat \in X
                /\ Cardinality(M) > 0
                /\ \E x \in M:
                    /\ Valid(X \union {x})
                    /\ X' = X \union {x}
                    /\ M' = M \ {x}
                    /\ UNCHANGED Y

Move == \/ Boat \in A
            /\ A' = A \ {Boat}
            /\ B' = B \union {Boat}
            /\ UNCHANGED M
        \/ Boat \in B
            /\ B' = B \ {Boat}
            /\ A' = A \union {Boat}
            /\ UNCHANGED M

Init == /\ A = Sheep \union Wolves \union {Boat}
        /\ B = {}
        /\ M = {}

Next == Load1(A,B) \/ Unload1(A,B) \/ Load1(B,A) \/ Unload1(B,A) \/ Move
vars == <<A, B, M>>

Spec == Init /\ [][Next]_vars

Solved == /\ \A s \in Sheep: s \notin A
          /\ \A s \in Wolves: s \notin A
          /\ \A s \in Sheep: s \in B
          /\ \A s \in Wolves: s \in B
          
NotSolved == \neg Solved

====