PlusCal options (-termination)

----------------------------- MODULE euclidalg -----------------------------

EXTENDS TLC, Integers

CONSTANT N

gcd(x, y) == CHOOSE i \in 1..x:
             /\ x % i = 0
             /\ y % i = 0
             /\ \A j \in 1..x:
                /\ x % j = 0
                /\ y % j = 0
                => i >= j
                
Divides(i,j) == \E k \in 0..j : j = i * k
IsGCD(i,j,k) == Divides(i,j) /\ Divides(i,k) /\ \A r \in 0..j \cup 0..k : Divides(r,j) /\ Divides(r,k) => Divides(r,i)

(*--algorithm eu

variables
    u = 24,
    v \in 1..N,
    ori_v = v;
begin
    while u /= 0 do
        if u < v then u := v || v := u ;
        end if ;
        u := u - v;
    end while ;
print <<"have gcd", u, ori_v, v, gcd(24, ori_v)>> ;
assert v = gcd(24, ori_v)
\* assert IsGCD(v, 24, ori_v)

end algorithm;*)


\* BEGIN TRANSLATION (chksum(pcal) = "54fe4470" /\ chksum(tla) = "6b6909ee")
VARIABLES u, v, ori_v, pc

vars == << u, v, ori_v, pc >>

Init == (* Global variables *)
        /\ u = 24
        /\ v \in 1..N
        /\ ori_v = v
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF u /= 0
               THEN /\ IF u < v
                          THEN /\ /\ u' = v
                                  /\ v' = u
                          ELSE /\ TRUE
                               /\ UNCHANGED << u, v >>
                    /\ pc' = "Lbl_2"
               ELSE /\ PrintT(<<"have gcd", u, ori_v, v, gcd(24, ori_v)>>)
                    /\ Assert(v = gcd(24, ori_v), 
                              "Failure of assertion at line 33, column 1.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << u, v >>
         /\ ori_v' = ori_v

Lbl_2 == /\ pc = "Lbl_2"
         /\ u' = u - v
         /\ pc' = "Lbl_1"
         /\ UNCHANGED << v, ori_v >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sun Dec 18 17:28:37 CST 2022 by Calvin
\* Created Sun Dec 18 16:50:52 CST 2022 by Calvin
