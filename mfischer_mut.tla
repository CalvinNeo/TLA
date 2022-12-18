---------------------------- MODULE mfischer_mut ----------------------------
EXTENDS TLC, Integers

CONSTANT N

(*--algorithm mut
variables lock = 0;
process Proc \in 1..N

begin
    ncs: while TRUE do
            skip;
            l1: while lock /= self do
                    l2: await lock = 0;
                    l3: lock := self;
                end while;
            
     cs:    skip;
         end while;
end process

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "48f1372c" /\ chksum(tla) = "351267be")
VARIABLES lock, pc

vars == << lock, pc >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ lock = 0
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "l1"]
             /\ lock' = lock

l1(self) == /\ pc[self] = "l1"
            /\ IF lock /= self
                  THEN /\ pc' = [pc EXCEPT ![self] = "l2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ lock' = lock

l2(self) == /\ pc[self] = "l2"
            /\ lock = 0
            /\ pc' = [pc EXCEPT ![self] = "l3"]
            /\ lock' = lock

l3(self) == /\ pc[self] = "l3"
            /\ lock' = self
            /\ pc' = [pc EXCEPT ![self] = "l1"]

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "ncs"]
            /\ lock' = lock

Proc(self) == ncs(self) \/ l1(self) \/ l2(self) \/ l3(self) \/ cs(self)

Next == (\E self \in 1..N: Proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

Mutex == \A i,k \in 1..N : (i # k) => \neg ((pc[i] = "cs") /\ (pc[k] = "cs"))
=============================================================================
\* Modification History
\* Last modified Mon Dec 19 01:27:28 CST 2022 by Calvin
\* Created Mon Dec 19 01:08:59 CST 2022 by Calvin
