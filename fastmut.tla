------------------------------ MODULE fastmut ------------------------------

EXTENDS TLC, Integers

CONSTANT N

(*--algorithm fastmut
variables fastLock = 0, slowLock = 0, want = [i \in 1..N |-> FALSE];

process Proc \in 1..N

variable j;
begin
    ncs: while TRUE do
            skip ;
    start:  want[self] := TRUE ;
    l1:     fastLock := self ;
    l2:     if slowLock /= 0 then l3: want[self] := FALSE ;
                                  l4: await slowLock = 0 ;
                                  goto start
            end if ;
    l5:     slowLock := self ;
    l6:     if fastLock /= self
            then l7: want[self] := FALSE ;
                     j := 1 ;
                 l8: while j <= N do await ~want[j] ;
                                     j := j + 1
                     end while;
                 l9: if slowLock /= self then l10: await slowLock = 0 ;
                                                   goto start ;
                     end if ;
            end if ;
    cs:     skip ;
    l11:    slowLock := 0 ;
    l12:    want[self] := FALSE ;
    end while ;

end process
end algorithm*)

\* BEGIN TRANSLATION (chksum(pcal) = "a0007a07" /\ chksum(tla) = "59f26c86")
CONSTANT defaultInitValue
VARIABLES fastLock, slowLock, want, pc, j

vars == << fastLock, slowLock, want, pc, j >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ fastLock = 0
        /\ slowLock = 0
        /\ want = [i \in 1..N |-> FALSE]
        (* Process Proc *)
        /\ j = [self \in 1..N |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << fastLock, slowLock, want, j >>

start(self) == /\ pc[self] = "start"
               /\ want' = [want EXCEPT ![self] = TRUE]
               /\ pc' = [pc EXCEPT ![self] = "l1"]
               /\ UNCHANGED << fastLock, slowLock, j >>

l1(self) == /\ pc[self] = "l1"
            /\ fastLock' = self
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << slowLock, want, j >>

l2(self) == /\ pc[self] = "l2"
            /\ IF slowLock /= 0
                  THEN /\ pc' = [pc EXCEPT ![self] = "l3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l5"]
            /\ UNCHANGED << fastLock, slowLock, want, j >>

l3(self) == /\ pc[self] = "l3"
            /\ want' = [want EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "l4"]
            /\ UNCHANGED << fastLock, slowLock, j >>

l4(self) == /\ pc[self] = "l4"
            /\ slowLock = 0
            /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << fastLock, slowLock, want, j >>

l5(self) == /\ pc[self] = "l5"
            /\ slowLock' = self
            /\ pc' = [pc EXCEPT ![self] = "l6"]
            /\ UNCHANGED << fastLock, want, j >>

l6(self) == /\ pc[self] = "l6"
            /\ IF fastLock /= self
                  THEN /\ pc' = [pc EXCEPT ![self] = "l7"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << fastLock, slowLock, want, j >>

l7(self) == /\ pc[self] = "l7"
            /\ want' = [want EXCEPT ![self] = FALSE]
            /\ j' = [j EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "l8"]
            /\ UNCHANGED << fastLock, slowLock >>

l8(self) == /\ pc[self] = "l8"
            /\ IF j[self] <= N
                  THEN /\ ~want[j[self]]
                       /\ j' = [j EXCEPT ![self] = j[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "l8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l9"]
                       /\ j' = j
            /\ UNCHANGED << fastLock, slowLock, want >>

l9(self) == /\ pc[self] = "l9"
            /\ IF slowLock /= self
                  THEN /\ pc' = [pc EXCEPT ![self] = "l10"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << fastLock, slowLock, want, j >>

l10(self) == /\ pc[self] = "l10"
             /\ slowLock = 0
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << fastLock, slowLock, want, j >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "l11"]
            /\ UNCHANGED << fastLock, slowLock, want, j >>

l11(self) == /\ pc[self] = "l11"
             /\ slowLock' = 0
             /\ pc' = [pc EXCEPT ![self] = "l12"]
             /\ UNCHANGED << fastLock, want, j >>

l12(self) == /\ pc[self] = "l12"
             /\ want' = [want EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "ncs"]
             /\ UNCHANGED << fastLock, slowLock, j >>

Proc(self) == ncs(self) \/ start(self) \/ l1(self) \/ l2(self) \/ l3(self)
                 \/ l4(self) \/ l5(self) \/ l6(self) \/ l7(self)
                 \/ l8(self) \/ l9(self) \/ l10(self) \/ cs(self)
                 \/ l11(self) \/ l12(self)

Next == (\E self \in 1..N: Proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

Mutex == \A i,k \in 1..N : (i # k) => \neg ((pc[i] = "cs") /\ (pc[k] = "cs"))
Liveness == \E i \in 1..N : pc[i] \notin {"ncs", "cs", "l11", "l12"} ~> \E k \in 1..N : pc[k] = "cs"

=============================================================================
\* Modification History
\* Last modified Mon Dec 19 01:08:17 CST 2022 by Calvin
\* Created Sun Dec 18 17:29:13 CST 2022 by Calvin
