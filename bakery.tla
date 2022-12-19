------------------------------- MODULE bakery -------------------------------

EXTENDS TLC, Naturals, FiniteSets, Sequences

CONSTANT N

gcd(x, y) == CHOOSE i \in 1..x:
             /\ x % i = 0
             /\ y % i = 0
             /\ \A j \in 1..x:
                /\ x % j = 0
                /\ y % j = 0
                => i >= j
                

\* ticket should be set, not tuple
nextTicket(ticket, Max) == CHOOSE t \in 1..Max+1:
                                /\ \A i \in ticket: t > i
                                /\ \A x \in 1..Max+1:
                                    /\ \A j \in ticket: x > j
                                    => t <= x

nextTicketT(ticket, Max) == CHOOSE t \in 1..Max+1:
                                /\ \A i \in 1..Len(ticket): t > ticket[i]
                                /\ \A x \in 1..Max+1:
                                    /\ \A j \in 1..Len(ticket): x > ticket[j]     
                                    => t <= x

prec(ticket, i, j) == \/ i = j
                      \/ ticket[i] > ticket[j]
                      \/ /\ ticket[i] = ticket[j]
                         /\ i > j

max(a, b) == IF a > b THEN a ELSE b

(*--algorithm bakery

variables
    ticket = [i \in 1..N |-> 0],
    choosing = [i \in 1..N |-> FALSE],
    maxTicket = N,

fair process Proc \in 1..N
    variable j;
    begin
ncs:while TRUE do
l1:     choosing[self] := TRUE;
l2:     ticket[self] := nextTicketT(ticket, maxTicket); maxTicket := max(maxTicket, ticket[self]);
l3:     choosing[self] := FALSE;
l4:     j := 1;
l5:     while j <= N do
l6:         while choosing[j] do
l7:             skip;
            end while;
            
l8:         while TRUE do
l9:             await ticket[j] /= 0 /\ prec(ticket, self, j);
                      goto l10;
            end while;
l10:        j := j + 1;
        end while;
cs:     skip;
cl:     ticket[self] := 0;
     end while;
end process

end algorithm*)
\* BEGIN TRANSLATION (chksum(pcal) = "4bbc17a8" /\ chksum(tla) = "8120766b")
CONSTANT defaultInitValue
VARIABLES ticket, choosing, maxTicket, pc, j

vars == << ticket, choosing, maxTicket, pc, j >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ ticket = [i \in 1..N |-> 0]
        /\ choosing = [i \in 1..N |-> FALSE]
        /\ maxTicket = N
        (* Process Proc *)
        /\ j = [self \in 1..N |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "l1"]
             /\ UNCHANGED << ticket, choosing, maxTicket, j >>

l1(self) == /\ pc[self] = "l1"
            /\ choosing' = [choosing EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << ticket, maxTicket, j >>

l2(self) == /\ pc[self] = "l2"
            /\ ticket' = [ticket EXCEPT ![self] = nextTicketT(ticket, maxTicket)]
            /\ maxTicket' = max(maxTicket, ticket'[self])
            /\ pc' = [pc EXCEPT ![self] = "l3"]
            /\ UNCHANGED << choosing, j >>

l3(self) == /\ pc[self] = "l3"
            /\ choosing' = [choosing EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "l4"]
            /\ UNCHANGED << ticket, maxTicket, j >>

l4(self) == /\ pc[self] = "l4"
            /\ j' = [j EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "l5"]
            /\ UNCHANGED << ticket, choosing, maxTicket >>

l5(self) == /\ pc[self] = "l5"
            /\ IF j[self] <= N
                  THEN /\ pc' = [pc EXCEPT ![self] = "l6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << ticket, choosing, maxTicket, j >>

l6(self) == /\ pc[self] = "l6"
            /\ IF choosing[j[self]]
                  THEN /\ pc' = [pc EXCEPT ![self] = "l7"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l8"]
            /\ UNCHANGED << ticket, choosing, maxTicket, j >>

l7(self) == /\ pc[self] = "l7"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "l6"]
            /\ UNCHANGED << ticket, choosing, maxTicket, j >>

l8(self) == /\ pc[self] = "l8"
            /\ pc' = [pc EXCEPT ![self] = "l9"]
            /\ UNCHANGED << ticket, choosing, maxTicket, j >>

l9(self) == /\ pc[self] = "l9"
            /\ ticket[j[self]] /= 0 /\ prec(ticket, self, j[self])
            /\ pc' = [pc EXCEPT ![self] = "l10"]
            /\ UNCHANGED << ticket, choosing, maxTicket, j >>

l10(self) == /\ pc[self] = "l10"
             /\ j' = [j EXCEPT ![self] = j[self] + 1]
             /\ pc' = [pc EXCEPT ![self] = "l5"]
             /\ UNCHANGED << ticket, choosing, maxTicket >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "cl"]
            /\ UNCHANGED << ticket, choosing, maxTicket, j >>

cl(self) == /\ pc[self] = "cl"
            /\ ticket' = [ticket EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "ncs"]
            /\ UNCHANGED << choosing, maxTicket, j >>

Proc(self) == ncs(self) \/ l1(self) \/ l2(self) \/ l3(self) \/ l4(self)
                 \/ l5(self) \/ l6(self) \/ l7(self) \/ l8(self)
                 \/ l9(self) \/ l10(self) \/ cs(self) \/ cl(self)

Next == (\E self \in 1..N: Proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..N : WF_vars(Proc(self))

\* END TRANSLATION 

Mutex == \A i,k \in 1..N : (i # k) => \neg ((pc[i] = "cs") /\ (pc[k] = "cs"))
Liveness == \E i \in 1..N : pc[i] \notin {"ncs", "cs", "cl"} ~> \E k \in 1..N : pc[k] = "cs"
=============================================================================
\* Modification History
\* Last modified Tue Dec 20 00:25:11 CST 2022 by Calvin
\* Created Mon Dec 19 22:50:56 CST 2022 by Calvin
