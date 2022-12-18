--------------------------------- MODULE msqueue ---------------------------------
\* https://www.hillelwayne.com/post/tla-messages/
EXTENDS Sequences, Integers, TLC, FiniteSets
CONSTANTS Writer, Readers, Data, NULL, MaxQueue

ASSUME Writer \notin Readers
ASSUME NULL \notin Data

SeqOf(set, n) == UNION {[1..m -> set] : m \in 0..n}
seq (+) elem == Append(seq, elem)

(*--algorithm polling
variables 
  queue = <<>>; \* Ordered messages

define
  TypeInvariant ==
    queue \in SeqOf(Data, MaxQueue)
end define;

process writer = Writer
variable d \in Data
begin
  Write:
    while TRUE do
      queue := queue (+) d;
    end while;
end process;

process reader \in Readers
variables local = NULL;
begin
  Read:
    while TRUE do
      await queue /= <<>>;
      local := Head(queue);
      queue := Tail(queue);
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "54873108" /\ chksum(tla) = "a4252e6")
VARIABLE queue

(* define statement *)
TypeInvariant ==
  queue \in SeqOf(Data, MaxQueue)

VARIABLES d, local

vars == << queue, d, local >>

ProcSet == {Writer} \cup (Readers)

Init == (* Global variables *)
        /\ queue = <<>>
        (* Process writer *)
        /\ d \in Data
        (* Process reader *)
        /\ local = [self \in Readers |-> NULL]

writer == /\ queue' = queue (+) d
          /\ UNCHANGED << d, local >>

reader(self) == /\ queue /= <<>>
                /\ local' = [local EXCEPT ![self] = Head(queue)]
                /\ queue' = Tail(queue)
                /\ d' = d

Next == writer
           \/ (\E self \in Readers: reader(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

====
