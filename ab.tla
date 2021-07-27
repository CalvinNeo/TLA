---- MODULE ab ----

EXTENDS Integers, Sequences

CONSTANT Data

Remove(i, seq) == 
  [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] 
                                      ELSE seq[j+1]]

VARIABLES AVar, BVar,   \* The same as in module ABSpec
          AtoB,  \* The sequence of data messages in transit from sender to receiver.
          BtoA   \* The sequence of ack messages in transit from receiver to sender.
                 \* Messages are sent by appending them to the end of the sequence.
                 \* and received by removing them from the head of the sequence.

vars == << AVar, BVar, AtoB, BtoA >>

(* Avar/BVar/AtoB/BtoA��VARIABLE������ȡ��Щֵ�أ� *)
TypeOK == /\ AVar \in Data \X {0,1}
          /\ BVar \in Data \X {0,1}
          /\ AtoB \in Seq(Data \X {0,1})
          /\ BtoA \in Seq({0,1})

(* ��ʼ״̬������Ĵ����Ǵ���ģ�
1. AVar�������κ�ֵ 
2. ʹ��Tuple������Set
*)

InitFault == /\ AVar = <<"", 0>>
             /\ BVar = <<"", 0>>
             /\ AtoB = {}
             /\ BtoA = {}

(* �����ƺ�����Ҫ��ɶCHOOSE *)
Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ AtoB = <<>>
        /\ BtoA = <<>>
        
ASnd == /\ AtoB' = AtoB \o <<AVar>>
        /\ UNCHANGED <<AVar, BVar, BtoA>>

(* A�յ�B����Ϣ������Ĵ����Ǵ���ģ�
1. ��Ҫ�ж�BtoA�Ƿ�Ϊ��
2. ������Ҫ��ʱɾ����ǰ��Ϣ
3. �����ظ�����Ϣ��ҲҪɾ��
*)

\*ARcvFault == /\ Head(BtoA) = AVar[2]
\*             /\ \E d \in Data: AVar' = <<d, 1 - AVar[2]>> \* �����������ʽֵ�òο� 
\*             /\ UNCHANGE << BVar, BtoA, AtoB >>

\*ARcv == /\ BtoA /= <<>>
\*        /\ AVar' = LET h == Head(BtoA)
\*                   IN IF h = AVar[2] THEN \* ˵�������ظ��� 
\*                        \E d \in Data: <<d, 1 - AVar[2]>> \* �����������ʽֵ�òο�
\*                      ELSE \* ˵�����ظ���
\*                        AVar
\*        /\ BtoA' = Tail(BtoA)
\*        /\ UNCHANGED << BVar, AtoB >>

ARcv == /\ BtoA /= <<>>
        /\ IF Head(BtoA) = AVar[2] THEN \* ˵�������ظ��� 
             \E d \in Data: AVar' = <<d, 1 - AVar[2]>> \* �����������ʽֵ�òο�
           ELSE \* ˵�����ظ���
             AVar' = AVar
        /\ BtoA' = Tail(BtoA)
        /\ UNCHANGED << BVar, AtoB >>
        
BSnd == /\ BtoA' = BtoA \o <<BVar[2]>> 
        /\ UNCHANGED << AVar, BVar, AtoB >>
      
\*BRcv == /\ AtoB /= <<>>
\*        /\ BVar' = LET h == Head(AtoB)
\*                   IN IF h[2] = BVar[2] THEN
\*                     BVar
\*                   ELSE
\*                     h
\*        /\ AtoB' = Tail(AtoB)
\*        /\ UNCHANGED <<AVar, BtoA>>

BRcv == /\ AtoB /= <<>>
        /\ IF Head(AtoB)[2] = BVar[2] THEN
             BVar' = BVar
           ELSE
             BVar' = Head(AtoB)
        /\ AtoB' = Tail(AtoB)
        /\ UNCHANGED <<AVar, BtoA>>

(* ʵ���Ͼ��Ǵ�AtoB����BtoA���Ƴ������һ����Ϣ  *)
LoseAtoB == /\ \E i \in 1..Len(AtoB): AtoB' = Remove(i, AtoB)
           /\ UNCHANGED BtoA
           
LoseBtoA == /\ \E i \in 1..Len(BtoA): BtoA' = Remove(i, BtoA)
           /\ UNCHANGED AtoB 
           
LoseMsg == /\ \/ LoseAtoB
              \/ LoseBtoA
           /\ UNCHANGED <<AVar, BVar>>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Spec == Init /\ [][Next]_vars
-----------------------------------------------------------------------------
ABS == INSTANCE ABSpec

THEOREM Spec => ABS!Spec
-----------------------------------------------------------------------------

FairSpec == Spec  /\  SF_vars(ARcv) /\ SF_vars(BRcv) /\
                      WF_vars(ASnd) /\ WF_vars(BSnd)


====