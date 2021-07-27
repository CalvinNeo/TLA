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

(* Avar/BVar/AtoB/BtoA等VARIABLE，可以取哪些值呢？ *)
TypeOK == /\ AVar \in Data \X {0,1}
          /\ BVar \in Data \X {0,1}
          /\ AtoB \in Seq(Data \X {0,1})
          /\ BtoA \in Seq({0,1})

(* 初始状态，下面的代码是错误的：
1. AVar可以是任何值 
2. 使用Tuple而不是Set
*)

InitFault == /\ AVar = <<"", 0>>
             /\ BVar = <<"", 0>>
             /\ AtoB = {}
             /\ BtoA = {}

(* 这里似乎不需要用啥CHOOSE *)
Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ AtoB = <<>>
        /\ BtoA = <<>>
        
ASnd == /\ AtoB' = AtoB \o <<AVar>>
        /\ UNCHANGED <<AVar, BVar, BtoA>>

(* A收到B的消息，下面的代码是错误的：
1. 需要判断BtoA是否为空
2. 完了需要及时删除当前信息
3. 对于重复的信息，也要删除
*)

\*ARcvFault == /\ Head(BtoA) = AVar[2]
\*             /\ \E d \in Data: AVar' = <<d, 1 - AVar[2]>> \* 这里的描述方式值得参考 
\*             /\ UNCHANGE << BVar, BtoA, AtoB >>

\*ARcv == /\ BtoA /= <<>>
\*        /\ AVar' = LET h == Head(BtoA)
\*                   IN IF h = AVar[2] THEN \* 说明不是重复的 
\*                        \E d \in Data: <<d, 1 - AVar[2]>> \* 这里的描述方式值得参考
\*                      ELSE \* 说明是重复的
\*                        AVar
\*        /\ BtoA' = Tail(BtoA)
\*        /\ UNCHANGED << BVar, AtoB >>

ARcv == /\ BtoA /= <<>>
        /\ IF Head(BtoA) = AVar[2] THEN \* 说明不是重复的 
             \E d \in Data: AVar' = <<d, 1 - AVar[2]>> \* 这里的描述方式值得参考
           ELSE \* 说明是重复的
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

(* 实际上就是从AtoB或者BtoA中移除任意的一个消息  *)
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