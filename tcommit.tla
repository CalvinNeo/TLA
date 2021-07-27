---- MODULE tcommit ----

(* 参与的Recource Manager的集合 *)
CONSTANT RM

(* rmState是一个集合，rmState[r]表示r这个RM的状态 *)
VARIABLE rmState

TCTypeOK == rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
\* TCTypeOK == \A r \in RM: rmState[r] \in {"working", "prepared", "committed", "aborted"}

TCInit == rmState = [r \in RM |-> "working"]

(* 不能有人是abort状态 *)
canCommit == \A r \in RM: rmState[r] \in {"working", "prepared"}

(* 
Q: 这里不应该理解为如果有人是abort状态 ，
而应该而应该理解为没有人已经committed
*)
notCommitted == \A r \in RM: rmState[r] /= "committed"


(* 这里不能写成rmState'[r] = "prepared"
*)
PrepareP(r) == /\ rmState[r] = "working"
               /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

PrepareA(r) == /\ rmState[r] = "working"
               /\ notCommitted \* 这个是必要的
               /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

(* 在Prepare阶段的合法动作，
实际上对应working->prepared和working->abort
Q: 为啥官方实现里面没有写abort状态呢？实际上官方将working->abort放到了DecideA上。
官方的实现是，如果r出于working状态，那么就将它设置为prepared状态。
*)
Prepare(r) == PrepareP(r) \/ PrepareA(r)


(* 
必须自己是prepared状态，
没有其他人是abort状态，实际上就是canCommit，
此时，我们可以改变状态为committed
*)
DecideC(r) == /\ rmState[r] = "prepared"
              /\ canCommit
              /\ rmState' = [rmState EXCEPT ![r] = "committed"]

DecideA(r) == /\ rmState[r] = "prepared"
              /\ notCommitted
              /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
              
(* 在Decide阶段的合法动作 ，
我认为实际上对应prepared->committed和prepared->abort，
官方认为working->abort也算
*)
Decide(r) == DecideA(r) \/ DecideC(r)
         
(* 
这里的语义是选择RM中的一个r执行一个操作，是通过\E实现的
*)
TCNext == \E r \in RM: Prepare(r) \/ Decide(r)

TCConsistent == \A r1, r2 \in RM: ~ /\ rmState[r1] = "aborted"
                                    /\ rmState[r2] = "committed"

TCSpec == TCInit /\ [][TCNext]_rmState

THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)
====