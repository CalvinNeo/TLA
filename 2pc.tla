---- MODULE 2pc ----

CONSTANT RM  \* The set of resource managers
VARIABLES rmState, tmState, tmPrepared, msgs

(* 所有可能的消息类型 *)
Messages == [type: {"Prepared"}, rm: RM] \union [type: {"Commit", "Abort"}]

(* rmState等四个变量的约束 *)
\* 注意这里也可以写成 rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
TPTypeOK == /\ \A r \in RM: rmState[r] \in {"working", "prepared", "committed", "aborted"}
            /\ tmState \in {"init", "done"}
            /\ tmPrepared \subseteq RM
            /\ msgs \subseteq Messages

(* rmState等四个变量的初始值 *)
\*TPInit == /\ [r \in rmState |-> "working"]
\*          /\ tmState = "init"
\*          /\ tmPrepared = {}
\*          /\ msgs = {}

TPInit == /\ rmState = [r \in RM |-> "working"]
          /\ tmState = "init"
          /\ tmPrepared = {}
          /\ msgs = {}

(* 当TM收到来自r的Prepared消息时：
    考虑enabling condition：
   1. rmState？是否要写一个rmState[r]是prepared的条件呢？
   1. tmState 不应该是done
   1. tmPrepared 因为可以接受重复消息，所以无所谓
   1. msgs 应当包含这个消息
    考虑状态转移：
   1. 更新rmState？还是这个是由RM自己更新的？
   1. 更新tmPrepared
   1. 更新msgs？这个应该是消息发送方更新的
   1. 更新tmState？done这个状态应该发生在TMCommit/TMAbort之后
 *)
TMRcvPrepared(r) == /\ tmState = "init"
                    /\ [type |-> "Prepared", rm |-> r] \in msgs
                    /\ tmPrepared' = tmPrepared \union {r}
                    /\ UNCHANGED << rmState, tmState, msgs >>    
                 \* /\ rmState[r] = "prepared"

(* 当TM准备Commit时：
    考虑enabling condition：
   1. rmState？是否应当考虑此时不能有rmState[r]为aborted的情况？
                应该不需要，因为这是对行为的描述，而不是对行为的检验。况且，TM怎么确切知道每个RM的情况？
   1. tmState 不应该是done
   1. tmPrepared 因为可以接受重复消息，所以无所谓
   1. msgs 所有的RM都已经发送了Prepared消息
    考虑状态转移：
   1. 更新rmState？还是这个是由RM自己更新的？
   1. 更新tmPrepared？因为没有收到RM的准备消息，所以应该不更新。
   1. 更新msgs？这个应该是消息发送方更新的
   1. 更新tmState？done这个状态应该发生在TMCommit/TMAbort之后
 *)
\*TMCommit == /\ tmState /= "done"
\*            /\ \A r \in RM [type |-> "Prepared", rm |-> r] \in msg
\*            /\ tmState' = "done"
\*            /\ UNCHANGED << rmState, tmPrepared, msgs >>
(* 主要做了两点修改
   1. 不通过msgs，而是通过判断tmPrepared是否等于RM，来判断是否收到了所有RM的Prepared
*)
TMCommit == /\ tmState /= "done"
            /\ tmPrepared = RM
            /\ tmState' = "done"
            /\ msgs' = msgs \union {[type |-> "Commit"]}
            /\ UNCHANGED << rmState, tmPrepared >>

TMAbort == /\ tmState /= "done"
           /\ tmState' = "done"
           /\ msgs' = msgs \union {[type |-> "Abort"]}
           /\ UNCHANGED << rmState, tmPrepared >>

(* 当RM准备Prepare时：
    考虑enabling condition：
   1. rmState 自己是working。要不要判断没有人是abort？不应该，因为r怎么知道其他RM的情况？
   1. tmState TM状态，无要求
   1. tmPrepared TM状态，无要求
   1. msgs 无要求
    考虑状态转移：
   1. 更新rmState？需要更新自己的状态
   1. 更新tmPrepared？TM状态，无要求
   1. 更新msgs？需要发送消息
   1. 更新tmState？TM状态，无要求
 *)
RMPrepare(r) == /\ rmState[r] = "working"
                /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
                /\ msgs' = msgs \union {[type |-> "Prepared", rm |-> r]}
                /\ UNCHANGED << tmState, tmPrepared >>
                
(* 当RM准备Abort
Abort不保证会发送消息，这个很显然，谁会在崩溃的时候先说一句我要崩溃了呢？
*)
RMChooseToAbort(r) == /\ rmState[r] = "working"
                      /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
                      /\ UNCHANGED << tmState, tmPrepared, msgs >>
    
(* 当RM收到了TM的Commit消息
注意，这里的大括号不能有{[type |-> "Commit"]}
*)
RMRcvCommitMsg(r) == /\ [type |-> "Commit"] \in msgs
                     /\ rmState' = [rmState EXCEPT ![r] = "committed"]
                     /\ UNCHANGED << tmState, tmPrepared, msgs >>

RMRcvAbortMsg(r) == /\ [type |-> "Abort"] \in msgs
                    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
                    /\ UNCHANGED << tmState, tmPrepared, msgs >>

(* 注意，这里是\E，表示从RM里面随机选择一个 *)
TPNext ==  \/ TMCommit \/ TMAbort
           \/ \E r \in RM : 
               TMRcvPrepared(r) \/ RMPrepare(r) \/ RMChooseToAbort(r)
                 \/ RMRcvCommitMsg(r) \/ RMRcvAbortMsg(r)


TPSpec == TPInit /\ [][TPNext]_<<rmState, tmState, tmPrepared, msgs>>


THEOREM TPSpec => []TPTypeOK


INSTANCE tcommit 

THEOREM TPSpec => TCSpec


====
