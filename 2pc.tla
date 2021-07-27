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
TPInit ==  /\ [r \in rmState |-> "working"]
           /\ tmState = "init"
           /\ tmPrepared = {}
           /\ msgs = {}
-----------------------------------------------------------------------------

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
                    /\ [type |-> "Prepared", rm |-> r] \in msg
                    /\ tmPrepared' = tmPrepared \union {r}
                    /\ UNCHANGED << rmState, tmState, msgs >>    
                 \* /\ rmState[r] = "prepared"

(* 当TM准备Commit时：
    考虑enabling condition：
   1. rmState？是否应当考虑此时不能有rmState[r]为aborted的情况？应该不需要，因为这是对行为的描述，而不是对行为的检验。
   1. tmState 不应该是done
   1. tmPrepared 因为可以接受重复消息，所以无所谓
   1. msgs 应当包含这个消息
    考虑状态转移：
   1. 更新rmState？还是这个是由RM自己更新的？
   1. 更新tmPrepared
   1. 更新msgs？这个应该是消息发送方更新的
   1. 更新tmState？done这个状态应该发生在TMCommit/TMAbort之后
 *)
TMCommit == 

TMAbort == 

RMPrepare(r) ==  
  
RMChooseToAbort(r) == 

RMRcvCommitMsg(r) == 

RMRcvAbortMsg(r) == 

TPNext == 
-----------------------------------------------------------------------------


TPSpec == TPInit /\ [][TPNext]_<<rmState, tmState, tmPrepared, msgs>>


THEOREM TPSpec => []TPTypeOK

-----------------------------------------------------------------------------

INSTANCE TCommit 

THEOREM TPSpec => TCSpec


====