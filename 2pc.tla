---- MODULE 2pc ----

CONSTANT RM  \* The set of resource managers
VARIABLES rmState, tmState, tmPrepared, msgs

(* ���п��ܵ���Ϣ���� *)
Messages == [type: {"Prepared"}, rm: RM] \union [type: {"Commit", "Abort"}]

(* rmState���ĸ�������Լ�� *)
\* ע������Ҳ����д�� rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
TPTypeOK == /\ \A r \in RM: rmState[r] \in {"working", "prepared", "committed", "aborted"}
            /\ tmState \in {"init", "done"}
            /\ tmPrepared \subseteq RM
            /\ msgs \subseteq Messages

(* rmState���ĸ������ĳ�ʼֵ *)
TPInit ==  /\ [r \in rmState |-> "working"]
           /\ tmState = "init"
           /\ tmPrepared = {}
           /\ msgs = {}
-----------------------------------------------------------------------------

(* ��TM�յ�����r��Prepared��Ϣʱ��
    ����enabling condition��
   1. rmState���Ƿ�Ҫдһ��rmState[r]��prepared�������أ�
   1. tmState ��Ӧ����done
   1. tmPrepared ��Ϊ���Խ����ظ���Ϣ����������ν
   1. msgs Ӧ�����������Ϣ
    ����״̬ת�ƣ�
   1. ����rmState�������������RM�Լ����µģ�
   1. ����tmPrepared
   1. ����msgs�����Ӧ������Ϣ���ͷ����µ�
   1. ����tmState��done���״̬Ӧ�÷�����TMCommit/TMAbort֮��
 *)
TMRcvPrepared(r) == /\ tmState = "init"
                    /\ [type |-> "Prepared", rm |-> r] \in msg
                    /\ tmPrepared' = tmPrepared \union {r}
                    /\ UNCHANGED << rmState, tmState, msgs >>    
                 \* /\ rmState[r] = "prepared"

(* ��TM׼��Commitʱ��
    ����enabling condition��
   1. rmState���Ƿ�Ӧ�����Ǵ�ʱ������rmState[r]Ϊaborted�������Ӧ�ò���Ҫ����Ϊ���Ƕ���Ϊ�������������Ƕ���Ϊ�ļ��顣
   1. tmState ��Ӧ����done
   1. tmPrepared ��Ϊ���Խ����ظ���Ϣ����������ν
   1. msgs Ӧ�����������Ϣ
    ����״̬ת�ƣ�
   1. ����rmState�������������RM�Լ����µģ�
   1. ����tmPrepared
   1. ����msgs�����Ӧ������Ϣ���ͷ����µ�
   1. ����tmState��done���״̬Ӧ�÷�����TMCommit/TMAbort֮��
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