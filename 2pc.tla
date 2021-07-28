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
\*TPInit == /\ [r \in rmState |-> "working"]
\*          /\ tmState = "init"
\*          /\ tmPrepared = {}
\*          /\ msgs = {}

TPInit == /\ rmState = [r \in RM |-> "working"]
          /\ tmState = "init"
          /\ tmPrepared = {}
          /\ msgs = {}

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
                    /\ [type |-> "Prepared", rm |-> r] \in msgs
                    /\ tmPrepared' = tmPrepared \union {r}
                    /\ UNCHANGED << rmState, tmState, msgs >>    
                 \* /\ rmState[r] = "prepared"

(* ��TM׼��Commitʱ��
    ����enabling condition��
   1. rmState���Ƿ�Ӧ�����Ǵ�ʱ������rmState[r]Ϊaborted�������
                Ӧ�ò���Ҫ����Ϊ���Ƕ���Ϊ�������������Ƕ���Ϊ�ļ��顣���ң�TM��ôȷ��֪��ÿ��RM�������
   1. tmState ��Ӧ����done
   1. tmPrepared ��Ϊ���Խ����ظ���Ϣ����������ν
   1. msgs ���е�RM���Ѿ�������Prepared��Ϣ
    ����״̬ת�ƣ�
   1. ����rmState�������������RM�Լ����µģ�
   1. ����tmPrepared����Ϊû���յ�RM��׼����Ϣ������Ӧ�ò����¡�
   1. ����msgs�����Ӧ������Ϣ���ͷ����µ�
   1. ����tmState��done���״̬Ӧ�÷�����TMCommit/TMAbort֮��
 *)
\*TMCommit == /\ tmState /= "done"
\*            /\ \A r \in RM [type |-> "Prepared", rm |-> r] \in msg
\*            /\ tmState' = "done"
\*            /\ UNCHANGED << rmState, tmPrepared, msgs >>
(* ��Ҫ���������޸�
   1. ��ͨ��msgs������ͨ���ж�tmPrepared�Ƿ����RM�����ж��Ƿ��յ�������RM��Prepared
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

(* ��RM׼��Prepareʱ��
    ����enabling condition��
   1. rmState �Լ���working��Ҫ��Ҫ�ж�û������abort����Ӧ�ã���Ϊr��ô֪������RM�������
   1. tmState TM״̬����Ҫ��
   1. tmPrepared TM״̬����Ҫ��
   1. msgs ��Ҫ��
    ����״̬ת�ƣ�
   1. ����rmState����Ҫ�����Լ���״̬
   1. ����tmPrepared��TM״̬����Ҫ��
   1. ����msgs����Ҫ������Ϣ
   1. ����tmState��TM״̬����Ҫ��
 *)
RMPrepare(r) == /\ rmState[r] = "working"
                /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
                /\ msgs' = msgs \union {[type |-> "Prepared", rm |-> r]}
                /\ UNCHANGED << tmState, tmPrepared >>
                
(* ��RM׼��Abort
Abort����֤�ᷢ����Ϣ���������Ȼ��˭���ڱ�����ʱ����˵һ����Ҫ�������أ�
*)
RMChooseToAbort(r) == /\ rmState[r] = "working"
                      /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
                      /\ UNCHANGED << tmState, tmPrepared, msgs >>
    
(* ��RM�յ���TM��Commit��Ϣ
ע�⣬����Ĵ����Ų�����{[type |-> "Commit"]}
*)
RMRcvCommitMsg(r) == /\ [type |-> "Commit"] \in msgs
                     /\ rmState' = [rmState EXCEPT ![r] = "committed"]
                     /\ UNCHANGED << tmState, tmPrepared, msgs >>

RMRcvAbortMsg(r) == /\ [type |-> "Abort"] \in msgs
                    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
                    /\ UNCHANGED << tmState, tmPrepared, msgs >>

(* ע�⣬������\E����ʾ��RM�������ѡ��һ�� *)
TPNext ==  \/ TMCommit \/ TMAbort
           \/ \E r \in RM : 
               TMRcvPrepared(r) \/ RMPrepare(r) \/ RMChooseToAbort(r)
                 \/ RMRcvCommitMsg(r) \/ RMRcvAbortMsg(r)


TPSpec == TPInit /\ [][TPNext]_<<rmState, tmState, tmPrepared, msgs>>


THEOREM TPSpec => []TPTypeOK


INSTANCE tcommit 

THEOREM TPSpec => TCSpec


====
