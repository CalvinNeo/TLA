---- MODULE tcommit ----

(* �����Recource Manager�ļ��� *)
CONSTANT RM

(* rmState��һ�����ϣ�rmState[r]��ʾr���RM��״̬ *)
VARIABLE rmState

TCTypeOK == rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
\* TCTypeOK == \A r \in RM: rmState[r] \in {"working", "prepared", "committed", "aborted"}

TCInit == rmState = [r \in RM |-> "working"]

(* ����������abort״̬ *)
canCommit == \A r \in RM: rmState[r] \in {"working", "prepared"}

(* 
Q: ���ﲻӦ�����Ϊ���������abort״̬ ��
��Ӧ�ö�Ӧ�����Ϊû�����Ѿ�committed
*)
notCommitted == \A r \in RM: rmState[r] /= "committed"


(* ���ﲻ��д��rmState'[r] = "prepared"
*)
PrepareP(r) == /\ rmState[r] = "working"
               /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

PrepareA(r) == /\ rmState[r] = "working"
               /\ notCommitted \* ����Ǳ�Ҫ��
               /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

(* ��Prepare�׶εĺϷ�������
ʵ���϶�Ӧworking->prepared��working->abort
Q: Ϊɶ�ٷ�ʵ������û��дabort״̬�أ�ʵ���Ϲٷ���working->abort�ŵ���DecideA�ϡ�
�ٷ���ʵ���ǣ����r����working״̬����ô�ͽ�������Ϊprepared״̬��
*)
Prepare(r) == PrepareP(r) \/ PrepareA(r)


(* 
�����Լ���prepared״̬��
û����������abort״̬��ʵ���Ͼ���canCommit��
��ʱ�����ǿ��Ըı�״̬Ϊcommitted
*)
DecideC(r) == /\ rmState[r] = "prepared"
              /\ canCommit
              /\ rmState' = [rmState EXCEPT ![r] = "committed"]

DecideA(r) == /\ rmState[r] = "prepared"
              /\ notCommitted
              /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
              
(* ��Decide�׶εĺϷ����� ��
����Ϊʵ���϶�Ӧprepared->committed��prepared->abort��
�ٷ���Ϊworking->abortҲ��
*)
Decide(r) == DecideA(r) \/ DecideC(r)
         
(* 
�����������ѡ��RM�е�һ��rִ��һ����������ͨ��\Eʵ�ֵ�
*)
TCNext == \E r \in RM: Prepare(r) \/ Decide(r)

TCConsistent == \A r1, r2 \in RM: ~ /\ rmState[r1] = "aborted"
                                    /\ rmState[r2] = "committed"

TCSpec == TCInit /\ [][TCNext]_rmState

THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)
====