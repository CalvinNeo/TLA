------------------------------- MODULE per_on_raft ------------------------------

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS NotFound
CONSTANTS KEYS

\* What's in leader
VARIABLES leader
\* What's in follower
VARIABLES follower
\* The raft log, in global view
VARIABLES log
\* The last index of log
\* For convenience, assume leader's applied_index always equals to last_index
VARIABLES last_index
\* Follower's applied_index
VARIABLES follower_index
\* All transactions, by their locks
\* Foe example, `{{1, 2}}` means a transaction involves key 1 and key 2
VARIABLES trans
VARIABLES done

VARIABLES DEBUG_LEADER_getAllLocksTo
VARIABLES DEBUG_LEADER_getAllUncommittedWrites
VARIABLES DEBUG_LEADER_getAllWritesTo
VARIABLES DEBUG_getAllLocksTo
VARIABLES DEBUG_getAllUncommittedWrites
VARIABLES DEBUG_getAllWritesTo

ASSUME \A key \in KEYS: key < 10000

debug_follower == << DEBUG_getAllUncommittedWrites, DEBUG_getAllWritesTo, DEBUG_getAllLocksTo>>
debug_leader == << DEBUG_LEADER_getAllUncommittedWrites, DEBUG_LEADER_getAllWritesTo, DEBUG_LEADER_getAllLocksTo>>
vars == <<leader, follower, log, last_index, follower_index, trans>> \o debug_follower \o debug_leader

isLock(x) == IF x < 10000 THEN TRUE ELSE FALSE
isWrite(x) == IF x >= 10000 THEN TRUE ELSE FALSE
getLock(write_key) == write_key - 10000
getWrite(key) == key + 10000
getStorageByLock(x) == x + 20000
getStorageByWrite(x) == x + 10000

ToSet(seq) == {seq[i]: i \in DOMAIN seq}
getAllLocksTo(index) == KEYS \intersect ToSet(SubSeq(log, 1, index))
WRITE_KEYS == { getWrite(key) : key \in KEYS }
getAllWritesTo(index) == WRITE_KEYS \intersect ToSet(SubSeq(log, 1, index))
getAllUncommittedWrites(index) == WRITE_KEYS \ getAllWritesTo(index)
getAllUncommittedLocks(index) == { getLock(key) : key \in getAllUncommittedWrites(index) }

applyLock(node, key) ==
    /\ isLock(key)
    /\ follower' = follower \union {key}

findTrans(key) == CHOOSE t \in trans: key \in t

applyWrite(node, write_key) ==
    /\ isWrite(write_key)
    /\ follower' = follower \union {write_key, getStorageByWrite(write_key)}


getEffectOfAllTransKeys1(node, write_key) == {key2 \in findTrans(getLock(write_key)): getWrite(key2) # write_key}

getEffectOfAllTransKeys(node, write_key) == {getStorageByLock(k) : k \in getEffectOfAllTransKeys1(node, write_key)}

applyWriteEnhanced(node, write_key) ==
    /\ isWrite(write_key)
    /\ follower' = follower \union {write_key, getStorageByWrite(write_key)} \union getEffectOfAllTransKeys(node, write_key)

doneChecker ==
    /\ done = FALSE
    /\ KEYS \subseteq leader
    /\ WRITE_KEYS \subseteq leader
    /\ KEYS \subseteq follower
    /\ WRITE_KEYS \subseteq follower
    /\ done' = TRUE
    /\ UNCHANGED <<leader, follower, log, last_index, follower_index, trans>>
    /\ UNCHANGED debug_follower
    /\ UNCHANGED debug_leader
    
genTrans1 == 
    /\ \E key, key2 \in KEYS: 
        /\ key \notin leader
        /\ getWrite(key) \notin leader
        /\ key2 \notin leader
        /\ getWrite(key2) \notin leader
        /\ log' = log \o <<key, key2>>
        /\ last_index' = last_index + 2
        /\ leader' = leader \union {key, key2}
        /\ trans' = trans \union { {key, key2} }
        /\ DEBUG_LEADER_getAllUncommittedWrites' = getAllUncommittedWrites(last_index)
        /\ DEBUG_LEADER_getAllWritesTo' = getAllWritesTo(last_index)
        /\ DEBUG_LEADER_getAllLocksTo' = getAllLocksTo(last_index)
        /\ UNCHANGED << follower, follower_index >>
        /\ UNCHANGED debug_follower
        /\ UNCHANGED done

genTrans2 == 
    /\ \E key \in KEYS: key \in leader /\ getWrite(key) \notin leader
        /\ log' = log \o <<getWrite(key)>>
        /\ last_index' = last_index + 1
        /\ leader' = leader \union {getWrite(key)}
        /\ DEBUG_LEADER_getAllUncommittedWrites' = getAllUncommittedWrites(last_index)
        /\ DEBUG_LEADER_getAllWritesTo' = getAllWritesTo(last_index)
        /\ DEBUG_LEADER_getAllLocksTo' = getAllLocksTo(last_index)
        /\ UNCHANGED << follower, follower_index, trans >>
        /\ UNCHANGED debug_follower
        /\ UNCHANGED done

applyLog(node) == 
    /\ follower_index < last_index
    /\ \/ applyLock(node, log[follower_index+1])
\*       \/ applyWrite(node, log[follower_index+1])
       \/ applyWriteEnhanced(node, log[follower_index+1])
    /\ follower_index' = follower_index + 1
    /\ DEBUG_getAllUncommittedWrites' = getAllUncommittedWrites(follower_index)
    /\ DEBUG_getAllWritesTo' = getAllWritesTo(follower_index)
    /\ DEBUG_getAllLocksTo' = getAllLocksTo(follower_index)
    /\ UNCHANGED << leader, log, last_index, trans >>
    /\ UNCHANGED debug_leader
    /\ UNCHANGED done

followerRead(node, key) ==
    IF getWrite(key) \in node THEN getStorageByLock(key)
    ELSE
        IF key \in node THEN key
        ELSE NotFound

Lin1 == 
    /\ \A write_key \in getAllWritesTo(follower_index):
        /\ followerRead(follower, getLock(write_key)) = getStorageByWrite(write_key)

Lin2 == 
    /\ \A key \in getAllUncommittedLocks(follower_index):
        \/ followerRead(follower, key) = NotFound
        \/ followerRead(follower, key) = key

Init == 
    /\ leader = {}
    /\ follower = {}
    /\ log = << >>
    /\ last_index = 0
    /\ follower_index = 0
    /\ trans = {}
    /\ DEBUG_getAllUncommittedWrites = {}
    /\ DEBUG_getAllWritesTo = {}
    /\ DEBUG_getAllLocksTo = {}
    /\ DEBUG_LEADER_getAllUncommittedWrites = {}
    /\ DEBUG_LEADER_getAllWritesTo = {}
    /\ DEBUG_LEADER_getAllLocksTo = {}
    /\ done = FALSE


Terminating == /\ done = TRUE
               /\ UNCHANGED <<leader, follower, log, last_index, follower_index, trans>>
               /\ UNCHANGED debug_follower
               /\ UNCHANGED debug_leader
               /\ UNCHANGED done
               
Next == 
    \/ genTrans1
    \/ genTrans2
    \/ applyLog(follower)
    \/ doneChecker
    \/ Terminating

allVars == vars \o << done >>

Spec == Init /\ [][Next]_allVars

\*THEOREM Spec => []Lin1 /\ []Lin2

====