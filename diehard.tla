---- MODULE diehard ---- 

EXTENDS Naturals

VARIABLES big,   \* The number of gallons of water in the 5 gallon jug.
          small  \* The number of gallons of water in the 3 gallon jug.

Init == /\ big = 0 
        /\ small = 0
        
TypeOK == /\ small \in 0..3 
          /\ big   \in 0..5
          
EmptyBig == /\ small' = small
            /\ big' = 0

EmptySmall == /\ small' = 0
              /\ big' = big

FillBig == /\ small' = small
           /\ big' = 5

FillSmall == /\ small' = 3
             /\ big' = big

\*SmallToBig == /\ small' = IF (5 - big) > small \*如果small能够全部倒进去
\*                          THEN 0 
\*                          ELSE small - (5 - big)
\*              /\ big' = IF (5 - big) > small 
\*                        THEN big + small
\*                        ELSE 5
\*              
\*BigToSmall == /\ small' = IF (3 - small) > big \*如果big能够全部倒进去
\*                          THEN big+small 
\*                          ELSE 3
\*              /\ big' = IF (3 - small) > big 
\*                        THEN 0 
\*                        ELSE big - (3 - small)

Min(m,n) == IF m < n THEN m ELSE n
SmallToBig == /\ big'   = Min(big + small, 5)
              /\ small' = small - (big' - big)

BigToSmall == /\ small' = Min(big + small, 3) 
              /\ big'   = big - (small' - small)

Next ==  \/ EmptyBig 
         \/ EmptySmall    
         \/ FillBig 
         \/ FillSmall    
         \/ SmallToBig    
         \/ BigToSmall    

Spec == Init /\ [][Next]_<<big, small>> 

NotSolved == big # 4

====