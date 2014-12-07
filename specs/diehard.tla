------------------------------ MODULE diehard ------------------------------
EXTENDS Integers

VARIABLES big, small

TypeOK == /\ big \in 0..5 /\ small \in 0..3

NotSolved == big # 4

Init == /\ big = 0
        /\ small = 0
        
Min(m,n) == IF m < n THEN m ELSE n

FillSmall == /\ small' = 3 /\ big' = big
FillBig == /\ big' = 5 /\ small' = small
EmptySmall == /\ small' = 0 /\ big' = big
EmptyBig == /\ big' = 0 /\ small' = small
SmallToBig ==
  LET poured == Min(big + small, 5) - big
  IN /\ big' = big + poured
     /\ small' = small - poured
BigToSmall ==
  LET poured == Min(big + small, 3) - small
  IN /\ big' = big - poured
     /\ small' = small + poured
        
Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ SmallToBig
        \/ BigToSmall



=============================================================================
\* Modification History
\* Last modified Sat Dec 06 14:37:07 PST 2014 by christian
\* Created Sat Dec 06 14:15:45 PST 2014 by christian




