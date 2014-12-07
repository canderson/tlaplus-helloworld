---------------------------- MODULE one_bit_clock ----------------------------
EXTENDS Integers
VARIABLE b

TypeOK == b \in {0,1}

Init1 == (b=0) \/ (b=1)
Next1 == \/ /\ b = 0
            /\ b' = 1
         \/ /\ b = 1
            /\ b' = 0
Next2 == b' = IF b = 0 THEN 1 ELSE 0
Next3 == b' = (b + 1) % 2
Next4 == IF b = 0 THEN b' = 1 ELSE b' = 0
Next5 == ((b = 0) => (b' = 1)) /\ ((b = 1) => (b' = 0))

=============================================================================
\* Modification History
\* Last modified Sat Dec 06 18:39:40 PST 2014 by christian
\* Created Sat Dec 06 00:31:16 PST 2014 by christian
