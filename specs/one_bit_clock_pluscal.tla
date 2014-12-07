---------------------------- MODULE hello_world2 ----------------------------

EXTENDS Integers

(***************************************************************************
--algorithm Clock {
variable b \in {0,1};
{ while (TRUE) {b := (b+1)%2
               }
}
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLE b

vars == << b >>

Init == (* Global variables *)
        /\ b \in {0,1}

Next == b' = (b+1)%2

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sat Dec 06 14:12:56 PST 2014 by christian
\* Created Sat Dec 06 01:26:29 PST 2014 by christian
