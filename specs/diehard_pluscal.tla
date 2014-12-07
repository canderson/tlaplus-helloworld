-------------------------- MODULE diehard_pluscal --------------------------
EXTENDS Integers

Min(m,n) == IF m > n THEN n ELSE m

(***************************************************************************
--algorithm DieHard {
  variables big = 0, small = 0;
  { while(TRUE) {
    either big := 5 \* Fill big
    or small := 3 \* Fill small
    or big := 0 \* Empty big
    or small := 0 \* Empty small
    or with (poured = Min(big + small, 5) - big) \* Pour small in to big
      { big := big + poured;
        small := small - poured }
    or with (poured = Min(big+small,3) - small) \* Pour big into small
      { big := big - poured;
        small := small + poured }
  }}
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES big, small

vars == << big, small >>

Init == (* Global variables *)
        /\ big = 0
        /\ small = 0

Next == \/ /\ big' = 5
           /\ small' = small
        \/ /\ small' = 3
           /\ big' = big
        \/ /\ big' = 0
           /\ small' = small
        \/ /\ small' = 0
           /\ big' = big
        \/ /\ LET poured == Min(big + small, 5) - big IN
                /\ big' = big + poured
                /\ small' = small - poured
        \/ /\ LET poured == Min(big+small,3) - small IN
                /\ big' = big - poured
                /\ small' = small + poured

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

TypeOK == big \in 0..5 /\ small \in 0..3
NotSolved == big # 4

=============================================================================
\* Modification History
\* Last modified Sat Dec 06 14:50:21 PST 2014 by christian
\* Created Sat Dec 06 14:41:18 PST 2014 by christian
