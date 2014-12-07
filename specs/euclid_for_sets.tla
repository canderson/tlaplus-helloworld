-------------------------- MODULE euclid_for_sets --------------------------
EXTENDS Integers, gcd, TLC

CONSTANTS Input

ASSUME Input \subseteq Nat \ {0} /\ Input # {}

(***************************************************************************
--fair algorithm EuclidForSets {
  variables S = Input;
  {
    while (\E x,y \in S : x # y) {
        with (x \in S, y \in {s \in S : s > x})
          { S := (S \ {y}) \cup {y - x} }
    };
  }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES S, pc

vars == << S, pc >>

Init == (* Global variables *)
        /\ S = Input
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF \E x,y \in S : x # y
               THEN /\ \E x \in S:
                         \E y \in {s \in S : s > x}:
                           S' = ((S \ {y}) \cup {y - x})
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ S' = S

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

RECURSIVE SetSum(_)
SetSum(T) == IF T = {}
             THEN 0
             ELSE LET t == CHOOSE x \in T : TRUE
                  IN t + SetSum(T \ {t})

TypeOK == /\ S \subseteq Nat \ {0}
          /\ S # {}
          
PartialCorrectness ==
  (pc = "Done") => (S = {SetGCD(Input)})

EuclidForSetsInvariant == /\ TypeOK
                          /\ SetGCD(S) = SetGCD(Input)
                          /\ PartialCorrectness
=============================================================================
\* Modification History
\* Last modified Sat Dec 06 17:07:46 PST 2014 by christian
\* Created Sat Dec 06 16:46:37 PST 2014 by christian
