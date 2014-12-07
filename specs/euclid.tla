------------------------------- MODULE euclid -------------------------------
EXTENDS Integers, gcd, TLC

CONSTANTS N

ASSUME N \in Nat \ {0}

(***************************************************************************
--fair algorithm Euclid {
  variables x \in 1..N, y \in 1..N, x0 = x, y0 = y;
  {
    abc: while (x # y) {
      d: if (x < y) {y := y - x} else {x := x - y}
    };
    assert (x = y) /\ (x = GCD(x0,y0))
  }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES x, y, x0, y0, pc

vars == << x, y, x0, y0, pc >>

Init == (* Global variables *)
        /\ x \in 1..N
        /\ y \in 1..N
        /\ x0 = x
        /\ y0 = y
        /\ pc = "abc"

abc == /\ pc = "abc"
       /\ IF x # y
             THEN /\ pc' = "d"
             ELSE /\ Assert((x = y) /\ (x = GCD(x0,y0)), 
                            "Failure of assertion at line 15, column 5.")
                  /\ pc' = "Done"
       /\ UNCHANGED << x, y, x0, y0 >>

d == /\ pc = "d"
     /\ IF x < y
           THEN /\ y' = y - x
                /\ x' = x
           ELSE /\ x' = x - y
                /\ y' = y
     /\ pc' = "abc"
     /\ UNCHANGED << x0, y0 >>

Next == abc \/ d
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

TypeOK == {x, y} \subseteq Nat \ {0}

PartialCorrectness ==
  (pc = "Done") => (x = y) /\ (x = GCD(x0,y0))
  
GCDInvariant ==
  TypeOK /\ (GCD(x,y) =  GCD(x0,y0)) /\ ((pc = "Done") => (x = y))

=============================================================================
\* Modification History
\* Last modified Sat Dec 06 16:27:01 PST 2014 by christian
\* Created Sat Dec 06 15:17:40 PST 2014 by christian
