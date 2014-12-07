-------------------------------- MODULE gcd --------------------------------

EXTENDS Integers

Divides(p,n) == \E q \in 1..n : n = q * p
DivisorsOf(n) == {p \in 1..n : Divides(p,n)}
SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

\* Exported:
GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))
SetGCD(T) == SetMax({d \in Int : \A t \in T : Divides(d,t)})
=============================================================================
\* Modification History
\* Last modified Sat Dec 06 17:23:33 PST 2014 by christian
\* Created Sat Dec 06 14:59:19 PST 2014 by christian
