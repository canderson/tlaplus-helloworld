----------------------------- MODULE gcd_lemmas -----------------------------
EXTENDS gcd

GCDLemma1 == \A m \in Nat \ {0} : GCD(m,m) = m
GCDLemma2 == \A m, n \in Nat \ {0} : GCD(m,n) = GCD(n,m)
GCDLemma3 == \A m, n \in Nat \ {0} : (n > m) => (GCD(m,n) = GCD(m, n - m))

=============================================================================
\* Modification History
\* Last modified Sat Dec 06 17:19:59 PST 2014 by christian
\* Created Sat Dec 06 17:18:26 PST 2014 by christian
