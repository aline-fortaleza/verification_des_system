---- MODULE MC ----
EXTENDS ticketing2, TLC

\* CONSTANT definitions @modelParameterConstants:0NUMSEATS
const_1770040737517168000 == 
10
----

\* CONSTANT definitions @modelParameterConstants:1MALICIOUS
const_1770040737517169000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:2NUMCLIENTS
const_1770040737517170000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3INITMONEY
const_1770040737517171000 == 
4
----

\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1770040737518173000 ==
 MoneyTicketsInv
----
=============================================================================
\* Modification History
\* Created Mon Feb 02 14:58:57 CET 2026 by BiaLeao
