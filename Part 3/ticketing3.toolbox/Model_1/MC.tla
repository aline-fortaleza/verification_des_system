---- MODULE MC ----
EXTENDS ticketing3, TLC

\* CONSTANT definitions @modelParameterConstants:0NUMSEATS
const_1770120389668296000 == 
10
----

\* CONSTANT definitions @modelParameterConstants:1MALICIOUS
const_1770120389668297000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:2NUMCLIENTS
const_1770120389668298000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3INITMONEY
const_1770120389668299000 == 
4
----

\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1770120389668302000 ==
 NoDoubleSell
----
=============================================================================
\* Modification History
\* Created Tue Feb 03 13:06:29 CET 2026 by BiaLeao
