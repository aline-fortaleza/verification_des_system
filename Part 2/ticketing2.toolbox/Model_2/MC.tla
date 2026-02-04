---- MODULE MC ----
EXTENDS ticketing2, TLC

\* CONSTANT definitions @modelParameterConstants:0NUMSEATS
const_1770231846002398000 == 
10
----

\* CONSTANT definitions @modelParameterConstants:1MALICIOUS
const_1770231846002399000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:2NUMCLIENTS
const_1770231846002400000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3INITMONEY
const_1770231846002401000 == 
5
----

\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1770231846002403000 ==
 MoneyTicketsInv
----
=============================================================================
\* Modification History
\* Created Wed Feb 04 20:04:06 CET 2026 by BiaLeao
