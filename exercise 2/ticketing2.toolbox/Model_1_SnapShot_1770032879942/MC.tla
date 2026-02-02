---- MODULE MC ----
EXTENDS ticketing2, TLC

\* CONSTANT definitions @modelParameterConstants:0NUMSEATS
const_177003275684485000 == 
10
----

\* CONSTANT definitions @modelParameterConstants:1MALICIOUS
const_177003275684486000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:2NUMCLIENTS
const_177003275684487000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3INITMONEY
const_177003275684488000 == 
4
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_177003275684589000 ==
 MoneyTicketsInv
----
=============================================================================
\* Modification History
\* Created Mon Feb 02 12:45:56 CET 2026 by BiaLeao
