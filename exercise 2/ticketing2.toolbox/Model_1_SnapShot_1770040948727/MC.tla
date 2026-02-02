---- MODULE MC ----
EXTENDS ticketing2, TLC

\* CONSTANT definitions @modelParameterConstants:0NUMSEATS
const_1770040938621206000 == 
10
----

\* CONSTANT definitions @modelParameterConstants:1MALICIOUS
const_1770040938621207000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:2NUMCLIENTS
const_1770040938621208000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3INITMONEY
const_1770040938621209000 == 
4
----

\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1770040938621211000 ==
 MoneyTicketsInv
----
=============================================================================
\* Modification History
\* Created Mon Feb 02 15:02:18 CET 2026 by BiaLeao
