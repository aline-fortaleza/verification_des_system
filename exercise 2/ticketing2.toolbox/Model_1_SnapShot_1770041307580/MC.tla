---- MODULE MC ----
EXTENDS ticketing2, TLC

\* CONSTANT definitions @modelParameterConstants:0NUMSEATS
const_1770041290714216000 == 
10
----

\* CONSTANT definitions @modelParameterConstants:1MALICIOUS
const_1770041290714217000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:2NUMCLIENTS
const_1770041290714218000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3INITMONEY
const_1770041290714219000 == 
4
----

\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1770041290714221000 ==
 MoneyTicketsInv
----
=============================================================================
\* Modification History
\* Created Mon Feb 02 15:08:10 CET 2026 by BiaLeao
