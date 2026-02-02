---- MODULE MC ----
EXTENDS ticketing2, TLC

\* CONSTANT definitions @modelParameterConstants:0NUMSEATS
const_1770041432648226000 == 
10
----

\* CONSTANT definitions @modelParameterConstants:1MALICIOUS
const_1770041432648227000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:2NUMCLIENTS
const_1770041432648228000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3INITMONEY
const_1770041432648229000 == 
4
----

\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1770041432648231000 ==
 MoneyTicketsInv
----
=============================================================================
\* Modification History
\* Created Mon Feb 02 15:10:32 CET 2026 by BiaLeao
