---- MODULE MC ----
EXTENDS ticketing2, TLC

\* CONSTANT definitions @modelParameterConstants:0NUMSEATS
const_1770040756592187000 == 
10
----

\* CONSTANT definitions @modelParameterConstants:1MALICIOUS
const_1770040756592188000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:2NUMCLIENTS
const_1770040756592189000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3INITMONEY
const_1770040756592190000 == 
4
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1770040756592191000 ==
 MoneyTicketsInv
----
=============================================================================
\* Modification History
\* Created Mon Feb 02 14:59:16 CET 2026 by BiaLeao
