---- MODULE MC ----
EXTENDS ticketing2, TLC

\* CONSTANT definitions @modelParameterConstants:0NUMSEATS
const_1770036065799158000 == 
10
----

\* CONSTANT definitions @modelParameterConstants:1MALICIOUS
const_1770036065799159000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:2NUMCLIENTS
const_1770036065799160000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3INITMONEY
const_1770036065799161000 == 
4
----

\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1770036065799163000 ==
 MoneyTicketsInv
----
=============================================================================
\* Modification History
\* Created Mon Feb 02 13:41:05 CET 2026 by BiaLeao
