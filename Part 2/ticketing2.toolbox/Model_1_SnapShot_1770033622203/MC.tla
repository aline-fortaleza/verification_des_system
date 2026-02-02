---- MODULE MC ----
EXTENDS ticketing2, TLC

\* CONSTANT definitions @modelParameterConstants:0NUMSEATS
const_1770033591073112000 == 
10
----

\* CONSTANT definitions @modelParameterConstants:1MALICIOUS
const_1770033591073113000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:2NUMCLIENTS
const_1770033591073114000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3INITMONEY
const_1770033591073115000 == 
4
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1770033591073116000 ==
 MoneyTicketsInv
----
=============================================================================
\* Modification History
\* Created Mon Feb 02 12:59:51 CET 2026 by BiaLeao
