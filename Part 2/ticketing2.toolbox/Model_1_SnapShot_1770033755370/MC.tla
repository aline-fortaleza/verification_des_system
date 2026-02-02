---- MODULE MC ----
EXTENDS ticketing2, TLC

\* CONSTANT definitions @modelParameterConstants:0NUMSEATS
const_1770033679416121000 == 
10
----

\* CONSTANT definitions @modelParameterConstants:1MALICIOUS
const_1770033679416122000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:2NUMCLIENTS
const_1770033679416123000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3INITMONEY
const_1770033679416124000 == 
4
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1770033679417125000 ==
 MoneyTicketsInv
----
=============================================================================
\* Modification History
\* Created Mon Feb 02 13:01:19 CET 2026 by BiaLeao
