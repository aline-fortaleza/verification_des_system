---- MODULE MC ----
EXTENDS ticketing3, TLC

\* CONSTANT definitions @modelParameterConstants:0NUMSEATS
const_1770230673625344000 == 
10
----

\* CONSTANT definitions @modelParameterConstants:1MALICIOUS
const_1770230673625345000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:2NUMCLIENTS
const_1770230673625346000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3INITMONEY
const_1770230673625347000 == 
4
----

\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1770230673625350000 ==
 NoDoubleSell
----
=============================================================================
\* Modification History
\* Created Wed Feb 04 19:44:33 CET 2026 by BiaLeao
