---- MODULE MC ----
EXTENDS ticketing3, TLC

\* CONSTANT definitions @modelParameterConstants:0NUMSEATS
const_1770230557252335000 == 
10
----

\* CONSTANT definitions @modelParameterConstants:1MALICIOUS
const_1770230557252336000 == 
TRUE
----

\* CONSTANT definitions @modelParameterConstants:2NUMCLIENTS
const_1770230557252337000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3INITMONEY
const_1770230557252338000 == 
4
----

\* INVARIANT definition @modelCorrectnessInvariants:2
inv_1770230557253341000 ==
 NoDoubleSell
----
=============================================================================
\* Modification History
\* Created Wed Feb 04 19:42:37 CET 2026 by BiaLeao
