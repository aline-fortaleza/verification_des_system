---- MODULE MC ----
EXTENDS ticketing, TLC

\* CONSTANT definitions @modelParameterConstants:0NUMSEATS
const_177003084140420000 == 
10
----

\* CONSTANT definitions @modelParameterConstants:1MALICIOUS
const_177003084140421000 == 
FALSE
----

\* CONSTANT definitions @modelParameterConstants:2NUMCLIENTS
const_177003084140422000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3INITMONEY
const_177003084140423000 == 
4
----

\* INVARIANT definition @modelCorrectnessInvariants:3
inv_177003084140427000 ==
 NoDoubleSell
----
=============================================================================
\* Modification History
\* Created Mon Feb 02 12:14:01 CET 2026 by BiaLeao
