# Algorithm and encoding contracts

The semantic correspondences, instruction executions and encoded-machine
contracts in this repository have distinct interfaces. This account identifies
what the selected statements establish and the remaining bridges to the full
paper algorithms.

## Program families and code construction

P02, P03, P04, P06 and P07 select instance-dependent program definitions supplied
by the Solution. Comparator checks the types and permitted axioms of definition
holes; it does not require their bodies to equal a predetermined implementation.
The supplied source bodies therefore require separate inspection. The ordinary
machine transition and resource definitions are explicit in each Challenge.

A bound on fetched execution starts with an instruction array already available.
It does not charge the computation used to generate that array. P04's
`ForestRootProjection.mixedSelectorCode` evaluates `ForestWeightedIndexed.runAll`
to form an instruction constant; `mixedPositiveProgram` also computes the
selected candidate when constructing its suffix. P06's `CriticalSets.forestProgram`
uses this assembly. Their fetched tick bounds do not establish the paper's
uniform linear-time algorithm. A charged constructor or a fixed program reading
the instance remains necessary for that conclusion.

P02's execution theorem decides whether a constrained detecting set exists and
checks its emitted native model. Its postcondition does not identify that model's
eligible set with the constrained witness. The live-word bound includes the
native-size term on both rejection and acceptance.

P03's `stream_step` includes search and canonical emission, and restores the
iterator invariant before the next search. `execution_output_sensitive` bounds
the entire run by `(r+1)*delay + r*emitBudget`, where `r` is the number of results.
One instruction array serves all prefixes of the supplied instance. Its program
and emitter remain definition holes; the selected interface does not charge
construction of that instance-dependent code. Working words exclude the retained
external output stream, and code words have a separate bound.

P07's execution statements retain the raw-layout and representation hypotheses.
Its XP and special-case inequalities bound the explicit time function. They are
supporting estimates for the execution statements.

P10 supplies fixed-machine simulation and composition results under their stated
constructor and resource premises. Applying those results to a program family
requires proofs of those premises, including charged image construction. The
general K00 bridge alone does not discharge them for P02–P07.

## Forest outputs and weights

P04's accepted output contains an indicator of an admissible detecting set K.
That descriptor defines a canonical physical input; it is not a serialization
of every primary-input coordinate. The selected weighted theorem bounds the
weight of each admissible true set by a returned candidate's score. It assumes
that candidate is returned and proves neither candidate existence nor score
attainment. Weight arithmetic is counted separately from encoded bit costs.

## Width and recognition

P06's selected primal and incidence graphs use the n-ary specification clause
list. A minor/width transfer to the bounded-gate native encoding in Proposition
6.10 remains required. The critical-set counts, query bounds and separately
identified native or specification backdoor theorems keep their literal scope.

P08's typed pipeline is sound after successful acceptance of a structured
payload. `decodeChecked_requires_extra_coordinates` proves that, with at least
one observed root, the source coordinate count must exceed the native variable
count. Private activities require those additional coordinates. The plain native
coordinate count therefore cannot be accepted in that case. A nontrivial
positive-output acceptance construction is not supplied. Projection equivalences
preserve the declared activity and polarity grammar; recognizer completeness and
raw-file parsing are separate claims.

## Resolution and supporting statements

P09's `canonical_refutation_resources` proves that one `compactRefute` object
passes the ordinary-resolution checker, has at most `100000*v^3` inferences and
at most `200000*v^4` derived literal occurrences, where `v` counts native
variables. These are certificate-size bounds. No polynomial-time compiler bound
is asserted by that theorem.

P01 and P05 state physical-image and representation/counting results with their
exact finite universes and interface hypotheses. A finite counting correspondence
alone is not an encoded counting-hardness theorem. Arithmetic estimates and size
lemmas elsewhere in the selection support the principal results; their proof
length does not change their mathematical scope.

The full target of the paper algorithms is retained. Uniform charged program
construction, the bounded-encoding width transfer and a nontrivial accepted
typed-family construction remain open obligations of that target. Passing
mechanical checks of the selected components does not close those obligations.
