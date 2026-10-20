# Algorithm and encoding contracts

The semantic correspondences, instruction executions and encoded-machine
contracts in this repository have distinct interfaces. This account identifies
what the selected statements establish and the remaining bridges to the full
paper algorithms.

## Program families and code construction

The ten Comparator files identify the registry-selected statements and any
implementation definition holes. Definition-hole comparison checks the type
and permitted axioms; it does not fix a predetermined implementation body.
The concrete supplied implementations therefore have separate image and
construction contracts in the proof library.

P04's `ForestSourceCompiler` constructs the complete cold resident from original
source rows, roots and weights, with linear construction work and temporary
word storage. It takes no selected set or precomputed healthy family as input.
The weighted cold execution emits an attained physical optimum under the
healthy-zero and nonnegative-weight premises. P06's critical/cycle recovery
instead uses a fixed 57-instruction source reader at each word width.

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

P07's selected execution statements retain raw-layout and representation
hypotheses. The XP and special-case inequalities support those executions.
Its concrete construction companions prove source-only bounded and proper-basis
constructors, complete code images, construction plus execution time and
temporary word storage. The constructed proper-basis guarded branch uses the
bounded `k=0` implementation. The original registry-selected proper-basis
execution keeps its own implementation. The construction certificates are
listed in the companion audit manifest rather than added as P07 Comparator
targets.

P10 provides the complete K00 encoded-machine simulation and composition bridge
under its stated constructor and resource premises. The word-model construction
proofs do not by themselves prove K01 or classify the complete encoded detector
language. P02/P03 construction and P08 accepted-family claims have their
separate interfaces and are not implicit consequences of these companions.

## Forest outputs and weights

P04 emits an indicator of an admissible detecting eligible set. That set
defines a canonical physical input; it is not a serialization of every primary
input coordinate. Its selected weighted statements include score domination
and an attained physical maximum under healthy-zero observations, nonnegative
weights, positive bus count and detectability. Generic arithmetic-operation
counts and encoded-weight bit costs are separate.

## Width and recognition

P06 includes both specification-clause graphs and the complete binary-expanded
native CNF graphs. The added native primal/incidence lower bounds use their
literal complete native clause list. Critical-set counts, query bounds and
native/specification backdoor theorems retain their own hypotheses.

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

The full paper target also includes the separate P02/P03 uniform source
construction interfaces, a nontrivial accepted P08 typed family, and conventional
encoded-language classification. The forest and extension construction
companions and the P06 binary-native width theorems establish their displayed
contracts; they do not imply those separate claims.
