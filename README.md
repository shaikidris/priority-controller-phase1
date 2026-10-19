# Priority-controller images and guarded detection

This Lean development studies a finite priority controller with independent
enable and request bits. Its selector follows the literal XOR-mask recurrence;
observations read the final qualifier vector before any channel encoder.
The formalization proves exact physical fault images and observation criteria,
then uses supplied guarded decoder DAGs to decide detection, construct witnesses
and extend partial eligibility assignments. It also contains charged native
execution results for the detector and further entry-specific enumeration,
representation, obstruction, certificate and encoded-machine results.

Each Palomar entry selects its own statements and records its assumptions in
[the entry catalogue](ENTRIES.md). A selected Comparator does not assert every
result in the source library. The source is Idris Ali Shaik, *Polynomial Fault
Detection Without Bounded Width: Exact Reachable Sets in Priority Controllers*,
version 1.0, [DOI 10.5281/zenodo.23400057](https://zenodo.org/records/23400057).
Per-entry metadata distinguishes manuscript statements from implementation
refinements and other differences in the formalization.

The [algorithm and encoding contracts](SEMANTIC_SCOPE.md) identify the remaining
uniform code-construction, bounded-encoding width and typed-family acceptance
bridges. The selected component theorems retain their literal scope; the full
paper algorithm target remains open at those bridges.

## P01: exact physical images

[P01](Phase1/P01/Challenge.lean) characterizes the activated drive-one bridge
image, excludes drive-zero detection, relates detection to qualifier-observation
discrepancies, proves the proper-coordinate projection obstruction and classifies
a specified qualifier-only stuck-at fault. Its source references are Section 3
and Theorem 4.1, Corollary 4.2, Lemma 4.3 and Theorem 4.4. Its selected statements
do not assert an algorithmic complexity bound. P01 uses the root
[formalization.yaml](formalization.yaml) and
[entries/P01/comparator.json](entries/P01/comparator.json).

## P02: guarded detection and constrained extension

[P02's Challenge](Phase1/P02/Challenge.lean),
[Solution](Phase1/P02/Solution.lean) and
[Comparator](entries/P02/comparator.json) select six theorems and the cold
program implementation:

- **Detector correctness and completeness.** For a supplied guarded decoder
  DAG, positive bus count and the displayed physical bridge interface, the
  detector returns a primary input exactly when a detecting input exists.
  Every returned input satisfies the interface and distinguishes an observed
  root. These are the semantic components of manuscript Theorem 5.1.
- **Constrained extension.** Given fixed-true and fixed-false eligibility sets,
  the extension routine returns an admissible root-changing set extending those
  constraints exactly when one exists with drive one. Its failure criterion
  includes inconsistent constraints. These results formalize Theorem 5.4;
  the constraints concern eligibility coordinates, not arbitrary enable or
  request bits.
- **Cold native execution.** The selected program halts with the exact constrained
  decision under the displayed raw-layout, drive-one, consistency,
  graph/row/head/root matching, observation-correspondence and initial-state
  assumptions. Let `n` count channels, `q` graph roots, `G` the displayed counted
  decoder size and `S` the selected native size. The run takes at most
  `5100*(n+q+1)*(G+1)` ticks, plus `55*S` on acceptance. Peak live words are at
  most the initial live words plus `210*(G+1)+3*S`. An accepting run emits output
  accepted by the specified native model checker. The model-checking postcondition
  does not tie that model's eligible set to T/F. The code is supplied by an
  instance-dependent factory whose construction cost is not selected. This explicit instruction
  model, program, constants and output-checking postcondition refine the
  algorithmic account in Theorems 5.1 and 5.4; the exact machine statement is
  not a separately numbered theorem of the manuscript.

The decoder structure is supplied. P02 does not recognize a guarded presentation
of arbitrary CNF or establish conventional encoded-language membership.
Its [metadata](entries/P02/formalization.yaml) gives the six exact theorem names,
source correspondence and qualifications. The proofs live in
[Controller.Public.Detection](Controller/Public/Detection.lean),
[Controller.Decoder.Extend](Controller/Decoder/Extend.lean) and
[Controller.Cost.SharedDetectorCold](Controller/Cost/SharedDetectorCold.lean).

## P03: canonical streaming enumeration

[P03](Phase1/P03/Challenge.lean) enumerates the detecting eligible sets of a
supplied guarded DAG without duplicates and in the stated order, and proves
that their canonical primary-input realizations detect. The supplied native
program terminates within `(r+1)*delay+r*emitBudget` ticks for `r` results.
The stream-step theorem includes search, canonical emission and return to the
iterator invariant, or exhaustion. One program serves all prefixes of the
instance; a charged constructor for that instance-dependent code remains separate. Immutable code,
mutable working words, external output and per-result emission costs are
separate measures. These results refine Corollary 5.5, based on Theorem 5.4.
The explicit program and numerical constants are implementation refinements;
the entry does not enumerate all primary assignments or all native-CNF models.
[Metadata and exact alignment](entries/P03/formalization.yaml).

## P04: formula forests and weighted candidate bounds

[P04](Phase1/P04/Challenge.lean) gives physical detection execution for a
supplied formula forest with matching rows, heads and roots, under its displayed
native layout and initial-state assumptions. It bounds ticks, live words and
other declared operation/storage measures and emits a detecting eligible-set
descriptor on acceptance. Its reference code factory precomputes a selected result;
the fetched tick bound does not charge that computation or establish the full
uniform algorithm of Theorem 5.6. Its separate weighted theorem assumes a
returned traversal candidate and nonnegative weights, and bounds every
admissible true-set weight by that candidate's score with linear operation
counts. This is the upper-bound component of Corollary 6.7; it does not establish
candidate existence, attainment or maximum-weight optimality of the emitted
physical test. Encoded-weight bit costs are separate.
[Metadata and exact alignment](entries/P04/formalization.yaml).

## P05: dual-Horn and graph-cover representations

[P05](Phase1/P05/Challenge.lean) represents dual-Horn satisfiability and finite
graph vertex covers by physical bridge detection. Its theorems prove semantic
correspondence, counted decoder size, formula-forest structure and eligible-set
count/realization laws. Source variables, isolated graph vertices and literal
multiplicities remain declared; graph enumeration and the required edge witness
are supplied. The source constructions are Propositions 5.2 and 6.4. The count
concerns eligible sets, and the selection does not assert a complete encoded
P-completeness or counting-hardness theorem.
[Entry account](entries/P05/README.md) and
[metadata](entries/P05/formalization.yaml).

## P06: critical sets, query bounds and structural obstructions

[P06](Phase1/P06/Challenge.lean) formalizes the cycle/critical-set constructions
of Example 6.1 and Proposition 6.2, universal physical-test-list lower bounds,
and deterministic and finite randomized query bounds from Corollary 6.3.
The costed recovery runs refine the constructive arguments with explicit native
representation and execution premises. The structural theorems cover the
specified primal/incidence encodings of Proposition 6.10, the conditional
graph-width component of Proposition 6.11 and the syntactic backdoors of
Proposition 6.12.
Expansion and degree bounds are supplied assumptions. The query bounds restrict
oracle access; they are not sequential-time lower bounds for an algorithm that
reads decoder syntax. No infinite expander construction or DNNF lower bound is
selected. [Metadata and exact alignment](entries/P06/formalization.yaml).

## P07: bounded live conjunction and proper bases

[P07](Phase1/P07/Challenge.lean) proves small-support and consistent selector
expansion laws from Lemmas 7.2 and 7.3, then gives actual native detection and
checked emitted witnesses for a supplied live-AND bound. Its numerical XP,
one-live-AND and healthy-one estimates refine Theorem 7.4; the displayed general
XP and healthy-one inequalities are weaker than the manuscript's sharper
expressions. The proper-basis program formalizes the algorithmic component of
Theorem 7.5 under supplied basis and representation evidence. It does not prove
the full-basis hardness classification or independently supply an encoded
language's missing construction bridge.
[Metadata and exact alignment](entries/P07/formalization.yaml).

## P08: observation projection and typed certificates

[P08](Phase1/P08/Challenge.lean) proves conditional observation projection and
optional/selected-wrapper equivalences from Theorems A.1 and A.2 and Corollary
A.3, plus intended-producer recovery from Lemma A.4. Its selected-observation
projection also handles the empty-list case. The Section 8 interface is refined
by checked structured-family decoding, model lifting, exact SAT behavior after
acceptance and sound SAT/UNSAT verdicts. Certified-UNSAT completeness assumes a
supplied certificate accepted by the typed checker. The payload, intended DAG,
promises and grammar premises remain explicit. This is not a raw DIMACS/JSON
parser, unrestricted CNF discovery or a proof of every auxiliary construction
time bound. [Metadata and exact alignment](entries/P08/formalization.yaml).

## P09: checked ordinary resolution

[P09](Phase1/P09/Challenge.lean) gives explicit ordinary-resolution construction
and checker acceptance for the raw guarded native encoding and supported
optional/selected observation wrappers. Theorems B.1 and B.2 and Corollary A.3
supply the source arguments. Completeness is stated under UNSAT and the relevant
wrapper/selection premises; returned-result checking is separate. The numerical
bounds count cubic inferences in the displayed size parameters, with a separate
quartic bound on derived literal occurrences. They do not bound compiler running
time or claim cubic encoded proof size. No extension-variable rule or arbitrary
CNF completeness is asserted.
[Metadata and exact alignment](entries/P09/formalization.yaml).

## P10: encoded simulation and reduction composition

[P10](Phase1/P10/Challenge.lean) selects six principal theorems from the
39-declaration K00 bridge: decoded image execution, polynomial-time native-to-TM2
compilation, logarithmic-space composition and allocation erasure, parameterized
reduction composition, and input-independent finite-TM2 realization. Constructor
execution and intermediate output size are charged where required; space uses
the stated finite-control tape model and visited-cell predicate. The custom
encodings and machine witnesses are stated and proved in this development,
using standard simulation and composition mechanisms. The controller manuscript
is background for this entry. Application-specific constructors and resulting
encoded-language class membership remain separate obligations.
[Proof mechanisms](entries/P10/README.md) and
[metadata](entries/P10/formalization.yaml).

## Selecting an entry

For P02, select `entries/P02/comparator.json` and explicitly set **File layout →
Formalization metadata** to `entries/P02/formalization.yaml`. Leave the project
directory blank. Selecting a Comparator does not automatically select the
metadata beside it: the default metadata is the root P01 file. Use the matching
metadata path in [ENTRIES.md](ENTRIES.md) for every other entry.

The project uses Lean 4.35.0-rc3 and canonical Mathlib at the exact revision in
the Lake manifest. Build and compare P02 with:

```sh
lake build Phase1.P02.Challenge Phase1.P02.Solution
lake comparator --config entries/P02/comparator.json
```

The proofs were developed with AI assistance under the author's direction.
[Source provenance](SOURCE_PROVENANCE.md) records manuscript and extraction
identities. Author-owned source is licensed under [Apache-2.0](LICENSE);
dependency licences and notices remain applicable.
