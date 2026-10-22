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

The [algorithm and encoding contracts](SEMANTIC_SCOPE.md) state the exact
entry interfaces. [Concrete construction contracts](CONSTRUCTION_CONTRACTS.md)
cover forest, bounded-live-AND and proper-basis source constructors, including
execution and temporary word storage. P06 includes complete binary-native width
proofs. P08 supplies a complete accepted positive-output typed packet. P02/P03
source construction and conventional encoded-language classification have
their separate interfaces.

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

## P04: forest detection and attained maximum weight

[P04](Phase1/P04/Challenge.lean) proves physical detection execution for supplied
formula forests, the weighted score bound, and an attained maximum-weight
physical detecting set for healthy-zero observations. The optimum theorem
retains nonnegative weights, a positive bus count and detectability. Its output
is an eligible-set indicator defining a canonical physical realization.

The [complete forest constructor](Controller/Cost/ForestSourceCompiler.lean)
reads original rows, roots and weights, constructs the same checked resident,
and has linear construction work and temporary word storage. The
[cold weighted execution](Controller/Cost/ForestWeightedCold.lean) emits the
attained optimum. Generic weight arithmetic and encoded bit costs have separate
contracts. [Metadata and exact alignment](entries/P04/formalization.yaml).

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

## P06: source recovery, query obstructions and native width

[P06](Phase1/P06/Challenge.lean) combines critical-set and cycle recovery,
black-box query lower bounds, backdoors, and primal/incidence width results.
The source recovery statements use one fixed 57-instruction program at each
word width. They include original source loading, canonical indicator emission,
halt and the displayed fetched, live-word and resident-word bounds, under the
stated critical-family or cycle source promises.

The binary-native width statements use the complete binary-expanded native CNF,
with its auxiliary wires and clauses. Both its primal and incidence treewidths
are at least the minimum of the channel and bus counts. Specification-graph
width statements retain their own graphs. These structured-family results do
not recognize arbitrary CNF or supply an infinite expander construction.
[Metadata and exact alignment](entries/P06/formalization.yaml).

## P07: bounded live conjunction and proper bases

[P07](Phase1/P07/Challenge.lean) selects the bounded-support and consistent
selector-expansion laws, complete bounded native execution and emitted-witness
checking, its displayed XP/special-case inequalities, and proper-basis execution.
Raw-layout, live-AND, basis `Uses`, proper-basis and representation premises are
explicit. The displayed general XP and healthy-one inequalities retain their
stated bounds rather than asserting the manuscript's sharper expressions.

The [construction companions](Controller/Cost/ExtensionAlgorithmsComplete.lean)
prove concrete source-only constructors, exact code images, total construction
plus execution time, and temporary construction storage. The constructed
proper-basis implementation uses bounded `k=0` in the guarded case and source
table constructors in the monotone/literal cases. The registry's selected
proper-basis theorem retains its own implementation. These larger construction
certificates are included in the proof library and the independent audit target
list; they are not additional Comparator-selected statements in P07.
[Construction contracts](CONSTRUCTION_CONTRACTS.md) and
[metadata](entries/P07/formalization.yaml).

## P08: observation projection and typed certificates

[P08](Phase1/P08/Challenge.lean) proves the conditional observation projection
and optional/selected-wrapper equivalences of Theorems A.1 and A.2 and Corollary
A.3. For guarded native controllers, declared optional wrappers with matching
observed pairs and full root coverage are satisfiable exactly when the physical
detector returns a detecting input. A finite candidate-scanning driver proves
exact intended-producer recovery under the candidate promise of Lemma A.4,
without a supplied run or maximality witness.

The typed Section 8 interface provides checked decoding, model lifting, exact
SAT behavior after acceptance and sound SAT/UNSAT verdicts. Certified-UNSAT
completeness requires an accepted refutation certificate. A fully accepted
serialized packet with two channels, one bus, one observed output, 36 source
coordinates and 91 rows has a physical detecting input, a source model and a
SAT verdict. Candidate discovery, a general accepted-family constructor,
raw-file parsing and machine-level auxiliary construction costs are separate
claims. [Proof mechanisms](entries/P08/README.md) and
[metadata and exact alignment](entries/P08/formalization.yaml).

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

## Abstract coverage

Each entry's `abstract-coverage.json` maps every selected theorem to a reviewed
mathematical family and exact wording in its public abstract. The preparation
guard checks all ten maps and rejects missing families, absent phrases or stale
metadata, Comparator and Challenge hashes before the full rehearsal. Review the
semantic changes before updating a map; the checker verifies coverage and
freshness of that review, rather than automatically certifying its meaning.

```sh
python3 scripts/check_palomar_abstract_coverage.py --source . \
  --metadata entries/P06/formalization.yaml \
  --comparator entries/P06/comparator.json \
  --coverage entries/P06/abstract-coverage.json
```

The proofs were developed with AI assistance under the author's direction.
[Source provenance](SOURCE_PROVENANCE.md) records manuscript and extraction
identities. Author-owned source is licensed under [Apache-2.0](LICENSE);
dependency licences and notices remain applicable.
