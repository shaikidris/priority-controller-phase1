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
  accepted by the specified native model checker. This explicit instruction
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
