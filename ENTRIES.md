# Selected formalization entries

The ten entries select 80 theorem statements from the Paper A proof library and
its encoded-machine bridge. The selection retains the complete K00 bridge,
including all 39 K00 obligations. Each entry has its own transparent Challenge,
Solution imports, comparison configuration and source metadata.

| Entry | Scope | Theorems + definitions | Comparator configuration | Formalization metadata |
|---|---|---:|---|---|
| [P01](Phase1/P01/Challenge.lean) | Exact physical image and observation criterion | 6 + 0 | `entries/P01/comparator.json` | `formalization.yaml` |
| [P02](Phase1/P02/Challenge.lean) | Guarded decision and constrained extension | 6 + 1 | `entries/P02/comparator.json` | `entries/P02/formalization.yaml` |
| [P03](Phase1/P03/Challenge.lean) | Canonical enumeration and streaming delay | 8 + 2 | `entries/P03/comparator.json` | `entries/P03/formalization.yaml` |
| [P04](Phase1/P04/Challenge.lean) | Formula-forest execution and candidate score bounds | 2 + 3 | `entries/P04/comparator.json` | `entries/P04/formalization.yaml` |
| [P05](Phase1/P05/Challenge.lean) | Dual-Horn and graph-cover representations | 7 + 0 | `entries/P05/comparator.json` | `entries/P05/formalization.yaml` |
| [P06](Phase1/P06/Challenge.lean) | Critical sets, queries, width and backdoors | 14 + 1 | `entries/P06/comparator.json` | `entries/P06/formalization.yaml` |
| [P07](Phase1/P07/Challenge.lean) | Bounded conjunction and proper bases | 11 + 4 | `entries/P07/comparator.json` | `entries/P07/formalization.yaml` |
| [P08](Phase1/P08/Challenge.lean) | Observation projection and typed certificates | 11 + 0 | `entries/P08/comparator.json` | `entries/P08/formalization.yaml` |
| [P09](Phase1/P09/Challenge.lean) | Ordinary resolution and wrappers | 9 + 4 | `entries/P09/comparator.json` | `entries/P09/formalization.yaml` |
| [P10](Phase1/P10/Challenge.lean) | Encoded simulation and reduction composition | 6 + 4 | `entries/P10/comparator.json` | `entries/P10/formalization.yaml` |

## Submission selection

Use a full, reviewed public commit SHA for each submission. For a new entry,
leave **Existing Palomar ID** blank. The registered ID of another entry is not
the target of a new selection. The author performs authentication, submission
and registration. Each selection receives its own verification and review.

The Comparator and metadata paths must both match the selected entry. In the
submission form, expand **File layout** and explicitly enter the metadata path
from the table. Leave **Project directory** blank. With a blank metadata field,
Palomar uses the root `formalization.yaml`, which describes P01 even when another
Comparator is selected. For P02 the pair is `entries/P02/comparator.json` and
`entries/P02/formalization.yaml`. Confirm that the **Registry preview** matches the selected metadata
file's `project.description` before submitting. The preview source label may
still say `formalization.yaml`; check the actual metadata-path field as well.

The detector and enumeration results use the literal, charged native execution
model and supplied decoder evidence. The machine bridge supplies conventional
encoded executions under its stated constructor and resource premises; those
premises remain part of every corresponding theorem. The width obstruction
uses the displayed graph expansion and degree assumptions. Proper-basis
execution does not assert the full-basis hardness classification. Certificate
recovery uses typed payloads and the displayed explicit grammar and checkers.
The selected forest weight theorem bounds feasible true-set weights by a returned
candidate score; it does not certify a maximum-weight physical test.
Resolution claims concern ordinary resolution and the stated inference or
literal-storage measures.

K01 encoded-language membership and the remaining whole-paper tranche are
outside these selections. The selected theorem map does not cover every numbered manuscript statement.

The project overview and all ten selections are described in
[the project README](README.md).
[Source provenance](SOURCE_PROVENANCE.md) records the manuscript identity,
authorship, AI assistance and per-file extraction identities.
