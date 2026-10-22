# Observation wrappers, finite recovery and checked certificates

These statements concern SAT encodings of priority-controller fault detection.
An optional auxiliary wrapper must preserve the discrepancy tested by the
physical detector, and a recovered typed record must pass its complete checker.
The entry connects a declared wrapper family to that detector, constructs a
finite recovery run under the candidate promise, and exhibits a satisfiable
positive-output packet accepted by the full serialized interface.

The mathematical applications are structural SAT preprocessing and checked
solver interfaces for hardware fault diagnosis. The wrapper grammar, native
observed pairs and candidate promise are explicit. Candidate discovery,
arbitrary-CNF recognition, a general accepted-packet constructor and
machine-level construction-time bounds are separate questions.

The Comparator selects fourteen declarations. The following table identifies
the decisive argument for each; the full signatures specify all premises.

| Selected declaration | Proof mechanism |
| --- | --- |
| `ObservationProjection.observation_projection_of_unit_conflict` | An active observation guard forces a discrepancy. Conversely the extension-or-impossible-orientation premises provide an extension; the unit-conflict premise excludes an all-inactive model. |
| `ObservationProjection.optional_declared_cnf_projection` | Requirement-tree clauses force an active observed leaf. A discrepant leaf admits an extension with inactive internal activities and active ancestors; declared support restricts the auxiliary domain to the finite recorded coordinates. |
| `ObservationProjection.selected_declared_cnf_projection` | The selected-observation clause restricts the required discrepancy to the supplied list. The same extension argument handles any selected discrepant leaf; an empty selected list has no satisfying extension. |
| `IntendedDAG.recovery_exact` | Fresh ready steps have distinct outputs. The candidate promise excludes alternative producers, and rank induction turns saturation into coverage of every intended nonroot. This statement retains the supplied run and saturation premises. |
| `GuardedFamily.decodeChecked_sound` | Successful decoding supplies guardedness and all record checks. Checked aliases, roles, partitions, producer blocks, wrapper certificates and row entailments give the source-to-physical satisfiability equivalence. |
| `GuardedFamily.decodeChecked_lifting` | The checked record transports a native specification model through the private wrapper, coordinate partition and signed alias maps to a model of the original source rows. |
| `Pipeline.runFamily_sat_iff` | Under successful family acceptance, detector absence is equivalent to source unsatisfiability. A returned native detecting assignment lifts to a source model and passes the final model check. |
| `Pipeline.runFamily_certified_unsat` | Soundness of the supplied accepted refutation implies source unsatisfiability and detector absence. The pipeline then returns the checked UNSAT verdict. |
| `Pipeline.runFamily_sat_sound` | The SAT branch validates an assignment against the submitted original source. Its accepted model check supplies a satisfying assignment. |
| `Pipeline.runFamily_unsat_sound` | The UNSAT branch requires a refutation accepted by a sound certificate checker for the original source. Acceptance therefore excludes every source assignment. |
| `GuardedFamily.decodeChecked_requires_extra_coordinates` | Role and partition bijections give the native and private coordinate counts. Alias anchors inject recovered coordinates into the source. A recorded observation activity supplies a private coordinate, forcing strict inequality. |
| `ObservationDetection.optional_native_decision` | Native defining equations identify the detected bit with the disjunction of observed discrepancies. Optional-wrapper projection and guarded physical-detector correctness give the equivalence without a successful-recognition premise. |
| `RecoveryDriver.recover_exact` | The actual driver scans for a ready candidate and inserts its fresh output. Fuel equal to the number of nonroots suffices for saturation; exact recovery and the run cardinality invariant give full coverage and exact trace length. No run or saturation witness is supplied. |
| `exists_accepted_positive_output` | Explicit native rows, ranks, producer blocks, aliases and certificate traces pass the existing full checker. Serialization round trips yield accepted decoding. A physical detecting input lifts to an original-source model and a SAT verdict. |

The last witness has two channels, one bus, one observed output, 35 native
coordinates, one private activity and 91 source rows. Ordinary-resolution
traces validate identity row cuts; LRAT traces validate wrapper and target
entailments. Both are certificate data checked by the existing backends.

The manuscript source and the precise distinction between its statements and
these implementation refinements are recorded in
[formalization.yaml](formalization.yaml). The authoritative selection is
[comparator.json](comparator.json), with explicit statement definitions in
[Challenge.lean](../../Phase1/P08/Challenge.lean) and proofs imported by
[Solution.lean](../../Phase1/P08/Solution.lean).
