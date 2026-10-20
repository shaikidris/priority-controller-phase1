/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ResolvedNativeLayoutShape
import Controller.Cost.ResolvedRowsConstruction
import Controller.Cost.ForestDirectoryConstruction

/-! Native layout metadata is constructed once from source rows and cached
normalization counts. No healthy values, satisfying assignment or normalized
clause stream is an input to the constructor. -/
namespace Controller.Cost.ResolvedNativeLayoutConstruction

open Controller Controller.Decoder Controller.Decoder.DAG Controller.CNF Controller.Cost
  Controller.Extensions

structure Data (ambient : Nat) where
  references : List (List (ForestZeroEmit.Reference ambient))
  protectedEnd : Nat
  scratchEnd : Nat
  nativeEnd : Nat

def references (base : Nat) : List (Clause (Fin ambient)) → List (List (ForestZeroEmit.Reference
  ambient)) × Nat
  | [] => ([], 1)
  | row :: rest =>
      let count := row.length
      let tail := references (base + count) rest
      (ResolvedResident.rowRefs base row :: tail.1, tail.2 + 32 * count + 16)

theorem references_image (base : Nat) (clauses : List (Clause (Fin ambient))) :
    (references base clauses).1 = ResolvedResident.refs base clauses := by
  induction clauses generalizing base with
  | nil => rfl
  | cons row rest ih => simp only [references, ResolvedResident.refs, ih]

theorem references_clock (base : Nat) (clauses : List (Clause (Fin ambient))) :
    (references base clauses).2 = 32 * clauses.flatten.length + 16 * clauses.length + 1 := by
  induction clauses generalizing base with
  | nil => simp [references]
  | cons row rest ih =>
      simp only [references, ih, List.flatten_cons, List.length_append, List.length_cons]
      omega


def build (graph : DAG n) (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount) : Data (n
  + graph.nodeCount) × Nat :=
  let source := ResolvedRowsConstruction.build graph b target reference
  let counted := ForestDirectoryConstruction.profile source.1
  let normalized := ResolvedSourceProfile.rows graph b
  let formed := references 2 source.1
  let keep := 2 + counted.2.1 + 2 * (n + graph.nodeCount)
  let scratch := keep + 7 + 2 * counted.1 + 2 * counted.2.1 + 2 * n
  let native := keep + 14 + 5 * counted.1 + 2 * counted.2.1 + 5 * n +
    5 * (n + graph.nodeCount) + 3 * normalized.1.sum
  (⟨formed.1, keep, scratch, native⟩,
    source.2 + counted.2.2 + normalized.2 + formed.2 + 16 * normalized.1.length + 1000)

theorem native_image (graph : DAG n) (b : Nat) (target : Channel n) (reference : Fin
  graph.nodeCount) :
    (build graph b target reference).1.nativeEnd = ResolvedNativeResident.templateBase graph b
      target reference width := by
  unfold ResolvedNativeResident.templateBase
  rw [ResolvedNativeLayoutShape.base]
  unfold build
  obtain ⟨rows, literals, _⟩ := ForestDirectoryConstruction.profile_exact
    (ResolvedResident.rows graph ∅ b target reference)
  simp only [rows, literals, ResolvedRowsConstruction.image,
    ResolvedResident.initial, ResolvedResident.sourceHeap_size]

theorem references_value (graph : DAG n) (b : Nat) (target : Channel n) (reference : Fin
  graph.nodeCount) :
    (build graph b target reference).1.references = ResolvedResident.refs 2 (ResolvedResident.rows
      graph ∅ b target reference) := by
  simp only [build, references_image, ResolvedRowsConstruction.image]

theorem keep_image (graph : DAG n) (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount)
  :
    (build graph b target reference).1.protectedEnd =
      (ResolvedResident.sourceHeap width n graph.nodeCount (ResolvedResident.rows graph ∅ b target
        reference)).size := by
  obtain ⟨_, literals, _⟩ := ForestDirectoryConstruction.profile_exact
    (ResolvedResident.rows graph ∅ b target reference)
  simp only [build, literals, ResolvedRowsConstruction.image, ResolvedResident.sourceHeap_size]

theorem scratch_image (graph : DAG n) (b : Nat) (target : Channel n) (reference : Fin
  graph.nodeCount) :
    (build graph b target reference).1.scratchEnd =
      ResolvedResident.scratchSize (build graph b target reference).1.protectedEnd n (n +
        graph.nodeCount)
        (ResolvedResident.rows graph ∅ b target reference) := by
  let dictionary := (ForestZeroCompile.compileRows (ForestZeroCompile.empty _)
    (SharedZeroTemplate.touchRows (n + graph.nodeCount))).1
  have covered := FullDictionaryProfile.covered dictionary
    (ForestZeroCompile.rows_dictionary _ (ForestZeroCompile.empty_coherent _) _).1
    SharedZeroDictionary.touch_rows_full n (by omega)
  have cardinal : dictionary.coordinates.size = n + graph.nodeCount := by
    simpa only [dictionary, List.append_nil] using
      SharedZeroDictionary.dictionary_size ([] : List (Clause (Fin (n + graph.nodeCount))))
  rw [cardinal] at covered
  obtain ⟨rows, literals, _⟩ := ForestDirectoryConstruction.profile_exact
    (ResolvedResident.rows graph ∅ b target reference)
  simp only [build, rows, literals, ResolvedRowsConstruction.image, ResolvedResident.scratchSize,
    EnumerationFixedResident.heapSize, ResolvedResident.refs_length, ResolvedResident.refs_literals,
    List.length_nil, Nat.add_zero]
  change _ = _ + (if (ForestZeroNonempty.search dictionary (n + graph.nodeCount + 1) n 0).reason =
    .covered then 2 * n else 0)
  rw [covered, if_pos rfl]
  omega

theorem clock (graph : DAG n) (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount) :
    (build graph b target reference).2 ≤ 10000 * (n + 1) * (graph.countedSize + 1) := by
  have source := ResolvedRowsConstruction.clock graph b target reference
  have normalized := ResolvedSourceProfile.rows_clock graph b
  have formed := references_clock 2 (ResolvedRowsConstruction.build graph b target reference).1
  obtain ⟨_, _, counted⟩ := ForestDirectoryConstruction.profile_exact
    (ResolvedRowsConstruction.build graph b target reference).1
  have length : (ResolvedSourceProfile.rows graph b).1.length =
      (ResolvedResident.rows graph ∅ b target reference).length := by
    rw [ResolvedSourceProfile.rows_value graph b target reference]
    simp only [SharedNormalizationShape.profile, List.length_map]
  have bounded := ResolvedResident.rows_bound graph ∅ b target reference
  have size := graph.countedSize_eq
  simp only [build]
  rw [counted, formed, length, ResolvedRowsConstruction.image]
  nlinarith

end Controller.Cost.ResolvedNativeLayoutConstruction
