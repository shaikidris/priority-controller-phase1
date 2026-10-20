/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ForestSourceResources

/-! Retained program storage for the actual source-only forest constructor.
Program words count the generated instruction backing, separately from fetched
heap/stack/output storage and construction-stage scratch. -/
namespace Controller.Cost.ForestSourceStorage

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.ForestRootProjection Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestCursorAllRoots Controller.Cost.ForestCursorDescriptors

variable {n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

theorem program_bound (graph : DAG n) (forest : graph.FormulaForest) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (weights : Channel n → W) (b : Nat) (target : Channel n)
    (width : Nat) (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (countFits : (buildRoots (healthyGraph graph target false)).count < 2 ^ width)
    (positionFits : ∀ record ∈ (buildRoots (healthyGraph graph target false)).entries, record.position < 2 ^ width) :
    programWords (ForestSourceImage.build width rows roots weights b target) ≤ 4000 * (graph.countedSize + 1) := by
  let pg := healthyGraph graph target false
  let ng := healthyGraph graph target true
  have pForest : pg.FormulaForest := Forest.rootFamily_forest graph forest _ (Forest.healthyPositions_nodup graph target false)
  have nForest : ng.FormulaForest := Forest.rootFamily_forest graph forest _ (Forest.healthyPositions_nodup graph target true)
  have bound := mixed_resident_size_bound (classificationPrior width graph rows roots (assignmentOfSet {target}))
    pg ng rows (healthyRootIds graph target false) (healthyRootIds graph target true)
    (Forest.rootFamily_rows graph _ rows matched) (Forest.rootFamily_rootIds graph _)
    (Forest.rootFamily_rows graph _ rows matched) nForest weights b target countFits positionFits
  have desc := actual_descriptor_count_bound pg pForest
  have pCounts := Forest.rootFamily_incidence_counts graph (Forest.healthyPositions graph target false)
  have nCounts := Forest.rootFamily_incidence_counts graph (Forest.healthyPositions graph target true)
  have pRootBound := Forest.healthyPositions_length_le graph target false
  have nRootBound := Forest.healthyPositions_length_le graph target true
  change pg.nodeCount = _ ∧ pg.childIncidences = _ ∧ pg.guardIncidences = _ ∧ pg.roots.length = _ at pCounts
  change ng.nodeCount = _ ∧ ng.childIncidences = _ ∧ ng.guardIncidences = _ ∧ ng.roots.length = _ at nCounts
  rw [pCounts.2.1, pCounts.2.2.1, pCounts.2.2.2] at desc
  rw [classificationPrior_size, nCounts.2.1, nCounts.2.2.1, nCounts.2.2.2] at bound
  rw [ForestSourceImage.build_image graph forest rows roots matched heads rootMatches weights b target width capacity countFits positionFits]
  unfold programWords
  have size := graph.countedSize_eq
  change 4 * (mixedResident _ pg ng _ _ _ _ _ _ _ _ _).size ≤ _
  omega


/-- Retaining the actual generated instruction image does not change the
linear fetched-space bound. The physical optimum is supplied by
`ForestSourceOptimal.execution`, from which this resource projection follows. -/
theorem retained_execution (graph : DAG n) (forest : graph.FormulaForest)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched) (rootsMatch : RootsMatch graph roots)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : Nat) (bridge : Physical.Bridge n) (positive : 0 < b)
    (healthy : ∀ position : Fin graph.roots.length,
      graph.eval (assignmentOfSet {bridge.target}) (graph.roots.get position) = false)
    (detectable : Physical.BridgeDetectable (b := b) bridge true graph.observations)
    (rest output : List (Word (chosenMixedWidth graph)))
    (address loaded temporary : Word (chosenMixedWidth graph))
    (saved : Fin 8 → Word (chosenMixedWidth graph)) :
    ∃ final ticks peak,
      Execution (ForestSourceImage.build (chosenMixedWidth graph) rows roots weights b bridge.target)
        (classificationInitial (chosenMixedWidth graph) graph rows roots (assignmentOfSet {bridge.target})
          bridge.target rest output address loaded temporary saved) final ticks peak ∧
      final.halted = true ∧ ticks ≤ 1000 * (graph.countedSize + 1) ∧
      programWords (ForestSourceImage.build (chosenMixedWidth graph) rows roots weights b bridge.target) + peak ≤
        4200 * (graph.countedSize + 1) + rest.length + output.length := by
  obtain ⟨K, final, ticks, peak, trace, halted, accepted, legal, detects, heap, stack, emitted,
      optimal, time, space⟩ := ForestSourceOptimal.execution graph forest rows roots matched heads rootsMatch
    weights nonnegative b bridge positive healthy detectable rest output address loaded temporary saved
  have size : forestSize graph = graph.countedSize := by
    rw [DAG.countedSize_eq]
    unfold forestSize
    omega
  have room : 256 * (graph.countedSize + 1) < 2 ^ chosenMixedWidth graph := by
    have capacity := chosenMixedCapacity graph
    rw [size] at capacity
    omega
  have backing := program_bound graph forest rows roots matched heads rootsMatch weights b bridge.target _ room
    (original_descriptor_capacity graph forest bridge.target).1 (original_descriptor_capacity graph forest bridge.target).2
  rw [size] at time space
  exact ⟨final, ticks, peak, trace, halted, time, by omega⟩

end Controller.Cost.ForestSourceStorage
