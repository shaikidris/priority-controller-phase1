module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ForestRootClassification
public import Controller.Cost.ForestSourceConstruction
public import Controller.Cost.ForestCompilerOffsets
public import Controller.Cost.ForestSelectionMachine

@[expose] public section


/-! Source-only preprocessing for the complete forest constructor. Root
families are computed by the fetched classifier; the weighted selector is
executed from those returned roots with an original-source fuel budget. -/
namespace Controller.Cost.ForestSourceDriver

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGRun
open Controller.Cost.ForestRootProjection Controller.Cost.ForestWeightedIndexed

variable {n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

structure Prepared (n : Nat) (W : Type) where
  table : Source n
  offsets : ForestCompilerOffsets.State
  positiveRoots : List Nat
  negativeRoots : List Nat
  selected : ForestSelectionMachine.Configuration n W

/-- Only source data, weights and the physical target are arguments. In
particular neither the healthy families nor a selected answer is supplied. -/
def prepare (width : Nat) (rows : List Row) (roots : List Nat)
    (weights : Channel n → W) (b : Nat) (target : Channel n) : Prepared n W :=
  let offsets := ForestCompilerOffsets.run rows ForestCompilerOffsets.initial
  let table := (ForestSourceConstruction.items n 0 rows).1.toArray
  let flags := ForestRootClassification.classify width n rows.length offsets.children offsets.guards roots.length roots
    ((ForestCounter.counterState (#[] : Array (Word width)) 0 (word width 0) (word width 0) (word width 0)).frame
      ((inputPacket n 0 rows roots).map (word width) ++
        List.ofFn (fun i => boolWord width (assignmentOfSet {target} i)) ++ []) [])
  let fuel := 14 * (roots.length + offsets.children + offsets.guards) + 1
  let selected := ForestSelectionMachine.run table weights (ForestSelectionMachine.totalWeight weights) b target fuel
    (ForestSelectionMachine.initial flags.1)
  ⟨table, offsets, flags.1, flags.2.1, selected⟩

theorem prepare_correct (graph : DAG n) (forest : graph.FormulaForest)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched) (rootsMatch : RootsMatch graph roots)
    (weights : Channel n → W) (b : Nat) (target : Channel n) (width : Nat)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width) :
    let result := prepare width rows roots weights b target
    result.table = source n rows ∧ result.positiveRoots = healthyRootIds graph target false ∧
      result.negativeRoots = healthyRootIds graph target true ∧
      result.selected = ⟨(runAll (source n rows) weights b target (healthyRootIds graph target false)).2, []⟩ := by
  have classifier := ForestRootClassification.classify_correct graph rows roots matched heads rootsMatch target width capacity
  have sourceImage := (ForestSourceConstruction.source_preparation n rows).1
  have offsets := ForestCompilerOffsets.run_totals rows ForestCompilerOffsets.initial
  have childCount : (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial).children =
      (rowChildren rows).length := by
    simpa only [ForestCompilerOffsets.initial, Nat.zero_add] using offsets.1
  have guardCount : (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial).guards =
      (rowGuards rows).length := by
    simpa only [ForestCompilerOffsets.initial, Nat.zero_add] using offsets.2.1
  let positiveGraph := healthyGraph graph target false
  have positiveForest : positiveGraph.FormulaForest := Forest.rootFamily_forest graph forest
    (Forest.healthyPositions graph target false) (Forest.healthyPositions_nodup graph target false)
  have positiveRows : RowsMatch positiveGraph rows := Forest.rootFamily_rows graph _ rows matched
  have positiveRoots : RootsMatch positiveGraph (healthyRootIds graph target false) :=
    Forest.rootFamily_rootIds graph (Forest.healthyPositions graph target false)
  obtain ⟨ticks, trace, bound⟩ :=
    (ForestSelectionMachine.linear_execution positiveGraph positiveForest rows
      (healthyRootIds graph target false) positiveRows positiveRoots weights b target).1
  have counts := Forest.rootFamily_incidence_counts graph (Forest.healthyPositions graph target false)
  have rootBound := Forest.healthyPositions_length_le graph target false
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have rootLength : roots.length = graph.roots.length := by rw [rootsMatch, List.length_map]
  have fuel : ticks ≤ 14 * (roots.length + (rowChildren rows).length + (rowGuards rows).length) + 1 := by
    unfold ForestSelectionMachine.fuelBound at bound
    change ticks ≤ 14 * (positiveGraph.roots.length + positiveGraph.childIncidences + positiveGraph.guardIncidences) + 1 at bound
    change positiveGraph.nodeCount = _ ∧ positiveGraph.childIncidences = _ ∧ positiveGraph.guardIncidences = _ ∧
      positiveGraph.roots.length = _ at counts
    rw [counts.2.1, counts.2.2.1, counts.2.2.2] at bound
    omega
  have actual := trace.run_of_le rfl _ fuel
  dsimp only [prepare]
  rw [childCount, guardCount, sourceImage, classifier]
  exact ⟨rfl, rfl, rfl, actual⟩

end Controller.Cost.ForestSourceDriver
