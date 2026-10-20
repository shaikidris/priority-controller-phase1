module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ForestQueryPackets
public import Controller.Cost.ForestReferenceStorage

@[expose] public section


/-! Newly formed storage for all source query packets, including cone records,
root/target units, outer-list copies and recursive packet continuations. -/
namespace Controller.Cost.ForestQueryPacketStorage

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestWeightedIndexed
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroSource

variable {n nodes : Nat}

def allocated (table : Source n) (cache : ForestCompilerOffsets.State)
    (roots : List (Fin nodes)) (b : Nat) (target : Channel n) : Nat :=
  let targetCell := ForestCompilerOffsets.rootSlot cache roots.length
  (roots.zipIdx.map fun item =>
    ForestReferenceStorage.allocated table cache item.1
      (nodeReference (ForestCompilerOffsets.rootSlot cache item.2) item.1 false) +
      8 * (ForestQueryPackets.one table cache targetCell item.2 item.1 b target).1.length + 100).sum + 32

private theorem sum_le (values : List α) (f g : α → Nat) (bound : ∀ value ∈ values, f value ≤ g value) :
    (values.map f).sum ≤ (values.map g).sum := by
  induction values with
  | nil => simp
  | cons value rest ih =>
      have head := bound value List.mem_cons_self
      have tail := ih (fun value member => bound value (List.mem_cons_of_mem _ member))
      simp only [List.map_cons, List.sum_cons]
      omega

private theorem sum_split (values : List α) (f g : α → Nat) :
    (values.map fun value => f value + 8 * g value + 100).sum =
      (values.map f).sum + 8 * (values.map g).sum + 100 * values.length := by
  induction values with
  | nil => simp
  | cons value rest ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons, Nat.mul_add]; omega

theorem bound (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots)
    (forest : graph.FormulaForest) (b : Nat) (target : Channel n) :
    allocated (source n rows) (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial) graph.roots b target ≤
      5000 * (graph.countedSize + 1) := by
  let table := source n rows
  let cache := ForestCompilerOffsets.run rows ForestCompilerOffsets.initial
  let targetCell := ForestCompilerOffsets.rootSlot cache graph.roots.length
  have perRoot := sum_le graph.roots.zipIdx
    (fun item => ForestReferenceStorage.allocated table cache item.1
      (nodeReference (ForestCompilerOffsets.rootSlot cache item.2) item.1 false))
    (fun item => 16 * ForestReferenceWork.budget table item.1)
    (fun item _ => ForestReferenceStorage.allocation_bound table cache item.1 _)
  have indexed := congrArg (List.map (fun root => 16 * ForestReferenceWork.budget table root))
    (List.zipIdx_map_fst 0 graph.roots)
  simp only [List.map_map, Function.comp_def] at indexed
  rw [indexed] at perRoot
  have scaled : (graph.roots.map fun root => 16 * ForestReferenceWork.budget table root).sum =
      16 * (graph.roots.map (ForestReferenceWork.budget table)).sum := by
    induction graph.roots with
    | nil => simp
    | cons root rest ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]
  rw [scaled] at perRoot
  have clauseCounts : (graph.roots.zipIdx.map fun item =>
      (ForestQueryPackets.one table cache targetCell item.2 item.1 b target).1.length) =
      (ForestQueryPackets.queries table cache graph.roots b target).1.map List.length := by
    have claim : ∀ (values : List (Fin graph.nodeCount)) position,
        (values.zipIdx position |>.map fun item =>
          (ForestQueryPackets.one table cache targetCell item.2 item.1 b target).1.length) =
        (ForestQueryPackets.buildFrom table cache targetCell b target position values).1.map List.length := by
      intro values
      induction values with
      | nil => intro position; rfl
      | cons root rest ih =>
          intro position
          simp only [List.zipIdx_cons, List.map_cons, ForestQueryPackets.buildFrom, ih]
    exact claim graph.roots 0
  have rowBound := (ForestZeroSourcePlan.zero_queries_forest_bounds (width := width) graph rows roots matched b target forest).1
  rw [← ForestCachedQueries.queries_eq width graph rows roots matched rootMatches b target,
    ← ForestQueryPackets.image] at rowBound
  change ((ForestQueryPackets.queries table cache graph.roots b target).1.map List.length).sum ≤ _ at rowBound
  have traversal := ForestReferenceWork.roots_bound graph rows matched forest
  dsimp only [allocated]
  rw [sum_split, List.length_zipIdx]
  change (graph.roots.zipIdx.map fun item => ForestReferenceStorage.allocated table cache item.1
      (nodeReference (ForestCompilerOffsets.rootSlot cache item.2) item.1 false)).sum +
      8 * (graph.roots.zipIdx.map fun item => (ForestQueryPackets.one table cache targetCell item.2 item.1 b target).1.length).sum +
      100 * graph.roots.length + 32 ≤ _
  rw [clauseCounts, DAG.countedSize_eq]
  dsimp only [table] at perRoot rowBound ⊢
  omega

end Controller.Cost.ForestQueryPacketStorage
