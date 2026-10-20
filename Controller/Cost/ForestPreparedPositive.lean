module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ForestPositiveConstruction
public import Controller.Cost.ForestFixedControlRecipes

@[expose] public section


/-! Positive image assembly from the executed selector state and scalar source
counts. Graphs and the recursive selector occur only in refinement theorems. -/
namespace Controller.Cost.ForestPreparedPositive

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.WordConstructionRecipe Controller.Cost.ForestConstructionRecipes
open Controller.Cost.ForestRootProjection Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestCursorAllRoots
open Controller.Cost.ForestWeightedTagged Controller.Cost.ForestCursorDescriptors

variable {n : Nat} {W : Type}

def front (prior : Program width 8) (failure : Nat) (selected : Option (Candidate W)) : Program width 8 :=
  prior ++ (evaluate (fun i : Fin 0 => [].getD i.val 0)
    (mixedMaskCode.constructionRecipe width)).toArray ++ #[.constant 3 (word width 0)] ++
    (evaluate (fun i => [failure, if selected.isSome then 1 else 0].getD i.val 0)
      (ForestFixedControlRecipes.selector.constructionRecipe width)).toArray

def form (prior : Program width 8) (nodes children guards rootCount : Nat)
    (computed : ForestWeightedIndexed.State n W) : Program width 8 :=
  match computed.selected with
  | none => front prior (prior.size + 5) computed.selected
  | some candidate =>
      let items := ForestPositiveConstruction.form width 5 nodes children guards rootCount
        (prior.size + 5) 0 computed candidate
      let endAt := prior.size + 5 + items.length
      let allocated := 5 + 6 * nodes + children + guards + rootCount +
        2 * computed.descriptors.count + (n + 3)
      let cleanup := evaluate (fun i => [endAt, allocated, 5 + 6 * nodes + children + guards].getD i.val 0)
        (positiveTargetCleanupCode.constructionRecipe width)
      (items.map RegisterWiden.widenInstruction).toArrayAux
        (front prior (endAt + 14) computed.selected) ++ cleanup.toArray

variable [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

omit [IsOrderedAddMonoid W] in
theorem prefix_image (prior : Program width 8) (failure : Nat) (rows : List Row) (roots : List Nat)
    (weights : Channel n → W) (b : Nat) (target : Channel n) :
    front prior failure (runAll (source n rows) weights b target roots).2.selected =
      mixedBranchPrefix prior failure rows roots weights b target := by
  simp only [front, mixedMaskCode.constructionRecipe_eq, ForestFixedControlRecipes.selector.constructionRecipe_eq,
    mixedBranchPrefix, mixedSelectorCode, ForestFixedControlRecipes.selector]
  cases (runAll (source n rows) weights b target roots).2.selected.isSome <;> rfl

/-- Every descriptor, candidate and branch flag is read from `computed`.
The theorem identifies that actual output with the existing weighted resident. -/
theorem form_image (prior : Program width 8) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots)
    (weights : Channel n → W) (b : Nat) (target : Channel n)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ record ∈ (buildRoots graph).entries, record.position < 2 ^ width) :
    form prior rows.length (rowChildren rows).length (rowGuards rows).length roots.length
      (runAll (source n rows) weights b target roots).2 =
      mixedPositiveProgram prior graph rows roots weights b target countFits positionFits := by
  have descriptors := runAll_descriptors graph rows roots matched rootMatches weights b target
  have itemImage := ForestPositiveConstruction.form_image width
    (UniformDAGRun.packetHeaderHeap width n rows roots) graph rows roots
    (runAll (source n rows) weights b target roots).2
  have header : (UniformDAGRun.packetHeaderHeap width n rows roots).size = 5 := rfl
  simp only [header] at itemImage
  dsimp only [form, mixedPositiveProgram]
  simp only [prefix_image]
  cases selected : (runAll (source n rows) weights b target roots).2.selected with
  | none => rfl
  | some candidate =>
      dsimp only
      rw [itemImage candidate descriptors countFits positionFits]
      simp only [positiveTargetCleanupCode.constructionRecipe_eq, descriptors,
        sourceAllocatedCells, sourcePrefixCells, weightedResident]

/-- This charge includes fixed operand formation, descriptor generation,
instruction widening, append copies and final materialization. -/
def constructionWork (prior : Program width 8) (computed : ForestWeightedIndexed.State n W) : Nat :=
  match computed.selected with
  | none => 500 + 4 * prior.size
  | some candidate => ForestPositiveConstruction.constructionWork width computed candidate +
      4000 + 4 * prior.size + 20 * computed.descriptors.entries.length + 20 * n

omit [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W] in
theorem work_bound (prior : Program width 8) (computed : ForestWeightedIndexed.State n W) :
    constructionWork prior computed ≤ 6000 + 4 * prior.size +
      140 * computed.descriptors.entries.length + 68 * n := by
  unfold constructionWork
  split
  · omega
  · rename_i candidate selected
    have charged := ForestPositiveConstruction.work_bound width computed candidate
    omega

end Controller.Cost.ForestPreparedPositive
