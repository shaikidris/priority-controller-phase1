/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ForestSourceDriver
import Controller.Cost.ForestPreparedPositive
import Controller.Cost.ForestPreparedNegative

/-! The complete forest instruction image is constructed from original source
rows, original roots, weights and the physical target. Its data path executes
classification and selection, then forms both resident branches. -/
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

namespace Controller.Cost.ForestSourceImage

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.WordConstructionRecipe Controller.Cost.ForestConstructionRecipes
open Controller.Cost.ForestRootProjection Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestCursorAllRoots
open Controller.Cost.ForestCursorDescriptors

variable {n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

def prelude (width channels : Nat) (rows : List Row) (roots : List Nat)
    (offsets : ForestCompilerOffsets.State) : Program width 8 :=
  let low := UniformSourceConstruction.code width channels rows.length offsets.children offsets.guards roots.length
  let prior := (low.map RegisterWiden.widenInstruction).toArray
  (evaluate (fun i => [prior.size].getD i.val 0)
    (ForestConstructionRecipes.packetPrelude.constructionRecipe width)).toArrayAux prior

def assemble (width : Nat) (rows : List Row) (roots : List Nat)
    (prepared : ForestSourceDriver.Prepared n W) (b : Nat) (target : Channel n) : Program width 8 :=
  let prior := prelude width n rows roots prepared.offsets
  let positive := ForestPreparedPositive.form prior rows.length prepared.offsets.children prepared.offsets.guards
    prepared.positiveRoots.length prepared.selected.data
  let allocated := 5 + 6 * rows.length + prepared.offsets.children + prepared.offsets.guards + prepared.positiveRoots.length
  ForestPreparedNegative.form positive rows.length allocated prepared.table prepared.offsets prepared.negativeRoots b target

def build (width : Nat) (rows : List Row) (roots : List Nat)
    (weights : Channel n → W) (b : Nat) (target : Channel n) : Program width 8 :=
  assemble width rows roots (ForestSourceDriver.prepare width rows roots weights b target) b target

omit [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W] in
private theorem prepared_ext (first second : ForestSourceDriver.Prepared n W)
    (table : first.table = second.table) (cache : first.offsets = second.offsets)
    (positive : first.positiveRoots = second.positiveRoots) (negative : first.negativeRoots = second.negativeRoots)
    (selected : first.selected = second.selected) : first = second := by
  cases first
  cases second
  cases table
  cases cache
  cases positive
  cases negative
  cases selected
  rfl

theorem prelude_image (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (values : Channel n → Bool) :
    prelude width n rows roots (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial) =
      packetPrelude (classificationPrior width graph rows roots values) := by
  have offsets := ForestCompilerOffsets.run_totals rows ForestCompilerOffsets.initial
  have childCount : (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial).children =
      (rowChildren rows).length := by
    simpa only [ForestCompilerOffsets.initial, Nat.zero_add] using offsets.1
  have guardCount : (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial).guards =
      (rowGuards rows).length := by
    simpa only [ForestCompilerOffsets.initial, Nat.zero_add] using offsets.2.1
  have low := UniformSourceConstruction.code_image width rows roots values
  unfold prelude
  rw [childCount, guardCount, low]
  simp only [ForestConstructionRecipes.packetPrelude.constructionRecipe_eq,
    ForestConstructionRecipes.packetPrelude, ForestRootProjection.packetPrelude, ForestZeroResident.materialize, classificationPrior,
    UniformDAGResources.program, RegisterWiden.widenProgram, List.map_toArray]

/-- The executed preprocessing result has the exact source, cache and selected
state used by the image assembly. The equation is a specification theorem. -/
theorem prepared_image (graph : DAG n) (forest : graph.FormulaForest) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (weights : Channel n → W) (b : Nat) (target : Channel n)
    (width : Nat) (capacity : 256 * (graph.countedSize + 1) < 2 ^ width) :
    ForestSourceDriver.prepare width rows roots weights b target =
      ⟨source n rows, ForestCompilerOffsets.run rows ForestCompilerOffsets.initial,
        healthyRootIds graph target false, healthyRootIds graph target true,
        ⟨(runAll (source n rows) weights b target (healthyRootIds graph target false)).2, []⟩⟩ := by
  have result := ForestSourceDriver.prepare_correct graph forest rows roots matched heads rootMatches weights b target width capacity
  exact prepared_ext _ _ result.1 rfl result.2.1 result.2.2.1 result.2.2.2

/-- Exact-image connection for the entire source-driven constructor. Healthy
families, candidate descriptors and query packets appear only on the semantic
right-hand side; none is an argument to `build`. -/
theorem build_image (graph : DAG n) (forest : graph.FormulaForest) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (weights : Channel n → W) (b : Nat) (target : Channel n)
    (width : Nat) (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (countFits : (buildRoots (healthyGraph graph target false)).count < 2 ^ width)
    (positionFits : ∀ record ∈ (buildRoots (healthyGraph graph target false)).entries, record.position < 2 ^ width) :
    build width rows roots weights b target =
      mixedResident (packetPrelude (classificationPrior width graph rows roots (assignmentOfSet {target})))
        (healthyGraph graph target false) (healthyGraph graph target true) rows
        (healthyRootIds graph target false) (healthyRootIds graph target true)
        (Forest.rootFamily_rows graph (Forest.healthyPositions graph target true) rows matched)
        weights b target countFits positionFits := by
  have prepared := ForestSourceDriver.prepare_correct graph forest rows roots matched heads rootMatches weights b target width capacity
  have inputImage : ForestSourceDriver.prepare width rows roots weights b target =
      ⟨source n rows, ForestCompilerOffsets.run rows ForestCompilerOffsets.initial,
        healthyRootIds graph target false, healthyRootIds graph target true,
        ⟨(runAll (source n rows) weights b target (healthyRootIds graph target false)).2, []⟩⟩ := by
    exact prepared_ext _ _ prepared.1 rfl prepared.2.1 prepared.2.2.1 prepared.2.2.2
  have offsets := ForestCompilerOffsets.run_totals rows ForestCompilerOffsets.initial
  have childCount : (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial).children =
      (rowChildren rows).length := by
    simpa only [ForestCompilerOffsets.initial, Nat.zero_add] using offsets.1
  have guardCount : (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial).guards =
      (rowGuards rows).length := by
    simpa only [ForestCompilerOffsets.initial, Nat.zero_add] using offsets.2.1
  have positiveImage := ForestPreparedPositive.form_image
    (packetPrelude (classificationPrior width graph rows roots (assignmentOfSet {target})))
    (healthyGraph graph target false) rows (healthyRootIds graph target false)
    (Forest.rootFamily_rows graph (Forest.healthyPositions graph target false) rows matched)
    (Forest.rootFamily_rootIds graph (Forest.healthyPositions graph target false)) weights b target countFits positionFits
  have negativeImage := ForestPreparedNegative.form_image
    (mixedPositiveProgram (packetPrelude (classificationPrior width graph rows roots (assignmentOfSet {target})))
      (healthyGraph graph target false) rows (healthyRootIds graph target false) weights b target countFits positionFits)
    (sourcePrefixCells rows + (healthyRootIds graph target false).length)
    (healthyGraph graph target true) rows (healthyRootIds graph target true)
    (Forest.rootFamily_rows graph (Forest.healthyPositions graph target true) rows matched)
    (Forest.rootFamily_rootIds graph (Forest.healthyPositions graph target true)) b target
  rw [build, inputImage]
  dsimp only [assemble]
  rw [prelude_image width graph rows roots (assignmentOfSet {target}), childCount, guardCount, positiveImage]
  change ForestPreparedNegative.form _ rows.length (sourcePrefixCells rows + (healthyRootIds graph target false).length)
    (source n rows) (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial) _ _ _ = _
  rw [matched.length_eq]
  exact negativeImage

end Controller.Cost.ForestSourceImage
