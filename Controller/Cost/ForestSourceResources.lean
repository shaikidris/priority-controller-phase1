/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ForestSourceOptimal

/-! Construction-operation accounting for the complete source-only forest
image. Weight arithmetic and its encoded storage are separate. The stage
clock includes original packet formation, the fetched classification pass,
source validation/caching, the executed selector, all instruction formation
and relocation, clause production, and program materialization. -/
namespace Controller.Cost.ForestSourceResources

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.ForestRootProjection Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestCursorAllRoots
open Controller.Cost.ForestCursorDescriptors

variable {n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- Fixed control/record operations are charged separately from generic weight
addition, subtraction and comparison. Source list scans use their own clocks. -/
def preparationWork (width channels : Nat) (rows : List Row) (roots : List Nat) : Nat :=
  (ForestSourceConstruction.items channels 0 rows).2 + rows.length +
    (rowChildren rows).length + (rowGuards rows).length + 10 * rows.length +
    20 * (channels + rows.length + (rowChildren rows).length + (rowGuards rows).length + roots.length + 1) +
    ForestRootClassification.constructionWork width channels +
    97 * (channels + rows.length + (rowChildren rows).length + (rowGuards rows).length + roots.length) + 37 +
    6 * roots.length + 1 + 64 * (14 * (roots.length + (rowChildren rows).length + (rowGuards rows).length) + 1) +
    16 * channels + 100

def preludeWork (width channels : Nat) : Nat :=
  UniformSourceConstruction.work width channels + 1340 + 12 * (159 + 2 * channels) + 500

def assembleWork (width : Nat) (rows : List Row) (roots : List Nat)
    (prepared : ForestSourceDriver.Prepared n W) (b : Nat) (target : Channel n) : Nat :=
  let prior := ForestSourceImage.prelude width n rows roots prepared.offsets
  let positive := ForestPreparedPositive.form prior rows.length prepared.offsets.children prepared.offsets.guards
    prepared.positiveRoots.length prepared.selected.data
  let allocated := 5 + 6 * rows.length + prepared.offsets.children + prepared.offsets.guards + prepared.positiveRoots.length
  preparationWork width n rows roots + preludeWork width n +
    ForestPreparedPositive.constructionWork prior prepared.selected.data +
    ForestPreparedNegative.constructionWork positive rows.length allocated prepared.table prepared.offsets prepared.negativeRoots b target

def constructionWork (width : Nat) (rows : List Row) (roots : List Nat)
    (weights : Channel n → W) (b : Nat) (target : Channel n) : Nat :=
  assembleWork width rows roots (ForestSourceDriver.prepare width rows roots weights b target) b target

omit [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W] in
theorem preparation_bound (width channels : Nat) (rows : List Row) (roots : List Nat) :
    preparationWork width channels rows roots ≤ 10000 *
      (channels + rows.length + (rowChildren rows).length + (rowGuards rows).length + roots.length + 1) := by
  have source := ForestSourceConstruction.items_work channels 0 rows
  have classifier := ForestRootClassification.construction_bound width channels
  unfold preparationWork
  omega

omit [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W] in
theorem prelude_bound (width channels : Nat) : preludeWork width channels ≤ 10000 + 48 * channels := by
  have code := UniformSourceConstruction.work_bound width channels
  unfold preludeWork
  omega

/-- The complete source-only image constructor has a linear operation clock
on formula forests. This is distinct from its fetched execution clock and
from a bound on binary weight arithmetic. -/
theorem construction_bound (graph : DAG n) (forest : graph.FormulaForest) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (weights : Channel n → W) (b : Nat) (target : Channel n)
    (width : Nat) (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (countFits : (buildRoots (healthyGraph graph target false)).count < 2 ^ width)
    (positionFits : ∀ record ∈ (buildRoots (healthyGraph graph target false)).entries, record.position < 2 ^ width) :
    constructionWork width rows roots weights b target ≤ 200000 * (graph.countedSize + 1) := by
  let cache := ForestCompilerOffsets.run rows ForestCompilerOffsets.initial
  let pg := healthyGraph graph target false
  let ng := healthyGraph graph target true
  let prior := ForestSourceImage.prelude width n rows roots cache
  let selected := (runAll (source n rows) weights b target (healthyRootIds graph target false)).2
  let positive := ForestPreparedPositive.form prior rows.length cache.children cache.guards
    (healthyRootIds graph target false).length selected
  let allocated := 5 + 6 * rows.length + cache.children + cache.guards + (healthyRootIds graph target false).length
  have offsets := ForestCompilerOffsets.run_totals rows ForestCompilerOffsets.initial
  have childCount : cache.children = (rowChildren rows).length := by
    simpa only [cache, ForestCompilerOffsets.initial, Nat.zero_add] using offsets.1
  have guardCount : cache.guards = (rowGuards rows).length := by
    simpa only [cache, ForestCompilerOffsets.initial, Nat.zero_add] using offsets.2.1
  have pRows : RowsMatch pg rows := Forest.rootFamily_rows graph _ rows matched
  have pRoots : RootsMatch pg (healthyRootIds graph target false) := Forest.rootFamily_rootIds graph _
  have nRows : RowsMatch ng rows := Forest.rootFamily_rows graph _ rows matched
  have nRoots : RootsMatch ng (healthyRootIds graph target true) := Forest.rootFamily_rootIds graph _
  have pForest : pg.FormulaForest := Forest.rootFamily_forest graph forest _ (Forest.healthyPositions_nodup graph target false)
  have nForest : ng.FormulaForest := Forest.rootFamily_forest graph forest _ (Forest.healthyPositions_nodup graph target true)
  have desc : selected.descriptors = buildRoots pg := runAll_descriptors pg rows _ pRows pRoots weights b target
  have entries : selected.descriptors.entries.length = (buildRoots pg).count := by rw [desc]; exact (buildRoots_valid pg).count
  have descriptors := actual_descriptor_count_bound pg pForest
  have pSize : pg.countedSize ≤ graph.countedSize := Forest.healthyFamily_countedSize_le graph target false
  have nSize : ng.countedSize ≤ graph.countedSize := Forest.healthyFamily_countedSize_le graph target true
  have positiveImage : positive = mixedPositiveProgram prior pg rows (healthyRootIds graph target false)
      weights b target countFits positionFits := by
    dsimp only [positive]
    rw [childCount, guardCount]
    exact ForestPreparedPositive.form_image prior pg rows _ pRows pRoots weights b target countFits positionFits
  have priorSize : prior.size = 304 + 2 * n := by
    dsimp only [prior, cache]
    rw [ForestSourceImage.prelude_image width graph rows roots (assignmentOfSet {target}), packetPrelude_size, classificationPrior_size]
    omega
  have positiveSize := mixed_positive_size_bound prior pg rows _ pRows pRoots weights b target countFits positionFits
  rw [← positiveImage] at positiveSize
  have positiveCost := ForestPreparedPositive.work_bound prior selected
  rw [entries] at positiveCost
  have negativeCost := ForestPreparedNegative.forest_work positive allocated
    ng rows (healthyRootIds graph target true) nRows nRoots nForest b target
  have preparation := preparation_bound width n rows roots
  have prelude := prelude_bound width n
  have incidence := matched_incidence_lengths graph rows matched
  have rootsLength : roots.length = graph.roots.length := by rw [rootMatches, List.length_map]
  have pCounts := Forest.rootFamily_incidence_counts graph (Forest.healthyPositions graph target false)
  have pRootBound := Forest.healthyPositions_length_le graph target false
  change pg.nodeCount = _ ∧ pg.childIncidences = _ ∧ pg.guardIncidences = _ ∧ pg.roots.length = _ at pCounts
  rw [pCounts.2.1, pCounts.2.2.1, pCounts.2.2.2] at descriptors
  rw [constructionWork, ForestSourceImage.prepared_image graph forest rows roots matched heads rootMatches weights b target width capacity]
  dsimp only [assembleWork]
  change preparationWork width n rows roots + preludeWork width n +
    ForestPreparedPositive.constructionWork prior selected +
      ForestPreparedNegative.constructionWork positive rows.length allocated
        (source n rows) cache (healthyRootIds graph target true) b target ≤ _
  have rowCount : rows.length = ng.nodeCount := matched.length_eq
  rw [rowCount]
  rw [matched.length_eq, incidence.1, incidence.2, rootsLength] at preparation
  have size := graph.countedSize_eq
  dsimp only [cache] at negativeCost ⊢
  omega

end Controller.Cost.ForestSourceResources
