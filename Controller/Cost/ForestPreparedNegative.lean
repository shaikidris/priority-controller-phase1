/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ForestStreamingConstruction
import Controller.Cost.ForestQueryPackets
import Controller.Cost.ForestSourceConstruction

/-! Negative image assembly from checked source roots and the shared source
cache. Both the root conversion and clause generation are executed; semantic
query packets are not constructor arguments. -/
namespace Controller.Cost.ForestPreparedNegative

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.WordConstructionRecipe Controller.Cost.ForestConstructionRecipes
open Controller.Cost.ForestRootProjection Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestZeroSourcePlan

variable {n : Nat}

def front (prior : Program width 8) (allocated : Nat) : Program width 8 :=
  let handoff := evaluate (fun i => [prior.size, allocated].getD i.val 0)
    (negativeHandoffCode.constructionRecipe width)
  let front := prior ++ handoff.toArray
  (evaluate (fun i => [front.size].getD i.val 0)
    (ForestFixedControlRecipes.cold.constructionRecipe width)).map
      RegisterWiden.widenInstruction |>.toArrayAux front

def form (prior : Program width 8) (nodes allocated : Nat)
    (table : Source n) (offsets : ForestCompilerOffsets.State)
    (roots : List Nat) (b : Nat) (target : Channel n) : Program width 8 :=
  let checked := (ForestSourceConstruction.ids nodes roots).1.getD []
  let packets := (ForestQueryPackets.queries table offsets checked b target).1
  let start := front prior allocated
  let protectedEnd := 6 + 6 * nodes + offsets.children + offsets.guards + roots.length + 2 * (n + nodes)
  ForestStreamingConstruction.compile protectedEnd n
    (ForestStreamingConstruction.initial (n + nodes) width start.size) packets start

theorem prefix_image (prior : Program width 8) (allocated : Nat) :
    front prior allocated = ForestZeroSourcePlan.coldPrefix (negativePrior prior allocated) := by
  simp only [front, negativeHandoffCode.constructionRecipe_eq,
    ForestFixedControlRecipes.cold.constructionRecipe_eq,
    ForestFixedControlRecipes.cold, ForestZeroSourcePlan.coldPrefix, negativePrior,
    ForestZeroResident.materialize]

theorem ids_of_fin (values : List (Fin nodes)) :
    (ForestSourceConstruction.ids nodes (values.map Fin.val)).1 = some values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp only [List.map_cons, ForestSourceConstruction.ids, dif_pos value.isLt, ih, Option.map_some]

theorem streaming_image (prior : Program width 8) (protectedEnd channels : Nat)
    (packets : List (List (List (ForestZeroEmit.Reference ambient)))) :
    ForestStreamingConstruction.compile protectedEnd channels
      (ForestStreamingConstruction.initial ambient width prior.size) packets prior =
      ForestCachedNegativeProgram.compile width protectedEnd channels prior packets := by
  apply Array.toList_inj.mp
  have same : (ForestStreamingConstruction.initial ambient width prior.size).marks =
      ForestCompilerMarks.compress (ForestCompilerDictionary.initial ambient) := rfl
  have contents := ForestStreamingConstruction.compile_contents protectedEnd channels
    (ForestStreamingConstruction.initial ambient width prior.size) (ForestCompilerDictionary.initial ambient)
    ForestCompilerDictionary.initial_valid same packets prior
  simpa only [ForestStreamingConstruction.initial, List.reverse_nil, List.flatten_nil, List.append_nil,
    ForestCachedNegativeProgram.compile, Array.toArrayAux_eq] using contents

/-- The shared-table streaming image agrees with the full physical negative
resident, including cold loading, all query relocations and the final halt. -/
theorem form_image (prior : Program width 8) (allocated : Nat) (graph : DAG n)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (rootMatches : RootsMatch graph roots) (b : Nat) (target : Channel n) :
    form prior graph.nodeCount allocated (source n rows)
      (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial) roots b target =
      negativeResident prior allocated graph rows roots matched b target := by
  have checked : (ForestSourceConstruction.ids graph.nodeCount roots).1 = some graph.roots := by
    rw [show roots = graph.roots.map Fin.val from rootMatches]
    exact ids_of_fin _
  have packets := ForestCachedQueries.queries_eq width graph rows roots matched rootMatches b target
  have counts := ForestCompilerOffsets.run_totals rows ForestCompilerOffsets.initial
  have childCount : (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial).children =
      (rowChildren rows).length := by
    simpa only [ForestCompilerOffsets.initial, Nat.zero_add] using counts.1
  have guardCount : (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial).guards =
      (rowGuards rows).length := by
    simpa only [ForestCompilerOffsets.initial, Nat.zero_add] using counts.2.1
  have incidence := matched_incidence_lengths graph rows matched
  have rootsLength : roots.length = graph.roots.length := by rw [rootMatches, List.length_map]
  have protectedEnd : 6 + 6 * graph.nodeCount +
      (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial).children +
      (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial).guards + roots.length + 2 * (n + graph.nodeCount) =
      (controlledHeap (width := width) graph rows roots target).size := by
    rw [childCount, guardCount, incidence.1, incidence.2, rootsLength,
      controlled_heap_size graph rows roots matched rootMatches target]
  dsimp only [form]
  rw [checked]
  dsimp only [Option.getD_some]
  rw [ForestQueryPackets.image, packets, streaming_image, protectedEnd, prefix_image,
    ForestCachedNegativeProgram.compile_eq _ (controlledLayout (width := width) graph rows roots target) n (Nat.le_add_right _ _)]
  rfl


/-- The charge follows the actual checked-root, clause and resident producers.
Fixed-kernel formation and prefix copies are included before the packet loop. -/
def constructionWork (prior : Program width 8) (nodes allocated : Nat)
    (table : Source n) (offsets : ForestCompilerOffsets.State)
    (roots : List Nat) (b : Nat) (target : Channel n) : Nat :=
  let checked := ForestSourceConstruction.ids nodes roots
  let packets := ForestQueryPackets.queries table offsets (checked.1.getD []) b target
  let start := front prior allocated
  let protectedEnd := 6 + 6 * nodes + offsets.children + offsets.guards + roots.length + 2 * (n + nodes)
  checked.2 + packets.2 + 5000 + 8 * prior.size +
    ForestStreamingConstruction.constructionWork protectedEnd n
      (ForestStreamingConstruction.initial (n + nodes) width start.size) packets.1 start

theorem front_size (prior : Program width 8) (allocated : Nat) : (front prior allocated).size = prior.size + 82 := by
  rw [prefix_image, ForestZeroSourcePlan.coldPrefix_size, negativePrior_size]

/-- Complete negative-branch construction, including source-clause production
and program materialization, is linear in the counted forest plus its prefix. -/
theorem forest_work (prior : Program width 8) (allocated : Nat) (graph : DAG n)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (rootMatches : RootsMatch graph roots) (forest : graph.FormulaForest) (b : Nat) (target : Channel n) :
    constructionWork prior graph.nodeCount allocated (source n rows)
      (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial) roots b target ≤
      100000 * (graph.countedSize + 1) + 10 * prior.size := by
  have checked : (ForestSourceConstruction.ids graph.nodeCount roots).1 = some graph.roots := by
    rw [show roots = graph.roots.map Fin.val from rootMatches]
    exact ids_of_fin _
  have conversion := ForestSourceConstruction.ids_work graph.nodeCount roots
  have generation := ForestQueryPackets.forest_work width graph rows roots matched rootMatches forest b target
  let cache := ForestCompilerOffsets.run rows ForestCompilerOffsets.initial
  let start := front prior allocated
  let protectedEnd := 6 + 6 * graph.nodeCount + cache.children + cache.guards + roots.length + 2 * (n + graph.nodeCount)
  let packets := (ForestQueryPackets.queries (source n rows) cache graph.roots b target).1
  have imageEq : packets = ForestZeroSourcePlan.zeroQueries width graph rows roots matched b target := by
    dsimp only [packets]
    rw [ForestQueryPackets.image, ForestCachedQueries.queries_eq width graph rows roots matched rootMatches b target]
  have packetLength : packets.length = graph.roots.length := by
    dsimp only [packets]
    rw [ForestQueryPackets.image, ForestCachedQueries.queries_length]
  have dimensions := ForestZeroSourcePlan.zero_queries_forest_bounds (width := width) graph rows roots matched b target forest
  have rowSize : packets.flatten.length ≤ 5 * graph.roots.length + 3 * graph.childIncidences := by
    simpa only [imageEq, List.length_flatten] using dimensions.1
  have literalSize : packets.flatten.flatten.length ≤ 8 * graph.roots.length + 6 * graph.childIncidences + graph.guardIncidences := by
    simpa only [imageEq, List.length_flatten, List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def] using dimensions.2
  have resident := ForestStreamingConstruction.construction_bound protectedEnd n
    (ForestStreamingConstruction.initial (n + graph.nodeCount) width start.size) packets start
  simp only [ForestStreamingConstruction.initial, ForestStreamingConstruction.buffered, List.flatten_nil,
    List.length_nil, Nat.mul_zero, Nat.add_zero, packetLength] at resident
  have rootsLength : roots.length = graph.roots.length := by rw [rootMatches, List.length_map]
  have startSize : start.size = prior.size + 82 := front_size prior allocated
  dsimp only [constructionWork]
  rw [checked, Option.getD_some]
  change (ForestSourceConstruction.ids graph.nodeCount roots).2 +
    (ForestQueryPackets.queries (source n rows) cache graph.roots b target).2 + 5000 + 8 * prior.size +
      ForestStreamingConstruction.constructionWork protectedEnd n
        (ForestStreamingConstruction.initial (n + graph.nodeCount) width start.size) packets start ≤ _
  dsimp only [cache, ForestStreamingConstruction.initial] at resident ⊢
  rw [DAG.countedSize_eq]
  omega

end Controller.Cost.ForestPreparedNegative
