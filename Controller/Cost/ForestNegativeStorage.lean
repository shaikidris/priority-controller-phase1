/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ForestPreparedNegative
import Controller.Cost.ForestStreamingStorage

/-! Original-forest storage bound for the complete negative image constructor.
The certified loop includes metadata and provisional/relocated scratch; final
reversal, flattening, widening and array materialization buffers are retained
in addition to the already formed source-prefix image. -/
namespace Controller.Cost.ForestNegativeStorage

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestWeightedIndexed
open Controller.Cost.ForestStreamingConstruction

variable {n : Nat}

theorem construction (prior : Program width 8) (allocated : Nat) (graph : DAG n)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots)
    (forest : graph.FormulaForest) (b : Nat) (target : Channel n) :
    let cache := ForestCompilerOffsets.run rows ForestCompilerOffsets.initial
    let start := ForestPreparedNegative.front prior allocated
    let packets := (ForestQueryPackets.queries (source n rows) cache graph.roots b target).1
    let protectedEnd := 6 + 6 * graph.nodeCount + cache.children + cache.guards + roots.length + 2 * (n + graph.nodeCount)
    let initial := ForestStreamingConstruction.initial (n + graph.nodeCount) width start.size
    let final := ForestStreamingConstruction.run protectedEnd n initial packets
    ∃ peak, ForestStreamingStorage.Trace protectedEnd n initial packets final peak ∧
      ForestPreparedNegative.form prior graph.nodeCount allocated (source n rows) cache roots b target =
        ForestStreamingConstruction.compile protectedEnd n initial packets start ∧
      peak + 32 * buffered final + 2 * final.blocks.length + 8 * start.size + 50000 ≤
        10000000 * (graph.countedSize + 1) + 8 * prior.size := by
  intro cache start packets protectedEnd initial final
  obtain ⟨peak, trace, bound⟩ := ForestStreamingStorage.construction protectedEnd n initial packets
  have bufferedBound := run_buffered protectedEnd n initial packets
  have blocks := run_blocks protectedEnd n initial packets
  have packetImage : packets = ForestZeroSourcePlan.zeroQueries width graph rows roots matched b target := by
    dsimp only [packets, cache]
    rw [ForestQueryPackets.image, ForestCachedQueries.queries_eq width graph rows roots matched rootMatches b target]
  have packetLength : packets.length = graph.roots.length := by
    dsimp only [packets]
    rw [ForestQueryPackets.image, ForestCachedQueries.queries_length]
  have sizes := ForestZeroSourcePlan.zero_queries_forest_bounds (width := width) graph rows roots matched b target forest
  have rowBound : packets.flatten.length ≤ 5 * graph.roots.length + 3 * graph.childIncidences := by
    simpa only [packetImage, List.length_flatten] using sizes.1
  have literalBound : packets.flatten.flatten.length ≤ 8 * graph.roots.length + 6 * graph.childIncidences + graph.guardIncidences := by
    simpa only [packetImage, List.length_flatten, List.map_flatten, List.sum_flatten,
      List.map_map, Function.comp_def] using sizes.2
  have checked : (ForestSourceConstruction.ids graph.nodeCount roots).1 = some graph.roots := by
    rw [show roots = graph.roots.map Fin.val from rootMatches]
    exact ForestPreparedNegative.ids_of_fin _
  refine ⟨peak, trace, ?_, ?_⟩
  · dsimp only [ForestPreparedNegative.form]
    rw [checked]
    rfl
  · have startSize : start.size = prior.size + 82 := ForestPreparedNegative.front_size prior allocated
    simp only [initial, ForestStreamingConstruction.initial, retainedWords, buffered, List.flatten_nil, List.length_nil,
      Nat.mul_zero, Nat.add_zero, packetLength] at bound bufferedBound blocks
    change peak + 32 * buffered final + 2 * final.blocks.length + 8 * start.size + 50000 ≤ _
    change buffered final ≤ _ at bufferedBound
    change final.blocks.length = _ at blocks
    rw [DAG.countedSize_eq]
    omega

end Controller.Cost.ForestNegativeStorage
