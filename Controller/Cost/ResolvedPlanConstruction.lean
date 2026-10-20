/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.AndRankConstruction
import Controller.Cost.SourceOperandConstruction

/-! The selector-query operand plan reads cached child offsets and dense AND
ranks. Original incidence positions and duplicate occurrences are preserved. -/
namespace Controller.Cost.ResolvedPlanConstruction

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Cost.ForestIndexedOperands Controller.Extensions.ResolvedSourceEmit

structure Cache (graph : DAG n) where
  offsets : ForestCompilerOffsets.State
  ranks : Vector Nat graph.nodeCount

def prepare (graph : DAG n) (rows : List Row) : Cache graph :=
  ⟨ForestCompilerOffsets.run rows ForestCompilerOffsets.initial, AndRankConstruction.build graph⟩

def childBase (packet : Array (Word width)) (cache : Cache graph) (index : Nat) : Nat :=
  packet.size + 6 * cache.offsets.rows.size + (cache.offsets.offsets[index]?.getD (0, 0)).1

theorem childBase_image (graph : DAG n) (rows : List Row) (matched : RowsMatch graph rows)
    (packet : Array (Word width)) (index : Fin graph.nodeCount) :
    childBase packet (prepare graph rows) index.val = ResolvedSourcePlan.childBase packet rows index.val := by
  have below : index.val < rows.length := by rw [matched.length_eq]; exact index.isLt
  have offset := ForestCompilerOffsets.run_offset rows ForestCompilerOffsets.initial index.val below
  have count := (ForestCompilerOffsets.run_totals rows ForestCompilerOffsets.initial).2.2.1
  simp only [show ForestCompilerOffsets.initial.offsets.size = 0 from rfl,
    show ForestCompilerOffsets.initial.rows.size = 0 from rfl,
    show ForestCompilerOffsets.initial.children = 0 from rfl,
    show ForestCompilerOffsets.initial.guards = 0 from rfl, Nat.zero_add] at offset count
  simp only [childBase, prepare, ResolvedSourcePlan.childBase]
  rw [count, offset]
  simp [ForestCompilerOffsets.initial]

def node (width : Nat) (graph : DAG n) (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
    (cache : Cache graph) (index : Fin graph.nodeCount) : List (Operand width) :=
  match graph.node index with
  | .liveAnd _ _ =>
      [.choice ((cacheHeap width packet rows roots).size + cache.ranks[index.val])
        (childBase packet cache index.val) (childBase packet cache index.val + 1) (word width n),
        .literal (word width (n + index.val))]
  | _ => ResolvedSourcePlan.literals width (ResolvedSourcePlan.coordinates (BoundedAnd.resolved graph ∅)
      ((BoundedAnd.resolved graph ∅).nodeClauses index))

theorem node_image (width : Nat) (graph : DAG n) (packet : Array (Word width))
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows) (index : Fin graph.nodeCount) :
    node width graph packet rows roots (prepare graph rows) index =
      ResolvedSourcePlan.node width graph packet rows roots index := by
  cases gate : graph.node index <;> simp only [node, ResolvedSourcePlan.node, gate]
  case liveAnd left right =>
    have rank := AndRankConstruction.build_rank graph index (by simp [gate, Gate.isLiveAnd])
    rw [childBase_image graph rows matched packet index]
    simp only [prepare, rank]

def forwards (width : Nat) (graph : DAG n) (packet : Array (Word width)) (rows : List Row)
    (roots : List Nat) (cache : Cache graph) : List (Operand width) :=
  (List.finRange graph.nodeCount).flatMap (node width graph packet rows roots cache)

def query (width : Nat) (graph : DAG n) (packet : Array (Word width)) (rows : List Row)
    (roots : List Nat) (cache : Cache graph) (b : Nat) (target : Channel n) (rootSlot : Nat) : List (Operand width) :=
  ResolvedSourcePlan.literals width (ResolvedSourcePlan.touchCoordinates graph) ++
    (forwards width graph packet rows roots cache ++
      (ResolvedSourcePlan.literals width (ResolvedSourcePlan.channelCoordinates graph b target) ++
        [.read rootSlot (word width n)]))

theorem query_image (width : Nat) (graph : DAG n) (packet : Array (Word width))
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows) (b : Nat) (target : Channel n)
    (rootSlot : Nat) :
    query width graph packet rows roots (prepare graph rows) b target rootSlot =
      ResolvedSourcePlan.query width graph packet rows roots b target rootSlot := by
  have nodes : forwards width graph packet rows roots (prepare graph rows) =
      ResolvedSourcePlan.forwards width graph packet rows roots := by
    apply List.flatMap_congr
    intro index member
    exact node_image width graph packet rows roots matched index
  simp only [query, ResolvedSourcePlan.query, nodes]

end Controller.Cost.ResolvedPlanConstruction
