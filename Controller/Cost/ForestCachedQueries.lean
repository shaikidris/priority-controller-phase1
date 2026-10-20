module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ForestCachedReferences
public import Controller.Cost.ForestZeroSourcePlan

@[expose] public section


/-! Root queries formed in source order from cached offsets. Positional roots
are traversed once, preserving duplicate declared observations. -/
namespace Controller.Cost.ForestCachedQueries

open Controller Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestWeightedIndexed
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroSource
open Controller.Cost.ForestZeroReferenceCone Controller.Cost.ForestZeroSourcePlan
open Controller.Cost.ForestZeroUnits

variable {n nodes : Nat}

def queries (table : Source n) (cache : ForestCompilerOffsets.State)
    (roots : List (Fin nodes)) (b : Nat) (target : Channel n) :
    List (List (List (Reference (n + nodes)))) :=
  let targetCell := ForestCompilerOffsets.rootSlot cache roots.length
  roots.zipIdx.map fun item =>
    let incoming := nodeReference (ForestCompilerOffsets.rootSlot cache item.2) item.1 false
    ForestCachedReferences.walk table cache item.1 incoming [] ++ [[incoming]] ++
      if b = 1 then [[targetReference targetCell target]] else []

private theorem zipIdx_finRange (values : List α) :
    values.zipIdx = (List.finRange values.length).map (fun index => (values.get index, index.val)) := by
  apply List.ext_getElem
  · simp
  · intro index left right
    simp

/-- Clause rows, source slots and target trailers coincide with the original
physical query implementation. Graph fields occur only in the specification. -/
theorem queries_eq (width : Nat) (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (matched : RowsMatch graph rows) (rootsMatch : RootsMatch graph rawRoots)
    (b : Nat) (target : Channel n) :
    queries (source n rows) (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial)
      graph.roots b target = zeroQueries width graph rows rawRoots matched b target := by
  have rootsLength : rawRoots.length = graph.roots.length := by rw [rootsMatch, List.length_map]
  simp only [queries, zipIdx_finRange, List.map_map, Function.comp_def,
    zeroQueries, List.ofFn_eq_map]
  apply List.map_congr_left
  intro position _
  have rootSlot : ForestCompilerOffsets.rootSlot
      (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial) position.val =
      5 + (6 * rows.length + (rowChildren rows).length + (rowGuards rows).length) + position.val := by
    rw [ForestCompilerOffsets.rootSlot_exact]
    omega
  have targetSlot : ForestCompilerOffsets.rootSlot
      (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial) graph.roots.length =
      (packetHeap width n rows rawRoots).size := by
    rw [ForestCompilerOffsets.rootSlot_exact, packetHeap_size, rootsLength]
  rw [rootSlot, targetSlot, ForestCachedReferences.walk_eq graph rows matched]
  unfold ForestZeroSourcePlan.zeroQuery forcedQuery query rootReference
  split <;> simp_all only [List.append_nil]

@[simp] theorem queries_length (table : Source n) (cache : ForestCompilerOffsets.State)
    (roots : List (Fin nodes)) (b : Nat) (target : Channel n) :
    (queries table cache roots b target).length = roots.length := by
  simp [queries]

end Controller.Cost.ForestCachedQueries
