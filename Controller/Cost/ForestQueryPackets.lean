/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ForestReferenceConstruction

/-! Source-driven construction of all negative query packets. This producer
runs the charged cone builder, appends the root/target units and advances the
original occurrence position. Repeated roots remain repeated queries. -/
namespace Controller.Cost.ForestQueryPackets

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestWeightedIndexed
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroSource
open Controller.Cost.ForestZeroReferenceCone Controller.Cost.ForestZeroUnits

variable {n nodes : Nat}

def one (table : Source n) (cache : ForestCompilerOffsets.State) (targetCell position : Nat)
    (root : Fin nodes) (b : Nat) (target : Channel n) : List (List (Reference (n + nodes))) × Nat :=
  let incoming := nodeReference (ForestCompilerOffsets.rootSlot cache position) root false
  let cone := ForestReferenceConstruction.form table cache root incoming []
  let suffix := [[incoming]] ++ if b = 1 then [[targetReference targetCell target]] else []
  (cone.1 ++ suffix, cone.2 + 4 * cone.1.length + 100)

def buildFrom (table : Source n) (cache : ForestCompilerOffsets.State) (targetCell : Nat) (b : Nat) (target : Channel n) :
    Nat → List (Fin nodes) → List (List (List (Reference (n + nodes)))) × Nat
  | _, [] => ([], 1)
  | position, root :: rest =>
      let current := one table cache targetCell position root b target
      let tail := buildFrom table cache targetCell b target (position + 1) rest
      (current.1 :: tail.1, current.2 + tail.2 + 10)

def queries (table : Source n) (cache : ForestCompilerOffsets.State) (roots : List (Fin nodes))
    (b : Nat) (target : Channel n) : List (List (List (Reference (n + nodes)))) × Nat :=
  buildFrom table cache (ForestCompilerOffsets.rootSlot cache roots.length) b target 0 roots

theorem from_image (table : Source n) (cache : ForestCompilerOffsets.State) (targetCell b : Nat)
    (target : Channel n) (roots : List (Fin nodes)) (position : Nat) :
    (buildFrom table cache targetCell b target position roots).1 = (roots.zipIdx position).map fun item =>
      let incoming := nodeReference (ForestCompilerOffsets.rootSlot cache item.2) item.1 false
      ForestCachedReferences.walk table cache item.1 incoming [] ++ [[incoming]] ++
        if b = 1 then [[targetReference targetCell target]] else [] := by
  induction roots generalizing position with
  | nil => rfl
  | cons root rest ih =>
      simp only [buildFrom, List.zipIdx_cons, List.map_cons, one, ForestReferenceConstruction.form_image, ih,
        List.append_assoc]

theorem image (table : Source n) (cache : ForestCompilerOffsets.State) (roots : List (Fin nodes))
    (b : Nat) (target : Channel n) :
    (queries table cache roots b target).1 = ForestCachedQueries.queries table cache roots b target := by
  exact from_image table cache _ b target roots 0

private theorem one_work (table : Source n) (cache : ForestCompilerOffsets.State) (targetCell position : Nat)
    (root : Fin nodes) (b : Nat) (target : Channel n) :
    (one table cache targetCell position root b target).2 ≤ 2 * ForestReferenceWork.budget table root +
      4 * (one table cache targetCell position root b target).1.length + 100 := by
  have cone := ForestReferenceConstruction.form_work table cache root
    (nodeReference (ForestCompilerOffsets.rootSlot cache position) root false) []
  simp only [one, List.length_append]
  omega

theorem from_work (table : Source n) (cache : ForestCompilerOffsets.State) (targetCell b : Nat)
    (target : Channel n) (roots : List (Fin nodes)) (position : Nat) :
    (buildFrom table cache targetCell b target position roots).2 ≤
      2 * (roots.map (ForestReferenceWork.budget table)).sum +
        4 * ((buildFrom table cache targetCell b target position roots).1.map List.length).sum +
          110 * roots.length + 1 := by
  induction roots generalizing position with
  | nil => simp [buildFrom]
  | cons root rest ih =>
      have current := one_work table cache targetCell position root b target
      have tail := ih (position + 1)
      simp only [buildFrom, List.map_cons, List.sum_cons, List.length_cons]
      omega

/-- The entire packet producer has a linear construction bound on a formula
forest. Every input occurrence, rather than just distinct roots, is charged. -/
theorem forest_work (width : Nat) (graph : DAG n) (rows : List Row) (rawRoots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph rawRoots)
    (forest : graph.FormulaForest) (b : Nat) (target : Channel n) :
    (queries (source n rows) (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial) graph.roots b target).2 ≤
      500 * graph.roots.length + 400 * graph.childIncidences + 100 * graph.guardIncidences + 1 := by
  have actual := from_work (source n rows) (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial)
    (ForestCompilerOffsets.rootSlot (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial) graph.roots.length) b target graph.roots 0
  change (queries (source n rows) (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial) graph.roots b target).2 ≤
    2 * (graph.roots.map (ForestReferenceWork.budget (source n rows))).sum +
      4 * ((queries (source n rows) (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial) graph.roots b target).1.map List.length).sum +
        110 * graph.roots.length + 1 at actual
  rw [image, ForestCachedQueries.queries_eq width graph rows rawRoots matched rootMatches b target] at actual
  have traversal := ForestReferenceWork.roots_bound graph rows matched forest
  have rowBound := (ForestZeroSourcePlan.zero_queries_forest_bounds (width := width) graph rows rawRoots matched b target forest).1
  omega

end Controller.Cost.ForestQueryPackets
