/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ForestReferenceConstruction

/-! Cumulative new-record storage of the cached source-clause producer.
Original source arrays and input tails are read-only and shared. The profile
counts source-reference records, signed literal/list copies, indexed child
control and pending call frames; retaining every new record is conservative. -/
namespace Controller.Cost.ForestReferenceStorage

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestWeightedIndexed
open Controller.Cost.ForestZeroEmit

variable {n nodes : Nat}

/-- Reference fields and list/call records, including temporary slot operands.
The fixed allowance covers source/tag dispatch and arithmetic continuations. -/
def localWords (table : Source n) (cache : ForestCompilerOffsets.State) (owner : Fin nodes)
    (incoming : Reference (n + nodes)) : Nat :=
  let gate := readNode table owner.val
  let emitted := ForestCachedReferences.own table cache owner incoming
  512 + 64 * gate.children.length + 64 * gate.guardLabels.length +
    16 * emitted.flatten.length + 8 * emitted.length

theorem local_bound (table : Source n) (cache : ForestCompilerOffsets.State) (owner : Fin nodes)
    (incoming : Reference (n + nodes)) :
    localWords table cache owner incoming ≤ 592 +
      104 * (readNode table owner.val).children.length + 80 * (readNode table owner.val).guardLabels.length := by
  have size := ForestReferenceWork.referenceClauses_size (cache.rows[owner.val]?.getD ⟨0, 0, [], []⟩)
    incoming (ForestCachedReferences.head owner (readNode table owner.val) incoming)
    (ForestCachedReferences.children cache owner (readNode table owner.val).children)
    (ForestCachedReferences.guards cache owner (readNode table owner.val).guardLabels)
  simp only [ForestCachedReferences.children, ForestCachedReferences.guards, List.length_map, List.length_zipIdx] at size
  change (ForestCachedReferences.own table cache owner incoming).length ≤ _ ∧
    (ForestCachedReferences.own table cache owner incoming).flatten.length ≤ _ at size
  dsimp only [localWords]
  omega

def allocated (table : Source n) (cache : ForestCompilerOffsets.State) (owner : Fin nodes)
    (incoming : Reference (n + nodes)) : Nat :=
  let gate := readNode table owner.val
  localWords table cache owner incoming + 16 * gate.children.length + 32 +
    (gate.children.zipIdx.map fun item => allocated table cache
      (⟨item.1.val, item.1.isLt.trans owner.isLt⟩ : Fin nodes)
      (ForestCachedReferences.child cache owner item.2 item.1)).sum
termination_by owner.val
decreasing_by exact Fin.isLt _

private theorem sum_le (values : List α) (f g : α → Nat) (bound : ∀ value ∈ values, f value ≤ g value) :
    (values.map f).sum ≤ (values.map g).sum := by
  induction values with
  | nil => simp
  | cons value rest ih =>
      have first := bound value List.mem_cons_self
      have tail := ih (fun value member => bound value (List.mem_cons_of_mem _ member))
      simp only [List.map_cons, List.sum_cons]
      omega

theorem allocation_bound (table : Source n) (cache : ForestCompilerOffsets.State) :
    ∀ owner : Fin nodes, ∀ incoming,
      allocated table cache owner incoming ≤ 16 * ForestReferenceWork.budget table owner := by
  have claim : ∀ rank, ∀ owner : Fin nodes, owner.val = rank → ∀ incoming,
      allocated table cache owner incoming ≤ 16 * ForestReferenceWork.budget table owner := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro owner equal incoming
      let gate := readNode table owner.val
      have descendants := sum_le gate.children.zipIdx
        (fun item => allocated table cache (⟨item.1.val, item.1.isLt.trans owner.isLt⟩ : Fin nodes)
          (ForestCachedReferences.child cache owner item.2 item.1))
        (fun item => 16 * ForestReferenceWork.budget table (⟨item.1.val, item.1.isLt.trans owner.isLt⟩ : Fin nodes))
        (fun item _ => ih item.1.val (by omega) _ rfl _)
      have summed : (gate.children.zipIdx.map fun item =>
          16 * ForestReferenceWork.budget table (⟨item.1.val, item.1.isLt.trans owner.isLt⟩ : Fin nodes)).sum =
          16 * (gate.children.map fun child => ForestReferenceWork.budget table
            (⟨child.val, child.isLt.trans owner.isLt⟩ : Fin nodes)).sum := by
        have indexed := congrArg (List.map (fun child : Fin owner.val => 16 * ForestReferenceWork.budget table
          (⟨child.val, child.isLt.trans owner.isLt⟩ : Fin nodes))) (List.zipIdx_map_fst 0 gate.children)
        simp only [List.map_map, Function.comp_def] at indexed
        rw [indexed]
        clear indexed descendants
        induction gate.children with
        | nil => simp
        | cons child rest ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]
      rw [summed] at descendants
      have own := local_bound table cache owner incoming
      rw [allocated.eq_def, ForestReferenceWork.budget.eq_def]
      dsimp only [gate] at descendants own ⊢
      omega
  intro owner incoming
  exact claim owner.val owner rfl incoming

/-- All newly allocated reference/row/control words across the original root
occurrences fit a linear bound, including duplicate observations. -/
theorem roots_bound (graph : DAG n) (rows : List Row) (matched : RowsMatch graph rows)
    (forest : graph.FormulaForest) (incoming : Fin graph.nodeCount → Reference (n + graph.nodeCount)) :
    (graph.roots.map fun root => allocated (source n rows)
      (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial) root (incoming root)).sum ≤
      2304 * (graph.roots.length + graph.childIncidences) + 640 * graph.guardIncidences := by
  have perRoot := sum_le graph.roots
    (fun root => allocated (source n rows) (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial) root (incoming root))
    (fun root => 16 * ForestReferenceWork.budget (source n rows) root)
    (fun root _ => allocation_bound _ _ root _)
  have scaled : (graph.roots.map fun root => 16 * ForestReferenceWork.budget (source n rows) root).sum =
      16 * (graph.roots.map (ForestReferenceWork.budget (source n rows))).sum := by
    induction graph.roots with
    | nil => simp
    | cons root rest ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]
  rw [scaled] at perRoot
  have count := ForestReferenceWork.roots_bound graph rows matched forest
  omega

end Controller.Cost.ForestReferenceStorage
