/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ForestCompilerOffsets
import Controller.Cost.ForestWeightedIndexed
import Controller.Cost.ForestZeroReferenceCone

/-! Source-addressed clauses formed from indexed rows and cached stream
positions. Child and guard lists are traversed with advancing indices; the
constructor does not repeatedly scan source prefixes or use positional list
lookup to enumerate incidences. -/
namespace Controller.Cost.ForestCachedReferences

open Controller Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestWeightedIndexed
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroSource
open Controller.Cost.ForestZeroReferenceCone

variable {n nodes : Nat}

def child (cache : ForestCompilerOffsets.State) (owner : Fin nodes) (position : Nat)
    (value : Fin owner.val) : Reference (n + nodes) :=
  nodeReference (ForestCompilerOffsets.childSlot cache owner.val position)
    (⟨value.val, value.isLt.trans owner.isLt⟩ : Fin nodes) false

def children (cache : ForestCompilerOffsets.State) (owner : Fin nodes)
    (values : List (Fin owner.val)) : List (Reference (n + nodes)) :=
  values.zipIdx.map fun item => child cache owner item.2 item.1

def guards (cache : ForestCompilerOffsets.State) (owner : Fin nodes)
    (values : List (Channel n)) : List (Reference (n + nodes)) :=
  values.zipIdx.map fun item => channelReference
    (ForestCompilerOffsets.guardSlot cache owner.val item.2) item.1 true

def head (owner : Fin nodes) (node : Gate n owner.val) (incoming : Reference (n + nodes)) :
    Reference (n + nodes) :=
  match node with
  | .input channel => channelReference (5 + (2 * owner.val + 1)) channel false
  | _ => incoming

def own (table : Source n) (cache : ForestCompilerOffsets.State) (owner : Fin nodes)
    (incoming : Reference (n + nodes)) : List (List (Reference (n + nodes))) :=
  let node := readNode table owner.val
  let row := cache.rows[owner.val]?.getD ⟨0, 0, [], []⟩
  referenceClauses row incoming (head owner node incoming)
    (children cache owner node.children) (guards cache owner node.guardLabels)

def walk (table : Source n) (cache : ForestCompilerOffsets.State) (owner : Fin nodes)
    (incoming : Reference (n + nodes)) (tail : List (List (Reference (n + nodes)))) :
    List (List (Reference (n + nodes))) :=
  own table cache owner incoming ++
    (readNode table owner.val).children.zipIdx.foldr (fun item suffix =>
      walk table cache (⟨item.1.val, item.1.isLt.trans owner.isLt⟩ : Fin nodes)
        (child cache owner item.2 item.1) suffix) tail
termination_by owner.val
decreasing_by exact Fin.isLt _

private theorem zipIdx_finRange (values : List α) :
    values.zipIdx = (List.finRange values.length).map (fun index => (values.get index, index.val)) := by
  apply List.ext_getElem
  · simp
  · intro index left right
    simp

theorem children_eq (graph : DAG n) (rows : List Row) (matched : RowsMatch graph rows)
    (owner : Fin graph.nodeCount) :
    children (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial) owner (graph.node owner).children =
      childReferences graph rows owner := by
  simp only [children, zipIdx_finRange, List.map_map, Function.comp_def,
    childReferences, List.ofFn_eq_map]
  apply List.map_congr_left
  intro position _
  unfold child childReference
  rw [ForestCompilerOffsets.childSlot_exact rows owner.val position.val
    (by rw [matched.length_eq]; exact owner.isLt)]
  rfl

theorem guards_eq (graph : DAG n) (rows : List Row) (matched : RowsMatch graph rows)
    (owner : Fin graph.nodeCount) :
    guards (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial) owner (graph.node owner).guardLabels =
      guardReferences graph rows owner := by
  simp only [guards, zipIdx_finRange, List.map_map, Function.comp_def,
    guardReferences, List.ofFn_eq_map]
  apply List.map_congr_left
  intro position _
  rw [ForestCompilerOffsets.guardSlot_exact rows owner.val position.val
    (by rw [matched.length_eq]; exact owner.isLt)]
  rfl

theorem own_eq (graph : DAG n) (rows : List Row) (matched : RowsMatch graph rows)
    (owner : Fin graph.nodeCount) (incoming : Reference (n + graph.nodeCount)) :
    own (source n rows) (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial) owner incoming =
      ownReferences graph rows matched owner incoming := by
  have records := ForestCompilerOffsets.run_rows rows ForestCompilerOffsets.initial
  have cell := congrArg (fun values : List Row => values[owner.val]?) records
  simp only [ForestCompilerOffsets.initial, Array.toList_empty, List.nil_append,
    Array.getElem?_toList] at cell
  have index : owner.val < rows.length := by rw [matched.length_eq]; exact owner.isLt
  unfold own ownReferences
  rw [readNode_matches graph rows matched owner]
  have actual : (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial).rows[owner.val]? =
      some rows[owner.val] := by
    simpa only [ForestCompilerOffsets.initial, List.getElem?_eq_getElem index] using cell
  rw [actual]
  simp only [Option.getD_some, children_eq graph rows matched owner, guards_eq graph rows matched owner]
  have same : head owner (graph.node owner) incoming = headReference graph owner incoming := by
    cases gate : graph.node owner <;> simp [head, headReference, gate, inputReference]
  rw [same]

private theorem foldr_agrees (items : List α) (left right : α → β → β)
    (same : ∀ item suffix, left item suffix = right item suffix) (tail : β) :
    items.foldr left tail = items.foldr right tail := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [List.foldr_cons, same, ih]

/-- The optimized traversal preserves every original clause and source slot,
including repeated child, guard and declared root occurrences. -/
theorem walk_eq (graph : DAG n) (rows : List Row) (matched : RowsMatch graph rows) :
    ∀ owner : Fin graph.nodeCount, ∀ incoming tail,
    walk (source n rows) (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial) owner incoming tail =
      referenceCone graph rows matched owner incoming tail := by
  have claim : ∀ rank : Nat, ∀ owner : Fin graph.nodeCount, owner.val = rank → ∀ incoming tail,
      walk (source n rows) (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial) owner incoming tail =
        referenceCone graph rows matched owner incoming tail := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro owner rankEq incoming tail
      rw [walk.eq_def, referenceCone.eq_def]
      rw [own_eq graph rows matched owner incoming, readNode_matches graph rows matched owner]
      simp only [zipIdx_finRange, List.foldr_map]
      apply congrArg (List.append (ownReferences graph rows matched owner incoming))
      apply foldr_agrees
      intro position suffix
      have earlier : (graph.childIndex owner ((graph.node owner).children.get position)).val < rank := by
        have smaller := graph.childIndex_lt owner ((graph.node owner).children.get position)
        omega
      have childEq : (⟨((graph.node owner).children.get position).val,
          ((graph.node owner).children.get position).isLt.trans owner.isLt⟩ : Fin graph.nodeCount) =
          graph.childIndex owner ((graph.node owner).children.get position) := by
        apply Fin.ext
        rfl
      rw [childEq, ih _ earlier _ rfl]
      congr 1
      unfold child childReference
      rw [ForestCompilerOffsets.childSlot_exact rows owner.val position.val
        (by rw [matched.length_eq]; exact owner.isLt)]
      rfl
  intro owner incoming tail
  exact claim owner.val owner rfl incoming tail

end Controller.Cost.ForestCachedReferences
