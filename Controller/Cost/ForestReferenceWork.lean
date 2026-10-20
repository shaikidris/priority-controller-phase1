/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ForestCachedQueries
import Controller.Cost.WordConstructionRecipe

/-! Source-field work for the cached clause producer. The resource measure
counts the indexed row/tag reads and dispatch, advancing incidence positions,
source-address arithmetic, five-field reference records, signed-literal copies
and row-list copies. It is a construction-operation model, not a fetched
execution bound. The tree count below is a ghost measure; the compiler does
not allocate annotated traversal paths. -/
namespace Controller.Cost.ForestReferenceWork

open Controller Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestWeightedIndexed
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroSource
open Controller.Cost.ForestZeroReferenceCone Controller.Cost.WordConstructionRecipe

/-- The cached child slot has five scalar reads and four arithmetic nodes;
no prefix traversal occurs in this expression. -/
def childSlot : Expression 3 :=
  .add (.add (.literal 5) (.mul (.literal 6) (.parameter 0)))
    (.add (.parameter 1) (.parameter 2))

theorem child_slot (rows offset position : Nat) :
    childSlot.eval (fun i => [rows, offset, position].getD i.val 0) =
      5 + 6 * rows + offset + position ∧ childSlot.work = 9 := by
  exact ⟨by simp [childSlot, Expression.eval, Nat.add_assoc], rfl⟩

/-- Guard slots additionally read the cached total child count. -/
def guardSlot : Expression 4 :=
  .add (.add (.add (.literal 5) (.mul (.literal 6) (.parameter 0))) (.parameter 1))
    (.add (.parameter 2) (.parameter 3))

theorem guard_slot (rows children offset position : Nat) :
    guardSlot.eval (fun i => [rows, children, offset, position].getD i.val 0) =
      5 + 6 * rows + children + offset + position ∧ guardSlot.work = 11 := by
  exact ⟨by simp [guardSlot, Expression.eval, Nat.add_assoc], rfl⟩

/-- The fixed allowance includes lookup/tag dispatch and output-list control.
Each incidence covers its bounded address recipe, source reads, position update
and five reference-field writes. Each emitted literal/row is explicitly copied. -/
def localWork (table : Source n) (cache : ForestCompilerOffsets.State) (owner : Fin nodes)
    (incoming : Reference (n + nodes)) : Nat :=
  let gate := readNode table owner.val
  let rows := ForestCachedReferences.own table cache owner incoming
  40 + 32 * gate.children.length + 32 * gate.guardLabels.length +
    8 * rows.flatten.length + 4 * rows.length

theorem referenceClauses_size (row : Row) (owner head : Reference ambient)
    (children guards : List (Reference ambient)) :
    (referenceClauses row owner head children guards).length ≤ 2 + children.length ∧
      (referenceClauses row owner head children guards).flatten.length ≤
        4 + 2 * children.length + guards.length := by
  unfold referenceClauses
  split <;> simp_all [List.length_flatten, List.map_map, Function.comp_def] <;> omega

theorem local_bound (table : Source n) (cache : ForestCompilerOffsets.State) (owner : Fin nodes)
    (incoming : Reference (n + nodes)) :
    localWork table cache owner incoming ≤ 80 + 64 * (readNode table owner.val).children.length +
      40 * (readNode table owner.val).guardLabels.length := by
  have size := referenceClauses_size (cache.rows[owner.val]?.getD ⟨0, 0, [], []⟩) incoming
    (ForestCachedReferences.head owner (readNode table owner.val) incoming)
    (ForestCachedReferences.children cache owner (readNode table owner.val).children)
    (ForestCachedReferences.guards cache owner (readNode table owner.val).guardLabels)
  simp only [ForestCachedReferences.children, ForestCachedReferences.guards, List.length_map, List.length_zipIdx] at size
  change (ForestCachedReferences.own table cache owner incoming).length ≤ _ ∧
    (ForestCachedReferences.own table cache owner incoming).flatten.length ≤ _ at size
  change 40 + 32 * (readNode table owner.val).children.length +
    32 * (readNode table owner.val).guardLabels.length +
    8 * (ForestCachedReferences.own table cache owner incoming).flatten.length +
    4 * (ForestCachedReferences.own table cache owner incoming).length ≤ _
  omega

/-- Exact source-recursion envelope, following the same ranked children as the
clause producer. It is independent of graph-node callbacks. -/
def budget (table : Source n) (owner : Fin nodes) : Nat :=
  let gate := readNode table owner.val
  80 + 64 * gate.children.length + 40 * gate.guardLabels.length +
    (gate.children.map fun child => budget table (⟨child.val, child.isLt.trans owner.isLt⟩ : Fin nodes)).sum
termination_by owner.val
decreasing_by exact Fin.isLt _

private theorem sum_map_bound (items : List α) (f g : α → Nat) (bound : ∀ a ∈ items, f a ≤ g a) :
    (items.map f).sum ≤ (items.map g).sum := by
  induction items with
  | nil => simp
  | cons item rest ih =>
      have first := bound item List.mem_cons_self
      have tail := ih (fun a member => bound a (List.mem_cons_of_mem _ member))
      simp only [List.map_cons, List.sum_cons]
      omega

private theorem sum_coeff (items : List α) (f g : α → Nat) (a b : Nat) :
    (items.map fun x => a * f x + b * g x).sum = a * (items.map f).sum + b * (items.map g).sum := by
  induction items with
  | nil => simp
  | cons x rest ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]; omega

private theorem sum_offset (items : List α) (f : α → Nat) (constant : Nat) :
    (items.map fun x => f x + constant).sum = (items.map f).sum + constant * items.length := by
  induction items with
  | nil => simp
  | cons x rest ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons, Nat.mul_add, Nat.mul_one]; omega

private theorem sum_flatMap (items : List α) (children : α → List β) (charge : β → Nat) :
    ((items.flatMap children).map charge).sum =
      (items.map fun x => ((children x).map charge).sum).sum := by
  induction items with
  | nil => rfl
  | cons x rest ih => simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons, ih]

/-- The construction envelope is bounded by actual node and guard occurrences.
The identities on these occurrences do not allocate a traversal in the compiler. -/
theorem budget_bound (graph : DAG n) (rows : List Row) (matched : RowsMatch graph rows) :
    ∀ owner : Fin graph.nodeCount,
    budget (source n rows) owner ≤
      144 * (Controller.Cost.ForestNodeVisits.walkNodes graph owner).length +
      40 * (((Controller.Cost.ForestNodeVisits.walkNodes graph owner).map fun node =>
        (graph.node node).guardLabels.length).sum) := by
  have claim : ∀ rank, ∀ owner : Fin graph.nodeCount, owner.val = rank →
      budget (source n rows) owner + 64 ≤
        144 * (Controller.Cost.ForestNodeVisits.walkNodes graph owner).length +
        40 * (((Controller.Cost.ForestNodeVisits.walkNodes graph owner).map fun node =>
          (graph.node node).guardLabels.length).sum) := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro owner equal
      rw [budget.eq_def, readNode_matches graph rows matched owner, Controller.Cost.ForestNodeVisits.walkNodes.eq_def]
      have children : ∀ child : Fin owner.val,
          budget (source n rows) (graph.childIndex owner child) + 64 ≤
            144 * (Controller.Cost.ForestNodeVisits.walkNodes graph (graph.childIndex owner child)).length +
            40 * (((Controller.Cost.ForestNodeVisits.walkNodes graph (graph.childIndex owner child)).map
              fun node => (graph.node node).guardLabels.length).sum) := by
        intro child
        exact ih child.val (by omega) _ rfl
      have sumBound := sum_map_bound (graph.node owner).children
        (fun child => budget (source n rows) (graph.childIndex owner child) + 64)
        (fun child => 144 * (Controller.Cost.ForestNodeVisits.walkNodes graph (graph.childIndex owner child)).length +
          40 * (((Controller.Cost.ForestNodeVisits.walkNodes graph (graph.childIndex owner child)).map
            fun node => (graph.node node).guardLabels.length).sum)) (fun child _ => children child)
      rw [sum_offset, sum_coeff] at sumBound
      simp only [List.length_cons, List.length_flatMap, List.map_cons, List.sum_cons, sum_flatMap]
      change 80 + 64 * (graph.node owner).children.length + 40 * (graph.node owner).guardLabels.length +
        ((graph.node owner).children.map fun child => budget (source n rows) (graph.childIndex owner child)).sum + 64 ≤ _
      omega
  intro owner
  have result := claim owner.val owner rfl
  omega

theorem roots_bound (graph : DAG n) (rows : List Row) (matched : RowsMatch graph rows)
    (forest : graph.FormulaForest) :
    (graph.roots.map (budget (source n rows))).sum ≤
      144 * (graph.roots.length + graph.childIncidences) + 40 * graph.guardIncidences := by
  have summed := sum_map_bound graph.roots (budget (source n rows))
    (fun owner => 144 * (Controller.Cost.ForestNodeVisits.walkNodes graph owner).length +
      40 * (((Controller.Cost.ForestNodeVisits.walkNodes graph owner).map
        fun node => (graph.node node).guardLabels.length).sum)) (fun owner _ => budget_bound graph rows matched owner)
  have nodes := Controller.Cost.ForestNodeVisits.root_node_count_le graph forest
  have guards := root_guard_sum_bound graph forest
  simp only [Controller.Cost.ForestNodeVisits.rootNodes, List.length_flatMap] at nodes
  rw [sum_coeff] at summed
  omega

end Controller.Cost.ForestReferenceWork
