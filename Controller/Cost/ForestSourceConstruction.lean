module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ForestWeightedIndexed

@[expose] public section


/-! Charged validation of the original ordered rows. Bounds include checked
child and channel conversion, advancing row positions and the final array
materialization; the graph correspondence is a specification, not an input
oracle. These are source construction operations rather than fetched ticks. -/
namespace Controller.Cost.ForestSourceConstruction

open Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestWeightedIndexed

/-- Checked conversions stop at the first out-of-range source identifier. -/
def ids (bound : Nat) : List Nat → Option (List (Fin bound)) × Nat
  | [] => (some [], 1)
  | value :: rest =>
      if valid : value < bound then
        let tail := ids bound rest
        (tail.1.map (⟨value, valid⟩ :: ·), tail.2 + 4)
      else (none, 2)

inductive IdTrace (bound : Nat) : List Nat → Option (List (Fin bound)) → Nat → Prop
  | nil : IdTrace bound [] (some []) 1
  | accepted (value rest result ticks) (valid : value < bound)
      (tail : IdTrace bound rest result ticks) :
      IdTrace bound (value :: rest) (result.map (⟨value, valid⟩ :: ·)) (ticks + 4)
  | rejected (value rest) (invalid : ¬ value < bound) : IdTrace bound (value :: rest) none 2

theorem ids_trace (bound : Nat) (values : List Nat) :
    IdTrace bound values (ids bound values).1 (ids bound values).2 := by
  induction values with
  | nil => exact .nil
  | cons value rest ih =>
      unfold ids
      split_ifs with valid
      · exact .accepted value rest _ _ valid ih
      · exact .rejected value rest valid

theorem ids_eq (bound : Nat) (values : List Nat) :
    (ids bound values).1 = boundedIds bound values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp only [ids, boundedIds]
      split_ifs <;> simp_all

theorem ids_work (bound : Nat) (values : List Nat) :
    (ids bound values).2 ≤ 4 * values.length + 1 := by
  induction values with
  | nil => simp [ids]
  | cons value rest ih =>
      simp only [ids]
      split_ifs <;> simp only [List.length_cons] <;> omega

/-- Both incidence lists are validated once. Validating an unused list is
permitted and preserves the original decoder's result. -/
def row (channels owner : Nat) (record : Row) : Option (Gate channels owner) × Nat :=
  let children := ids owner record.children
  let guards := ids channels record.guards
  let result := match record.tag with
    | 0 => some .zero
    | 1 => if valid : record.head < channels then some (.input ⟨record.head, valid⟩) else none
    | 2 => children.1.map Gate.disj
    | 3 => do
        let values ← children.1
        let labels ← guards.1
        match values with
        | [child] => some (.guard child labels)
        | _ => none
    | 4 => do
        let values ← children.1
        match values with
        | [first, second] => some (.liveAnd first second)
        | _ => none
    | _ => none
  (result, children.2 + guards.2 + 10)

theorem row_eq (channels owner : Nat) (record : Row) :
    (row channels owner record).1 = decodeRow channels owner record := by
  simp only [row, ids_eq]
  rfl

theorem row_work (channels owner : Nat) (record : Row) :
    (row channels owner record).2 ≤ 4 * record.children.length + 4 * record.guards.length + 12 := by
  have children := ids_work owner record.children
  have guards := ids_work channels record.guards
  change (ids owner record.children).2 + (ids channels record.guards).2 + 10 ≤ _
  omega

/-- The advancing index is carried by recursion, not recovered by list lookup. -/
def items (channels : Nat) : Nat → List Row → List (Option (Sigma fun owner : Nat => Gate channels owner)) × Nat
  | _, [] => ([], 1)
  | owner, record :: rest =>
      let current := row channels owner record
      let tail := items channels (owner + 1) rest
      ((current.1.map (Sigma.mk owner)) :: tail.1, current.2 + tail.2 + 5)

theorem items_eq (channels owner : Nat) (records : List Row) :
    (items channels owner records).1 = (records.zipIdx owner).map
      (fun item => (decodeRow channels item.2 item.1).map (Sigma.mk item.2)) := by
  induction records generalizing owner with
  | nil => rfl
  | cons record rest ih => simp only [items, List.zipIdx_cons, List.map_cons, row_eq, ih]

theorem items_work (channels owner : Nat) (records : List Row) :
    (items channels owner records).2 ≤
      4 * (rowChildren records).length + 4 * (rowGuards records).length + 17 * records.length + 1 := by
  induction records generalizing owner with
  | nil => simp [items, rowChildren, rowGuards]
  | cons record rest ih =>
      have first := row_work channels owner record
      have tail := ih (owner + 1)
      simp only [items, rowChildren, rowGuards, List.flatMap_cons, List.length_append,
        List.length_cons] at *
      omega

/-- The validated output is the actual indexed source consumed by the
selector. The final materialization performs one array push per source row. -/
theorem source_preparation (channels : Nat) (records : List Row) :
    (items channels 0 records).1.toArray = source channels records ∧
      CompilerArrayTrace.Trace (items channels 0 records).1 #[] (source channels records) records.length ∧
      (items channels 0 records).2 + records.length ≤
        4 * (rowChildren records).length + 4 * (rowGuards records).length + 18 * records.length + 1 := by
  have same : (items channels 0 records).1 = sourceItems channels records := items_eq channels 0 records
  have length : (items channels 0 records).1.length = records.length := by rw [same]; simp [sourceItems]
  refine ⟨congrArg List.toArray same, ?_, ?_⟩
  · rw [← length, source, ← congrArg List.toArray same]
    exact CompilerArrayTrace.empty_array _
  · have bounded := items_work channels 0 records
    omega

end Controller.Cost.ForestSourceConstruction
