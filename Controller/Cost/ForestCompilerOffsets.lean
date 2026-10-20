module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ForestIndexedOperands
public import Controller.Cost.CompilerAppendTrace

@[expose] public section


/-! One source pass caches row records and child/guard stream offsets. Later
reference formation uses indexed reads of these arrays; prefix sums occur
only in the correctness statement. Original incidence order is retained. -/
namespace Controller.Cost.ForestCompilerOffsets

open Controller.Cost.ForestIndexedOperands Controller.Cost.CompilerAppendTrace

structure State where
  children : Nat
  guards : Nat
  rows : Array Row
  offsets : Array (Nat × Nat)

def initial : State := ⟨0, 0, #[], #[]⟩

def step (state : State) (row : Row) : State :=
  ⟨state.children + row.children.length, state.guards + row.guards.length,
    state.rows.push row, state.offsets.push (state.children, state.guards)⟩

def run : List Row → State → State
  | [], state => state
  | row :: rest, state => run rest (step state row)

inductive Trace : List Row → State → State → Nat → Prop
  | nil (state) : Trace [] state state 0
  | cons (row rest state final childCount guardCount remaining)
      (children : LengthTrace row.children childCount childCount)
      (guards : LengthTrace row.guards guardCount guardCount)
      (tail : Trace rest (step state row) final remaining) :
      Trace (row :: rest) state final (childCount + guardCount + 10 + remaining)

theorem complete (rows : List Row) (state : State) :
    Trace rows state (run rows state)
      ((rowChildren rows).length + (rowGuards rows).length + 10 * rows.length) := by
  induction rows generalizing state with
  | nil => exact .nil state
  | cons row rest ih =>
      have result := Trace.cons row rest state _ row.children.length row.guards.length _
        (length_exists row.children) (length_exists row.guards) (ih (step state row))
      simpa [run, rowChildren, rowGuards, List.length_flatMap, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result

theorem run_totals (rows : List Row) (state : State) :
    (run rows state).children = state.children + (rowChildren rows).length ∧
      (run rows state).guards = state.guards + (rowGuards rows).length ∧
      (run rows state).rows.size = state.rows.size + rows.length ∧
      (run rows state).offsets.size = state.offsets.size + rows.length := by
  induction rows generalizing state with
  | nil => exact ⟨by simp [run, rowChildren], by simp [run, rowGuards], by simp [run], by simp [run]⟩
  | cons row rest ih =>
      obtain ⟨children, guards, records, offsets⟩ := ih (step state row)
      simp only [run]
      simp [step, rowChildren, rowGuards, List.length_flatMap, Nat.add_assoc] at children guards records offsets ⊢
      exact ⟨children, guards, by omega, by omega⟩

theorem run_rows (rows : List Row) (state : State) :
    (run rows state).rows.toList = state.rows.toList ++ rows := by
  induction rows generalizing state with
  | nil => simp [run]
  | cons row rest ih => simpa [run, step, List.append_assoc] using ih (step state row)

theorem run_old_offset (rows : List Row) (state : State) (index : Nat)
    (below : index < state.offsets.size) :
    (run rows state).offsets[index]? = state.offsets[index]? := by
  induction rows generalizing state with
  | nil => rfl
  | cons row rest ih =>
      have later := ih (step state row) (by simp [step]; omega)
      simpa only [run, step, Array.getElem?_push_lt below, Array.getElem?_eq_getElem below] using later

theorem run_offset (rows : List Row) (state : State) (index : Nat) (below : index < rows.length) :
    (run rows state).offsets[state.offsets.size + index]? =
      some (state.children + (rowChildren (rows.take index)).length,
        state.guards + (rowGuards (rows.take index)).length) := by
  induction rows generalizing state index with
  | nil => simp at below
  | cons row rest ih =>
      cases index with
      | zero =>
          have retained := run_old_offset rest (step state row) state.offsets.size (by simp [step])
          simpa [run, step, rowChildren, rowGuards] using retained
      | succ index =>
          have tail := ih (step state row) index (by simpa using below)
          simpa [run, step, List.take_succ_cons, rowChildren, rowGuards, List.length_flatMap,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail

def childSlot (source : State) (owner position : Nat) : Nat :=
  5 + 6 * source.rows.size + (source.offsets[owner]?.getD (0, 0)).1 + position

def guardSlot (source : State) (owner position : Nat) : Nat :=
  5 + 6 * source.rows.size + source.children + (source.offsets[owner]?.getD (0, 0)).2 + position

def rootSlot (source : State) (position : Nat) : Nat :=
  5 + 6 * source.rows.size + source.children + source.guards + position

theorem childSlot_exact (rows : List Row) (owner position : Nat) (below : owner < rows.length) :
    childSlot (run rows initial) owner position =
      5 + 6 * rows.length + (rowChildren (rows.take owner)).length + position := by
  have offset := run_offset rows initial owner below
  have count := (run_totals rows initial).2.2.1
  simp only [initial, Array.size_empty, Nat.zero_add] at offset count
  simp [childSlot, initial, offset, count]

theorem guardSlot_exact (rows : List Row) (owner position : Nat) (below : owner < rows.length) :
    guardSlot (run rows initial) owner position =
      5 + 6 * rows.length + (rowChildren rows).length + (rowGuards (rows.take owner)).length + position := by
  have offset := run_offset rows initial owner below
  have counts := run_totals rows initial
  simp only [initial, Array.size_empty, Nat.zero_add] at offset counts
  simp [guardSlot, initial, offset, counts.1, counts.2.2.1]

theorem rootSlot_exact (rows : List Row) (position : Nat) :
    rootSlot (run rows initial) position =
      5 + 6 * rows.length + (rowChildren rows).length + (rowGuards rows).length + position := by
  have counts := run_totals rows initial
  simp only [initial, Array.size_empty, Nat.zero_add] at counts
  simp [rootSlot, initial, counts.1, counts.2.1, counts.2.2.1]

end Controller.Cost.ForestCompilerOffsets
