module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ForestZeroCompile

@[expose] public section


/-! An epoch-indexed source compiler dictionary. The two dense arrays are
initialized once; starting a query increments the epoch and clears only the
local coordinate accumulator. Its dense dictionary projection is a proof view,
not an operation used by the executable compiler. -/
namespace Controller.Cost.ForestCompilerDictionary

open Controller.CNF
open Controller.Cost.ForestZeroCompile

structure State (ambient : Nat) where
  epoch : Nat
  stamps : Vector Nat ambient
  indices : Vector Nat ambient
  coordinates : Array (Fin ambient)

def initial (ambient : Nat) : State ambient :=
  ⟨1, Vector.replicate ambient 0, Vector.replicate ambient 0, #[]⟩

def encoded (state : State ambient) (coordinate : Fin ambient) : Nat :=
  if state.stamps[coordinate.val] = state.epoch then state.indices[coordinate.val] else 0

/-- The projection is used to state equality with the existing dense compiler. -/
def project (state : State ambient) : Dictionary ambient :=
  ⟨Vector.ofFn (encoded state), state.coordinates⟩

def Valid (state : State ambient) : Prop :=
  ∀ coordinate : Fin ambient, state.stamps[coordinate.val] ≤ state.epoch

@[simp] theorem initial_project : project (initial ambient) = empty ambient := by
  simp only [project, initial, empty, Dictionary.mk.injEq]
  constructor
  · apply Vector.ext
    intro index bound
    simp [encoded]
  · trivial

theorem initial_valid : Valid (initial ambient) := by
  intro coordinate
  simp [initial]

def nextQuery (state : State ambient) : State ambient :=
  { state with epoch := state.epoch + 1, coordinates := #[] }

theorem nextQuery_project (state : State ambient) (valid : Valid state) :
    project (nextQuery state) = empty ambient := by
  simp only [project, nextQuery, empty, Dictionary.mk.injEq]
  constructor
  · apply Vector.ext
    intro index bound
    have older := valid ⟨index, bound⟩
    change state.stamps[index] ≤ state.epoch at older
    have different : state.stamps[index] ≠ state.epoch + 1 := by omega
    simp [encoded, different]
  · trivial

theorem nextQuery_valid (state : State ambient) (valid : Valid state) : Valid (nextQuery state) := by
  intro coordinate
  have previous := valid coordinate
  change state.stamps[coordinate.val] ≤ state.epoch + 1
  omega

def touch (state : State ambient) (coordinate : Fin ambient) : State ambient × Nat × Counts :=
  let present := encoded state coordinate
  if present = 0 then
    (⟨state.epoch, state.stamps.set coordinate.val state.epoch,
      state.indices.set coordinate.val (state.coordinates.size + 1), state.coordinates.push coordinate⟩,
      state.coordinates.size, ⟨2, 2, 1, 0, 0⟩)
  else (state, present - 1, ⟨2, 0, 0, 0, 0⟩)

theorem touch_project (state : State ambient) (coordinate : Fin ambient) :
    project (touch state coordinate).1 = (ForestZeroCompile.touch (project state) coordinate).1 ∧
      (touch state coordinate).2.1 = (ForestZeroCompile.touch (project state) coordinate).2.1 := by
  have read : (project state).slots[coordinate.val] = encoded state coordinate := by
    simp [project]
  unfold touch ForestZeroCompile.touch
  rw [read]
  dsimp only
  split_ifs with unseen
  · constructor
    · simp only [project, Dictionary.mk.injEq]
      constructor
      · apply Vector.ext
        intro index bound
        by_cases same : index = coordinate.val
        · subst index
          simp [encoded]
        · simp [encoded, Ne.symm same]
      · trivial
    · rfl
  · exact ⟨rfl, rfl⟩

theorem touch_valid (state : State ambient) (valid : Valid state) (coordinate : Fin ambient) :
    Valid (touch state coordinate).1 := by
  intro other
  unfold touch
  dsimp only
  split_ifs
  · change (state.stamps.set coordinate.val state.epoch)[other.val] ≤ state.epoch
    by_cases same : other.val = coordinate.val
    · simp [same]
    · simpa [same, Ne.symm same] using valid other
  · exact valid other

/-- The executable traversal uses two array reads per occurrence and at most
two writes plus one coordinate append on first touch. It never constructs the
ambient-sized projection used in the refinement theorem. -/
def compileClause (state : State ambient) : Clause (Fin ambient) → State ambient × Clause Nat × Counts
  | [] => (state, [], {})
  | literal :: rest =>
      let touched := touch state literal.1
      let returned := compileClause touched.1 rest
      (returned.1, (touched.2.1, literal.2) :: returned.2.1,
        (touched.2.2.add returned.2.2).add ⟨0, 0, 0, 1, 0⟩)

def compileRows (state : State ambient) : List (Clause (Fin ambient)) →
    State ambient × List (Clause Nat) × Counts
  | [] => (state, [], {})
  | row :: rest =>
      let clause := compileClause state row
      let returned := compileRows clause.1 rest
      (returned.1, clause.2.1 :: returned.2.1,
        (clause.2.2.add returned.2.2).add ⟨0, 0, 0, 0, 1⟩)

theorem compileClause_project (state : State ambient) (clause : Clause (Fin ambient)) :
    project (compileClause state clause).1 = (ForestZeroCompile.compileClause (project state) clause).1 ∧
      (compileClause state clause).2.1 = (ForestZeroCompile.compileClause (project state) clause).2.1 := by
  induction clause generalizing state with
  | nil => exact ⟨rfl, rfl⟩
  | cons literal rest ih =>
      have one := touch_project state literal.1
      have tail := ih (touch state literal.1).1
      simp only [compileClause, ForestZeroCompile.compileClause]
      rw [one.1] at tail
      exact ⟨tail.1, by rw [one.2, tail.2]⟩

theorem compileRows_project (state : State ambient) (rows : List (Clause (Fin ambient))) :
    project (compileRows state rows).1 = (ForestZeroCompile.compileRows (project state) rows).1 ∧
      (compileRows state rows).2.1 = (ForestZeroCompile.compileRows (project state) rows).2.1 := by
  induction rows generalizing state with
  | nil => exact ⟨rfl, rfl⟩
  | cons row rest ih =>
      have one := compileClause_project state row
      have tail := ih (compileClause state row).1
      simp only [compileRows, ForestZeroCompile.compileRows]
      rw [one.1] at tail
      exact ⟨tail.1, by rw [one.2, tail.2]⟩

theorem compileClause_valid (state : State ambient) (valid : Valid state) (clause : Clause (Fin ambient)) :
    Valid (compileClause state clause).1 := by
  induction clause generalizing state with
  | nil => exact valid
  | cons literal rest ih => exact ih _ (touch_valid state valid literal.1)

theorem compileRows_valid (state : State ambient) (valid : Valid state) (rows : List (Clause (Fin ambient))) :
    Valid (compileRows state rows).1 := by
  induction rows generalizing state with
  | nil => exact valid
  | cons row rest ih => exact ih _ (compileClause_valid state valid row)

def work (counts : Counts) : Nat :=
  counts.reads + counts.writes + counts.appends + counts.literalCons + counts.rowCons

@[simp] theorem work_add (left right : Counts) : work (left.add right) = work left + work right := by
  simp only [work, Counts.add]
  omega

theorem touch_work (state : State ambient) (coordinate : Fin ambient) :
    work (touch state coordinate).2.2 ≤ 5 := by
  unfold touch
  dsimp only
  split_ifs <;> simp [work]

theorem compileClause_work (state : State ambient) (clause : Clause (Fin ambient)) :
    work (compileClause state clause).2.2 ≤ 6 * clause.length := by
  induction clause generalizing state with
  | nil => simp [compileClause, work]
  | cons literal rest ih =>
      have one := touch_work state literal.1
      have tail := ih (touch state literal.1).1
      simp only [compileClause, work, Counts.add, List.length_cons] at *
      omega

theorem compileRows_work (state : State ambient) (rows : List (Clause (Fin ambient))) :
    work (compileRows state rows).2.2 ≤ 6 * rows.flatten.length + rows.length := by
  induction rows generalizing state with
  | nil => simp [compileRows, work]
  | cons row rest ih =>
      have one := compileClause_work state row
      have tail := ih (compileClause state row).1
      simp only [compileRows, work, Counts.add, List.flatten_cons,
        List.length_append, List.length_cons] at *
      omega

end Controller.Cost.ForestCompilerDictionary
