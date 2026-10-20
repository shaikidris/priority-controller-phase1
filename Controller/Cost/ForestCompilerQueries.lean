/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ForestCompilerDictionary
import Controller.Cost.ForestZeroNonempty

/-! Root-local compiler metadata with one shared ambient dictionary. Local
rows, local counts and channel coverage are computed in occurrence order. A
new query changes the epoch without clearing either ambient array. -/
namespace Controller.Cost.ForestCompilerQueries

open Controller.CNF Controller.Cost.ForestCompilerDictionary
open Controller.Cost.ForestZeroCompile

variable {ambient : Nat}

def slotAt (state : ForestCompilerDictionary.State ambient) (index : Nat) : Nat :=
  if valid : index < ambient then encoded state ⟨index, valid⟩ else 0

@[simp] theorem slotAt_project (state : ForestCompilerDictionary.State ambient) (index : Nat) :
    ForestZeroNonempty.slotAt (project state) index = slotAt state index := by
  unfold ForestZeroNonempty.slotAt slotAt
  split_ifs <;> simp [project]

def search (state : ForestCompilerDictionary.State ambient) :
    Nat → Nat → Nat → ForestZeroNonempty.Result × Nat
  | 0, 0, _ => (⟨0, .covered⟩, 1)
  | 0, _ + 1, _ => (⟨0, .exhausted⟩, 1)
  | _ + 1, 0, _ => (⟨0, .covered⟩, 1)
  | budget + 1, channels + 1, offset =>
      if slotAt state offset = 0 then (⟨0, .unused⟩, 4)
      else
        let tail := search state budget channels (offset + 1)
        (tail.1.bump, tail.2 + 8)

theorem search_project (state : ForestCompilerDictionary.State ambient) (budget channels offset : Nat) :
    (search state budget channels offset).1 = ForestZeroNonempty.search (project state) budget channels offset := by
  induction budget generalizing channels offset with
  | zero => cases channels <;> rfl
  | succ budget ih =>
      cases channels with
      | zero => rfl
      | succ channels =>
          simp only [search, ForestZeroNonempty.search, slotAt_project]
          split_ifs
          · rfl
          · exact congrArg ForestZeroNonempty.Result.bump (ih channels (offset + 1))

theorem search_work (state : ForestCompilerDictionary.State ambient) (budget channels offset : Nat) :
    (search state budget channels offset).2 ≤ 8 * budget + 4 := by
  induction budget generalizing channels offset with
  | zero => cases channels <;> simp [search]
  | succ budget ih =>
      cases channels with
      | zero => simp [search]
      | succ channels =>
          simp only [search]
          split_ifs
          · omega
          · have tail := ih channels (offset + 1)
            dsimp only
            omega

theorem touch_size (state : ForestCompilerDictionary.State ambient) (coordinate : Fin ambient) :
    (ForestCompilerDictionary.touch state coordinate).1.coordinates.size ≤ state.coordinates.size + 1 := by
  unfold ForestCompilerDictionary.touch
  dsimp only
  split_ifs <;> simp

theorem compileClause_size (state : ForestCompilerDictionary.State ambient) (clause : Clause (Fin ambient)) :
    (ForestCompilerDictionary.compileClause state clause).1.coordinates.size ≤ state.coordinates.size + clause.length := by
  induction clause generalizing state with
  | nil => simp [ForestCompilerDictionary.compileClause]
  | cons literal rest ih =>
      have one := touch_size state literal.1
      have tail := ih (ForestCompilerDictionary.touch state literal.1).1
      simp only [ForestCompilerDictionary.compileClause, List.length_cons]
      omega

theorem compileRows_size (state : ForestCompilerDictionary.State ambient) (rows : List (Clause (Fin ambient))) :
    (ForestCompilerDictionary.compileRows state rows).1.coordinates.size ≤ state.coordinates.size + rows.flatten.length := by
  induction rows generalizing state with
  | nil => simp [ForestCompilerDictionary.compileRows]
  | cons row rest ih =>
      have one := compileClause_size state row
      have tail := ih (ForestCompilerDictionary.compileClause state row).1
      simp only [ForestCompilerDictionary.compileRows, List.flatten_cons, List.length_append]
      omega

structure Summary (ambient : Nat) where
  coordinates : Array (Fin ambient)
  rows : List (Clause Nat)
  coverage : ForestZeroNonempty.Result

/-- The result stores only local data, not a fresh copy of either ambient array. -/
def query (channels : Nat) (state : ForestCompilerDictionary.State ambient)
    (rows : List (Clause (Fin ambient))) : ForestCompilerDictionary.State ambient × Summary ambient × Nat :=
  let started := nextQuery state
  let compiled := ForestCompilerDictionary.compileRows started rows
  let covered := search compiled.1 (compiled.1.coordinates.size + 1) channels 0
  (compiled.1, ⟨compiled.1.coordinates, compiled.2.1, covered.1⟩,
    work compiled.2.2 + covered.2 + 4)

theorem query_project (channels : Nat) (state : ForestCompilerDictionary.State ambient)
    (valid : Valid state) (rows : List (Clause (Fin ambient))) :
    let compiled := ForestZeroCompile.compileRows (empty ambient) rows
    (query channels state rows).2.1.coordinates = compiled.1.coordinates ∧
      (query channels state rows).2.1.rows = compiled.2.1 ∧
      (query channels state rows).2.1.coverage =
        ForestZeroNonempty.search compiled.1 (compiled.1.coordinates.size + 1) channels 0 := by
  intro compiled
  have same := ForestCompilerDictionary.compileRows_project (nextQuery state) rows
  rw [nextQuery_project state valid] at same
  have counts := congrArg Dictionary.coordinates same.1
  simp only [project] at counts
  unfold query
  dsimp only
  exact ⟨counts, same.2, by rw [search_project, same.1, counts]⟩

theorem query_valid (channels : Nat) (state : ForestCompilerDictionary.State ambient)
    (valid : Valid state) (rows : List (Clause (Fin ambient))) : Valid (query channels state rows).1 :=
  ForestCompilerDictionary.compileRows_valid (nextQuery state) (nextQuery_valid state valid) rows

theorem query_work (channels : Nat) (state : ForestCompilerDictionary.State ambient)
    (rows : List (Clause (Fin ambient))) :
    (query channels state rows).2.2 ≤ 14 * rows.flatten.length + rows.length + 16 := by
  have compileCost := ForestCompilerDictionary.compileRows_work (nextQuery state) rows
  have count := compileRows_size (nextQuery state) rows
  have scan := search_work (ForestCompilerDictionary.compileRows (nextQuery state) rows).1
    ((ForestCompilerDictionary.compileRows (nextQuery state) rows).1.coordinates.size + 1) channels 0
  have cleared : (nextQuery state).coordinates.size = 0 := rfl
  rw [cleared, Nat.zero_add] at count
  unfold query
  dsimp only
  omega

def queries (channels : Nat) (state : ForestCompilerDictionary.State ambient) :
    List (List (Clause (Fin ambient))) → ForestCompilerDictionary.State ambient × List (Summary ambient) × Nat
  | [] => (state, [], 0)
  | rows :: rest =>
      let one := query channels state rows
      let tail := queries channels one.1 rest
      (tail.1, one.2.1 :: tail.2.1, one.2.2 + tail.2.2 + 1)

def referenceSummary (channels : Nat) (rows : List (Clause (Fin ambient))) : Summary ambient :=
  let compiled := ForestZeroCompile.compileRows (empty ambient) rows
  ⟨compiled.1.coordinates, compiled.2.1,
    ForestZeroNonempty.search compiled.1 (compiled.1.coordinates.size + 1) channels 0⟩

theorem queries_project (channels : Nat) (state : ForestCompilerDictionary.State ambient)
    (valid : Valid state) (packets : List (List (Clause (Fin ambient)))) :
    (queries channels state packets).2.1 = packets.map (referenceSummary channels) ∧
      Valid (queries channels state packets).1 := by
  induction packets generalizing state with
  | nil => exact ⟨rfl, valid⟩
  | cons rows rest ih =>
      have one := query_project channels state valid rows
      have tail := ih (query channels state rows).1 (query_valid channels state valid rows)
      constructor
      · simp only [queries, List.map_cons]
        rw [tail.1]
        congr 1
        cases fields : (query channels state rows).2.1 with
        | mk coordinates output coverage =>
            simp only [fields] at one
            simp only [referenceSummary, Summary.mk.injEq]
            exact ⟨one.1, one.2.1, one.2.2⟩
      · exact tail.2

theorem queries_work (channels : Nat) (state : ForestCompilerDictionary.State ambient)
    (packets : List (List (Clause (Fin ambient)))) :
    (queries channels state packets).2.2 ≤
      14 * packets.flatten.flatten.length + packets.flatten.length + 17 * packets.length := by
  induction packets generalizing state with
  | nil => simp [queries]
  | cons rows rest ih =>
      have one := query_work channels state rows
      have tail := ih (query channels state rows).1
      simp only [queries, List.flatten_cons, List.flatten_append, List.length_append, List.length_cons]
      omega

end Controller.Cost.ForestCompilerQueries
