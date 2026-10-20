module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ForestCompilerQueries

@[expose] public section


/-! Count-only compiler metadata. Native instruction generation needs the
number of distinct coordinates and channel coverage, not a second copy of
local clause labels or an inverse-coordinate array. The executable state is
one epoch table and two counters. Dense dictionaries below are proof views. -/
namespace Controller.Cost.ForestCompilerMarks

open Controller.CNF Controller.Cost.ForestCompilerDictionary

structure State (ambient : Nat) where
  epoch : Nat
  stamps : Vector Nat ambient
  count : Nat

def initial (ambient : Nat) : State ambient := ⟨1, Vector.replicate ambient 0, 0⟩

def begin (state : State ambient) : State ambient :=
  { state with epoch := state.epoch + 1, count := 0 }

def touch (state : State ambient) (coordinate : Fin ambient) : State ambient :=
  if state.stamps[coordinate.val] = state.epoch then state
  else ⟨state.epoch, state.stamps.set coordinate.val state.epoch, state.count + 1⟩

/-- Compression is not called by the executable metadata pass. -/
def compress (state : ForestCompilerDictionary.State ambient) : State ambient :=
  ⟨state.epoch, state.stamps, state.coordinates.size⟩

def Coherent (state : ForestCompilerDictionary.State ambient) : Prop :=
  ∀ coordinate : Fin ambient, state.stamps[coordinate.val] = state.epoch →
    0 < state.indices[coordinate.val]

theorem initial_compress : initial ambient = compress (ForestCompilerDictionary.initial ambient) := rfl

theorem initial_coherent : Coherent (ForestCompilerDictionary.initial ambient) := by
  intro coordinate current
  simp [ForestCompilerDictionary.initial] at current

theorem begin_compress (state : ForestCompilerDictionary.State ambient) :
    begin (compress state) = compress (nextQuery state) := rfl

theorem begin_coherent (state : ForestCompilerDictionary.State ambient) (valid : Valid state) :
    Coherent (nextQuery state) := by
  intro coordinate current
  have older := valid coordinate
  change state.stamps[coordinate.val] = state.epoch + 1 at current
  omega

theorem touch_compress (state : ForestCompilerDictionary.State ambient) (coherent : Coherent state)
    (coordinate : Fin ambient) :
    touch (compress state) coordinate = compress (ForestCompilerDictionary.touch state coordinate).1 ∧
      Coherent (ForestCompilerDictionary.touch state coordinate).1 := by
  by_cases current : state.stamps[coordinate.val] = state.epoch
  · have positive := coherent coordinate current
    have encodedValue : encoded state coordinate = state.indices[coordinate.val] := by simp [encoded, current]
    have nonzero : encoded state coordinate ≠ 0 := by omega
    simp only [touch, compress, current, if_pos, ForestCompilerDictionary.touch, nonzero, if_false]
    exact ⟨trivial, coherent⟩
  · have zero : encoded state coordinate = 0 := by simp [encoded, current]
    constructor
    · simp [touch, compress, current, ForestCompilerDictionary.touch, zero]
    · intro other sameEpoch
      change (ForestCompilerDictionary.touch state coordinate).1.stamps[other.val] =
        (ForestCompilerDictionary.touch state coordinate).1.epoch at sameEpoch
      simp only [ForestCompilerDictionary.touch, zero, if_pos] at sameEpoch ⊢
      by_cases same : other.val = coordinate.val
      · simp [same]
      · have previous : state.stamps[other.val] = state.epoch := by
          simpa [same, Ne.symm same] using sameEpoch
        simpa [same, Ne.symm same] using coherent other previous

/-- The scan carries only the current epoch table and counters. -/
def scan (state : State ambient) : List (Fin ambient) → State ambient
  | [] => state
  | coordinate :: rest => scan (touch state coordinate) rest

theorem scan_append (state : State ambient) (first second : List (Fin ambient)) :
    scan state (first ++ second) = scan (scan state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons coordinate rest ih => exact ih (touch state coordinate)

theorem clause_refines (state : ForestCompilerDictionary.State ambient) (coherent : Coherent state)
    (row : Clause (Fin ambient)) :
    scan (compress state) (row.map Prod.fst) = compress (compileClause state row).1 ∧
      Coherent (compileClause state row).1 := by
  induction row generalizing state with
  | nil => exact ⟨rfl, coherent⟩
  | cons literal rest ih =>
      have current := touch_compress state coherent literal.1
      have tail := ih (ForestCompilerDictionary.touch state literal.1).1 current.2
      simp only [List.map_cons, scan, compileClause]
      rw [current.1]
      exact tail

theorem rows_refine (state : ForestCompilerDictionary.State ambient) (coherent : Coherent state)
    (rows : List (Clause (Fin ambient))) :
    scan (compress state) ((rows.map (List.map Prod.fst)).flatten) = compress (compileRows state rows).1 ∧
      Coherent (compileRows state rows).1 := by
  induction rows generalizing state with
  | nil => exact ⟨rfl, coherent⟩
  | cons row rest ih =>
      have clause := clause_refines state coherent row
      have tail := ih (compileClause state row).1 clause.2
      simp only [List.map_cons, List.flatten_cons, scan_append, compileRows]
      rw [clause.1]
      exact tail

theorem scan_count (state : State ambient) (coordinates : List (Fin ambient)) :
    (scan state coordinates).count ≤ state.count + coordinates.length := by
  induction coordinates generalizing state with
  | nil => simp [scan]
  | cons coordinate rest ih =>
      have tail := ih (touch state coordinate)
      have changed : (touch state coordinate).count ≤ state.count + 1 := by
        unfold touch
        split_ifs <;> simp
      simp only [scan, List.length_cons]
      omega

/-- Each transition reads a source coordinate, advances its list cursor and
performs one epoch lookup/test and at most one stamp write/counter update.
The fixed allowance includes address arithmetic and scalar control fields;
pending input is a shared list suffix. -/
inductive Trace : State ambient → List (Fin ambient) → State ambient → Nat → Prop
  | nil (state) : Trace state [] state 1
  | cons (state coordinate rest final ticks)
      (tail : Trace (touch state coordinate) rest final ticks) :
      Trace state (coordinate :: rest) final (ticks + 32)

theorem scan_trace (state : State ambient) (coordinates : List (Fin ambient)) :
    Trace state coordinates (scan state coordinates) (32 * coordinates.length + 1) := by
  induction coordinates generalizing state with
  | nil => exact .nil state
  | cons coordinate rest ih =>
      simpa only [scan, List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using
        Trace.cons state coordinate rest _ _ (ih (touch state coordinate))

def present (state : State ambient) (index : Nat) : Bool :=
  if valid : index < ambient then state.stamps[index] == state.epoch else false

theorem present_refines (state : ForestCompilerDictionary.State ambient) (coherent : Coherent state)
    (index : Nat) :
    present (compress state) index = true ↔ ForestCompilerQueries.slotAt state index ≠ 0 := by
  by_cases valid : index < ambient
  · by_cases current : state.stamps[index] = state.epoch
    · have nonzero : state.indices[index] ≠ 0 := Nat.ne_of_gt (coherent ⟨index, valid⟩ current)
      simp [present, compress, valid, ForestCompilerQueries.slotAt, encoded, current, nonzero]
    · simp [present, compress, valid, ForestCompilerQueries.slotAt, encoded, current]
  · simp [present, valid, ForestCompilerQueries.slotAt]

def search (state : State ambient) : Nat → Nat → Nat → ForestZeroNonempty.Result × Nat
  | 0, 0, _ => (⟨0, .covered⟩, 1)
  | 0, _ + 1, _ => (⟨0, .exhausted⟩, 1)
  | _ + 1, 0, _ => (⟨0, .covered⟩, 1)
  | budget + 1, channels + 1, offset =>
      if present state offset then
        let tail := search state budget channels (offset + 1)
        (tail.1.bump, tail.2 + 8)
      else (⟨0, .unused⟩, 4)

theorem search_refines (state : ForestCompilerDictionary.State ambient) (coherent : Coherent state)
    (budget channels offset : Nat) :
    (search (compress state) budget channels offset).1 =
      (ForestCompilerQueries.search state budget channels offset).1 := by
  induction budget generalizing channels offset with
  | zero => cases channels <;> rfl
  | succ budget ih =>
      cases channels with
      | zero => rfl
      | succ channels =>
          by_cases seen : present (compress state) offset = true
          · have nonzero := (present_refines state coherent offset).mp seen
            simp only [search, ForestCompilerQueries.search, seen, if_pos, if_neg nonzero]
            exact congrArg ForestZeroNonempty.Result.bump (ih channels (offset + 1))
          · have zero : ForestCompilerQueries.slotAt state offset = 0 := by
              by_contra notZero
              exact seen ((present_refines state coherent offset).mpr notZero)
            simp only [search, ForestCompilerQueries.search, if_neg seen, if_pos zero]

theorem search_work (state : State ambient) (budget channels offset : Nat) :
    (search state budget channels offset).2 ≤ 8 * budget + 4 := by
  induction budget generalizing channels offset with
  | zero => cases channels <;> simp [search]
  | succ budget ih =>
      cases channels with
      | zero => simp [search]
      | succ channels =>
          have tail := ih channels (offset + 1)
          simp only [search]
          split_ifs <;> omega

/-- The scan and bounded channel-coverage pass retain no local row labels. -/
def query (channels : Nat) (state : State ambient) (rows : List (Clause (Fin ambient))) :
    State ambient × ForestZeroNonempty.Result × Nat :=
  let coordinates := (rows.map (List.map Prod.fst)).flatten
  let marked := scan (begin state) coordinates
  let covered := search marked (marked.count + 1) channels 0
  (marked, covered.1, 40 * coordinates.length + 4 * rows.length + covered.2 + 8)

theorem query_refines (channels : Nat) (state : ForestCompilerDictionary.State ambient)
    (valid : Valid state) (rows : List (Clause (Fin ambient))) :
    (query channels (compress state) rows).1 =
      compress (ForestCompilerQueries.query channels state rows).1 ∧
      (query channels (compress state) rows).2.1 =
      (ForestCompilerQueries.query channels state rows).2.1.coverage := by
  have cells := rows_refine (nextQuery state) (begin_coherent state valid) rows
  simp only [query, begin_compress, ForestCompilerQueries.query]
  rw [cells.1]
  exact ⟨rfl, search_refines (compileRows (nextQuery state) rows).1 cells.2 _ _ _⟩

theorem query_work (channels : Nat) (state : State ambient) (rows : List (Clause (Fin ambient))) :
    (query channels state rows).2.2 ≤ 48 * rows.flatten.length + 4 * rows.length + 24 := by
  let coordinates := (rows.map (List.map Prod.fst)).flatten
  have length : coordinates.length = rows.flatten.length := by
    simp [coordinates, List.length_flatten, List.map_map, Function.comp_def]
  have count := scan_count (begin state) coordinates
  have covered := search_work (scan (begin state) coordinates)
    ((scan (begin state) coordinates).count + 1) channels 0
  have cleared : (begin state).count = 0 := rfl
  rw [cleared, Nat.zero_add, length] at count
  simp only [query]
  change 40 * coordinates.length + 4 * rows.length +
    (search (scan (begin state) coordinates) ((scan (begin state) coordinates).count + 1) channels 0).2 + 8 ≤ _
  rw [length]
  omega

theorem query_coherent (channels : Nat) (state : ForestCompilerDictionary.State ambient)
    (valid : ForestCompilerDictionary.Valid state) (rows : List (Clause (Fin ambient))) :
    Coherent (ForestCompilerQueries.query channels state rows).1 :=
  (rows_refine (nextQuery state) (begin_coherent state valid) rows).2

def Valid (state : State ambient) : Prop :=
  ∀ coordinate : Fin ambient, state.stamps[coordinate.val] ≤ state.epoch

theorem initial_valid : Valid (initial ambient) := by
  intro coordinate
  simp [initial]

theorem begin_valid (state : State ambient) (valid : Valid state) : Valid (begin state) := by
  intro coordinate
  have older := valid coordinate
  change state.stamps[coordinate.val] ≤ state.epoch + 1
  omega

theorem touch_valid (state : State ambient) (valid : Valid state) (coordinate : Fin ambient) :
    Valid (touch state coordinate) := by
  intro other
  unfold touch
  split_ifs
  · exact valid other
  · change (state.stamps.set coordinate.val state.epoch)[other.val] ≤ state.epoch
    by_cases same : other.val = coordinate.val
    · simp [same]
    · simpa [same, Ne.symm same] using valid other

/-- Retained storage consists of one mark table, two counters, the unread
coordinate suffix and a fixed control/operand allowance. Tail recursion does
not retain previous versions of the dictionary in continuation frames. -/
def liveWords (_state : State ambient) (pending : List (Fin ambient)) : Nat :=
  ambient + pending.length + 18

inductive SpaceTrace : State ambient → List (Fin ambient) → State ambient → Nat → Nat → Prop
  | nil (state) : SpaceTrace state [] state 1 (liveWords state [])
  | cons (state coordinate rest final ticks peak)
      (tail : SpaceTrace (touch state coordinate) rest final ticks peak) :
      SpaceTrace state (coordinate :: rest) final (ticks + 32)
        (max (liveWords state (coordinate :: rest)) peak)

theorem scan_space (state : State ambient) (coordinates : List (Fin ambient)) :
    ∃ peak, SpaceTrace state coordinates (scan state coordinates) (32 * coordinates.length + 1) peak ∧
      peak ≤ ambient + coordinates.length + 18 := by
  induction coordinates generalizing state with
  | nil => exact ⟨liveWords state [], .nil state, by simp [liveWords]⟩
  | cons coordinate rest ih =>
      obtain ⟨peak, trace, bound⟩ := ih (touch state coordinate)
      refine ⟨max (liveWords state (coordinate :: rest)) peak, ?_, ?_⟩
      · simpa only [scan, List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using
          SpaceTrace.cons state coordinate rest _ _ _ trace
      · simp only [liveWords, List.length_cons]
        exact Nat.max_le.mpr ⟨le_rfl, by omega⟩

end Controller.Cost.ForestCompilerMarks
