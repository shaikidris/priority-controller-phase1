module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ForestStreamingConstruction

@[expose] public section


/-! Scalar range invariants of the source compiler's shared mark table.
An epoch advances once per query; counts are reset and bounded by the actual
literal stream. These are word operands rather than unbounded answer data. -/
namespace Controller.Cost.ForestCompilerRanges

open Controller.Cost Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroAdmissibleCaller

variable {ambient : Nat}

theorem touch_epoch (state : ForestCompilerMarks.State ambient) (coordinate : Fin ambient) :
    (ForestCompilerMarks.touch state coordinate).epoch = state.epoch := by
  unfold ForestCompilerMarks.touch
  split_ifs <;> rfl

theorem scan_epoch (state : ForestCompilerMarks.State ambient) (coordinates : List (Fin ambient)) :
    (ForestCompilerMarks.scan state coordinates).epoch = state.epoch := by
  induction coordinates generalizing state with
  | nil => rfl
  | cons coordinate rest ih =>
      rw [ForestCompilerMarks.scan, ih, touch_epoch]

theorem query_epoch (channels : Nat) (state : ForestCompilerMarks.State ambient)
    (rows : List (Controller.CNF.Clause (Fin ambient))) :
    (ForestCompilerMarks.query channels state rows).1.epoch = state.epoch + 1 := by
  exact scan_epoch (ForestCompilerMarks.begin state) _

theorem query_count (channels : Nat) (state : ForestCompilerMarks.State ambient)
    (rows : List (Controller.CNF.Clause (Fin ambient))) :
    (ForestCompilerMarks.query channels state rows).1.count ≤ rows.flatten.length := by
  have count := ForestCompilerMarks.scan_count (ForestCompilerMarks.begin state) ((rows.map (List.map Prod.fst)).flatten)
  have length : ((rows.map (List.map Prod.fst)).flatten).length = rows.flatten.length := by
    simp [List.length_flatten, List.map_map, Function.comp_def]
  simpa only [ForestCompilerMarks.query, ForestCompilerMarks.begin, Nat.zero_add, length] using count

theorem step_epoch (protectedEnd channels : Nat) (state : ForestStreamingConstruction.State ambient width)
    (refs : List (List (Reference ambient))) :
    (ForestStreamingConstruction.step protectedEnd channels state refs).marks.epoch = state.marks.epoch + 1 := by
  exact query_epoch channels state.marks _

theorem step_count (protectedEnd channels : Nat) (state : ForestStreamingConstruction.State ambient width)
    (refs : List (List (Reference ambient))) :
    (ForestStreamingConstruction.step protectedEnd channels state refs).marks.count ≤ refs.flatten.length := by
  have count := query_count channels state.marks (ForestZeroAssembly.originalRows (reservedReferences refs))
  simpa only [ForestStreamingConstruction.step, ForestZeroAssembly.originalRows, reservedReferences,
    List.map_append, List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.length_append, List.length_nil, Nat.add_zero, List.length_flatten, List.map_map, Function.comp_def,
    List.length_map, List.map_nil, List.map_cons, List.sum_cons, List.sum_nil] using count

theorem run_epoch (protectedEnd channels : Nat) (state : ForestStreamingConstruction.State ambient width)
    (packets : List (List (List (Reference ambient)))) :
    (ForestStreamingConstruction.run protectedEnd channels state packets).marks.epoch = state.marks.epoch + packets.length := by
  induction packets generalizing state with
  | nil => simp [ForestStreamingConstruction.run]
  | cons refs rest ih =>
      rw [ForestStreamingConstruction.run, ih, step_epoch]
      simp only [List.length_cons]
      omega

theorem run_count (protectedEnd channels : Nat) (state : ForestStreamingConstruction.State ambient width)
    (packets : List (List (List (Reference ambient)))) :
    (ForestStreamingConstruction.run protectedEnd channels state packets).marks.count ≤
      state.marks.count + packets.flatten.flatten.length := by
  induction packets generalizing state with
  | nil => simp [ForestStreamingConstruction.run]
  | cons refs rest ih =>
      have one := step_count protectedEnd channels state refs
      have tail := ih (ForestStreamingConstruction.step protectedEnd channels state refs)
      simp only [ForestStreamingConstruction.run, List.flatten_cons, List.flatten_append, List.length_append]
      omega


theorem scan_valid (state : ForestCompilerMarks.State ambient) (valid : ForestCompilerMarks.Valid state)
    (coordinates : List (Fin ambient)) : ForestCompilerMarks.Valid (ForestCompilerMarks.scan state coordinates) := by
  induction coordinates generalizing state with
  | nil => exact valid
  | cons coordinate rest ih =>
      exact ih (ForestCompilerMarks.touch state coordinate) (ForestCompilerMarks.touch_valid state valid coordinate)

theorem query_valid (channels : Nat) (state : ForestCompilerMarks.State ambient)
    (valid : ForestCompilerMarks.Valid state) (rows : List (Controller.CNF.Clause (Fin ambient))) :
    ForestCompilerMarks.Valid (ForestCompilerMarks.query channels state rows).1 :=
  scan_valid (ForestCompilerMarks.begin state) (ForestCompilerMarks.begin_valid state valid) _

theorem run_valid (protectedEnd channels : Nat) (state : ForestStreamingConstruction.State ambient width)
    (valid : ForestCompilerMarks.Valid state.marks) (packets : List (List (List (Reference ambient)))) :
    ForestCompilerMarks.Valid (ForestStreamingConstruction.run protectedEnd channels state packets).marks := by
  induction packets generalizing state with
  | nil => exact valid
  | cons refs rest ih =>
      exact ih (ForestStreamingConstruction.step protectedEnd channels state refs) (query_valid channels state.marks valid _)

/-- All shared-table counters and stamps fit the working word. The capacity is
original-source based; no per-query fresh ambient allocation is assumed. -/
theorem initial_word_ranges (protectedEnd channels entry inputSize : Nat)
    (packets : List (List (List (Reference ambient)))) (coordinates : ambient ≤ inputSize)
    (queries : packets.length ≤ inputSize) (literals : packets.flatten.flatten.length ≤ 8 * inputSize)
    (capacity : 256 * (inputSize + 1) < 2 ^ width) :
    let initial := ForestStreamingConstruction.initial ambient width entry
    let final := ForestStreamingConstruction.run protectedEnd channels initial packets
    final.marks.epoch < 2 ^ width ∧ final.marks.count < 2 ^ width ∧
      (∀ coordinate : Fin ambient, final.marks.stamps[coordinate.val] < 2 ^ width) ∧
      (∀ coordinate : Fin ambient, coordinate.val < 2 ^ width) := by
  intro initial final
  have epoch := run_epoch protectedEnd channels initial packets
  have count := run_count protectedEnd channels initial packets
  have valid := run_valid protectedEnd channels initial ForestCompilerMarks.initial_valid packets
  change final.marks.epoch = 1 + packets.length at epoch
  change final.marks.count ≤ 0 + packets.flatten.flatten.length at count
  have epochFits : final.marks.epoch < 2 ^ width := by omega
  have countFits : final.marks.count < 2 ^ width := by omega
  refine ⟨epochFits, countFits, ?_, ?_⟩
  · intro coordinate
    exact (valid coordinate).trans_lt epochFits
  · intro coordinate
    have bounded := coordinate.isLt
    omega

end Controller.Cost.ForestCompilerRanges
