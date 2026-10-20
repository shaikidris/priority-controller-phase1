module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ForestCompilerMarks

@[expose] public section


/-! Transient storage of the count-only metadata pass. Coverage recursion
shares a read-only mark table; a continuation stores scalar words rather than
copying the ambient array. -/
namespace Controller.Cost.ForestMarkStorage

open Controller.CNF Controller.Cost Controller.Cost.ForestCompilerMarks

inductive CoverageTrace (state : ForestCompilerMarks.State ambient) :
    Nat → Nat → Nat → ForestZeroNonempty.Result → Nat → Nat → Prop
  | empty : CoverageTrace state 0 0 offset ⟨0, .covered⟩ 1 (ambient + 12)
  | exhausted : CoverageTrace state 0 (channels + 1) offset ⟨0, .exhausted⟩ 1 (ambient + 12)
  | covered : CoverageTrace state (budget + 1) 0 offset ⟨0, .covered⟩ 1 (ambient + 12)
  | unused (missing : present state offset = false) :
      CoverageTrace state (budget + 1) (channels + 1) offset ⟨0, .unused⟩ 4 (ambient + 12)
  | next {result ticks peak} (seen : present state offset = true)
      (tail : CoverageTrace state budget channels (offset + 1) result ticks peak) :
      CoverageTrace state (budget + 1) (channels + 1) offset result.bump (ticks + 8) (peak + 8)

theorem coverage (state : ForestCompilerMarks.State ambient) (budget channels offset : Nat) :
    ∃ peak, CoverageTrace state budget channels offset (search state budget channels offset).1
      (search state budget channels offset).2 peak ∧ peak ≤ ambient + 12 + 8 * budget := by
  induction budget generalizing channels offset with
  | zero =>
      cases channels with
      | zero => exact ⟨ambient + 12, .empty, by omega⟩
      | succ channels => exact ⟨ambient + 12, .exhausted, by omega⟩
  | succ budget ih =>
      cases channels with
      | zero => exact ⟨ambient + 12, .covered, by omega⟩
      | succ channels =>
          cases seen : present state offset with
          | false =>
              exact ⟨ambient + 12, by simpa only [search, seen, Bool.false_eq_true, if_false] using
                (CoverageTrace.unused (budget := budget) (channels := channels) seen), by omega⟩
          | true =>
              obtain ⟨peak, trace, bound⟩ := ih channels (offset + 1)
              refine ⟨peak + 8, ?_, by omega⟩
              simpa only [search, seen, if_true] using (CoverageTrace.next seen trace)

/-- Both actual metadata stages are accounted for. Input clause rows are
read-only; the coordinate projection and fixed control words are included in
the displayed query storage envelope. -/
theorem query (channels : Nat) (state : ForestCompilerMarks.State ambient)
    (rows : List (Clause (Fin ambient))) :
    let coordinates := (rows.map (List.map Prod.fst)).flatten
    let marked := scan (begin state) coordinates
    ∃ scanPeak coveragePeak,
      SpaceTrace (begin state) coordinates marked (32 * coordinates.length + 1) scanPeak ∧
      CoverageTrace marked (marked.count + 1) channels 0
        (ForestCompilerMarks.query channels state rows).2.1
        (search marked (marked.count + 1) channels 0).2 coveragePeak ∧
      max scanPeak coveragePeak + 4 * rows.length + 8 * rows.flatten.length + 32 ≤
        ambient + 20 * rows.flatten.length + 4 * rows.length + 64 := by
  intro coordinates marked
  obtain ⟨scanPeak, scanTrace, scanBound⟩ := scan_space (begin state) coordinates
  obtain ⟨coveragePeak, coverageTrace, coverageBound⟩ := coverage marked (marked.count + 1) channels 0
  have length : coordinates.length = rows.flatten.length := by
    simp [coordinates, List.length_flatten, List.map_map, Function.comp_def]
  have count := scan_count (begin state) coordinates
  change marked.count ≤ 0 + coordinates.length at count
  rw [Nat.zero_add, length] at count
  rw [length] at scanBound
  refine ⟨scanPeak, coveragePeak, scanTrace, coverageTrace, ?_⟩
  have peakBound : max scanPeak coveragePeak ≤ ambient + 12 * rows.flatten.length + 32 :=
    Nat.max_le.mpr ⟨by omega, by omega⟩
  omega

end Controller.Cost.ForestMarkStorage
