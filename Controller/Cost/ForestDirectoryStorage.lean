module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ForestDirectoryConstruction
public import Controller.Cost.WordConstructionStorage

@[expose] public section


/-! Temporary construction storage for source-row directories. Row-length
scans retain source-list tails; generated code and scalar continuation records
are counted by the directory trace. -/
namespace Controller.Cost.ForestDirectoryStorage

open Controller.Cost Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestDirectoryConstruction Controller.Cost.CompilerAppendTrace

inductive Trace (width : Nat) : List (List α) → GateProgram.Code width → Nat → Nat → Prop
  | nil : Trace width [] [] 1 32
  | cons {row rest code output formed later firstPeak tailPeak}
      (counted : LengthTrace row row.length row.length)
      (formedCode : WordConstructionStorage.Trace (environment row.length) (rowCode.constructionRecipe width)
        code formed firstPeak)
      (tail : Trace width rest output later tailPeak)
      (copied : AppendTrace code output (code ++ output) code.length) :
      Trace width (row :: rest) (code ++ output) (row.length + formed + code.length + later + 8)
        (max (firstPeak + 8) (tailPeak + 16 * code.length + 32))

theorem construction (width : Nat) (rows : List (List α)) :
    ∃ peak, Trace width rows (directory width rows).1 (directory width rows).2 peak ∧
      peak ≤ 64 * (directory width rows).2 := by
  induction rows with
  | nil => exact ⟨32, .nil, by simp [directory]⟩
  | cons row rest ih =>
      let current := evaluate (environment row.length) (rowCode.constructionRecipe width)
      obtain ⟨firstPeak, head, headBound⟩ :=
        WordConstructionStorage.construction (environment row.length) (rowCode.constructionRecipe width)
      obtain ⟨tailPeak, tail, tailBound⟩ := ih
      have formed : work (rowCode.constructionRecipe width) = 42 := rowCode.constructionRecipe_work width
      refine ⟨max (firstPeak + 8) (tailPeak + 16 * current.length + 32), ?_, ?_⟩
      · exact .cons (length_exists row) head tail (append_exists _ _)
      · change max (firstPeak + 8) (tailPeak + 16 * current.length + 32) ≤
          64 * (row.length + work (rowCode.constructionRecipe width) + current.length + (directory width rest).2 + 8)
        rw [formed] at headBound ⊢
        exact Nat.max_le.mpr ⟨by omega, by omega⟩

theorem bound (width : Nat) (rows : List (List α)) :
    ∃ peak, Trace width rows (directory width rows).1 (directory width rows).2 peak ∧
      peak ≤ 64 * rows.flatten.length + 3520 * rows.length + 64 := by
  obtain ⟨peak, trace, space⟩ := construction width rows
  have clock := directory_work width rows
  exact ⟨peak, trace, by omega⟩


inductive ProfileTrace : List (List α) → Nat → Nat → Nat → Nat → Prop
  | nil : ProfileTrace [] 0 0 1 32
  | cons {row rest rows literals ticks peak}
      (counted : LengthTrace row row.length row.length)
      (tail : ProfileTrace rest rows literals ticks peak) :
      ProfileTrace (row :: rest) (rows + 1) (row.length + literals) (row.length + ticks + 4) (peak + 16)

theorem profile_space (rows : List (List α)) :
    ∃ peak, ProfileTrace rows (profile rows).1 (profile rows).2.1 (profile rows).2.2 peak ∧
      peak ≤ 16 * rows.length + 32 := by
  induction rows with
  | nil => exact ⟨32, .nil, by simp⟩
  | cons row rest ih =>
      obtain ⟨peak, trace, bound⟩ := ih
      refine ⟨peak + 16, .cons (length_exists row) trace, ?_⟩
      simp only [List.length_cons]
      omega

end Controller.Cost.ForestDirectoryStorage
