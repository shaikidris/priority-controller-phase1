module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ForestQueryConstruction

@[expose] public section


/-! Variable row-directory formation. Row lengths are obtained by a charged
source traversal and embedded using a fixed checked instruction recipe. -/
namespace Controller.Cost.ForestDirectoryConstruction

open Controller.Cost Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestZeroQuery Controller.Cost.CompilerAppendTrace

def rowCode (width count : Nat) : GateProgram.Code width :=
  [.constant 2 (word width count)] ++ boundaryCode width

derive_word_recipe rowCode

def environment (count : Nat) (index : Fin 1) : Nat := [count].getD index.val 0

def directory (width : Nat) : List (List α) → GateProgram.Code width × Nat
  | [] => ([], 1)
  | row :: rest =>
      let count := row.length
      let current := evaluate (environment count) (rowCode.constructionRecipe width)
      let tail := directory width rest
      (current ++ tail.1, count + work (rowCode.constructionRecipe width) + current.length + tail.2 + 8)

inductive Trace (width : Nat) : List (List α) → GateProgram.Code width → Nat → Prop
  | nil : Trace width [] [] 1
  | cons (row rest count code tail first later)
      (counted : LengthTrace row count count)
      (formed : WordConstructionRecipe.Trace (environment count) (rowCode.constructionRecipe width) code first)
      (remaining : Trace width rest tail later)
      (copied : AppendTrace code tail (code ++ tail) code.length) :
      Trace width (row :: rest) (code ++ tail) (count + first + code.length + later + 8)

theorem row_image (width count : Nat) :
    evaluate (environment count) (rowCode.constructionRecipe width) = rowCode width count := by
  change evaluate (fun index => [count].getD index.val 0) (rowCode.constructionRecipe width) = _
  exact rowCode.constructionRecipe_eq width count

theorem directory_trace (width : Nat) (rows : List (List α)) :
    Trace width rows (directory width rows).1 (directory width rows).2 := by
  induction rows with
  | nil => exact .nil
  | cons row rest ih =>
      have counted := length_exists row
      exact .cons row rest _ _ _ _ _ counted (WordConstructionRecipe.trace _ _) ih (append_exists _ _)

theorem directory_image (width : Nat) (rows : List (List α)) :
    (directory width rows).1 = rows.flatMap (fun row => rowCode width row.length) := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp only [directory, row_image, List.flatMap_cons, ih]

theorem directory_work (width : Nat) (rows : List (List α)) :
    (directory width rows).2 ≤ rows.flatten.length + 55 * rows.length + 1 := by
  induction rows with
  | nil => simp [directory]
  | cons row rest ih =>
      simp only [directory, row_image, rowCode.constructionRecipe_work, rowCode,
        List.length_append, List.length_cons, List.length_nil, boundaryCode_length,
        List.flatten_cons] at *
      omega

/-- The source profile pass includes the complete traversal of each row. -/
def profile : List (List α) → Nat × Nat × Nat
  | [] => (0, 0, 1)
  | row :: rest =>
      let count := row.length
      let tail := profile rest
      (tail.1 + 1, count + tail.2.1, count + tail.2.2 + 4)

theorem profile_exact (rows : List (List α)) :
    (profile rows).1 = rows.length ∧ (profile rows).2.1 = rows.flatten.length ∧
      (profile rows).2.2 = rows.flatten.length + 4 * rows.length + 1 := by
  induction rows with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons row rest ih =>
      simp only [profile, List.length_cons, List.flatten_cons, List.length_append]
      obtain ⟨a, b, c⟩ := ih
      rw [a, b, c]
      omega

end Controller.Cost.ForestDirectoryConstruction
