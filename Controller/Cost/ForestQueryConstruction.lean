module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ForestConstructionRecipes
public import Controller.Cost.CompilerAppendTrace

@[expose] public section


/-! Charged formation of variable source-literal streams. Fixed templates
use checked first-order recipes; the stream writer forms each block once,
advances its program counter and copies only that block onto the suffix. -/
namespace Controller.Cost.ForestQueryConstruction

open Controller.Cost Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestConstructionRecipes

variable {ambient : Nat}

/-- Recipe formation plus a constant allowance for two source-field reads,
case dispatch, the fixed-size operand environment and counter update. -/
def literalRecipes (width : Nat) (activity positive : Bool) :
    List (InstructionRecipe 2 width 4) :=
  match activity, positive with
  | false, false => channelNegative.constructionRecipe width
  | false, true => channelPositive.constructionRecipe width
  | true, false => activityNegative.constructionRecipe width
  | true, true => activityPositive.constructionRecipe width

def literalEnvironment (base slot : Nat) (index : Fin 2) : Nat :=
  [base, slot].getD index.val 0

theorem literal_image (width base : Nat) (reference : Reference ambient) :
    evaluate (literalEnvironment base reference.slot) (literalRecipes width reference.activity reference.positive) =
      literalCode width base reference := by
  cases reference with
  | mk slot raw activity coordinate positive =>
      cases activity <;> cases positive
      · change evaluate (fun index => [base, slot].getD index.val 0)
          (channelNegative.constructionRecipe width) = _
        exact (channelNegative.constructionRecipe_eq width base slot).trans (by rfl)
      · change evaluate (fun index => [base, slot].getD index.val 0)
          (channelPositive.constructionRecipe width) = _
        exact (channelPositive.constructionRecipe_eq width base slot).trans (by rfl)
      · change evaluate (fun index => [base, slot].getD index.val 0)
          (activityNegative.constructionRecipe width) = _
        exact (activityNegative.constructionRecipe_eq width base slot).trans (by rfl)
      · change evaluate (fun index => [base, slot].getD index.val 0)
          (activityPositive.constructionRecipe width) = _
        exact (activityPositive.constructionRecipe_eq width base slot).trans (by rfl)

theorem literal_work (width : Nat) (reference : Reference ambient) :
    work (literalRecipes width reference.activity reference.positive) ≤ 266 := by
  cases reference.activity <;> cases reference.positive <;>
    simp only [literalRecipes, channelNegative.constructionRecipe_work,
      channelPositive.constructionRecipe_work, activityNegative.constructionRecipe_work,
      activityPositive.constructionRecipe_work] <;> decide

inductive StreamTrace (width : Nat) : Nat → List (Reference ambient) → List (Instruction width 4) → Nat → Prop
  | nil (base) : StreamTrace width base [] [] 1
  | cons (base reference rest code tail formed later)
      (literal : WordConstructionRecipe.Trace (literalEnvironment base reference.slot)
        (literalRecipes width reference.activity reference.positive) code formed)
      (remaining : StreamTrace width (base + code.length) rest tail later)
      (copied : CompilerAppendTrace.AppendTrace code tail (code ++ tail) code.length) :
      StreamTrace width base (reference :: rest) (code ++ tail) (formed + code.length + later + 20)

/-- Both image and cost follow the actual recursion. No second call forms a
provisional literal merely to learn its instruction count. -/
def emit (width : Nat) : Nat → List (Reference ambient) → List (Instruction width 4) × Nat
  | _, [] => ([], 1)
  | base, reference :: rest =>
      let recipes := literalRecipes width reference.activity reference.positive
      let current := evaluate (literalEnvironment base reference.slot) recipes
      let tail := emit width (base + current.length) rest
      (current ++ tail.1, work recipes + current.length + tail.2 + 20)

theorem emit_trace (width base : Nat) (references : List (Reference ambient)) :
    StreamTrace width base references (emit width base references).1 (emit width base references).2 := by
  induction references generalizing base with
  | nil => exact .nil base
  | cons reference rest ih =>
      exact .cons base reference rest _ _ _ _ (WordConstructionRecipe.trace _ _)
        (ih _) (CompilerAppendTrace.append_exists _ _)

theorem emit_image (width base : Nat) (references : List (Reference ambient)) :
    (emit width base references).1 = emitCode width base references := by
  induction references generalizing base with
  | nil => rfl
  | cons reference rest ih => simp only [emit, literal_image, emitCode, ih]

theorem emit_work (width base : Nat) (references : List (Reference ambient)) :
    (emit width base references).2 ≤ 314 * references.length + 1 := by
  induction references generalizing base with
  | nil => simp [emit]
  | cons reference rest ih =>
      have formed := literal_work width reference
      have length : (literalCode width base reference).length ≤ 28 := by
        rw [literalCode_length, readCode_length]
        cases reference.activity <;> decide
      have tail := ih (base + (literalCode width base reference).length)
      simp only [emit, literal_image, List.length_cons] at *
      omega

end Controller.Cost.ForestQueryConstruction
