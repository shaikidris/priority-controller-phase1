module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ProgramRelocationConstruction

@[expose] public section


/-! The source operand emitter forms literal, read and selected-read blocks
from explicit scalar fields. Choice reads are runtime branches, not decisions
made while constructing the instruction stream. -/
namespace Controller.Cost.SourceOperandConstruction

open Controller.Cost Controller.Extensions
open Controller.Cost.WordConstructionRecipe Controller.Cost.ExtensionConstructionRecipes
open Controller.Cost.ForestClauseProgramConstruction (environment)
open Controller.Extensions.ResolvedSourceEmit

structure Block (width : Nat) where
  values : List Nat
  recipes : List (InstructionRecipe values.length width 8)

def block (width entry : Nat) : Operand width → Block width
  | .literal value => ⟨[value.val], literalOperand.constructionRecipe width⟩
  | .read address offset => ⟨[address, offset.val], readOperand.constructionRecipe width⟩
  | .choice flag left right offset => ⟨[entry, flag, left, right, offset.val], choiceOperand.constructionRecipe width⟩

def Block.image (item : Block width) : List (Instruction width 8) := evaluate (environment item.values) item.recipes

def Block.clock (item : Block width) : Nat := work item.recipes + item.values.length + 16

theorem one_image (width entry : Nat) (operand : Operand width) :
    (block width entry operand).image = oneCode width entry operand := by
  have packed : ∀ value : Word width, word width value.val = value := fun value =>
    Fin.ext (Nat.mod_eq_of_lt value.isLt)
  cases operand with
  | literal value =>
      exact (literalOperand.constructionRecipe_eq width value.val).trans
        (by simp only [literalOperand, oneCode, packed])
  | read address offset =>
      exact (readOperand.constructionRecipe_eq width address offset.val).trans
        (by simp only [readOperand, oneCode, packed])
  | choice flag left right offset =>
      exact (choiceOperand.constructionRecipe_eq width entry flag left right offset.val).trans
        (by simp only [choiceOperand, oneCode, packed])

theorem one_clock (width entry : Nat) (operand : Operand width) : (block width entry operand).clock ≤ 140 := by
  cases operand <;> simp only [block, Block.clock, literalOperand.constructionRecipe_work,
    readOperand.constructionRecipe_work, choiceOperand.constructionRecipe_work, List.length_cons, List.length_nil] <;> omega

def build (width entry : Nat) : List (Operand width) → List (Instruction width 8) × Nat
  | [] => ([], 1)
  | operand :: rest =>
      let current := block width entry operand
      let tail := build width (entry + current.image.length) rest
      (current.image ++ tail.1, current.clock + current.image.length + tail.2 + 32)

theorem build_image (width entry : Nat) (operands : List (Operand width)) :
    (build width entry operands).1 = ResolvedSourceEmit.code width entry operands := by
  induction operands generalizing entry with
  | nil => rfl
  | cons operand rest ih => simp only [build, one_image, ResolvedSourceEmit.code, ih]

theorem build_clock (width entry : Nat) (operands : List (Operand width)) :
    (build width entry operands).2 ≤ 200 * operands.length + 1 := by
  induction operands generalizing entry with
  | nil => simp [build]
  | cons operand rest ih =>
      have head := one_clock width entry operand
      have length := oneCode_length (width := width) (entry := entry) operand
      have tail := ih (entry + (block width entry operand).image.length)
      rw [← one_image width entry operand] at length
      simp only [build, List.length_cons]
      omega

inductive Trace (width : Nat) : Nat → List (Operand width) → List (Instruction width 8) → Nat → Nat → Prop
  | nil (entry) : Trace width entry [] [] 1 32
  | cons {entry operand rest current output first later p q}
      (formed : WordConstructionStorage.Trace (environment (block width entry operand).values)
        (block width entry operand).recipes current first p)
      (tail : Trace width (entry + current.length) rest output later q)
      (copied : CompilerAppendTrace.AppendTrace current output (current ++ output) current.length) :
      Trace width entry (operand :: rest) (current ++ output)
        (first + (block width entry operand).values.length + 16 + current.length + later + 32)
        (max p (q + 16 * current.length + 64))

theorem storage (width entry : Nat) (operands : List (Operand width)) :
    ∃ peak, Trace width entry operands (build width entry operands).1 (build width entry operands).2 peak ∧
      peak ≤ 5000 * operands.length + 32 := by
  induction operands generalizing entry with
  | nil => exact ⟨32, .nil entry, by simp⟩
  | cons operand rest ih =>
      obtain ⟨p, formed, formBound⟩ := WordConstructionStorage.construction
        (environment (block width entry operand).values) (block width entry operand).recipes
      obtain ⟨q, tail, tailBound⟩ := ih (entry + (block width entry operand).image.length)
      have head := one_clock width entry operand
      have length := oneCode_length (width := width) (entry := entry) operand
      rw [← one_image width entry operand] at length
      have recipeBound : work (block width entry operand).recipes ≤ 140 := by
        dsimp only [Block.clock] at head; omega
      refine ⟨_, .cons formed tail (CompilerAppendTrace.append_exists _ _), ?_⟩
      simp only [List.length_cons]
      exact Nat.max_le.mpr ⟨by omega, by omega⟩

end Controller.Cost.SourceOperandConstruction
