/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ExtensionConstructionRecipes
import Controller.Cost.ForestClauseProgramConstruction
import Controller.Cost.WordConstructionStorage

/-! Relocation reads already formed instruction fields, adds the segment offset
to branch targets and repacks that word. Other fields are copied. The input
instruction stream is charged by its producing stage. -/
namespace Controller.Cost.ProgramRelocationConstruction

open Controller.Cost Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestClauseProgramConstruction (environment)

def recipe (instruction : Instruction width 8) : InstructionRecipe 2 width 8 :=
  match instruction with
  | .branchZero source _ => .branchZero source (.add (.parameter 1) (.parameter 0))
  | _ => .plain instruction

def target (instruction : Instruction width 8) : Nat :=
  match instruction with
  | .branchZero _ address => address.val
  | _ => 0

def form (delta : Nat) (instruction : Instruction width 8) : Instruction width 8 :=
  (recipe instruction).eval (environment [delta, target instruction])

theorem form_image (delta : Nat) (instruction : Instruction width 8) :
    form delta instruction = RawAdapterProgram.relocatedInstruction delta instruction := by
  cases instruction <;> rfl

theorem form_work (instruction : Instruction width 8) : (recipe instruction).work ≤ 12 := by
  cases instruction <;> simp [recipe, InstructionRecipe.work, Expression.work]

def build (delta : Nat) : List (Instruction width 8) → List (Instruction width 8) × Nat
  | [] => ([], 1)
  | instruction :: rest =>
      let tail := build delta rest
      (form delta instruction :: tail.1, (recipe instruction).work + tail.2 + 8)

theorem build_image (delta : Nat) (instructions : List (Instruction width 8)) :
    (build delta instructions).1 = Controller.Extensions.ResidentSegment.code delta instructions := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih => simp only [build, form_image, Controller.Extensions.ResidentSegment.code, List.map_cons] at *; rw [ih]

theorem build_clock (delta : Nat) (instructions : List (Instruction width 8)) :
    (build delta instructions).2 ≤ 20 * instructions.length + 1 := by
  induction instructions with
  | nil => simp [build]
  | cons instruction rest ih =>
      have head := form_work instruction
      simp only [build, List.length_cons]
      omega

inductive Trace (delta : Nat) : List (Instruction width 8) → List (Instruction width 8) → Nat → Nat → Prop
  | nil : Trace delta [] [] 1 16
  | cons {instruction rest output first later p q}
      (formed : WordConstructionStorage.InstructionStorage (environment [delta, target instruction])
        (recipe instruction) (form delta instruction) first p)
      (tail : Trace delta rest output later q) :
      Trace delta (instruction :: rest) (form delta instruction :: output) (first + later + 8)
        (max p (q + 16))

theorem construction (delta : Nat) (instructions : List (Instruction width 8)) :
    ∃ peak, Trace delta instructions (build delta instructions).1 (build delta instructions).2 peak ∧
      peak ≤ 256 * instructions.length + 16 := by
  induction instructions with
  | nil => exact ⟨16, .nil, by simp⟩
  | cons instruction rest ih =>
      obtain ⟨p, formed, bound⟩ := WordConstructionStorage.instruction
        (environment [delta, target instruction]) (recipe instruction)
      obtain ⟨q, remaining, tailBound⟩ := ih
      have head := form_work instruction
      refine ⟨_, .cons formed remaining, ?_⟩
      simp only [List.length_cons]
      exact Nat.max_le.mpr ⟨by omega, by omega⟩

end Controller.Cost.ProgramRelocationConstruction
