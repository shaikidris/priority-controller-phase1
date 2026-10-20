/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ProperBasisConstructionRecipes
import Controller.Cost.ForestClauseProgramConstruction

/-! Witness emission instructions are formed from explicit scalar operands;
the candidate values are read and emitted by the resulting program. -/
namespace Controller.Cost.WitnessEmissionConstruction

open Controller.Cost Controller.Extensions Controller.Extensions.LiteralWitnessEmit
open Controller.Cost.WordConstructionRecipe Controller.Cost.ProperBasisConstructionRecipes
open Controller.Cost.ForestClauseProgramConstruction (environment)

def operand (width entry : Nat) : Operand → List (Instruction width 8) × Nat
  | .one => (evaluate (fun index => Fin.elim0 index) (emitOne.constructionRecipe width), 100)
  | .stored offset => (evaluate (environment [offset]) (emitStored.constructionRecipe width), 100)
  | .selected channel => (evaluate (environment [entry, channel]) (emitSelected.constructionRecipe
    width), 200)

theorem operand_image (width entry : Nat) (value : Operand) :
    (operand width entry value).1 = operandCode (width := width) entry value := by
  have one : evaluate (fun index => Fin.elim0 index) (emitOne.constructionRecipe width) = emitOne
    width := emitOne.constructionRecipe_eq width
  have stored (offset : Nat) : evaluate (environment [offset]) (emitStored.constructionRecipe width)
    = emitStored width offset := emitStored.constructionRecipe_eq width offset
  have selected (channel : Nat) : evaluate (environment [entry, channel])
    (emitSelected.constructionRecipe width) = emitSelected width entry channel :=
    emitSelected.constructionRecipe_eq width entry channel
  cases value <;> simp only [operand, one, stored, selected, operandCode, emitOne, emitStored,
    emitSelected]

def build (width : Nat) : Nat → List Operand → List (Instruction width 8) × Nat
  | _, [] => ([], 1)
  | entry, value :: rest =>
      let head := operand width entry value
      let tail := build width (entry + head.1.length) rest
      (head.1 ++ tail.1, head.2 + tail.2 + 16 * head.1.length + 20)

theorem image (width entry : Nat) (operands : List Operand) :
    (build width entry operands).1 = LiteralWitnessEmit.code (width := width) entry operands := by
  induction operands generalizing entry with
  | nil => rfl
  | cons value rest ih => simp only [build, operand_image, operandCode_length, ih,
    LiteralWitnessEmit.code]

theorem clock (width entry : Nat) (operands : List Operand) :
    (build width entry operands).2 ≤ 500 * operands.length + 1 := by
  induction operands generalizing entry with
  | nil => simp [build]
  | cons value rest ih =>
      have tail := ih (entry + (operand width entry value).1.length)
      have bound : (operand width entry value).2 ≤ 200 := by cases value <;> simp [operand]
      have length : (operand width entry value).1.length ≤ 9 := by
        rw [operand_image, operandCode_length]
        cases value <;> simp [operandSize]
      simp only [build, List.length_cons]
      omega

end Controller.Cost.WitnessEmissionConstruction
