/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ProperBasisConstructionRecipes
import Controller.Cost.SourceRepackConstruction

/-! Fixed source interpreters and copy/reclaim continuations for proper-basis
table columns. Construction reads source counts and typed channel IDs only. -/
namespace Controller.Cost.BasisProbeConstruction

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Cost.ForestIndexedOperands Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestClauseProgramConstruction (environment)

inductive Mode where
  | positive | negative | zero
  deriving DecidableEq

def config : Mode → LiteralSourceNode.Mode
  | .positive => LiteralSourceConstruction.positive
  | .negative => LiteralSourceConstruction.negative
  | .zero => LiteralSourceConstruction.zero

def recipes (width : Nat) : Mode → List (InstructionRecipe 5 width 4)
  | .positive => ProperBasisConstructionRecipes.positive.constructionRecipe width
  | .negative => ProperBasisConstructionRecipes.negative.constructionRecipe width
  | .zero => ProperBasisConstructionRecipes.zero.constructionRecipe width

def literalKernel (mode : Mode) (width n : Nat) (rows : List Row) (roots : List Nat) : List
  (Instruction width 4) :=
  evaluate (environment [n, rows.length, (rowChildren rows).length, (rowGuards rows).length,
    roots.length]) (recipes width mode)

theorem literalKernel_image (mode : Mode) (width n : Nat) (rows : List Row) (roots : List Nat) :
    literalKernel mode width n rows roots = (LiteralSourceProbe.kernel (config mode) width n rows
      roots).toList := by
  have layout := UniformSourceConstruction.layout_eq width rows roots (fun _ : Channel n => false)
  cases mode <;> simp only [literalKernel, recipes, config]
  · rw [show evaluate (environment [n, rows.length, (rowChildren rows).length, (rowGuards
    rows).length, roots.length])
        (ProperBasisConstructionRecipes.positive.constructionRecipe width) = _ from
        ProperBasisConstructionRecipes.positive.constructionRecipe_eq width n rows.length
          (rowChildren rows).length (rowGuards rows).length roots.length]
    simp only [ProperBasisConstructionRecipes.positive, layout, LiteralSourceProbe.kernel,
      List.toList_toArray]
  · rw [show evaluate (environment [n, rows.length, (rowChildren rows).length, (rowGuards
    rows).length, roots.length])
        (ProperBasisConstructionRecipes.negative.constructionRecipe width) = _ from
        ProperBasisConstructionRecipes.negative.constructionRecipe_eq width n rows.length
          (rowChildren rows).length (rowGuards rows).length roots.length]
    simp only [ProperBasisConstructionRecipes.negative, layout, LiteralSourceProbe.kernel,
      List.toList_toArray]
  · rw [show evaluate (environment [n, rows.length, (rowChildren rows).length, (rowGuards
    rows).length, roots.length])
        (ProperBasisConstructionRecipes.zero.constructionRecipe width) = _ from
        ProperBasisConstructionRecipes.zero.constructionRecipe_eq width n rows.length
          (rowChildren rows).length (rowGuards rows).length roots.length]
    simp only [ProperBasisConstructionRecipes.zero, layout, LiteralSourceProbe.kernel,
      List.toList_toArray]

def literal (mode : Mode) (width n : Nat) (rows : List Row) (roots : List Nat) (entry done : Nat) :
  List (Instruction width 8) × Nat :=
  let kernel := literalKernel mode width n rows roots
  let round := ProgramRelocationConstruction.build entry (kernel.map RegisterWiden.widenInstruction)
  let base := SharedReusableProbe.tableSize width n rows roots
  let copy := StackPacketConstruction.copy width (entry + 117) (entry + 127) base rows.length
  let reclaim := StackPacketConstruction.reclaim width (entry + 127) done rows.length
  let image := round.1 ++ copy ++ reclaim
  (image, work (recipes width mode) + round.2 + 16 * image.length +
    100 * (n + rows.length + (rowChildren rows).length + (rowGuards rows).length + roots.length +
      1))

theorem literal_image (mode : Mode) (width n : Nat) (rows : List Row) (roots : List Nat) (entry done
  : Nat) :
    (literal mode width n rows roots entry done).1 = (LiteralSourceProbe.code (config mode) width n
      rows roots entry done).toList := by
  simp only [literal, literalKernel_image, ProgramRelocationConstruction.build_image,
    StackPacketConstruction.copy_image, StackPacketConstruction.reclaim_image,
      LiteralSourceProbe.code,
    Array.toList_append, RegisterWiden.widenProgram, Array.toList_map, ResidentSegment.code,
    RawAdapterProgram.relocatedInstruction, List.append_assoc]

def monotone (width n : Nat) (rows : List Row) (roots : List Nat) (entry done : Nat) : List
  (Instruction width 8) × Nat :=
  let round := SupportControllerConstruction.sourceRound width n (UniformDAGRun.packetHeaderHeap
    width n rows roots) rows roots entry
  let base := SharedReusableProbe.tableSize width n rows roots
  let copy := StackPacketConstruction.copy width (entry + 126) (entry + 136) base rows.length
  let reclaim := StackPacketConstruction.reclaim width (entry + 136) done rows.length
  let image := round.1 ++ copy ++ reclaim
  (image, round.2 + 16 * image.length + 1000)

theorem monotone_image (width n : Nat) (rows : List Row) (roots : List Nat) (entry done : Nat) :
    (monotone width n rows roots entry done).1 = (SharedTableProbe.code width n rows roots entry
      done).toList := by
  simp only [monotone, SupportControllerConstruction.sourceRound_image,
    StackPacketConstruction.copy_image,
    StackPacketConstruction.reclaim_image, SharedTableProbe.code, Array.toList_append,
      List.append_assoc]
  rfl

theorem literal_clock (mode : Mode) (width n : Nat) (rows : List Row) (roots : List Nat) (entry done
  : Nat) :
    (literal mode width n rows roots entry done).2 ≤
      30000 + 1000 * (n + rows.length + (rowChildren rows).length + (rowGuards rows).length +
        roots.length) := by
  have recipeWork : work (recipes width mode) ≤ 5000 := by
    cases mode <;> simp only [recipes,
      ProperBasisConstructionRecipes.positive.constructionRecipe_work,
      ProperBasisConstructionRecipes.negative.constructionRecipe_work,
        ProperBasisConstructionRecipes.zero.constructionRecipe_work] <;> omega
  have kernelSize : (literalKernel mode width n rows roots).length = 117 := by
    rw [literalKernel_image]
    simp only [Array.length_toList, LiteralSourceProbe.kernel_size]
  have relocated := ProgramRelocationConstruction.build_clock entry
    ((literalKernel mode width n rows roots).map RegisterWiden.widenInstruction)
  simp only [List.length_map, kernelSize] at relocated
  have length : (literal mode width n rows roots entry done).1.length = 134 := by
    rw [literal_image]
    simp only [Array.length_toList, LiteralSourceProbe.code_size]
  change _ + _ + 16 * (literal mode width n rows roots entry done).1.length + _ ≤ _
  omega

theorem monotone_clock (width n : Nat) (rows : List Row) (roots : List Nat) (entry done : Nat) :
    (monotone width n rows roots entry done).2 ≤
      30000 + 1000 * (n + rows.length + (rowChildren rows).length + (rowGuards rows).length +
        roots.length) := by
  have round := SupportControllerConstruction.sourceRound_clock width n
    (UniformDAGRun.packetHeaderHeap width n rows roots) rows roots entry
  have length : (monotone width n rows roots entry done).1.length = 143 := by
    rw [monotone_image]
    simp only [Array.length_toList, SharedTableProbe.code_size]
  change _ + 16 * (monotone width n rows roots entry done).1.length + 1000 ≤ _
  omega

end Controller.Cost.BasisProbeConstruction
