module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.BasisProbeConstruction

@[expose] public section


/-! Singleton column schedules form and relocate one fixed source interpreter
per channel. Column values are produced only by fetched execution. -/
namespace Controller.Cost.BasisColumnConstruction

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Cost.ForestIndexedOperands Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestClauseProgramConstruction (environment)

def candidateOne (width base : Nat) : List (Instruction width 8) := (SharedCandidateSet.code width
  base true).toList

def candidateZero (width base : Nat) : List (Instruction width 8) := (SharedCandidateSet.code width
  base false).toList

derive_extension_recipe candidateOne

derive_extension_recipe candidateZero

def step (mode : Option BasisProbeConstruction.Mode) (width n : Nat) (rows : List Row) (roots : List
  Nat)
    (channel : Fin n) (entry : Nat) : List (Instruction width 8) × Nat :=
  let base := (cacheHeap width (UniformDAGRun.packetHeaderHeap width n rows roots) rows roots).size
  let first := evaluate (environment [base]) (candidateOne.constructionRecipe width)
  let last := evaluate (environment [base]) (candidateZero.constructionRecipe width)
  let probe := match mode with
    | none => BasisProbeConstruction.monotone width n rows roots (entry + 5) (entry + 148)
    | some value => BasisProbeConstruction.literal value width n rows roots (entry + 5) (entry +
      139)
  let image := [.constant 4 (word width channel.val)] ++ first ++ probe.1 ++ last
  (image, probe.2 + 16 * image.length + 1000 * (n + rows.length + (rowChildren rows).length +
    (rowGuards rows).length + roots.length + 1))

theorem step_monotone (width n : Nat) (rows : List Row) (roots : List Nat) (channel : Fin n) (entry
  : Nat) :
    (step none width n rows roots channel entry).1 = (SharedTableBatch.stepCode width n rows roots
      channel entry).toList := by
  have one (base : Nat) : evaluate (environment [base]) (candidateOne.constructionRecipe width) =
    candidateOne width base := candidateOne.constructionRecipe_eq width base
  have zero (base : Nat) : evaluate (environment [base]) (candidateZero.constructionRecipe width) =
    candidateZero width base := candidateZero.constructionRecipe_eq width base
  simp only [step, one, zero, BasisProbeConstruction.monotone_image, candidateOne, candidateZero,
    SharedTableBatch.stepCode, Array.toList_append, List.toList_toArray, List.append_assoc]

theorem step_literal (mode : BasisProbeConstruction.Mode) (width n : Nat) (rows : List Row) (roots :
  List Nat) (channel : Fin n) (entry : Nat) :
    (step (some mode) width n rows roots channel entry).1 = (LiteralSourceBatch.stepCode
      (BasisProbeConstruction.config mode) width n rows roots channel entry).toList := by
  have one (base : Nat) : evaluate (environment [base]) (candidateOne.constructionRecipe width) =
    candidateOne width base := candidateOne.constructionRecipe_eq width base
  have zero (base : Nat) : evaluate (environment [base]) (candidateZero.constructionRecipe width) =
    candidateZero width base := candidateZero.constructionRecipe_eq width base
  simp only [step, one, zero, BasisProbeConstruction.literal_image, candidateOne, candidateZero,
    LiteralSourceBatch.stepCode, Array.toList_append, List.toList_toArray, List.append_assoc]

def build (mode : Option BasisProbeConstruction.Mode) (width n : Nat) (rows : List Row) (roots :
  List Nat) : Nat → List (Fin n) → List (Instruction width 8) × Nat
  | _, [] => ([], 1)
  | entry, channel :: rest =>
      let head := step mode width n rows roots channel entry
      let tail := build mode width n rows roots (entry + head.1.length) rest
      (head.1 ++ tail.1, head.2 + tail.2 + 16 * head.1.length + 20)

theorem monotone_image (width n : Nat) (rows : List Row) (roots : List Nat) (entry : Nat) (channels
  : List (Fin n)) :
    (build none width n rows roots entry channels).1 = (SharedTableBatch.code width n rows roots
      entry channels).toList := by
  induction channels generalizing entry with
  | nil => rfl
  | cons channel rest ih =>
      simp only [build, step_monotone, Array.length_toList, SharedTableBatch.stepCode_size, ih,
        SharedTableBatch.code, Array.toList_append]

theorem literal_image (mode : BasisProbeConstruction.Mode) (width n : Nat) (rows : List Row) (roots
  : List Nat) (entry : Nat) (channels : List (Fin n)) :
    (build (some mode) width n rows roots entry channels).1 = (LiteralSourceBatch.code
      (BasisProbeConstruction.config mode) width n rows roots entry channels).toList := by
  induction channels generalizing entry with
  | nil => rfl
  | cons channel rest ih =>
      simp only [build, step_literal, Array.length_toList, LiteralSourceBatch.stepCode_size, ih,
        LiteralSourceBatch.code, Array.toList_append]

theorem step_length (mode : Option BasisProbeConstruction.Mode) (width n : Nat) (rows : List Row)
  (roots : List Nat)
    (channel : Fin n) (entry : Nat) : (step mode width n rows roots channel entry).1.length ≤ 152 :=
      by
  cases mode with
  | none =>
      rw [step_monotone]
      simp only [Array.length_toList, SharedTableBatch.stepCode_size]
      omega
  | some mode =>
      rw [step_literal]
      simp only [Array.length_toList, LiteralSourceBatch.stepCode_size]
      omega

theorem step_clock (mode : Option BasisProbeConstruction.Mode) (width n : Nat) (rows : List Row)
  (roots : List Nat)
    (channel : Fin n) (entry : Nat) :
    (step mode width n rows roots channel entry).2 ≤
      100000 + 3000 * (n + rows.length + (rowChildren rows).length + (rowGuards rows).length +
        roots.length) := by
  have length := step_length mode width n rows roots channel entry
  cases mode with
  | none =>
      have head := BasisProbeConstruction.monotone_clock width n rows roots (entry + 5) (entry +
        148)
      change _ + 16 * (step none width n rows roots channel entry).1.length + _ ≤ _
      dsimp only
      omega
  | some mode =>
      have head := BasisProbeConstruction.literal_clock mode width n rows roots (entry + 5) (entry +
        139)
      change _ + 16 * (step (some mode) width n rows roots channel entry).1.length + _ ≤ _
      dsimp only
      omega

theorem clock (mode : Option BasisProbeConstruction.Mode) (width n : Nat) (rows : List Row) (roots :
  List Nat)
    (entry : Nat) (channels : List (Fin n)) :
    (build mode width n rows roots entry channels).2 ≤
      channels.length * (110000 + 3000 * (n + rows.length + (rowChildren rows).length + (rowGuards
        rows).length + roots.length)) + 1 := by
  induction channels generalizing entry with
  | nil => simp [build]
  | cons channel rest ih =>
      have head := step_clock mode width n rows roots channel entry
      have length := step_length mode width n rows roots channel entry
      have tail := ih (entry + (step mode width n rows roots channel entry).1.length)
      simp only [build, List.length_cons]
      nlinarith

end Controller.Cost.BasisColumnConstruction
