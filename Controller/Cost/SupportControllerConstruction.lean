module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.SourceOperandConstruction
public import Controller.Cost.TemplateStreamConstruction

@[expose] public section


/-! Source-count and occurrence-stream construction for the support controller.
The interpreter image reads the original encoded graph. Healthy values are not
computed during construction and occur only in the runtime source packet. -/
namespace Controller.Cost.SupportControllerConstruction

open Controller.Cost Controller.Extensions
open Controller.Cost.WordConstructionRecipe Controller.Cost.ExtensionConstructionRecipes
open Controller.Cost.ForestClauseProgramConstruction (environment)
open Controller.Cost.ForestIndexedOperands

def sourceRound (width n : Nat) (header : Array (Word width)) (rows : List Row) (roots : List Nat)
    (entry : Nat) : List (Instruction width 8) × Nat :=
  let kernel := evaluate (environment [n, header.size, rows.length, (rowChildren rows).length,
    (rowGuards rows).length, roots.length]) (sourceKernel.constructionRecipe width)
  let relocated := ProgramRelocationConstruction.build entry (kernel.map RegisterWiden.widenInstruction)
  (relocated.1, relocated.2 + 1210 + 16 * kernel.length +
    16 * (rows.length + (rowChildren rows).length + (rowGuards rows).length + roots.length) + 100)

theorem sourceRound_image (width n : Nat) (header : Array (Word width)) (rows : List Row) (roots : List Nat)
    (entry : Nat) :
    (sourceRound width n header rows roots entry).1 = (SupportSourceRound.code width n header rows roots entry).toList := by
  have formed : evaluate (environment [n, header.size, rows.length, (rowChildren rows).length,
      (rowGuards rows).length, roots.length]) (sourceKernel.constructionRecipe width) =
      sourceKernel width n header.size rows.length (rowChildren rows).length (rowGuards rows).length roots.length :=
    sourceKernel.constructionRecipe_eq width n header.size rows.length (rowChildren rows).length
      (rowGuards rows).length roots.length
  simp only [sourceRound, formed, sourceKernel, sourceLayout_image,
    ProgramRelocationConstruction.build_image, ResidentSegment.code,
    SupportSourceRound.code, SupportSourceRound.kernel, RegisterWiden.widenProgram,
    Array.toList_map, List.toList_toArray]

set_option maxHeartbeats 1000000 in
theorem sourceRound_clock (width n : Nat) (header : Array (Word width)) (rows : List Row) (roots : List Nat)
    (entry : Nat) :
    (sourceRound width n header rows roots entry).2 ≤
      10000 + 16 * (rows.length + (rowChildren rows).length + (rowGuards rows).length + roots.length) := by
  let kernel := evaluate (environment [n, header.size, rows.length, (rowChildren rows).length,
    (rowGuards rows).length, roots.length]) (sourceKernel.constructionRecipe width)
  have formed : kernel = sourceKernel width n header.size rows.length (rowChildren rows).length
      (rowGuards rows).length roots.length :=
    sourceKernel.constructionRecipe_eq width n header.size rows.length (rowChildren rows).length
      (rowGuards rows).length roots.length
  have length : kernel.length = 126 := by rw [formed]; exact UniformDAGLoop.code_length
  have relocated := ProgramRelocationConstruction.build_clock entry (kernel.map RegisterWiden.widenInstruction)
  simp only [List.length_map, length] at relocated
  change (ProgramRelocationConstruction.build entry (kernel.map RegisterWiden.widenInstruction)).2 +
    1210 + 16 * kernel.length + 16 * (rows.length + (rowChildren rows).length +
      (rowGuards rows).length + roots.length) + 100 ≤ _
  omega

def healthyScan (width cursor healthy needed count : Nat) : List (Instruction width 8) × Nat :=
  let emitted := TemplateStreamConstruction.build (SupportHealthyScan.nodeCode.constructionRecipe width)
    (fun i => environment [cursor + i, healthy, needed]) 0 count
  (emitted.1, emitted.2 + 8 * count + 16)

theorem healthyScan_image (width cursor healthy needed count : Nat) :
    (healthyScan width cursor healthy needed count).1 = SupportHealthyScan.code width cursor healthy needed count := by
  have formed (i : Nat) : evaluate (environment [cursor + i, healthy, needed])
      (SupportHealthyScan.nodeCode.constructionRecipe width) = SupportHealthyScan.nodeCode width (cursor + i) healthy needed :=
    SupportHealthyScan.nodeCode.constructionRecipe_eq width (cursor + i) healthy needed
  simpa only [healthyScan, TemplateStreamConstruction.image, Nat.zero_add,
    formed, SupportHealthyScan.code]

theorem healthyScan_clock (width cursor healthy needed count : Nat) :
    (healthyScan width cursor healthy needed count).2 ≤ 100 * count + 17 := by
  simp only [healthyScan, TemplateStreamConstruction.clock, SupportHealthyScan.nodeCode.constructionRecipe_work]
  have length : (SupportHealthyScan.nodeCode.constructionRecipe width).length = 6 := rfl
  rw [length]
  omega

def rootScan (width entry cursor healthy values found count : Nat) : List (Instruction width 8) × Nat :=
  let emitted := TemplateStreamConstruction.build (SupportRootScan.nodeCode.constructionRecipe width)
    (fun i => environment [entry + 15 * i, cursor + i, healthy, values, found]) 0 count
  (emitted.1, emitted.2 + 16 * count + 16)

theorem rootScan_image (width entry cursor healthy values found count : Nat) :
    (rootScan width entry cursor healthy values found count).1 =
      SupportRootScan.code width entry cursor healthy values found count := by
  have formed (i : Nat) : evaluate (environment [entry + 15 * i, cursor + i, healthy, values, found])
      (SupportRootScan.nodeCode.constructionRecipe width) = SupportRootScan.nodeCode width (entry + 15 * i) (cursor + i) healthy values found :=
    SupportRootScan.nodeCode.constructionRecipe_eq width (entry + 15 * i) (cursor + i) healthy values found
  simpa only [rootScan, TemplateStreamConstruction.image, Nat.zero_add, formed, SupportRootScan.code]

theorem rootScan_clock (width entry cursor healthy values found count : Nat) :
    (rootScan width entry cursor healthy values found count).2 ≤ 200 * count + 17 := by
  simp only [rootScan, TemplateStreamConstruction.clock, SupportRootScan.nodeCode.constructionRecipe_work]
  have length : (SupportRootScan.nodeCode.constructionRecipe width).length = 15 := rfl
  rw [length]
  omega

end Controller.Cost.SupportControllerConstruction
