/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ForestNegativeConstruction

/-! Negative image formation from scalar metadata. Coordinate arrays and local
clause labels are absent from this executable interface; they occur only in
the refinement equation to the existing complete image constructor. -/
set_option maxRecDepth 10000

namespace Controller.Cost.ForestScalarNegativeConstruction

open Controller.Cost Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.ForestClauseProgramConstruction Controller.Cost.ForestNegativeRecipes

variable {ambient : Nat}

def heapEnd (protectedEnd channels : Nat) (refs : List (List (Reference ambient)))
    (coverage : ForestZeroNonempty.Result) : Nat :=
  protectedEnd + 5 + 2 * (refs.length + 1) + 2 * refs.flatten.length +
    (if coverage.reason = .covered then 2 * channels else 0)

def form (width protectedEnd channels entry next : Nat)
    (refs : List (List (Reference ambient))) (count : Nat) (coverage : ForestZeroNonempty.Result) :
    List (Instruction width 8) × Nat :=
  let provisional := ForestAdmissibleConstruction.construct width (entry + 15)
    protectedEnd protectedEnd (protectedEnd + 4) 0 refs
  let query := entry + 15 + provisional.1.length
  let middle := ForestAdmissibleConstruction.construct width (entry + 15)
    protectedEnd protectedEnd (protectedEnd + 4) query refs
  let frontRecipes := entryCode.constructionRecipe width
  let frontCode := evaluate (environment [protectedEnd + 5 + 2 * (refs.length + 1)]) frontRecipes
  let suffixCode := evaluate (environment [protectedEnd, heapEnd protectedEnd channels refs coverage,
    count, query, next]) (suffixRecipes width)
  let widened := middle.1.map RegisterWiden.widenInstruction
  let blocks := [frontCode, widened, suffixCode]
  (join blocks, provisional.2 + middle.2 + work frontRecipes + work (suffixRecipes width) +
    2 * provisional.1.length + middle.1.length + joinWork blocks +
    4 * refs.length + 4 * refs.flatten.length + 100)

theorem form_refines (width protectedEnd channels entry next : Nat)
    (refs : List (List (Reference ambient))) (summary : ForestCompilerQueries.Summary ambient) :
    form width protectedEnd channels entry next refs summary.coordinates.size summary.coverage =
      ForestNegativeConstruction.form width protectedEnd channels entry next refs summary := rfl

/-- Scalar formation has the same image and charge for all summaries sharing
these two operands. The array/row payloads are not evaluated or retained. -/
theorem summary_irrelevant (width protectedEnd channels entry next : Nat)
    (refs : List (List (Reference ambient))) (first second : ForestCompilerQueries.Summary ambient)
    (count : first.coordinates.size = second.coordinates.size) (coverage : first.coverage = second.coverage) :
    ForestNegativeConstruction.form width protectedEnd channels entry next refs first =
      ForestNegativeConstruction.form width protectedEnd channels entry next refs second := by
  rw [← form_refines, ← form_refines, count, coverage]

theorem form_work (width protectedEnd channels entry next : Nat)
    (refs : List (List (Reference ambient))) (count : Nat) (coverage : ForestZeroNonempty.Result) :
    (form width protectedEnd channels entry next refs count coverage).2 ≤
      15000 + 250 * refs.length + 1050 * refs.flatten.length := by
  let provisional := ForestAdmissibleConstruction.construct width (entry + 15)
    protectedEnd protectedEnd (protectedEnd + 4) 0 refs
  let query := entry + 15 + provisional.1.length
  have first := ForestAdmissibleConstruction.construct_work width (entry + 15) protectedEnd protectedEnd (protectedEnd + 4) 0 refs
  have second := ForestAdmissibleConstruction.construct_work width (entry + 15) protectedEnd protectedEnd (protectedEnd + 4) query refs
  have firstSize := constructorCode_length width (entry + 15) protectedEnd protectedEnd (protectedEnd + 4) 0 refs
  have secondSize := constructorCode_length width (entry + 15) protectedEnd protectedEnd (protectedEnd + 4) query refs
  rw [← ForestAdmissibleConstruction.construct_image] at firstSize secondSize
  have suffixSize : (suffix width protectedEnd
      (heapEnd protectedEnd channels refs coverage)
      count query next).length = 467 := by
    rw [← suffix_recipe_image]
    simp only [evaluate, List.length_map]
    rfl
  have prefixSize : (entryCode width (protectedEnd + 5 + 2 * (refs.length + 1))).length = 15 := by
    rfl
  have suffixCost := ForestNegativeConstruction.suffix_work width
  simp only [form, entryCode.constructionRecipe_work, joinWork, List.flatten_cons,
    List.flatten_nil, List.append_nil, List.length_append, List.length_cons, List.length_nil,
    List.length_map, ForestNegativeConstruction.entry_image, ForestNegativeConstruction.suffix_image, prefixSize]
  change _ ≤ _ at first second firstSize secondSize
  change _ = _ at suffixSize
  dsimp only [provisional, query] at first second firstSize secondSize suffixSize ⊢
  omega

theorem instruction_bound (width protectedEnd channels entry next : Nat)
    (refs : List (List (Reference ambient))) (count : Nat) (coverage : ForestZeroNonempty.Result) :
    (form width protectedEnd channels entry next refs count coverage).1.length ≤
      584 + 5 * refs.length + 28 * refs.flatten.length := by
  let provisional := ForestAdmissibleConstruction.construct width (entry + 15)
    protectedEnd protectedEnd (protectedEnd + 4) 0 refs
  let query := entry + 15 + provisional.1.length
  have size := constructorCode_length width (entry + 15) protectedEnd protectedEnd (protectedEnd + 4) query refs
  rw [← ForestAdmissibleConstruction.construct_image] at size
  have suffixSize : (suffix width protectedEnd (heapEnd protectedEnd channels refs coverage) count query next).length = 467 := by
    rw [← suffix_recipe_image]
    simp only [evaluate, List.length_map]
    rfl
  have frontSize : (entryCode width (protectedEnd + 5 + 2 * (refs.length + 1))).length = 15 := rfl
  simp only [form, join, List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append,
    List.length_map, ForestNegativeConstruction.entry_image, ForestNegativeConstruction.suffix_image, frontSize]
  dsimp only [provisional, query] at size suffixSize ⊢
  omega

end Controller.Cost.ForestScalarNegativeConstruction
