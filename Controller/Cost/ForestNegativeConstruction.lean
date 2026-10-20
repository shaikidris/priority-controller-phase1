module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ForestNegativeRecipes
public import Controller.Cost.ForestAdmissibleConstruction

@[expose] public section


/-! Complete negative-query instruction formation from cached metadata.
The provisional constructor is charged before its size is used for relocation.
The final image is formed once; neither a semantic query answer nor a
hypothetical solver heap is supplied to this constructor. -/
set_option maxRecDepth 10000

namespace Controller.Cost.ForestNegativeConstruction

open Controller.Cost Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.ForestClauseProgramConstruction
open Controller.Cost.ForestNegativeRecipes

variable {ambient : Nat}

def form (width protectedEnd channels entry next : Nat)
    (refs : List (List (Reference ambient))) (summary : ForestCompilerQueries.Summary ambient) :
    List (Instruction width 8) × Nat :=
  let provisional := ForestAdmissibleConstruction.construct width (entry + 15)
    protectedEnd protectedEnd (protectedEnd + 4) 0 refs
  let query := entry + 15 + provisional.1.length
  let middle := ForestAdmissibleConstruction.construct width (entry + 15)
    protectedEnd protectedEnd (protectedEnd + 4) query refs
  let prefixRecipes := entryCode.constructionRecipe width
  let prefixCode := evaluate (environment [protectedEnd + 5 + 2 * (refs.length + 1)]) prefixRecipes
  let suffixCode := evaluate (environment [protectedEnd,
    ForestCachedNegativeProgram.heapEnd protectedEnd channels refs summary,
    summary.coordinates.size, query, next]) (suffixRecipes width)
  let widened := middle.1.map RegisterWiden.widenInstruction
  let blocks := [prefixCode, widened, suffixCode]
  (join blocks, provisional.2 + middle.2 + work prefixRecipes + work (suffixRecipes width) +
    2 * provisional.1.length + middle.1.length + joinWork blocks +
    4 * refs.length + 4 * refs.flatten.length + 100)

theorem entry_image (width sourceBase : Nat) :
    evaluate (environment [sourceBase]) (entryCode.constructionRecipe width) = entryCode width sourceBase := by
  change evaluate (fun index => [sourceBase].getD index.val 0) _ = _
  exact entryCode.constructionRecipe_eq width sourceBase

theorem suffix_image (width protectedEnd base count query next : Nat) :
    evaluate (environment [protectedEnd, base, count, query, next]) (suffixRecipes width) =
      suffix width protectedEnd base count query next := by
  change evaluate (fun index => [protectedEnd, base, count, query, next].getD index.val 0) _ = _
  exact suffix_recipe_image width protectedEnd base count query next

theorem form_image (width protectedEnd channels entry next : Nat)
    (refs : List (List (Reference ambient))) (summary : ForestCompilerQueries.Summary ambient) :
    (form width protectedEnd channels entry next refs summary).1 =
      ForestCachedNegativeProgram.instructions width protectedEnd channels entry next refs summary := by
  rw [image_eq]
  simp only [form, ForestAdmissibleConstruction.construct_image, entry_image, suffix_image,
    join, List.flatten_cons, List.flatten_nil, List.append_nil, ForestZeroResident.placement,
    List.append_assoc]

set_option maxHeartbeats 400000 in
 theorem suffix_work (width : Nat) : work (suffixRecipes width) ≤ 10000 := by
  simp only [suffixRecipes, work_flatten, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    part00.constructionRecipe_work, part01.constructionRecipe_work, part02.constructionRecipe_work,
    part03.constructionRecipe_work, part04.constructionRecipe_work, part05.constructionRecipe_work,
    part06.constructionRecipe_work, part07.constructionRecipe_work, part08.constructionRecipe_work,
    part09.constructionRecipe_work, part10.constructionRecipe_work, part11.constructionRecipe_work,
    part12.constructionRecipe_work, part13.constructionRecipe_work, part14.constructionRecipe_work,
    part15.constructionRecipe_work, part16.constructionRecipe_work, part17.constructionRecipe_work,
    part18.constructionRecipe_work, part19.constructionRecipe_work, part20.constructionRecipe_work,
    part21.constructionRecipe_work, part22.constructionRecipe_work, part23.constructionRecipe_work,
    part24.constructionRecipe_work, part25.constructionRecipe_work, part26.constructionRecipe_work,
    part27.constructionRecipe_work]
  decide

theorem form_work (width protectedEnd channels entry next : Nat)
    (refs : List (List (Reference ambient))) (summary : ForestCompilerQueries.Summary ambient) :
    (form width protectedEnd channels entry next refs summary).2 ≤
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
      (ForestCachedNegativeProgram.heapEnd protectedEnd channels refs summary)
      summary.coordinates.size query next).length = 467 := by
    rw [← suffix_recipe_image]
    simp only [evaluate, List.length_map]
    rfl
  have prefixSize : (entryCode width (protectedEnd + 5 + 2 * (refs.length + 1))).length = 15 := by
    rfl
  have suffixCost := suffix_work width
  simp only [form, entryCode.constructionRecipe_work, joinWork, List.flatten_cons,
    List.flatten_nil, List.append_nil, List.length_append, List.length_cons, List.length_nil,
    List.length_map, entry_image, suffix_image, prefixSize]
  change _ ≤ _ at first second firstSize secondSize
  change _ = _ at suffixSize
  dsimp only [provisional, query] at first second firstSize secondSize suffixSize ⊢
  omega

end Controller.Cost.ForestNegativeConstruction
