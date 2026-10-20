module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ExtensionConstructionRecipes
public import Controller.Cost.ResidentSolverConstruction
public import Controller.Cost.ForestAdmissibleConstruction
public import Controller.Cost.ForestNegativeRecipes

@[expose] public section


/-! Decision-only resident query formation. The clause constructor is shared
with the forest compiler; a fixed first-order solver suffix is installed at
the cached constructor end. No solver answer is computed during construction. -/
namespace Controller.Cost.QuietQueryConstruction

open Controller.Cost Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestClauseProgramConstruction (environment join joinWork)
open Controller.Cost.ForestZeroEmit

variable {ambient : Nat}

def build (width entry keep count base : Nat) (refs : List (List (Reference ambient))) :
    List (Instruction width 8) × Nat :=
  let provisional := ForestAdmissibleConstruction.construct width (entry + 15) keep keep (keep + 4)
    0 refs
  let solver := entry + 15 + provisional.1.length
  let middle := ForestAdmissibleConstruction.construct width (entry + 15) keep keep (keep + 4)
    solver refs
  let front := evaluate (environment [keep + 5 + 2 * (refs.length + 1)])
    (ForestNegativeRecipes.entryCode.constructionRecipe width)
  let suffix := ResidentSolverConstruction.build width solver keep count base
  let blocks := [front, middle.1.map RegisterWiden.widenInstruction, suffix]
  (join blocks, provisional.2 + middle.2 + work (ForestNegativeRecipes.entryCode.constructionRecipe
    width) +
    ResidentSolverConstruction.clock width + 16 * middle.1.length +
    joinWork blocks + 16 * refs.length + 16 * refs.flatten.length + 100)

theorem image (width entry keep count base : Nat) (refs : List (List (Reference ambient))) :
    (build width entry keep count base refs).1 = EnumerationResident.code width entry keep count
      base refs := by
  have front : evaluate (environment [keep + 5 + 2 * (refs.length + 1)])
      (ForestNegativeRecipes.entryCode.constructionRecipe width) =
      ForestNegativeRecipes.entryCode width (keep + 5 + 2 * (refs.length + 1)) :=
    ForestNegativeRecipes.entryCode.constructionRecipe_eq width (keep + 5 + 2 * (refs.length + 1))
  have suffix (solver : Nat) : ResidentSolverConstruction.build width solver keep count base =
      EnumerationResident.solverCode width solver count base (keep + 3) (keep + 4) (keep + 1) (keep
        + 2) keep :=
    ResidentSolverConstruction.image width solver keep count base
  have cursor : entry + 15 + (ForestAdmissibleConstruction.construct width (entry + 15) keep keep
    (keep + 4) 0 refs).1.length =
      SharedQuerySourceCode.solverEntry width entry keep refs := by
    rw [ForestAdmissibleConstruction.construct_image]
    simp only [SharedQuerySourceCode.solverEntry, ForestZeroAdmissibleCaller.constructorCode,
      List.length_append, ForestZeroAdmissibleCaller.code_length]
    omega
  rw [ForestAdmissibleConstruction.construct_image] at cursor
  simp only [build, cursor, front, suffix, ForestAdmissibleConstruction.construct_image,
    join, List.flatten_cons, List.flatten_nil, List.append_nil, EnumerationResident.code,
    SharedQuerySourceCode.code, ForestNegativeRecipes.entryCode, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.append_assoc]
  all_goals rfl

theorem clock (width entry keep count base : Nat) (refs : List (List (Reference ambient))) :
    (build width entry keep count base refs).2 ≤ 30000 + 500 * refs.length + 2000 *
      refs.flatten.length := by
  let provisional := ForestAdmissibleConstruction.construct width (entry + 15) keep keep (keep + 4)
    0 refs
  let solver := entry + 15 + provisional.1.length
  let middle := ForestAdmissibleConstruction.construct width (entry + 15) keep keep (keep + 4)
    solver refs
  have first := ForestAdmissibleConstruction.construct_work width (entry + 15) keep keep (keep + 4)
    0 refs
  have second := ForestAdmissibleConstruction.construct_work width (entry + 15) keep keep (keep + 4)
    solver refs
  have length := ForestZeroAdmissibleCaller.constructorCode_length width (entry + 15) keep keep
    (keep + 4) solver refs
  rw [← ForestAdmissibleConstruction.construct_image] at length
  have suffixSize : (ResidentSolverConstruction.build width solver keep count base).length = 430 :=
    by
    rw [ResidentSolverConstruction.image, EnumerationResident.solverCode_length]
  have suffixWork := ResidentSolverConstruction.clock_bound width
  have frontSize : (evaluate (environment [keep + 5 + 2 * (refs.length + 1)])
      (ForestNegativeRecipes.entryCode.constructionRecipe width)).length = 15 := by
    simp only [evaluate, List.length_map]; rfl
  simp only [build, ForestNegativeRecipes.entryCode.constructionRecipe_work, joinWork,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append, List.length_map,
    List.length_cons, List.length_nil, frontSize]
  dsimp only [provisional, solver, middle] at first second length suffixSize ⊢
  rw [suffixSize]
  omega

end Controller.Cost.QuietQueryConstruction
