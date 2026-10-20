module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public meta import Controller.Cost.DeriveExtensionRecipe
public import Controller.Cost.ForestNegativeRecipes
public import Controller.Cost.EnumerationResident
public import Controller.Cost.ForestClauseProgramConstruction

public import Controller.Cost.WordConstructionRecipe

@[expose] public section


/-! Fixed resident solvers assembled from small checked templates. The shared
normalizer and FIFO recipes retain explicit scalar headers and source counts. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Controller.Cost.ResidentSolverConstruction

open Controller.Cost Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestClauseProgramConstruction (environment)
open Controller.Cost.ForestNegativeRecipes

def quietSuccess (width query : Nat) : List (Instruction width 8) :=
  (EnumerationQuery.quietSavedCode width 1 (query + 395)).toList

def quietConflict (width query : Nat) : List (Instruction width 8) :=
  (EnumerationQuery.quietSavedCode width 0 (query + 395)).toList

derive_extension_recipe quietSuccess

derive_extension_recipe quietConflict

derive_extension_recipe SharedQueryCleanupCode.code

def recipes (width : Nat) : List (InstructionRecipe 5 width 8) :=
  [part00.constructionRecipe width, part01.constructionRecipe width, part02.constructionRecipe
    width,
   part03.constructionRecipe width, part04.constructionRecipe width, part05.constructionRecipe
     width,
   part06.constructionRecipe width, part07.constructionRecipe width, part08.constructionRecipe
     width,
   part09.constructionRecipe width, part10.constructionRecipe width, part11.constructionRecipe
     width,
   part12.constructionRecipe width, part13.constructionRecipe width, part14.constructionRecipe
     width,
   part15.constructionRecipe width, part16.constructionRecipe width].flatten

def build (width entry keep count base : Nat) : List (Instruction width 8) :=
  evaluate (environment [keep, base, count, entry, 0]) (recipes width) ++
    evaluate (environment [entry]) (quietSuccess.constructionRecipe width) ++
    evaluate (environment [entry]) (quietConflict.constructionRecipe width) ++
    evaluate (environment [entry + 395]) (SharedQueryCleanupCode.code.constructionRecipe width)

theorem image (width entry keep count base : Nat) :
    build width entry keep count base =
      EnumerationResident.solverCode width entry count base (keep + 3) (keep + 4) (keep + 1) (keep +
        2) keep := by
  have part00Image : evaluate (environment [keep, base, count, entry, 0]) (part00.constructionRecipe
    width) =
      part00 width keep base count entry 0 := part00.constructionRecipe_eq width keep base count
        entry 0
  have part01Image : evaluate (environment [keep, base, count, entry, 0]) (part01.constructionRecipe
    width) =
      part01 width keep base count entry 0 := part01.constructionRecipe_eq width keep base count
        entry 0
  have part02Image : evaluate (environment [keep, base, count, entry, 0]) (part02.constructionRecipe
    width) =
      part02 width keep base count entry 0 := part02.constructionRecipe_eq width keep base count
        entry 0
  have part03Image : evaluate (environment [keep, base, count, entry, 0]) (part03.constructionRecipe
    width) =
      part03 width keep base count entry 0 := part03.constructionRecipe_eq width keep base count
        entry 0
  have part04Image : evaluate (environment [keep, base, count, entry, 0]) (part04.constructionRecipe
    width) =
      part04 width keep base count entry 0 := part04.constructionRecipe_eq width keep base count
        entry 0
  have part05Image : evaluate (environment [keep, base, count, entry, 0]) (part05.constructionRecipe
    width) =
      part05 width keep base count entry 0 := part05.constructionRecipe_eq width keep base count
        entry 0
  have part06Image : evaluate (environment [keep, base, count, entry, 0]) (part06.constructionRecipe
    width) =
      part06 width keep base count entry 0 := part06.constructionRecipe_eq width keep base count
        entry 0
  have part07Image : evaluate (environment [keep, base, count, entry, 0]) (part07.constructionRecipe
    width) =
      part07 width keep base count entry 0 := part07.constructionRecipe_eq width keep base count
        entry 0
  have part08Image : evaluate (environment [keep, base, count, entry, 0]) (part08.constructionRecipe
    width) =
      part08 width keep base count entry 0 := part08.constructionRecipe_eq width keep base count
        entry 0
  have part09Image : evaluate (environment [keep, base, count, entry, 0]) (part09.constructionRecipe
    width) =
      part09 width keep base count entry 0 := part09.constructionRecipe_eq width keep base count
        entry 0
  have part10Image : evaluate (environment [keep, base, count, entry, 0]) (part10.constructionRecipe
    width) =
      part10 width keep base count entry 0 := part10.constructionRecipe_eq width keep base count
        entry 0
  have part11Image : evaluate (environment [keep, base, count, entry, 0]) (part11.constructionRecipe
    width) =
      part11 width keep base count entry 0 := part11.constructionRecipe_eq width keep base count
        entry 0
  have part12Image : evaluate (environment [keep, base, count, entry, 0]) (part12.constructionRecipe
    width) =
      part12 width keep base count entry 0 := part12.constructionRecipe_eq width keep base count
        entry 0
  have part13Image : evaluate (environment [keep, base, count, entry, 0]) (part13.constructionRecipe
    width) =
      part13 width keep base count entry 0 := part13.constructionRecipe_eq width keep base count
        entry 0
  have part14Image : evaluate (environment [keep, base, count, entry, 0]) (part14.constructionRecipe
    width) =
      part14 width keep base count entry 0 := part14.constructionRecipe_eq width keep base count
        entry 0
  have part15Image : evaluate (environment [keep, base, count, entry, 0]) (part15.constructionRecipe
    width) =
      part15 width keep base count entry 0 := part15.constructionRecipe_eq width keep base count
        entry 0
  have part16Image : evaluate (environment [keep, base, count, entry, 0]) (part16.constructionRecipe
    width) =
      part16 width keep base count entry 0 := part16.constructionRecipe_eq width keep base count
        entry 0
  have yes : evaluate (environment [entry]) (quietSuccess.constructionRecipe width) =
      quietSuccess width entry := quietSuccess.constructionRecipe_eq width entry
  have no : evaluate (environment [entry]) (quietConflict.constructionRecipe width) =
      quietConflict width entry := quietConflict.constructionRecipe_eq width entry
  have done : evaluate (environment [entry + 395]) (SharedQueryCleanupCode.code.constructionRecipe
    width) =
      SharedQueryCleanupCode.code width (entry + 395) :=
        SharedQueryCleanupCode.code.constructionRecipe_eq width (entry + 395)
  simp only [build, recipes, evaluate_append, evaluate_flatten, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.append_nil, part00Image, part01Image, part02Image,
      part03Image, part04Image, part05Image, part06Image, part07Image, part08Image, part09Image,
      part10Image, part11Image, part12Image, part13Image, part14Image, part15Image, part16Image,
      yes, no, done,
    part00, part01, part02, part03, part04, part05, part06, part07, part08, part09, part10, part11,
      part12, part13, part14, part15, part16, quietSuccess, quietConflict,
    EnumerationResident.solverCode, SharedSolverPrefix.code, SharedNormalizerCode.code,
    EnumerationResident.worklistCode, normalizeStream, rowStream_eq, copyStream_eq, seedStream_eq,
    Array.toList_append, List.append_assoc, Nat.add_assoc, Nat.reduceAdd]

theorem head_image (width entry keep count base : Nat) :
    evaluate (environment [keep, base, count, entry, 0]) (recipes width) =
      [part00 width keep base count entry 0, part01 width keep base count entry 0, part02 width keep
        base count entry 0, part03 width keep base count entry 0, part04 width keep base count entry
        0, part05 width keep base count entry 0, part06 width keep base count entry 0, part07 width
        keep base count entry 0, part08 width keep base count entry 0, part09 width keep base count
        entry 0, part10 width keep base count entry 0, part11 width keep base count entry 0, part12
        width keep base count entry 0, part13 width keep base count entry 0, part14 width keep base
        count entry 0, part15 width keep base count entry 0, part16 width keep base count entry
        0].flatten := by
  have part00Image : evaluate (environment [keep, base, count, entry, 0]) (part00.constructionRecipe
    width) =
      part00 width keep base count entry 0 := part00.constructionRecipe_eq width keep base count
        entry 0
  have part01Image : evaluate (environment [keep, base, count, entry, 0]) (part01.constructionRecipe
    width) =
      part01 width keep base count entry 0 := part01.constructionRecipe_eq width keep base count
        entry 0
  have part02Image : evaluate (environment [keep, base, count, entry, 0]) (part02.constructionRecipe
    width) =
      part02 width keep base count entry 0 := part02.constructionRecipe_eq width keep base count
        entry 0
  have part03Image : evaluate (environment [keep, base, count, entry, 0]) (part03.constructionRecipe
    width) =
      part03 width keep base count entry 0 := part03.constructionRecipe_eq width keep base count
        entry 0
  have part04Image : evaluate (environment [keep, base, count, entry, 0]) (part04.constructionRecipe
    width) =
      part04 width keep base count entry 0 := part04.constructionRecipe_eq width keep base count
        entry 0
  have part05Image : evaluate (environment [keep, base, count, entry, 0]) (part05.constructionRecipe
    width) =
      part05 width keep base count entry 0 := part05.constructionRecipe_eq width keep base count
        entry 0
  have part06Image : evaluate (environment [keep, base, count, entry, 0]) (part06.constructionRecipe
    width) =
      part06 width keep base count entry 0 := part06.constructionRecipe_eq width keep base count
        entry 0
  have part07Image : evaluate (environment [keep, base, count, entry, 0]) (part07.constructionRecipe
    width) =
      part07 width keep base count entry 0 := part07.constructionRecipe_eq width keep base count
        entry 0
  have part08Image : evaluate (environment [keep, base, count, entry, 0]) (part08.constructionRecipe
    width) =
      part08 width keep base count entry 0 := part08.constructionRecipe_eq width keep base count
        entry 0
  have part09Image : evaluate (environment [keep, base, count, entry, 0]) (part09.constructionRecipe
    width) =
      part09 width keep base count entry 0 := part09.constructionRecipe_eq width keep base count
        entry 0
  have part10Image : evaluate (environment [keep, base, count, entry, 0]) (part10.constructionRecipe
    width) =
      part10 width keep base count entry 0 := part10.constructionRecipe_eq width keep base count
        entry 0
  have part11Image : evaluate (environment [keep, base, count, entry, 0]) (part11.constructionRecipe
    width) =
      part11 width keep base count entry 0 := part11.constructionRecipe_eq width keep base count
        entry 0
  have part12Image : evaluate (environment [keep, base, count, entry, 0]) (part12.constructionRecipe
    width) =
      part12 width keep base count entry 0 := part12.constructionRecipe_eq width keep base count
        entry 0
  have part13Image : evaluate (environment [keep, base, count, entry, 0]) (part13.constructionRecipe
    width) =
      part13 width keep base count entry 0 := part13.constructionRecipe_eq width keep base count
        entry 0
  have part14Image : evaluate (environment [keep, base, count, entry, 0]) (part14.constructionRecipe
    width) =
      part14 width keep base count entry 0 := part14.constructionRecipe_eq width keep base count
        entry 0
  have part15Image : evaluate (environment [keep, base, count, entry, 0]) (part15.constructionRecipe
    width) =
      part15 width keep base count entry 0 := part15.constructionRecipe_eq width keep base count
        entry 0
  have part16Image : evaluate (environment [keep, base, count, entry, 0]) (part16.constructionRecipe
    width) =
      part16 width keep base count entry 0 := part16.constructionRecipe_eq width keep base count
        entry 0
  simp only [recipes, evaluate_append, List.flatten_cons, List.flatten_nil, List.append_nil,
    part00Image, part01Image, part02Image, part03Image, part04Image, part05Image, part06Image,
      part07Image, part08Image, part09Image, part10Image, part11Image, part12Image, part13Image,
      part14Image, part15Image, part16Image]

theorem head_length (width entry keep count base : Nat) :
    (evaluate (environment [keep, base, count, entry, 0]) (recipes width)).length = 369 := by
  have length : (build width entry keep count base).length = 430 := by
    rw [image, EnumerationResident.solverCode_length]
  have yes : evaluate (environment [entry]) (quietSuccess.constructionRecipe width) = quietSuccess
    width entry :=
    quietSuccess.constructionRecipe_eq width entry
  have no : evaluate (environment [entry]) (quietConflict.constructionRecipe width) = quietConflict
    width entry :=
    quietConflict.constructionRecipe_eq width entry
  have ending : evaluate (environment [entry + 395]) (SharedQueryCleanupCode.code.constructionRecipe
    width) =
      SharedQueryCleanupCode.code width (entry + 395) :=
        SharedQueryCleanupCode.code.constructionRecipe_eq width (entry + 395)
  have savedSize (value destination : Nat) : (EnumerationQuery.quietSavedCode width value
    destination).size = 13 := rfl
  simp only [build, yes, no, ending, quietSuccess, quietConflict, List.length_append,
    Array.length_toList, savedSize, SharedQueryCleanupCode.code_length] at length
  omega

def clock (width : Nat) : Nat := work (recipes width) + 114 + 114 + 316 + 8 * 430 + 100

theorem clock_bound (width : Nat) : clock width ≤ 10000 := by
  simp only [clock, recipes, work_flatten, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    part00.constructionRecipe_work, part01.constructionRecipe_work, part02.constructionRecipe_work,
      part03.constructionRecipe_work, part04.constructionRecipe_work,
      part05.constructionRecipe_work, part06.constructionRecipe_work,
      part07.constructionRecipe_work, part08.constructionRecipe_work,
      part09.constructionRecipe_work, part10.constructionRecipe_work,
      part11.constructionRecipe_work, part12.constructionRecipe_work,
      part13.constructionRecipe_work, part14.constructionRecipe_work,
      part15.constructionRecipe_work, part16.constructionRecipe_work]
  decide

end Controller.Cost.ResidentSolverConstruction
