/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ResidentSolverStorage
import Controller.Cost.ForestAdmissibleStorage
import Controller.Cost.NativeQueryConstruction

/-! Storage for both provisional and relocated quiet query construction,
including its fixed resident solver and source-prefix materialization. -/
namespace Controller.Cost.QuietQueryStorage

open Controller.Cost Controller.Cost.WordConstructionRecipe Controller.Cost.ForestZeroEmit
open Controller.Cost.ForestClauseProgramConstruction (environment)

variable {ambient : Nat}

def solver (width entry keep : Nat) (refs : List (List (Reference ambient))) : Nat :=
  entry + 15 + (ForestAdmissibleConstruction.construct width (entry + 15)
    keep keep (keep + 4) 0 refs).1.length

structure Certificate (width entry keep count base : Nat)
    (refs : List (List (Reference ambient))) where
  provisional : ForestAdmissibleStorage.Certificate width (entry + 15) keep keep (keep + 4) 0 refs
  relocated : ForestAdmissibleStorage.Certificate width (entry + 15) keep keep (keep + 4)
    (solver width entry keep refs) refs
  backend : ResidentSolverStorage.Certificate width (solver width entry keep refs) keep count base
  entryPeak : Nat
  entered : WordConstructionStorage.Trace (environment [keep + 5 + 2 * (refs.length + 1)])
    (ForestNegativeRecipes.entryCode.constructionRecipe width)
    (evaluate (environment [keep + 5 + 2 * (refs.length + 1)])
      (ForestNegativeRecipes.entryCode.constructionRecipe width)) 134 entryPeak

def buffers (width entry keep count base : Nat) (refs : List (List (Reference ambient)))
    (certificate : Certificate width entry keep count base refs) : Nat :=
  ForestAdmissibleStorage.buffers width (entry + 15) keep keep (keep + 4) 0 refs
    certificate.provisional +
  ForestAdmissibleStorage.buffers width (entry + 15) keep keep (keep + 4)
    (solver width entry keep refs) refs certificate.relocated +
  ResidentSolverStorage.buffers width (solver width entry keep refs) keep count base
    certificate.backend + certificate.entryPeak +
  128 * (QuietQueryConstruction.build width entry keep count base refs).1.length +
    128 * (refs.length + refs.flatten.length + 1)

theorem complete (width entry keep count base : Nat) (refs : List (List (Reference ambient))) :
    ∃ certificate : Certificate width entry keep count base refs,
      buffers width entry keep count base refs certificate ≤
        1000000 + 100000 * refs.length + 200000 * refs.flatten.length := by
  obtain ⟨provisional, firstBound⟩ := ForestAdmissibleStorage.construction width (entry + 15)
    keep keep (keep + 4) 0 refs
  obtain ⟨relocated, secondBound⟩ := ForestAdmissibleStorage.construction width (entry + 15)
    keep keep (keep + 4) (solver width entry keep refs) refs
  obtain ⟨backend, backendBound⟩ := ResidentSolverStorage.complete width
    (solver width entry keep refs) keep count base
  obtain ⟨entryPeak, entered, entryBound⟩ := WordConstructionStorage.construction
    (environment [keep + 5 + 2 * (refs.length + 1)])
    (ForestNegativeRecipes.entryCode.constructionRecipe width)
  rw [ForestNegativeRecipes.entryCode.constructionRecipe_work] at entered entryBound
  have source := NativeQueryConstruction.source_length width entry keep count base refs
  rw [NativeQueryConstruction.source_image] at source
  have length : (QuietQueryConstruction.build width entry keep count base refs).1.length ≤
      547 + 5 * refs.length + 28 * refs.flatten.length := by
    rw [QuietQueryConstruction.image]
    simp only [EnumerationResident.code, List.length_append, EnumerationResident.solverCode_length]
    omega
  refine ⟨⟨provisional, relocated, backend, entryPeak, entered⟩, ?_⟩
  simp only [buffers]
  omega

end Controller.Cost.QuietQueryStorage
