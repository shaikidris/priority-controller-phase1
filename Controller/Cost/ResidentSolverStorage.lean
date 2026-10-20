/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ResidentSolverConstruction
import Controller.Cost.WordConstructionStorage

/-! Storage for the fixed normalizer/FIFO resident solver templates. All four
formed blocks and their joins are retained by this conservative envelope. -/
namespace Controller.Cost.ResidentSolverStorage

open Controller.Cost Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestClauseProgramConstruction (environment)

structure Certificate (width entry keep count base : Nat) where
  headPeak : Nat
  yesPeak : Nat
  noPeak : Nat
  donePeak : Nat
  head : WordConstructionStorage.Trace (environment [keep, base, count, entry, 0])
    (ResidentSolverConstruction.recipes width)
    (evaluate (environment [keep, base, count, entry, 0])
      (ResidentSolverConstruction.recipes width))
    (work (ResidentSolverConstruction.recipes width)) headPeak
  yes : WordConstructionStorage.Trace (environment [entry])
    (ResidentSolverConstruction.quietSuccess.constructionRecipe width)
    (evaluate (environment [entry])
      (ResidentSolverConstruction.quietSuccess.constructionRecipe width)) 114 yesPeak
  no : WordConstructionStorage.Trace (environment [entry])
    (ResidentSolverConstruction.quietConflict.constructionRecipe width)
    (evaluate (environment [entry])
      (ResidentSolverConstruction.quietConflict.constructionRecipe width)) 114 noPeak
  done : WordConstructionStorage.Trace (environment [entry + 395])
    (SharedQueryCleanupCode.code.constructionRecipe width)
    (evaluate (environment [entry + 395]) (SharedQueryCleanupCode.code.constructionRecipe width))
    316 donePeak

def buffers (width entry keep count base : Nat)
    (certificate : Certificate width entry keep count base) : Nat :=
  certificate.headPeak + certificate.yesPeak + certificate.noPeak + certificate.donePeak +
    64 * (ResidentSolverConstruction.build width entry keep count base).length + 5000

theorem complete (width entry keep count base : Nat) :
    ∃ certificate : Certificate width entry keep count base,
      buffers width entry keep count base certificate ≤ 500000 := by
  obtain ⟨headPeak, head, headBound⟩ := WordConstructionStorage.construction
    (environment [keep, base, count, entry, 0]) (ResidentSolverConstruction.recipes width)
  obtain ⟨yesPeak, yes, yesBound⟩ := WordConstructionStorage.construction
    (environment [entry]) (ResidentSolverConstruction.quietSuccess.constructionRecipe width)
  obtain ⟨noPeak, no, noBound⟩ := WordConstructionStorage.construction
    (environment [entry]) (ResidentSolverConstruction.quietConflict.constructionRecipe width)
  obtain ⟨donePeak, done, doneBound⟩ := WordConstructionStorage.construction
    (environment [entry + 395]) (SharedQueryCleanupCode.code.constructionRecipe width)
  rw [ResidentSolverConstruction.quietSuccess.constructionRecipe_work] at yes yesBound
  rw [ResidentSolverConstruction.quietConflict.constructionRecipe_work] at no noBound
  rw [SharedQueryCleanupCode.code.constructionRecipe_work] at done doneBound
  have headWork := ResidentSolverConstruction.clock_bound width
  unfold ResidentSolverConstruction.clock at headWork
  have length : (ResidentSolverConstruction.build width entry keep count base).length = 430 := by
    rw [ResidentSolverConstruction.image, EnumerationResident.solverCode_length]
  refine ⟨⟨headPeak, yesPeak, noPeak, donePeak, head, yes, no, done⟩, ?_⟩
  simp only [buffers, length]
  omega

end Controller.Cost.ResidentSolverStorage
