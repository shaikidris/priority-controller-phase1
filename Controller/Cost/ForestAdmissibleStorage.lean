/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ForestAdmissibleConstruction
import Controller.Cost.ForestClauseStorage

/-! Complete reserved-row caller construction storage. The source image and
fixed admissibility continuation have traced operand evaluation; buffers cover
the reserved-row copy, caller append and retained instruction backing. -/
namespace Controller.Cost.ForestAdmissibleStorage

open Controller.Cost Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.ForestClauseProgramConstruction

variable {ambient : Nat}

structure Certificate (width base protectedEnd recordHeader endHeader returnPC : Nat)
    (refs : List (List (Reference ambient))) where
  source : ForestClauseStorage.Certificate width base protectedEnd (reservedReferences refs)
  callerPeak : Nat
  callerTrace : WordConstructionStorage.Trace
    (environment [base + (ForestClauseProgramConstruction.query width base protectedEnd (reservedReferences refs)).1.length,
      recordHeader, endHeader, returnPC]) (code.constructionRecipe width)
    (evaluate (environment [base + (ForestClauseProgramConstruction.query width base protectedEnd (reservedReferences refs)).1.length,
      recordHeader, endHeader, returnPC]) (code.constructionRecipe width)) 806 callerPeak

def buffers (width base protectedEnd recordHeader endHeader returnPC : Nat)
    (refs : List (List (Reference ambient)))
    (certificate : Certificate width base protectedEnd recordHeader endHeader returnPC refs) : Nat :=
  ForestClauseStorage.buffers width base protectedEnd (reservedReferences refs)
    certificate.source.profilePeak certificate.source.headerPeak certificate.source.directoryPeak
      certificate.source.literalPeak certificate.source.finalPeak + certificate.callerPeak +
    32 * (ForestAdmissibleConstruction.construct width base protectedEnd recordHeader endHeader returnPC refs).1.length +
      32 * refs.length + 512

theorem construction (width base protectedEnd recordHeader endHeader returnPC : Nat)
    (refs : List (List (Reference ambient))) :
    ∃ certificate : Certificate width base protectedEnd recordHeader endHeader returnPC refs,
      buffers width base protectedEnd recordHeader endHeader returnPC refs certificate ≤
        100000 + 20000 * refs.length + 40000 * refs.flatten.length := by
  obtain ⟨source, sourceBound⟩ := ForestClauseStorage.construction width base protectedEnd (reservedReferences refs)
  obtain ⟨callerPeak, callerTrace, callerBound⟩ := WordConstructionStorage.construction
    (environment [base + (ForestClauseProgramConstruction.query width base protectedEnd (reservedReferences refs)).1.length,
      recordHeader, endHeader, returnPC]) (code.constructionRecipe width)
  rw [code.constructionRecipe_work] at callerTrace callerBound
  have size := constructorCode_length width base protectedEnd recordHeader endHeader returnPC refs
  rw [← ForestAdmissibleConstruction.construct_image] at size
  simp only [reservedReferences_length, reservedReferences_flatten] at sourceBound
  refine ⟨⟨source, callerPeak, callerTrace⟩, ?_⟩
  dsimp only [buffers]
  omega

end Controller.Cost.ForestAdmissibleStorage
