module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ForestClauseProgramConstruction

@[expose] public section


/-! Charged image construction for the complete reserved-row query caller.
The constructor includes the variable source clause program and the fixed
nonemptiness dispatch, including operand arithmetic and program copying. -/
namespace Controller.Cost.ForestAdmissibleConstruction

open Controller.Cost Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.ForestClauseProgramConstruction

variable {ambient : Nat}

def construct (width base protectedEnd recordHeader endHeader returnPC : Nat)
    (refs : List (List (Reference ambient))) : GateProgram.Code width × Nat :=
  let source := ForestClauseProgramConstruction.query width base protectedEnd (reservedReferences refs)
  let recipes := code.constructionRecipe width
  let caller := evaluate (environment [base + source.1.length, recordHeader, endHeader, returnPC]) recipes
  (source.1 ++ caller, source.2 + work recipes + 2 * source.1.length + refs.length + 30)

theorem caller_image (width base recordHeader endHeader returnPC : Nat) :
    evaluate (environment [base, recordHeader, endHeader, returnPC]) (code.constructionRecipe width) =
      code width base recordHeader endHeader returnPC := by
  change evaluate (fun index => [base, recordHeader, endHeader, returnPC].getD index.val 0) _ = _
  exact code.constructionRecipe_eq width base recordHeader endHeader returnPC

theorem construct_image (width base protectedEnd recordHeader endHeader returnPC : Nat)
    (refs : List (List (Reference ambient))) :
    (construct width base protectedEnd recordHeader endHeader returnPC refs).1 =
      constructorCode width base protectedEnd recordHeader endHeader returnPC refs := by
  simp only [construct, caller_image, ForestClauseProgramConstruction.query_image, constructorCode]

theorem construct_work (width base protectedEnd recordHeader endHeader returnPC : Nat)
    (refs : List (List (Reference ambient))) :
    (construct width base protectedEnd recordHeader endHeader returnPC refs).2 ≤
      1500 + 100 * refs.length + 450 * refs.flatten.length := by
  have source := query_work width base protectedEnd (reservedReferences refs)
  have size := ForestZeroQueryCaller.queryCode_length width base protectedEnd (reservedReferences refs)
  rw [← ForestClauseProgramConstruction.query_image] at size
  simp only [reservedReferences_length, reservedReferences_flatten] at source size
  simp only [construct, code.constructionRecipe_work]
  omega

/-- The reserved source row and the generated program prefix are copied by
explicit append traversals, not by a free concatenation operation. -/
theorem construction_traces (width base protectedEnd recordHeader endHeader returnPC : Nat)
    (refs : List (List (Reference ambient))) :
    CompilerAppendTrace.AppendTrace refs [[]] (reservedReferences refs) refs.length ∧
      WordConstructionRecipe.Trace
        (environment [base + (ForestClauseProgramConstruction.query width base protectedEnd (reservedReferences refs)).1.length,
          recordHeader, endHeader, returnPC]) (code.constructionRecipe width)
        (code width (base + (ForestClauseProgramConstruction.query width base protectedEnd (reservedReferences refs)).1.length)
          recordHeader endHeader returnPC) 806 := by
  constructor
  · exact CompilerAppendTrace.append_exists _ _
  · have trace := WordConstructionRecipe.trace
      (environment [base + (ForestClauseProgramConstruction.query width base protectedEnd (reservedReferences refs)).1.length,
        recordHeader, endHeader, returnPC]) (code.constructionRecipe width)
    rw [caller_image, code.constructionRecipe_work] at trace
    exact trace

end Controller.Cost.ForestAdmissibleConstruction
