module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ForestScalarNegativeConstruction
public import Controller.Cost.ForestAdmissibleStorage

@[expose] public section


/-! Complete per-query negative construction storage. Provisional placement,
relocated variable code and every fixed backend operand are independently
traced; the envelope retains both images and their widening/join buffers. -/
namespace Controller.Cost.ForestScalarStorage

open Controller.Cost Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestClauseProgramConstruction
open Controller.Cost.ForestNegativeRecipes

variable {ambient : Nat}

def queryPC (width protectedEnd entry : Nat) (refs : List (List (Reference ambient))) : Nat :=
  entry + 15 + (ForestAdmissibleConstruction.construct width (entry + 15)
    protectedEnd protectedEnd (protectedEnd + 4) 0 refs).1.length

structure Certificate (width protectedEnd channels entry next : Nat)
    (refs : List (List (Reference ambient))) (count : Nat) (coverage : ForestZeroNonempty.Result) where
  provisional : ForestAdmissibleStorage.Certificate width (entry + 15) protectedEnd protectedEnd (protectedEnd + 4) 0 refs
  relocated : ForestAdmissibleStorage.Certificate width (entry + 15) protectedEnd protectedEnd (protectedEnd + 4)
    (queryPC width protectedEnd entry refs) refs
  entryPeak : Nat
  suffixPeak : Nat
  entryTrace : WordConstructionStorage.Trace (environment [protectedEnd + 5 + 2 * (refs.length + 1)])
    (entryCode.constructionRecipe width)
    (evaluate (environment [protectedEnd + 5 + 2 * (refs.length + 1)]) (entryCode.constructionRecipe width)) 134 entryPeak
  suffixTrace : WordConstructionStorage.Trace
    (environment [protectedEnd, ForestScalarNegativeConstruction.heapEnd protectedEnd channels refs coverage,
      count, queryPC width protectedEnd entry refs, next]) (suffixRecipes width)
    (evaluate (environment [protectedEnd, ForestScalarNegativeConstruction.heapEnd protectedEnd channels refs coverage,
      count, queryPC width protectedEnd entry refs, next]) (suffixRecipes width)) (work (suffixRecipes width)) suffixPeak

def buffers (width protectedEnd channels entry next : Nat) (refs : List (List (Reference ambient)))
    (count : Nat) (coverage : ForestZeroNonempty.Result)
    (certificate : Certificate width protectedEnd channels entry next refs count coverage) : Nat :=
  ForestAdmissibleStorage.buffers width (entry + 15) protectedEnd protectedEnd (protectedEnd + 4) 0 refs certificate.provisional +
    ForestAdmissibleStorage.buffers width (entry + 15) protectedEnd protectedEnd (protectedEnd + 4)
      (queryPC width protectedEnd entry refs) refs certificate.relocated + certificate.entryPeak + certificate.suffixPeak +
    32 * (ForestScalarNegativeConstruction.form width protectedEnd channels entry next refs count coverage).1.length +
      64 * refs.length + 64 * refs.flatten.length + 2048

theorem construction (width protectedEnd channels entry next : Nat)
    (refs : List (List (Reference ambient))) (count : Nat) (coverage : ForestZeroNonempty.Result) :
    ∃ certificate : Certificate width protectedEnd channels entry next refs count coverage,
      buffers width protectedEnd channels entry next refs count coverage certificate ≤
        600000 + 50000 * refs.length + 100000 * refs.flatten.length := by
  obtain ⟨provisional, provisionalBound⟩ := ForestAdmissibleStorage.construction width (entry + 15)
    protectedEnd protectedEnd (protectedEnd + 4) 0 refs
  obtain ⟨relocated, relocatedBound⟩ := ForestAdmissibleStorage.construction width (entry + 15)
    protectedEnd protectedEnd (protectedEnd + 4) (queryPC width protectedEnd entry refs) refs
  obtain ⟨entryPeak, entryTrace, entryBound⟩ := WordConstructionStorage.construction
    (environment [protectedEnd + 5 + 2 * (refs.length + 1)]) (entryCode.constructionRecipe width)
  rw [entryCode.constructionRecipe_work] at entryTrace entryBound
  obtain ⟨suffixPeak, suffixTrace, suffixBound⟩ := WordConstructionStorage.construction
    (environment [protectedEnd, ForestScalarNegativeConstruction.heapEnd protectedEnd channels refs coverage,
      count, queryPC width protectedEnd entry refs, next]) (suffixRecipes width)
  have suffixWork := ForestNegativeConstruction.suffix_work width
  have codeSize := ForestScalarNegativeConstruction.instruction_bound width protectedEnd channels entry next refs count coverage
  refine ⟨⟨provisional, relocated, entryPeak, suffixPeak, entryTrace, suffixTrace⟩, ?_⟩
  dsimp only [buffers]
  omega

end Controller.Cost.ForestScalarStorage
