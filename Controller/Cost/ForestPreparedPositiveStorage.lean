module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ForestPreparedPositive
public import Controller.Cost.ForestClauseProgramConstruction
public import Controller.Cost.ForestPositiveStorage

@[expose] public section


/-! Storage of the actual selected positive-branch assembler. Prefix operands,
descriptors, witness code and cleanup have traced formation; widening and final
array buffers are retained in the same bound. -/
namespace Controller.Cost.ForestPreparedPositiveStorage

open Controller.Cost Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestRootProjection Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestClauseProgramConstruction

variable {n : Nat} {W : Type}

structure Front (prior : Program width 8) (failure : Nat) (selected : Option (Candidate W)) where
  maskPeak : Nat
  selectorPeak : Nat
  mask : WordConstructionStorage.Trace (fun i : Fin 0 => [].getD i.val 0)
    (mixedMaskCode.constructionRecipe width)
    (evaluate (fun i : Fin 0 => [].getD i.val 0) (mixedMaskCode.constructionRecipe width)) 20 maskPeak
  selector : WordConstructionStorage.Trace
    (environment [failure, if selected.isSome then 1 else 0])
    (ForestFixedControlRecipes.selector.constructionRecipe width)
    (evaluate (environment [failure, if selected.isSome then 1 else 0])
      (ForestFixedControlRecipes.selector.constructionRecipe width)) 20 selectorPeak

def frontWords (prior : Program width 8) (failure : Nat) (selected : Option (Candidate W))
    (front : Front prior failure selected) : Nat := front.maskPeak + front.selectorPeak + 32 * prior.size + 256

theorem front_space (prior : Program width 8) (failure : Nat) (selected : Option (Candidate W)) :
    ∃ front : Front prior failure selected, frontWords prior failure selected front ≤ 2000 + 32 * prior.size := by
  obtain ⟨maskPeak, mask, maskBound⟩ := WordConstructionStorage.construction
    (fun i : Fin 0 => [].getD i.val 0) (mixedMaskCode.constructionRecipe width)
  obtain ⟨selectorPeak, selector, selectorBound⟩ := WordConstructionStorage.construction
    (environment [failure, if selected.isSome then 1 else 0]) (ForestFixedControlRecipes.selector.constructionRecipe width)
  rw [mixedMaskCode.constructionRecipe_work] at mask maskBound
  rw [ForestFixedControlRecipes.selector.constructionRecipe_work] at selector selectorBound
  refine ⟨⟨maskPeak, selectorPeak, mask, selector⟩, ?_⟩
  dsimp only [frontWords]
  omega

def items (prior : Program width 8) (nodes children guards roots : Nat)
    (state : ForestWeightedIndexed.State n W) (candidate : Candidate W) :=
  ForestPositiveConstruction.form width 5 nodes children guards roots (prior.size + 5) 0 state candidate

def endAt (prior : Program width 8) (nodes children guards roots : Nat)
    (state : ForestWeightedIndexed.State n W) (candidate : Candidate W) :=
  prior.size + 5 + (items prior nodes children guards roots state candidate).length

def allocated (nodes children guards roots : Nat) (state : ForestWeightedIndexed.State n W) :=
  5 + 6 * nodes + children + guards + roots + 2 * state.descriptors.count + (n + 3)

inductive Trace (prior : Program width 8) (nodes children guards roots : Nat)
    (state : ForestWeightedIndexed.State n W) : Nat → Prop
  | none (selected : state.selected = none) (front : Front prior (prior.size + 5) state.selected) :
      Trace prior nodes children guards roots state (frontWords prior (prior.size + 5) state.selected front)
  | some (candidate) (selected : state.selected = some candidate)
      (front : Front prior (endAt prior nodes children guards roots state candidate + 14) state.selected)
      (positive : ForestPositiveStorage.Certificate width 5 nodes children guards roots (prior.size + 5) 0 state candidate)
      (cleanupPeak : Nat)
      (cleanup : WordConstructionStorage.Trace
        (environment [endAt prior nodes children guards roots state candidate, allocated nodes children guards roots state,
          5 + 6 * nodes + children + guards]) (positiveTargetCleanupCode.constructionRecipe width)
        (evaluate (environment [endAt prior nodes children guards roots state candidate, allocated nodes children guards roots state,
          5 + 6 * nodes + children + guards]) (positiveTargetCleanupCode.constructionRecipe width)) 140 cleanupPeak) :
      Trace prior nodes children guards roots state
        (frontWords prior (endAt prior nodes children guards roots state candidate + 14) state.selected front +
          ForestPositiveStorage.bufferWords width state candidate positive.descriptorPeak positive.witnessPeak + cleanupPeak +
            32 * (items prior nodes children guards roots state candidate).length + 512)

theorem items_length (prior : Program width 8) (nodes children guards roots : Nat)
    (state : ForestWeightedIndexed.State n W) (candidate : Candidate W) :
    (items prior nodes children guards roots state candidate).length = 4 * state.descriptors.entries.length + 2 * n + 100 := by
  simp only [items, ForestPositiveConstruction.form, List.length_append, evaluate, List.length_map,
    ForestPositiveConstruction.leading_length]
  change 4 * state.descriptors.entries.length + 2 * n + 8 + 92 = _
  omega

theorem construction (prior : Program width 8) (nodes children guards roots : Nat)
    (state : ForestWeightedIndexed.State n W) :
    ∃ peak, Trace prior nodes children guards roots state peak ∧
      peak ≤ 100000 + 400 * state.descriptors.entries.length + 200 * n + 32 * prior.size := by
  cases selected : state.selected with
  | none =>
      obtain ⟨front, bound⟩ := front_space prior (prior.size + 5) state.selected
      exact ⟨_, .none selected front, by omega⟩
  | some candidate =>
      obtain ⟨front, frontBound⟩ := front_space prior (endAt prior nodes children guards roots state candidate + 14) state.selected
      obtain ⟨positive, positiveBound⟩ := ForestPositiveStorage.certificate width 5 nodes children guards roots (prior.size + 5) 0 state candidate
      obtain ⟨cleanupPeak, cleanup, cleanupBound⟩ := WordConstructionStorage.construction
        (environment [endAt prior nodes children guards roots state candidate, allocated nodes children guards roots state,
          5 + 6 * nodes + children + guards]) (positiveTargetCleanupCode.constructionRecipe width)
      rw [positiveTargetCleanupCode.constructionRecipe_work] at cleanup cleanupBound
      refine ⟨_, .some candidate selected front positive cleanupPeak cleanup, ?_⟩
      rw [items_length]
      omega

end Controller.Cost.ForestPreparedPositiveStorage
