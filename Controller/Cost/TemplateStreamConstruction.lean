module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.WordConstructionStorage
public import Controller.Cost.CompilerAppendTrace
public import Mathlib.Tactic.Linarith

@[expose] public section


/-! Construction of a stream of fixed templates over supplied scalar records.
Record production is charged by the caller. Every record is read through its
finite environment, and every resulting instruction block is formed and copied. -/
namespace Controller.Cost.TemplateStreamConstruction

open Controller.Cost Controller.Cost.WordConstructionRecipe

def build (recipes : List (InstructionRecipe parameters width registers))
    (records : Nat → Fin parameters → Nat) (start : Nat) : Nat → List (Instruction width registers) × Nat
  | 0 => ([], 1)
  | count + 1 =>
      let current := evaluate (records start) recipes
      let tail := build recipes records (start + 1) count
      (current ++ tail.1, work recipes + recipes.length + tail.2 + 24)

theorem image (recipes : List (InstructionRecipe parameters width registers))
    (records : Nat → Fin parameters → Nat) (start count : Nat) :
    (build recipes records start count).1 =
      (List.range count).flatMap (fun i => evaluate (records (start + i)) recipes) := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      simp only [build, ih, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, Nat.add_zero]
      congr 1
      apply List.flatMap_congr
      intro i member
      congr 2
      omega

theorem clock (recipes : List (InstructionRecipe parameters width registers))
    (records : Nat → Fin parameters → Nat) (start count : Nat) :
    (build recipes records start count).2 =
      count * (work recipes + recipes.length + 24) + 1 := by
  induction count generalizing start with
  | zero => simp [build]
  | succ count ih => simp only [build, ih, Nat.succ_mul]; omega

inductive Trace (recipes : List (InstructionRecipe parameters width registers))
    (records : Nat → Fin parameters → Nat) : Nat → Nat → List (Instruction width registers) → Nat → Nat → Prop
  | nil (start) : Trace recipes records start 0 [] 1 32
  | cons {start count current output first later p q}
      (formed : WordConstructionStorage.Trace (records start) recipes current first p)
      (tail : Trace recipes records (start + 1) count output later q)
      (copied : CompilerAppendTrace.AppendTrace current output (current ++ output) current.length) :
      Trace recipes records start (count + 1) (current ++ output)
        (first + recipes.length + later + 24) (max p (q + 16 * recipes.length + 32))

theorem storage (recipes : List (InstructionRecipe parameters width registers))
    (records : Nat → Fin parameters → Nat) (start count : Nat) :
    ∃ peak, Trace recipes records start count (build recipes records start count).1
      (build recipes records start count).2 peak ∧
      peak ≤ 32 * (count + 1) * (work recipes + recipes.length + 2) := by
  induction count generalizing start with
  | zero => exact ⟨32, .nil start, by omega⟩
  | succ count ih =>
      obtain ⟨p, formed, bound⟩ := WordConstructionStorage.construction (records start) recipes
      obtain ⟨q, tail, tailBound⟩ := ih (start + 1)
      refine ⟨_, .cons formed tail (CompilerAppendTrace.append_exists _ _), ?_⟩
      have positivity : 0 < count + 1 := by omega
      apply Nat.max_le.mpr
      constructor
      · nlinarith
      · nlinarith

end Controller.Cost.TemplateStreamConstruction
