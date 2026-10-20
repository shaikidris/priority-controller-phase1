/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ForestSourceConstruction
import Controller.Cost.ForestCompilerOffsets

/-! Source validation and cache construction storage. Checked ID conversion
retains scalar/list continuations, and the source/cache arrays grow once in
source order. Original rows and their unread list tails are shared input. -/
namespace Controller.Cost.ForestSourcePreparationStorage

open Controller.Cost Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestSourceConstruction

inductive IdTrace (bound : Nat) : List Nat → Option (List (Fin bound)) → Nat → Nat → Prop
  | nil : IdTrace bound [] (some []) 1 16
  | rejected (value rest) (invalid : ¬value < bound) : IdTrace bound (value :: rest) none 2 16
  | accepted (value rest result ticks peak) (valid : value < bound)
      (tail : IdTrace bound rest result ticks peak) :
      IdTrace bound (value :: rest) (result.map (⟨value, valid⟩ :: ·)) (ticks + 4) (peak + 16)

theorem ids_space (bound : Nat) (values : List Nat) :
    ∃ peak, IdTrace bound values (ids bound values).1 (ids bound values).2 peak ∧
      peak ≤ 16 * values.length + 16 := by
  induction values with
  | nil => exact ⟨16, .nil, by simp⟩
  | cons value rest ih =>
      dsimp only [ids]
      split_ifs with valid
      · obtain ⟨peak, trace, space⟩ := ih
        exact ⟨peak + 16, .accepted value rest _ _ _ valid trace, by simp only [List.length_cons]; omega⟩
      · exact ⟨16, .rejected value rest valid, by omega⟩

/-- Both validated incidence outputs may be retained while forming a gate. -/
structure RowTrace (channels owner : Nat) (record : Row) where
  childPeak : Nat
  guardPeak : Nat
  children : IdTrace owner record.children (ids owner record.children).1 (ids owner record.children).2 childPeak
  guards : IdTrace channels record.guards (ids channels record.guards).1 (ids channels record.guards).2 guardPeak

def rowWords (record : Row) (childPeak guardPeak : Nat) : Nat :=
  max childPeak (guardPeak + 8 * record.children.length) + 32

theorem row_space (channels owner : Nat) (record : Row) :
    ∃ trace : RowTrace channels owner record,
      rowWords record trace.childPeak trace.guardPeak ≤
        32 * record.children.length + 32 * record.guards.length + 64 := by
  obtain ⟨childPeak, children, childBound⟩ := ids_space owner record.children
  obtain ⟨guardPeak, guards, guardBound⟩ := ids_space channels record.guards
  refine ⟨⟨childPeak, guardPeak, children, guards⟩, ?_⟩
  dsimp only [rowWords]
  have bound : max childPeak (guardPeak + 8 * record.children.length) ≤
      32 * record.children.length + 32 * record.guards.length + 32 :=
    Nat.max_le.mpr ⟨by omega, by omega⟩
  omega

/-- A gate, its option/rank wrapper and copied incidence IDs are retained by
the source-list continuation until the final source array is materialized. -/
def gateWords (record : Row) : Nat := 8 * record.children.length + 8 * record.guards.length + 16

inductive ItemsTrace (channels : Nat) : Nat → List Row → Nat → Prop
  | nil (owner) : ItemsTrace channels owner [] 32
  | cons (owner record rest peak) (row : RowTrace channels owner record)
      (tail : ItemsTrace channels (owner + 1) rest peak) :
      ItemsTrace channels owner (record :: rest)
        (max (rowWords record row.childPeak row.guardPeak) (peak + gateWords record + 32))

theorem items_space (channels owner : Nat) (rows : List Row) :
    ∃ peak, ItemsTrace channels owner rows peak ∧
      peak ≤ 128 * ((rowChildren rows).length + (rowGuards rows).length + rows.length + 1) := by
  induction rows generalizing owner with
  | nil => exact ⟨32, .nil owner, by simp [rowChildren, rowGuards]⟩
  | cons record rest ih =>
      obtain ⟨row, rowBound⟩ := row_space channels owner record
      obtain ⟨peak, tail, tailBound⟩ := ih (owner + 1)
      refine ⟨max (rowWords record row.childPeak row.guardPeak) (peak + gateWords record + 32),
        .cons owner record rest peak row tail, ?_⟩
      simp only [rowChildren, rowGuards, List.flatMap_cons, List.length_append, List.length_cons] at tailBound ⊢
      dsimp only [gateWords]
      exact Nat.max_le.mpr ⟨by omega, by omega⟩

def cacheWords (cache : ForestCompilerOffsets.State) : Nat := 16 + 8 * cache.rows.size + 8 * cache.offsets.size

inductive CacheTrace : List Row → ForestCompilerOffsets.State → ForestCompilerOffsets.State → Nat → Prop
  | nil (cache) : CacheTrace [] cache cache (cacheWords cache + 32)
  | cons (row rest cache final peak)
      (tail : CacheTrace rest (ForestCompilerOffsets.step cache row) final peak) :
      CacheTrace (row :: rest) cache final (max (cacheWords cache + 32) peak)

theorem cache_space (rows : List Row) (cache : ForestCompilerOffsets.State) :
    ∃ peak, CacheTrace rows cache (ForestCompilerOffsets.run rows cache) peak ∧
      peak ≤ cacheWords cache + 16 * rows.length + 32 := by
  induction rows generalizing cache with
  | nil => exact ⟨cacheWords cache + 32, .nil cache, by simp⟩
  | cons row rest ih =>
      obtain ⟨peak, trace, bound⟩ := ih (ForestCompilerOffsets.step cache row)
      have increase : cacheWords (ForestCompilerOffsets.step cache row) = cacheWords cache + 16 := by
        simp only [cacheWords, ForestCompilerOffsets.step, Array.size_push]
        omega
      rw [increase] at bound
      refine ⟨max (cacheWords cache + 32) peak, .cons row rest cache _ _ trace, ?_⟩
      simp only [List.length_cons]
      exact Nat.max_le.mpr ⟨by omega, by omega⟩

end Controller.Cost.ForestSourcePreparationStorage
