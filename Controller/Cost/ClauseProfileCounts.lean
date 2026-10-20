/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.SharedNormalizationShape
import Controller.Cost.ResolvedPlanProducer

/-! Source-field normalization counts. Guard labels are counted by finite
channel membership; no Boolean assignment is chosen to construct a program. -/
namespace Controller.Cost.ClauseProfileCounts

open Controller.CNF Controller.Cost Controller.Horn

variable {n m : Nat}

def unique (labels : List (Fin n)) : Nat × Nat :=
  (((List.finRange n).filter labels.contains).length, 32 * n * (labels.length + 1) + 16)

theorem unique_value (labels : List (Fin n)) : (unique labels).1 = labels.dedup.length := by
  have distinct : ((List.finRange n).filter labels.contains).Nodup := (List.nodup_finRange n).filter
    _
  have same : ((List.finRange n).filter labels.contains).toFinset = labels.toFinset := by
    ext index
    simp
  have left := List.toFinset_card_of_nodup distinct
  have right := List.card_toFinset labels
  rw [same] at left
  exact left.symm.trans right

theorem positive_count {α : Type} [DecidableEq α] (clause : Clause α)
    (notTautology : Worklist.tautologyCheck clause = false) :
    (Worklist.compileClause clause).positives.length =
      ((clause.filter fun literal => decide (literal.2 = true)).map Prod.fst).toFinset.card := by
  have cardinal := List.card_toFinset ((clause.filter fun literal => decide (literal.2 = true)).map
    Prod.fst)
  unfold Worklist.compileClause
  rw [if_neg (by simp [notTautology])]
  cases negatives : Worklist.signedLabels clause false <;>
    simpa only [Worklist.Rule.positives, Worklist.signedLabels] using cardinal.symm

theorem positive_clause {α : Type} [DecidableEq α] (labels : List α) :
    (Worklist.compileClause (labels.map fun label => (label, true))).positives.length =
      labels.dedup.length := by
  let row : Clause α := labels.map fun label => (label, true)
  have falseRow : ¬ClauseHolds (fun _ : α => false) row := by simp [row, ClauseHolds, LiteralHolds]
  have notTautology : Worklist.tautologyCheck row = false := by
    apply Bool.eq_false_iff.mpr
    intro tautology
    obtain ⟨literal, member, opposite⟩ := (Worklist.tautologyCheck_eq_true row).mp tautology
    exact falseRow (tautology_holds (fun _ => false) member opposite)
  have count := positive_count row notTautology
  have keep : row.filter (fun literal => decide (literal.2 = true)) = row := by
    apply List.filter_eq_self.mpr
    intro literal member
    obtain ⟨label, _, rfl⟩ := List.mem_map.mp member
    rfl
  have filtered : (row.filter (fun literal => decide (literal.2 = true))).map Prod.fst = labels :=
    by
    rw [keep]
    simp [row, Function.comp_def]
  rw [filtered] at count
  calc
    (Worklist.compileClause row).positives.length = labels.toFinset.card := count
    _ = labels.dedup.length := List.card_toFinset labels

theorem implication_count (child parent : Fin m) (different : child ≠ parent) (labels : List (Fin
  n)) :
    (Worklist.compileClause ((Sum.inr child, false) ::
      (labels.map fun channel => (Sum.inl channel, true)) ++ [(Sum.inr parent,
        true)])).positives.length =
      labels.dedup.length + 1 := by
  let row : Clause (Fin n ⊕ Fin m) := (Sum.inr child, false) ::
    (labels.map fun channel => (Sum.inl channel, true)) ++ [(Sum.inr parent, true)]
  let values : Fin n ⊕ Fin m → Bool := fun coordinate => match coordinate with
    | .inl _ => false
    | .inr index => decide (index = child)
  have falseRow : ¬ClauseHolds values row := by
    simp [row, ClauseHolds, LiteralHolds, values, different, Ne.symm different]
  have notTautology : Worklist.tautologyCheck row = false := by
    apply Bool.eq_false_iff.mpr
    intro tautology
    obtain ⟨literal, member, opposite⟩ := (Worklist.tautologyCheck_eq_true row).mp tautology
    exact falseRow (tautology_holds values member opposite)
  have count := positive_count row notTautology
  have members : ((row.filter fun literal => decide (literal.2 = true)).map Prod.fst).toFinset =
      insert (Sum.inr parent) (labels.toFinset.image (Sum.inl : Fin n → Fin n ⊕ Fin m)) := by
    ext index
    cases index <;> simp [row]
  have cardinal : (labels.toFinset.image (Sum.inl : Fin n → Fin n ⊕ Fin m)).card =
    labels.toFinset.card :=
    Finset.card_image_of_injective _ Sum.inl_injective
  have dedup := List.card_toFinset labels
  change (Worklist.compileClause row).positives.length = _
  rw [count, members, Finset.card_insert_of_notMem (by simp), cardinal, dedup]

end Controller.Cost.ClauseProfileCounts
