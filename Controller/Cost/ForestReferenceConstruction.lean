/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ForestReferenceWork

/-! Charged source-clause construction. The recursive result carries the
actual emitted rows and its construction clock; it does not first allocate a
semantic traversal tree or annotated node paths. The suffix is shared, so only
each node's newly formed rows are copied by the local append. -/
namespace Controller.Cost.ForestReferenceConstruction

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestWeightedIndexed
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroSource

variable {n nodes : Nat}

def form (table : Source n) (cache : ForestCompilerOffsets.State) (owner : Fin nodes)
    (incoming : Reference (n + nodes)) (tail : List (List (Reference (n + nodes)))) :
    List (List (Reference (n + nodes))) × Nat :=
  let gate := readNode table owner.val
  let below := gate.children.zipIdx.foldr (fun item suffix =>
    let one := form table cache (⟨item.1.val, item.1.isLt.trans owner.isLt⟩ : Fin nodes)
      (ForestCachedReferences.child cache owner item.2 item.1) suffix.1
    (one.1, one.2 + suffix.2 + 4)) (tail, 0)
  (ForestCachedReferences.own table cache owner incoming ++ below.1,
    ForestReferenceWork.localWork table cache owner incoming + below.2 + 8)
termination_by owner.val
decreasing_by exact Fin.isLt _

/-- The returned rows are exactly those used by the existing physical source
query. The clock is accumulated by this same recursive producer. -/
theorem form_image (table : Source n) (cache : ForestCompilerOffsets.State) :
    ∀ owner : Fin nodes, ∀ incoming tail,
      (form table cache owner incoming tail).1 = ForestCachedReferences.walk table cache owner incoming tail := by
  have claim : ∀ rank, ∀ owner : Fin nodes, owner.val = rank → ∀ incoming tail,
      (form table cache owner incoming tail).1 = ForestCachedReferences.walk table cache owner incoming tail := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro owner equal incoming tail
      rw [form.eq_def, ForestCachedReferences.walk.eq_def]
      dsimp only
      congr 1
      have fold : ∀ items : List (Fin owner.val × Nat),
          (items.foldr (fun item suffix =>
            let one := form table cache (⟨item.1.val, item.1.isLt.trans owner.isLt⟩ : Fin nodes)
              (ForestCachedReferences.child cache owner item.2 item.1) suffix.1
            (one.1, one.2 + suffix.2 + 4)) (tail, 0)).1 =
          items.foldr (fun item suffix => ForestCachedReferences.walk table cache
            (⟨item.1.val, item.1.isLt.trans owner.isLt⟩ : Fin nodes)
            (ForestCachedReferences.child cache owner item.2 item.1) suffix) tail := by
        intro items
        induction items with
        | nil => rfl
        | cons item rest tailEq =>
            simp only [List.foldr_cons]
            rw [ih item.1.val (by omega) _ rfl, tailEq]
      exact fold _
  intro owner incoming tail
  exact claim owner.val owner rfl incoming tail

/-- The concrete producer fits the original source-occurrence envelope. Its
charge covers local field/reference formation, row copies and child control. -/
theorem form_work (table : Source n) (cache : ForestCompilerOffsets.State) :
    ∀ owner : Fin nodes, ∀ incoming tail,
      (form table cache owner incoming tail).2 ≤ 2 * ForestReferenceWork.budget table owner := by
  have claim : ∀ rank, ∀ owner : Fin nodes, owner.val = rank → ∀ incoming tail,
      (form table cache owner incoming tail).2 ≤ 2 * ForestReferenceWork.budget table owner := by
    intro rank
    induction rank using Nat.strong_induction_on with
    | h rank ih =>
      intro owner equal incoming tail
      let gate := readNode table owner.val
      have folded : ∀ items : List (Fin owner.val × Nat),
          (items.foldr (fun item suffix =>
            let one := form table cache (⟨item.1.val, item.1.isLt.trans owner.isLt⟩ : Fin nodes)
              (ForestCachedReferences.child cache owner item.2 item.1) suffix.1
            (one.1, one.2 + suffix.2 + 4)) (tail, 0)).2 ≤
          2 * (items.map fun item => ForestReferenceWork.budget table
            (⟨item.1.val, item.1.isLt.trans owner.isLt⟩ : Fin nodes)).sum + 4 * items.length := by
        intro items
        induction items with
        | nil => simp
        | cons item rest tailBound =>
            have one := ih item.1.val (by omega)
              (⟨item.1.val, item.1.isLt.trans owner.isLt⟩ : Fin nodes) rfl
              (ForestCachedReferences.child cache owner item.2 item.1)
              (rest.foldr (fun item suffix =>
                let one := form table cache (⟨item.1.val, item.1.isLt.trans owner.isLt⟩ : Fin nodes)
                  (ForestCachedReferences.child cache owner item.2 item.1) suffix.1
                (one.1, one.2 + suffix.2 + 4)) (tail, 0)).1
            simp only [List.foldr_cons, List.map_cons, List.sum_cons, List.length_cons]
            dsimp only at one tailBound ⊢
            omega
      have descendants := folded gate.children.zipIdx
      have zip : (gate.children.zipIdx.map fun item => ForestReferenceWork.budget table
          (⟨item.1.val, item.1.isLt.trans owner.isLt⟩ : Fin nodes)) =
          gate.children.map (fun child => ForestReferenceWork.budget table
            (⟨child.val, child.isLt.trans owner.isLt⟩ : Fin nodes)) := by
        have mapped := congrArg (List.map (fun child : Fin owner.val => ForestReferenceWork.budget table
          (⟨child.val, child.isLt.trans owner.isLt⟩ : Fin nodes))) (List.zipIdx_map_fst 0 gate.children)
        simpa only [List.map_map, Function.comp_def] using mapped
      rw [zip, List.length_zipIdx] at descendants
      have ownWork := ForestReferenceWork.local_bound table cache owner incoming
      rw [form.eq_def, ForestReferenceWork.budget.eq_def]
      change ForestReferenceWork.localWork table cache owner incoming + _ + 8 ≤ _
      change _ ≤ 80 + 64 * gate.children.length + 40 * gate.guardLabels.length at ownWork
      dsimp only [gate] at descendants ownWork ⊢
      omega
  intro owner incoming tail
  exact claim owner.val owner rfl incoming tail

end Controller.Cost.ForestReferenceConstruction
