module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.BasisColumnConstruction

@[expose] public section


/-! Contradiction-table instructions are constructed from source sign-cell
addresses. Their flags are computed by fetched reads, comparisons and stores. -/
namespace Controller.Cost.BasisConflictConstruction

open Controller.Cost Controller.Extensions Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestClauseProgramConstruction (environment)

def pairCode (width entry positive negative flag : Nat) : List (Instruction width 8) :=
  (LiteralConflict.code width entry positive negative flag).toList

def initialCode (width address : Nat) : List (Instruction width 8) :=
  [.constant 0 (word width address), .load 1 0, .allocate 1]

derive_extension_recipe pairCode

derive_extension_recipe initialCode

def pairs (width flag : Nat) : Nat → List (Nat × Nat) → List (Instruction width 8) × Nat
  | _, [] => ([], 1)
  | entry, pair :: rest =>
      let head := evaluate (environment [entry, pair.1, pair.2, flag]) (pairCode.constructionRecipe
        width)
      let tail := pairs width flag (entry + 9) rest
      (head ++ tail.1, work (pairCode.constructionRecipe width) + tail.2 + 200)

theorem pairs_image (width flag entry : Nat) (values : List (Nat × Nat)) :
    (pairs width flag entry values).1 = (LiteralConflict.scanCode width flag entry values).toList :=
      by
  have formed (entry : Nat) (pair : Nat × Nat) :
      evaluate (environment [entry, pair.1, pair.2, flag]) (pairCode.constructionRecipe width) =
        pairCode width entry pair.1 pair.2 flag :=
    pairCode.constructionRecipe_eq width entry pair.1 pair.2 flag
  induction values generalizing entry with
  | nil => rfl
  | cons pair rest ih =>
      simp only [pairs]
      rw [formed, ih]
      cases pair
      simp only [pairCode, LiteralConflict.scanCode, Array.toList_append]

theorem pairs_clock (width flag entry : Nat) (values : List (Nat × Nat)) :
    (pairs width flag entry values).2 ≤ 1000 * values.length + 1 := by
  induction values generalizing entry with
  | nil => simp [pairs]
  | cons pair rest ih =>
      simp only [pairs, pairCode.constructionRecipe_work, List.length_cons]
      have tail := ih (entry + 9)
      omega


def build (width : Nat) : Nat → Nat → List LiteralConflict.Job → List (Instruction width 8) × Nat
  | _, _, [] => ([], 1)
  | entry, flag, job :: rest =>
      let first := evaluate (environment [job.zeroAddress]) (initialCode.constructionRecipe width)
      let scan := pairs width flag (entry + 3) job.pairs
      let tail := build width (entry + 3 + 9 * job.pairs.length) (flag + 1) rest
      let head := first ++ scan.1
      (head ++ tail.1, scan.2 + tail.2 + 16 * head.length + 1000)

theorem image (width entry flag : Nat) (jobs : List LiteralConflict.Job) :
    (build width entry flag jobs).1 = (LiteralConflict.jobsCode width entry flag jobs).toList := by
  have formed (address : Nat) : evaluate (environment [address]) (initialCode.constructionRecipe
    width) = initialCode width address :=
    initialCode.constructionRecipe_eq width address
  induction jobs generalizing entry flag with
  | nil => rfl
  | cons job rest ih =>
      simp only [build, formed, pairs_image, ih, initialCode, LiteralConflict.jobsCode,
        LiteralConflict.jobCode, Array.toList_append, Nat.add_assoc, List.append_assoc]

theorem clock (width entry flag : Nat) (jobs : List LiteralConflict.Job) :
    (build width entry flag jobs).2 ≤ 2000 * LiteralConflict.work jobs + 1 := by
  induction jobs generalizing entry flag with
  | nil => simp [build, LiteralConflict.work]
  | cons job rest ih =>
      have scan := pairs_clock width flag (entry + 3) job.pairs
      have tail := ih (entry + 3 + 9 * job.pairs.length) (flag + 1)
      have length : ((evaluate (environment [job.zeroAddress]) (initialCode.constructionRecipe
        width)) ++
          (pairs width flag (entry + 3) job.pairs).1).length = 3 + 9 * job.pairs.length := by
        rw [pairs_image]
        simp only [evaluate, List.length_map, List.length_append, Array.length_toList,
          LiteralConflict.scanCode_size]
        rfl
      simp only [build, LiteralConflict.work, List.map_cons, List.sum_cons]
      rw [length]
      simp only [LiteralConflict.work] at tail
      omega

end Controller.Cost.BasisConflictConstruction
