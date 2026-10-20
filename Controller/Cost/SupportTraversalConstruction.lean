module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.SupportCandidateConstruction

@[expose] public section


/-! The complete bounded-support controller is constructed from scalar source
counts. A zero-filled header supplies layout only; no healthy evaluation or
successful support is a constructor input. -/
namespace Controller.Cost.SupportTraversalConstruction

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Cost.WordConstructionRecipe Controller.Cost.ExtensionConstructionRecipes
open Controller.Cost.ForestClauseProgramConstruction (environment)
open Controller.Cost.ForestIndexedOperands

def mask (width : Nat) : Nat → List (Instruction width 8) × Nat
  | 0 => ([], 1)
  | count + 1 =>
      let current := evaluate (environment [0]) (literalOperand.constructionRecipe width)
      let tail := mask width count
      (current ++ tail.1, tail.2 + 40)

theorem mask_image (width count : Nat) :
    (mask width count).1 = SharedCoordinateTable.code width (List.replicate count (word width 0)) := by
  have formed : evaluate (environment [0]) (literalOperand.constructionRecipe width) =
      literalOperand width 0 := literalOperand.constructionRecipe_eq width 0
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [mask, formed, ih, literalOperand, ResolvedSourceEmit.oneCode,
        List.replicate_succ, SharedCoordinateTable.code, List.append_nil]

theorem mask_clock (width count : Nat) : (mask width count).2 = 40 * count + 1 := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [mask, ih]; omega

def build (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (k b : Nat) (target : Channel n) (found done : Nat) : List (Instruction width 8) × Nat :=
  let packet := SupportCandidate.header width n rows roots (fun _ : Fin graph.nodeCount => false)
  let first := mask width n
  let entry := evaluate (environment [n, min (k + 1) n]) (enter.constructionRecipe width)
  let seek := SupportSearchBody.seek n
  let call := SupportSearchBody.call n
  let cleanup := SupportSearchBody.cleanup n b roots
  let traversal := evaluate (environment [seek, n, (cacheHeap width packet rows roots).size, call])
    (traversal.constructionRecipe width)
  let callback := SupportCandidateConstruction.callback width n b packet rows roots target.val call found (SupportTraversal.backtrack seek)
  let ending := evaluate (environment [cleanup, done, n]) (SharedEvaluationReclaim.code.constructionRecipe width)
  let image := first.1 ++ entry ++ traversal ++ [.branchZero 0 (word width cleanup)] ++ callback.1 ++ ending
  (image, first.2 + callback.2 + 1000 + 16 * image.length +
    32 * (n + rows.length + (rowChildren rows).length + (rowGuards rows).length + roots.length) + 100)

theorem image (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (healthy : Fin graph.nodeCount → Bool) (k b : Nat) (target : Channel n) (found done : Nat) :
    (build width graph rows roots k b target found done).1 =
      SupportSearchBody.code width graph rows roots healthy k b target found done := by
  have entry : evaluate (environment [n, min (k + 1) n]) (enter.constructionRecipe width) =
      enter width n (min (k + 1) n) := enter.constructionRecipe_eq width n (min (k + 1) n)
  have tree (seek base call : Nat) : evaluate (environment [seek, n, base, call]) (traversal.constructionRecipe width) =
      traversal width seek n base call := traversal.constructionRecipe_eq width seek n base call
  have ending (cleanup : Nat) : evaluate (environment [cleanup, done, n])
      (SharedEvaluationReclaim.code.constructionRecipe width) = (SharedEvaluationReclaim.code width cleanup done n).toList :=
    SharedEvaluationReclaim.code.constructionRecipe_eq width cleanup done n
  rw [SupportSearchBody.healthy_independent graph rows roots healthy (fun _ => false)]
  simp only [build, mask_image, entry, tree, ending, SupportCandidateConstruction.callback_image,
    traversal, enter, SupportSearchBody.code, SupportSearchInit.code, SupportSearchInit.enterCode, List.append_assoc]

theorem clock (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (k b : Nat) (target : Channel n) (found done : Nat) :
    (build width graph rows roots k b target found done).2 ≤
      100000 + 2000 * (n + rows.length + (rowChildren rows).length + (rowGuards rows).length + roots.length) := by
  have first := mask_clock width n
  let packet := SupportCandidate.header width n rows roots (fun _ : Fin graph.nodeCount => false)
  have callback := SupportCandidateConstruction.callback_clock width n b packet rows roots target.val
    (SupportSearchBody.call n) found (SupportTraversal.backtrack (SupportSearchBody.seek n))
  have length : (build width graph rows roots k b target found done).1.length = SupportSearchBody.cleanup n b roots + 7 := by
    rw [image width graph rows roots (fun _ => false), SupportSearchBody.code_length]
  change (mask width n).2 +
    (SupportCandidateConstruction.callback width n b packet rows roots target.val (SupportSearchBody.call n) found
      (SupportTraversal.backtrack (SupportSearchBody.seek n))).2 + 1000 +
    16 * (build width graph rows roots k b target found done).1.length + _ + 100 ≤ _
  rw [length]
  simp only [SupportSearchBody.cleanup, SupportSearchBody.call, SupportSearchBody.seek] at callback ⊢
  split <;> omega

end Controller.Cost.SupportTraversalConstruction
