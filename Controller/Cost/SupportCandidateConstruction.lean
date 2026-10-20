module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.SupportControllerConstruction

@[expose] public section


/-! Charged construction of one source-evaluating support callback. The same
root scan is shared by the subset traversal; construction reads source counts
and emits both continuations without choosing a successful support. -/
namespace Controller.Cost.SupportCandidateConstruction

open Controller.Cost Controller.Extensions Controller.Cost.ForestIndexedOperands
open Controller.Cost.WordConstructionRecipe Controller.Cost.ExtensionConstructionRecipes
open Controller.Cost.ForestClauseProgramConstruction (environment)

def finish (width entry destination count : Nat) : List (Instruction width 8) :=
  evaluate (environment [entry, destination, count]) (SupportCandidate.finishCode.constructionRecipe width)

theorem finish_image (width entry destination count : Nat) :
    finish width entry destination count = SupportCandidate.finishCode width entry destination count :=
  SupportCandidate.finishCode.constructionRecipe_eq width entry destination count

def build (width n : Nat) (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
    (entry healthy found rejected : Nat) : List (Instruction width 8) × Nat :=
  let first := SupportControllerConstruction.sourceRound width n packet rows roots entry
  let scan := SupportControllerConstruction.rootScan width (entry + 126)
    (UniformDAGRuntimeOutputs.rootBase packet rows) healthy ((cacheHeap width packet rows roots).size + n)
    (entry + 126 + 15 * roots.length + 9) roots.length
  let no := finish width (entry + 126 + 15 * roots.length) rejected rows.length
  let yes := finish width (entry + 126 + 15 * roots.length + 9) found rows.length
  let image := first.1 ++ scan.1 ++ no ++ yes
  (image, first.2 + scan.2 + 200 + 8 * image.length +
    16 * (rows.length + (rowChildren rows).length + (rowGuards rows).length + roots.length) + 100)

theorem image (width n : Nat) (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
    (entry healthy found rejected : Nat) :
    (build width n packet rows roots entry healthy found rejected).1 =
      SupportCandidate.code width n packet rows roots entry healthy found rejected := by
  simp only [build, SupportControllerConstruction.sourceRound_image,
    SupportControllerConstruction.rootScan_image, finish_image, SupportCandidate.code, List.append_assoc]

theorem clock (width n : Nat) (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
    (entry healthy found rejected : Nat) :
    (build width n packet rows roots entry healthy found rejected).2 ≤
      20000 + 400 * (rows.length + (rowChildren rows).length + (rowGuards rows).length + roots.length) := by
  have first := SupportControllerConstruction.sourceRound_clock width n packet rows roots entry
  have scan := SupportControllerConstruction.rootScan_clock width (entry + 126)
    (UniformDAGRuntimeOutputs.rootBase packet rows) healthy ((cacheHeap width packet rows roots).size + n)
    (entry + 126 + 15 * roots.length + 9) roots.length
  have length : (build width n packet rows roots entry healthy found rejected).1.length = 144 + 15 * roots.length := by
    rw [image, SupportCandidate.code_length]
  change _ + _ + 200 + 8 * (build width n packet rows roots entry healthy found rejected).1.length + _ + 100 ≤ _
  rw [length]
  omega

def prepare (width b address : Nat) : List (Instruction width 8) :=
  if b = 1 then evaluate (environment [address]) (SupportTarget.saveCode.constructionRecipe width) else []

def returning (width b address destination : Nat) : List (Instruction width 8) :=
  if b = 1 then evaluate (environment [address, destination]) (returnSingle.constructionRecipe width)
  else evaluate (environment [destination]) (returnPlain.constructionRecipe width)

theorem prepare_image (width b address : Nat) : prepare width b address = SupportCallback.prepareCode width b address := by
  have formed : evaluate (environment [address]) (SupportTarget.saveCode.constructionRecipe width) =
      SupportTarget.saveCode width address := SupportTarget.saveCode.constructionRecipe_eq width address
  simp only [prepare, formed, SupportCallback.prepareCode]

theorem returning_image (width b address destination : Nat) :
    returning width b address destination = SupportCallback.returnCode width b address destination := by
  have positive : evaluate (environment [address, destination]) (returnSingle.constructionRecipe width) =
      returnSingle width address destination := returnSingle.constructionRecipe_eq width address destination
  have negative : evaluate (environment [destination]) (returnPlain.constructionRecipe width) =
      returnPlain width destination := returnPlain.constructionRecipe_eq width destination
  by_cases one : b = 1 <;> simp [returning, positive, negative, SupportCallback.returnCode, returnSingle, returnPlain, one]

def callback (width n b : Nat) (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
    (target entry found rejected : Nat) : List (Instruction width 8) × Nat :=
  let address := (cacheHeap width packet rows roots).size + target
  let first := prepare width b address
  let start := entry + first.length
  let last := start + 144 + 15 * roots.length
  let no := returning width b address rejected
  let yes := last + no.length
  let candidate := build width n packet rows roots start 5 yes last
  let image := first ++ candidate.1 ++ no ++ returning width b address found
  (image, candidate.2 + 8 * image.length + 1000)

theorem callback_image (width n b : Nat) (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
    (target entry found rejected : Nat) :
    (callback width n b packet rows roots target entry found rejected).1 =
      SupportCallback.code width n b packet rows roots target entry found rejected := by
  simp only [callback, prepare_image, returning_image, image, SupportCallback.code, List.append_assoc]

theorem callback_clock (width n b : Nat) (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
    (target entry found rejected : Nat) :
    (callback width n b packet rows roots target entry found rejected).2 ≤
      25000 + 600 * (rows.length + (rowChildren rows).length + (rowGuards rows).length + roots.length) := by
  let address := (cacheHeap width packet rows roots).size + target
  let start := entry + (prepare width b address).length
  let last := start + 144 + 15 * roots.length
  let yes := last + (returning width b address rejected).length
  have candidate := clock width n packet rows roots start 5 yes last
  have length := SupportCallback.code_length (width := width) (n := n) (b := b) (packet := packet)
    (rows := rows) (roots := roots) (target := target) (entry := entry) (found := found) (rejected := rejected)
  rw [← callback_image] at length
  change (build width n packet rows roots start 5 yes last).2 +
    8 * (callback width n b packet rows roots target entry found rejected).1.length + 1000 ≤ _
  rw [length]
  split <;> omega

end Controller.Cost.SupportCandidateConstruction
