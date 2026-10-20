module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ResolvedCallbackConstruction

@[expose] public section


/-! The selector and root traversal image has one returning callback. Source
layout and live-AND counts determine every block placement. -/
namespace Controller.Cost.ResolvedBodyConstruction

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Cost.ForestIndexedOperands Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestClauseProgramConstruction (environment)
open Controller.Cost.ExtensionConstructionRecipes

def build (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount) (found done : Nat) : List
      (Instruction width 8) × Nat :=
  let p := ResolvedOutputBody.positions graph found done
  let packet := ResolvedRootSource.packet width n rows roots (fun _ : Fin graph.nodeCount => false)
    0
  let source := cacheHeap width packet rows roots
  let mask := SupportTraversalConstruction.mask width graph.liveAndCount
  let driver := evaluate (environment [p.loop, graph.roots.length, UniformDAGRuntimeOutputs.rootBase
    packet rows,
    4, 5, p.seek, p.done, graph.liveAndCount]) (rootDriver.constructionRecipe width)
  let advance := evaluate (environment [p.loop]) (ResolvedRootLoop.advanceCode.constructionRecipe
    width)
  let ending := evaluate (environment [p.seek, graph.liveAndCount, source.size, p.call])
    (traversal.constructionRecipe width)
  let callback := ResolvedCallbackConstruction.build width graph packet rows roots b target
    reference
    4 p.call (source.size + graph.liveAndCount) p.found (SupportTraversal.backtrack p.seek)
  let image := mask.1 ++ [.constant 3 (word width 0)] ++ driver ++ advance ++ ending ++
    [.branchZero 0 (word width (p.loop + 23))] ++ callback.1
  (image, mask.2 + callback.2 + 16 * image.length + 10000 * (graph.countedSize + 1))

theorem image (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat) (matched :
  RowsMatch graph rows)
    (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount) (found done : Nat) :
    (build width graph rows roots b target reference found done).1 =
      ResolvedOutputBody.code width graph rows roots (fun _ => false) b target reference found done
        := by
  let p := ResolvedOutputBody.positions graph found done
  let packet := ResolvedRootSource.packet width n rows roots (fun _ : Fin graph.nodeCount => false)
    0
  have driver : evaluate (environment [p.loop, graph.roots.length, UniformDAGRuntimeOutputs.rootBase
    packet rows,
      4, 5, p.seek, p.done, graph.liveAndCount]) (rootDriver.constructionRecipe width) =
      rootDriver width p.loop graph.roots.length (UniformDAGRuntimeOutputs.rootBase packet rows)
        4 5 p.seek p.done graph.liveAndCount :=
    rootDriver.constructionRecipe_eq width p.loop graph.roots.length
      (UniformDAGRuntimeOutputs.rootBase packet rows) 4 5 p.seek p.done graph.liveAndCount
  have advance : evaluate (environment [p.loop]) (ResolvedRootLoop.advanceCode.constructionRecipe
    width) =
      ResolvedRootLoop.advanceCode width p.loop :=
        ResolvedRootLoop.advanceCode.constructionRecipe_eq width p.loop
  have ending : evaluate (environment [p.seek, graph.liveAndCount, (cacheHeap width packet rows
    roots).size, p.call])
      (traversal.constructionRecipe width) = traversal width p.seek graph.liveAndCount (cacheHeap
        width packet rows roots).size p.call :=
    traversal.constructionRecipe_eq width p.seek graph.liveAndCount (cacheHeap width packet rows
      roots).size p.call
  dsimp only [p, packet] at driver advance ending
  simp only [build, SupportTraversalConstruction.mask_image, ResolvedCallbackConstruction.image
    width graph _ rows roots matched,
    driver, advance, ending, rootDriver_image, traversal, ResolvedOutputBody.code,
      List.append_assoc]

theorem clock (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots) (b : Nat) (target :
      Channel n)
    (reference : Fin graph.nodeCount) (found done : Nat) :
    (build width graph rows roots b target reference found done).2 ≤
      1100000 * (n + 1) * (graph.countedSize + 1) := by
  let p := ResolvedOutputBody.positions graph found done
  let packet := ResolvedRootSource.packet width n rows roots (fun _ : Fin graph.nodeCount => false)
    0
  have callback := ResolvedCallbackConstruction.clock width graph packet rows roots matched
    rootMatches b target reference
    4 p.call ((cacheHeap width packet rows roots).size + graph.liveAndCount) p.found
      (SupportTraversal.backtrack p.seek)
    (ResolvedRootSource.source_bound graph (fun _ => false) 0 matched rootMatches)
  have mask := SupportTraversalConstruction.mask_clock width graph.liveAndCount
  have length : (build width graph rows roots b target reference found done).1.length ≤ 1400 *
    (graph.countedSize + 1) := by
    rw [image width graph rows roots matched b target reference found done]
    exact ResolvedOutputBody.code_bound graph rows roots matched rootMatches (fun _ => false) b
      target reference found done
  have ands := graph.liveAndCount_le_nodeCount
  have size := graph.countedSize_eq
  change _ + _ + 16 * (build width graph rows roots b target reference found done).1.length + 10000
    * (graph.countedSize + 1) ≤ _
  dsimp only [p, packet] at callback
  nlinarith

end Controller.Cost.ResolvedBodyConstruction
