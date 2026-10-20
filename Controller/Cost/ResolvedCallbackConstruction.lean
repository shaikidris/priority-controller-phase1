module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ResolvedNativeLayoutConstruction
public import Controller.Cost.ResolvedFrontConstruction
public import Controller.Cost.QuietQueryConstruction

@[expose] public section


/-! Returning selector callback construction uses the cached source layout,
charged operand front, quiet query and stack restoration. -/
namespace Controller.Cost.ResolvedCallbackConstruction

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Cost.ForestIndexedOperands Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestClauseProgramConstruction (environment)

def build (width : Nat) (graph : DAG n) (packet : Array (Word width)) (rows : List Row) (roots :
  List Nat)
    (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount)
    (rootSlot entry sourceCount found rejected : Nat) : List (Instruction width 8) × Nat :=
  let metadata := ResolvedNativeLayoutConstruction.build graph b target reference
  let data := metadata.1
  let parked := evaluate (environment [entry, sourceCount])
    (ResolvedSourcePark.code.constructionRecipe width)
  let front := ResolvedFrontConstruction.prepare width graph packet rows roots b target rootSlot
    (entry + 13) sourceCount
  let solver := entry + 13 + front.1.length
  let query := QuietQueryConstruction.build width solver data.protectedEnd (n + graph.nodeCount)
    data.scratchEnd data.references
  let restored := StackPacketConstruction.returning width (solver + query.1.length)
    data.protectedEnd sourceCount found rejected
  let image := parked ++ front.1 ++ query.1 ++ restored.1
  (image, metadata.2 + front.2 + query.2 + restored.2 + 16 * image.length + 2000)

theorem image (width : Nat) (graph : DAG n) (packet : Array (Word width)) (rows : List Row) (roots :
  List Nat)
    (matched : RowsMatch graph rows) (b : Nat) (target : Channel n) (reference : Fin
      graph.nodeCount)
    (rootSlot entry sourceCount found rejected : Nat) :
    (build width graph packet rows roots b target reference rootSlot entry sourceCount found
      rejected).1 =
      ResolvedSourceCallback.code width graph packet rows roots b target reference rootSlot entry
        sourceCount found rejected := by
  have parked : evaluate (environment [entry, sourceCount])
    (ResolvedSourcePark.code.constructionRecipe width) =
      ResolvedSourcePark.code width entry sourceCount :=
        ResolvedSourcePark.code.constructionRecipe_eq width entry sourceCount
  have front := ResolvedFrontConstruction.image width graph packet rows roots matched b target
    reference rootSlot (entry + 13) sourceCount
  have cursor := ResolvedSourcePrepare.code_end (width := width) (entry := entry + 13) (rootSlot :=
    rootSlot)
    (sourceCount := sourceCount) graph packet rows roots b target reference
  have solver : entry + 13 +
      (ResolvedFrontConstruction.prepare width graph packet rows roots b target rootSlot (entry +
        13) sourceCount).1.length =
      (ResolvedSourceCallback.positions width graph packet rows roots b target reference rootSlot
        entry).solver := by
    rw [front, cursor]
    rfl
  dsimp only [build]
  rw [solver]
  simp only [parked, front, QuietQueryConstruction.image,
    ResolvedNativeLayoutConstruction.references_value,
      ResolvedNativeLayoutConstruction.scratch_image,
    ResolvedNativeLayoutConstruction.keep_image (width := width),
      StackPacketConstruction.returning_image,
    ResolvedResident.sourceHeap_size]
  simp only [ResolvedSourceCallback.code, ResolvedSourceCallback.positions,
    ResolvedSourcePrepare.code, ResolvedSourcePrepare.positions, ResolvedResident.queryCode,
    ResolvedResident.sourceHeap_size, ResolvedSourceCallback.querySize, List.append_assoc]

theorem clock (width : Nat) (graph : DAG n) (packet : Array (Word width)) (rows : List Row) (roots :
  List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots) (b : Nat) (target :
      Channel n)
    (reference : Fin graph.nodeCount) (rootSlot entry sourceCount found rejected : Nat)
    (sourceBound : sourceCount ≤ 40 * (graph.countedSize + 1)) :
    (build width graph packet rows roots b target reference rootSlot entry sourceCount found
      rejected).2 ≤
      1000000 * (n + 1) * (graph.countedSize + 1) := by
  let metadata := ResolvedNativeLayoutConstruction.build graph b target reference
  let front := ResolvedFrontConstruction.prepare width graph packet rows roots b target rootSlot
    (entry + 13) sourceCount
  let solver := entry + 13 + front.1.length
  let query := QuietQueryConstruction.build width solver metadata.1.protectedEnd (n +
    graph.nodeCount)
    metadata.1.scratchEnd metadata.1.references
  have layout := ResolvedNativeLayoutConstruction.clock graph b target reference
  have frontBound := ResolvedFrontConstruction.clock width graph packet rows roots matched
    rootMatches b target
    reference rootSlot (entry + 13) sourceCount
  have queryBound := QuietQueryConstruction.clock width solver metadata.1.protectedEnd (n +
    graph.nodeCount)
    metadata.1.scratchEnd metadata.1.references
  have restored := StackPacketConstruction.returning_clock width (solver + query.1.length)
    metadata.1.protectedEnd sourceCount found rejected
  have size : (build width graph packet rows roots b target reference rootSlot entry sourceCount
    found rejected).1.length ≤
      1200 * (graph.countedSize + 1) := by
    rw [image width graph packet rows roots matched b target reference rootSlot entry sourceCount
      found rejected]
    exact ResolvedSourceCallback.code_length_bound graph packet rows roots b target reference
      sourceBound
  have source := ResolvedResident.rows_bound graph ∅ b target reference
  dsimp only [metadata] at queryBound
  rw [ResolvedNativeLayoutConstruction.references_value] at queryBound
  simp only [ResolvedResident.refs_length, ResolvedResident.refs_literals] at queryBound
  change metadata.2 + front.2 + query.2 + _ +
    16 * (build width graph packet rows roots b target reference rootSlot entry sourceCount found
      rejected).1.length + 2000 ≤ _
  dsimp only [metadata, front, query, solver] at *
  simp only [ResolvedNativeLayoutConstruction.references_value] at restored ⊢
  nlinarith

end Controller.Cost.ResolvedCallbackConstruction
