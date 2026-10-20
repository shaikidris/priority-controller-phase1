module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ResolvedPlanProducer
public import Controller.Cost.StackPacketConstruction

@[expose] public section


/-! Source-query preparation constructs its operand plan and emitter, then
forms the copy and packet handoff at cached positions. Selector bits remain
runtime input; instruction construction does not select an expansion. -/
namespace Controller.Cost.ResolvedFrontConstruction

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Cost.ForestIndexedOperands Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestClauseProgramConstruction (environment)

def prepare (width : Nat) (graph : DAG n) (packet : Array (Word width)) (rows : List Row) (roots :
  List Nat)
    (b : Nat) (target : Channel n) (rootSlot entry sourceCount : Nat) : List (Instruction width 8) ×
      Nat :=
  let plan := ResolvedPlanProducer.compile width graph packet rows roots b target rootSlot
  let emitted := SourceOperandConstruction.build width entry plan.1
  let copyPC := entry + emitted.1.length
  let nodesPC := copyPC + 10
  let channelsPC := nodesPC + 3
  let handoffPC := channelsPC + 3
  let copied := StackPacketConstruction.copy width copyPC nodesPC sourceCount plan.1.length
  let nodes := evaluate (environment [1]) (ResolvedSourceRead.pushCode.constructionRecipe width)
  let channels := evaluate (environment [0]) (ResolvedSourceRead.pushCode.constructionRecipe width)
  let handoff := StackPacketConstruction.handoff width handoffPC (sourceCount + plan.1.length)
    (2 + plan.1.length) (n + graph.nodeCount)
  let image := emitted.1 ++ copied ++ nodes ++ channels ++ handoff.1
  (image, plan.2 + emitted.2 + handoff.2 + 16 * image.length + 2000)

theorem image (width : Nat) (graph : DAG n) (packet : Array (Word width)) (rows : List Row) (roots :
  List Nat)
    (matched : RowsMatch graph rows) (b : Nat) (target : Channel n) (reference : Fin
      graph.nodeCount)
    (rootSlot entry sourceCount : Nat) :
    (prepare width graph packet rows roots b target rootSlot entry sourceCount).1 =
      ResolvedSourcePrepare.code width graph packet rows roots b target reference rootSlot entry
        sourceCount := by
  have planLength : (ResolvedPlanProducer.compile width graph packet rows roots b target
    rootSlot).1.length =
      (ResolvedResident.rows graph ∅ b target reference).flatten.length := by
    rw [ResolvedPlanProducer.compile_image width graph packet rows roots matched b target rootSlot,
      ResolvedSourcePlan.query_length graph packet rows roots b target reference]
  have emitted : (SourceOperandConstruction.build width entry
      (ResolvedPlanProducer.compile width graph packet rows roots b target rootSlot).1).1 =
      ResolvedSourceCallback.emitCode width graph packet rows roots b target rootSlot entry := by
    rw [ResolvedPlanProducer.compile_image width graph packet rows roots matched b target rootSlot,
      SourceOperandConstruction.build_image]
    rfl
  have nodes : evaluate (environment [1]) (ResolvedSourceRead.pushCode.constructionRecipe width) =
      ResolvedSourceRead.pushCode width 1 := ResolvedSourceRead.pushCode.constructionRecipe_eq width
        1
  have channels : evaluate (environment [0]) (ResolvedSourceRead.pushCode.constructionRecipe width)
    =
      ResolvedSourceRead.pushCode width 0 := ResolvedSourceRead.pushCode.constructionRecipe_eq width
        0
  dsimp only [prepare]
  rw [planLength, emitted]
  simp only [StackPacketConstruction.copy_image, StackPacketConstruction.handoff_image, nodes,
    channels,
    ResolvedSourcePrepare.code, ResolvedSourcePrepare.positions, ResolvedSourceCallback.querySize,
      List.append_assoc]

theorem clock (width : Nat) (graph : DAG n) (packet : Array (Word width)) (rows : List Row) (roots :
  List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots) (b : Nat) (target :
      Channel n)
    (reference : Fin graph.nodeCount) (rootSlot entry sourceCount : Nat) :
    (prepare width graph packet rows roots b target rootSlot entry sourceCount).2 ≤
      30000 * (graph.countedSize + 1) := by
  let plan := ResolvedPlanProducer.compile width graph packet rows roots b target rootSlot
  let emitted := SourceOperandConstruction.build width entry plan.1
  let handoffPC := entry + emitted.1.length + 10 + 3 + 3
  have planClock := ResolvedPlanProducer.compile_clock width graph packet rows roots matched
    rootMatches b target rootSlot reference
  have emission := SourceOperandConstruction.build_clock width entry plan.1
  have handoff := StackPacketConstruction.handoff_clock width handoffPC (sourceCount +
    plan.1.length)
    (2 + plan.1.length) (n + graph.nodeCount)
  have rowsBound := ResolvedResident.rows_bound graph ∅ b target reference
  have length : plan.1.length ≤ 11 * (graph.countedSize + 1) := by
    dsimp only [plan]
    rw [ResolvedPlanProducer.compile_image width graph packet rows roots matched b target rootSlot,
      ResolvedSourcePlan.query_length graph packet rows roots b target reference]
    omega
  have imageLength : (prepare width graph packet rows roots b target rootSlot entry
    sourceCount).1.length ≤
      200 * (graph.countedSize + 1) := by
    rw [image width graph packet rows roots matched b target reference rootSlot entry sourceCount]
    exact ResolvedSourcePrepare.code_bound graph packet rows roots b target reference
  have size := graph.countedSize_eq
  change plan.2 + emitted.2 + (StackPacketConstruction.handoff width handoffPC (sourceCount +
    plan.1.length)
    (2 + plan.1.length) (n + graph.nodeCount)).2 +
    16 * (prepare width graph packet rows roots b target rootSlot entry sourceCount).1.length + 2000
      ≤ _
  dsimp only [plan, emitted, handoffPC] at planClock emission handoff length ⊢
  omega

end Controller.Cost.ResolvedFrontConstruction
