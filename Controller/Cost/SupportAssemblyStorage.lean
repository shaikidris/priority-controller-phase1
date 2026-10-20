/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.AssemblyStorage
import Controller.Cost.SupportColdConstruction
import Controller.Cost.SupportNativeConstruction

/-! Actual assembly traces for source-count streams, support callbacks and
cold source exchange. No source evaluation is performed to form an instruction. -/
namespace Controller.Cost.SupportAssemblyStorage

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Cost.ForestIndexedOperands Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestClauseProgramConstruction (environment)
open Controller.Cost.AssemblyStorage Controller.Cost.ExtensionConstructionRecipes

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

attribute [local irreducible] SupportControllerConstruction.sourceRound
  SupportCandidateConstruction.build SupportCandidateConstruction.callback

theorem sourceRound (width n : Nat) (header : Array (Word width)) (rows : List Row)
    (roots : List Nat) (entry : Nat) :
    Bounded (SupportControllerConstruction.sourceRound width n header rows roots entry).1
      100000 := by
  let kernel := evaluate (environment [n, header.size, rows.length, (rowChildren rows).length,
    (rowGuards rows).length, roots.length]) (sourceKernel.constructionRecipe width)
  have formed := wordCode (width := width)
    (environment [n, header.size, rows.length, (rowChildren rows).length,
      (rowGuards rows).length, roots.length]) (sourceKernel.constructionRecipe width)
  have length : kernel.length = 126 := by
    simp only [kernel, evaluate, List.length_map]
    rfl
  have wide := Trace.widen formed
  have moved := relocate wide entry
  unfold SupportControllerConstruction.sourceRound
  exact .enlarge moved (by
    simp only [List.length_map, sourceKernel.constructionRecipe_work]
    change 32 * _ + 32 * kernel.length + 288 * kernel.length + 16 ≤ _
    rw [length]
    decide)

theorem park (width start count : Nat) :
    Bounded (StackPacketConstruction.park width start count).1 (640 * (count + 1)) := by
  obtain ⟨peak, trace, bound⟩ := PacketTransferStorage.park width start count
  exact .enlarge (.stream trace) bound

theorem mask (width count : Nat) :
    Bounded (SupportTraversalConstruction.mask width count).1 (1500 * count) := by
  induction count with
  | zero => exact .empty
  | succ count ih =>
      have head := wordCode (width := width) (environment [0])
        (literalOperand.constructionRecipe width)
      have formed := join head ih
      change Bounded (_ ++ _) _
      exact .enlarge formed (by
        simp only [literalOperand.constructionRecipe_work, evaluate, List.length_map]
        have length : (literalOperand.constructionRecipe width).length = 2 := rfl
        rw [length]
        omega)

theorem rootScan (width entry cursor healthy values found count : Nat) :
    Bounded (SupportControllerConstruction.rootScan width entry cursor healthy values found count).1
      (6000 * (count + 1)) := by
  obtain ⟨peak, trace, bound⟩ := TemplateStreamConstruction.storage
    (SupportRootScan.nodeCode.constructionRecipe width)
    (fun i => environment [entry + 15 * i, cursor + i, healthy, values, found]) 0 count
  exact .enlarge (.stream trace) (by
    simp only [SupportRootScan.nodeCode.constructionRecipe_work] at bound
    have length : (SupportRootScan.nodeCode.constructionRecipe width).length = 15 := rfl
    rw [length] at bound
    omega)

theorem healthyScan (width cursor healthy needed count : Nat) :
    Bounded (SupportControllerConstruction.healthyScan width cursor healthy needed count).1
      (3000 * (count + 1)) := by
  obtain ⟨peak, trace, bound⟩ := TemplateStreamConstruction.storage
    (SupportHealthyScan.nodeCode.constructionRecipe width)
    (fun i => environment [cursor + i, healthy, needed]) 0 count
  exact .enlarge (.stream trace) (by
    simp only [SupportHealthyScan.nodeCode.constructionRecipe_work] at bound
    have length : (SupportHealthyScan.nodeCode.constructionRecipe width).length = 6 := rfl
    rw [length] at bound
    omega)

theorem copy (width entry next base count : Nat) :
    Bounded (StackPacketConstruction.copy width entry next base count) 5000 := by
  unfold StackPacketConstruction.copy
  exact .enlarge (wordCode _ _) (by
    rw [SharedWitnessCopy.code.constructionRecipe_work]
    decide)

theorem reclaim (width entry next count : Nat) :
    Bounded (StackPacketConstruction.reclaim width entry next count) 5000 := by
  unfold StackPacketConstruction.reclaim
  exact .enlarge (wordCode _ _) (by
    rw [SharedEvaluationReclaim.code.constructionRecipe_work]
    decide)

theorem repack (width entry oldCount : Nat) (operands : List (ResolvedSourceEmit.Operand width)) :
    Bounded (SourceRepackConstruction.build width entry oldCount operands).1
      (20000 * (operands.length + 1)) := by
  have first := AssemblyStorage.operand width entry operands
  let emitted := SourceOperandConstruction.build width entry operands
  have copied := copy width (entry + emitted.1.length) (entry + emitted.1.length + 10)
    oldCount operands.length
  have release := reclaim width (entry + emitted.1.length + 10)
    (entry + emitted.1.length + 17) (oldCount + operands.length)
  have parked := park width 0 operands.length
  have assembled := join (join (join first copied) release) parked
  have emitLength := ResolvedSourceEmit.code_length (width := width) (entry := entry) operands
  rw [← SourceOperandConstruction.build_image] at emitLength
  have copyLength : (StackPacketConstruction.copy width (entry + emitted.1.length)
      (entry + emitted.1.length + 10) oldCount operands.length).length = 10 := by
    rw [StackPacketConstruction.copy_image, Array.length_toList, SharedWitnessCopy.code_size]
  have releaseLength : (StackPacketConstruction.reclaim width (entry + emitted.1.length + 10)
      (entry + emitted.1.length + 17) (oldCount + operands.length)).length = 7 := by
    rw [StackPacketConstruction.reclaim_image, Array.length_toList,
      SharedEvaluationReclaim.code_size]
  unfold SourceRepackConstruction.build
  exact .enlarge assembled (by
    simp only [List.length_append, copyLength, releaseLength]
    omega)


theorem candidate (width n : Nat) (packet : Array (Word width)) (rows : List Row)
    (roots : List Nat) (entry healthy found rejected : Nat) :
    Bounded (SupportCandidateConstruction.build width n packet rows roots entry healthy found
      rejected).1
      (1000 * (SupportCandidateConstruction.build width n packet rows roots entry healthy found
        rejected).2) := by
  have first := sourceRound width n packet rows roots entry
  have scan := rootScan width (entry + 126) (UniformDAGRuntimeOutputs.rootBase packet rows) healthy
    ((cacheHeap width packet rows roots).size + n) (entry + 126 + 15 * roots.length + 9)
        roots.length
  have no := wordCode (width := width)
    (environment [entry + 126 + 15 * roots.length, rejected, rows.length])
    (SupportCandidate.finishCode.constructionRecipe width)
  have yes := wordCode (width := width)
    (environment [entry + 126 + 15 * roots.length + 9, found, rows.length])
    (SupportCandidate.finishCode.constructionRecipe width)
  have assembled := join (join (join first scan) no) yes
  have sourceLength : (SupportControllerConstruction.sourceRound width n packet rows roots
      entry).1.length
      = 126 := by
    rw [SupportControllerConstruction.sourceRound_image, Array.length_toList,
      SupportSourceRound.code_size]
  have scanLength : (SupportControllerConstruction.rootScan width (entry + 126)
      (UniformDAGRuntimeOutputs.rootBase packet rows) healthy
      ((cacheHeap width packet rows roots).size + n)
      (entry + 126 + 15 * roots.length + 9) roots.length).1.length = 15 * roots.length := by
    rw [SupportControllerConstruction.rootScan_image, SupportRootScan.code_length]
  have sourceLower : 1210 ≤
      (SupportControllerConstruction.sourceRound width n packet rows roots entry).2 := by
    unfold SupportControllerConstruction.sourceRound
    dsimp only
    omega
  have scanLower : 100 * roots.length ≤ (SupportControllerConstruction.rootScan width
      (entry + 126) (UniformDAGRuntimeOutputs.rootBase packet rows) healthy
      ((cacheHeap width packet rows roots).size + n)
      (entry + 126 + 15 * roots.length + 9) roots.length).2 := by
    simp only [SupportControllerConstruction.rootScan, TemplateStreamConstruction.clock,
      SupportRootScan.nodeCode.constructionRecipe_work]
    have length : (SupportRootScan.nodeCode.constructionRecipe width).length = 15 := rfl
    rw [length]
    omega
  unfold SupportCandidateConstruction.build SupportCandidateConstruction.finish
  dsimp only
  exact .enlarge assembled (by
    simp only [List.length_append, sourceLength, scanLength, evaluate, List.length_map,
      SupportCandidate.finishCode.constructionRecipe_work]
    have len : (SupportCandidate.finishCode.constructionRecipe width).length = 9 := rfl
    rw [len]
    omega)

theorem callback (width n b : Nat) (packet : Array (Word width)) (rows : List Row)
    (roots : List Nat) (target entry found rejected : Nat) :
    Bounded (SupportCandidateConstruction.callback width n b packet rows roots target entry found
      rejected).1
      (1000 * (SupportCandidateConstruction.callback width n b packet rows roots target entry found
        rejected).2) := by
  let address := (cacheHeap width packet rows roots).size + target
  let first := SupportCandidateConstruction.prepare width b address
  let start := entry + first.length
  let last := start + 144 + 15 * roots.length
  let no := SupportCandidateConstruction.returning width b address rejected
  let yes := last + no.length
  have prepare : Bounded first 10000 := by
    dsimp only [first, SupportCandidateConstruction.prepare]
    split
    · exact .enlarge (wordCode _ _) (by
        rw [SupportTarget.saveCode.constructionRecipe_work]; decide)
    · exact .enlarge .empty (by omega)
  have returning (destination : Nat) :
      Bounded (SupportCandidateConstruction.returning width b address destination) 10000 := by
    unfold SupportCandidateConstruction.returning
    split
    · exact .enlarge (wordCode _ _) (by rw [returnSingle.constructionRecipe_work]; decide)
    · exact .enlarge (wordCode _ _) (by rw [returnPlain.constructionRecipe_work]; decide)
  have middle := candidate width n packet rows roots start 5 yes last
  have assembled := join (join (join prepare middle) (returning rejected)) (returning found)
  unfold SupportCandidateConstruction.callback
  dsimp only
  exact .enlarge assembled (by
    simp only [List.length_append]
    dsimp only [first, start, last, no, yes, address] at *
    omega)

end Controller.Cost.SupportAssemblyStorage
