/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.PlanConstructionStorage
import Controller.Cost.PacketTransferStorage

/-! Source-front buffers account for the cached source plan, operand emitter,
packet handoff, fixed copy/header recipes and all intermediate list images. -/
namespace Controller.Cost.ResolvedFrontStorage

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Cost.ForestIndexedOperands

abbrev operands (width : Nat) (graph : DAG n) (packet : Array (Word width))
    (rows : List Row) (roots : List Nat) (b : Nat) (target : Channel n) (rootSlot : Nat) :=
  (ResolvedPlanProducer.compile width graph packet rows roots b target rootSlot).1

abbrev handoffEntry (width : Nat) (graph : DAG n) (packet : Array (Word width))
    (rows : List Row) (roots : List Nat) (b : Nat) (target : Channel n)
    (rootSlot entry : Nat) :=
  entry + (SourceOperandConstruction.build width entry
    (operands width graph packet rows roots b target rootSlot)).1.length + 16

structure Certificate (width : Nat) (graph : DAG n) (packet : Array (Word width))
    (rows : List Row) (roots : List Nat) (b : Nat) (target : Channel n)
    (rootSlot entry sourceCount : Nat) where
  plan : PlanConstructionStorage.Certificate width graph packet rows roots b target rootSlot entry
  handoff : PacketTransferStorage.HandoffCertificate width
    (handoffEntry width graph packet rows roots b target rootSlot entry)
    (sourceCount + (operands width graph packet rows roots b target rootSlot).length)
    (2 + (operands width graph packet rows roots b target rootSlot).length) (n + graph.nodeCount)
  fixed : PacketTransferStorage.Fixed width

def buffers (width : Nat) (graph : DAG n) (packet : Array (Word width))
    (rows : List Row) (roots : List Nat) (b : Nat) (target : Channel n)
    (rootSlot entry sourceCount : Nat)
    (certificate : Certificate width graph packet rows roots b target rootSlot entry sourceCount) :=
  PlanConstructionStorage.buffers width graph packet rows roots b target rootSlot entry
    certificate.plan +
  PacketTransferStorage.handoffBuffers width
    (handoffEntry width graph packet rows roots b target rootSlot entry)
    (sourceCount + (operands width graph packet rows roots b target rootSlot).length)
    (2 + (operands width graph packet rows roots b target rootSlot).length) (n + graph.nodeCount)
    certificate.handoff +
  256 * ((ResolvedFrontConstruction.prepare width graph packet rows roots b target rootSlot entry
    sourceCount).1.length + packet.size + sourceCount + 1) + 100000

theorem complete (width : Nat) (graph : DAG n) (packet : Array (Word width))
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (rootMatches : RootsMatch graph roots) (b : Nat) (target : Channel n)
    (reference : Fin graph.nodeCount) (rootSlot entry sourceCount : Nat) :
    ∃ certificate : Certificate width graph packet rows roots b target rootSlot entry sourceCount,
      buffers width graph packet rows roots b target rootSlot entry sourceCount certificate ≤
        20000000 * (graph.countedSize + 1) + 1000 * (packet.size + sourceCount) := by
  obtain ⟨plan, planBound⟩ := PlanConstructionStorage.complete width graph packet rows roots
    matched rootMatches b target reference rootSlot entry
  obtain ⟨handoff, handoffBound⟩ := PacketTransferStorage.handoff width
    (handoffEntry width graph packet rows roots b target rootSlot entry)
    (sourceCount + (operands width graph packet rows roots b target rootSlot).length)
    (2 + (operands width graph packet rows roots b target rootSlot).length) (n + graph.nodeCount)
  have operandLength : (operands width graph packet rows roots b target rootSlot).length ≤
      11 * (graph.countedSize + 1) := by
    rw [operands, ResolvedPlanProducer.compile_image width graph packet rows roots matched b target
      rootSlot, ResolvedSourcePlan.query_length graph packet rows roots b target reference]
    have source := ResolvedResident.rows_bound graph ∅ b target reference
    omega
  have imageLength : (ResolvedFrontConstruction.prepare width graph packet rows roots b target
      rootSlot entry sourceCount).1.length ≤ 200 * (graph.countedSize + 1) := by
    rw [ResolvedFrontConstruction.image width graph packet rows roots matched b target reference]
    exact ResolvedSourcePrepare.code_bound graph packet rows roots b target reference
  have size := graph.countedSize_eq
  refine ⟨⟨plan, handoff, PacketTransferStorage.fixed width⟩, ?_⟩
  simp only [buffers]
  omega

end Controller.Cost.ResolvedFrontStorage
