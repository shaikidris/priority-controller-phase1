/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ProperNativeConstruction
import Controller.Cost.BoundedDetectorConstruction
import Controller.Extensions.BoundedNativeComplete

/-! A constructed implementation of the proper-basis algorithm. The guarded
case reuses the bounded detector at zero live conjunctions; the other two cases
use the constructed monotone and literal table algorithms. Existing detector
and execution declarations retain their original types and implementations. -/
namespace Controller.Cost.ProperDetectorConstruction

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

attribute [local irreducible] Controller.Extensions.ProperBasisDetector.machine
  Controller.Extensions.BoundedNativeDetector.program
    Controller.Extensions.MonotoneNativeDetector.program
  Controller.Extensions.LiteralNativeDetector.program

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestIndexedOperands
open Controller.Extensions.ProperBasisDetector Controller.Extensions.GateBasis

def machine (parameters : Parameters) (kind : Kind) (rows : List Row) (roots : List Nat) : Machine
  :=
  match kind with
  | .guarded => ⟨BoundedNativeDetector.width parameters,
      BoundedNativeDetector.program parameters (BoundedNativeDetector.width parameters) 0,
      BoundedNativeComplete.initial parameters, fun state => state.reg 4 == word _ 1⟩
  | .monotone => ProperBasisDetector.machine parameters .monotone rows roots
  | .literal => ProperBasisDetector.machine parameters .literal rows roots

def detector (parameters : Parameters) (basis : Basis) (rows : List Row) (roots : List Nat) :
  Machine :=
  if parameters.drive then machine parameters (select basis) rows roots else
    ProperBasisComplete.disabled

def constructKind (parameters : Parameters) (kind : Kind) (rows : List Row) (roots : List Nat) :
  Machine × Nat :=
  match kind with
  | .guarded =>
      let width := BoundedNativeDetector.width parameters
      let formed := BoundedDetectorConstruction.build parameters width 0
      (⟨width, formed.1.toArray, BoundedNativeComplete.initial parameters, fun state => state.reg 4
        == word _ 1⟩,
        formed.2 + 1000 * (parameters.decoder.countedSize + (selectedSize parameters).total + 1))
  | .monotone =>
      let width := MonotoneNativeDetector.Width parameters parameters.decoder
      let formed := ProperNativeConstruction.monotone parameters parameters.decoder width rows roots
      (⟨width, formed.1.toArray, LiteralSourceConstruction.initial parameters.channels width rows
        roots [] [],
        fun state => !state.output.isEmpty⟩,
        formed.2 + 1000 * ((parameters.channels + 1) * (parameters.decoder.countedSize + 1) +
          (selectedSize parameters).total))
  | .literal =>
      let width := LiteralNativeDetector.Width parameters parameters.decoder
      let formed := ProperNativeConstruction.literal parameters parameters.decoder width rows roots
      (⟨width, formed.1.toArray, LiteralSourceConstruction.initial parameters.channels width rows
        roots [] [],
        fun state => !state.output.isEmpty⟩,
        formed.2 + 1000 * ((parameters.channels + 1) * (parameters.decoder.countedSize + 1) +
          (selectedSize parameters).total))

theorem constructKind_image (parameters : Parameters) (kind : Kind) (rows : List Row) (roots : List
  Nat) :
    (constructKind parameters kind rows roots).1 = machine parameters kind rows roots := by
  cases kind with
  | guarded => simp only [constructKind, BoundedDetectorConstruction.image, machine,
    BoundedNativeDetector.program]
  | monotone => simp only [constructKind, ProperNativeConstruction.monotone_image, machine,
      ProperBasisDetector.machine, MonotoneNativeDetector.program]
  | literal => simp only [constructKind, ProperNativeConstruction.literal_image, machine,
      ProperBasisDetector.machine, LiteralNativeDetector.program]

def build (parameters : Parameters) (basis : Basis) (rows : List Row) (roots : List Nat) : Machine ×
  Nat :=
  if parameters.drive then constructKind parameters (select basis) rows roots else
    (ProperBasisComplete.disabled, 32)

theorem image (parameters : Parameters) (basis : Basis) (rows : List Row) (roots : List Nat) :
    (build parameters basis rows roots).1 = detector parameters basis rows roots := by
  simp only [build, detector]
  split <;> simp only [constructKind_image]

theorem clock (parameters : Parameters) (basis : Basis) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch parameters.decoder rows) (rootMatches : RootsMatch parameters.decoder
      roots) :
    (build parameters basis rows roots).2 ≤
      20000000 * (parameters.channels + parameters.decoder.roots.length + 1) *
        (parameters.decoder.countedSize + 1) +
        200000 * ((selectedSize parameters).total + 1) := by
  unfold build
  split
  · cases chosen : select basis with
    | guarded =>
        have formed := BoundedDetectorConstruction.clock parameters (BoundedNativeDetector.width
          parameters) 0
        simp only [constructKind]
        nlinarith
    | monotone =>
        have formed := ProperNativeConstruction.monotone_clock parameters parameters.decoder
          (MonotoneNativeDetector.Width parameters parameters.decoder) rows roots matched
            rootMatches
        simp only [constructKind]
        nlinarith
    | literal =>
        have formed := ProperNativeConstruction.literal_clock parameters parameters.decoder
          (LiteralNativeDetector.Width parameters parameters.decoder) rows roots matched rootMatches
        simp only [constructKind]
        nlinarith
  · dsimp only
    nlinarith

theorem guarded_count (graph : DAG n) (guarded : graph.Guarded) : graph.liveAndCount = 0 := by
  unfold DAG.liveAndCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro index present
  have gate := guarded index
  simp only [DAG.liveAndNodes, Finset.mem_filter, Finset.mem_univ, true_and] at present
  exact Bool.false_ne_true (gate.symm.trans present)

theorem execution (parameters : Parameters) (raw : parameters.layout = .raw)
    (basis : Basis) (uses : Uses parameters.decoder basis) (proper : basis ≠ full)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch parameters.decoder rows)
    (heads : UniformDAGSource.HeadsMatch parameters.decoder rows matched) (rootMatches : RootsMatch
      parameters.decoder roots) :
    let selected := detector parameters basis rows roots
    ∃ final ticks peak, Execution selected.program selected.initial final ticks peak ∧ final.halted
      = true ∧
      ticks ≤ 100000 * (parameters.channels + parameters.decoder.roots.length + 1) *
        (parameters.decoder.countedSize + 1) +
        1000 * ((selectedSize parameters).total + 1) ∧
      programWords selected.program + peak ≤ 100000 * (parameters.channels + 1) *
        (parameters.decoder.countedSize + 1) +
        1000 * ((selectedSize parameters).total + 1) ∧
      (selected.accepted final = true ↔ parameters.drive = true ∧ Feasible parameters) ∧
      (selected.accepted final = true → Certificate.ModelCheck.check (formula parameters)
        (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true)
          := by
  cases drive : parameters.drive with
  | false =>
      have oldEq : ProperBasisComplete.detector parameters basis rows roots =
        ProperBasisComplete.disabled := by
        unfold ProperBasisComplete.detector
        rw [if_neg (by simp only [drive, Bool.false_eq_true, not_false_eq_true])]
      have newEq : detector parameters basis rows roots = ProperBasisComplete.disabled := by
        unfold detector
        rw [if_neg (by simp only [drive, Bool.false_eq_true, not_false_eq_true])]
      have original := ProperBasisComplete.execution parameters raw basis uses proper rows roots
        matched heads rootMatches
      rw [oldEq] at original
      rw [newEq]
      obtain ⟨final, ticks, peak, trace, halted, time, space, accepts, checked⟩ := original
      refine ⟨final, ticks, peak, trace, halted, ?_, ?_, ?_, checked⟩
      · nlinarith
      · nlinarith
      · simpa only [drive] using accepts
  | true =>
      have valid := selected_valid parameters.decoder basis uses proper
      cases chosen : select basis with
      | guarded =>
          have guarded : parameters.decoder.Guarded := by simpa only [chosen, Valid] using valid
          have andBound : parameters.decoder.liveAndCount ≤ 0 := by rw [guarded_count
            parameters.decoder guarded]
          obtain ⟨final, ticks, peak, trace, halted, accepts, time, space, words, checked, _⟩ :=
            BoundedNativeComplete.execution parameters raw 0 andBound
          have totalTime := BoundedNativeComplete.time_bound parameters 0
          have supports := BoundedAnd.supportCount_polynomial parameters.channels 0
          simp only [pow_zero, Nat.mul_one] at totalTime
          simp only [Nat.reduceAdd, pow_one] at supports
          have newEq : detector parameters basis rows roots = machine parameters .guarded rows roots
            := by
            unfold detector
            rw [if_pos drive, chosen]
          rw [newEq]
          simp only [machine]
          refine ⟨final, ticks, peak, trace, halted, ?_, ?_, ?_, ?_⟩
          · nlinarith
          · nlinarith
          · simpa only [beq_iff_eq, Bool.true_eq,
              BoundedNativeDetector.Detects, Feasible, drive] using accepts
          · intro accepted
            exact checked (by simpa only [beq_iff_eq] using accepted)
      | monotone =>
          have oldEq : ProperBasisComplete.detector parameters basis rows roots =
            ProperBasisDetector.machine parameters .monotone rows roots := by
            unfold ProperBasisComplete.detector
            rw [if_pos drive, chosen]
          have newEq : detector parameters basis rows roots = ProperBasisDetector.machine parameters
            .monotone rows roots := by
            unfold detector
            rw [if_pos drive, chosen]
            rfl
          have original := ProperBasisComplete.execution parameters raw basis uses proper rows roots
            matched heads rootMatches
          rw [oldEq] at original
          rw [newEq]
          obtain ⟨final, ticks, peak, trace, halted, time, space, accepts, checked⟩ := original
          refine ⟨final, ticks, peak, trace, halted, ?_, ?_, ?_, checked⟩
          · nlinarith
          · nlinarith
          · simpa only [drive] using accepts
      | literal =>
          have oldEq : ProperBasisComplete.detector parameters basis rows roots =
            ProperBasisDetector.machine parameters .literal rows roots := by
            unfold ProperBasisComplete.detector
            rw [if_pos drive, chosen]
          have newEq : detector parameters basis rows roots = ProperBasisDetector.machine parameters
            .literal rows roots := by
            unfold detector
            rw [if_pos drive, chosen]
            rfl
          have original := ProperBasisComplete.execution parameters raw basis uses proper rows roots
            matched heads rootMatches
          rw [oldEq] at original
          rw [newEq]
          obtain ⟨final, ticks, peak, trace, halted, time, space, accepts, checked⟩ := original
          refine ⟨final, ticks, peak, trace, halted, ?_, ?_, ?_, checked⟩
          · nlinarith
          · nlinarith
          · simpa only [drive] using accepts

end Controller.Cost.ProperDetectorConstruction
