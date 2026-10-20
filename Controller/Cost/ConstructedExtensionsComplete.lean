module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ProperDetectorConstruction
public import Controller.Cost.ClauseProfileStorage
public import Controller.Cost.NativeConstructionStorage

@[expose] public section


/-! Complete source-driven extension algorithms with construction and fetched
execution charged in the word-operation model. The input retains the raw native
layout and the original basis or live-conjunction promise. -/
namespace Controller.Cost.ConstructedExtensionsComplete

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestIndexedOperands
open scoped BigOperators

theorem support_dominates (n k : Nat) (positive : 0 < n) : n + 1 ≤ BoundedAnd.supportCount n k := by
  have contained : ({0, 1} : Finset Nat) ⊆ Finset.range (min (k + 1) n + 1) := by
    intro index member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl <;> simp only [Finset.mem_range] <;> omega
  have bound := Finset.sum_le_sum_of_subset (f := fun index => n.choose index) contained
  simpa only [BoundedAnd.supportCount, Finset.sum_insert (by simp : (0 : Nat) ∉ ({1} : Finset Nat)),
    Finset.sum_singleton, Nat.choose_zero_right, Nat.choose_one_right, Nat.add_comm] using bound

theorem bounded_total_time (parameters : Parameters) (width k : Nat) :
    (BoundedDetectorConstruction.build parameters width k).2 + BoundedNativeCold.timeBound
      parameters k ≤
      8000000 * (BoundedAnd.supportCount parameters.channels k + parameters.decoder.roots.length * 2
        ^ k) *
        (parameters.decoder.countedSize + 1) + 200000 * ((selectedSize parameters).total + 1) := by
  have constructed := BoundedDetectorConstruction.clock parameters width k
  have executed := BoundedNativeComplete.time_bound parameters k
  have positive : 0 < parameters.channels := by have bound := parameters.bridge.target.isLt; omega
  have support := Nat.mul_le_mul_right (parameters.decoder.countedSize + 1) (support_dominates
    parameters.channels k positive)
  nlinarith [Nat.zero_le (BoundedAnd.supportCount parameters.channels k *
    (parameters.decoder.countedSize + 1)),
    Nat.zero_le (parameters.decoder.roots.length * 2 ^ k * (parameters.decoder.countedSize + 1))]

theorem bounded_execution (parameters : Parameters) (raw : parameters.layout = .raw)
    (k : Nat) (andBound : parameters.decoder.liveAndCount ≤ k) :
    let built := BoundedDetectorConstruction.build parameters (BoundedNativeDetector.width
      parameters) k
    ∃ final ticks peak, Execution built.1.toArray (BoundedNativeComplete.initial parameters) final
      ticks peak ∧
      final.halted = true ∧ (final.reg 4 = word _ 1 ↔ BoundedNativeDetector.Detects parameters) ∧
      built.2 + ticks ≤ 8000000 * (BoundedAnd.supportCount parameters.channels k +
        parameters.decoder.roots.length * 2 ^ k) *
        (parameters.decoder.countedSize + 1) + 200000 * ((selectedSize parameters).total + 1) ∧
      programWords built.1.toArray + peak ≤ 20000 * (parameters.decoder.countedSize + 1) +
        1000 * ((selectedSize parameters).total + 1) ∧
      (final.reg 4 = word _ 1 → Certificate.ModelCheck.check (formula parameters)
        (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true)
          := by
  have whole := BoundedNativeComplete.execution parameters raw k andBound
  change ∃ final ticks peak, Execution (BoundedNativeDetector.code parameters
    (BoundedNativeDetector.width parameters) k).toArray _ final ticks peak ∧ _ at whole
  dsimp only
  rw [BoundedDetectorConstruction.image]
  obtain ⟨final, ticks, peak, trace, halted, accepts, time, space, words, checked, _⟩ := whole
  change programWords (BoundedNativeDetector.code parameters (BoundedNativeDetector.width
    parameters) k).toArray ≤ _ at words
  have total := bounded_total_time parameters (BoundedNativeDetector.width parameters) k
  exact ⟨final, ticks, peak, trace, halted, accepts, by omega, by omega, checked⟩

theorem proper_execution (parameters : Parameters) (raw : parameters.layout = .raw)
    (basis : GateBasis.Basis) (uses : GateBasis.Uses parameters.decoder basis) (proper : basis ≠
      GateBasis.full)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch parameters.decoder rows)
    (heads : UniformDAGSource.HeadsMatch parameters.decoder rows matched) (rootMatches : RootsMatch
      parameters.decoder roots) :
    let built := ProperDetectorConstruction.build parameters basis rows roots
    ∃ final ticks peak, Execution built.1.program built.1.initial final ticks peak ∧ final.halted =
      true ∧
      built.2 + ticks ≤ 21000000 * (parameters.channels + parameters.decoder.roots.length + 1) *
        (parameters.decoder.countedSize + 1) +
        210000 * ((selectedSize parameters).total + 1) ∧
      programWords built.1.program + peak ≤ 100000 * (parameters.channels + 1) *
        (parameters.decoder.countedSize + 1) +
        1000 * ((selectedSize parameters).total + 1) ∧
      (built.1.accepted final = true ↔ parameters.drive = true ∧ ProperBasisDetector.Feasible
        parameters) ∧
      (built.1.accepted final = true → Certificate.ModelCheck.check (formula parameters)
        (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true)
          := by
  have whole := ProperDetectorConstruction.execution parameters raw basis uses proper rows roots
    matched heads rootMatches
  have constructed := ProperDetectorConstruction.clock parameters basis rows roots matched
    rootMatches
  dsimp only
  rw [ProperDetectorConstruction.image]
  obtain ⟨final, ticks, peak, trace, halted, time, space, accepts, checked⟩ := whole
  exact ⟨final, ticks, peak, trace, halted, by nlinarith, space, accepts, checked⟩

end Controller.Cost.ConstructedExtensionsComplete
