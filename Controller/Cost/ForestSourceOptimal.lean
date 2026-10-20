/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ForestSourceImage
import Controller.Cost.ForestWeightedCold

/-! Physical optimum emission by the source-only instruction constructor.
Generic weight operations and encoded input/output sizes keep their separate
cost contracts. This theorem concerns the complete fetched execution; the
construction resource bound is stated separately. -/
namespace Controller.Cost.ForestSourceOptimal

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.ForestRootProjection Controller.Cost.ForestIndexedOperands

variable {n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

theorem image (graph : DAG n) (forest : graph.FormulaForest) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (rootsMatch : RootsMatch graph roots) (weights : Channel n → W) (b : Nat) (target : Channel n) :
    ForestSourceImage.build (chosenMixedWidth graph) rows roots weights b target =
      ForestWeightedCold.program graph forest rows roots matched weights b target := by
  have capacity := chosenMixedCapacity graph
  have size : graph.countedSize = forestSize graph := by
    rw [DAG.countedSize_eq]
    unfold forestSize
    omega
  have room : 256 * (graph.countedSize + 1) < 2 ^ chosenMixedWidth graph := by omega
  exact ForestSourceImage.build_image graph forest rows roots matched heads rootsMatch weights b target _ room
    (original_descriptor_capacity graph forest target).1 (original_descriptor_capacity graph forest target).2

/-- Healthy-zero weighted detection retains the attained nonnegative-weight
optimum. Classification, selection and native code formation are executed by
`ForestSourceImage.build`; no chosen-candidate or prebuilt-code premise occurs. -/
theorem execution (graph : DAG n) (forest : graph.FormulaForest)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched) (rootsMatch : RootsMatch graph roots)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : Nat) (bridge : Physical.Bridge n) (positive : 0 < b)
    (healthy : ∀ position : Fin graph.roots.length,
      graph.eval (assignmentOfSet {bridge.target}) (graph.roots.get position) = false)
    (detectable : Physical.BridgeDetectable (b := b) bridge true graph.observations)
    (rest output : List (Word (chosenMixedWidth graph)))
    (address loaded temporary : Word (chosenMixedWidth graph))
    (saved : Fin 8 → Word (chosenMixedWidth graph)) :
    ∃ K final ticks peak,
      Execution (ForestSourceImage.build (chosenMixedWidth graph) rows roots weights b bridge.target)
        (classificationInitial (chosenMixedWidth graph) graph rows roots (assignmentOfSet {bridge.target})
          bridge.target rest output address loaded temporary saved) final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word (chosenMixedWidth graph) 1 ∧
      Admissible b bridge.target K ∧
      Physical.BridgeInputDetects bridge true graph.observations
        (Physical.realizeBridge bridge positive K) true ∧
      final.heap = #[] ∧ final.stack = rest ∧
      final.output = List.ofFn (fun channel : Channel n =>
        boolWord (chosenMixedWidth graph) (decide (channel ∈ K))) ++ output ∧
      (∀ L, Admissible b bridge.target L →
        Physical.BridgeInputDetects bridge true graph.observations
          (Physical.realizeBridge bridge positive L) true →
        GenericWeight.total weights L ≤ GenericWeight.total weights K) ∧
      ticks ≤ 1000 * (forestSize graph + 1) ∧
      peak ≤ 200 * (forestSize graph + 1) + rest.length + output.length := by
  rw [image graph forest rows roots matched heads rootsMatch weights b bridge.target]
  exact ForestWeightedCold.chosen_execution graph forest rows roots matched heads rootsMatch weights nonnegative
    b bridge positive healthy detectable rest output address loaded temporary saved

end Controller.Cost.ForestSourceOptimal
