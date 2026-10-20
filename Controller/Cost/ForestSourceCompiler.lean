/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ForestCompilerStorage
import Controller.Cost.ForestCompilerRanges

/-! Complete original-source forest construction contract. The source/list
construction clock, retained construction words and fetched execution use
separate measures. Weight arithmetic and encoded input/output costs retain
their separate contracts. -/
namespace Controller.Cost.ForestSourceCompiler

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.ForestRootProjection Controller.Cost.ForestIndexedOperands

variable {n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- The output architecture is selected from raw source counts. -/
def sourceWidth (channels : Nat) (rows : List Row) (roots : List Nat) : Nat :=
  Nat.log 2 (10000 * (channels + rows.length + roots.length +
    (rowChildren rows).length + (rowGuards rows).length + 1)) + 1

def build (rows : List Row) (roots : List Nat) (weights : Channel n → W) (b : Nat) (target : Channel n) :
    Program (sourceWidth n rows roots) 8 :=
  ForestSourceImage.build (sourceWidth n rows roots) rows roots weights b target

omit [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W] in
theorem source_width (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots) :
    sourceWidth n rows roots = chosenMixedWidth graph := by
  have incidence := matched_incidence_lengths graph rows matched
  have rootsLength : roots.length = graph.roots.length := by rw [rootMatches, List.length_map]
  simp only [sourceWidth, chosenMixedWidth, forestSize, matched.length_eq, incidence.1, incidence.2, rootsLength]

/-- The complete source constructor terminates with the same resident as the
checked cold algorithm, with linear charged construction and retained storage
in the displayed models. Neither a selected answer nor healthy families are
inputs to the constructor. -/
theorem construction (graph : DAG n) (forest : graph.FormulaForest) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (weights : Channel n → W) (b : Nat) (target : Channel n) :
    let width := chosenMixedWidth graph
    ForestSourceImage.build width rows roots weights b target =
      ForestWeightedCold.program graph forest rows roots matched weights b target ∧
    ForestSourceResources.constructionWork width rows roots weights b target ≤ 200000 * (graph.countedSize + 1) ∧
    ∃ certificate : ForestCompilerStorage.Certificate width graph rows roots weights b target,
      ForestCompilerStorage.words width graph rows roots weights b target certificate ≤
        20000000 * (graph.countedSize + 1) := by
  intro width
  have size : graph.countedSize = forestSize graph := by
    rw [DAG.countedSize_eq]
    unfold forestSize
    omega
  have capacity : 256 * (graph.countedSize + 1) < 2 ^ width := by
    have room := chosenMixedCapacity graph
    dsimp only [width]
    omega
  have descriptors := original_descriptor_capacity graph forest target
  refine ⟨ForestSourceOptimal.image graph forest rows roots matched heads rootMatches weights b target,
    ForestSourceResources.construction_bound graph forest rows roots matched heads rootMatches weights b target width capacity
      descriptors.1 descriptors.2, ?_⟩
  exact ForestCompilerStorage.construction graph forest rows roots matched heads rootMatches weights b target width capacity
    descriptors.1 descriptors.2


/-- The public raw-source entry chooses its own width and returns the same
checked resident. The heterogeneous equation preserves its exact dependent
program type without making the graph specification a runtime input. -/
theorem build_eq (graph : DAG n) (forest : graph.FormulaForest) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (weights : Channel n → W) (b : Nat) (target : Channel n) :
    HEq (build rows roots weights b target) (ForestWeightedCold.program graph forest rows roots matched weights b target) := by
  unfold build
  rw [source_width graph rows roots matched rootMatches]
  exact heq_of_eq (ForestSourceOptimal.image graph forest rows roots matched heads rootMatches weights b target)

end Controller.Cost.ForestSourceCompiler
