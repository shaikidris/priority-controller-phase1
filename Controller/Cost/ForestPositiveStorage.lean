module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ForestPositiveConstruction
public import Controller.Cost.ForestDescriptorStorage
public import Controller.Cost.WordConstructionStorage

@[expose] public section


/-! Construction storage of the positive descriptor/witness image. Descriptor
control and witness arithmetic have explicit traces. The front-list and final
append buffers are charged together with the temporary descriptor array. -/
namespace Controller.Cost.ForestPositiveStorage

open Controller.Cost Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestPositiveConstruction

variable {W : Type}

/-- The envelope includes retained front instructions, their append copies
and the fixed caller/environment words. Generic weight data is read-only. -/
def bufferWords (width : Nat) (state : ForestWeightedIndexed.State n W) (candidate : Candidate W)
    (descriptorPeak witnessPeak : Nat) : Nat :=
  descriptorPeak + witnessPeak + 12 * (leading width state candidate).length +
    6 * state.descriptors.entries.length + 64

theorem construction (width sourceBase nodes children guards roots entry countAddress : Nat)
    (state : ForestWeightedIndexed.State n W) (candidate : Candidate W) :
    let front := leading width state candidate
    let rootBase := sourceBase + 6 * nodes + children + guards
    let packetEnd := rootBase + roots
    let markerBase := packetEnd + 2 * state.descriptors.count
    let environment := fun i : Fin 9 => [entry + front.length, markerBase + n + 2, markerBase + n + 1,
      packetEnd, rootBase, sourceBase, nodes, markerBase, countAddress].getD i.val 0
    ∃ final descriptorPeak witnessPeak,
      ForestDescriptorStorage.SpaceTrace width n candidate.root candidate.pointer
        ⟨.reverse state.descriptors.entries [], #[]⟩ final
        (5 * state.descriptors.entries.length + 2 * n + 11) descriptorPeak ∧
      WordConstructionStorage.Trace environment (ForestConstructionRecipes.witness.constructionRecipe width)
        (evaluate environment (ForestConstructionRecipes.witness.constructionRecipe width)) 930 witnessPeak ∧
      bufferWords width state candidate descriptorPeak witnessPeak ≤
        50000 + 200 * state.descriptors.entries.length + 100 * n := by
  intro front rootBase packetEnd markerBase environment
  obtain ⟨final, descriptorPeak, descriptorTrace, descriptorBound, done⟩ :=
    ForestDescriptorStorage.complete (width := width) n state.descriptors.entries candidate.root candidate.pointer #[]
  obtain ⟨witnessPeak, witnessTrace, witnessBound⟩ :=
    WordConstructionStorage.construction environment (ForestConstructionRecipes.witness.constructionRecipe width)
  rw [ForestConstructionRecipes.witness.constructionRecipe_work] at witnessTrace witnessBound
  refine ⟨final, descriptorPeak, witnessPeak, descriptorTrace, witnessTrace, ?_⟩
  simp only [Array.size_empty, Nat.mul_zero, Nat.zero_add] at descriptorBound
  simp only [bufferWords, leading_length]
  omega


def witnessEnvironment (width sourceBase nodes children guards roots entry countAddress : Nat)
    (state : ForestWeightedIndexed.State n W) (candidate : Candidate W) (index : Fin 9) : Nat :=
  let rootBase := sourceBase + 6 * nodes + children + guards
  let packetEnd := rootBase + roots
  let markerBase := packetEnd + 2 * state.descriptors.count
  [entry + (leading width state candidate).length, markerBase + n + 2, markerBase + n + 1,
    packetEnd, rootBase, sourceBase, nodes, markerBase, countAddress].getD index.val 0

structure Certificate (width sourceBase nodes children guards roots entry countAddress : Nat)
    (state : ForestWeightedIndexed.State n W) (candidate : Candidate W) where
  final : ForestDescriptorConstruction.Configuration width
  descriptorPeak : Nat
  witnessPeak : Nat
  descriptor : ForestDescriptorStorage.SpaceTrace width n candidate.root candidate.pointer
    ⟨.reverse state.descriptors.entries [], #[]⟩ final
    (5 * state.descriptors.entries.length + 2 * n + 11) descriptorPeak
  witness : WordConstructionStorage.Trace
    (witnessEnvironment width sourceBase nodes children guards roots entry countAddress state candidate)
    (ForestConstructionRecipes.witness.constructionRecipe width)
    (evaluate (witnessEnvironment width sourceBase nodes children guards roots entry countAddress state candidate)
      (ForestConstructionRecipes.witness.constructionRecipe width)) 930 witnessPeak

theorem certificate (width sourceBase nodes children guards roots entry countAddress : Nat)
    (state : ForestWeightedIndexed.State n W) (candidate : Candidate W) :
    ∃ cert : Certificate width sourceBase nodes children guards roots entry countAddress state candidate,
      bufferWords width state candidate cert.descriptorPeak cert.witnessPeak ≤
        50000 + 200 * state.descriptors.entries.length + 100 * n := by
  obtain ⟨final, descriptorPeak, witnessPeak, descriptor, witness, bound⟩ :=
    construction width sourceBase nodes children guards roots entry countAddress state candidate
  exact ⟨⟨final, descriptorPeak, witnessPeak, descriptor, witness⟩, bound⟩

end Controller.Cost.ForestPositiveStorage
