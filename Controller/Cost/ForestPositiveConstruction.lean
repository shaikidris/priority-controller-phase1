module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ForestDescriptorConstruction
public import Controller.Cost.ForestConstructionRecipes

@[expose] public section


/-! The positive witness image is formed from the selector's computed records.
The descriptor writer is executed with its proved fuel bound; the witness
kernel is evaluated from a fixed first-order recipe and scalar source offsets.
The supplied selector state has a separate execution contract. -/
namespace Controller.Cost.ForestPositiveConstruction

open Controller Controller.Decoder Controller.Decoder.DAG
open Controller.Cost Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedTagged
open Controller.Cost.ForestCursorDescriptors Controller.Cost.ForestCursorAllRoots
open Controller.Cost.ForestCursorAllRootsExecution

variable {W : Type}

def leading (width : Nat) (state : ForestWeightedIndexed.State n W) (candidate : Candidate W) :
    List (Instruction width 4) :=
  (ForestDescriptorConstruction.run width n candidate.root candidate.pointer
    (5 * state.descriptors.entries.length + 2 * n + 11)
    ⟨.reverse state.descriptors.entries [], #[]⟩).image.toList

theorem leading_image (width : Nat) (state : ForestWeightedIndexed.State n W) (candidate : Candidate W) :
    leading width state candidate = descriptorCode width state ++ candidateCode width candidate := by
  have trace := ForestDescriptorConstruction.prefix_exact (width := width) state candidate #[]
  have actual := trace.run
  unfold leading
  rw [actual]
  simp

def form (width sourceBase nodes children guards roots entry countAddress : Nat)
    (state : ForestWeightedIndexed.State n W) (candidate : Candidate W) : List (Instruction width 4) :=
  let front := leading width state candidate
  let rootBase := sourceBase + 6 * nodes + children + guards
  let packetEnd := rootBase + roots
  let markerBase := packetEnd + 2 * state.descriptors.count
  front ++ evaluate (fun i => [entry + front.length, markerBase + n + 2, markerBase + n + 1,
      packetEnd, rootBase, sourceBase, nodes, markerBase, countAddress].getD i.val 0)
    (ForestConstructionRecipes.witness.constructionRecipe width)

/-- Source offsets use the retained descriptor count. The equation to the
old graph-based count occurs only in the correctness statement. -/
theorem form_image (width : Nat) (heap : Array (Word width)) (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (state : ForestWeightedIndexed.State n W)
    (candidate : Candidate W) (descriptors : state.descriptors = buildRoots graph)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ record ∈ (buildRoots graph).entries, record.position < 2 ^ width)
    (entry countAddress : Nat) :
    form width heap.size rows.length (ForestIndexedOperands.rowChildren rows).length
      (ForestIndexedOperands.rowGuards rows).length roots.length entry countAddress state candidate =
      selectedItems width heap graph rows roots state candidate countFits positionFits entry countAddress := by
  simp only [form, leading_image, ForestConstructionRecipes.witness.constructionRecipe_eq,
    ForestConstructionRecipes.witness, selectedItems, provenanceCell, setupLayout, setupOffset,
    descriptors, ForestIndexedOperands.cacheHeap_size, List.append_assoc]
  simp only [setupRoutes, extendRouteDescriptors, allRepresented, ForestCursorMaterialize.represented,
    ForestIndexedOperands.cacheHeap_size]

/-- Control transitions include descriptor reversal and zero-region writes;
recipe work includes every source-dependent witness operand. Final array
materialization is charged separately by the complete image assembler. -/
def constructionWork (width : Nat) (state : ForestWeightedIndexed.State n W) (candidate : Candidate W) : Nat :=
  20 * (5 * state.descriptors.entries.length + 2 * n + 11) +
    work (ForestConstructionRecipes.witness.constructionRecipe width) +
    2 * (leading width state candidate).length + 200

theorem leading_length (width : Nat) (state : ForestWeightedIndexed.State n W) (candidate : Candidate W) :
    (leading width state candidate).length = 4 * state.descriptors.entries.length + 2 * n + 8 := by
  rw [leading_image]
  simp only [descriptorCode, descriptorValues, List.length_append,
    ForestCursorMaterialize.writeCode_length, ForestCursorMaterialize.fields_length,
    List.length_reverse, List.length_replicate, candidateCode, List.length_cons, List.length_nil]
  omega

theorem work_bound (width : Nat) (state : ForestWeightedIndexed.State n W) (candidate : Candidate W) :
    constructionWork width state candidate ≤ 1500 + 120 * state.descriptors.entries.length + 48 * n := by
  simp only [constructionWork, leading_length, ForestConstructionRecipes.witness.constructionRecipe_work]
  omega

end Controller.Cost.ForestPositiveConstruction
