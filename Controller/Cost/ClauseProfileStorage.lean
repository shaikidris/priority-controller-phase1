module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ResolvedSourceProfile
public import Controller.Cost.WordConstructionStorage

@[expose] public section


/-! Guard membership scans retain source-list tails and one finite-channel
filter. Their storage follows scan depth and retained output, not scan time. -/
namespace Controller.Cost.ClauseProfileStorage

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions

inductive ContainsTrace [DecidableEq α] (value : α) : List α → Bool → Nat → Prop
  | nil : ContainsTrace value [] false 16
  | hit (rest) : ContainsTrace value (value :: rest) true 16
  | miss {head rest answer peak} (different : head ≠ value)
      (tail : ContainsTrace value rest answer peak) : ContainsTrace value (head :: rest) answer
        (peak + 16)

theorem contains [DecidableEq α] (value : α) (labels : List α) :
    ∃ peak, ContainsTrace value labels (labels.contains value) peak ∧ peak ≤ 16 * labels.length + 16
      := by
  induction labels with
  | nil => exact ⟨16, .nil, by simp⟩
  | cons head rest ih =>
      by_cases same : head = value
      · subst head
        refine ⟨16, ?_, ?_⟩
        · simpa using ContainsTrace.hit (value := value) rest
        · simp only [List.length_cons]
          omega
      · obtain ⟨peak, tail, bound⟩ := ih
        refine ⟨peak + 16, ?_, by simp only [List.length_cons]; omega⟩
        simpa [same, Ne.symm same] using ContainsTrace.miss same tail

inductive FilterTrace [DecidableEq α] (labels : List α) : List α → List α → Nat → Prop
  | nil : FilterTrace labels [] [] 16
  | cons {value rest answer output first later}
      (checked : ContainsTrace value labels answer first)
      (tail : FilterTrace labels rest output later) :
      FilterTrace labels (value :: rest) (if answer then value :: output else output)
        (max (first + 32) (later + 48))

theorem filter [DecidableEq α] (labels indices : List α) :
    ∃ peak, FilterTrace labels indices (indices.filter labels.contains) peak ∧
      peak ≤ 64 * indices.length + 16 * labels.length + 64 := by
  induction indices with
  | nil => exact ⟨16, .nil, by simp⟩
  | cons value rest ih =>
      obtain ⟨first, checked, firstBound⟩ := contains value labels
      obtain ⟨later, tail, tailBound⟩ := ih
      refine ⟨max (first + 32) (later + 48), ?_, ?_⟩
      · simpa only [List.filter_cons] using FilterTrace.cons checked tail
      · simp only [List.length_cons]
        exact Nat.max_le.mpr ⟨by omega, by omega⟩

def NodeEvidence (graph : DAG n) (index : Fin graph.nodeCount) (peak : Nat) : Prop :=
  match graph.node index with
  | .guard _ labels => ∃ first, FilterTrace labels (List.finRange n)
      ((List.finRange n).filter labels.contains) first ∧ peak = first + 64
  | _ => peak = 64 * (1 + (graph.node index).children.length)

theorem node (graph : DAG n) (index : Fin graph.nodeCount) :
    ∃ peak, NodeEvidence graph index peak ∧ peak ≤ 64 * n +
      128 * (1 + (graph.node index).children.length + (graph.node index).guardLabels.length) := by
  cases gate : graph.node index with
  | guard child labels =>
      obtain ⟨peak, trace, bound⟩ := filter labels (List.finRange n)
      refine ⟨peak + 64, ?_, ?_⟩
      · simpa only [NodeEvidence, gate] using ⟨peak, trace, rfl⟩
      · simp only [List.length_finRange] at bound
        simp only [gate, Gate.children, Gate.guardLabels, List.length_cons, List.length_nil]
        omega
  | zero => exact ⟨64 * (1 + (graph.node index).children.length), by simp [NodeEvidence, gate], by
    simp only [gate, Gate.children, Gate.guardLabels]; omega⟩
  | input channel => exact ⟨64 * (1 + (graph.node index).children.length), by simp [NodeEvidence,
    gate], by simp only [gate, Gate.children, Gate.guardLabels]; omega⟩
  | disj children => exact ⟨64 * (1 + (graph.node index).children.length), by simp [NodeEvidence,
    gate], by simp only [gate, Gate.children, Gate.guardLabels]; omega⟩
  | liveAnd left right => exact ⟨64 * (1 + (graph.node index).children.length), by simp
    [NodeEvidence, gate], by simp only [gate, Gate.children, Gate.guardLabels]; omega⟩

inductive NodesTrace (graph : DAG n) : List (Fin graph.nodeCount) → List Nat → Nat → Prop
  | nil : NodesTrace graph [] [] 32
  | cons {index rest output first later}
      (formed : NodeEvidence graph index first)
      (tail : NodesTrace graph rest output later)
      (copied : CompilerAppendTrace.AppendTrace (ResolvedSourceProfile.node graph index).1 output
        ((ResolvedSourceProfile.node graph index).1 ++ output) (ResolvedSourceProfile.node graph
          index).1.length) :
      NodesTrace graph (index :: rest) ((ResolvedSourceProfile.node graph index).1 ++ output)
        (max (first + 32) (later + 16 * (ResolvedSourceProfile.node graph index).1.length + 32))

theorem nodes (graph : DAG n) (indices : List (Fin graph.nodeCount)) :
    ∃ peak, NodesTrace graph indices (ResolvedSourceProfile.nodes graph indices).1 peak ∧
      peak ≤ 64 * n + 512 * ResolvedPlanProducer.budget graph indices + 128 := by
  induction indices with
  | nil => exact ⟨32, .nil, by simp [ResolvedPlanProducer.budget]⟩
  | cons index rest ih =>
      obtain ⟨first, formed, firstBound⟩ := node graph index
      obtain ⟨later, tail, tailBound⟩ := ih
      have length := ResolvedSourceProfile.node_length graph index
      refine ⟨_, .cons formed tail (CompilerAppendTrace.append_exists _ _), ?_⟩
      simp only [ResolvedPlanProducer.budget, List.length_cons, List.map_cons, List.sum_cons] at *
      exact Nat.max_le.mpr ⟨by omega, by omega⟩

theorem complete (graph : DAG n) :
    ∃ peak, NodesTrace graph (List.finRange graph.nodeCount)
      (ResolvedSourceProfile.nodes graph (List.finRange graph.nodeCount)).1 peak ∧
      peak ≤ 1000 * (graph.countedSize + 1) := by
  obtain ⟨peak, trace, bound⟩ := nodes graph (List.finRange graph.nodeCount)
  rw [ResolvedPlanProducer.full_budget] at bound
  have size := graph.countedSize_eq
  exact ⟨peak, trace, by omega⟩

end Controller.Cost.ClauseProfileStorage
