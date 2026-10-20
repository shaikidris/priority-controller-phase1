/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ResolvedSourceProfile

/-! Source-order literal rows for the fixed placement template. All fields are
original node IDs, guard labels or polarities. Runtime selector choices and
Boolean evaluation are absent from this construction. -/
namespace Controller.Cost.ResolvedRowsConstruction

open Controller Controller.Decoder Controller.Decoder.DAG Controller.CNF Controller.Cost
  Controller.Extensions

def node (graph : DAG n) (index : Fin graph.nodeCount) : List (Clause (Fin (n + graph.nodeCount))) ×
  Nat :=
  (((BoundedAnd.resolved graph ∅).nodeClauses index).map
      (fun clause => clause.map fun (literal : Literal graph.ZeroVar) => (graph.zeroIndex literal.1,
        literal.2)),
    100 * (1 + (graph.node index).children.length + (graph.node index).guardLabels.length))

def nodes (graph : DAG n) : List (Fin graph.nodeCount) → List (Clause (Fin (n + graph.nodeCount))) ×
  Nat
  | [] => ([], 1)
  | index :: rest =>
      let head := node graph index
      let tail := nodes graph rest
      (head.1 ++ tail.1, head.2 + tail.2 + 8 * head.1.length + 20)

theorem node_length (graph : DAG n) (index : Fin graph.nodeCount) :
    (node graph index).1.length ≤ 2 + (graph.node index).children.length := by
  cases gate : graph.node index <;>
    simp [node, BoundedAnd.resolved, gate, Gate.resolve, DAG.nodeClauses, Gate.children]

theorem nodes_clock (graph : DAG n) (indices : List (Fin graph.nodeCount)) :
    (nodes graph indices).2 ≤ 200 * ResolvedPlanProducer.budget graph indices + 1 := by
  induction indices with
  | nil => simp [nodes, ResolvedPlanProducer.budget]
  | cons index rest ih =>
      have length := node_length graph index
      simp only [nodes, node, ResolvedPlanProducer.budget, List.length_cons, List.map_cons,
        List.sum_cons] at *
      omega

theorem nodes_image (graph : DAG n) (indices : List (Fin graph.nodeCount)) :
    (nodes graph indices).1 = (indices.flatMap ((BoundedAnd.resolved graph ∅).nodeClauses)).map
      (fun clause => clause.map fun (literal : Literal graph.ZeroVar) => (graph.zeroIndex literal.1,
        literal.2)) := by
  induction indices with
  | nil => rfl
  | cons index rest ih => simp only [nodes, node, ih, List.flatMap_cons, List.map_append]

def build (graph : DAG n) (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount) :
    List (Clause (Fin (n + graph.nodeCount))) × Nat :=
  let forwards := nodes graph (List.finRange graph.nodeCount)
  let channels : List (Clause graph.ZeroVar) :=
    [ZeroSystem.positiveClause ((List.finRange n).map Sum.inl)] ++
      (if b = 1 then [ZeroSystem.positiveClause [Sum.inl target]] else [])
  (SharedZeroTemplate.touchRows (n + graph.nodeCount) ++ forwards.1 ++
    (channels ++ [ZeroSystem.implicationClause (Sum.inr reference) []]).map
      (fun (clause : Clause graph.ZeroVar) => clause.map fun (literal : Literal graph.ZeroVar) =>
        (graph.zeroIndex literal.1, literal.2)),
    forwards.2 + 1000 * (n + graph.nodeCount + 1))

theorem image (graph : DAG n) (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount) :
    (build graph b target reference).1 = ResolvedResident.rows graph ∅ b target reference := by
  have clauseRelabel : Controller.CNF.OrderedFormula.Clause.relabel graph.zeroIndex =
      fun clause => clause.map (fun literal => (graph.zeroIndex literal.1, literal.2)) := by
    funext clause; rfl
  have sameIndex : (BoundedAnd.resolved graph ∅).zeroIndex = graph.zeroIndex := rfl
  simp only [build, nodes_image, ResolvedResident.rows, SharedZeroTemplate.formula,
    DAG.finiteZeroSystem, CNF.relabel, Controller.CNF.OrderedFormula.relabel, Array.toList_map,
    CNF.ofClauses, List.toList_toArray, DAG.zeroSystem, List.map_append, DAG.forwardClauses,
    DAG.channelClauses, DAG.trueUnitClauses, DAG.falseUnitClauses]
  simp [sameIndex, clauseRelabel, List.append_assoc, List.map_append]

theorem clock (graph : DAG n) (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount) :
    (build graph b target reference).2 ≤ 2000 * (graph.countedSize + 1) := by
  have bounded := nodes_clock graph (List.finRange graph.nodeCount)
  rw [ResolvedPlanProducer.full_budget] at bounded
  have size := graph.countedSize_eq
  simp only [build]
  omega

end Controller.Cost.ResolvedRowsConstruction
