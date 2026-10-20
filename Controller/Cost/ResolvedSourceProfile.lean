module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ClauseProfileCounts
public import Controller.Extensions.ResolvedNativeProfile
public import Mathlib.Tactic.Linarith

@[expose] public section


/-! Normalized row sizes from original source fields. A guard counts distinct
channel labels by finite membership scans; its negative child cannot coincide
with a positive channel or with its later parent. -/
namespace Controller.Cost.ResolvedSourceProfile

open Controller Controller.Decoder Controller.Decoder.DAG Controller.CNF Controller.Cost
  Controller.Extensions

variable {n : Nat}

def node (graph : DAG n) (index : Fin graph.nodeCount) : List Nat × Nat :=
  match graph.node index with
  | .zero => ([0], 32)
  | .input _ => ([1, 1], 64)
  | .disj children => (List.replicate children.length 1, 32 * children.length + 32)
  | .guard _ labels => ([(ClauseProfileCounts.unique labels).1 + 1], (ClauseProfileCounts.unique
    labels).2 + 32)
  | .liveAnd _ _ => ([1], 32)

theorem node_value (graph : DAG n) (index : Fin graph.nodeCount) :
    (node graph index).1 = ((BoundedAnd.resolved graph ∅).nodeClauses index).map
      (fun clause => (Horn.Worklist.compileClause clause).positives.length) := by
  have before (child : Fin index.val) : graph.childIndex index child ≠ index := by
    intro same
    have values := congrArg Fin.val same
    have bound := child.isLt
    simp only [DAG.childIndex] at values
    omega
  have implication (child : Fin index.val) :
      (Horn.Worklist.compileClause [(Sum.inr (graph.childIndex index child), false),
        (Sum.inr index, true)] : Horn.Worklist.Rule graph.ZeroVar).positives.length = 1 :=
    ResolvedNativeProfile.implication_positives _ _ (by simpa using before child)
  simp only [DAG.childIndex] at implication
  cases gate : graph.node index with
  | zero =>
      simp [node, BoundedAnd.resolved, gate, Gate.resolve, DAG.nodeClauses,
        ZeroSystem.implicationClause, ZeroSystem.positiveClause, Horn.Worklist.compileClause,
        Horn.Worklist.tautologyCheck, Horn.Worklist.signedLabels, Horn.Worklist.Rule.positives,
        Controller.CNF.negate, Std.Sat.Literal.negate]
  | input channel =>
      have forward := ResolvedNativeProfile.implication_positives
        (Sum.inl channel : graph.ZeroVar) (Sum.inr index) (by simp)
      have backward := ResolvedNativeProfile.implication_positives
        (Sum.inr index : graph.ZeroVar) (Sum.inl channel) (by simp)
      simp only [node, BoundedAnd.resolved, gate, Gate.resolve, DAG.nodeClauses,
        ZeroSystem.implicationClause, ZeroSystem.positiveClause, List.map_cons, List.map_nil]
      rw [forward, backward]
  | disj children =>
      simp [node, BoundedAnd.resolved, gate, Gate.resolve, DAG.nodeClauses,
        ZeroSystem.implicationClause, ZeroSystem.positiveClause, List.map_map, Function.comp_def,
          DAG.childIndex, implication]
  | guard child labels =>
      have current := ClauseProfileCounts.implication_count (graph.childIndex index child) index
        (before child) labels
      simp only [DAG.childIndex] at current
      simp only [node, BoundedAnd.resolved, gate, Gate.resolve, DAG.nodeClauses,
        DAG.childIndex, List.map_cons, List.map_nil, ZeroSystem.implicationClause,
          ZeroSystem.positiveClause,
        List.map_append, List.map_map, Function.comp_def, List.map_singleton]
      rw [ClauseProfileCounts.unique_value]
      exact congrArg (fun value => [value]) (by simpa only [List.cons_append] using current.symm)
  | liveAnd left right =>
      simp [node, BoundedAnd.resolved, gate, Gate.resolve, DAG.nodeClauses,
        ZeroSystem.implicationClause, ZeroSystem.positiveClause, DAG.childIndex, implication]

theorem node_clock (graph : DAG n) (index : Fin graph.nodeCount) :
    (node graph index).2 ≤ 100 * (n + 1) *
      (1 + (graph.node index).children.length + (graph.node index).guardLabels.length) := by
  cases gate : graph.node index <;>
    simp only [node, gate, Gate.children, Gate.guardLabels, List.length_cons, List.length_nil,
      ClauseProfileCounts.unique]
  all_goals nlinarith

def nodes (graph : DAG n) : List (Fin graph.nodeCount) → List Nat × Nat
  | [] => ([], 1)
  | index :: rest =>
      let head := node graph index
      let tail := nodes graph rest
      (head.1 ++ tail.1, head.2 + tail.2 + 8 * head.1.length + 20)

theorem nodes_value (graph : DAG n) (indices : List (Fin graph.nodeCount)) :
    (nodes graph indices).1 = (indices.flatMap ((BoundedAnd.resolved graph ∅).nodeClauses)).map
      (fun clause => (Horn.Worklist.compileClause clause).positives.length) := by
  induction indices with
  | nil => rfl
  | cons index rest ih => simp only [nodes, node_value, ih, List.flatMap_cons, List.map_append]

theorem node_length (graph : DAG n) (index : Fin graph.nodeCount) :
    (node graph index).1.length ≤ 2 + (graph.node index).children.length := by
  cases gate : graph.node index <;> simp [node, gate, Gate.children]

theorem nodes_clock (graph : DAG n) (indices : List (Fin graph.nodeCount)) :
    (nodes graph indices).2 ≤ 200 * (n + 1) * ResolvedPlanProducer.budget graph indices + 1 := by
  induction indices with
  | nil => simp [nodes, ResolvedPlanProducer.budget]
  | cons index rest ih =>
      have head := node_clock graph index
      have length := node_length graph index
      simp only [nodes, ResolvedPlanProducer.budget, List.length_cons, List.map_cons, List.sum_cons]
        at *
      nlinarith

def rows (graph : DAG n) (b : Nat) : List Nat × Nat :=
  let forward := nodes graph (List.finRange graph.nodeCount)
  (List.replicate (n + graph.nodeCount) 0 ++ forward.1 ++ [n] ++
    (if b = 1 then [1] else []) ++ [0], forward.2 + 100 * (n + graph.nodeCount + 1))

theorem rows_value (graph : DAG n) (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount)
  :
    (rows graph b).1 = SharedNormalizationShape.profile (ResolvedResident.rows graph ∅ b target
      reference) := by
  have touched (coordinate : Fin (n + graph.nodeCount)) :
      (Horn.Worklist.compileClause [(coordinate, false), (coordinate, true)]).positives.length = 0
        := by
    simp [Horn.Worklist.compileClause, Horn.Worklist.tautologyCheck, CNF.negate,
      Std.Sat.Literal.negate,
      Horn.Worklist.Rule.positives]
  have nonempty : (Horn.Worklist.compileClause (ZeroSystem.positiveClause
      ((List.finRange n).map (Sum.inl : Channel n → graph.ZeroVar)))).positives.length = n := by
    rw [ZeroSystem.positiveClause, ClauseProfileCounts.positive_clause]
    rw [List.dedup_eq_self.mpr ((List.nodup_finRange n).map Sum.inl_injective)]
    simp
  have singleton : (Horn.Worklist.compileClause (ZeroSystem.positiveClause
      [(Sum.inl target : graph.ZeroVar)])).positives.length = 1 := by
    rw [ZeroSystem.positiveClause, ClauseProfileCounts.positive_clause]
    simp
  have negative : (Horn.Worklist.compileClause (ZeroSystem.implicationClause
      (Sum.inr reference : graph.ZeroVar) [])).positives.length = 0 := by
    simp [ZeroSystem.implicationClause, ZeroSystem.positiveClause, Horn.Worklist.compileClause,
      Horn.Worklist.tautologyCheck, Horn.Worklist.signedLabels, Horn.Worklist.Rule.positives,
      CNF.negate, Std.Sat.Literal.negate]
  let resolved := BoundedAnd.resolved graph ∅
  have mapped (clauses : List (Clause graph.ZeroVar)) :
      SharedNormalizationShape.profile
        (clauses.map (fun clause => clause.map (fun literal => (resolved.zeroIndex literal.1,
          literal.2)))) =
      clauses.map (fun clause => (Horn.Worklist.compileClause clause).positives.length) := by
    simp only [SharedNormalizationShape.profile, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro clause _
    exact SharedNormalizationShape.positives_length_map resolved.zeroIndex
      resolved.zeroIndex.injective clause
  have finite : SharedNormalizationShape.profile
      (resolved.finiteZeroSystem b target reference ∅ ∅).clauses.toList =
      (resolved.zeroSystem b target reference ∅ ∅).clauses.toList.map
        (fun clause => (Horn.Worklist.compileClause clause).positives.length) := by
    have clauseRelabel : Controller.CNF.OrderedFormula.Clause.relabel resolved.zeroIndex =
        fun clause => clause.map (fun literal => (resolved.zeroIndex literal.1, literal.2)) := by
      funext clause; rfl
    simpa only [clauseRelabel, DAG.finiteZeroSystem, CNF.relabel, Controller.CNF.OrderedFormula.relabel,
      Array.toList_map,
      Controller.CNF.OrderedFormula.Clause.relabel] using mapped (resolved.zeroSystem b target reference ∅
        ∅).clauses.toList
  change _ = SharedNormalizationShape.profile
    (SharedZeroTemplate.touchRows (n + graph.nodeCount) ++ (resolved.finiteZeroSystem b target
      reference ∅ ∅).clauses.toList)
  simp only [SharedNormalizationShape.profile, List.map_append] at finite ⊢
  rw [finite]
  simp only [rows, nodes_value, SharedZeroTemplate.touchRows, List.map_map, Function.comp_def,
    touched, List.map_const', List.length_finRange, DAG.zeroSystem, CNF.ofClauses,
    List.toList_toArray, List.map_append, DAG.forwardClauses, DAG.channelClauses,
    DAG.trueUnitClauses, DAG.falseUnitClauses, List.map_nil, List.append_nil,
    List.map_cons, List.map_singleton, nonempty, singleton, negative]
  split_ifs <;> simp_all [List.append_assoc, resolved]

theorem rows_clock (graph : DAG n) (b : Nat) :
    (rows graph b).2 ≤ 400 * (n + 1) * (graph.countedSize + 1) := by
  have clock := nodes_clock graph (List.finRange graph.nodeCount)
  rw [ResolvedPlanProducer.full_budget] at clock
  have size := graph.countedSize_eq
  simp only [rows]
  nlinarith

end Controller.Cost.ResolvedSourceProfile
