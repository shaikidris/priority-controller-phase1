/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ResolvedPlanConstruction

/-! Selector-query operands formed directly from typed source fields. Only a
live AND produces a runtime selected read. Other gates preserve every source
child and guard occurrence in its original order. -/
namespace Controller.Cost.ResolvedNodeConstruction

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Cost.ForestIndexedOperands Controller.Extensions.ResolvedSourceEmit

def literal (width coordinate : Nat) : Operand width := .literal (word width coordinate)

def form (width : Nat) (graph : DAG n) (packet : Array (Word width))
    (cache : ResolvedPlanConstruction.Cache graph) (sourceEnd : Nat) (index : Fin graph.nodeCount) :
    List (Operand width) × Nat :=
  match graph.node index with
  | .zero => ([literal width (n + index.val)], 32)
  | .input channel =>
      ([literal width channel.val, literal width (n + index.val),
        literal width (n + index.val), literal width channel.val], 96)
  | .disj children =>
      (children.flatMap (fun child => [literal width (n + child.val), literal width (n +
        index.val)]),
        64 * children.length + 32)
  | .guard child labels =>
      (literal width (n + child.val) :: labels.map (fun channel => literal width channel.val) ++
        [literal width (n + index.val)], 32 * labels.length + 96)
  | .liveAnd _ _ =>
      ([.choice (sourceEnd + cache.ranks[index.val])
        (ResolvedPlanConstruction.childBase packet cache index.val)
        (ResolvedPlanConstruction.childBase packet cache index.val + 1) (word width n),
        literal width (n + index.val)], 96)

theorem image (width : Nat) (graph : DAG n) (packet : Array (Word width)) (rows : List Row)
    (roots : List Nat) (cache : ResolvedPlanConstruction.Cache graph) (sourceEnd : Nat)
    (storedEnd : sourceEnd = (cacheHeap width packet rows roots).size) (index : Fin graph.nodeCount)
      :
    (form width graph packet cache sourceEnd index).1 =
      ResolvedPlanConstruction.node width graph packet rows roots cache index := by
  subst sourceEnd
  cases gate : graph.node index <;>
    simp [form, ResolvedPlanConstruction.node, gate, literal, ResolvedSourcePlan.literals,
      ResolvedSourcePlan.coordinates, BoundedAnd.resolved, DAG.nodeClauses, Gate.resolve,
      DAG.zeroIndex, ZeroSystem.implicationClause, ZeroSystem.positiveClause,
      List.map_map, Function.comp_def, List.map_flatMap, List.flatten_eq_flatMap, List.flatMap_map]

theorem clock (width : Nat) (graph : DAG n) (packet : Array (Word width))
    (cache : ResolvedPlanConstruction.Cache graph) (sourceEnd : Nat) (index : Fin graph.nodeCount) :
    (form width graph packet cache sourceEnd index).2 ≤
      100 * (1 + (graph.node index).children.length + (graph.node index).guardLabels.length) := by
  cases gate : graph.node index <;> simp [form, gate, Gate.children, Gate.guardLabels] <;> omega

end Controller.Cost.ResolvedNodeConstruction
