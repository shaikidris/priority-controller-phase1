module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ResolvedNativeLayoutConstruction
public import Controller.Cost.ClauseProfileStorage
public import Controller.Cost.ForestDirectoryStorage

@[expose] public section


/-! Storage for source-row and scalar layout preparation. Source-node
constructors expose the six syntax cases; reference records and profiles have
independent list traces. No normalized clause matrix is retained. -/
namespace Controller.Cost.ResolvedMetadataStorage

open Controller Controller.Decoder Controller.Decoder.DAG Controller.CNF Controller.Cost
  Controller.Extensions

/-- Each source case constructs its fixed row skeleton and maps supplied
child/guard IDs. The envelope includes literal records, both relabel buffers
and the continuation of their source-list traversals. -/
inductive NodeTrace (graph : DAG n) (index : Fin graph.nodeCount) : Nat → Prop
  | zero (gate : graph.node index = .zero) : NodeTrace graph index 512
  | input (channel) (gate : graph.node index = .input channel) : NodeTrace graph index 512
  | disj (children) (gate : graph.node index = .disj children) : NodeTrace graph index (512 *
    (children.length + 1))
  | guard (child labels) (gate : graph.node index = .guard child labels) : NodeTrace graph index
    (512 * (labels.length + 2))
  | liveAnd (left right) (gate : graph.node index = .liveAnd left right) : NodeTrace graph index
    1536

theorem node (graph : DAG n) (index : Fin graph.nodeCount) :
    ∃ peak, NodeTrace graph index peak ∧ peak ≤ 512 *
      (1 + (graph.node index).children.length + (graph.node index).guardLabels.length) := by
  cases gate : graph.node index with
  | zero => exact ⟨512, .zero gate, by simp [gate, Gate.children, Gate.guardLabels]⟩
  | input channel => exact ⟨512, .input channel gate, by simp [gate, Gate.children,
    Gate.guardLabels]⟩
  | disj children => exact ⟨_, .disj children gate, by simp [gate, Gate.children, Gate.guardLabels,
    Nat.add_comm]⟩
  | guard child labels =>
      refine ⟨_, .guard child labels gate, ?_⟩
      simp only [gate, Gate.children, Gate.guardLabels, List.length_cons, List.length_nil]
      omega
  | liveAnd left right => exact ⟨1536, .liveAnd left right gate, by simp [gate, Gate.children,
    Gate.guardLabels]⟩

theorem node_sizes (graph : DAG n) (index : Fin graph.nodeCount) :
    (ResolvedRowsConstruction.node graph index).1.length + (ResolvedRowsConstruction.node graph
      index).1.flatten.length ≤
      7 + 3 * (graph.node index).children.length + (graph.node index).guardLabels.length := by
  cases gate : graph.node index <;>
    simp [ResolvedRowsConstruction.node, BoundedAnd.resolved, gate, Gate.resolve, DAG.nodeClauses,
      ZeroSystem.implicationClause, ZeroSystem.positiveClause, Gate.children, Gate.guardLabels,
      List.length_flatten, List.map_map, Function.comp_def, List.sum_map_add] <;> omega

inductive RowsTrace (graph : DAG n) : List (Fin graph.nodeCount) → Nat → Prop
  | nil : RowsTrace graph [] 32
  | cons {index rest first later}
      (head : NodeTrace graph index first) (tail : RowsTrace graph rest later)
      (copied : CompilerAppendTrace.AppendTrace (ResolvedRowsConstruction.node graph index).1
        (ResolvedRowsConstruction.nodes graph rest).1
        ((ResolvedRowsConstruction.node graph index).1 ++ (ResolvedRowsConstruction.nodes graph
          rest).1)
        (ResolvedRowsConstruction.node graph index).1.length) :
      RowsTrace graph (index :: rest) (max first (later + 64 *
        ((ResolvedRowsConstruction.node graph index).1.length + (ResolvedRowsConstruction.node graph
          index).1.flatten.length) + 64))

theorem rows (graph : DAG n) (indices : List (Fin graph.nodeCount)) :
    ∃ peak, RowsTrace graph indices peak ∧ peak ≤ 2048 * ResolvedPlanProducer.budget graph indices +
      64 := by
  induction indices with
  | nil => exact ⟨32, .nil, by simp [ResolvedPlanProducer.budget]⟩
  | cons index rest ih =>
      obtain ⟨first, head, firstBound⟩ := node graph index
      obtain ⟨later, tail, tailBound⟩ := ih
      have sizes := node_sizes graph index
      refine ⟨_, .cons head tail (CompilerAppendTrace.append_exists _ _), ?_⟩
      simp only [ResolvedPlanProducer.budget, List.length_cons, List.map_cons, List.sum_cons] at *
      exact Nat.max_le.mpr ⟨by omega, by omega⟩

inductive RowReferences : Nat → List (Literal (Fin ambient)) → Nat → Prop
  | nil (base) : RowReferences base [] 32
  | cons {base literal rest peak} (tail : RowReferences (base + 1) rest peak) :
      RowReferences base (literal :: rest) (peak + 64)

theorem row_references (base : Nat) (row : Clause (Fin ambient)) :
    ∃ peak, RowReferences base row peak ∧ peak ≤ 64 * row.length + 32 := by
  induction row generalizing base with
  | nil => exact ⟨32, .nil base, by simp⟩
  | cons literal rest ih =>
      obtain ⟨peak, tail, bound⟩ := ih (base + 1)
      exact ⟨peak + 64, .cons tail, by simp only [List.length_cons]; omega⟩

inductive ReferencesTrace : Nat → List (Clause (Fin ambient)) → Nat → Prop
  | nil (base) : ReferencesTrace base [] 32
  | cons {base row rest first later}
      (head : RowReferences base row first)
      (counted : CompilerAppendTrace.LengthTrace row row.length row.length)
      (tail : ReferencesTrace (base + row.length) rest later) :
      ReferencesTrace base (row :: rest) (first + later + 64)

theorem references (base : Nat) (clauses : List (Clause (Fin ambient))) :
    ∃ peak, ReferencesTrace base clauses peak ∧ peak ≤ 128 * (clauses.length +
      clauses.flatten.length + 1) := by
  induction clauses generalizing base with
  | nil => exact ⟨32, .nil base, by simp⟩
  | cons row rest ih =>
      obtain ⟨first, head, firstBound⟩ := row_references base row
      obtain ⟨later, tail, tailBound⟩ := ih (base + row.length)
      refine ⟨_, .cons head (CompilerAppendTrace.length_exists row) tail, ?_⟩
      simp only [List.length_cons, List.flatten_cons, List.length_append]
      omega

structure Certificate (graph : DAG n) (b : Nat) (target : Channel n) (reference : Fin
  graph.nodeCount) where
  sourcePeak : Nat
  normalizedPeak : Nat
  profilePeak : Nat
  referencesPeak : Nat
  source : RowsTrace graph (List.finRange graph.nodeCount) sourcePeak
  normalized : ClauseProfileStorage.NodesTrace graph (List.finRange graph.nodeCount)
    (ResolvedSourceProfile.nodes graph (List.finRange graph.nodeCount)).1 normalizedPeak
  counted : ForestDirectoryStorage.ProfileTrace (ResolvedRowsConstruction.build graph b target
    reference).1
    (ForestDirectoryConstruction.profile (ResolvedRowsConstruction.build graph b target
      reference).1).1
    (ForestDirectoryConstruction.profile (ResolvedRowsConstruction.build graph b target
      reference).1).2.1
    (ForestDirectoryConstruction.profile (ResolvedRowsConstruction.build graph b target
      reference).1).2.2 profilePeak
  references : ReferencesTrace 2 (ResolvedRowsConstruction.build graph b target reference).1
    referencesPeak

def buffers (graph : DAG n) (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount)
    (certificate : Certificate graph b target reference) : Nat :=
  certificate.sourcePeak + certificate.normalizedPeak + certificate.profilePeak +
    certificate.referencesPeak +
    256 * (n + graph.nodeCount + (ResolvedRowsConstruction.build graph b target reference).1.length
      +
      (ResolvedRowsConstruction.build graph b target reference).1.flatten.length + 1)

theorem complete (graph : DAG n) (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount) :
    ∃ certificate : Certificate graph b target reference, buffers graph b target reference
      certificate ≤ 100000 * (graph.countedSize + 1) := by
  obtain ⟨sourcePeak, source, sourceBound⟩ := rows graph (List.finRange graph.nodeCount)
  obtain ⟨normalizedPeak, normalized, normalizedBound⟩ := ClauseProfileStorage.complete graph
  obtain ⟨profilePeak, counted, profileBound⟩ := ForestDirectoryStorage.profile_space
    (ResolvedRowsConstruction.build graph b target reference).1
  obtain ⟨referencesPeak, formed, referencesBound⟩ := references 2 (ResolvedRowsConstruction.build
    graph b target reference).1
  have bounded := ResolvedResident.rows_bound graph ∅ b target reference
  rw [ResolvedPlanProducer.full_budget] at sourceBound
  simp only [ResolvedRowsConstruction.image] at profileBound referencesBound
  have size := graph.countedSize_eq
  refine ⟨⟨sourcePeak, normalizedPeak, profilePeak, referencesPeak, source, normalized, counted,
    formed⟩, ?_⟩
  simp only [buffers, ResolvedRowsConstruction.image]
  omega

end Controller.Cost.ResolvedMetadataStorage
