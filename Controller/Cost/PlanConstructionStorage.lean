/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ResolvedMetadataStorage
import Controller.Cost.ForestSourcePreparationStorage
import Controller.Cost.ResolvedFrontConstruction

/-! Cached selector ranks, child offsets, source-field operands and their
instruction emitter share one linear source preparation. Indexed updates use
the source word-vector model; native Lean allocator behaviour is separate. -/
namespace Controller.Cost.PlanConstructionStorage

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Cost.ForestIndexedOperands

variable {size : Nat}

inductive RanksTrace : List (Fin size) → Nat → Vector Nat size → Vector Nat size → Nat → Prop
  | nil (next table) : RanksTrace [] next table table (size + 16)
  | cons {index rest next table final peak}
      (tail : RanksTrace rest (next + 1) (table.set index next) final peak) :
      RanksTrace (index :: rest) next table final (peak + 16)

theorem ranks (indices : List (Fin size)) (next : Nat) (table : Vector Nat size) :
    ∃ peak, RanksTrace indices next table (AndRankConstruction.run indices next table) peak ∧
      peak ≤ size + 16 * indices.length + 16 := by
  induction indices generalizing next table with
  | nil => exact ⟨size + 16, .nil next table, by simp⟩
  | cons index rest ih =>
      obtain ⟨peak, tail, bound⟩ := ih (next + 1) (table.set index next)
      exact ⟨peak + 16, .cons tail, by simp only [List.length_cons]; omega⟩

structure Certificate (width : Nat) (graph : DAG n) (packet : Array (Word width))
    (rows : List Row) (roots : List Nat) (b : Nat) (target : Channel n)
    (rootSlot entry : Nat) where
  cachePeak : Nat
  ranksPeak : Nat
  fieldsPeak : Nat
  emitPeak : Nat
  cache : ForestSourcePreparationStorage.CacheTrace rows ForestCompilerOffsets.initial
    (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial) cachePeak
  ranks : RanksTrace (BoundedAnd.andIdentities graph) 0 (Vector.replicate graph.nodeCount 0)
    (AndRankConstruction.build graph) ranksPeak
  fields : ResolvedMetadataStorage.RowsTrace graph (List.finRange graph.nodeCount) fieldsPeak
  emitter : SourceOperandConstruction.Trace width entry
    (ResolvedPlanProducer.compile width graph packet rows roots b target rootSlot).1
    (SourceOperandConstruction.build width entry
      (ResolvedPlanProducer.compile width graph packet rows roots b target rootSlot).1).1
    (SourceOperandConstruction.build width entry
      (ResolvedPlanProducer.compile width graph packet rows roots b target rootSlot).1).2 emitPeak

def buffers (width : Nat) (graph : DAG n) (packet : Array (Word width))
    (rows : List Row) (roots : List Nat) (b : Nat) (target : Channel n)
    (rootSlot entry : Nat)
    (certificate : Certificate width graph packet rows roots b target rootSlot entry) : Nat :=
  certificate.cachePeak + certificate.ranksPeak + certificate.fieldsPeak + certificate.emitPeak +
    256 * (packet.size + n + rows.length + (rowChildren rows).length +
      (rowGuards rows).length + roots.length +
      (ResolvedPlanProducer.compile width graph packet rows roots b target rootSlot).1.length + 1)

theorem complete (width : Nat) (graph : DAG n) (packet : Array (Word width))
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (rootMatches : RootsMatch graph roots) (b : Nat) (target : Channel n)
    (reference : Fin graph.nodeCount) (rootSlot entry : Nat) :
    ∃ certificate : Certificate width graph packet rows roots b target rootSlot entry,
      buffers width graph packet rows roots b target rootSlot entry certificate ≤
        1000000 * (graph.countedSize + 1) + 256 * packet.size := by
  obtain ⟨cachePeak, cache, cacheBound⟩ := ForestSourcePreparationStorage.cache_space
    rows ForestCompilerOffsets.initial
  obtain ⟨ranksPeak, rankTrace, rankBound⟩ := ranks (BoundedAnd.andIdentities graph)
    0 (Vector.replicate graph.nodeCount 0)
  obtain ⟨fieldsPeak, fields, fieldsBound⟩ := ResolvedMetadataStorage.rows
    graph (List.finRange graph.nodeCount)
  obtain ⟨emitPeak, emitter, emitBound⟩ := SourceOperandConstruction.storage width entry
    (ResolvedPlanProducer.compile width graph packet rows roots b target rootSlot).1
  have length : (ResolvedPlanProducer.compile width graph packet rows roots b target
      rootSlot).1.length ≤
      11 * (graph.countedSize + 1) := by
    rw [ResolvedPlanProducer.compile_image width graph packet rows roots matched b target rootSlot,
      ResolvedSourcePlan.query_length graph packet rows roots b target reference]
    have source := ResolvedResident.rows_bound graph ∅ b target reference
    omega
  have ands : (BoundedAnd.andIdentities graph).length ≤ graph.nodeCount := by
    exact (List.length_filter_le _ _).trans_eq List.length_finRange
  rw [ResolvedPlanProducer.full_budget] at fieldsBound
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have rootLength : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have size := graph.countedSize_eq
  simp only [ForestSourcePreparationStorage.cacheWords, ForestCompilerOffsets.initial,
    Array.size_empty] at cacheBound
  refine ⟨⟨cachePeak, ranksPeak, fieldsPeak, emitPeak, cache, rankTrace, fields, emitter⟩, ?_⟩
  simp only [buffers, matched.length_eq, children, guards, rootLength]
  simp only [matched.length_eq] at cacheBound
  omega

end Controller.Cost.PlanConstructionStorage
