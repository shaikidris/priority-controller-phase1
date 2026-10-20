module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.BasisTableStorage
public import Controller.Cost.BasisOutputStorage
public import Controller.Cost.ProperNativeConstruction

@[expose] public section


/-! Proper-basis native assembly retains the source table image, redirected
root/witness schedule and the selected native continuation at the same time. -/
namespace Controller.Cost.ProperNativeStorage

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestIndexedOperands Controller.Cost.AssemblyStorage

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
attribute [local irreducible] BasisTableConstruction.monotone BasisTableConstruction.literal
  BasisOutputConstruction.monotone BasisOutputConstruction.literal
      NativeContinuationConstruction.finish

theorem monotone (parameters : Parameters) (graph : DAG parameters.channels) (width : Nat)
    (rows : List Row) (roots : List Nat) :
    Bounded (ProperNativeConstruction.monotone parameters graph width rows roots).1
      (300000000 * (parameters.channels + 1) * (graph.countedSize + 1) +
        3000000 * ((selectedSize parameters).total + 1)) := by
  let base := (LiteralDetector.sourceHeap width parameters.channels rows roots).size
  let found := MonotoneDetector.found graph parameters.buses
  let native := NativeContinuationConstruction.finish parameters width
    (base + (parameters.channels + 1) * graph.nodeCount) found
  let output := BasisOutputConstruction.monotone width parameters.buses parameters.bridge.target
    graph.nodeCount base found (found + native.1.length) graph.roots.length
    (MonotoneDetector.constructionSize graph) (SharedDetectorPrepared.rootBase graph)
  have table := BasisTableStorage.monotone graph width rows roots 0
  have returned := BasisOutputStorage.monotone width parameters.buses parameters.bridge.target
    graph.nodeCount base found (found + native.1.length) graph.roots.length
    (MonotoneDetector.constructionSize graph) (SharedDetectorPrepared.rootBase graph)
  have redirected := Trace.redirect returned
  have finished := AssemblyStorage.native parameters width
    (base + (parameters.channels + 1) * graph.nodeCount) found
  have halted := fixed (Instruction.halt : Instruction width 8) (by trivial)
  have assembled := join (join (join table redirected) finished) halted
  have tableSize : (BasisTableConstruction.monotone graph width rows roots 0).1.length =
      162 * parameters.channels + 143 + 2 * (parameters.channels + 1) * graph.nodeCount := by
    rw [BasisTableConstruction.monotone_image, Array.length_toList,
      MonotoneTableConstruction.code_size]
  have outputSize : output.1.length ≤ graph.roots.length * (39 + 18 * parameters.channels) + 2 := by
    dsimp only [output]
    rw [BasisOutputConstruction.monotone_image, MonotoneOutputSearch.code_length]
    have stride := Nat.mul_le_mul_left graph.roots.length
      (MonotoneOutputSearch.stride_bound parameters.buses parameters.channels)
    omega
  have nativeSize : native.1.length ≤ 34 * (selectedSize parameters).total + 1 := by
    dsimp only [native]
    rw [NativeContinuationConstruction.finish_image]
    exact BasisNativeFinish.code_bound parameters width _ _
  have size := graph.countedSize_eq
  have nodeBound := Nat.mul_le_mul_left (parameters.channels + 1)
    (by omega : graph.nodeCount ≤ graph.countedSize + 1)
  have rootBound := Nat.mul_le_mul_left (parameters.channels + 1)
    (by omega : graph.roots.length ≤ graph.countedSize + 1)
  dsimp only [ProperNativeConstruction.monotone]
  exact .enlarge assembled (by
    simp only [List.length_append, List.length_map] at *
    dsimp only [output, native, base, found] at *
    nlinarith)

theorem literal (parameters : Parameters) (graph : DAG parameters.channels) (width : Nat)
    (rows : List Row) (roots : List Nat) :
    Bounded (ProperNativeConstruction.literal parameters graph width rows roots).1
      (300000000 * (parameters.channels + 1) * (graph.countedSize + 1) +
        3000000 * ((selectedSize parameters).total + 1)) := by
  let base := (LiteralDetector.sourceHeap width parameters.channels rows roots).size
  let found := LiteralDetector.found graph parameters.buses parameters.bridge.target base
  let native := NativeContinuationConstruction.finish parameters width
    (base + (2 * parameters.channels + 1) * graph.nodeCount + graph.nodeCount) found
  let output := BasisOutputConstruction.literal width parameters.buses parameters.bridge.target
    graph.nodeCount base found (found + native.1.length) graph.roots.length
    (LiteralSourceConstruction.constructionSize graph) (SharedDetectorPrepared.rootBase graph)
  have table := BasisTableStorage.literal graph width rows roots 0 base
  have returned := BasisOutputStorage.literal width parameters.buses parameters.bridge.target
    graph.nodeCount base found (found + native.1.length) graph.roots.length
    (LiteralSourceConstruction.constructionSize graph) (SharedDetectorPrepared.rootBase graph)
  have redirected := Trace.redirect returned
  have finished := AssemblyStorage.native parameters width
    (base + (2 * parameters.channels + 1) * graph.nodeCount + graph.nodeCount) found
  have halted := fixed (Instruction.halt : Instruction width 8) (by trivial)
  have assembled := join (join (join table redirected) finished) halted
  have tableSize : (BasisTableConstruction.literal graph width rows roots 0 base).1.length =
      LiteralSourceConstruction.constructionSize graph := by
    rw [BasisTableConstruction.literal_image, Array.length_toList,
      LiteralSourceConstruction.constructionCode_size]
  have outputSize : output.1.length ≤ graph.roots.length * (154 + 18 * parameters.channels) +
      2 := by
    dsimp only [output]
    rw [BasisOutputConstruction.literal_image, LiteralOutputSearch.code_length]
    have stride := Nat.mul_le_mul_left graph.roots.length
      (LiteralOutputSearch.stride_bound parameters.buses parameters.bridge.target
          graph.nodeCount base)
    omega
  have nativeSize : native.1.length ≤ 34 * (selectedSize parameters).total + 1 := by
    dsimp only [native]
    rw [NativeContinuationConstruction.finish_image]
    exact BasisNativeFinish.code_bound parameters width _ _
  have size := graph.countedSize_eq
  have nodeBound := Nat.mul_le_mul_left (parameters.channels + 1)
    (by omega : graph.nodeCount ≤ graph.countedSize + 1)
  have rootBound := Nat.mul_le_mul_left (parameters.channels + 1)
    (by omega : graph.roots.length ≤ graph.countedSize + 1)
  dsimp only [ProperNativeConstruction.literal]
  exact .enlarge assembled (by
    dsimp only [output, native, base, found] at *
    simp only [List.length_append, List.length_map, LiteralSourceConstruction.constructionSize] at *
    nlinarith)

end Controller.Cost.ProperNativeStorage
