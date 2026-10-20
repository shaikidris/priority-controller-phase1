/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.BasisTableConstruction
import Controller.Cost.BasisOutputConstruction
import Controller.Cost.NativeContinuationConstruction

/-! Proper-basis native detector image assembly. Matrix sizes are arithmetic
source dimensions, and the source native circuit is compiled only once. -/
namespace Controller.Cost.ProperNativeConstruction

set_option maxHeartbeats 2000000

attribute [local irreducible] BasisTableConstruction.monotone BasisTableConstruction.literal
  BasisOutputConstruction.monotone BasisOutputConstruction.literal
    NativeContinuationConstruction.finish

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestIndexedOperands

def monotone (parameters : Parameters) (graph : DAG parameters.channels) (width : Nat) (rows : List
  Row) (roots : List Nat) : List (Instruction width 8) × Nat :=
  let table := BasisTableConstruction.monotone graph width rows roots 0
  let base := (LiteralDetector.sourceHeap width parameters.channels rows roots).size
  let found := MonotoneDetector.found graph parameters.buses
  let native := NativeContinuationConstruction.finish parameters width (base + (parameters.channels
    + 1) * graph.nodeCount) found
  let output := BasisOutputConstruction.monotone width parameters.buses parameters.bridge.target
    graph.nodeCount base found
    (found + native.1.length) graph.roots.length (MonotoneDetector.constructionSize graph)
      (SharedDetectorPrepared.rootBase graph)
  let image := table.1 ++ output.1.map WitnessStack.redirect ++ native.1 ++ [.halt]
  (image, table.2 + output.2 + native.2 + 16 * image.length + 1000 * (graph.countedSize + 1))

theorem monotone_image (parameters : Parameters) (graph : DAG parameters.channels) (width : Nat)
  (rows : List Row) (roots : List Nat) :
    (monotone parameters graph width rows roots).1 = MonotoneNativeDetector.code parameters graph
      width rows roots := by
  simp only [monotone, BasisTableConstruction.monotone_image,
    BasisOutputConstruction.monotone_image,
    NativeContinuationConstruction.finish_image, MonotoneNativeDetector.code,
      MonotoneNativeDetector.absent,
    MonotoneNativeDetector.found, MonotoneNativeDetector.nativeBase,
      MonotoneTableConstruction.matrix_length, List.append_assoc]

def literal (parameters : Parameters) (graph : DAG parameters.channels) (width : Nat) (rows : List
  Row) (roots : List Nat) : List (Instruction width 8) × Nat :=
  let base := (LiteralDetector.sourceHeap width parameters.channels rows roots).size
  let table := BasisTableConstruction.literal graph width rows roots 0 base
  let found := LiteralDetector.found graph parameters.buses parameters.bridge.target base
  let native := NativeContinuationConstruction.finish parameters width
    (base + (2 * parameters.channels + 1) * graph.nodeCount + graph.nodeCount) found
  let output := BasisOutputConstruction.literal width parameters.buses parameters.bridge.target
    graph.nodeCount base found
    (found + native.1.length) graph.roots.length (LiteralSourceConstruction.constructionSize graph)
      (SharedDetectorPrepared.rootBase graph)
  let image := table.1 ++ output.1.map WitnessStack.redirect ++ native.1 ++ [.halt]
  (image, table.2 + output.2 + native.2 + 16 * image.length + 1000 * (graph.countedSize + 1))

theorem literal_image (parameters : Parameters) (graph : DAG parameters.channels) (width : Nat)
  (rows : List Row) (roots : List Nat) :
    (literal parameters graph width rows roots).1 = LiteralNativeDetector.code parameters graph
      width rows roots := by
  simp only [literal, BasisTableConstruction.literal_image, BasisOutputConstruction.literal_image,
    NativeContinuationConstruction.finish_image, LiteralNativeDetector.code,
      LiteralNativeDetector.absent,
    LiteralNativeDetector.found, LiteralNativeDetector.nativeBase,
      LiteralSourceConstruction.matrix_length, List.append_assoc]

theorem monotone_clock (parameters : Parameters) (graph : DAG parameters.channels) (width : Nat)
  (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots) :
    (monotone parameters graph width rows roots).2 ≤
      5000000 * (parameters.channels + graph.roots.length + 1) * (graph.countedSize + 1) +
        10000 * ((selectedSize parameters).total + 1) := by
  let base := (LiteralDetector.sourceHeap width parameters.channels rows roots).size
  let found := MonotoneDetector.found graph parameters.buses
  let native := NativeContinuationConstruction.finish parameters width (base + (parameters.channels
    + 1) * graph.nodeCount) found
  let output := BasisOutputConstruction.monotone width parameters.buses parameters.bridge.target
    graph.nodeCount base found
    (found + native.1.length) graph.roots.length (MonotoneDetector.constructionSize graph)
      (SharedDetectorPrepared.rootBase graph)
  have table := BasisTableConstruction.monotone_clock graph width rows roots 0 matched rootMatches
  have out := BasisOutputConstruction.monotone_clock width parameters.buses parameters.bridge.target
    graph.nodeCount base found
    (found + native.1.length) graph.roots.length (MonotoneDetector.constructionSize graph)
      (SharedDetectorPrepared.rootBase graph)
  have lift := NativeContinuationConstruction.finish_clock parameters width (base +
    (parameters.channels + 1) * graph.nodeCount) found
  have liftSize : native.1.length ≤ 34 * (selectedSize parameters).total + 1 := by
    dsimp only [native]
    rw [NativeContinuationConstruction.finish_image]
    exact BasisNativeFinish.code_bound parameters width _ _
  have outputSize : output.1.length ≤ graph.roots.length * (39 + 18 * parameters.channels) + 2 := by
    dsimp only [output]
    rw [BasisOutputConstruction.monotone_image, MonotoneOutputSearch.code_length]
    have stride := Nat.mul_le_mul_left graph.roots.length (MonotoneOutputSearch.stride_bound
      parameters.buses parameters.channels)
    omega
  have tableSize : (BasisTableConstruction.monotone graph width rows roots 0).1.length =
      162 * parameters.channels + 143 + 2 * (parameters.channels + 1) * graph.nodeCount := by
    rw [BasisTableConstruction.monotone_image]
    simp only [Array.length_toList, MonotoneTableConstruction.code_size]
  have length : (monotone parameters graph width rows roots).1.length =
      (BasisTableConstruction.monotone graph width rows roots 0).1.length + output.1.length +
        native.1.length + 1 := by
    simp only [monotone, output, native, base, found, List.length_append, List.length_map,
      List.length_cons, List.length_nil, Nat.zero_add]
  have size := graph.countedSize_eq
  have matrix := Nat.mul_le_mul_left (parameters.channels + 1) (by omega : graph.nodeCount ≤
    graph.countedSize + 1)
  have rootsChannels := Nat.mul_le_mul_left graph.roots.length (by omega : parameters.channels ≤
    graph.countedSize + 1)
  change _ + _ + _ + 16 * (monotone parameters graph width rows roots).1.length + 1000 *
    (graph.countedSize + 1) ≤ _
  rw [length, tableSize]
  dsimp only [base, found, native, output] at *
  nlinarith

theorem literal_clock (parameters : Parameters) (graph : DAG parameters.channels) (width : Nat)
  (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots) :
    (literal parameters graph width rows roots).2 ≤
      5000000 * (parameters.channels + graph.roots.length + 1) * (graph.countedSize + 1) +
        10000 * ((selectedSize parameters).total + 1) := by
  let base := (LiteralDetector.sourceHeap width parameters.channels rows roots).size
  let found := LiteralDetector.found graph parameters.buses parameters.bridge.target base
  let native := NativeContinuationConstruction.finish parameters width
    (base + (2 * parameters.channels + 1) * graph.nodeCount + graph.nodeCount) found
  let output := BasisOutputConstruction.literal width parameters.buses parameters.bridge.target
    graph.nodeCount base found
    (found + native.1.length) graph.roots.length (LiteralSourceConstruction.constructionSize graph)
      (SharedDetectorPrepared.rootBase graph)
  have table := BasisTableConstruction.literal_clock graph width rows roots 0 base matched
    rootMatches
  have out := BasisOutputConstruction.literal_clock width parameters.buses parameters.bridge.target
    graph.nodeCount base found
    (found + native.1.length) graph.roots.length (LiteralSourceConstruction.constructionSize graph)
      (SharedDetectorPrepared.rootBase graph)
  have lift := NativeContinuationConstruction.finish_clock parameters width
    (base + (2 * parameters.channels + 1) * graph.nodeCount + graph.nodeCount) found
  have liftSize : native.1.length ≤ 34 * (selectedSize parameters).total + 1 := by
    dsimp only [native]
    rw [NativeContinuationConstruction.finish_image]
    exact BasisNativeFinish.code_bound parameters width _ _
  have outputSize : output.1.length ≤ graph.roots.length * (154 + 18 * parameters.channels) + 2 :=
    by
    dsimp only [output]
    rw [BasisOutputConstruction.literal_image, LiteralOutputSearch.code_length]
    have stride := Nat.mul_le_mul_left graph.roots.length (LiteralOutputSearch.stride_bound
      parameters.buses parameters.bridge.target graph.nodeCount base)
    omega
  have tableSize : (BasisTableConstruction.literal graph width rows roots 0 base).1.length =
      LiteralSourceConstruction.constructionSize graph := by
    rw [BasisTableConstruction.literal_image]
    simp only [Array.length_toList, LiteralSourceConstruction.constructionCode_size]
  have length : (literal parameters graph width rows roots).1.length =
      (BasisTableConstruction.literal graph width rows roots 0 base).1.length + output.1.length +
        native.1.length + 1 := by
    simp only [literal, output, native, base, found, List.length_append, List.length_map,
      List.length_cons, List.length_nil, Nat.zero_add]
  have size := graph.countedSize_eq
  have matrix := Nat.mul_le_mul_left (parameters.channels + 1) (by omega : graph.nodeCount ≤
    graph.countedSize + 1)
  have rootsChannels := Nat.mul_le_mul_left graph.roots.length (by omega : parameters.channels ≤
    graph.countedSize + 1)
  change _ + _ + _ + 16 * (literal parameters graph width rows roots).1.length + 1000 *
    (graph.countedSize + 1) ≤ _
  rw [length, tableSize]
  simp only [LiteralSourceConstruction.constructionSize] at *
  dsimp only [base, found, native, output] at *
  nlinarith

end Controller.Cost.ProperNativeConstruction
