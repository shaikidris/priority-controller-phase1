/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ResolvedBodyConstruction
import Controller.Cost.ResolvedNativeSourceConstruction

/-! One source-driven healthy-one image shares the selector body and the
native emission continuation. Provisional layout, relocation and concatenation
are included in its construction clock. -/
namespace Controller.Cost.ResolvedSearchConstruction

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestIndexedOperands

def build (parameters : Parameters) (width : Nat) (rows : List Row) (roots : List Nat)
    (reference : Fin parameters.decoder.nodeCount) : List (Instruction width 8) × Nat :=
  let graph := parameters.decoder
  let packet := ResolvedRootSource.packet width parameters.channels rows roots (fun _ : Fin
    graph.nodeCount => false) 0
  let sourceCount := (cacheHeap width packet rows roots).size + graph.liveAndCount
  let provisional := ResolvedBodyConstruction.build width graph rows roots parameters.buses
    parameters.bridge.target reference 0 0
  let start := provisional.1.length
  let native := ResolvedNativeSourceConstruction.build parameters width packet rows roots reference
    4 0 sourceCount
  let body := ResolvedBodyConstruction.build width graph rows roots parameters.buses
    parameters.bridge.target reference start (start + native.1.length)
  let relocated := ProgramRelocationConstruction.build start native.1
  let image := body.1 ++ relocated.1 ++ [.constant 4 (word width 0), .halt]
  (image, provisional.2 + native.2 + body.2 + relocated.2 + 16 * image.length + 1000 *
    (graph.countedSize + 1))

theorem image (parameters : Parameters) (width : Nat) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch parameters.decoder rows) (reference : Fin parameters.decoder.nodeCount) :
    (build parameters width rows roots reference).1 = ResolvedNativeSearch.code parameters width
      rows roots reference := by
  simp only [build, ResolvedBodyConstruction.image width parameters.decoder rows roots matched,
    ResolvedNativeSourceConstruction.image parameters width _ rows roots matched,
    ProgramRelocationConstruction.build_image, ResolvedNativeSearch.code,
      ResolvedNativeSearch.bodyLength,
    ResolvedNativeSearch.nativeCode, List.append_assoc]

theorem clock (parameters : Parameters) (width : Nat) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch parameters.decoder rows) (rootMatches : RootsMatch parameters.decoder
      roots)
    (reference : Fin parameters.decoder.nodeCount) :
    (build parameters width rows roots reference).2 ≤
      4000000 * (parameters.channels + 1) * (parameters.decoder.countedSize + 1) +
        50000 * ((selectedSize parameters).total + 1) := by
  let graph := parameters.decoder
  let packet := ResolvedRootSource.packet width parameters.channels rows roots (fun _ : Fin
    graph.nodeCount => false) 0
  let sourceCount := (cacheHeap width packet rows roots).size + graph.liveAndCount
  let provisional := ResolvedBodyConstruction.build width graph rows roots parameters.buses
    parameters.bridge.target reference 0 0
  let start := provisional.1.length
  let native := ResolvedNativeSourceConstruction.build parameters width packet rows roots reference
    4 0 sourceCount
  have first := ResolvedBodyConstruction.clock width graph rows roots matched rootMatches
    parameters.buses parameters.bridge.target reference 0 0
  have nativeClock := ResolvedNativeSourceConstruction.clock parameters width packet rows roots
    matched rootMatches reference 4 0 sourceCount
  have body := ResolvedBodyConstruction.clock width graph rows roots matched rootMatches
    parameters.buses parameters.bridge.target reference start (start + native.1.length)
  have relocated := ProgramRelocationConstruction.build_clock start native.1
  have nativeLength : native.1.length ≤ 1200 * (graph.countedSize + 1) + 34 * (selectedSize
    parameters).total := by
    dsimp only [native]
    rw [ResolvedNativeSourceConstruction.image parameters width packet rows roots matched reference
      4 0 sourceCount]
    exact ResolvedNativeSource.code_bound parameters packet rows roots reference
  have length : (build parameters width rows roots reference).1.length ≤
      2600 * (graph.countedSize + 1) + 34 * (selectedSize parameters).total + 2 := by
    rw [image parameters width rows roots matched reference]
    exact ResolvedNativeSearch.code_bound parameters rows roots reference matched rootMatches
  change _ + _ + _ + _ + 16 * (build parameters width rows roots reference).1.length + 1000 *
    (graph.countedSize + 1) ≤ _
  dsimp only [provisional, start, native, sourceCount, graph, packet] at *
  nlinarith

end Controller.Cost.ResolvedSearchConstruction
