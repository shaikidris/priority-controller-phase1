/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ProperNativeStorage
import Controller.Cost.BoundedConstructionStorage
import Controller.Cost.ConstructedExtensionsComplete

/-! Storage contracts for complete extension constructors. Assembly traces
charge the actual instruction images. Source validation/cache buffers and the
final array copy are retained in addition to those assembly peaks. -/
namespace Controller.Cost.ExtensionConstructionStorage

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestIndexedOperands Controller.Cost.AssemblyStorage
open Controller.Extensions.ProperBasisDetector

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
attribute [local irreducible] BoundedDetectorConstruction.build ProperNativeConstruction.monotone
  ProperNativeConstruction.literal

structure Source (graph : DAG n) (rows : List Row) where
  itemPeak : Nat
  cachePeak : Nat
  items : ForestSourcePreparationStorage.ItemsTrace n 0 rows itemPeak
  cache : ForestSourcePreparationStorage.CacheTrace rows ForestCompilerOffsets.initial
    (ForestCompilerOffsets.run rows ForestCompilerOffsets.initial) cachePeak

def sourceWords (graph : DAG n) (rows : List Row) (roots : List Nat)
    (source : Source graph rows) :=
  source.itemPeak + source.cachePeak +
    1024 * (n + rows.length + (rowChildren rows).length + (rowGuards rows).length +
        roots.length + 1)

theorem source (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots) :
    ∃ certificate : Source graph rows,
      sourceWords graph rows roots certificate ≤ 10000 * (graph.countedSize + 1) := by
  obtain ⟨itemPeak, items, itemBound⟩ := ForestSourcePreparationStorage.items_space n 0 rows
  obtain ⟨cachePeak, cache, cacheBound⟩ := ForestSourcePreparationStorage.cache_space rows
    ForestCompilerOffsets.initial
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have rootLength : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have size := graph.countedSize_eq
  refine ⟨⟨itemPeak, cachePeak, items, cache⟩, ?_⟩
  simp only [sourceWords]
  simp only [ForestSourcePreparationStorage.cacheWords, ForestCompilerOffsets.initial,
    Array.size_empty, matched.length_eq, children, guards, rootLength] at *
  omega

theorem properAssembly (parameters : Parameters) (basis : GateBasis.Basis)
    (rows : List Row) (roots : List Nat) :
    let built := ProperDetectorConstruction.build parameters basis rows roots
    Trace built.1.width built.1.program.toList
      (10000000000 * (parameters.channels + 1) * (parameters.decoder.countedSize + 1) +
        1000000000 * ((selectedSize parameters).total + 1)) := by
  unfold ProperDetectorConstruction.build
  split
  · cases chosen : ProperBasisDetector.select basis with
    | guarded =>
        dsimp only [ProperDetectorConstruction.constructKind]
        exact .enlarge (BoundedConstructionStorage.complete parameters _ 0) (by nlinarith)
    | monotone =>
        dsimp only [ProperDetectorConstruction.constructKind]
        exact .enlarge (ProperNativeStorage.monotone parameters parameters.decoder _ rows roots)
          (by nlinarith)
    | literal =>
        dsimp only [ProperDetectorConstruction.constructKind]
        exact .enlarge (ProperNativeStorage.literal parameters parameters.decoder _ rows roots)
          (by nlinarith)
  · dsimp only [ProperBasisComplete.disabled]
    exact .enlarge (fixed (Instruction.halt : Instruction 4 8) (by trivial)) (by nlinarith)

structure Certificate (width : Nat) (graph : DAG n) (rows : List Row)
    (code : List (Instruction width 8)) where
  peak : Nat
  assembled : Trace width code peak
  source : Source graph rows

def buffers (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (code : List (Instruction width 8)) (certificate : Certificate width graph rows code) :=
  certificate.peak + sourceWords graph rows roots certificate.source + 1024 * (code.length + 1)

theorem bounded (parameters : Parameters) (width k : Nat) :
    let rows := UniformDAGOutputs.rowsOfGraph parameters.decoder
    let roots := parameters.decoder.roots.map Fin.val
    let code := (BoundedDetectorConstruction.build parameters width k).1
    ∃ certificate : Certificate width parameters.decoder rows code,
      buffers width parameters.decoder rows roots code certificate ≤
        20000000000 * (parameters.decoder.countedSize + 1) +
        2000000000 * ((selectedSize parameters).total + 1) := by
  let rows := UniformDAGOutputs.rowsOfGraph parameters.decoder
  let roots := parameters.decoder.roots.map Fin.val
  obtain ⟨source, sourceBound⟩ := source parameters.decoder rows roots
    (UniformDAGOutputs.rowsOfGraph_match parameters.decoder) rfl
  have assembly := BoundedConstructionStorage.complete parameters width k
  have codeBound : (BoundedDetectorConstruction.build parameters width k).1.length ≤
      3400 * (parameters.decoder.countedSize + 1) + 68 * (selectedSize parameters).total := by
    rw [BoundedDetectorConstruction.image]
    exact BoundedNativeDetector.code_bound (wordWidth := width) parameters k
  dsimp only
  refine ⟨⟨_, assembly, source⟩, ?_⟩
  simp only [buffers]
  dsimp only [rows, roots] at *
  omega

theorem proper (parameters : Parameters) (raw : parameters.layout = .raw)
    (basis : GateBasis.Basis) (uses : GateBasis.Uses parameters.decoder basis)
    (proper : basis ≠ GateBasis.full) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch parameters.decoder rows)
    (heads : UniformDAGSource.HeadsMatch parameters.decoder rows matched)
    (rootMatches : RootsMatch parameters.decoder roots) :
    let built := ProperDetectorConstruction.build parameters basis rows roots
    ∃ certificate : Certificate built.1.width parameters.decoder rows built.1.program.toList,
      buffers built.1.width parameters.decoder rows roots built.1.program.toList certificate ≤
        20000000000 * (parameters.channels + 1) * (parameters.decoder.countedSize + 1) +
        2000000000 * ((selectedSize parameters).total + 1) := by
  obtain ⟨source, sourceBound⟩ := source parameters.decoder rows roots matched rootMatches
  have assembly := properAssembly parameters basis rows roots
  obtain ⟨final, ticks, peak, execution, halted, time, space, accepts, checked⟩ :=
    ConstructedExtensionsComplete.proper_execution parameters raw basis uses proper rows roots
      matched heads rootMatches
  simp only [programWords] at space
  dsimp only
  refine ⟨⟨_, assembly, source⟩, ?_⟩
  simp only [buffers, Array.length_toList]
  nlinarith

end Controller.Cost.ExtensionConstructionStorage
