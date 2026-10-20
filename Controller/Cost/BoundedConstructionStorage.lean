/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.SelectorAssemblyStorage
import Controller.Cost.SupportCompleteStorage
import Controller.Cost.BoundedDetectorConstruction

/-! Full bounded-live-AND instruction construction, including cold preparation,
both search phases, provisional images, all relocations and the final image. -/
namespace Controller.Cost.BoundedConstructionStorage

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestIndexedOperands Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestClauseProgramConstruction (environment)
open Controller.Cost.AssemblyStorage

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
attribute [local irreducible] SupportColdConstruction.build SupportNativeConstruction.build
  ResolvedSearchConstruction.build BoundedDetectorConstruction.prepared
      BoundedDetectorConstruction.cold

theorem prepared (parameters : Parameters) (width : Nat) (rows : List Row) (roots : List Nat)
    (k : Nat) (matched : RowsMatch parameters.decoder rows)
    (rootMatches : RootsMatch parameters.decoder roots)
    (reference : Fin parameters.decoder.nodeCount) :
    Bounded (BoundedDetectorConstruction.prepared parameters width rows roots k reference).1
      (6000000000 * (parameters.decoder.countedSize + 1) +
        500000000 * ((selectedSize parameters).total + 1)) := by
  let packet := SupportCandidate.header width parameters.channels rows roots
    (fun _ : Fin parameters.decoder.nodeCount => false)
  let support := SupportNativeConstruction.build parameters width rows roots k
  let entry := 6 * roots.length + 2
  let root := entry + support.1.length
  let selector := ResolvedSearchConstruction.build parameters width rows roots reference
  have supportTrace := SupportCompleteStorage.support parameters width rows roots k matched
      rootMatches
  have left := relocate supportTrace entry
  have selectorTrace := SelectorAssemblyStorage.search parameters width rows roots matched
      rootMatches
    reference
  have right := relocate selectorTrace (root + 3)
  have scan := SupportAssemblyStorage.healthyScan width
    (UniformDAGRuntimeOutputs.rootBase packet rows) 5 entry roots.length
  have jump := join (constant (width := width) (registers := 8) 0 0)
    (branch (width := width) (registers := 8) 0 root)
  have setup := wordCode (width := width) (fun index => Fin.elim0 index)
    (ResolvedNativeFinish.setupCode.constructionRecipe width)
  have assembled := join (join (join (join scan jump) left) setup) right
  have supportSize : support.1.length ≤ 300 * (parameters.decoder.countedSize + 1) +
      34 * (selectedSize parameters).total := by
    dsimp only [support]
    rw [SupportNativeConstruction.image]
    exact SupportNativeSearch.code_bound parameters rows roots rootMatches
  have selectorSize : selector.1.length ≤ 2600 * (parameters.decoder.countedSize + 1) +
      34 * (selectedSize parameters).total + 2 := by
    dsimp only [selector]
    rw [ResolvedSearchConstruction.image parameters width rows roots matched]
    exact ResolvedNativeSearch.code_bound parameters rows roots reference matched rootMatches
  have scanSize : (SupportControllerConstruction.healthyScan width
      (UniformDAGRuntimeOutputs.rootBase packet rows) 5 entry roots.length).1.length =
      6 * roots.length := by
    rw [SupportControllerConstruction.healthyScan_image, SupportHealthyScan.code_length]
  have movedSize : (ProgramRelocationConstruction.build entry support.1).1.length =
      support.1.length := by
    rw [ProgramRelocationConstruction.build_image, ResidentSegment.code, List.length_map]
  have rootLength : roots.length = parameters.decoder.roots.length := by rw [rootMatches]; simp
  have size := parameters.decoder.countedSize_eq
  unfold BoundedDetectorConstruction.prepared
  dsimp only
  exact .enlarge assembled (by
    simp only [List.length_append, List.length_cons, List.length_nil, evaluate, List.length_map,
      ResolvedNativeFinish.setupCode.constructionRecipe_work]
    have setupLength : (ResolvedNativeFinish.setupCode.constructionRecipe width).length = 3 := rfl
    rw [setupLength]
    dsimp only [packet, support, selector, root, entry] at *
    omega)

theorem cold (parameters : Parameters) (width : Nat) (rows : List Row) (roots : List Nat)
    (k : Nat) (matched : RowsMatch parameters.decoder rows)
    (rootMatches : RootsMatch parameters.decoder roots)
    (reference : Fin parameters.decoder.nodeCount) :
    Bounded (BoundedDetectorConstruction.cold parameters width rows roots k reference).1
      (7000000000 * (parameters.decoder.countedSize + 1) +
        600000000 * ((selectedSize parameters).total + 1)) := by
  let front := SupportColdConstruction.build width parameters.decoder rows roots
  let driver := BoundedDetectorConstruction.prepared parameters width rows roots k reference
  have first := SupportCompleteStorage.cold width parameters.decoder rows roots matched rootMatches
  have driverTrace := prepared parameters width rows roots k matched rootMatches reference
  have moved := relocate driverTrace front.1.length
  have assembled := join first moved
  have frontSize : front.1.length ≤ 400 * (parameters.decoder.countedSize + 1) := by
    dsimp only [front]
    rw [SupportColdConstruction.image]
    exact SupportColdPrepare.code_bound parameters.decoder rows roots matched rootMatches
  have driverSize : driver.1.length ≤ 3000 * (parameters.decoder.countedSize + 1) +
      68 * (selectedSize parameters).total := by
    dsimp only [driver]
    rw [BoundedDetectorConstruction.prepared_image parameters width rows roots k matched]
    exact BoundedNativePrepared.code_bound parameters rows roots k reference matched rootMatches
  unfold BoundedDetectorConstruction.cold
  dsimp only
  exact .enlarge assembled (by
    dsimp only [front, driver] at *
    omega)

theorem complete (parameters : Parameters) (width k : Nat) :
    Bounded (BoundedDetectorConstruction.build parameters width k).1
      (10000000000 * (parameters.decoder.countedSize + 1) +
        1000000000 * ((selectedSize parameters).total + 1)) := by
  unfold BoundedDetectorConstruction.build
  split
  · split
    · rename_i nonempty
      exact .enlarge
        (cold parameters width (UniformDAGOutputs.rowsOfGraph parameters.decoder)
          (parameters.decoder.roots.map Fin.val) k
          (UniformDAGOutputs.rowsOfGraph_match parameters.decoder) rfl ⟨0, nonempty⟩) (by omega)
    · exact .enlarge (join (constant 4 0) (fixed .halt (by trivial))) (by
        simp only [List.length_cons, List.length_nil]
        omega)
  · exact .enlarge (join (constant 4 0) (fixed .halt (by trivial))) (by
      simp only [List.length_cons, List.length_nil]
      omega)

end Controller.Cost.BoundedConstructionStorage
