module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ResolvedSearchConstruction
public import Controller.Cost.SupportNativeConstruction
public import Controller.Cost.SupportColdConstruction

@[expose] public section


/-! Complete bounded-live-AND detector instruction construction. Both search
phases, cold input preparation and relocation belong to this constructor. -/
namespace Controller.Cost.BoundedDetectorConstruction

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestIndexedOperands Controller.Cost.WordConstructionRecipe

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

derive_extension_recipe ResolvedNativeFinish.setupCode

attribute [local irreducible] SupportColdConstruction.build SupportNativeConstruction.build
  ResolvedSearchConstruction.build

def prepared (parameters : Parameters) (width : Nat) (rows : List Row) (roots : List Nat) (k : Nat)
    (reference : Fin parameters.decoder.nodeCount) : List (Instruction width 8) × Nat :=
  let packet := SupportCandidate.header width parameters.channels rows roots (fun _ : Fin
    parameters.decoder.nodeCount => false)
  let support := SupportNativeConstruction.build parameters width rows roots k
  let entry := 6 * roots.length + 2
  let root := entry + support.1.length
  let scan := SupportControllerConstruction.healthyScan width (UniformDAGRuntimeOutputs.rootBase
    packet rows) 5 entry roots.length
  let relocatedSupport := ProgramRelocationConstruction.build entry support.1
  let selector := ResolvedSearchConstruction.build parameters width rows roots reference
  let relocatedSelector := ProgramRelocationConstruction.build (root + 3) selector.1
  let setup := evaluate (fun index => Fin.elim0 index)
    (ResolvedNativeFinish.setupCode.constructionRecipe width)
  let image := scan.1 ++ [.constant 0 (word width 0), .branchZero 0 (word width root)] ++
    relocatedSupport.1 ++ setup ++ relocatedSelector.1
  (image, support.2 + scan.2 + relocatedSupport.2 + selector.2 + relocatedSelector.2 +
    16 * image.length + 1000 * (parameters.decoder.countedSize + 1))

theorem prepared_image (parameters : Parameters) (width : Nat) (rows : List Row) (roots : List Nat)
  (k : Nat)
    (matched : RowsMatch parameters.decoder rows) (reference : Fin parameters.decoder.nodeCount) :
    (prepared parameters width rows roots k reference).1 = BoundedNativePrepared.code parameters
      width rows roots k reference := by
  have setup : evaluate (fun index => Fin.elim0 index)
    (ResolvedNativeFinish.setupCode.constructionRecipe width) =
      ResolvedNativeFinish.setupCode width := ResolvedNativeFinish.setupCode.constructionRecipe_eq
        width
  simp only [prepared, SupportNativeConstruction.image,
    SupportControllerConstruction.healthyScan_image,
    ResolvedSearchConstruction.image parameters width rows roots matched,
      ProgramRelocationConstruction.build_image,
    setup, BoundedNativePrepared.code, BoundedNativePrepared.rootEntry,
      BoundedNativePrepared.supportEntry,
    ResolvedNativeFinish.code, EnumerationDriverCode.jump, List.append_assoc]

theorem prepared_clock (parameters : Parameters) (width : Nat) (rows : List Row) (roots : List Nat)
  (k : Nat)
    (matched : RowsMatch parameters.decoder rows) (rootMatches : RootsMatch parameters.decoder
      roots)
    (reference : Fin parameters.decoder.nodeCount) :
    (prepared parameters width rows roots k reference).2 ≤
      5000000 * (parameters.channels + 1) * (parameters.decoder.countedSize + 1) +
        100000 * ((selectedSize parameters).total + 1) := by
  let packet := SupportCandidate.header width parameters.channels rows roots (fun _ : Fin
    parameters.decoder.nodeCount => false)
  let support := SupportNativeConstruction.build parameters width rows roots k
  let entry := 6 * roots.length + 2
  let root := entry + support.1.length
  let selector := ResolvedSearchConstruction.build parameters width rows roots reference
  have supportClock := SupportNativeConstruction.clock parameters width rows roots k matched
    rootMatches
  have selectorClock := ResolvedSearchConstruction.clock parameters width rows roots matched
    rootMatches reference
  have scan := SupportControllerConstruction.healthyScan_clock width
    (UniformDAGRuntimeOutputs.rootBase packet rows) 5 entry roots.length
  have left := ProgramRelocationConstruction.build_clock entry support.1
  have right := ProgramRelocationConstruction.build_clock (root + 3) selector.1
  have supportSize : support.1.length ≤ 300 * (parameters.decoder.countedSize + 1) + 34 *
    (selectedSize parameters).total := by
    dsimp only [support]
    rw [SupportNativeConstruction.image]
    exact SupportNativeSearch.code_bound parameters rows roots rootMatches
  have selectorSize : selector.1.length ≤ 2600 * (parameters.decoder.countedSize + 1) + 34 *
    (selectedSize parameters).total + 2 := by
    dsimp only [selector]
    rw [ResolvedSearchConstruction.image parameters width rows roots matched reference]
    exact ResolvedNativeSearch.code_bound parameters rows roots reference matched rootMatches
  have length : (prepared parameters width rows roots k reference).1.length ≤
      3000 * (parameters.decoder.countedSize + 1) + 68 * (selectedSize parameters).total := by
    rw [prepared_image parameters width rows roots k matched reference]
    exact BoundedNativePrepared.code_bound parameters rows roots k reference matched rootMatches
  have rootLength : roots.length = parameters.decoder.roots.length := by rw [rootMatches]; simp
  have size := parameters.decoder.countedSize_eq
  change _ + _ + _ + _ + _ + 16 * (prepared parameters width rows roots k reference).1.length +
    1000 * (parameters.decoder.countedSize + 1) ≤ _
  dsimp only [support, selector, packet, root, entry] at *
  simp only [rootLength] at scan left right ⊢
  nlinarith

attribute [local irreducible] prepared

def cold (parameters : Parameters) (width : Nat) (rows : List Row) (roots : List Nat) (k : Nat)
    (reference : Fin parameters.decoder.nodeCount) : List (Instruction width 8) × Nat :=
  let front := SupportColdConstruction.build width parameters.decoder rows roots
  let driver := prepared parameters width rows roots k reference
  let relocated := ProgramRelocationConstruction.build front.1.length driver.1
  let image := front.1 ++ relocated.1
  (image, front.2 + driver.2 + relocated.2 + 16 * image.length + 1000)

theorem cold_image (parameters : Parameters) (width : Nat) (rows : List Row) (roots : List Nat) (k :
  Nat)
    (matched : RowsMatch parameters.decoder rows) (reference : Fin parameters.decoder.nodeCount) :
    (cold parameters width rows roots k reference).1 = BoundedNativeCold.code parameters width rows
      roots k reference := by
  simp only [cold, SupportColdConstruction.image, prepared_image parameters width rows roots k
    matched,
    ProgramRelocationConstruction.build_image, BoundedNativeCold.code]

theorem cold_clock (parameters : Parameters) (width : Nat) (rows : List Row) (roots : List Nat) (k :
  Nat)
    (matched : RowsMatch parameters.decoder rows) (rootMatches : RootsMatch parameters.decoder
      roots)
    (reference : Fin parameters.decoder.nodeCount) :
    (cold parameters width rows roots k reference).2 ≤
      6000000 * (parameters.channels + 1) * (parameters.decoder.countedSize + 1) +
        120000 * ((selectedSize parameters).total + 1) := by
  let front := SupportColdConstruction.build width parameters.decoder rows roots
  let driver := prepared parameters width rows roots k reference
  have frontClock := SupportColdConstruction.clock width parameters.decoder rows roots matched
    rootMatches
  have driverClock := prepared_clock parameters width rows roots k matched rootMatches reference
  have relocated := ProgramRelocationConstruction.build_clock front.1.length driver.1
  have driverSize : driver.1.length ≤ 3000 * (parameters.decoder.countedSize + 1) + 68 *
    (selectedSize parameters).total := by
    dsimp only [driver]
    rw [prepared_image parameters width rows roots k matched reference]
    exact BoundedNativePrepared.code_bound parameters rows roots k reference matched rootMatches
  have length : (cold parameters width rows roots k reference).1.length ≤
      3400 * (parameters.decoder.countedSize + 1) + 68 * (selectedSize parameters).total := by
    rw [cold_image parameters width rows roots k matched reference]
    exact BoundedNativeCold.code_bound parameters rows roots k reference matched rootMatches
  change _ + _ + _ + 16 * (cold parameters width rows roots k reference).1.length + 1000 ≤ _
  dsimp only [front, driver] at *
  nlinarith

attribute [local irreducible] cold

def build (parameters : Parameters) (width k : Nat) : List (Instruction width 8) × Nat :=
  if parameters.drive then
    if nonempty : 0 < parameters.decoder.nodeCount then
      let formed := cold parameters width (UniformDAGOutputs.rowsOfGraph parameters.decoder)
        (parameters.decoder.roots.map Fin.val) k ⟨0, nonempty⟩
      (formed.1, formed.2 + 1000 * (parameters.decoder.countedSize + 1))
    else ([.constant 4 (word width 0), .halt], 32)
  else ([.constant 4 (word width 0), .halt], 32)

theorem image (parameters : Parameters) (width k : Nat) :
    (build parameters width k).1 = BoundedNativeDetector.code parameters width k := by
  unfold build BoundedNativeDetector.code
  split
  · split
    · exact cold_image parameters width _ _ k (UniformDAGOutputs.rowsOfGraph_match
      parameters.decoder) _
    · rfl
  · rfl

theorem clock (parameters : Parameters) (width k : Nat) :
    (build parameters width k).2 ≤
      7000000 * (parameters.channels + 1) * (parameters.decoder.countedSize + 1) +
        150000 * ((selectedSize parameters).total + 1) := by
  unfold build
  split
  · split
    · rename_i nonempty
      have formed := cold_clock parameters width (UniformDAGOutputs.rowsOfGraph parameters.decoder)
        (parameters.decoder.roots.map Fin.val) k (UniformDAGOutputs.rowsOfGraph_match
          parameters.decoder) rfl ⟨0, nonempty⟩
      dsimp only
      nlinarith
    · dsimp only; nlinarith
  · dsimp only; nlinarith

end Controller.Cost.BoundedDetectorConstruction
