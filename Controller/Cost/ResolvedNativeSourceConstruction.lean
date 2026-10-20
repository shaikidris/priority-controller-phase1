module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ResolvedNativeQueryConstruction
public import Controller.Cost.ResolvedFrontConstruction

@[expose] public section


/-! The successful selector continuation is assembled from a charged source
front and the complete native query constructor. -/
namespace Controller.Cost.ResolvedNativeSourceConstruction

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestIndexedOperands

def build (parameters : Parameters) (width : Nat) (packet : Array (Word width)) (rows : List Row)
  (roots : List Nat)
    (reference : Fin parameters.decoder.nodeCount) (rootSlot entry sourceCount : Nat) : List
      (Instruction width 8) × Nat :=
  let front := ResolvedFrontConstruction.prepare width parameters.decoder packet rows roots
    parameters.buses
    parameters.bridge.target rootSlot entry sourceCount
  let native := ResolvedNativeQueryConstruction.build parameters width (entry + front.1.length) 0
    reference
  let image := front.1 ++ native.1
  (image, front.2 + native.2 + 16 * image.length + 100)

theorem image (parameters : Parameters) (width : Nat) (packet : Array (Word width)) (rows : List
  Row) (roots : List Nat)
    (matched : RowsMatch parameters.decoder rows) (reference : Fin parameters.decoder.nodeCount)
    (rootSlot entry sourceCount : Nat) :
    (build parameters width packet rows roots reference rootSlot entry sourceCount).1 =
      ResolvedNativeSource.code parameters width packet rows roots reference rootSlot entry
        sourceCount := by
  have front := ResolvedFrontConstruction.image width parameters.decoder packet rows roots matched
    parameters.buses
    parameters.bridge.target reference rootSlot entry sourceCount
  have cursor := ResolvedSourcePrepare.code_end (width := width) (entry := entry) (rootSlot :=
    rootSlot)
    (sourceCount := sourceCount) parameters.decoder packet rows roots parameters.buses
      parameters.bridge.target reference
  have solver : entry + (ResolvedFrontConstruction.prepare width parameters.decoder packet rows
    roots parameters.buses
      parameters.bridge.target rootSlot entry sourceCount).1.length =
      (ResolvedSourcePrepare.positions width parameters.decoder packet rows roots parameters.buses
        parameters.bridge.target reference rootSlot entry).solver := by rw [front, cursor]
  dsimp only [build]
  rw [solver]
  simp only [front, ResolvedNativeQueryConstruction.image,
    ResolvedNativeLayoutConstruction.keep_image (width := width), ResolvedNativeSource.code]

theorem clock (parameters : Parameters) (width : Nat) (packet : Array (Word width)) (rows : List
  Row) (roots : List Nat)
    (matched : RowsMatch parameters.decoder rows) (rootMatches : RootsMatch parameters.decoder
      roots)
    (reference : Fin parameters.decoder.nodeCount) (rootSlot entry sourceCount : Nat) :
    (build parameters width packet rows roots reference rootSlot entry sourceCount).2 ≤
      1000000 * (parameters.channels + 1) * (parameters.decoder.countedSize + 1) +
        40000 * ((selectedSize parameters).total + 1) := by
  have front := ResolvedFrontConstruction.clock width parameters.decoder packet rows roots matched
    rootMatches parameters.buses
    parameters.bridge.target reference rootSlot entry sourceCount
  have native := ResolvedNativeQueryConstruction.clock parameters width
    (entry + (ResolvedFrontConstruction.prepare width parameters.decoder packet rows roots
      parameters.buses
      parameters.bridge.target rootSlot entry sourceCount).1.length) 0 reference
  have length : (build parameters width packet rows roots reference rootSlot entry
    sourceCount).1.length ≤
      1200 * (parameters.decoder.countedSize + 1) + 34 * (selectedSize parameters).total := by
    rw [image parameters width packet rows roots matched reference rootSlot entry sourceCount]
    exact ResolvedNativeSource.code_bound parameters packet rows roots reference
  change _ + _ + 16 * (build parameters width packet rows roots reference rootSlot entry
    sourceCount).1.length + 100 ≤ _
  nlinarith

end Controller.Cost.ResolvedNativeSourceConstruction
