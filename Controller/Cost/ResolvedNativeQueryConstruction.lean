/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ResolvedNativeLayoutConstruction
import Controller.Cost.NativeQueryConstruction

/-! Complete native query image construction from the original typed source.
The source normalization profile is cached once. Native emission reuses the
selected source circuit; no assignment is computed while forming instructions. -/
namespace Controller.Cost.ResolvedNativeQueryConstruction

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution

def build (parameters : Parameters) (width entry next : Nat)
    (reference : Fin parameters.decoder.nodeCount) : List (Instruction width 8) × Nat :=
  let prepared := ResolvedNativeLayoutConstruction.build parameters.decoder parameters.buses
    parameters.bridge.target reference
  let data := prepared.1
  let formed := NativeQueryConstruction.build parameters width entry data.protectedEnd
    (parameters.channels + parameters.decoder.nodeCount) data.scratchEnd data.nativeEnd
      data.references next
  (formed.1, prepared.2 + formed.2 + 100)

theorem image (parameters : Parameters) (width entry next : Nat)
    (reference : Fin parameters.decoder.nodeCount) :
    (build parameters width entry next reference).1 =
      ResolvedNativeResident.code parameters parameters.decoder parameters.buses
        parameters.bridge.target reference width entry
        (ResolvedNativeLayoutConstruction.build parameters.decoder parameters.buses
          parameters.bridge.target reference).1.protectedEnd next := by
  simp only [build, NativeQueryConstruction.image,
    ResolvedNativeLayoutConstruction.scratch_image, ResolvedNativeLayoutConstruction.native_image
      (width := width),
    ResolvedNativeLayoutConstruction.references_value, ResolvedNativeResident.code]

theorem clock (parameters : Parameters) (width entry next : Nat)
    (reference : Fin parameters.decoder.nodeCount) :
    (build parameters width entry next reference).2 ≤
      500000 * (parameters.channels + 1) * (parameters.decoder.countedSize + 1) +
        30000 * ((selectedSize parameters).total + 1) := by
  let prepared := ResolvedNativeLayoutConstruction.build parameters.decoder parameters.buses
    parameters.bridge.target reference
  have layout := ResolvedNativeLayoutConstruction.clock parameters.decoder parameters.buses
    parameters.bridge.target reference
  have query := NativeQueryConstruction.clock parameters width entry prepared.1.protectedEnd
    (parameters.channels + parameters.decoder.nodeCount) prepared.1.scratchEnd prepared.1.nativeEnd
      prepared.1.references next
  have rows := ResolvedResident.rows_bound parameters.decoder ∅ parameters.buses
    parameters.bridge.target reference
  dsimp only [prepared] at query
  rw [ResolvedNativeLayoutConstruction.references_value] at query
  simp only [ResolvedResident.refs_length, ResolvedResident.refs_literals] at query
  change prepared.2 + _ + 100 ≤ _
  dsimp only [prepared] at *
  rw [ResolvedNativeLayoutConstruction.references_value]
  nlinarith

end Controller.Cost.ResolvedNativeQueryConstruction
