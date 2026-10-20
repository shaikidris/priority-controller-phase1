/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.NativeContinuationConstruction
import Controller.Cost.SupportTraversalConstruction
import Controller.Cost.StackPacketConstruction

/-! The healthy-zero support phase shares one native continuation, formed
from explicit source counts and the selected native source circuit. -/
namespace Controller.Cost.SupportNativeConstruction

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestIndexedOperands

def continuation (parameters : Parameters) (width base entry : Nat) : List (Instruction width 8) ×
  Nat :=
  let first := SupportCandidateConstruction.prepare width parameters.buses (base +
    parameters.bridge.target.val)
  let copy := entry + first.length
  let copied := StackPacketConstruction.copy width copy (copy + 10) base parameters.channels
  let native := NativeContinuationConstruction.finish parameters width (base + parameters.channels)
    (copy + 11)
  let image := first ++ copied ++ [.constant 4 (word width 1)] ++ native.1
  (image, native.2 + 16 * image.length + 2000)

theorem continuation_image (parameters : Parameters) (width base entry : Nat) :
    (continuation parameters width base entry).1 = SupportNativeSource.code parameters width base
      entry := by
  simp only [continuation, SupportCandidateConstruction.prepare_image,
    StackPacketConstruction.copy_image,
    NativeContinuationConstruction.finish_image, SupportNativeSource.code,
      SupportNativeSource.copyEntry,
    SupportNativeFinish.code, Nat.add_assoc, List.append_assoc]

def build (parameters : Parameters) (width : Nat) (rows : List Row) (roots : List Nat) (k : Nat) :
  List (Instruction width 8) × Nat :=
  let base := (SupportNativeSearch.source parameters width rows roots).size
  let native := continuation parameters width base 0
  let start := SupportNativeSearch.start parameters roots
  let body := SupportTraversalConstruction.build width parameters.decoder rows roots k
    parameters.buses parameters.bridge.target start (start + native.1.length)
  let relocated := ProgramRelocationConstruction.build start native.1
  let image := body.1 ++ relocated.1
  (image, native.2 + body.2 + relocated.2 + 16 * image.length + 1000 *
    (parameters.decoder.countedSize + 1))

theorem image (parameters : Parameters) (width : Nat) (rows : List Row) (roots : List Nat) (k : Nat)
  :
    (build parameters width rows roots k).1 = SupportNativeSearch.code parameters width rows roots k
      := by
  simp only [build, continuation_image, SupportTraversalConstruction.image width parameters.decoder
    rows roots (fun _ => false),
    ProgramRelocationConstruction.build_image, SupportNativeSearch.code,
      SupportNativeSearch.nativeCode]

theorem continuation_clock (parameters : Parameters) (width base entry : Nat) :
    (continuation parameters width base entry).2 ≤ 10000 * ((selectedSize parameters).total + 1) :=
      by
  have native := NativeContinuationConstruction.finish_clock parameters width (base +
    parameters.channels)
    (entry + (SupportCandidateConstruction.prepare width parameters.buses (base +
      parameters.bridge.target.val)).length + 11)
  have length : (continuation parameters width base entry).1.length ≤ 34 * (selectedSize
    parameters).total + 17 := by
    rw [continuation_image]
    exact SupportNativeSource.code_bound parameters
  change _ + 16 * (continuation parameters width base entry).1.length + 2000 ≤ _
  omega

theorem clock (parameters : Parameters) (width : Nat) (rows : List Row) (roots : List Nat) (k : Nat)
    (matched : RowsMatch parameters.decoder rows) (rootMatches : RootsMatch parameters.decoder
      roots) :
    (build parameters width rows roots k).2 ≤
      200000 * (parameters.decoder.countedSize + 1) + 20000 * ((selectedSize parameters).total + 1)
        := by
  let base := (SupportNativeSearch.source parameters width rows roots).size
  let native := continuation parameters width base 0
  let start := SupportNativeSearch.start parameters roots
  have nativeClock := continuation_clock parameters width base 0
  have body := SupportTraversalConstruction.clock width parameters.decoder rows roots k
    parameters.buses parameters.bridge.target start (start + native.1.length)
  have relocated := ProgramRelocationConstruction.build_clock start native.1
  have nativeLength : native.1.length ≤ 34 * (selectedSize parameters).total + 17 := by
    dsimp only [native]
    rw [continuation_image]
    exact SupportNativeSource.code_bound parameters
  have length : (build parameters width rows roots k).1.length ≤
      300 * (parameters.decoder.countedSize + 1) + 34 * (selectedSize parameters).total := by
    rw [image]
    exact SupportNativeSearch.code_bound parameters rows roots rootMatches
  obtain ⟨children, guards⟩ := matched_incidence_lengths parameters.decoder rows matched
  have rootLength : roots.length = parameters.decoder.roots.length := by rw [rootMatches]; simp
  simp only [matched.length_eq, children, guards, rootLength] at body
  have size := parameters.decoder.countedSize_eq
  change _ + _ + _ + 16 * (build parameters width rows roots k).1.length + 1000 *
    (parameters.decoder.countedSize + 1) ≤ _
  dsimp only [base, native, start] at *
  omega

end Controller.Cost.SupportNativeConstruction
