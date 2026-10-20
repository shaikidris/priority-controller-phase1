/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.NativeConstructionStorage

/-! Native output emission storage includes its address stream, mapped block
directory, flattened code and widening buffers in addition to the retained
native circuit constructor. -/
namespace Controller.Cost.NativeFinishStorage

open Controller.Cost Controller.Native Controller.Native.SourceController
open Controller.Cost.NativeSourceExecution Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestClauseProgramConstruction (environment)

inductive EmitTrace (width : Nat) : List Nat → List (Instruction width 4) → Nat → Prop
  | nil : EmitTrace width [] [] 32
  | cons {address rest code output first later}
      (head : WordConstructionStorage.Trace (environment [address])
        (NativeContinuationConstruction.emitRecipes width) code
        (work (NativeContinuationConstruction.emitRecipes width)) first)
      (tail : EmitTrace width rest output later)
      (copied : CompilerAppendTrace.AppendTrace code output (code ++ output) code.length) :
      EmitTrace width (address :: rest) (code ++ output)
        (max (first + 128) (later + 512))

theorem output (width : Nat) (addresses : List Nat) :
    ∃ peak, EmitTrace width addresses (NativeContinuationConstruction.emit width addresses).1 peak ∧
      peak ≤ 5000 * addresses.length + 1000 := by
  induction addresses with
  | nil => exact ⟨32, .nil, by simp⟩
  | cons address rest ih =>
      obtain ⟨first, head, firstBound⟩ := WordConstructionStorage.construction
        (environment [address]) (NativeContinuationConstruction.emitRecipes width)
      obtain ⟨later, tail, tailBound⟩ := ih
      have workBound : work (NativeContinuationConstruction.emitRecipes width) ≤ 100 := by
        simp [NativeContinuationConstruction.emitRecipes, work, InstructionRecipe.work,
          Expression.work]
      refine ⟨_, .cons head tail (CompilerAppendTrace.append_exists _ _), ?_⟩
      simp only [List.length_cons]
      exact Nat.max_le.mpr ⟨by omega, by omega⟩

structure Certificate (parameters : Parameters) (width base entry : Nat) where
  retained : NativeConstructionStorage.RetainedCertificate parameters width base entry
  outputPeak : Nat
  emitted : EmitTrace width
    (NativeRealizedCore.addresses (base + parameters.channels) (compile parameters).toState.count)
    (NativeContinuationConstruction.emit width
      (NativeRealizedCore.addresses (base + parameters.channels)
        (compile parameters).toState.count)).1 outputPeak

def buffers (parameters : Parameters) (width base entry : Nat)
    (certificate : Certificate parameters width base entry) : Nat :=
  NativeConstructionStorage.retainedBuffers parameters width base entry certificate.retained +
    certificate.outputPeak +
    64 * (NativeContinuationConstruction.finish parameters width base entry).1.length +
    1000 * ((selectedSize parameters).total + 1)

theorem complete (parameters : Parameters) (width base entry : Nat) :
    ∃ certificate : Certificate parameters width base entry,
      buffers parameters width base entry certificate ≤
        2000000 * ((selectedSize parameters).total + 1) := by
  obtain ⟨retained, retainedBound⟩ :=
    NativeConstructionStorage.retained_storage parameters width base entry
  obtain ⟨peak, emitted, outputBound⟩ := output width
    (NativeRealizedCore.addresses (base + parameters.channels) (compile parameters).toState.count)
  rw [NativeRealizedCore.addresses_length] at outputBound
  have length : (NativeContinuationConstruction.finish parameters width base entry).1.length ≤
      34 * (selectedSize parameters).total + 1 := by
    rw [NativeContinuationConstruction.finish_image]
    exact Controller.Extensions.BasisNativeFinish.code_bound parameters width base entry
  have variableBound : (compile parameters).toState.count ≤ (selectedSize parameters).total := by
    simp only [selectedSize, NativeSize.total]
    omega
  refine ⟨⟨retained, peak, emitted⟩, ?_⟩
  simp only [buffers]
  omega

end Controller.Cost.NativeFinishStorage
