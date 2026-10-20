module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.NativeFinishStorage
public import Controller.Cost.NativeSuccessConstruction

@[expose] public section


/-! Native success storage retains the fixed save/restore frames and both
native code materializations alongside the checked source-circuit constructor. -/
namespace Controller.Cost.NativeSuccessStorage

open Controller.Cost Controller.Native Controller.Native.SourceController
open Controller.Cost.NativeSourceExecution Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestClauseProgramConstruction (environment)

structure Certificate (parameters : Parameters) (width base entry returnPC : Nat) where
  native : NativeFinishStorage.Certificate parameters width base (entry + 43)
  frontPeak : Nat
  endingPeak : Nat
  front : WordConstructionStorage.Trace (environment [entry])
    (SharedNativeSuccessCode.prelude.constructionRecipe width)
    (evaluate (environment [entry]) (SharedNativeSuccessCode.prelude.constructionRecipe width))
    376 frontPeak
  ending : WordConstructionStorage.Trace
    (environment [entry + 43 +
      (NativeContinuationConstruction.retained parameters width base (entry + 43)).1.length,
      (compile parameters).toState.count, parameters.channels, returnPC])
    (ExtensionNativeRecipes.successTail.constructionRecipe width)
    (evaluate (environment [entry + 43 +
      (NativeContinuationConstruction.retained parameters width base (entry + 43)).1.length,
      (compile parameters).toState.count, parameters.channels, returnPC])
      (ExtensionNativeRecipes.successTail.constructionRecipe width)) 216 endingPeak

def buffers (parameters : Parameters) (width base entry returnPC : Nat)
    (certificate : Certificate parameters width base entry returnPC) : Nat :=
  NativeFinishStorage.buffers parameters width base (entry + 43) certificate.native +
    certificate.frontPeak + certificate.endingPeak +
    64 * (NativeSuccessConstruction.build parameters width base entry returnPC).1.length + 10000

theorem complete (parameters : Parameters) (width base entry returnPC : Nat) :
    ∃ certificate : Certificate parameters width base entry returnPC,
      buffers parameters width base entry returnPC certificate ≤
        3000000 * ((selectedSize parameters).total + 1) := by
  obtain ⟨native, nativeBound⟩ := NativeFinishStorage.complete parameters width base (entry + 43)
  obtain ⟨frontPeak, front, frontBound⟩ := WordConstructionStorage.construction
    (environment [entry]) (SharedNativeSuccessCode.prelude.constructionRecipe width)
  obtain ⟨endingPeak, ending, endingBound⟩ := WordConstructionStorage.construction
    (environment [entry + 43 +
      (NativeContinuationConstruction.retained parameters width base (entry + 43)).1.length,
      (compile parameters).toState.count, parameters.channels, returnPC])
    (ExtensionNativeRecipes.successTail.constructionRecipe width)
  rw [SharedNativeSuccessCode.prelude.constructionRecipe_work] at front frontBound
  rw [ExtensionNativeRecipes.successTail.constructionRecipe_work] at ending endingBound
  have length : (NativeSuccessConstruction.build parameters width base entry returnPC).1.length ≤
      100 * ((selectedSize parameters).total + 1) := by
    rw [NativeSuccessConstruction.image, SharedNativeSuccessCode.code_length]
    have bound := Controller.Extensions.BasisNativeFinish.code_bound parameters width base
      (SharedNativeSuccessCode.nativeEntry entry)
    rw [Controller.Extensions.BasisNativeFinish.code_length] at bound
    simp only [SharedNativeSuccessCode.nativeEntry] at bound ⊢
    omega
  refine ⟨⟨native, frontPeak, endingPeak, front, ending⟩, ?_⟩
  simp only [buffers]
  omega

end Controller.Cost.NativeSuccessStorage
