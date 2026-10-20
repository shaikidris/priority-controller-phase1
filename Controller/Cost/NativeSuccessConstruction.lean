/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ExtensionNativeRecipes

/-! A native success continuation is formed from fixed control templates and
the charged selected-circuit constructor. It emits the runtime assignment;
no satisfying assignment appears in the constructor input. -/
namespace Controller.Cost.NativeSuccessConstruction

open Controller.Cost Controller.Native Controller.Native.SourceController
open Controller.Cost.NativeSourceExecution Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestClauseProgramConstruction (environment)
open Controller.Cost.ExtensionNativeRecipes

def build (parameters : Parameters) (width base entry returnPC : Nat) : List (Instruction width 8) ×
  Nat :=
  let front := evaluate (environment [entry]) (SharedNativeSuccessCode.prelude.constructionRecipe
    width)
  let native := NativeContinuationConstruction.retained parameters width base (entry + 43)
  let outEntry := entry + 43 + native.1.length
  let output := NativeContinuationConstruction.emit width
    (NativeRealizedCore.addresses (base + parameters.channels) (compile parameters).toState.count)
  let ending := evaluate (environment [outEntry, (compile parameters).toState.count,
    parameters.channels, returnPC])
    (successTail.constructionRecipe width)
  let image := front ++ native.1.map RegisterWiden.widenInstruction ++
    output.1.map RegisterWiden.widenInstruction ++ ending
  (image, native.2 + output.2 + work (SharedNativeSuccessCode.prelude.constructionRecipe width) +
    work (successTail.constructionRecipe width) + 16 * image.length + 100)

theorem image (parameters : Parameters) (width base entry returnPC : Nat) :
    (build parameters width base entry returnPC).1 = SharedNativeSuccessCode.code parameters width
      base entry returnPC := by
  have front : evaluate (environment [entry]) (SharedNativeSuccessCode.prelude.constructionRecipe
    width) =
      SharedNativeSuccessCode.prelude width entry :=
        SharedNativeSuccessCode.prelude.constructionRecipe_eq width entry
  have ending (outEntry : Nat) : evaluate (environment [outEntry, (compile
    parameters).toState.count, parameters.channels, returnPC])
      (successTail.constructionRecipe width) = successTail width outEntry (compile
        parameters).toState.count parameters.channels returnPC :=
    successTail.constructionRecipe_eq width outEntry (compile parameters).toState.count
      parameters.channels returnPC
  simp only [build, front, ending, NativeContinuationConstruction.retained_image,
    NativeContinuationConstruction.emit_image, SharedNativeSuccessCode.code,
      SharedNativeSuccessCode.suffix,
    SharedNativeSuccessCode.nativeEntry, SharedNativeSuccessCode.outputEntry,
      SharedZeroNativeComplete.emitEntry,
    SharedNativeSuccessCode.done, successTail, List.append_assoc]

theorem clock (parameters : Parameters) (width base entry returnPC : Nat) :
    (build parameters width base entry returnPC).2 ≤ 10000 * ((selectedSize parameters).total + 1)
      := by
  have native := NativeContinuationConstruction.retained_clock parameters width base (entry + 43)
  have size := Controller.Extensions.BasisNativeFinish.code_bound parameters width base (entry + 43)
  rw [Controller.Extensions.BasisNativeFinish.code_length] at size
  have count : (compile parameters).toState.count ≤ (selectedSize parameters).total := by
    simp only [selectedSize, NativeSize.total]; omega
  have length : (build parameters width base entry returnPC).1.length ≤ 34 * (selectedSize
    parameters).total + 65 := by
    rw [image, SharedNativeSuccessCode.code_length]
    simp only [SharedNativeSuccessCode.nativeEntry]
    omega
  have fixed : work (SharedNativeSuccessCode.prelude.constructionRecipe width) + work
    (successTail.constructionRecipe width) ≤ 2000 := by
    rw [SharedNativeSuccessCode.prelude.constructionRecipe_work,
      successTail.constructionRecipe_work]
    decide
  change (NativeContinuationConstruction.retained parameters width base (entry + 43)).2 +
    (50 * (NativeRealizedCore.addresses (base + parameters.channels) (compile
      parameters).toState.count).length + 1) +
    work (SharedNativeSuccessCode.prelude.constructionRecipe width) + work
      (successTail.constructionRecipe width) +
    16 * (build parameters width base entry returnPC).1.length + 100 ≤ _
  rw [NativeRealizedCore.addresses_length]
  omega

end Controller.Cost.NativeSuccessConstruction
