/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.QuietQueryStorage
import Controller.Cost.NativeSuccessStorage

/-! Storage for the complete shared native query constructor. Uniform fixed
recipe traces cover every scalar placement; source and native continuations
are tied to their actual provisional and final constructor calls. -/
namespace Controller.Cost.NativeQueryStorage

open Controller.Cost Controller.Native Controller.Native.SourceController
open Controller.Cost.NativeSourceExecution Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestZeroEmit Controller.Cost.ExtensionNativeRecipes

variable {ambient : Nat}

def Uniform (recipes : List (InstructionRecipe parameters width registers)) : Prop :=
  ∀ environment, ∃ peak,
    WordConstructionStorage.Trace environment recipes (evaluate environment recipes)
      (work recipes) peak ∧ peak ≤ 32 * work recipes

theorem uniform (recipes : List (InstructionRecipe parameters width registers)) :
    Uniform recipes := fun environment => WordConstructionStorage.construction environment recipes

structure FixedBlocks (width : Nat) where
  head : Uniform (ResidentSolverConstruction.recipes width)
  accepted : Uniform (ForestNegativeRecipes.part17.constructionRecipe width)
  rejected : Uniform (failed.constructionRecipe width)
  cleaned : Uniform (SharedQueryCleanupCode.code.constructionRecipe width)
  dispatched : Uniform (ForestZeroRootLoop.dispatchCode.constructionRecipe width)

def fixedWork (width : Nat) : Nat :=
  work (ResidentSolverConstruction.recipes width) +
  work (ForestNegativeRecipes.part17.constructionRecipe width) +
  work (failed.constructionRecipe width) +
  work (SharedQueryCleanupCode.code.constructionRecipe width) +
  work (ForestZeroRootLoop.dispatchCode.constructionRecipe width)

theorem fixed_bound (width : Nat) : fixedWork width ≤ 20000 := by
  have head := ResidentSolverConstruction.clock_bound width
  unfold ResidentSolverConstruction.clock at head
  simp only [fixedWork, ForestNegativeRecipes.part17.constructionRecipe_work,
    failed.constructionRecipe_work, SharedQueryCleanupCode.code.constructionRecipe_work,
    ForestZeroRootLoop.dispatchCode.constructionRecipe_work]
  omega

def solver (width entry keep count base : Nat) (refs : List (List (Reference ambient))) : Nat :=
  entry + (NativeQueryConstruction.source width entry keep count base refs).1.length

def cleanup (parameters : Parameters) (width entry keep count base nativeBase : Nat)
    (refs : List (List (Reference ambient))) : Nat :=
  solver width entry keep count base refs + 395 +
    (NativeSuccessConstruction.build parameters width nativeBase
      (solver width entry keep count base refs + 395) 0).1.length

structure Certificate (parameters : Parameters) (width entry keep count base nativeBase : Nat)
    (refs : List (List (Reference ambient))) where
  source : QuietQueryStorage.Certificate width entry keep count base refs
  provisional : NativeSuccessStorage.Certificate parameters width nativeBase
    (solver width entry keep count base refs + 395) 0
  native : NativeSuccessStorage.Certificate parameters width nativeBase
    (solver width entry keep count base refs + 395)
    (cleanup parameters width entry keep count base nativeBase refs + 7)
  fixed : FixedBlocks width

def buffers (parameters : Parameters) (width entry keep count base nativeBase next : Nat)
    (refs : List (List (Reference ambient)))
    (certificate : Certificate parameters width entry keep count base nativeBase refs) : Nat :=
  QuietQueryStorage.buffers width entry keep count base refs certificate.source +
  NativeSuccessStorage.buffers parameters width nativeBase
    (solver width entry keep count base refs + 395) 0 certificate.provisional +
  NativeSuccessStorage.buffers parameters width nativeBase
    (solver width entry keep count base refs + 395)
    (cleanup parameters width entry keep count base nativeBase refs + 7) certificate.native +
  32 * fixedWork width +
  128 * (NativeQueryConstruction.build parameters width entry keep count base nativeBase
    refs next).1.length + 10000

theorem complete (parameters : Parameters) (width entry keep count base nativeBase next : Nat)
    (refs : List (List (Reference ambient))) :
    ∃ certificate : Certificate parameters width entry keep count base nativeBase refs,
      buffers parameters width entry keep count base nativeBase next refs certificate ≤
        100000000 * (refs.length + refs.flatten.length + (selectedSize parameters).total + 1) := by
  obtain ⟨source, sourceBound⟩ := QuietQueryStorage.complete width entry keep count base refs
  obtain ⟨provisional, provisionalBound⟩ := NativeSuccessStorage.complete parameters width
    nativeBase (solver width entry keep count base refs + 395) 0
  obtain ⟨native, nativeBound⟩ := NativeSuccessStorage.complete parameters width nativeBase
    (solver width entry keep count base refs + 395)
    (cleanup parameters width entry keep count base nativeBase refs + 7)
  have fixed := fixed_bound width
  have length := NativeQueryConstruction.code_length parameters width entry keep count base
    nativeBase refs next
  refine ⟨⟨source, provisional, native,
    ⟨uniform _, uniform _, uniform _, uniform _, uniform _⟩⟩, ?_⟩
  simp only [buffers]
  omega

end Controller.Cost.NativeQueryStorage
