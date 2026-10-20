/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.NativeSuccessConstruction
import Controller.Cost.QuietQueryConstruction

/-! Native-emitting resident query construction shares the charged clause
prefix and fixed normalizer/FIFO stream with the quiet query. The successful
runtime verdict enters the charged native continuation. -/
set_option maxRecDepth 10000

namespace Controller.Cost.NativeQueryConstruction

open Controller.Cost Controller.Native Controller.Native.SourceController
open Controller.Cost.WordConstructionRecipe Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestClauseProgramConstruction (environment)
open Controller.Cost.ForestZeroEmit Controller.Cost.ExtensionNativeRecipes

variable {ambient : Nat}

def source (width entry keep count base : Nat) (refs : List (List (Reference ambient))) :
    List (Instruction width 8) × Nat :=
  let quiet := QuietQueryConstruction.build width entry keep count base refs
  (quiet.1.take (quiet.1.length - 430), quiet.2 + 16 * quiet.1.length + 100)

theorem source_image (width entry keep count base : Nat) (refs : List (List (Reference ambient))) :
    (source width entry keep count base refs).1 = SharedQuerySourceCode.code width entry keep refs
      := by
  simp only [source, QuietQueryConstruction.image, EnumerationResident.code, List.length_append,
    EnumerationResident.solverCode_length, Nat.add_sub_cancel_right, List.take_left]

theorem source_cursor (width entry keep count base : Nat) (refs : List (List (Reference ambient))) :
    entry + (source width entry keep count base refs).1.length = SharedQuerySourceCode.solverEntry
      width entry keep refs := by
  have after : entry ≤ SharedQuerySourceCode.solverEntry width entry keep refs := by
    unfold SharedQuerySourceCode.solverEntry; omega
  rw [source_image, SharedQuerySourceCode.code_length]
  omega

structure Data (width : Nat) where
  prefixCode : List (Instruction width 8)
  solver : Nat
  cleanup : Nat
  nativeCode : List (Instruction width 8)

def prepare (parameters : Parameters) (width entry keep count base nativeBase : Nat)
    (refs : List (List (Reference ambient))) : Data width × Nat :=
  let first := source width entry keep count base refs
  let solver := entry + first.1.length
  let provisional := NativeSuccessConstruction.build parameters width nativeBase (solver + 395) 0
  let cleanup := solver + 395 + provisional.1.length
  let native := NativeSuccessConstruction.build parameters width nativeBase (solver + 395) (cleanup
    + 7)
  (⟨first.1, solver, cleanup, native.1⟩, first.2 + provisional.2 + native.2 + 20000)

def assemble (width keep count base next : Nat) (data : Data width) : List (Instruction width 8) :=
  let head := evaluate (environment [keep, base, count, data.solver, 0])
    (ResidentSolverConstruction.recipes width)
  let yes := evaluate (environment [keep, base, count, data.solver, 0])
    (ForestNegativeRecipes.part17.constructionRecipe width)
  let no := evaluate (environment [data.cleanup]) (failed.constructionRecipe width)
  let ending := evaluate (environment [data.cleanup])
    (SharedQueryCleanupCode.code.constructionRecipe width)
  let dispatch := evaluate (environment [next]) (ForestZeroRootLoop.dispatchCode.constructionRecipe
    width)
  data.prefixCode ++ head ++ yes ++ no ++ data.nativeCode ++ ending ++ dispatch

def build (parameters : Parameters) (width entry keep count base nativeBase : Nat)
    (refs : List (List (Reference ambient))) (next : Nat) : List (Instruction width 8) × Nat :=
  let prepared := prepare parameters width entry keep count base nativeBase refs
  let image := assemble width keep count base next prepared.1
  (image, prepared.2 + 16 * image.length)

def specified (parameters : Parameters) (width entry keep nativeBase : Nat)
    (refs : List (List (Reference ambient))) : Data width :=
  let solver := SharedQuerySourceCode.solverEntry width entry keep refs
  let cleanup := SharedQueryTailCode.cleanup parameters width nativeBase (solver + 261)
  ⟨SharedQuerySourceCode.code width entry keep refs, solver, cleanup,
    SharedNativeSuccessCode.code parameters width nativeBase (solver + 395) (cleanup + 7)⟩

theorem prepare_image (parameters : Parameters) (width entry keep count base nativeBase : Nat)
    (refs : List (List (Reference ambient))) :
    (prepare parameters width entry keep count base nativeBase refs).1 =
      specified parameters width entry keep nativeBase refs := by
  have cleanup (solver : Nat) : solver + 395 +
      (NativeSuccessConstruction.build parameters width nativeBase (solver + 395) 0).1.length =
      SharedQueryTailCode.cleanup parameters width nativeBase (solver + 261) := by
    rw [NativeSuccessConstruction.image, SharedNativeSuccessCode.code_length]
    simp only [SharedQueryTailCode.cleanup, SharedQueryTailCode.projection,
      SharedNativeSuccessCode.nativeEntry,
      Nat.add_assoc, Nat.reduceAdd]
  unfold prepare
  simp only [source_cursor]
  simp only [cleanup]
  simp only [source_image, NativeSuccessConstruction.image, specified]

set_option maxHeartbeats 1000000 in
theorem assemble_image (parameters : Parameters) (width entry keep count base nativeBase : Nat)
    (refs : List (List (Reference ambient))) (next : Nat) :
    assemble width keep count base next (specified parameters width entry keep nativeBase refs) =
      SharedQueryDispatch.code parameters width entry keep count base nativeBase refs next := by
  have yes (solver : Nat) : evaluate (environment [keep, base, count, solver, 0])
      (ForestNegativeRecipes.part17.constructionRecipe width) = ForestNegativeRecipes.part17 width
        keep base count solver 0 :=
    ForestNegativeRecipes.part17.constructionRecipe_eq width keep base count solver 0
  have no (cleanup : Nat) : evaluate (environment [cleanup]) (failed.constructionRecipe width) =
    failed width cleanup :=
    failed.constructionRecipe_eq width cleanup
  have ending (cleanup : Nat) : evaluate (environment [cleanup])
    (SharedQueryCleanupCode.code.constructionRecipe width) =
      SharedQueryCleanupCode.code width cleanup := SharedQueryCleanupCode.code.constructionRecipe_eq
        width cleanup
  have dispatch : evaluate (environment [next]) (ForestZeroRootLoop.dispatchCode.constructionRecipe
    width) =
      (ForestZeroRootLoop.dispatchCode width next).toList :=
        ForestZeroRootLoop.dispatchCode.constructionRecipe_eq width next
  simp only [assemble, specified]
  rw [ResidentSolverConstruction.head_image, yes, no, ending, dispatch]
  conv_rhs => unfold SharedQueryDispatch.code
  conv_rhs => unfold SharedQueryResidentCode.code
  conv_rhs => unfold SharedQuerySolverCode.code
  conv_rhs => unfold SharedQueryTailCode.code
  conv_rhs => unfold SharedQueryTailCode.success
  simp only [SharedQueryTailCode.projection]
  simp only [SharedSolverPrefix.code, SharedNormalizerCode.code, SharedWorklistCode.code,
    Array.toList_append]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil,
    ForestNegativeRecipes.part00, ForestNegativeRecipes.part01, ForestNegativeRecipes.part02,
      ForestNegativeRecipes.part03, ForestNegativeRecipes.part04, ForestNegativeRecipes.part05,
      ForestNegativeRecipes.part06, ForestNegativeRecipes.part07, ForestNegativeRecipes.part08,
      ForestNegativeRecipes.part09, ForestNegativeRecipes.part10, ForestNegativeRecipes.part11,
      ForestNegativeRecipes.part12, ForestNegativeRecipes.part13, ForestNegativeRecipes.part14,
      ForestNegativeRecipes.part15, ForestNegativeRecipes.part16, ForestNegativeRecipes.part17,
    ForestNegativeRecipes.normalizeStream, failed]
  simp only [ForestNegativeRecipes.rowStream_eq, ForestNegativeRecipes.copyStream_eq,
    ForestNegativeRecipes.seedStream_eq, Array.toList_append, List.append_assoc, Nat.add_assoc,
      Nat.reduceAdd]

theorem image (parameters : Parameters) (width entry keep count base nativeBase : Nat)
    (refs : List (List (Reference ambient))) (next : Nat) :
    (build parameters width entry keep count base nativeBase refs next).1 =
      SharedQueryDispatch.code parameters width entry keep count base nativeBase refs next := by
  change assemble width keep count base next (prepare parameters width entry keep count base
    nativeBase refs).1 = _
  rw [prepare_image]
  exact assemble_image parameters width entry keep count base nativeBase refs next

theorem source_length (width entry keep count base : Nat) (refs : List (List (Reference ambient))) :
    (source width entry keep count base refs).1.length ≤ 117 + 5 * refs.length + 28 *
      refs.flatten.length := by
  have length := ForestZeroAdmissibleCaller.constructorCode_length width (entry + 15) keep keep
    (keep + 4) 0 refs
  simp only [ForestZeroAdmissibleCaller.constructorCode, List.length_append,
    ForestZeroAdmissibleCaller.code_length] at length
  rw [source_image, SharedQuerySourceCode.code_length]
  unfold SharedQuerySourceCode.solverEntry
  omega

theorem source_clock (width entry keep count base : Nat) (refs : List (List (Reference ambient))) :
    (source width entry keep count base refs).2 ≤ 50000 + 1000 * refs.length + 3000 *
      refs.flatten.length := by
  have clock := QuietQueryConstruction.clock width entry keep count base refs
  have first := source_length width entry keep count base refs
  rw [source_image] at first
  have length : (QuietQueryConstruction.build width entry keep count base refs).1.length ≤
      547 + 5 * refs.length + 28 * refs.flatten.length := by
    simp only [QuietQueryConstruction.image, EnumerationResident.code, List.length_append,
      EnumerationResident.solverCode_length]
    omega
  change (QuietQueryConstruction.build width entry keep count base refs).2 +
    16 * (QuietQueryConstruction.build width entry keep count base refs).1.length + 100 ≤ _
  omega

theorem code_length (parameters : Parameters) (width entry keep count base nativeBase : Nat)
    (refs : List (List (Reference ambient))) (next : Nat) :
    (build parameters width entry keep count base nativeBase refs next).1.length ≤
      614 + 5 * refs.length + 28 * refs.flatten.length + 34 * (selectedSize parameters).total := by
  let solver := SharedQuerySourceCode.solverEntry width entry keep refs
  have first := source_length width entry keep count base refs
  have cursor := source_cursor width entry keep count base refs
  have endpoint := SharedQueryResidentCode.code_end parameters width entry keep count base
    nativeBase refs
  have native := Controller.Extensions.BasisNativeFinish.code_bound parameters width nativeBase
    (SharedNativeSuccessCode.nativeEntry (SharedQueryTailCode.projection (solver + 261)))
  rw [Controller.Extensions.BasisNativeFinish.code_length] at native
  rw [image]
  rw [SharedQueryDispatch.code]
  simp only [List.length_append, Array.length_toList, ForestZeroRootLoop.dispatchCode,
    List.length_cons, List.length_nil]
  dsimp only [SharedQueryTailCode.cleanup, SharedQueryTailCode.projection, solver] at endpoint
  dsimp only [SharedQueryTailCode.cleanup, SharedQueryTailCode.projection, solver] at native
  omega

theorem clock (parameters : Parameters) (width entry keep count base nativeBase : Nat)
    (refs : List (List (Reference ambient))) (next : Nat) :
    (build parameters width entry keep count base nativeBase refs next).2 ≤
      200000 + 2000 * refs.length + 5000 * refs.flatten.length + 30000 * ((selectedSize
        parameters).total + 1) := by
  let solver := entry + (source width entry keep count base refs).1.length
  let cleanup := solver + 395 + (NativeSuccessConstruction.build parameters width nativeBase (solver
    + 395) 0).1.length
  have first := source_clock width entry keep count base refs
  have provisional := NativeSuccessConstruction.clock parameters width nativeBase (solver + 395) 0
  have native := NativeSuccessConstruction.clock parameters width nativeBase (solver + 395) (cleanup
    + 7)
  have length := code_length parameters width entry keep count base nativeBase refs next
  change (source width entry keep count base refs).2 +
    (NativeSuccessConstruction.build parameters width nativeBase (solver + 395) 0).2 +
    (NativeSuccessConstruction.build parameters width nativeBase (solver + 395) (cleanup + 7)).2 +
      20000 +
    16 * (build parameters width entry keep count base nativeBase refs next).1.length ≤ _
  omega

end Controller.Cost.NativeQueryConstruction
