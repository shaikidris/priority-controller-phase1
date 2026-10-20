/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.DeriveExtensionRecipe
import Controller.Cost.NativeContinuationConstruction
import Controller.Cost.SharedQueryDispatch
import Controller.Cost.ResidentSolverConstruction

/-! Fixed first-order blocks around the shared native model continuation. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Controller.Cost.ExtensionNativeRecipes

open Controller.Cost

derive_extension_recipe SharedNativeSuccessCode.prelude




def successTail (width outputEntry nativeCount channels returnPC : Nat) : List (Instruction width 8)
  :=
  (SharedEvaluationReclaim.code width (outputEntry + 3 * nativeCount)
    (outputEntry + 3 * nativeCount + 7) (channels + nativeCount)).toList ++
  SharedRegisterStack.restoreCode (List.finRange 8).reverse ++
  (ForestZeroReclaim.setupCode width).toList ++
  (ForestZeroReclaim.code width (outputEntry + 3 * nativeCount + 7 + 11) returnPC).toList

derive_extension_recipe successTail

def failed (width cleanup : Nat) : List (Instruction width 8) :=
  (ForestZeroAnswer.savedCode width 0 cleanup).toList

derive_extension_recipe failed

derive_extension_recipe ForestZeroRootLoop.dispatchCode

end Controller.Cost.ExtensionNativeRecipes
