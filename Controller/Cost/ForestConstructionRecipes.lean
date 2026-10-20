module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public meta import Controller.Cost.DeriveWordRecipe
public import Controller.Cost.ForestRootProjection

public import Controller.Cost.WordConstructionRecipe

@[expose] public section


/-! Fixed numeric forest kernels as first-order construction recipes. The
checked identities bind every operand and branch target to the native kernels. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Controller.Cost.ForestConstructionRecipes

open Controller.Cost.WordConstructionRecipe

def witness (width base rootCell bestCell descriptorBase rootBase sourceBase nodeCount markerBase countAddress : Nat) :
    GateProgram.Code width :=
  ForestWitnessMarshal.preludeCode width base rootCell bestCell descriptorBase rootBase ++
    ForestWitnessWalk.code width (base + 25)
      (ForestWitnessPath.packetLayout sourceBase nodeCount markerBase) countAddress

derive_word_recipe witness

derive_word_recipe ForestRootProjection.positiveTargetCleanupCode

derive_word_recipe ForestRootProjection.mixedMaskCode

def packetPrelude (width entry : Nat) : List (Instruction width 8) :=
  (ForestRootProjection.packetPreludeChunks width entry).flatMap Array.toList

derive_word_recipe packetPrelude

derive_word_recipe ForestRootProjection.negativeHandoffCode

derive_word_recipe ForestInputMetadata.fullCode

derive_word_recipe ForestZeroAdmissibleCaller.code

derive_word_recipe ForestZeroQueryCaller.preservingHeaderCode

derive_word_recipe ForestZeroQueryCaller.countCode

derive_word_recipe ForestZeroQuery.boundaryCode

def channelNegative (width base slot : Nat) : GateProgram.Code width :=
  ForestZeroEmit.literalCode width base ⟨slot, 0, false, (0 : Fin 1), false⟩
def channelPositive (width base slot : Nat) : GateProgram.Code width :=
  ForestZeroEmit.literalCode width base ⟨slot, 0, false, (0 : Fin 1), true⟩
def activityNegative (width base slot : Nat) : GateProgram.Code width :=
  ForestZeroEmit.literalCode width base ⟨slot, 0, true, (0 : Fin 1), false⟩
def activityPositive (width base slot : Nat) : GateProgram.Code width :=
  ForestZeroEmit.literalCode width base ⟨slot, 0, true, (0 : Fin 1), true⟩

derive_word_recipe channelNegative
derive_word_recipe channelPositive
derive_word_recipe activityNegative
derive_word_recipe activityPositive

end Controller.Cost.ForestConstructionRecipes
