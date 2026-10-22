module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Recognition.AcceptanceMetadataData
public import Controller.Recognition.AcceptanceCoordinates
import all Init.Data.Nat.Lemmas

@[expose] public section

/-! Validation of the fixed native core's finite producer certificate. -/

namespace Controller.Recognition.AcceptanceMetadataCheck
open Controller.CNF
set_option maxRecDepth 100000
set_option maxHeartbeats 200000
set_option cbv.maxSteps 2000000
attribute [local cbv_eval] Nat.decidableBallLT_eq_decidableBallLTTR

def metadata := AcceptanceMetadataData.build AcceptanceCoordinates.native (by decide_cbv)

theorem selection : ValidSelection metadata.roots metadata.rank metadata.selected := by
  unfold ValidSelection
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide_cbv

theorem blocks : ∀ block ∈ metadata.blocks, block.Valid := by decide_cbv

theorem replay : ProducerMetadata.replay metadata.roots AcceptanceCoordinates.native
    metadata.blocks = some Finset.univ := by decide_cbv

theorem checked : metadata.check = true :=
  metadata.check_iff.mpr ⟨selection, blocks, replay⟩

#print axioms checked

end Controller.Recognition.AcceptanceMetadataCheck
