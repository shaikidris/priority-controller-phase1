module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Recognition.AcceptanceReplay

@[expose] public section

/-! Nonvacuity of positive-output typed recognition. The witness has two
channels, one bus, one observed output, one private activity, 36 source
coordinates and 91 source clauses. It passes the entire serialized decoder
and the SAT pipeline, and has a physical detecting input. -/

namespace Controller.Recognition
open Controller.CNF Controller.Certificate

/-- A positive-output accepted packet exists, with a genuine physical
detection and a successful SAT verdict checked against the original source. -/
theorem exists_accepted_positive_output :
    ∃ (parameters : Native.Parameters) (source : Formula (Fin 36))
      (payload : PrivateFamily.CompletePayload source 36 parameters 35 1)
      (record : PrivateFamily.Record source 36 parameters 35 1),
      parameters.channels = 2 ∧ parameters.buses = 1 ∧ parameters.drive = true ∧
      parameters.decoder.roots.length = 1 ∧ source.clauses.size = 91 ∧
      GuardedFamily.decodeChecked payload = some record ∧
      Physical.BridgeDetectable (b := parameters.buses) parameters.bridge parameters.drive parameters.observations ∧
      Pipeline.runFamily source (.structured (InputPacket.serialize source)) payload none = .sat ∧
      Satisfiable source := by
  obtain ⟨record, accepted⟩ := AcceptanceReplay.payload_accepted
  refine ⟨AcceptanceReplay.parameters, AcceptanceReplay.source, AcceptanceReplay.payload,
    record, rfl, rfl, rfl, rfl, AcceptanceReplay.sizes.2.2.1, accepted,
    ⟨AcceptanceReplay.input, true, AcceptanceReplay.physical_detection⟩,
    AcceptanceReplay.pipeline_sat, AcceptanceReplay.model, AcceptanceReplay.model_satisfies⟩

#print axioms exists_accepted_positive_output

end Controller.Recognition
