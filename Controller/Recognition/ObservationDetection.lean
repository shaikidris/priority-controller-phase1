module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Recognition.Check
public import Controller.Physical.DetectCorrect

@[expose] public section

/-! Optional observation wrappers over the actual native controller equations.
The private assignment domain is the wrapper's finite declared support.
Projection is related to physical detection without a successful-recognition
premise. This is a semantic construction theorem, not a discovery-time bound. -/

namespace Controller.Recognition.ObservationDetection
open Controller.CNF Controller.Native.ObservationProjection

def observedPair (parameters : Native.Parameters)
    (i : Fin parameters.decoder.roots.length) :
    Literal (Native.Variable parameters) × Literal (Native.Variable parameters) :=
  (Native.Parameters.internal parameters (.decoder .healthy (parameters.decoder.roots.get i)),
   Native.Parameters.internal parameters (.decoder .faulty (parameters.decoder.roots.get i)))

/-- Under the actual defining equations, the detection output is the
disjunction of discrepancies at the declared observed decoder roots. -/
theorem detected_iff (parameters : Native.Parameters)
    (assignment : Native.Variable parameters → Bool)
    (model : Satisfies assignment (PrivateFamily.driveFormula parameters)) :
    LiteralHolds assignment (Native.Parameters.internal parameters .detected) ↔
      ∃ i, Discrepant assignment (observedPair parameters i) := by
  have equations := (parameters.equationFormula_iff assignment).mp
    ((satisfies_append _ _ _).mp model).1
  have detection := equations .detected
  have differences : ∀ i : Fin parameters.decoder.roots.length,
      literalValue assignment (Native.Parameters.internal parameters (.difference i)) =
        (literalValue assignment (observedPair parameters i).1 ^^
          literalValue assignment (observedPair parameters i).2) := by
    intro i
    simpa [Native.Parameters.gate, Gate.eval, Native.Parameters.internal,
      Native.Parameters.positive, literalValue, observedPair] using equations (.difference i)
  change assignment (.internal .detected) = true ↔ _
  rw [detection]
  simp only [Native.Parameters.gate, Gate.eval, List.any_map, Function.comp_def, differences]
  simp [Discrepant]

/-- An optional grammar attached to the physical native roots projects to
physical bridge detectability. Every private assignment here has the finite
declared auxiliary domain. No decoder-acceptance witness is assumed. -/
theorem optional_native_projection [Fintype ι] (parameters : Native.Parameters)
    (wrapper : OptionalWrapper (Native.Variable parameters) ι
      (Fin parameters.decoder.roots.length))
    (declared : wrapper.DeclaredPrivate)
    (pairs : wrapper.observedPairs = observedPair parameters)
    (allRoots : ∀ i, i ∈ wrapper.tree.leaves) :
    (∃ (signals : Native.Variable parameters → Bool)
      (privateValues : {a // a ∈ wrapper.declaredAuxiliaries} → Bool),
      Satisfies (joint signals (extendDeclaredAuxiliaries wrapper.declaredAuxiliaries privateValues))
        (relabel Sum.inl (PrivateFamily.driveFormula parameters) ++ wrapper.formula)) ↔
      Physical.BridgeDetectable (b := parameters.buses) parameters.bridge parameters.drive
        parameters.observations := by
  rw [← parameters.specification_satisfiable_iff]
  constructor
  · rintro ⟨signals, privateValues, model⟩
    obtain ⟨native, wrapped⟩ := (satisfies_append _ _ _).mp model
    have nativeModel : Satisfies signals (PrivateFamily.driveFormula parameters) :=
      (satisfies_relabel Sum.inl _ _).mp native
    have discrepancy := (optional_declared_cnf_projection wrapper declared signals).mp
      ⟨privateValues, wrapped⟩
    obtain ⟨i, _, different⟩ := discrepancy
    have detected := (detected_iff parameters signals nativeModel).mpr
      ⟨i, by simpa only [pairs] using different⟩
    exact ⟨signals, (PrivateFamily.native_drive_detection_iff parameters signals).mpr
      ⟨nativeModel, detected⟩⟩
  · rintro ⟨signals, model⟩
    obtain ⟨native, detected⟩ := (PrivateFamily.native_drive_detection_iff parameters signals).mp model
    obtain ⟨i, different⟩ := (detected_iff parameters signals native).mp detected
    obtain ⟨privateValues, wrapped⟩ :=
      (optional_declared_cnf_projection wrapper declared signals).mpr
        ⟨i, allRoots i, by simpa only [pairs] using different⟩
    refine ⟨signals, privateValues, (satisfies_append _ _ _).mpr ⟨?_, wrapped⟩⟩
    exact (satisfies_relabel Sum.inl _ _).mpr native

/-- The existing guarded detector decides this represented wrapper family.
Construction and discovery costs are separate from this correctness theorem. -/
theorem optional_native_decision [Fintype ι] (parameters : Native.Parameters)
    (guarded : parameters.decoder.Guarded)
    (wrapper : OptionalWrapper (Native.Variable parameters) ι
      (Fin parameters.decoder.roots.length))
    (declared : wrapper.DeclaredPrivate)
    (pairs : wrapper.observedPairs = observedPair parameters)
    (allRoots : ∀ i, i ∈ wrapper.tree.leaves) :
    (∃ (signals : Native.Variable parameters → Bool)
      (privateValues : {a // a ∈ wrapper.declaredAuxiliaries} → Bool),
      Satisfies (joint signals (extendDeclaredAuxiliaries wrapper.declaredAuxiliaries privateValues))
        (relabel Sum.inl (PrivateFamily.driveFormula parameters) ++ wrapper.formula)) ↔
      (Physical.detectInput parameters.bridge parameters.positiveBuses parameters.drive
        parameters.decoder).isSome = true := by
  rw [optional_native_projection parameters wrapper declared pairs allRoots]
  cases found : Physical.detectInput parameters.bridge parameters.positiveBuses parameters.drive
      parameters.decoder with
  | none =>
    have absent := (Physical.detectInput_none_iff parameters.bridge parameters.positiveBuses
      parameters.drive parameters.decoder guarded).mp found
    constructor
    · intro detects
      exact (absent detects).elim
    · intro impossible
      cases impossible
  | some input =>
    have detects : Physical.BridgeDetectable (b := parameters.buses) parameters.bridge
        parameters.drive parameters.observations :=
      ⟨input, true, Physical.detectInput_some parameters.bridge parameters.positiveBuses
        parameters.drive parameters.decoder guarded input found⟩
    simp [detects]

#print axioms detected_iff
#print axioms optional_native_projection
#print axioms optional_native_decision

end Controller.Recognition.ObservationDetection
