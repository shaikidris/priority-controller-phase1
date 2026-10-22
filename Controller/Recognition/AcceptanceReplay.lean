module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Certificate.Pipeline
public import Controller.Recognition.AcceptanceCertificates
public import Controller.Recognition.AcceptanceCoordinates
public import Controller.Recognition.AcceptanceMetadataCheck
public import Controller.Recognition.AcceptanceCutCheck
public import Controller.Recognition.SerializationRoundtrip
public import Controller.Recognition.AliasIdentity
import all Std.Tactic.BVDecide.LRAT.Internal.Checker
import all Std.Tactic.BVDecide.LRAT.Internal.Basic
import all Std.Tactic.BVDecide.LRAT.Internal.Assignment
import all Std.Tactic.BVDecide.LRAT.Internal.Add
import all Std.Tactic.BVDecide.LRAT.Internal.Delete
import all Std.Tactic.BVDecide.LRAT.Internal.Rup
import all Std.Tactic.BVDecide.LRAT.Internal.Empty
import all Std.Tactic.BVDecide.LRAT.Internal.Rat
import all Std.Sat.CNF.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Array.Basic
import all Init.Data.Nat.Lemmas

@[expose] public section

/-! A concrete one-observation controller with an activity wrapper.
Finite certificate data are replayed by the existing LRAT backend. The construction uses the full typed recognition API. -/

namespace Controller.Recognition.AcceptanceReplay
open Controller.CNF Controller.Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option cbv.warning false
set_option cbv.maxSteps 2000000
attribute [local cbv_eval] Nat.decidableBallLT_eq_decidableBallLTTR

def parameters : Native.Parameters where
  channels := 2
  buses := 1
  positiveBuses := by decide
  bridge := {
    target := 0
    drivers := {1}
    drivers_nonempty := by simp
    target_not_mem := by decide }
  decoder := {
    nodeCount := 1
    node := fun _ => .input 1
    roots := [0] }
  layout := .raw
  drive := true

abbrev boundary := 35
abbrev total := boundary + 1

@[local cbv_eval] theorem drivers_sort : parameters.bridge.drivers.sort = [⟨1, by decide⟩] := by
  simp [parameters]

@[local cbv_eval] theorem remaining_sort : parameters.bridge.remaining.sort = [] := by
  have empty : parameters.bridge.remaining = ∅ := by decide
  simp [empty]

def roles : FamilyRecord.Roles parameters boundary where
  identify := SerializedRoles.roleIndex parameters
  name := parameters.variableRoles.get
  phase := fun _ => true

def nativeDefinitions : Formula (Fin boundary) :=
  signedRelabel roles.identify roles.phase (PrivateFamily.driveFormula parameters)

def definitions : Formula (Fin boundary) := AcceptanceCoordinates.native

theorem definitions_normalized : nativeDefinitions = definitions := by
  apply OrderedFormula.Internal.ext_iff.mpr
  decide_cbv

def pair : Literal (Fin boundary) × Literal (Fin boundary) :=
  (signedLiteral roles.identify roles.phase
    (Native.Parameters.internal parameters (.decoder .healthy ⟨0, by decide⟩)),
   signedLiteral roles.identify roles.phase
    (Native.Parameters.internal parameters (.decoder .faulty ⟨0, by decide⟩)))

def wrapperFormula : Formula (Fin boundary ⊕ Fin 1) :=
  ofClauses (Native.ObservationProjection.guardRows 0 pair ++ [[(Sum.inr 0, true)]])

def partition : PrivateFamily.Partition boundary 1 total where
  identify := finSumFinEquiv
  name := finSumFinEquiv.symm
  phase := fun _ => true

def sourceTemplate : Formula (Fin total) :=
  signedRelabel partition.identify partition.phase
    (relabel Sum.inl definitions ++ wrapperFormula)

def source : Formula (Fin total) := AcceptanceCoordinates.wrapped

theorem source_normalized : sourceTemplate = source := by
  apply OrderedFormula.Internal.ext_iff.mpr
  decide_cbv

/-- Original rows and recovered coordinates coincide in this source. -/
def aliases : AliasTrace.Record source total where
  base := {
    expected := source
    coordinate := id
    phase := fun _ => true
    anchor := id
    aliases := fun _ => []
    sourceRows := some
    expectedRows := id }
  edges := []
  origins := fun i => Fin.elim0 i
  paths := fun _ => []

/-- Certificate lookup fails closed if an index is absent. -/
def certificateAt (data : Array (Certificate n)) (index : Nat) : Certificate n :=
  data[index]?.getD (.lrat #[])

def target : Literal (Fin boundary) :=
  signedLiteral roles.identify roles.phase (Native.Parameters.internal parameters .detected)

def wrapper : Attachment.WrapperRecord boundary 1 1 where
  definitions := definitions
  wrapper := wrapperFormula
  pairs := fun _ => pair
  activities := fun _ => 0
  selected := [0]
  guards := fun _ slot => certificateAt AcceptanceCertificates.guards slot.val
  necessity := AcceptanceCertificates.necessity
  orientations := fun _ left right => .extension (fun _ => true) (fun index =>
    certificateAt AcceptanceCertificates.orientations
      (((if left then 2 else 0) + (if right then 1 else 0)) * 3 + index.val))

def targetLink : Attachment.TargetLink.Record boundary 1 where
  definitions := definitions
  target := target
  pairs := fun _ => pair
  selected := [0]
  forward := fun _ left right => certificateAt AcceptanceCertificates.targetForward
    ((if left then 2 else 0) + (if right then 1 else 0))
  necessary := AcceptanceCertificates.targetNecessary

def metadata : ProducerMetadata.Record definitions :=
  AcceptanceMetadataCheck.metadata

def coreCuts : PrivateFamily.Cuts definitions definitions := AcceptanceCutCheck.core

def sourceCuts : PrivateFamily.Cuts source source := AcceptanceCutCheck.source

def record : PrivateFamily.Record source total parameters boundary 1 where
  aliases := aliases
  roles := roles
  partition := partition
  wrapper := wrapper
  targetLink := targetLink
  metadata := metadata
  namedDrive := definitions
  bundle := source
  coreCuts := coreCuts
  sourceCuts := sourceCuts

def payload : PrivateFamily.CompletePayload source total parameters boundary 1 :=
  PrivateFamily.CompletePayload.ofRecord record

/-- Both channels are enabled, but only the target requests the sole bus. -/
def input : Physical.PrimaryInput 2 1 where
  positiveBuses := by decide
  enable := fun _ => true
  request := fun _ channel => channel == 0

def model : Fin total → Bool :=
  record.liftNative (Native.Lift.named parameters input true)

theorem aliases_checked : aliases.check = true := by
  simp [AliasTrace.Record.check, aliases, AliasTrace.Record.EdgeChecks,
    Recognition.Record.RowChecks, Recognition.Record.mappedRow, signedLiteral,
    SameLiterals, AliasTrace.Record.AnchorChecks, AliasTrace.Record.pathCheck, AliasTrace.replay]

theorem roles_checked : roles.check = true := by
  apply roles.check_iff.mpr
  constructor
  · intro role
    exact SerializedRoles.roleIndex_get parameters role
  · intro index
    apply Fin.ext
    exact parameters.variableRoles_nodup.idxOf_getElem index.val index.isLt

theorem partition_checked : partition.check = true := by
  apply partition.check_iff.mpr
  constructor <;> intro index <;> simp [partition]

theorem coreCuts_checked : coreCuts.check = true := AcceptanceCutCheck.core_checked
theorem sourceCuts_checked : sourceCuts.check = true := AcceptanceCutCheck.source_checked
theorem wrapper_checked : wrapper.check = true := by decide_cbv
theorem targetLink_checked : targetLink.check = true := by decide_cbv
theorem metadata_checked : metadata.check = true :=
  AcceptanceMetadataCheck.checked

/-- The concrete record passes every producer, projection and row check. -/
theorem record_checked : record.check = true := by
  apply record.check_iff.mpr
  refine ⟨aliases_checked, roles_checked, partition_checked, coreCuts_checked,
    sourceCuts_checked, wrapper_checked, targetLink_checked, metadata_checked, ?_⟩
  refine ⟨congrArg OrderedFormula.clauses definitions_normalized.symm,
    congrArg OrderedFormula.clauses source_normalized.symm,
    rfl, rfl, rfl, rfl, ?_, rfl, ?_⟩
  · funext index
    rcases index with ⟨index, bound⟩
    have zero : index = 0 := by
      change index < 1 at bound
      omega
    subst index
    rfl
  · decide_cbv

/-- The complete serialized packet is accepted with one observed output. -/
theorem payload_accepted : ∃ accepted,
    GuardedFamily.decodeChecked payload = some accepted := by
  refine ⟨record, PrivateFamily.CompletePayload.guardedDecode_ofRecord record record_checked ?_⟩
  intro index
  rfl

/-- The witness detects an actual physical discrepancy at the observed output. -/
theorem physical_detection : Physical.BridgeInputDetects parameters.bridge parameters.drive
    parameters.observations input true := by
  unfold Physical.BridgeInputDetects Physical.BridgeInterfaceSatisfied
    Physical.ObservationsDiffer
  decide_cbv

/-- The source has a full satisfying assignment, including the activity bit. -/
theorem model_satisfies : Satisfies model source :=
  record.checked_lift_native record_checked _
    (Native.Lift.named_satisfies parameters input true physical_detection)

/-- Typed recognition, the guarded detector, lifting and original-row validation
return SAT on this nontrivial wrapped instance without a refutation input. -/
theorem pipeline_sat : Pipeline.runFamily source
    (.structured (InputPacket.serialize source)) payload none = .sat := by
  obtain ⟨accepted, recognized⟩ := payload_accepted
  exact (Pipeline.runFamily_sat_iff source payload accepted recognized none).mpr
    ⟨model, model_satisfies⟩

theorem sizes : boundary = 35 ∧ total = 36 ∧ source.clauses.size = 91 ∧
    parameters.decoder.roots.length = 1 := by decide_cbv

#print axioms record_checked
#print axioms payload_accepted
#print axioms model_satisfies
#print axioms physical_detection
#print axioms pipeline_sat
#print axioms sizes

end Controller.Recognition.AcceptanceReplay
