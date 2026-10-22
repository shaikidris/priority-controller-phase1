module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Recognition.Check
public import Controller.Recognition.FamilyRecord

@[expose] public section

/-! Checked serialization reconstructs finite maps from their coordinate
vectors. These round trips are independent of a particular controller. -/

namespace Controller.Recognition
open Controller.CNF

namespace SerializedRecord

@[simp] theorem mapM_some (values : List α) (f : α → β) :
    values.mapM (fun value => some (f value)) = some (values.map f) := by
  induction values with
  | nil => simp
  | cons head tail ih => simp [ih]

@[simp] theorem mapM_some_id (values : List α) :
    values.mapM some = some values := by
  induction values with
  | nil => simp
  | cons head tail ih => simp [ih]

@[simp] theorem decodeID_val (i : Fin n) : decodeID n i.val = some i := by
  simp [decodeID, i.isLt]

@[simp] theorem decodeLiteral_val (literal : Literal (Fin n)) :
    decodeLiteral n (literal.1.val, literal.2) = some literal := by
  simp [decodeLiteral]

@[simp] theorem decodeOptionalID_val (index : Option (Fin n)) :
    decodeOptionalID n (index.map Fin.val) = some index := by
  cases index <;> simp [decodeOptionalID]

@[simp] theorem mapM_decodeID (values : List (Fin n)) :
    (values.map Fin.val).mapM (decodeID n) = some values := by
  induction values with
  | nil => simp
  | cons head tail ih => simp [ih]

@[simp] theorem mapM_decodeLiteral (values : Clause (Fin n)) :
    (values.map fun literal => (literal.1.val, literal.2)).mapM (decodeLiteral n) = some values := by
  induction values with
  | nil => simp
  | cons head tail ih => simp [ih]

@[simp] theorem decodeVector_finRange (values : Fin n → α) :
    decodeVector n ((List.finRange n).map values) = some values := by
  simp only [decodeVector, List.length_map, List.length_finRange, dite_true]
  congr 1
  funext i
  simp

theorem decodeRaw_serialize (record : Record source recovered) :
    decodeRaw source recovered record.serialize = some record := by
  cases record with
  | mk expected coordinate phase anchor aliases sourceRows expectedRows =>
    cases expected
    simp [decodeRaw, Record.serialize, Function.comp_def, ofClauses]

end SerializedRecord

namespace SerializedChainedRecord

@[simp] theorem decodeEdge_val (edge : AliasEdge (Fin n)) :
    decodeEdge n ((edge.left.val, edge.right.val), edge.phase) = some edge := by
  cases edge
  simp [decodeEdge]

theorem decodeRaw_serialize (record : AliasTrace.Record source recovered) :
    decodeRaw source recovered record.serialize = some record := by
  cases record
  simp [decodeRaw, AliasTrace.Record.serialize, SerializedRecord.decodeRaw_serialize,
    Function.comp_def]

theorem decodeChecked_serialize (record : AliasTrace.Record source recovered)
    (checked : record.check = true) :
    decodeChecked source recovered record.serialize = some record := by
  simp [decodeChecked, decodeRaw_serialize, AliasTrace.Record.serializedCheck, checked]

end SerializedChainedRecord

namespace SerializedRoles

@[simp] theorem roleIndex_get (parameters : Native.Parameters) (role : Native.Variable parameters) :
    parameters.variableRoles.get (roleIndex parameters role) = role := by
  simp [roleIndex]

@[simp] theorem roleIndex_getElem (parameters : Native.Parameters) (role : Native.Variable parameters) :
    parameters.variableRoles[(roleIndex parameters role).val] = role := by
  exact roleIndex_get parameters role

@[simp] theorem decodeID_roleIndex (parameters : Native.Parameters) (role : Native.Variable parameters) :
    SerializedRecord.decodeID parameters.variableRoles.length (parameters.variableRoles.idxOf role) =
      some (roleIndex parameters role) := by
  exact SerializedRecord.decodeID_val (roleIndex parameters role)

theorem decodeRaw_serialize (roles : FamilyRecord.Roles parameters recovered) :
    decodeRaw parameters recovered roles.serialize = some roles := by
  cases roles
  simp [decodeRaw, FamilyRecord.Roles.serialize, Function.comp_def,
    SerializedRecord.decodeVector]

theorem decodeChecked_serialize (roles : FamilyRecord.Roles parameters recovered)
    (checked : roles.check = true) :
    decodeChecked parameters recovered roles.serialize = some roles := by
  simp [decodeChecked, decodeRaw_serialize, FamilyRecord.Roles.serializedCheck, checked]

end SerializedRoles

namespace PrivateFamily.SerializedPartition

theorem decodeRaw_serialize (partition : Partition boundary auxCount recovered) :
    decodeRaw boundary auxCount recovered partition.serialize = some partition := by
  cases partition
  simp [decodeRaw, Partition.serialize, Function.comp_def]

theorem decodeChecked_serialize (partition : Partition boundary auxCount recovered)
    (checked : partition.check = true) :
    decodeChecked boundary auxCount recovered partition.serialize = some partition := by
  simp [decodeChecked, decodeRaw_serialize, Partition.serializedCheck, checked]

end PrivateFamily.SerializedPartition

namespace PrivateFamily.CompletePayload

/-- Serialize a typed recovery record into the packet accepted by the public
decoder. All certificate traces and row-indexed data retain their exact owners. -/
def ofRecord (record : PrivateFamily.Record source recovered parameters boundary auxCount) :
    CompletePayload source recovered parameters boundary auxCount where
  aliases := record.aliases.serialize
  roles := record.roles.serialize
  partition := record.partition.serialize
  expected := record.aliases.base.expected
  wrapper := record.wrapper
  targetLink := record.targetLink
  metadata := record.metadata
  namedDrive := record.namedDrive
  bundle := record.bundle
  coreCuts := record.coreCuts
  sourceCuts := record.sourceCuts

theorem decodeRaw_ofRecord
    (record : PrivateFamily.Record source recovered parameters boundary auxCount)
    (checked : record.check = true) : (ofRecord record).decodeRaw = some record := by
  have checks := (PrivateFamily.Record.check_iff record).mp checked
  simp [ofRecord, decodeRaw, SerializedChainedRecord.decodeChecked_serialize _ checks.1,
    SerializedRoles.decodeChecked_serialize _ checks.2.1,
    PrivateFamily.SerializedPartition.decodeChecked_serialize _ checks.2.2.1]

/-- Every checked typed record survives serialization and full packet replay. -/
theorem decodeChecked_ofRecord
    (record : PrivateFamily.Record source recovered parameters boundary auxCount)
    (checked : record.check = true) : (ofRecord record).decodeChecked = some record := by
  simp [decodeChecked, decodeRaw_ofRecord record checked, checked]

/-- Guarded dispatch preserves acceptance of the serialized checked record. -/
theorem guardedDecode_ofRecord
    (record : PrivateFamily.Record source recovered parameters boundary auxCount)
    (checked : record.check = true) (guarded : parameters.decoder.Guarded) :
    GuardedFamily.decodeChecked (ofRecord record) = some record := by
  simp [GuardedFamily.decodeChecked, (GuardedFamily.guardedCheck_iff parameters.decoder).mpr guarded,
    decodeChecked_ofRecord record checked]

#print axioms guardedDecode_ofRecord

end PrivateFamily.CompletePayload

end Controller.Recognition
