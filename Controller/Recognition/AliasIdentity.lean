module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Recognition.Check

@[expose] public section

namespace Controller.Recognition.AliasTrace
open Controller.CNF

/-- A formula already in recovered coordinates needs no signed alias edges. -/
def identity (source : Formula (Fin n)) : Record source n where
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

theorem identity_checked (source : Formula (Fin n)) : (identity source).check = true := by
  simp [Record.check, identity, Record.EdgeChecks,
    Recognition.Record.RowChecks, Recognition.Record.mappedRow, signedLiteral,
    SameLiterals, Record.AnchorChecks, Record.pathCheck, replay]

end Controller.Recognition.AliasTrace
