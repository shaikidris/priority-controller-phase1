module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Recognition.AcceptanceCoordinates
public import Controller.Recognition.AcceptanceCertificates
public import Controller.Recognition.Check
import all Init.Data.Nat.Lemmas

@[expose] public section

/-! Ordinary-resolution checks for the witness's exact identity row cuts. -/

namespace Controller.Recognition.AcceptanceCutCheck
open Controller.Certificate
set_option maxRecDepth 100000
set_option maxHeartbeats 200000
set_option cbv.maxSteps 2000000
attribute [local cbv_eval] Nat.decidableBallLT_eq_decidableBallLTTR

def certificateAt (data : Array (Certificate n)) (index : Nat) : Certificate n :=
  data[index]?.getD (.lrat #[])

def core : PrivateFamily.Cuts AcceptanceCoordinates.native AcceptanceCoordinates.native where
  forward := fun i => certificateAt AcceptanceCertificates.core i.val
  backward := fun i => certificateAt AcceptanceCertificates.core i.val

def source : PrivateFamily.Cuts AcceptanceCoordinates.wrapped AcceptanceCoordinates.wrapped where
  forward := fun i => certificateAt AcceptanceCertificates.source i.val
  backward := fun i => certificateAt AcceptanceCertificates.source i.val

theorem core_checked : core.check = true := by decide_cbv
theorem source_checked : source.check = true := by decide_cbv

#print axioms core_checked
#print axioms source_checked
end Controller.Recognition.AcceptanceCutCheck
