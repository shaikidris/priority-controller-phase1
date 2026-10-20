/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.NativeCircuitConstruction
import Controller.Cost.NativeRetainedExecution

/-! Physical native roots are formed once, in source-interface order. The
constructor caches each block length, so subsequent addresses do not require
rebuilding any previous native code. -/
namespace Controller.Cost.NativeRootConstruction

open Controller.Cost Controller.CNF Controller.Native Controller.Native.SourceController
open Controller.Cost.NativeGateConstruction

variable {channels : Nat}

def collect (width base entry : Nat) : List (Gate (Fin channels)) →
    List (List (Instruction width 4)) × Nat
  | [] => ([], 1)
  | gate :: rest =>
      let current := form width base entry true gate
      let tail := collect width base (entry + current.1.length) rest
      (current.1 :: tail.1, current.2 + tail.2 + 20)

theorem collect_image (width base entry : Nat) (gates : List (Gate (Fin channels))) :
    (collect width base entry gates).1.flatten = NativeRootBuilder.code width base entry gates := by
  induction gates generalizing entry with
  | nil => rfl
  | cons gate rest ih => simp only [collect, List.flatten_cons, form_image, NativeRootBuilder.code, ih]

def inputs (gates : List (Gate (Fin channels))) : Nat := (gates.map fun gate => gate.inputs.length).sum

theorem collect_clock (width base entry : Nat) (gates : List (Gate (Fin channels))) :
    (collect width base entry gates).2 ≤ 420 * (gates.length + inputs gates) + 1 := by
  induction gates generalizing entry with
  | nil => simp [collect, inputs]
  | cons gate rest ih =>
      have head := form_work width base entry true gate
      have tail := ih (entry + (form width base entry true gate).1.length)
      simp only [collect, inputs, List.map_cons, List.sum_cons, List.length_cons] at *
      omega

theorem source_inputs (parameters : Parameters) :
    inputs (NativeRootBuilder.sourceGates parameters) ≤ 2 * SourceInitialIDs.rootCount parameters := by
  have localBound : ∀ gate ∈ NativeRootBuilder.sourceGates parameters, gate.inputs.length ≤ 2 := by
    intro gate member
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    unfold NativePhysicalRootGate.sourceGate
    generalize (SourceInitialIDs.rootIndex (n := parameters.channels) (b := parameters.buses)).symm index = root
    cases root with
    | enable channel => simp only [NativePhysicalRootGate.gate]; split <;> simp [Gate.inputs]
    | request bus channel =>
        simp only [NativePhysicalRootGate.gate]
        split_ifs <;> simp [Gate.inputs]
  have listBound : ∀ gates : List (Gate (Fin parameters.channels)),
      (∀ gate ∈ gates, gate.inputs.length ≤ 2) → inputs gates ≤ 2 * gates.length := by
    intro gates
    induction gates with
    | nil => intro _; simp [inputs]
    | cons gate rest ih =>
        intro bound
        have first := bound gate (by simp)
        have later := ih (fun other member => bound other (by simp [member]))
        simp only [inputs, List.map_cons, List.sum_cons, List.length_cons] at *
        omega
  simpa only [NativeRootBuilder.sourceGates_length] using listBound _ localBound

def build (width base entry : Nat) (gates : List (Gate (Fin channels))) : List (Instruction width 4) × Nat :=
  let result := collect width base entry gates
  let image := result.1.flatten
  (image, result.2 + 4 * image.length + 4 * gates.length + 16)

theorem build_image (width base entry : Nat) (gates : List (Gate (Fin channels))) :
    (build width base entry gates).1 = NativeRootBuilder.code width base entry gates := collect_image width base entry gates

theorem source_clock (parameters : Parameters) (width base entry : Nat) :
    (build width base entry (NativeRootBuilder.sourceGates parameters)).2 ≤
      1500 * (SourceInitialIDs.rootCount parameters + 1) := by
  have clock := collect_clock width base entry (NativeRootBuilder.sourceGates parameters)
  have occurrences := source_inputs parameters
  have length := NativeRootBuilder.code_length_le width base entry (NativeRootBuilder.sourceGates parameters)
    (by
      intro producer member position
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
      exact NativePhysicalRootGate.code_length_le parameters.bridge.target
        ((SourceInitialIDs.rootIndex (n := parameters.channels) (b := parameters.buses)).symm index) width base position)
  simp only [NativeRootBuilder.sourceGates_length] at clock length
  simp only [build, collect_image, NativeRootBuilder.sourceGates_length]
  omega

end Controller.Cost.NativeRootConstruction
