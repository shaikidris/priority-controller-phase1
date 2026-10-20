/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.NativeGateConstruction
import Controller.Cost.NativeCircuitSize

/-! One traversal builds native gate blocks and caches their lengths. Instruction
blocks are collected in reverse order and materialized once; no recursive
prefix is rebuilt to compute a later entry address. -/
namespace Controller.Cost.NativeCircuitConstruction

open Controller.Cost Controller.CNF
open Controller.Cost.NativeGateConstruction

structure Assembly (width : Nat) where
  reversed : List (List (Instruction width 4))
  cursor : Nat
  clock : Nat

def Assembly.image (assembly : Assembly width) : List (Instruction width 4) :=
  assembly.reversed.reverse.flatten

def collect (width base entry : Nat) : AcyclicCircuit roots count → Assembly width
  | .roots => ⟨[], 0, 1⟩
  | .snoc previous gate phase =>
      let prior := collect width base entry previous
      let current := form width base (entry + prior.cursor) phase gate
      ⟨current.1 :: prior.reversed, prior.cursor + current.1.length, prior.clock + current.2 + 20⟩

theorem collect_image (width base entry : Nat) (circuit : AcyclicCircuit roots count) :
    (collect width base entry circuit).image = NativeCircuitExecution.code width base entry circuit ∧
      (collect width base entry circuit).cursor = (NativeCircuitExecution.code width base entry circuit).length := by
  induction circuit with
  | roots => exact ⟨rfl, rfl⟩
  | snoc previous gate phase ih =>
      simp only [collect, Assembly.image, List.reverse_cons, List.flatten_append,
        List.flatten_cons, List.flatten_nil, List.append_nil, form_image, ih.2,
        NativeCircuitExecution.code, List.length_append]
      exact ⟨congrArg (fun front => front ++ NativeGateExecution.code width base
        (entry + (NativeCircuitExecution.code width base entry previous).length) phase gate) ih.1, trivial⟩

theorem collect_clock (width base entry : Nat) (circuit : AcyclicCircuit roots count) :
    (collect width base entry circuit).clock ≤
      420 * (circuit.gateCount + NativeCircuitExecution.inputOccurrences circuit) + 1 := by
  induction circuit with
  | roots => simp [collect, AcyclicCircuit.gateCount, NativeCircuitExecution.inputOccurrences]
  | snoc previous gate phase ih =>
      have formed := form_work width base (entry + (collect width base entry previous).cursor) phase gate
      simp only [collect, AcyclicCircuit.gateCount, NativeCircuitExecution.inputOccurrences]
      omega

theorem collect_blocks (width base entry : Nat) (circuit : AcyclicCircuit roots count) :
    (collect width base entry circuit).reversed.length = circuit.gateCount := by
  induction circuit with
  | roots => rfl
  | snoc previous gate phase ih => simp only [collect, List.length_cons, AcyclicCircuit.gateCount, ih]

def build (width base entry : Nat) (circuit : AcyclicCircuit roots count) : List (Instruction width 4) × Nat :=
  let result := collect width base entry circuit
  (result.image, result.clock + 4 * result.cursor + 4 * result.reversed.length + 16)

theorem build_image (width base entry : Nat) (circuit : AcyclicCircuit roots count) :
    (build width base entry circuit).1 = NativeCircuitExecution.code width base entry circuit :=
  (collect_image width base entry circuit).1

theorem build_clock (width base entry : Nat) (circuit : AcyclicCircuit roots count) :
    (build width base entry circuit).2 ≤
      500 * (circuit.gateCount + NativeCircuitExecution.inputOccurrences circuit + 1) := by
  have clock := collect_clock width base entry circuit
  have cursor := (collect_image width base entry circuit).2
  have length := NativeCircuitExecution.code_length_le width base entry circuit
  have blocks := collect_blocks width base entry circuit
  simp only [build, cursor, blocks]
  omega

theorem selected_clock (width base entry : Nat) (circuit : AcyclicCircuit roots count) :
    (build width base entry circuit).2 ≤ 500 * ((NativeCircuitSize.selectedSize circuit).total + 1) := by
  have clock := build_clock width base entry circuit
  have gates := NativeCircuitSize.gate_count_le_rows circuit
  have inputs := NativeCircuitSize.input_occurrences_le_literals circuit
  simp only [NativeCircuitSize.selectedSize, NativeSize.total]
  omega

end Controller.Cost.NativeCircuitConstruction
