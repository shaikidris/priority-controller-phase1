/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.NativeRootConstruction
import Controller.Extensions.BasisNativeFinish

/-! Native continuation construction from the selected source circuit and its
physical interface. Root blocks and circuit blocks are built once. The selected
circuit is a source description, not a computed satisfying assignment. -/
namespace Controller.Cost.NativeContinuationConstruction

open Controller.Cost Controller.Native Controller.Native.SourceController
open Controller.Cost.NativeSourceExecution Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestClauseProgramConstruction (environment)

def retained (parameters : Parameters) (width base entry : Nat) : List (Instruction width 4) × Nat :=
  let roots := NativeRootConstruction.build width base (entry + 2 * parameters.channels)
    (NativeRootBuilder.sourceGates parameters)
  let circuit := NativeCircuitConstruction.build width (base + parameters.channels)
    (entry + 2 * parameters.channels + roots.1.length) (sourceCircuit parameters)
  let image := NativeRootLoad.code width parameters.channels ++ roots.1 ++ circuit.1
  (image, 20 * parameters.channels + roots.2 + circuit.2 + 4 * image.length + 100)

theorem retained_image (parameters : Parameters) (width base entry : Nat) :
    (retained parameters width base entry).1 = NativeRetainedExecution.code parameters width base entry := by
  simp only [retained, NativeRootConstruction.build_image, NativeCircuitConstruction.build_image,
    NativeRetainedExecution.code, NativeRetainedExecution.rootCode, NativeRetainedExecution.circuitCode,
    NativeRetainedExecution.circuitEntry, List.append_assoc]

theorem circuit_clock (parameters : Parameters) (width base entry : Nat) :
    (NativeCircuitConstruction.build width base entry (sourceCircuit parameters)).2 ≤
      500 * ((selectedSize parameters).total + 1) := by
  have clock := NativeCircuitConstruction.build_clock width base entry (sourceCircuit parameters)
  have gates := NativeCircuitSize.gate_count_le_rows (sourceCircuit parameters)
  have inputs := NativeCircuitSize.input_occurrences_le_literals (sourceCircuit parameters)
  rw [equation_rows] at gates
  rw [equation_literals] at inputs
  have rows := equation_rows_le parameters
  have literals := equation_literals_le parameters
  simp only [selectedSize, NativeSize.total]
  omega

theorem retained_clock (parameters : Parameters) (width base entry : Nat) :
    (retained parameters width base entry).2 ≤ 3000 * ((selectedSize parameters).total + 1) := by
  have roots := NativeRootConstruction.source_clock parameters width base (entry + 2 * parameters.channels)
  have circuit := circuit_clock parameters width (base + parameters.channels)
    (entry + 2 * parameters.channels +
      (NativeRootConstruction.build width base (entry + 2 * parameters.channels) (NativeRootBuilder.sourceGates parameters)).1.length)
  have source := NativeRetainedExecution.source_code_bound parameters width base entry
  have body := NativeSourceExecution.code_length_le parameters width (base + parameters.channels)
    (NativeRetainedExecution.circuitEntry parameters width base entry)
  have interface := (sourceCircuit parameters).roots_le
  have channels : parameters.channels ≤ SourceInitialIDs.rootCount parameters := by simp [SourceInitialIDs.rootCount]
  have variableBound : (compile parameters).toState.count ≤ (selectedSize parameters).total := by
    simp only [selectedSize, NativeSize.total]; omega
  have length : (retained parameters width base entry).1.length ≤ 31 * (selectedSize parameters).total := by
    rw [retained_image, NativeRetainedExecution.code_length]
    change (NativeRetainedExecution.circuitCode parameters width base entry).length ≤ _ at body
    omega
  change 20 * parameters.channels + _ + _ + 4 * (retained parameters width base entry).1.length + 100 ≤ _
  omega

def emitRecipes (width : Nat) : List (InstructionRecipe 1 width 4) :=
  [.constant 0 (.parameter 0), .plain (.load 1 0), .plain (.emit 1)]

def emit (width : Nat) (addresses : List Nat) : List (Instruction width 4) × Nat :=
  let blocks := addresses.map fun address => evaluate (environment [address]) (emitRecipes width)
  (blocks.flatten, 50 * addresses.length + 1)

theorem emit_image (width : Nat) (addresses : List Nat) :
    (emit width addresses).1 = OutputProgram.emitCode width addresses := by
  induction addresses with
  | nil => rfl
  | cons address rest ih =>
      change evaluate (environment [address]) (emitRecipes width) ++ (emit width rest).1 = _
      rw [ih]
      rfl

def finish (parameters : Parameters) (width base entry : Nat) : List (Instruction width 8) × Nat :=
  let front := retained parameters width base entry
  let output := emit width (NativeRealizedCore.addresses (base + parameters.channels) (compile parameters).toState.count)
  let image := front.1.map RegisterWiden.widenInstruction ++ output.1.map RegisterWiden.widenInstruction ++ [.halt]
  (image, front.2 + output.2 + 16 * front.1.length + 16 * output.1.length + 100)

theorem finish_image (parameters : Parameters) (width base entry : Nat) :
    (finish parameters width base entry).1 = Controller.Extensions.BasisNativeFinish.code parameters width base entry := by
  simp only [finish, retained_image, emit_image, Controller.Extensions.BasisNativeFinish.code, List.append_assoc]

theorem finish_clock (parameters : Parameters) (width base entry : Nat) :
    (finish parameters width base entry).2 ≤ 5000 * ((selectedSize parameters).total + 1) := by
  have front := retained_clock parameters width base entry
  have length := Controller.Extensions.BasisNativeFinish.code_bound parameters width base entry
  have decomposition := Controller.Extensions.BasisNativeFinish.code_length parameters width base entry
  have variableBound : (compile parameters).toState.count ≤ (selectedSize parameters).total := by
    simp only [selectedSize, NativeSize.total]; omega
  have outputLength : (emit width (NativeRealizedCore.addresses (base + parameters.channels)
      (compile parameters).toState.count)).1.length = 3 * (compile parameters).toState.count := by
    rw [emit_image, OutputProgram.emitCode_length, NativeRealizedCore.addresses_length]
  change _ + (50 * (NativeRealizedCore.addresses (base + parameters.channels)
    (compile parameters).toState.count).length + 1) + _ + _ + 100 ≤ _
  rw [NativeRealizedCore.addresses_length, outputLength, retained_image]
  omega

end Controller.Cost.NativeContinuationConstruction
