/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.NativeContinuationConstruction
import Controller.Cost.TemplateStreamConstruction

/-! Temporary native-constructor storage. Fixed read/store recipes, occurrence
streams, gate blocks, reverse block directories and final materialization are
accounted in words. Source circuits are shared read-only inputs. -/
namespace Controller.Cost.NativeConstructionStorage

open Controller.Cost Controller.CNF Controller.Cost.NativeGateConstruction
open Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestClauseProgramConstruction (environment)

def ReadEvidence (width base : Nat) (literal : Literal (Fin count)) (peak : Nat) : Prop :=
  WordConstructionStorage.Trace (environment [base, literal.1.val]) (readRecipes width literal.2)
    (read width base literal) (work (readRecipes width literal.2)) peak

def StoreEvidence (width : Nat) (phase : Bool) (peak : Nat) : Prop :=
  WordConstructionStorage.Trace (environment [0, 0]) (storeRecipes width phase)
    (store width phase) (work (storeRecipes width phase)) peak

theorem read_storage (width base : Nat) (literal : Literal (Fin count)) :
    ∃ peak, ReadEvidence width base literal peak ∧ peak ≤ 3200 := by
  obtain ⟨peak, trace, bound⟩ := WordConstructionStorage.construction
    (environment [base, literal.1.val]) (readRecipes width literal.2)
  have workBound : work (readRecipes width literal.2) ≤ 100 := by
    simp [work, readRecipes, InstructionRecipe.work, Expression.work]
  exact ⟨peak, trace, by omega⟩

theorem store_storage (width : Nat) (phase : Bool) :
    ∃ peak, StoreEvidence width phase peak ∧ peak ≤ 3200 := by
  obtain ⟨peak, trace, bound⟩ := WordConstructionStorage.construction (environment [0, 0])
    (storeRecipes width phase)
  have workBound : work (storeRecipes width phase) ≤ 100 := by
    simp [work, storeRecipes, InstructionRecipe.work, Expression.work]
  exact ⟨peak, trace, by omega⟩

def ScanEvidence (width base entry : Nat) (phase replacement : Bool) (inputs : List (Literal (Fin
  count))) (peak : Nat) : Prop :=
  ∃ first stored, OccurrenceTrace width base replacement (entry + 1) inputs
      (occurrences width base replacement (entry + 1) inputs).1
      (occurrences width base replacement (entry + 1) inputs).2 first ∧
    StoreEvidence width phase stored ∧ peak = first + stored + 1000 * (inputs.length + 1)

def FormEvidence (width base entry : Nat) (phase : Bool) : Gate (Fin count) → Nat → Prop
  | .and inputs, peak => ScanEvidence width base entry phase false (inputs.map negate) peak
  | .or inputs, peak => ScanEvidence width base entry phase true inputs peak
  | .constant _, peak => ScanEvidence (count := count) width base entry phase false [] peak
  | .alias literal, peak => ∃ first stored, ReadEvidence width base literal first ∧ StoreEvidence
    width phase stored ∧
      peak = first + stored + 1000
  | .not literal, peak => ∃ first stored, ReadEvidence width base (negate literal) first ∧
    StoreEvidence width phase stored ∧
      peak = first + stored + 1000
  | .xor left right, peak => ∃ first second stored, ReadEvidence width base left first ∧
    ReadEvidence width base right second ∧
      StoreEvidence width phase stored ∧ peak = first + second + stored + 1000

theorem scan_storage (width base entry : Nat) (phase replacement : Bool) (inputs : List (Literal
  (Fin count))) :
    ∃ peak, ScanEvidence width base entry phase replacement inputs peak ∧ peak ≤ 10000 *
      (inputs.length + 1) := by
  obtain ⟨first, trace, firstBound⟩ := occurrences_storage width base replacement (entry + 1) inputs
  obtain ⟨stored, storeTrace, storeBound⟩ := store_storage width phase
  exact ⟨_, ⟨first, stored, trace, storeTrace, rfl⟩, by omega⟩

theorem form_storage (width base entry : Nat) (phase : Bool) (gate : Gate (Fin count)) :
    ∃ peak, FormEvidence width base entry phase gate peak ∧ peak ≤ 20000 * (gate.inputs.length + 1)
      := by
  cases gate with
  | and inputs =>
      obtain ⟨peak, trace, bound⟩ := scan_storage width base entry phase false (inputs.map negate)
      refine ⟨peak, trace, ?_⟩
      simp only [Gate.inputs, List.length_map]
      simp only [List.length_map] at bound
      omega
  | or inputs =>
      obtain ⟨peak, trace, bound⟩ := scan_storage width base entry phase true inputs
      exact ⟨peak, trace, by simp only [Gate.inputs]; omega⟩
  | constant value =>
      obtain ⟨peak, trace, bound⟩ := scan_storage (count := count) width base entry phase false []
      exact ⟨peak, trace, by simp only [Gate.inputs, List.length_nil] at bound ⊢; omega⟩
  | «alias» literal =>
      obtain ⟨first, trace, bound⟩ := read_storage width base literal
      obtain ⟨stored, storeTrace, storeBound⟩ := store_storage width phase
      refine ⟨_, ⟨first, stored, trace, storeTrace, rfl⟩, ?_⟩
      simp only [Gate.inputs, List.length_cons, List.length_nil]
      omega
  | «not» literal =>
      obtain ⟨first, trace, bound⟩ := read_storage width base (negate literal)
      obtain ⟨stored, storeTrace, storeBound⟩ := store_storage width phase
      refine ⟨_, ⟨first, stored, trace, storeTrace, rfl⟩, ?_⟩
      simp only [Gate.inputs, List.length_cons, List.length_nil]
      omega
  | xor left right =>
      obtain ⟨first, trace, firstBound⟩ := read_storage width base left
      obtain ⟨second, secondTrace, secondBound⟩ := read_storage width base right
      obtain ⟨stored, storeTrace, storeBound⟩ := store_storage width phase
      exact ⟨_, ⟨first, second, stored, trace, secondTrace, storeTrace, rfl⟩,
        by simp only [Gate.inputs, List.length_cons, List.length_nil]; omega⟩

inductive CircuitTrace (width base entry : Nat) : {roots count : Nat} → AcyclicCircuit roots count →
  Nat → Prop
  | roots : CircuitTrace width base entry AcyclicCircuit.roots 32
  | snoc {previous : AcyclicCircuit roots count} {gate phase first later}
      (tail : CircuitTrace width base entry previous later)
      (formed : FormEvidence width base (entry + (NativeCircuitConstruction.collect width base entry
        previous).cursor) phase gate first) :
      CircuitTrace width base entry (.snoc previous gate phase)
        (later + first + 1000 * (gate.inputs.length + 1))

theorem circuit_storage (width base entry : Nat) (circuit : AcyclicCircuit roots count) :
    ∃ peak, CircuitTrace width base entry circuit peak ∧ peak ≤
      30000 * (circuit.gateCount + NativeCircuitExecution.inputOccurrences circuit + 1) := by
  induction circuit with
  | roots => exact ⟨32, .roots, by simp [AcyclicCircuit.gateCount,
    NativeCircuitExecution.inputOccurrences]⟩
  | snoc previous gate phase ih =>
      obtain ⟨later, tail, tailBound⟩ := ih
      obtain ⟨first, formed, firstBound⟩ := form_storage width base
        (entry + (NativeCircuitConstruction.collect width base entry previous).cursor) phase gate
      refine ⟨_, .snoc tail formed, ?_⟩
      simp only [AcyclicCircuit.gateCount, NativeCircuitExecution.inputOccurrences]
      omega

inductive RootsTrace (width base : Nat) : Nat → List (Gate (Fin channels)) → Nat → Prop
  | nil (entry) : RootsTrace width base entry [] 32
  | cons {entry gate rest first later}
      (formed : FormEvidence width base entry true gate first)
      (tail : RootsTrace width base (entry + (NativeGateConstruction.form width base entry true
        gate).1.length) rest later) :
      RootsTrace width base entry (gate :: rest) (first + later + 1000 * (gate.inputs.length + 1))

theorem roots_storage (width base entry : Nat) (gates : List (Gate (Fin channels))) :
    ∃ peak, RootsTrace width base entry gates peak ∧
      peak ≤ 30000 * (gates.length + NativeRootConstruction.inputs gates + 1) := by
  induction gates generalizing entry with
  | nil => exact ⟨32, .nil entry, by simp [NativeRootConstruction.inputs]⟩
  | cons gate rest ih =>
      obtain ⟨first, formed, firstBound⟩ := form_storage width base entry true gate
      obtain ⟨later, tail, tailBound⟩ := ih (entry + (NativeGateConstruction.form width base entry
        true gate).1.length)
      refine ⟨_, .cons formed tail, ?_⟩
      simp only [List.length_cons, NativeRootConstruction.inputs, List.map_cons, List.sum_cons] at *
      omega

open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution

def inputRecipes (width : Nat) : List (InstructionRecipe 0 width 4) := [.plain (.pop 3), .plain
  (.allocate 3)]

theorem input_image (width start count : Nat) :
    (TemplateStreamConstruction.build (inputRecipes width) (fun _ index => Fin.elim0 index) start
      count).1 =
      NativeRootLoad.code width count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      change [.pop 3, .allocate 3] ++ (TemplateStreamConstruction.build (inputRecipes width)
        (fun _ index => Fin.elim0 index) (start + 1) count).1 = _
      rw [ih]
      rfl

theorem input_storage (width count : Nat) :
    ∃ peak, TemplateStreamConstruction.Trace (inputRecipes width) (fun _ index => Fin.elim0 index) 0
      count
      (NativeRootLoad.code width count) (42 * count + 1) peak ∧ peak ≤ 640 * (count + 1) := by
  obtain ⟨peak, trace, bound⟩ := TemplateStreamConstruction.storage (inputRecipes width) (fun _
    index => Fin.elim0 index) 0 count
  rw [input_image, TemplateStreamConstruction.clock] at trace
  simp only [inputRecipes, work, InstructionRecipe.work, List.length_cons, List.length_nil,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd] at trace bound
  exact ⟨peak, by simpa only [inputRecipes, Nat.mul_comm] using trace, by nlinarith⟩

structure RetainedCertificate (parameters : Parameters) (width base entry : Nat) where
  inputPeak : Nat
  input : TemplateStreamConstruction.Trace (inputRecipes width) (fun _ index => Fin.elim0 index) 0
    parameters.channels
    (NativeRootLoad.code width parameters.channels) (42 * parameters.channels + 1) inputPeak
  rootsPeak : Nat
  circuitPeak : Nat
  roots : RootsTrace width base (entry + 2 * parameters.channels) (NativeRootBuilder.sourceGates
    parameters) rootsPeak
  circuit : CircuitTrace width (base + parameters.channels)
    (entry + 2 * parameters.channels +
      (NativeRootConstruction.build width base (entry + 2 * parameters.channels)
        (NativeRootBuilder.sourceGates parameters)).1.length)
    (sourceCircuit parameters) circuitPeak

def retainedBuffers (parameters : Parameters) (width base entry : Nat)
    (certificate : RetainedCertificate parameters width base entry) : Nat :=
  certificate.inputPeak + certificate.rootsPeak + certificate.circuitPeak +
    64 * (NativeContinuationConstruction.retained parameters width base entry).1.length +
    1000 * ((selectedSize parameters).total + 1)

theorem retained_storage (parameters : Parameters) (width base entry : Nat) :
    ∃ certificate : RetainedCertificate parameters width base entry,
      retainedBuffers parameters width base entry certificate ≤ 1000000 * ((selectedSize
        parameters).total + 1) := by
  obtain ⟨inputPeak, inputTrace, inputBound⟩ := input_storage width parameters.channels
  obtain ⟨rootsPeak, rootsTrace, rootsBound⟩ := roots_storage width base (entry + 2 *
    parameters.channels)
    (NativeRootBuilder.sourceGates parameters)
  obtain ⟨circuitPeak, circuitTrace, circuitBound⟩ := circuit_storage width (base +
    parameters.channels)
    (entry + 2 * parameters.channels +
      (NativeRootConstruction.build width base (entry + 2 * parameters.channels)
        (NativeRootBuilder.sourceGates parameters)).1.length)
    (sourceCircuit parameters)
  have rootInputs := NativeRootConstruction.source_inputs parameters
  rw [NativeRootBuilder.sourceGates_length] at rootsBound
  have circuitGates := NativeCircuitSize.gate_count_le_rows (sourceCircuit parameters)
  have circuitInputs := NativeCircuitSize.input_occurrences_le_literals (sourceCircuit parameters)
  rw [equation_rows] at circuitGates
  rw [equation_literals] at circuitInputs
  have rows := equation_rows_le parameters
  have literals := equation_literals_le parameters
  have interface := (sourceCircuit parameters).roots_le
  have channels : parameters.channels ≤ SourceInitialIDs.rootCount parameters := by simp
    [SourceInitialIDs.rootCount]
  have source := NativeRetainedExecution.source_code_bound parameters width base entry
  have body := NativeSourceExecution.code_length_le parameters width (base + parameters.channels)
    (NativeRetainedExecution.circuitEntry parameters width base entry)
  have length : (NativeContinuationConstruction.retained parameters width base entry).1.length ≤ 31
    * (selectedSize parameters).total := by
    rw [NativeContinuationConstruction.retained_image, NativeRetainedExecution.code_length]
    change (NativeRetainedExecution.circuitCode parameters width base entry).length ≤ _ at body
    simp only [selectedSize, NativeSize.total] at *
    omega
  refine ⟨{
    inputPeak := inputPeak
    input := inputTrace
    rootsPeak := rootsPeak
    circuitPeak := circuitPeak
    roots := rootsTrace
    circuit := circuitTrace }, ?_⟩
  simp only [retainedBuffers, selectedSize, NativeSize.total] at *
  omega

end Controller.Cost.NativeConstructionStorage
