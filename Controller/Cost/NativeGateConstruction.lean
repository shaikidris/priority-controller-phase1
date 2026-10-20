module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.NativeGateExecution
public import Controller.Cost.ForestClauseProgramConstruction
public import Controller.Cost.WordConstructionStorage

@[expose] public section


/-! Native instruction formation from source literal coordinates. Environments
contain scalar source fields; arithmetic recipes form addresses and branch
positions. No environment field contains an instruction or a selected answer. -/
namespace Controller.Cost.NativeGateConstruction

open Controller.Cost Controller.CNF Controller.Cost.GateProgram
open Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestClauseProgramConstruction (environment)

def readRecipes (width : Nat) (positive : Bool) : List (InstructionRecipe 2 width 4) :=
  [.constant 0 (.add (.parameter 0) (.parameter 1)), .plain (.load 1 0),
    .constant 2 (.literal (if !positive then 1 else 0)), .plain (.xor 1 1 2)]

theorem read_image (width base : Nat) (literal : Literal (Fin count)) :
    evaluate (environment [base, literal.1.val]) (readRecipes width literal.2) =
      NativeGateRead.code width base literal := by
  cases literal with
  | mk index positive => cases positive <;> rfl

def storeRecipes (width : Nat) (phase : Bool) : List (InstructionRecipe 2 width 4) :=
  [.constant 2 (.literal (if !phase then 1 else 0)), .plain (.xor 3 3 2), .plain (.allocate 3)]

theorem store_image (width : Nat) (phase : Bool) (values : Fin 2 → Nat) :
    evaluate values (storeRecipes width phase) = NativeGateStore.code width phase := by
  cases phase <;> rfl

def occurrenceRecipes (width : Nat) (positive replacement : Bool) :
    List (InstructionRecipe 3 width 4) :=
  [.constant 0 (.add (.parameter 0) (.parameter 1)), .plain (.load 1 0),
    .constant 2 (.literal (if !positive then 1 else 0)), .plain (.xor 1 1 2),
    .branchZero 1 (.add (.parameter 2) (.literal 6)),
    .constant 3 (.literal (if replacement then 1 else 0))]

theorem occurrence_image (width base entry : Nat) (literal : Literal (Fin count)) (replacement : Bool) :
    evaluate (environment [base, literal.1.val, entry]) (occurrenceRecipes width literal.2 replacement) =
      NativeGateConditional.code width base entry literal replacement := by
  rcases literal with ⟨index, positive⟩
  cases positive <;> cases replacement <;> rfl

def occurrences (width base : Nat) (replacement : Bool) (entry : Nat) :
    List (Literal (Fin count)) → List (Instruction width 4) × Nat
  | [] => ([], 1)
  | literal :: rest =>
      let recipes := occurrenceRecipes width literal.2 replacement
      let current := evaluate (environment [base, literal.1.val, entry]) recipes
      let tail := occurrences width base replacement (entry + 6) rest
      (current ++ tail.1, work recipes + tail.2 + 40)

theorem occurrences_image (width base : Nat) (replacement : Bool) (entry : Nat)
    (inputs : List (Literal (Fin count))) :
    (occurrences width base replacement entry inputs).1 = NativeGateFold.code width base replacement entry inputs := by
  induction inputs generalizing entry with
  | nil => rfl
  | cons literal rest ih =>
      simp only [occurrences, NativeGateFold.code, occurrence_image, ih]

theorem occurrences_work (width base : Nat) (replacement : Bool) (entry : Nat)
    (inputs : List (Literal (Fin count))) :
    (occurrences width base replacement entry inputs).2 ≤ 120 * inputs.length + 1 := by
  induction inputs generalizing entry with
  | nil => simp [occurrences]
  | cons literal rest ih =>
      have bound := ih (entry + 6)
      have formed : work (occurrenceRecipes width literal.2 replacement) = 60 := by
        simp [work, occurrenceRecipes, InstructionRecipe.work, Expression.work]
      simp only [occurrences, formed, List.length_cons]
      omega

inductive OccurrenceTrace (width base : Nat) (replacement : Bool) : Nat →
    List (Literal (Fin count)) → List (Instruction width 4) → Nat → Nat → Prop
  | nil (entry) : OccurrenceTrace width base replacement entry [] [] 1 32
  | cons {entry literal rest code tail first later p q}
      (head : WordConstructionStorage.Trace (environment [base, literal.1.val, entry])
        (occurrenceRecipes width literal.2 replacement) code first p)
      (remaining : OccurrenceTrace width base replacement (entry + 6) rest tail later q)
      (copied : CompilerAppendTrace.AppendTrace code tail (code ++ tail) code.length) :
      OccurrenceTrace width base replacement entry (literal :: rest) (code ++ tail)
        (first + later + 40) (max p (q + 16 * code.length + 32))

theorem occurrences_storage (width base : Nat) (replacement : Bool) (entry : Nat)
    (inputs : List (Literal (Fin count))) :
    ∃ peak, OccurrenceTrace width base replacement entry inputs
      (occurrences width base replacement entry inputs).1
      (occurrences width base replacement entry inputs).2 peak ∧
      peak ≤ 5000 * inputs.length + 32 := by
  induction inputs generalizing entry with
  | nil => exact ⟨32, .nil entry, by simp⟩
  | cons literal rest ih =>
      obtain ⟨p, formed, formBound⟩ := WordConstructionStorage.construction
        (environment [base, literal.1.val, entry]) (occurrenceRecipes width literal.2 replacement)
      obtain ⟨q, remaining, tailBound⟩ := ih (entry + 6)
      have amount : work (occurrenceRecipes width literal.2 replacement) = 60 := by
        simp [work, occurrenceRecipes, InstructionRecipe.work, Expression.work]
      have length : (evaluate (environment [base, literal.1.val, entry])
          (occurrenceRecipes width literal.2 replacement)).length = 6 := rfl
      refine ⟨_, .cons formed remaining (CompilerAppendTrace.append_exists _ _), ?_⟩
      simp only [length, amount] at formBound ⊢
      simp only [List.length_cons]
      exact Nat.max_le.mpr ⟨by omega, by omega⟩

def read (width base : Nat) (literal : Literal (Fin count)) : List (Instruction width 4) :=
  evaluate (environment [base, literal.1.val]) (readRecipes width literal.2)

def store (width : Nat) (phase : Bool) : List (Instruction width 4) :=
  evaluate (environment [0, 0]) (storeRecipes width phase)

def scan (width base entry : Nat) (inputs : List (Literal (Fin count)))
    (initial replacement phase : Bool) : List (Instruction width 4) × Nat :=
  let tail := occurrences width base replacement (entry + 1) inputs
  ([.constant 3 (boolWord width initial)] ++ tail.1 ++ store width phase, tail.2 + 100)

def unary (width base : Nat) (literal : Literal (Fin count)) (phase : Bool) : List (Instruction width 4) :=
  read width base literal ++ [.copy 3 1] ++ store width phase

def exclusive (width base : Nat) (left right : Literal (Fin count)) (phase : Bool) :
    List (Instruction width 4) :=
  read width base left ++ [.copy 3 1] ++ read width base right ++ [.xor 3 3 1] ++ store width phase

def form (width base entry : Nat) (phase : Bool) : Gate (Fin count) → List (Instruction width 4) × Nat
  | .and inputs => scan width base entry (inputs.map negate) true false phase
  | .or inputs => scan width base entry inputs false true phase
  | .xor left right => (exclusive width base left right phase, 300)
  | .alias literal => (unary width base literal phase, 200)
  | .not literal => (unary width base (negate literal) phase, 200)
  | .constant value => scan (count := count) width base entry [] value false phase

theorem scan_image (width base entry : Nat) (inputs : List (Literal (Fin count)))
    (initial replacement phase : Bool) :
    (scan width base entry inputs initial replacement phase).1 =
      NativeGateScan.code width base entry inputs initial replacement phase := by
  simp only [scan, occurrences_image, store, store_image, NativeGateScan.code, List.append_assoc]

theorem form_image (width base entry : Nat) (phase : Bool) (gate : Gate (Fin count)) :
    (form width base entry phase gate).1 = NativeGateExecution.code width base entry phase gate := by
  cases gate <;> simp only [form, scan_image, NativeGateExecution.code, unary, exclusive,
    read, read_image, store, store_image, NativeGateUnary.code, NativeGateXor.code, List.append_assoc]

theorem form_work (width base entry : Nat) (phase : Bool) (gate : Gate (Fin count)) :
    (form width base entry phase gate).2 ≤ 400 * (1 + gate.inputs.length) := by
  cases gate with
  | and inputs =>
      have bound := occurrences_work width base false (entry + 1) (inputs.map negate)
      simp only [form, scan, Gate.inputs, List.length_map] at *
      omega
  | or inputs =>
      have bound := occurrences_work width base true (entry + 1) inputs
      simp only [form, scan, Gate.inputs] at *
      omega
  | xor left right => simp [form, Gate.inputs]
  | «alias» literal => simp [form, Gate.inputs]
  | «not» literal => simp [form, Gate.inputs]
  | constant value => simp [form, scan, occurrences, Gate.inputs]

end Controller.Cost.NativeGateConstruction
