module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ForestZeroResident

@[expose] public section


/-! First-order word-construction recipes. Instance-dependent operands are
read from an explicit finite environment and formed using the displayed
arithmetic operations. Recipe syntax has no function-call or oracle node.
Architecture constants may depend on the fixed word width. -/
namespace Controller.Cost.WordConstructionRecipe

inductive Expression (parameters : Nat) where
  | literal (value : Nat)
  | parameter (index : Fin parameters)
  | add (left right : Expression parameters)
  | sub (left right : Expression parameters)
  | mul (left right : Expression parameters)
  deriving Repr

def Expression.eval (environment : Fin parameters → Nat) : Expression parameters → Nat
  | .literal value => value
  | .parameter index => environment index
  | .add left right => left.eval environment + right.eval environment
  | .sub left right => left.eval environment - right.eval environment
  | .mul left right => left.eval environment * right.eval environment

def Expression.work : Expression parameters → Nat
  | .literal _ => 1
  | .parameter _ => 1
  | .add left right | .sub left right | .mul left right => left.work + right.work + 1

inductive Arithmetic (environment : Fin parameters → Nat) : Expression parameters → Nat → Nat → Prop
  | literal (value) : Arithmetic environment (.literal value) value 1
  | read (index) : Arithmetic environment (.parameter index) (environment index) 1
  | add {left right x y a b} (first : Arithmetic environment left x a)
      (second : Arithmetic environment right y b) : Arithmetic environment (.add left right) (x + y) (a + b + 1)
  | sub {left right x y a b} (first : Arithmetic environment left x a)
      (second : Arithmetic environment right y b) : Arithmetic environment (.sub left right) (x - y) (a + b + 1)
  | mul {left right x y a b} (first : Arithmetic environment left x a)
      (second : Arithmetic environment right y b) : Arithmetic environment (.mul left right) (x * y) (a + b + 1)

theorem arithmetic (environment : Fin parameters → Nat) (expression : Expression parameters) :
    Arithmetic environment expression (expression.eval environment) expression.work := by
  induction expression with
  | literal value => exact .literal value
  | parameter index => exact .read index
  | add left right first second => exact .add first second
  | sub left right first second => exact .sub first second
  | mul left right first second => exact .mul first second

inductive InstructionRecipe (parameters width registers : Nat) where
  | plain (instruction : Instruction width registers)
  | constant (destination : Fin registers) (value : Expression parameters)
  | branchZero (source : Fin registers) (target : Expression parameters)

def InstructionRecipe.eval (environment : Fin parameters → Nat) :
    InstructionRecipe parameters width registers → Instruction width registers
  | .plain instruction => instruction
  | .constant destination value => .constant destination (word width (value.eval environment))
  | .branchZero source target => .branchZero source (word width (target.eval environment))

def InstructionRecipe.work : InstructionRecipe parameters width registers → Nat
  | .plain _ => 8
  | .constant _ expression | .branchZero _ expression => expression.work + 9

/-- A recipe evaluation includes operand arithmetic, word packing, four field
formation/copy operations and four backing writes for each instruction. -/
inductive Formation (environment : Fin parameters → Nat) :
    InstructionRecipe parameters width registers → Instruction width registers → Nat → Prop
  | plain (instruction : Instruction width registers)
      (fields : ForestZeroResident.FormationTrace (ForestZeroResident.instructionInputs instruction)
        (ForestZeroResident.instructionFields instruction) 4) :
      Formation environment (.plain instruction) instruction 8
  | constant (destination : Fin registers) (expression : Expression parameters) (value ticks)
      (operand : Arithmetic environment expression value ticks)
      (fields : ForestZeroResident.FormationTrace
        (ForestZeroResident.instructionInputs (.constant destination (word width value)))
        (ForestZeroResident.instructionFields (.constant destination (word width value))) 4) :
      Formation environment (.constant destination expression) (.constant destination (word width value)) (ticks + 9)
  | branchZero (source : Fin registers) (expression : Expression parameters) (value ticks)
      (operand : Arithmetic environment expression value ticks)
      (fields : ForestZeroResident.FormationTrace
        (ForestZeroResident.instructionInputs (.branchZero source (word width value)))
        (ForestZeroResident.instructionFields (.branchZero source (word width value))) 4) :
      Formation environment (.branchZero source expression) (.branchZero source (word width value)) (ticks + 9)

theorem instruction_formation (environment : Fin parameters → Nat)
    (recipe : InstructionRecipe parameters width registers) :
    Formation environment recipe (recipe.eval environment) recipe.work := by
  cases recipe with
  | plain instruction => exact .plain instruction (ForestZeroResident.instruction_formation instruction)
  | constant destination expression =>
      exact .constant destination expression _ _ (arithmetic environment expression)
        (ForestZeroResident.instruction_formation _)
  | branchZero source expression =>
      exact .branchZero source expression _ _ (arithmetic environment expression)
        (ForestZeroResident.instruction_formation _)

def evaluate (environment : Fin parameters → Nat) (recipes : List (InstructionRecipe parameters width registers)) :
    List (Instruction width registers) := recipes.map (InstructionRecipe.eval environment)

def work (recipes : List (InstructionRecipe parameters width registers)) : Nat :=
  (recipes.map InstructionRecipe.work).sum

theorem evaluate_append (environment : Fin parameters → Nat)
    (left right : List (InstructionRecipe parameters width registers)) :
    evaluate environment (left ++ right) = evaluate environment left ++ evaluate environment right := by
  exact List.map_append

theorem work_append (left right : List (InstructionRecipe parameters width registers)) :
    work (left ++ right) = work left + work right := by
  simp only [work, List.map_append, List.sum_append]

theorem evaluate_flatten (environment : Fin parameters → Nat)
    (blocks : List (List (InstructionRecipe parameters width registers))) :
    evaluate environment blocks.flatten = (blocks.map (evaluate environment)).flatten := by
  induction blocks with
  | nil => rfl
  | cons block rest ih => simp only [List.flatten_cons, evaluate_append, List.map_cons, ih]

theorem work_flatten (blocks : List (List (InstructionRecipe parameters width registers))) :
    work blocks.flatten = (blocks.map work).sum := by
  induction blocks with
  | nil => rfl
  | cons block rest ih => simp only [List.flatten_cons, work_append, List.map_cons, List.sum_cons, ih]

inductive Trace (environment : Fin parameters → Nat) :
    List (InstructionRecipe parameters width registers) → List (Instruction width registers) → Nat → Prop
  | nil : Trace environment [] [] 0
  | cons {recipe rest instruction tail first later}
      (formed : Formation environment recipe instruction first)
      (remaining : Trace environment rest tail later) :
      Trace environment (recipe :: rest) (instruction :: tail) (first + later)

theorem trace (environment : Fin parameters → Nat) (recipes : List (InstructionRecipe parameters width registers)) :
    Trace environment recipes (evaluate environment recipes) (work recipes) := by
  induction recipes with
  | nil => exact .nil
  | cons recipe rest ih => exact .cons (instruction_formation environment recipe) ih

/-- Backing writes operate on the exact formed output stream. The initial
backing is retained, and every resulting instruction has four packed fields. -/
theorem backing (environment : Fin parameters → Nat)
    (recipes : List (InstructionRecipe parameters width registers)) (initial : Array (Word width)) :
    Trace environment recipes (evaluate environment recipes) (work recipes) ∧
      ForestZeroResident.BackingTrace (evaluate environment recipes) initial
        (ForestZeroResident.backing (evaluate environment recipes) initial)
        (4 * recipes.length) (4 * recipes.length) := by
  refine ⟨trace environment recipes, ?_⟩
  simpa only [evaluate, List.length_map] using
    ForestZeroResident.backing_trace (evaluate environment recipes) initial

end Controller.Cost.WordConstructionRecipe
