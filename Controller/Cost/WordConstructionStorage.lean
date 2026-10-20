module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.WordConstructionRecipe

@[expose] public section


/-! Construction storage for first-order instruction recipes. Environments and
recipe syntax are read-only inputs. The measure counts temporary operand/control
words, newly formed instruction backing and output-list cells. -/
namespace Controller.Cost.WordConstructionStorage

open Controller.Cost Controller.Cost.WordConstructionRecipe

/-- An arithmetic continuation has four control words and at most one saved
left operand. Each rule evaluates the same first-order expression as `eval`. -/
inductive ArithmeticStorage (environment : Fin parameters → Nat) :
    Expression parameters → Nat → Nat → Nat → Prop
  | literal (value) : ArithmeticStorage environment (.literal value) value 1 1
  | read (index) : ArithmeticStorage environment (.parameter index) (environment index) 1 1
  | add {left right x y a b p q}
      (first : ArithmeticStorage environment left x a p)
      (second : ArithmeticStorage environment right y b q) :
      ArithmeticStorage environment (.add left right) (x + y) (a + b + 1) (max (p + 4) (q + 5))
  | sub {left right x y a b p q}
      (first : ArithmeticStorage environment left x a p)
      (second : ArithmeticStorage environment right y b q) :
      ArithmeticStorage environment (.sub left right) (x - y) (a + b + 1) (max (p + 4) (q + 5))
  | mul {left right x y a b p q}
      (first : ArithmeticStorage environment left x a p)
      (second : ArithmeticStorage environment right y b q) :
      ArithmeticStorage environment (.mul left right) (x * y) (a + b + 1) (max (p + 4) (q + 5))

theorem arithmetic (environment : Fin parameters → Nat) (expression : Expression parameters) :
    ∃ peak, ArithmeticStorage environment expression (expression.eval environment) expression.work peak ∧
      peak ≤ 8 * expression.work := by
  induction expression with
  | literal value => exact ⟨1, .literal value, by simp [Expression.work]⟩
  | parameter index => exact ⟨1, .read index, by simp [Expression.work]⟩
  | add left right ihLeft ihRight | sub left right ihLeft ihRight | mul left right ihLeft ihRight =>
      obtain ⟨p, first, firstBound⟩ := ihLeft
      obtain ⟨q, second, secondBound⟩ := ihRight
      refine ⟨max (p + 4) (q + 5), ?_, ?_⟩
      first | exact .add first second | exact .sub first second | exact .mul first second
      all_goals
        simp only [Expression.work]
        exact Nat.max_le.mpr ⟨by omega, by omega⟩

/-- Formation includes four backing words, six output/control words and the
operand evaluator's peak. Plain recipes have no dynamic operand traversal. -/
inductive InstructionStorage (environment : Fin parameters → Nat) :
    InstructionRecipe parameters width registers → Instruction width registers → Nat → Nat → Prop
  | plain (instruction) : InstructionStorage environment (.plain instruction) instruction 8 10
  | constant (destination expression value ticks peak)
      (operand : ArithmeticStorage environment expression value ticks peak) :
      InstructionStorage environment (.constant destination expression) (.constant destination (word width value))
        (ticks + 9) (peak + 10)
  | branchZero (source expression value ticks peak)
      (operand : ArithmeticStorage environment expression value ticks peak) :
      InstructionStorage environment (.branchZero source expression) (.branchZero source (word width value))
        (ticks + 9) (peak + 10)

theorem instruction (environment : Fin parameters → Nat)
    (recipe : InstructionRecipe parameters width registers) :
    ∃ peak, InstructionStorage environment recipe (recipe.eval environment) recipe.work peak ∧
      peak ≤ 16 * recipe.work := by
  cases recipe with
  | plain code => exact ⟨10, .plain code, by simp [InstructionRecipe.work]⟩
  | constant destination expression =>
      obtain ⟨peak, trace, bound⟩ := arithmetic environment expression
      exact ⟨peak + 10, .constant destination expression _ _ _ trace, by simp only [InstructionRecipe.work]; omega⟩
  | branchZero source expression =>
      obtain ⟨peak, trace, bound⟩ := arithmetic environment expression
      exact ⟨peak + 10, .branchZero source expression _ _ _ trace, by simp only [InstructionRecipe.work]; omega⟩

/-- Pending recipe syntax is shared input. A formed head and its map
continuation retain at most sixteen additional words during the tail call. -/
inductive Trace (environment : Fin parameters → Nat) :
    List (InstructionRecipe parameters width registers) → List (Instruction width registers) → Nat → Nat → Prop
  | nil : Trace environment [] [] 0 0
  | cons {recipe code ticks peak recipes output restTicks restPeak}
      (head : InstructionStorage environment recipe code ticks peak)
      (tail : Trace environment recipes output restTicks restPeak) :
      Trace environment (recipe :: recipes) (code :: output) (ticks + restTicks)
        (max peak (restPeak + 16))

theorem construction (environment : Fin parameters → Nat)
    (recipes : List (InstructionRecipe parameters width registers)) :
    ∃ peak, Trace environment recipes (evaluate environment recipes) (work recipes) peak ∧
      peak ≤ 32 * work recipes := by
  induction recipes with
  | nil => exact ⟨0, .nil, by simp [work]⟩
  | cons recipe recipes ih =>
      obtain ⟨onePeak, one, oneBound⟩ := instruction environment recipe
      obtain ⟨restPeak, tail, tailBound⟩ := ih
      have positive : 1 ≤ recipe.work := by
        cases recipe <;> simp [InstructionRecipe.work]
      refine ⟨max onePeak (restPeak + 16), ?_, ?_⟩
      · simpa only [evaluate, List.map_cons, work, List.sum_cons] using Trace.cons one tail
      · simp only [work, List.map_cons, List.sum_cons]
        change max onePeak (restPeak + 16) ≤ 32 * (recipe.work + work recipes)
        exact Nat.max_le.mpr ⟨by omega, by omega⟩

end Controller.Cost.WordConstructionStorage
