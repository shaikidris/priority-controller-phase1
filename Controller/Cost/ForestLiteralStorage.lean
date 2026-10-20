module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ForestQueryConstruction
public import Controller.Cost.WordConstructionStorage

@[expose] public section


/-! Transient construction storage for the source-literal instruction stream.
Literal formation uses the checked first-order recipes. Continuations retain
only the current bounded code block and scalar placement operands. -/
namespace Controller.Cost.ForestLiteralStorage

open Controller.Cost Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestQueryConstruction

inductive Trace (width : Nat) : Nat → List (Reference ambient) →
    List (Instruction width 4) → Nat → Nat → Prop
  | nil (base) : Trace width base [] [] 1 32
  | cons {base reference rest code output formed later literalPeak tailPeak}
      (literal : WordConstructionStorage.Trace (literalEnvironment base reference.slot)
        (literalRecipes width reference.activity reference.positive) code formed literalPeak)
      (tail : Trace width (base + code.length) rest output later tailPeak)
      (copied : CompilerAppendTrace.AppendTrace code output (code ++ output) code.length) :
      Trace width base (reference :: rest) (code ++ output) (formed + code.length + later + 20)
        (max literalPeak (tailPeak + 16 * code.length + 32))

theorem construction (width base : Nat) (references : List (Reference ambient)) :
    ∃ peak, Trace width base references (emit width base references).1 (emit width base references).2 peak ∧
      peak ≤ 64 * (emit width base references).2 := by
  induction references generalizing base with
  | nil => exact ⟨32, .nil base, by simp [emit]⟩
  | cons reference rest ih =>
      let recipes := literalRecipes width reference.activity reference.positive
      let current := evaluate (literalEnvironment base reference.slot) recipes
      obtain ⟨literalPeak, literalTrace, literalBound⟩ :=
        WordConstructionStorage.construction (literalEnvironment base reference.slot) recipes
      obtain ⟨tailPeak, tailTrace, tailBound⟩ := ih (base + current.length)
      refine ⟨max literalPeak (tailPeak + 16 * current.length + 32), ?_, ?_⟩
      · exact .cons literalTrace tailTrace (CompilerAppendTrace.append_exists _ _)
      · change max literalPeak (tailPeak + 16 * current.length + 32) ≤
          64 * (work recipes + current.length + (emit width (base + current.length) rest).2 + 20)
        exact Nat.max_le.mpr ⟨by omega, by omega⟩

/-- Code buffers, backing words and literal-map continuations have a linear
peak in the original source-literal count. -/
theorem bound (width base : Nat) (references : List (Reference ambient)) :
    ∃ peak, Trace width base references (emit width base references).1 (emit width base references).2 peak ∧
      peak ≤ 21000 * references.length + 64 := by
  obtain ⟨peak, trace, space⟩ := construction width base references
  have clock := emit_work width base references
  exact ⟨peak, trace, by omega⟩

end Controller.Cost.ForestLiteralStorage
