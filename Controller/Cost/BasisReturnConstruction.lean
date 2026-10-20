module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.BasisRootConstruction

@[expose] public section


/-! A proper-basis root verdict is followed by one explicit channel-word
emitter. Cached emission lengths determine the two success continuations. -/
namespace Controller.Cost.BasisReturnConstruction

open Controller Controller.Decoder Controller.Cost Controller.Extensions
open Controller.Extensions.LiteralWitnessEmit

def monotone (width b : Nat) (target : Channel n) (nodes base entry absent : Nat) : List
  (Instruction width 8) × Nat :=
  let full := entry + MonotoneReturn.rootSize b
  let first := WitnessEmissionConstruction.build width full (MonotoneReturn.operands true n)
  let single := full + first.1.length + 2
  let second := WitnessEmissionConstruction.build width single (MonotoneReturn.operands false n)
  let finish := single + second.1.length
  let root := BasisRootConstruction.monotone width b target nodes base entry absent full single
  let image := root ++ first.1 ++ [.constant 0 (word width 0), .branchZero 0 (word width finish)] ++
    second.1
  (image, first.2 + second.2 + 16 * image.length + 10000 + 1000 * n)

theorem monotone_image (width b : Nat) (target : Channel n) (nodes base entry absent : Nat) :
    (monotone width b target nodes base entry absent).1 = MonotoneReturn.code (width := width) b
      target nodes base entry absent := by
  simp only [monotone, WitnessEmissionConstruction.image, LiteralWitnessEmit.code_length,
    BasisRootConstruction.monotone_image, MonotoneReturn.code, MonotoneReturn.fullEntry,
    MonotoneReturn.singleEntry, MonotoneReturn.finish, LiteralWitnessReturn.jump, List.append_assoc]

def literal (width b : Nat) (target : Channel n) (nodes base entry absent : Nat) : List (Instruction
  width 8) × Nat :=
  let keep := entry + LiteralWitnessReturn.rootSize b
  let first := WitnessEmissionConstruction.build width keep (LiteralWitnessReturn.operands true b
    target nodes base)
  let single := keep + first.1.length + 2
  let second := WitnessEmissionConstruction.build width single (LiteralWitnessReturn.operands false
    b target nodes base)
  let finish := single + second.1.length
  let root := BasisRootConstruction.literal width b target nodes base entry absent keep single
  let image := root ++ first.1 ++ [.constant 0 (word width 0), .branchZero 0 (word width finish)] ++
    second.1
  (image, first.2 + second.2 + 16 * image.length + 10000 + 1000 * n)

theorem literal_image (width b : Nat) (target : Channel n) (nodes base entry absent : Nat) :
    (literal width b target nodes base entry absent).1 = LiteralWitnessReturn.code (width := width)
      b target nodes base entry absent := by
  simp only [literal, WitnessEmissionConstruction.image, LiteralWitnessEmit.code_length,
    BasisRootConstruction.literal_image, LiteralWitnessReturn.code, LiteralWitnessReturn.keepEntry,
    LiteralWitnessReturn.singleEntry, LiteralWitnessReturn.finish, LiteralWitnessReturn.jump,
      List.append_assoc]

theorem monotone_clock (width b : Nat) (target : Channel n) (nodes base entry absent : Nat) :
    (monotone width b target nodes base entry absent).2 ≤ 30000 * (n + 1) := by
  let full := entry + MonotoneReturn.rootSize b
  let first := WitnessEmissionConstruction.build width full (MonotoneReturn.operands true n)
  have head := WitnessEmissionConstruction.clock width full (MonotoneReturn.operands true n)
  have tail := WitnessEmissionConstruction.clock width (full + first.1.length + 2)
    (MonotoneReturn.operands false n)
  simp only [MonotoneReturn.operands_length] at head tail
  have length : (monotone width b target nodes base entry absent).1.length ≤ 35 + 18 * n := by
    rw [monotone_image]
    exact MonotoneReturn.code_length_bound b target nodes base entry absent
  change _ + _ + 16 * (monotone width b target nodes base entry absent).1.length + 10000 + 1000 * n
    ≤ _
  dsimp only [full, first] at *
  omega

theorem literal_clock (width b : Nat) (target : Channel n) (nodes base entry absent : Nat) :
    (literal width b target nodes base entry absent).2 ≤ 30000 * (n + 1) := by
  let keep := entry + LiteralWitnessReturn.rootSize b
  let first := WitnessEmissionConstruction.build width keep (LiteralWitnessReturn.operands true b
    target nodes base)
  have head := WitnessEmissionConstruction.clock width keep (LiteralWitnessReturn.operands true b
    target nodes base)
  have tail := WitnessEmissionConstruction.clock width (keep + first.1.length + 2)
    (LiteralWitnessReturn.operands false b target nodes base)
  simp only [LiteralWitnessReturn.operands_length] at head tail
  have length : (literal width b target nodes base entry absent).1.length ≤ 150 + 18 * n := by
    rw [literal_image]
    exact LiteralWitnessReturn.code_length_bound b target nodes base entry absent
  change _ + _ + 16 * (literal width b target nodes base entry absent).1.length + 10000 + 1000 * n ≤
    _
  dsimp only [keep, first] at *
  omega

end Controller.Cost.BasisReturnConstruction
