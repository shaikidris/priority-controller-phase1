module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.AssemblyStorage
public import Controller.Cost.BasisOutputConstruction

@[expose] public section


/-! Source-indexed proper-basis witness and root schedules. Values are emitted
by fetched loads; instruction construction uses only offsets and channel IDs. -/
namespace Controller.Cost.BasisOutputStorage

open Controller Controller.Decoder Controller.Cost Controller.Extensions
open Controller.Cost.WordConstructionRecipe Controller.Cost.ProperBasisConstructionRecipes
open Controller.Cost.ForestClauseProgramConstruction (environment)
open Controller.Cost.AssemblyStorage

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
attribute [local irreducible] BasisReturnConstruction.monotone BasisReturnConstruction.literal
  BasisRootConstruction.monotone BasisRootConstruction.literal

theorem operand (width entry : Nat) (value : LiteralWitnessEmit.Operand) :
    Bounded (WitnessEmissionConstruction.operand width entry value).1 5000 := by
  cases value with
  | one => exact .enlarge (wordCode _ _) (by rw [emitOne.constructionRecipe_work]; decide)
  | stored offset =>
      exact .enlarge (wordCode _ _) (by rw [emitStored.constructionRecipe_work]; decide)
  | selected channel =>
      exact .enlarge (wordCode _ _) (by rw [emitSelected.constructionRecipe_work]; decide)

theorem witness (width entry : Nat) (values : List LiteralWitnessEmit.Operand) :
    Bounded (WitnessEmissionConstruction.build width entry values).1 (6000 * values.length) := by
  induction values generalizing entry with
  | nil => exact .empty
  | cons value rest ih =>
      have first := operand width entry value
      have tail := ih (entry + (WitnessEmissionConstruction.operand width entry value).1.length)
      have assembled := join first tail
      have length : (WitnessEmissionConstruction.operand width entry value).1.length ≤ 9 := by
        rw [WitnessEmissionConstruction.operand_image, LiteralWitnessEmit.operandCode_length]
        cases value <;> simp [LiteralWitnessEmit.operandSize]
      exact .enlarge assembled (by simp only [List.length_cons]; omega)

theorem monotoneRoot (width b : Nat) (target : Channel n)
    (nodes base entry absent full single : Nat) :
    Bounded (BasisRootConstruction.monotone width b target nodes base entry absent full single)
      100000 := by
  unfold BasisRootConstruction.monotone
  split
  · exact .enlarge (wordCode _ _) (by rw [monotoneOne.constructionRecipe_work]; decide)
  · exact .enlarge (wordCode _ _) (by rw [monotoneMany.constructionRecipe_work]; decide)

theorem literalRoot (width b : Nat) (target : Channel n)
    (nodes base entry absent keep single : Nat) :
    Bounded (BasisRootConstruction.literal width b target nodes base entry absent keep single)
      100000 := by
  let otherChannel := if target.val = 0 then 1 else 0
  let destination := if b ≠ 1 ∧ 2 ≤ n then single else absent
  let tailEntry := LiteralRootRun.unhealthyEntry entry + 22
  have first := wordCode (width := width)
    (environment [n, target.val, nodes, base, entry, absent, single, destination, otherChannel])
    (literalPrefix.constructionRecipe width)
  have tail : Bounded (if b = 1 then
      evaluate (environment [n, target.val, nodes, base, tailEntry, absent, keep])
        (literalOneTail.constructionRecipe width)
    else evaluate (environment [n, nodes, base, tailEntry, absent, keep, single])
        (literalManyTail.constructionRecipe width)) 50000 := by
    split
    · exact .enlarge (wordCode _ _) (by rw [literalOneTail.constructionRecipe_work]; decide)
    · exact .enlarge (wordCode _ _) (by rw [literalManyTail.constructionRecipe_work]; decide)
  have assembled := join first tail
  unfold BasisRootConstruction.literal
  dsimp only
  exact .enlarge assembled (by
    simp only [literalPrefix.constructionRecipe_work, evaluate, List.length_map]
    have length : (literalPrefix.constructionRecipe width).length = 106 := rfl
    rw [length]
    decide)

theorem monotoneReturn (width b : Nat) (target : Channel n) (nodes base entry absent : Nat) :
    Bounded (BasisReturnConstruction.monotone width b target nodes base entry absent).1
      (200000 * (n + 1)) := by
  let full := entry + MonotoneReturn.rootSize b
  let first := WitnessEmissionConstruction.build width full (MonotoneReturn.operands true n)
  let single := full + first.1.length + 2
  let second := WitnessEmissionConstruction.build width single (MonotoneReturn.operands false n)
  let finish := single + second.1.length
  have root := monotoneRoot width b target nodes base entry absent full single
  have one := witness width full (MonotoneReturn.operands true n)
  have two := witness width single (MonotoneReturn.operands false n)
  have jump := join (constant (width := width) (registers := 8) 0 0)
    (branch (width := width) (registers := 8) 0 finish)
  have assembled := join (join (join root one) jump) two
  have rootLength : (BasisRootConstruction.monotone width b target nodes base entry absent full
      single).length ≤ 33 := by
    rw [BasisRootConstruction.monotone_image, MonotoneRoot.code_length]
    split <;> omega
  have firstLength : first.1.length ≤ 9 * n := by
    dsimp only [first]
    rw [WitnessEmissionConstruction.image, LiteralWitnessEmit.code_length]
    simpa only [MonotoneReturn.operands_length] using
      LiteralWitnessEmit.size_bound (MonotoneReturn.operands true n)
  unfold BasisReturnConstruction.monotone
  dsimp only
  exact .enlarge assembled (by
    simp only [List.length_append, List.length_cons, List.length_nil,
        MonotoneReturn.operands_length]
    dsimp only [first, full, single, second, finish] at *
    omega)

theorem literalReturn (width b : Nat) (target : Channel n) (nodes base entry absent : Nat) :
    Bounded (BasisReturnConstruction.literal width b target nodes base entry absent).1
      (200000 * (n + 1)) := by
  let keep := entry + LiteralWitnessReturn.rootSize b
  let first := WitnessEmissionConstruction.build width keep
    (LiteralWitnessReturn.operands true b target nodes base)
  let single := keep + first.1.length + 2
  let second := WitnessEmissionConstruction.build width single
    (LiteralWitnessReturn.operands false b target nodes base)
  let finish := single + second.1.length
  have root := literalRoot width b target nodes base entry absent keep single
  have one := witness width keep (LiteralWitnessReturn.operands true b target nodes base)
  have two := witness width single (LiteralWitnessReturn.operands false b target nodes base)
  have jump := join (constant (width := width) (registers := 8) 0 0)
    (branch (width := width) (registers := 8) 0 finish)
  have assembled := join (join (join root one) jump) two
  have rootLength : (BasisRootConstruction.literal width b target nodes base entry absent keep
      single).length ≤ 148 := by
    rw [BasisRootConstruction.literal_image, LiteralWitnessReturn.root_code_length]
    unfold LiteralWitnessReturn.rootSize
    split <;> omega
  have firstLength : first.1.length ≤ 9 * n := by
    dsimp only [first]
    rw [WitnessEmissionConstruction.image, LiteralWitnessEmit.code_length]
    simpa only [LiteralWitnessReturn.operands_length] using
      LiteralWitnessEmit.size_bound (LiteralWitnessReturn.operands true b target nodes base)
  unfold BasisReturnConstruction.literal
  dsimp only
  exact .enlarge assembled (by
    simp only [List.length_append, List.length_cons, List.length_nil,
      LiteralWitnessReturn.operands_length]
    dsimp only [first, keep, single, second, finish] at *
    omega)


theorem read (width cursor : Nat) :
    Bounded ([.constant 3 (word width cursor), .load 4 3] : List (Instruction width 8)) 1000 :=
  .enlarge (join (constant 3 cursor) (fixed (.load 4 3) (by trivial))) (by
    simp only [List.length_cons, List.length_nil]
    omega)

theorem jump (width target : Nat) :
    Bounded ([.constant 0 (word width 0), .branchZero 0 (word width target)] :
      List (Instruction width 8)) 1000 :=
  .enlarge (join (constant 0 0) (branch 0 target)) (by
    simp only [List.length_cons, List.length_nil]
    omega)

theorem monotone (width b : Nat) (target : Channel n)
    (nodes base found absent count entry cursor : Nat) :
    Bounded (BasisOutputConstruction.monotone width b target nodes base found absent count entry
      cursor).1 (300000 * count * (n + 1) + 1000) := by
  induction count generalizing entry cursor with
  | zero =>
      simpa only [BasisOutputConstruction.monotone, BasisOutputConstruction.literal,
        Nat.mul_zero, Nat.zero_mul, Nat.zero_add] using jump width absent
  | succ count ih =>
      let stride := MonotoneOutputSearch.stride b n
      have first := read width cursor
      have returned := monotoneReturn width b target nodes base (entry + 2) (entry + stride)
      have next := jump width found
      have tail := ih (entry + stride) (cursor + 1)
      have assembled := join (join (join first returned) next) tail
      have length : (BasisReturnConstruction.monotone width b target nodes base (entry + 2)
          (entry + stride)).1.length ≤ 35 + 18 * n := by
        rw [BasisReturnConstruction.monotone_image]
        exact MonotoneReturn.code_length_bound b target nodes base (entry + 2) (entry + stride)
      dsimp only [BasisOutputConstruction.monotone]
      exact .enlarge assembled (by
        simp only [List.length_append, List.length_cons, List.length_nil]
        nlinarith)

theorem literal (width b : Nat) (target : Channel n)
    (nodes base found absent count entry cursor : Nat) :
    Bounded (BasisOutputConstruction.literal width b target nodes base found absent count entry
      cursor).1 (300000 * count * (n + 1) + 1000) := by
  induction count generalizing entry cursor with
  | zero =>
      simpa only [BasisOutputConstruction.monotone, BasisOutputConstruction.literal,
        Nat.mul_zero, Nat.zero_mul, Nat.zero_add] using jump width absent
  | succ count ih =>
      let stride := LiteralOutputSearch.stride b target nodes base
      have first := read width cursor
      have returned := literalReturn width b target nodes base (entry + 2) (entry + stride)
      have next := jump width found
      have tail := ih (entry + stride) (cursor + 1)
      have assembled := join (join (join first returned) next) tail
      have length : (BasisReturnConstruction.literal width b target nodes base (entry + 2)
          (entry + stride)).1.length ≤ 150 + 18 * n := by
        rw [BasisReturnConstruction.literal_image]
        exact LiteralWitnessReturn.code_length_bound b target nodes base (entry + 2) (entry +
            stride)
      dsimp only [BasisOutputConstruction.literal]
      exact .enlarge assembled (by
        simp only [List.length_append, List.length_cons, List.length_nil]
        nlinarith)

end Controller.Cost.BasisOutputStorage
