/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.BasisReturnConstruction

/-! Root occurrences share a proper-basis table. The schedule depends on the
root count and source directory cursor, with one explicit witness emitter. -/
namespace Controller.Cost.BasisOutputConstruction

open Controller Controller.Decoder Controller.Cost Controller.Extensions

def monotone (width b : Nat) (target : Channel n) (nodes base found absent : Nat) : Nat → Nat → Nat
  → List (Instruction width 8) × Nat
  | 0, _, _ => ([.constant 0 (word width 0), .branchZero 0 (word width absent)], 32)
  | count + 1, entry, cursor =>
      let stride := MonotoneOutputSearch.stride b n
      let head := BasisReturnConstruction.monotone width b target nodes base (entry + 2) (entry +
        stride)
      let tail := monotone width b target nodes base found absent count (entry + stride) (cursor +
        1)
      let image := [.constant 3 (word width cursor), .load 4 3] ++ head.1 ++
        [.constant 0 (word width 0), .branchZero 0 (word width found)] ++ tail.1
      (image, head.2 + tail.2 + 16 * head.1.length + 1000 * (n + 1))

theorem monotone_image (width b : Nat) (target : Channel n) (nodes base found absent count entry
  cursor : Nat) :
    (monotone width b target nodes base found absent count entry cursor).1 =
      MonotoneOutputSearch.code (width := width) b target nodes base found absent count entry cursor
        := by
  induction count generalizing entry cursor with
  | zero => rfl
  | succ count ih =>
      simp only [monotone, BasisReturnConstruction.monotone_image, ih, MonotoneOutputSearch.code,
        LiteralOutputSearch.readCode, LiteralWitnessReturn.jump, List.append_assoc]

def literal (width b : Nat) (target : Channel n) (nodes base found absent : Nat) : Nat → Nat → Nat →
  List (Instruction width 8) × Nat
  | 0, _, _ => ([.constant 0 (word width 0), .branchZero 0 (word width absent)], 32)
  | count + 1, entry, cursor =>
      let stride := LiteralOutputSearch.stride b target nodes base
      let head := BasisReturnConstruction.literal width b target nodes base (entry + 2) (entry +
        stride)
      let tail := literal width b target nodes base found absent count (entry + stride) (cursor + 1)
      let image := [.constant 3 (word width cursor), .load 4 3] ++ head.1 ++
        [.constant 0 (word width 0), .branchZero 0 (word width found)] ++ tail.1
      (image, head.2 + tail.2 + 16 * head.1.length + 1000 * (n + 1))

theorem literal_image (width b : Nat) (target : Channel n) (nodes base found absent count entry
  cursor : Nat) :
    (literal width b target nodes base found absent count entry cursor).1 =
      LiteralOutputSearch.code (width := width) b target nodes base found absent count entry cursor
        := by
  induction count generalizing entry cursor with
  | zero => rfl
  | succ count ih =>
      simp only [literal, BasisReturnConstruction.literal_image, ih, LiteralOutputSearch.code,
        LiteralOutputSearch.readCode, LiteralWitnessReturn.jump, List.append_assoc]

theorem monotone_clock (width b : Nat) (target : Channel n) (nodes base found absent count entry
  cursor : Nat) :
    (monotone width b target nodes base found absent count entry cursor).2 ≤ 100000 * count * (n +
      1) + 32 := by
  induction count generalizing entry cursor with
  | zero => simp [monotone]
  | succ count ih =>
      have head := BasisReturnConstruction.monotone_clock width b target nodes base (entry + 2)
        (entry + MonotoneOutputSearch.stride b n)
      have length : (BasisReturnConstruction.monotone width b target nodes base (entry + 2) (entry +
        MonotoneOutputSearch.stride b n)).1.length ≤ 35 + 18 * n := by
        rw [BasisReturnConstruction.monotone_image]
        exact MonotoneReturn.code_length_bound _ _ _ _ _ _
      have tail := ih (entry + MonotoneOutputSearch.stride b n) (cursor + 1)
      simp only [monotone]
      nlinarith

theorem literal_clock (width b : Nat) (target : Channel n) (nodes base found absent count entry
  cursor : Nat) :
    (literal width b target nodes base found absent count entry cursor).2 ≤ 100000 * count * (n + 1)
      + 32 := by
  induction count generalizing entry cursor with
  | zero => simp [literal]
  | succ count ih =>
      have head := BasisReturnConstruction.literal_clock width b target nodes base (entry + 2)
        (entry + LiteralOutputSearch.stride b target nodes base)
      have length : (BasisReturnConstruction.literal width b target nodes base (entry + 2) (entry +
        LiteralOutputSearch.stride b target nodes base)).1.length ≤ 150 + 18 * n := by
        rw [BasisReturnConstruction.literal_image]
        exact LiteralWitnessReturn.code_length_bound _ _ _ _ _ _
      have tail := ih (entry + LiteralOutputSearch.stride b target nodes base) (cursor + 1)
      simp only [literal]
      nlinarith

end Controller.Cost.BasisOutputConstruction
