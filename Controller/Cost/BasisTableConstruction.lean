/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.BasisConflictConstruction
import Controller.Cost.StackPacketConstruction

/-! Proper-basis table images are constructed from original source counts.
Matrix allocation uses its arithmetic dimensions; no matrix value is evaluated
while computing instruction addresses or instruction counts. -/
namespace Controller.Cost.BasisTableConstruction

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Cost.ForestIndexedOperands Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestClauseProgramConstruction (environment)

def seedCode (width value : Nat) : List (Instruction width 8) := [.constant 3 (word width value),
  .push 3]

def writeCode (width address : Nat) : List (Instruction width 8) := [.constant 0 (word width
  address), .pop 1, .store 0 1]

derive_extension_recipe seedCode

derive_extension_recipe writeCode

def seed (width value : Nat) : Nat → List (Instruction width 8) × Nat
  | 0 => ([], 1)
  | count + 1 =>
      let tail := seed width value count
      (evaluate (environment [value]) (seedCode.constructionRecipe width) ++ tail.1, tail.2 + 100)

theorem seed_image (width value count : Nat) :
    (seed width value count).1 = SharedWitnessSeed.code width (word width value) count := by
  have formed : evaluate (environment [value]) (seedCode.constructionRecipe width) = seedCode width
    value := seedCode.constructionRecipe_eq width value
  induction count with
  | zero => rfl
  | succ count ih => simp only [seed, formed, seedCode, ih, SharedWitnessSeed.code]

def writes (width base : Nat) : List (Fin n) → List (Instruction width 8) × Nat
  | [] => ([], 1)
  | channel :: rest =>
      let tail := writes width base rest
      (evaluate (environment [base + channel.val]) (writeCode.constructionRecipe width) ++ tail.1,
        tail.2 + 100)

theorem writes_image (width base : Nat) (channels : List (Fin n)) :
    (writes width base channels).1 = SharedChannelRewrite.code width base channels := by
  have formed (channel : Fin n) : evaluate (environment [base + channel.val])
    (writeCode.constructionRecipe width) = writeCode width (base + channel.val) :=
    writeCode.constructionRecipe_eq width (base + channel.val)
  induction channels with
  | nil => rfl
  | cons channel rest ih => simp only [writes, formed, writeCode, ih, SharedChannelRewrite.code]

def rewrite (width n : Nat) (rows : List Row) (roots : List Nat) (value : Bool) : List (Instruction
  width 8) × Nat :=
  let base := (cacheHeap width (UniformDAGRun.packetHeaderHeap width n rows roots) rows roots).size
  let seeded := seed width (if value then 1 else 0) n
  let written := writes width base (List.finRange n)
  (seeded.1 ++ written.1, seeded.2 + written.2 + 1000 * (base + n + 1))

theorem rewrite_image (width n : Nat) (rows : List Row) (roots : List Nat) (value : Bool) :
    (rewrite width n rows roots value).1 = MonotoneTableConstruction.rewriteCode width n rows roots
      value := by
  cases value <;> simp only [rewrite, seed_image, writes_image,
    MonotoneTableConstruction.rewriteCode,
    Bool.false_eq_true, if_false, if_true, Controller.Cost.boolWord]

def monotone (graph : DAG n) (width : Nat) (rows : List Row) (roots : List Nat) (entry : Nat) : List
  (Instruction width 8) × Nat :=
  let columns := BasisColumnConstruction.build none width n rows roots entry (List.finRange n)
  let full := rewrite width n rows roots true
  let probe := BasisProbeConstruction.monotone width n rows roots (entry + 157 * n) (entry + 157 * n
    + 143)
  let reset := rewrite width n rows roots false
  let park := StackPacketConstruction.park width 0 ((n + 1) * graph.nodeCount)
  let image := columns.1 ++ full.1 ++ probe.1 ++ reset.1 ++ park.1
  (image, columns.2 + full.2 + probe.2 + reset.2 + park.2 + 16 * image.length + 1000 * (n + 1))

theorem monotone_image (graph : DAG n) (width : Nat) (rows : List Row) (roots : List Nat) (entry :
  Nat) :
    (monotone graph width rows roots entry).1 = (MonotoneTableConstruction.code graph width rows
      roots entry).toList := by
  simp only [monotone, BasisColumnConstruction.monotone_image, rewrite_image,
    BasisProbeConstruction.monotone_image,
    StackPacketConstruction.park_image, MonotoneTableConstruction.code, Array.toList_append,
    List.toList_toArray, MonotoneTableConstruction.matrix_length, List.append_assoc]

def literal (graph : DAG n) (width : Nat) (rows : List Row) (roots : List Nat) (entry sourceSize :
  Nat) : List (Instruction width 8) × Nat :=
  let positive := BasisColumnConstruction.build (some .positive) width n rows roots entry
    (List.finRange n)
  let negative := BasisColumnConstruction.build (some .negative) width n rows roots (entry + 143 *
    n) (List.finRange n)
  let zero := BasisProbeConstruction.literal .zero width n rows roots (entry + 286 * n) (entry + 286
    * n + 134)
  let size := (2 * n + 1) * graph.nodeCount
  let park := StackPacketConstruction.park width 0 size
  let jobs := LiteralSourceConstruction.jobs graph sourceSize
  let flags := BasisConflictConstruction.build width (entry + (286 * n + 134) + 2 * size)
    (sourceSize + size) jobs
  let image := positive.1 ++ negative.1 ++ zero.1 ++ park.1 ++ flags.1
  (image, positive.2 + negative.2 + zero.2 + park.2 + flags.2 + 16 * image.length + 1000 * (size + n
    + 1))

theorem literal_image (graph : DAG n) (width : Nat) (rows : List Row) (roots : List Nat) (entry
  sourceSize : Nat) :
    (literal graph width rows roots entry sourceSize).1 =
      (LiteralSourceConstruction.constructionCode graph width rows roots entry sourceSize).toList :=
      by
  simp only [literal, BasisColumnConstruction.literal_image, BasisProbeConstruction.literal_image,
    BasisProbeConstruction.config, StackPacketConstruction.park_image,
      BasisConflictConstruction.image,
    LiteralSourceConstruction.constructionCode, LiteralSourceConstruction.columnsCode,
      Array.toList_append,
    List.toList_toArray, List.append_assoc]

theorem seed_clock (width value count : Nat) : (seed width value count).2 = 100 * count + 1 := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [seed, ih]; omega

theorem writes_clock (width base : Nat) (channels : List (Fin n)) : (writes width base channels).2 =
  100 * channels.length + 1 := by
  induction channels with
  | nil => rfl
  | cons channel rest ih => simp only [writes, ih, List.length_cons]; omega

theorem rewrite_clock (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots) (value : Bool) :
    (rewrite width n rows roots value).2 ≤ 20000 * (graph.countedSize + 1) := by
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have rootLength : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have size := graph.countedSize_eq
  simp only [rewrite, seed_clock, writes_clock, List.length_finRange, cacheHeap_size,
    UniformDAGRun.packetHeaderHeap_size, matched.length_eq, children, guards, rootLength]
  omega

theorem monotone_clock (graph : DAG n) (width : Nat) (rows : List Row) (roots : List Nat) (entry :
  Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots) :
    (monotone graph width rows roots entry).2 ≤ 1000000 * (n + 1) * (graph.countedSize + 1) := by
  have columns := BasisColumnConstruction.clock none width n rows roots entry (List.finRange n)
  have full := rewrite_clock width graph rows roots matched rootMatches true
  have reset := rewrite_clock width graph rows roots matched rootMatches false
  have probe := BasisProbeConstruction.monotone_clock width n rows roots (entry + 157 * n) (entry +
    157 * n + 143)
  have parked := StackPacketConstruction.park_clock width 0 ((n + 1) * graph.nodeCount)
  have length : (monotone graph width rows roots entry).1.length = 162 * n + 143 + 2 * (n + 1) *
    graph.nodeCount := by
    rw [monotone_image]
    simp only [Array.length_toList, MonotoneTableConstruction.code_size]
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have rootLength : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have size := graph.countedSize_eq
  simp only [List.length_finRange, matched.length_eq, children, guards, rootLength] at columns probe
  have matrix := Nat.mul_le_mul_left (n + 1) (by omega : graph.nodeCount ≤ graph.countedSize + 1)
  change _ + _ + _ + _ + _ + 16 * (monotone graph width rows roots entry).1.length + 1000 * (n + 1)
    ≤ _
  rw [length]
  nlinarith

theorem literal_clock (graph : DAG n) (width : Nat) (rows : List Row) (roots : List Nat) (entry
  sourceSize : Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots) :
    (literal graph width rows roots entry sourceSize).2 ≤ 1000000 * (n + 1) * (graph.countedSize +
      1) := by
  have positive := BasisColumnConstruction.clock (some .positive) width n rows roots entry
    (List.finRange n)
  have negative := BasisColumnConstruction.clock (some .negative) width n rows roots (entry + 143 *
    n) (List.finRange n)
  have zero := BasisProbeConstruction.literal_clock .zero width n rows roots (entry + 286 * n)
    (entry + 286 * n + 134)
  have parked := StackPacketConstruction.park_clock width 0 ((2 * n + 1) * graph.nodeCount)
  have flags := BasisConflictConstruction.clock width (entry + (286 * n + 134) + 2 * ((2 * n + 1) *
    graph.nodeCount))
    (sourceSize + (2 * n + 1) * graph.nodeCount) (LiteralSourceConstruction.jobs graph sourceSize)
  rw [LiteralSourceConstruction.jobs_work] at flags
  have length : (literal graph width rows roots entry sourceSize).1.length =
    LiteralSourceConstruction.constructionSize graph := by
    rw [literal_image]
    simp only [Array.length_toList, LiteralSourceConstruction.constructionCode_size]
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have rootLength : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have size := graph.countedSize_eq
  simp only [List.length_finRange, matched.length_eq, children, guards,
    rootLength] at positive negative zero
  have matrix := Nat.mul_le_mul_left (n + 1) (by omega : graph.nodeCount ≤ graph.countedSize + 1)
  change _ + _ + _ + _ + _ + 16 * (literal graph width rows roots entry sourceSize).1.length + 1000
    * ((2 * n + 1) * graph.nodeCount + n + 1) ≤ _
  rw [length]
  simp only [LiteralSourceConstruction.constructionSize]
  nlinarith

end Controller.Cost.BasisTableConstruction
