/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.SupportAssemblyStorage
import Controller.Cost.BasisTableConstruction

/-! Proper-basis table construction storage. Singleton interpreters are fixed
images; columns, sign-pair jobs and matrix parking form source-count streams. -/
namespace Controller.Cost.BasisTableStorage

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Cost.ForestIndexedOperands Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestClauseProgramConstruction (environment)
open Controller.Cost.AssemblyStorage

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
attribute [local irreducible] BasisProbeConstruction.literal BasisProbeConstruction.monotone
  BasisColumnConstruction.step BasisColumnConstruction.build

theorem literalProbe (mode : BasisProbeConstruction.Mode) (width n : Nat) (rows : List Row)
    (roots : List Nat) (entry done : Nat) :
    Bounded (BasisProbeConstruction.literal mode width n rows roots entry done).1 200000 := by
  let kernel := BasisProbeConstruction.literalKernel mode width n rows roots
  have formed := wordCode (width := width)
    (environment [n, rows.length, (rowChildren rows).length, (rowGuards rows).length, roots.length])
    (BasisProbeConstruction.recipes width mode)
  have wide := Trace.widen formed
  have moved := relocate wide entry
  let base := SharedReusableProbe.tableSize width n rows roots
  have copied := SupportAssemblyStorage.copy width (entry + 117) (entry + 127) base rows.length
  have released := SupportAssemblyStorage.reclaim width (entry + 127) done rows.length
  have assembled := join (join moved copied) released
  have length : kernel.length = 117 := by
    cases mode <;> rfl
  have imageLength : (ProgramRelocationConstruction.build entry
      (kernel.map RegisterWiden.widenInstruction)).1.length = 117 := by
    rw [ProgramRelocationConstruction.build_image, ResidentSegment.code]
    simp only [List.length_map, length]
  have copyLength : (StackPacketConstruction.copy width (entry + 117) (entry + 127) base
      rows.length).length = 10 := by
    rw [StackPacketConstruction.copy_image, Array.length_toList, SharedWitnessCopy.code_size]
  have workBound : work (BasisProbeConstruction.recipes width mode) ≤ 2000 := by
    cases mode <;>
      simp only [BasisProbeConstruction.recipes,
        ProperBasisConstructionRecipes.positive.constructionRecipe_work,
        ProperBasisConstructionRecipes.negative.constructionRecipe_work,
        ProperBasisConstructionRecipes.zero.constructionRecipe_work] <;> decide
  unfold BasisProbeConstruction.literal
  dsimp only
  exact .enlarge assembled (by
    change 32 * work (BasisProbeConstruction.recipes width mode) +
      32 * kernel.length + 288 * (kernel.map RegisterWiden.widenInstruction).length + 16 +
      5000 + 32 * (ProgramRelocationConstruction.build entry
        (kernel.map RegisterWiden.widenInstruction)).1.length + 32 + 5000 +
      32 * ((ProgramRelocationConstruction.build entry
        (kernel.map RegisterWiden.widenInstruction)).1 ++
        StackPacketConstruction.copy width (entry + 117) (entry + 127) base rows.length).length +
      32 ≤ _
    simp only [List.length_map, List.length_append, length, imageLength, copyLength]
    omega)

theorem monotoneProbe (width n : Nat) (rows : List Row) (roots : List Nat) (entry done : Nat) :
    Bounded (BasisProbeConstruction.monotone width n rows roots entry done).1 200000 := by
  let header := UniformDAGRun.packetHeaderHeap width n rows roots
  let base := SharedReusableProbe.tableSize width n rows roots
  have round := SupportAssemblyStorage.sourceRound width n header rows roots entry
  have copied := SupportAssemblyStorage.copy width (entry + 126) (entry + 136) base rows.length
  have released := SupportAssemblyStorage.reclaim width (entry + 136) done rows.length
  have assembled := join (join round copied) released
  have roundLength : (SupportControllerConstruction.sourceRound width n header rows roots
      entry).1.length = 126 := by
    rw [SupportControllerConstruction.sourceRound_image, Array.length_toList,
      SupportSourceRound.code_size]
  have copyLength : (StackPacketConstruction.copy width (entry + 126) (entry + 136) base
      rows.length).length = 10 := by
    rw [StackPacketConstruction.copy_image, Array.length_toList, SharedWitnessCopy.code_size]
  unfold BasisProbeConstruction.monotone
  dsimp only
  exact .enlarge assembled (by
    simp only [List.length_append, roundLength, copyLength]
    omega)

theorem step (mode : Option BasisProbeConstruction.Mode) (width n : Nat) (rows : List Row)
    (roots : List Nat) (channel : Fin n) (entry : Nat) :
    Bounded (BasisColumnConstruction.step mode width n rows roots channel entry).1 250000 := by
  let base := (cacheHeap width (UniformDAGRun.packetHeaderHeap width n rows roots) rows roots).size
  have first := wordCode (width := width) (environment [base])
    (BasisColumnConstruction.candidateOne.constructionRecipe width)
  have last := wordCode (width := width) (environment [base])
    (BasisColumnConstruction.candidateZero.constructionRecipe width)
  have probe : Bounded
      (match mode with
      | none => BasisProbeConstruction.monotone width n rows roots (entry + 5) (entry + 148)
      | some value => BasisProbeConstruction.literal value width n rows roots (entry + 5)
          (entry + 139)).1 200000 := by
    cases mode with
    | none => exact monotoneProbe _ _ _ _ _ _
    | some value => exact literalProbe value _ _ _ _ _ _
  have set := constant (width := width) (registers := 8) 4 channel.val
  have assembled := join (join (join set first) probe) last
  have probeLength : (match mode with
      | none => BasisProbeConstruction.monotone width n rows roots (entry + 5) (entry + 148)
      | some value => BasisProbeConstruction.literal value width n rows roots (entry + 5)
          (entry + 139)).1.length ≤ 143 := by
    cases mode with
    | none => rw [BasisProbeConstruction.monotone_image, Array.length_toList,
        SharedTableProbe.code_size]
    | some value => rw [BasisProbeConstruction.literal_image, Array.length_toList,
        LiteralSourceProbe.code_size]; omega
  unfold BasisColumnConstruction.step
  dsimp only
  exact .enlarge assembled (by
    simp only [List.length_append, List.length_cons, List.length_nil, evaluate, List.length_map,
      BasisColumnConstruction.candidateOne.constructionRecipe_work,
      BasisColumnConstruction.candidateZero.constructionRecipe_work]
    have length : (BasisColumnConstruction.candidateOne.constructionRecipe width).length = 4 := rfl
    rw [length]
    omega)

theorem columns (mode : Option BasisProbeConstruction.Mode) (width n : Nat) (rows : List Row)
    (roots : List Nat) (entry : Nat) (channels : List (Fin n)) :
    Bounded (BasisColumnConstruction.build mode width n rows roots entry channels).1
      (300000 * channels.length) := by
  induction channels generalizing entry with
  | nil => unfold BasisColumnConstruction.build; exact .empty
  | cons channel rest ih =>
      have head := step mode width n rows roots channel entry
      have tail := ih (entry + (BasisColumnConstruction.step mode width n rows roots channel
          entry).1.length)
      have assembled := join head tail
      have length := BasisColumnConstruction.step_length mode width n rows roots channel entry
      unfold BasisColumnConstruction.build
      dsimp only
      exact .enlarge assembled (by simp only [List.length_cons]; omega)

theorem seed (width value count : Nat) :
    Bounded (BasisTableConstruction.seed width value count).1 (1000 * count) := by
  induction count with
  | zero => exact .empty
  | succ count ih =>
      have formed := join (wordCode (width := width) (environment [value])
        (BasisTableConstruction.seedCode.constructionRecipe width)) ih
      exact .enlarge formed (by
        simp only [BasisTableConstruction.seedCode.constructionRecipe_work, evaluate,
            List.length_map]
        have length : (BasisTableConstruction.seedCode.constructionRecipe width).length = 2 := rfl
        rw [length]
        omega)

theorem writes (width base : Nat) (channels : List (Fin n)) :
    Bounded (BasisTableConstruction.writes width base channels).1 (2000 * channels.length) := by
  induction channels with
  | nil => exact .empty
  | cons channel rest ih =>
      have formed := join (wordCode (width := width) (environment [base + channel.val])
        (BasisTableConstruction.writeCode.constructionRecipe width)) ih
      exact .enlarge formed (by
        simp only [BasisTableConstruction.writeCode.constructionRecipe_work, evaluate,
            List.length_map,
          List.length_cons]
        have length : (BasisTableConstruction.writeCode.constructionRecipe width).length = 3 := rfl
        rw [length]
        omega)

theorem rewrite (width n : Nat) (rows : List Row) (roots : List Nat) (value : Bool) :
    Bounded (BasisTableConstruction.rewrite width n rows roots value).1 (4000 * n + 32) := by
  let base := (cacheHeap width (UniformDAGRun.packetHeaderHeap width n rows roots) rows roots).size
  have first := seed width (if value then 1 else 0) n
  have last := writes width base (List.finRange n)
  have assembled := join first last
  have length : (BasisTableConstruction.seed width (if value then 1 else 0) n).1.length = 2 *
      n := by
    rw [BasisTableConstruction.seed_image, SharedWitnessSeed.code_length]
  dsimp only [BasisTableConstruction.rewrite]
  exact .enlarge assembled (by rw [List.length_finRange] at *; omega)


theorem columnLength (mode : Option BasisProbeConstruction.Mode) (width n : Nat)
    (rows : List Row) (roots : List Nat) (entry : Nat) (channels : List (Fin n)) :
    (BasisColumnConstruction.build mode width n rows roots entry channels).1.length ≤
      152 * channels.length := by
  induction channels generalizing entry with
  | nil =>
      unfold BasisColumnConstruction.build
      exact Nat.le_refl 0
  | cons channel rest ih =>
      have head := BasisColumnConstruction.step_length mode width n rows roots channel entry
      have tail := ih (entry + (BasisColumnConstruction.step mode width n rows roots channel
          entry).1.length)
      unfold BasisColumnConstruction.build
      dsimp only
      simp only [List.length_append, List.length_cons]
      omega

theorem pairScan (width flag entry : Nat) (pairs : List (Nat × Nat)) :
    Bounded (BasisConflictConstruction.pairs width flag entry pairs).1 (4000 * pairs.length) := by
  induction pairs generalizing entry with
  | nil => exact .empty
  | cons pair rest ih =>
      have first := wordCode (width := width) (environment [entry, pair.1, pair.2, flag])
        (BasisConflictConstruction.pairCode.constructionRecipe width)
      have tail := ih (entry + 9)
      have assembled := join first tail
      exact .enlarge assembled (by
        simp only [BasisConflictConstruction.pairCode.constructionRecipe_work, List.length_cons,
          evaluate, List.length_map]
        have length : (BasisConflictConstruction.pairCode.constructionRecipe width).length =
            9 := rfl
        rw [length]
        omega)

theorem conflicts (width entry flag : Nat) (jobs : List LiteralConflict.Job) :
    Bounded (BasisConflictConstruction.build width entry flag jobs).1
      (10000 * LiteralConflict.work jobs) := by
  induction jobs generalizing entry flag with
  | nil => exact .empty
  | cons job rest ih =>
      have initial := wordCode (width := width) (environment [job.zeroAddress])
        (BasisConflictConstruction.initialCode.constructionRecipe width)
      have scan := pairScan width flag (entry + 3) job.pairs
      have tail := ih (entry + 3 + 9 * job.pairs.length) (flag + 1)
      have assembled := join (join initial scan) tail
      have scanLength : (BasisConflictConstruction.pairs width flag (entry + 3)
          job.pairs).1.length =
          9 * job.pairs.length := by
        rw [BasisConflictConstruction.pairs_image, Array.length_toList,
            LiteralConflict.scanCode_size]
      exact .enlarge assembled (by
        simp only [BasisConflictConstruction.initialCode.constructionRecipe_work,
            LiteralConflict.work,
          List.map_cons, List.sum_cons, List.length_append, evaluate, List.length_map]
        have length : (BasisConflictConstruction.initialCode.constructionRecipe width).length =
            3 := rfl
        rw [length, scanLength]
        omega)

theorem rewriteLength (width n : Nat) (rows : List Row) (roots : List Nat) (value : Bool) :
    (BasisTableConstruction.rewrite width n rows roots value).1.length = 5 * n := by
  rw [BasisTableConstruction.rewrite_image]
  simp only [MonotoneTableConstruction.rewriteCode, List.length_append,
      SharedWitnessSeed.code_length,
    SharedChannelRewrite.code_length, List.length_finRange]
  omega

theorem monotone (graph : DAG n) (width : Nat) (rows : List Row) (roots : List Nat)
    (entry : Nat) :
    Bounded (BasisTableConstruction.monotone graph width rows roots entry).1
      (100000000 * (n + 1) * (graph.countedSize + 1)) := by
  have columns := columns none width n rows roots entry (List.finRange n)
  have full := rewrite width n rows roots true
  have probe := monotoneProbe width n rows roots (entry + 157 * n) (entry + 157 * n + 143)
  have reset := rewrite width n rows roots false
  have parked := SupportAssemblyStorage.park width 0 ((n + 1) * graph.nodeCount)
  have assembled := join (join (join (join columns full) probe) reset) parked
  have columnSize := columnLength none width n rows roots entry (List.finRange n)
  have fullSize := rewriteLength width n rows roots true
  have resetSize := rewriteLength width n rows roots false
  have probeSize : (BasisProbeConstruction.monotone width n rows roots (entry + 157 * n)
      (entry + 157 * n + 143)).1.length = 143 := by
    rw [BasisProbeConstruction.monotone_image, Array.length_toList, SharedTableProbe.code_size]
  have size := graph.countedSize_eq
  have matrix := Nat.mul_le_mul_left (n + 1) (by omega : graph.nodeCount ≤ graph.countedSize + 1)
  dsimp only [BasisTableConstruction.monotone]
  exact .enlarge assembled (by
    simp only [List.length_append, List.length_finRange] at *
    nlinarith)

theorem literal (graph : DAG n) (width : Nat) (rows : List Row) (roots : List Nat)
    (entry sourceSize : Nat) :
    Bounded (BasisTableConstruction.literal graph width rows roots entry sourceSize).1
      (100000000 * (n + 1) * (graph.countedSize + 1)) := by
  let size := (2 * n + 1) * graph.nodeCount
  have positive := columns (some .positive) width n rows roots entry (List.finRange n)
  have negative := columns (some .negative) width n rows roots (entry + 143 * n) (List.finRange n)
  have zero := literalProbe .zero width n rows roots (entry + 286 * n) (entry + 286 * n + 134)
  have parked := SupportAssemblyStorage.park width 0 size
  have flags := conflicts width (entry + (286 * n + 134) + 2 * size)
    (sourceSize + size) (LiteralSourceConstruction.jobs graph sourceSize)
  have assembled := join (join (join (join positive negative) zero) parked) flags
  have positiveSize := columnLength (some .positive) width n rows roots entry (List.finRange n)
  have negativeSize := columnLength (some .negative) width n rows roots (entry + 143 * n)
    (List.finRange n)
  have zeroSize : (BasisProbeConstruction.literal .zero width n rows roots (entry + 286 * n)
      (entry + 286 * n + 134)).1.length = 134 := by
    rw [BasisProbeConstruction.literal_image, Array.length_toList, LiteralSourceProbe.code_size]
  have parkSize : (StackPacketConstruction.park width 0 size).1.length = 2 * size := by
    rw [StackPacketConstruction.park_image, SharedWitnessPark.code_length]
  have source := graph.countedSize_eq
  dsimp only [BasisTableConstruction.literal]
  exact .enlarge assembled (by
    simp only [List.length_append, List.length_finRange, LiteralSourceConstruction.jobs_work] at *
    dsimp only [size] at *
    nlinarith [Nat.mul_le_mul_left (n + 1) (by omega : graph.nodeCount ≤ graph.countedSize + 1)])

end Controller.Cost.BasisTableStorage
