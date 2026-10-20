/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ForestStreamingConstruction
import Controller.Cost.ForestMarkStorage
import Controller.Cost.ForestScalarStorage

/-! Construction storage of the complete tail packet loop. Metadata and both
placement images have traced scratch storage. Maxima compose those stages
without multiplying the shared ambient mark table by the query count. -/
namespace Controller.Cost.ForestStreamingStorage

open Controller.Cost Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.ForestStreamingConstruction

variable {ambient : Nat}

def rows (refs : List (List (Reference ambient))) := ForestZeroAssembly.originalRows (reservedReferences refs)
def coordinates (refs : List (List (Reference ambient))) := ((rows refs).map (List.map Prod.fst)).flatten

def metadata (channels : Nat) (state : ForestStreamingConstruction.State ambient width) (refs : List (List (Reference ambient))) :=
  ForestCompilerMarks.query channels state.marks (rows refs)

def nextEntry (protectedEnd channels : Nat) (state : ForestStreamingConstruction.State ambient width) (refs : List (List (Reference ambient))) : Nat :=
  state.cursor + (ForestScalarNegativeConstruction.form width protectedEnd channels state.cursor 0 refs
    (metadata channels state refs).1.count (metadata channels state refs).2.1).1.length

structure Packet (protectedEnd channels : Nat) (state : ForestStreamingConstruction.State ambient width) (refs : List (List (Reference ambient))) where
  scanPeak : Nat
  coveragePeak : Nat
  scanTrace : ForestCompilerMarks.SpaceTrace (ForestCompilerMarks.begin state.marks) (coordinates refs)
    (metadata channels state refs).1 (32 * (coordinates refs).length + 1) scanPeak
  coverageTrace : ForestMarkStorage.CoverageTrace (metadata channels state refs).1
    ((metadata channels state refs).1.count + 1) channels 0 (metadata channels state refs).2.1
    (ForestCompilerMarks.search (metadata channels state refs).1 ((metadata channels state refs).1.count + 1) channels 0).2 coveragePeak
  provisional : ForestScalarStorage.Certificate width protectedEnd channels state.cursor 0 refs
    (metadata channels state refs).1.count (metadata channels state refs).2.1
  relocated : ForestScalarStorage.Certificate width protectedEnd channels state.cursor (nextEntry protectedEnd channels state refs) refs
    (metadata channels state refs).1.count (metadata channels state refs).2.1

def packetWords (protectedEnd channels : Nat) (state : ForestStreamingConstruction.State ambient width) (refs : List (List (Reference ambient)))
    (packet : Packet protectedEnd channels state refs) : Nat :=
  max packet.scanPeak packet.coveragePeak + 4 * (rows refs).length + 8 * (rows refs).flatten.length + 32 +
    ForestScalarStorage.buffers width protectedEnd channels state.cursor 0 refs
      (metadata channels state refs).1.count (metadata channels state refs).2.1 packet.provisional +
    ForestScalarStorage.buffers width protectedEnd channels state.cursor (nextEntry protectedEnd channels state refs) refs
      (metadata channels state refs).1.count (metadata channels state refs).2.1 packet.relocated +
    16 * (ForestScalarNegativeConstruction.form width protectedEnd channels state.cursor 0 refs
      (metadata channels state refs).1.count (metadata channels state refs).2.1).1.length + 128

theorem packet_space (protectedEnd channels : Nat) (state : ForestStreamingConstruction.State ambient width) (refs : List (List (Reference ambient))) :
    ∃ packet : Packet protectedEnd channels state refs,
      packetWords protectedEnd channels state refs packet ≤ ambient + 2000000 +
        200000 * refs.length + 400000 * refs.flatten.length := by
  obtain ⟨scanPeak, coveragePeak, scanTrace, coverageTrace, metadataBound⟩ :=
    ForestMarkStorage.query channels state.marks (rows refs)
  obtain ⟨provisional, provisionalBound⟩ := ForestScalarStorage.construction width protectedEnd channels state.cursor 0 refs
    (metadata channels state refs).1.count (metadata channels state refs).2.1
  obtain ⟨relocated, relocatedBound⟩ := ForestScalarStorage.construction width protectedEnd channels state.cursor
    (nextEntry protectedEnd channels state refs) refs (metadata channels state refs).1.count (metadata channels state refs).2.1
  have codeSize := ForestScalarNegativeConstruction.instruction_bound width protectedEnd channels state.cursor 0 refs
    (metadata channels state refs).1.count (metadata channels state refs).2.1
  have rowCount : (rows refs).length = refs.length + 1 := by
    simp [rows, ForestZeroAssembly.originalRows, reservedReferences]
  have literalCount : (rows refs).flatten.length = refs.flatten.length := by
    simp [rows, ForestZeroAssembly.originalRows, reservedReferences, List.length_flatten,
      List.map_map, Function.comp_def]
  rw [rowCount, literalCount] at metadataBound
  refine ⟨⟨scanPeak, coveragePeak, scanTrace, coverageTrace, provisional, relocated⟩, ?_⟩
  dsimp only [packetWords]
  rw [rowCount, literalCount]
  omega

/-- Each loop transition retains the actual code accumulator and one metadata
state, plus the certified scratch of that one packet. -/
inductive Trace (protectedEnd channels : Nat) : ForestStreamingConstruction.State ambient width →
    List (List (List (Reference ambient))) → ForestStreamingConstruction.State ambient width → Nat → Prop
  | nil (state) : Trace protectedEnd channels state [] state (retainedWords state)
  | cons (state refs rest final peak) (packet : Packet protectedEnd channels state refs)
      (tail : Trace protectedEnd channels (ForestStreamingConstruction.step protectedEnd channels state refs) rest final peak) :
      Trace protectedEnd channels state (refs :: rest) final
        (max (retainedWords state + packetWords protectedEnd channels state refs packet) peak)

/-- Ambient storage is charged once in the peak. The remaining coefficients
cover all provisional/relocated buffers and continuation records. -/
theorem construction (protectedEnd channels : Nat) (state : ForestStreamingConstruction.State ambient width)
    (packets : List (List (List (Reference ambient)))) :
    ∃ peak, Trace protectedEnd channels state packets (ForestStreamingConstruction.run protectedEnd channels state packets) peak ∧
      peak ≤ retainedWords state + ambient + 3000000 * packets.length +
        201000 * packets.flatten.length + 401000 * packets.flatten.flatten.length + 128 := by
  induction packets generalizing state with
  | nil => exact ⟨retainedWords state, .nil state, by simp; omega⟩
  | cons refs rest ih =>
      obtain ⟨packet, scratch⟩ := packet_space protectedEnd channels state refs
      obtain ⟨peak, trace, bound⟩ := ih (ForestStreamingConstruction.step protectedEnd channels state refs)
      have retained := step_retained protectedEnd channels state refs
      refine ⟨max (retainedWords state + packetWords protectedEnd channels state refs packet) peak,
        .cons state refs rest _ _ packet trace, ?_⟩
      simp only [List.length_cons, List.flatten_cons, List.flatten_append, List.length_append]
      exact Nat.max_le.mpr ⟨by omega, by omega⟩

end Controller.Cost.ForestStreamingStorage
