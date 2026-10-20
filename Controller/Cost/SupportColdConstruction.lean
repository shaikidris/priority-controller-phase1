module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.SourceRepackConstruction

@[expose] public section


/-! Cold source preparation constructs its interpreter, reads the healthy
value table at runtime, and constructs the physical retained-header exchange. -/
namespace Controller.Cost.SupportColdConstruction

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Cost.ForestIndexedOperands

def healthy (width n m : Nat) (rows : List Row) (roots : List Nat) (entry : Nat) : List (Instruction
  width 8) × Nat :=
  let header := UniformDAGRun.packetHeaderHeap width n rows roots
  let source := (cacheHeap width header rows roots).size
  let round := SupportControllerConstruction.sourceRound width n header rows roots entry
  let operands := SupportHealthyLayout.plan width n m header rows roots
  let repack := SourceRepackConstruction.build width (entry + 126) (source + n + m) operands
  let image := round.1 ++ repack.1
  (image, round.2 + repack.2 + 1000 * (source + m + 1) + 16 * image.length)

theorem healthy_image (width n m : Nat) (rows : List Row) (roots : List Nat) (entry : Nat) :
    (healthy width n m rows roots entry).1 = SupportHealthyPrepare.code width n m rows roots entry
      := by
  simp only [healthy, SupportControllerConstruction.sourceRound_image,
    SourceRepackConstruction.image,
    SupportHealthyPrepare.code]

def build (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat) : List (Instruction
  width 8) × Nat :=
  let count := SharedDetectorPrepared.packetSize graph
  let parked := StackPacketConstruction.park width 0 count
  let preparation := healthy width n graph.nodeCount rows roots (2 * count)
  let image := parked.1 ++ preparation.1
  (image, parked.2 + preparation.2 + 16 * image.length + 1000 * (graph.countedSize + 1))

theorem image (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat) :
    (build width graph rows roots).1 = SupportColdPrepare.code width graph rows roots := by
  simp only [build, StackPacketConstruction.park_image, healthy_image, SupportColdPrepare.code]

theorem healthy_clock (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots) (entry : Nat) :
    (healthy width n graph.nodeCount rows roots entry).2 ≤ 100000 * (graph.countedSize + 1) := by
  let header := UniformDAGRun.packetHeaderHeap width n rows roots
  let operands := SupportHealthyLayout.plan width n graph.nodeCount header rows roots
  have round := SupportControllerConstruction.sourceRound_clock width n header rows roots entry
  have repack := SourceRepackConstruction.clock width (entry + 126)
    ((cacheHeap width header rows roots).size + n + graph.nodeCount) operands
  have planLength := SupportHealthyLayout.plan_length (width := width) (n := n) (m :=
    graph.nodeCount) header rows roots
  have length : (healthy width n graph.nodeCount rows roots entry).1.length ≤ 300 *
    (graph.countedSize + 1) := by
    rw [healthy_image]
    exact SupportHealthyPrepare.code_bound graph rows roots matched rootMatches
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have rootLength : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have source : (cacheHeap width header rows roots).size + graph.nodeCount ≤ 8 * graph.countedSize +
    5 := by
    simp only [cacheHeap_size, header, UniformDAGRun.packetHeaderHeap_size, matched.length_eq,
      children, guards, rootLength]
    have size := graph.countedSize_eq
    omega
  change _ + _ + 1000 * ((cacheHeap width header rows roots).size + graph.nodeCount + 1) +
    16 * (healthy width n graph.nodeCount rows roots entry).1.length ≤ _
  dsimp only [operands] at repack
  rw [planLength] at repack
  simp only [matched.length_eq, children, guards, rootLength] at round
  have size := graph.countedSize_eq
  dsimp only [header] at round source repack ⊢
  omega

theorem clock (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots) :
    (build width graph rows roots).2 ≤ 200000 * (graph.countedSize + 1) := by
  have healthy := healthy_clock width graph rows roots matched rootMatches (2 *
    SharedDetectorPrepared.packetSize graph)
  have parked := StackPacketConstruction.park_clock width 0 (SharedDetectorPrepared.packetSize
    graph)
  have count := SupportColdPrepare.packet_bound graph
  have length : (build width graph rows roots).1.length ≤ 400 * (graph.countedSize + 1) := by
    rw [image]
    exact SupportColdPrepare.code_bound graph rows roots matched rootMatches
  change _ + _ + 16 * (build width graph rows roots).1.length + 1000 * (graph.countedSize + 1) ≤ _
  omega

end Controller.Cost.SupportColdConstruction
