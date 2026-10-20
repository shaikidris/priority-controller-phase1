/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.CriticalSourceBoot

/-! Uniform source-to-output recovery for the critical-set source layouts. -/
namespace Controller.Cost.CriticalSourceScan

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Boundaries
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestRootProjection
open Controller.Cost.ForestWeightedIndexed

variable {n : Nat}

def sourceTerm (graph : DAG n) (nodes : graph.nodeCount = 2 * n + 1) (channel : Channel n) :
    Fin graph.nodeCount := ⟨n + channel.val, by rw [nodes]; have := channel.isLt; omega⟩

private theorem vector_eq (width : Nat) (bits : Nat → Bool) :
    (List.range n).map (fun index => boolWord width (bits index)) =
      List.ofFn (fun channel : Channel n => boolWord width (bits channel.val)) := by
  apply List.ext_getElem
  · simp
  · intro index leftBound rightBound
    simp

/-- Source tags, rather than a selected answer in code, determine the emitted
vector. The representation hypotheses refer to every original row occurrence. -/
theorem source_recovery (graph : DAG n) (nodes : graph.nodeCount = 2 * n + 1)
    (size : forestSize graph ≤ 12 * n) (target : Channel n)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (rootMatch : RootsMatch graph roots) (bits : Nat → Bool)
    (tags : ∀ channel : Channel n, tagValue graph (sourceTerm graph nodes channel) =
      if bits channel.val then 3 else 1)
    (rest output : List (Word (chosenMixedWidth graph)))
    (address loaded temporary : Word (chosenMixedWidth graph))
    (saved : Fin 8 → Word (chosenMixedWidth graph)) :
    ∃ final ticks peak, Execution (program (chosenMixedWidth graph))
      (classificationInitial (chosenMixedWidth graph) graph rows roots (assignmentOfSet {target})
        target rest output address loaded temporary saved) final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word (chosenMixedWidth graph) 1 ∧
      ticks ≤ 556 * n ∧ peak ≤ 89 * n + rest.length + output.length ∧
      programWords (program (chosenMixedWidth graph)) + peak ≤ 317 * n + rest.length + output.length ∧
      final.output = List.ofFn (fun channel : Channel n =>
        boolWord (chosenMixedWidth graph) (bits channel.val)) ++ output := by
  let width := chosenMixedWidth graph
  let payload := (serializedRows 5 rows roots).map (word width)
  let prefixHeap := UniformDAGRun.packetHeaderHeap width n rows roots
  let heap := cacheHeap width prefixHeap rows roots
  let suffix := List.ofFn (fun channel => boolWord width (assignmentOfSet {target} channel)) ++
    (word width target.val :: rest)
  let initial := classificationInitial width graph rows roots (assignmentOfSet {target})
    target rest output address loaded temporary saved
  have cap := chosenMixedCapacity graph
  change 10000 * (forestSize graph + 1) < 2 ^ width at cap
  have npos : 0 < n := Nat.zero_lt_of_lt target.isLt
  have channelSize : n ≤ forestSize graph := by unfold forestSize; omega
  have payloadLength : payload.length = 6 * rows.length + (rowChildren rows).length +
      (rowGuards rows).length + roots.length := by simp [payload, serializedRows_length]
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have rootLength : roots.length = graph.roots.length := by rw [rootMatch]; simp
  have payloadBound : payload.length ≤ 6 * forestSize graph := by
    rw [payloadLength, matched.length_eq, children, guards, rootLength]
    unfold forestSize
    omega
  have sourceHeap : (ForestInputMetadata.headerWords width n rows.length (rowChildren rows).length
      (rowGuards rows).length roots.length).toArray ++ payload.toArray = heap := by
    simp [heap, prefixHeap, UniformDAGRun.packetHeaderHeap, globalHeader, ForestInputMetadata.headerWords,
      cacheHeap, ForestCursorMaterialize.allocatedHeap, payload, countSource_value]
  have input : initial.stack = ForestInputMetadata.headerWords width n rows.length (rowChildren rows).length
      (rowGuards rows).length roots.length ++ payload ++ suffix := by
    simp [initial, classificationInitial, RegisterWiden.widenState, State.frame, ForestCounter.counterState,
      inputPacket, globalHeader, ForestInputMetadata.headerWords, payload, suffix, countSource_value]
  have inside : ∀ index, index < n → 5 + 2 * (n + index) < heap.size := by
    intro index below
    simp only [heap, cacheHeap_size, prefixHeap, UniformDAGRun.packetHeaderHeap_size,
      matched.length_eq, nodes]
    omega
  have stored : ∀ index (below : index < n),
      heap[5 + 2 * (n + index)]'(inside index below) = word width (if bits index then 3 else 1) := by
    intro index below
    let channel : Channel n := ⟨index, below⟩
    have cell := cache_tag_word prefixHeap graph rows roots matched (sourceTerm graph nodes channel)
    rw [tags] at cell
    simpa only [heap, prefixHeap, UniformDAGRun.packetHeaderHeap_size, sourceTerm, channel] using cell
  obtain ⟨final, ticks, trace, time, halted, accepted, _, _, emitted⟩ :=
    cold_execution initial n rows.length (rowChildren rows).length (rowGuards rows).length roots.length
      bits payload suffix rfl rfl rfl rfl input payloadLength (by omega)
      (by omega) (by omega)
      (by intro index below; simpa only [sourceHeap] using inside index below)
      (by intro index below; simpa only [sourceHeap] using stored index below)
  have live : initial.liveWords + n = 15 + payload.length + 2 * n + rest.length + output.length := by
    simp [initial, classificationInitial, RegisterWiden.widenState, State.liveWords, State.frame,
      ForestCounter.counterState, inputPacket, globalHeader, payload, serializedRows_length]
    omega
  have instructions : programWords (program width) = 228 := by simp [programWords]
  refine ⟨final, ticks, initial.liveWords + n, trace, halted, accepted, by omega, ?_, ?_, ?_⟩
  · rw [live]
    omega
  · change programWords (program width) + _ ≤ _
    rw [instructions, live]
    omega
  · change final.output = _ at emitted
    rw [vector_eq] at emitted
    exact emitted

def setBits (K : Finset (Channel n)) (index : Nat) : Bool :=
  if below : index < n then decide ((⟨index, below⟩ : Channel n) ∈ K) else false

@[simp] theorem setBits_channel (K : Finset (Channel n)) (channel : Channel n) :
    setBits K channel.val = assignmentOfSet K channel := by
  simp [setBits, channel.isLt, assignmentOfSet]

/-- The critical family is recovered from its original row packet by a
57-instruction template independent of the hidden critical set. -/
theorem critical_recovery (K : Finset (Channel n)) (target : Channel n)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch (criticalDAG K) rows)
    (rootMatch : RootsMatch (criticalDAG K) roots)
    (rest output : List (Word (chosenMixedWidth (criticalDAG K))))
    (address loaded temporary : Word (chosenMixedWidth (criticalDAG K)))
    (saved : Fin 8 → Word (chosenMixedWidth (criticalDAG K))) :
    ∃ final ticks peak, Execution (program (chosenMixedWidth (criticalDAG K)))
      (classificationInitial (chosenMixedWidth (criticalDAG K)) (criticalDAG K) rows roots
        (assignmentOfSet {target}) target rest output address loaded temporary saved) final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word (chosenMixedWidth (criticalDAG K)) 1 ∧
      ticks ≤ 556 * n ∧ peak ≤ 89 * n + rest.length + output.length ∧
      programWords (program (chosenMixedWidth (criticalDAG K))) + peak ≤ 317 * n + rest.length + output.length ∧
      final.output = List.ofFn (fun channel : Channel n =>
        boolWord (chosenMixedWidth (criticalDAG K)) (assignmentOfSet K channel)) ++ output := by
  have npos : 0 < n := Nat.zero_lt_of_lt target.isLt
  have size : forestSize (criticalDAG K) ≤ 12 * n := by
    have bound := criticalDAG_countedSize_le K
    rw [DAG.countedSize_eq] at bound
    unfold forestSize
    omega
  have tags : ∀ channel : Channel n,
      tagValue (criticalDAG K) (sourceTerm (criticalDAG K) rfl channel) =
        if setBits K channel.val then 3 else 1 := by
    intro channel
    change tagValue (criticalDAG K) (termNode n channel) = if setBits K channel.val then 3 else 1
    simpa [setBits_channel, assignmentOfSet] using critical_tag K channel
  simpa only [setBits_channel] using source_recovery (criticalDAG K) rfl size target rows roots matched rootMatch
    (setBits K) tags rest output address loaded temporary saved

/-- The literal modulo-cycle family uses the same fixed source-input program. -/
theorem cycle_recovery (target : Channel n)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch (CriticalSets.cycleDAG n) rows)
    (rootMatch : RootsMatch (CriticalSets.cycleDAG n) roots)
    (rest output : List (Word (chosenMixedWidth (CriticalSets.cycleDAG n))))
    (address loaded temporary : Word (chosenMixedWidth (CriticalSets.cycleDAG n)))
    (saved : Fin 8 → Word (chosenMixedWidth (CriticalSets.cycleDAG n))) :
    ∃ final ticks peak, Execution (program (chosenMixedWidth (CriticalSets.cycleDAG n)))
      (classificationInitial (chosenMixedWidth (CriticalSets.cycleDAG n)) (CriticalSets.cycleDAG n) rows roots
        (assignmentOfSet {target}) target rest output address loaded temporary saved) final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word (chosenMixedWidth (CriticalSets.cycleDAG n)) 1 ∧
      ticks ≤ 556 * n ∧ peak ≤ 89 * n + rest.length + output.length ∧
      programWords (program (chosenMixedWidth (CriticalSets.cycleDAG n))) + peak ≤
        317 * n + rest.length + output.length ∧
      final.output = List.ofFn (fun _ : Channel n => boolWord (chosenMixedWidth (CriticalSets.cycleDAG n)) true) ++ output := by
  have npos : 0 < n := Nat.zero_lt_of_lt target.isLt
  have size : forestSize (CriticalSets.cycleDAG n) ≤ 12 * n := by
    have bound := CriticalSets.cycle_size n
    rw [DAG.countedSize_eq] at bound
    unfold forestSize
    omega
  have tags : ∀ channel : Channel n,
      tagValue (CriticalSets.cycleDAG n) (sourceTerm (CriticalSets.cycleDAG n) rfl channel) =
        if (fun _ : Nat => true) channel.val then 3 else 1 := by
    intro channel
    change tagValue (CriticalSets.cycleDAG n) (termNode n channel) = 3
    exact cycle_tag channel
  exact source_recovery (CriticalSets.cycleDAG n) rfl size target rows roots matched rootMatch
    (fun _ => true) tags rest output address loaded temporary saved

/-- On the critical-family promise, the recovered vector describes a physical
detecting input. Source loading, output and resident code share the same bounds. -/
theorem critical_physical_recovery (b : Nat) (bridge : Physical.Bridge n) (positive : 0 < b)
    (K : Finset (Channel n)) (legal : K ∈ criticalSets b bridge.target)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch (criticalDAG K) rows)
    (rootMatch : RootsMatch (criticalDAG K) roots)
    (rest output : List (Word (chosenMixedWidth (criticalDAG K))))
    (address loaded temporary : Word (chosenMixedWidth (criticalDAG K)))
    (saved : Fin 8 → Word (chosenMixedWidth (criticalDAG K))) :
    ∃ final ticks peak, Execution (program (chosenMixedWidth (criticalDAG K)))
      (classificationInitial (chosenMixedWidth (criticalDAG K)) (criticalDAG K) rows roots
        (assignmentOfSet {bridge.target}) bridge.target rest output address loaded temporary saved) final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word (chosenMixedWidth (criticalDAG K)) 1 ∧
      ticks ≤ 556 * n ∧ peak ≤ 89 * n + rest.length + output.length ∧
      programWords (program (chosenMixedWidth (criticalDAG K))) + peak ≤ 317 * n + rest.length + output.length ∧
      final.output = List.ofFn (fun channel : Channel n =>
        boolWord (chosenMixedWidth (criticalDAG K)) (assignmentOfSet K channel)) ++ output ∧
      Physical.BridgeInputDetects bridge true (criticalDAG K).observations
        (Physical.realizeBridge bridge positive K) true := by
  obtain ⟨final, ticks, peak, trace, halted, accepted, time, space, resident, emitted⟩ :=
    critical_recovery K bridge.target rows roots matched rootMatch rest output address loaded temporary saved
  refine ⟨final, ticks, peak, trace, halted, accepted, time, space, resident, emitted, ?_⟩
  rw [CriticalSets.critical_observations]
  exact critical_physical_realizer_detects bridge positive K legal

/-- The modulo-cycle source yields the full simultaneous detecting set and
its physical realization through the same fixed instruction template. -/
theorem cycle_physical_recovery (b : Nat) (bridge : Physical.Bridge n) (positive : 0 < b)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch (CriticalSets.cycleDAG n) rows)
    (rootMatch : RootsMatch (CriticalSets.cycleDAG n) roots)
    (rest output : List (Word (chosenMixedWidth (CriticalSets.cycleDAG n))))
    (address loaded temporary : Word (chosenMixedWidth (CriticalSets.cycleDAG n)))
    (saved : Fin 8 → Word (chosenMixedWidth (CriticalSets.cycleDAG n))) :
    ∃ final ticks peak, Execution (program (chosenMixedWidth (CriticalSets.cycleDAG n)))
      (classificationInitial (chosenMixedWidth (CriticalSets.cycleDAG n)) (CriticalSets.cycleDAG n) rows roots
        (assignmentOfSet {bridge.target}) bridge.target rest output address loaded temporary saved) final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word (chosenMixedWidth (CriticalSets.cycleDAG n)) 1 ∧
      ticks ≤ 556 * n ∧ peak ≤ 89 * n + rest.length + output.length ∧
      programWords (program (chosenMixedWidth (CriticalSets.cycleDAG n))) + peak ≤
        317 * n + rest.length + output.length ∧
      final.output = List.ofFn (fun _ : Channel n => boolWord (chosenMixedWidth (CriticalSets.cycleDAG n)) true) ++ output ∧
      Physical.BridgeInputDetects bridge true (CriticalSets.cycleDAG n).observations
        (Physical.realizeBridge bridge positive Finset.univ) true := by
  obtain ⟨final, ticks, peak, trace, halted, accepted, time, space, resident, emitted⟩ :=
    cycle_recovery bridge.target rows roots matched rootMatch rest output address loaded temporary saved
  exact ⟨final, ticks, peak, trace, halted, accepted, time, space, resident, emitted,
    CriticalSets.cycle_detects_full bridge positive⟩

end Controller.Cost.CriticalSourceScan
