/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ForestOriginalSemantics

/-! Cold loading, evaluation and root classification preserve the attained
weighted optimum for forests whose healthy observations are zero. Instruction
image construction remains a separate cost from the fetched execution here. -/
namespace Controller.Cost.ForestWeightedCold

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.ForestRootProjection Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestCursorDescriptors

variable {n width : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

private theorem classified_zero (graph : DAG n) (target : Channel n)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (rootsMatch : RootsMatch graph roots)
    (healthy : ∀ position : Fin graph.roots.length,
      graph.eval (assignmentOfSet {target}) (graph.roots.get position) = false)
    (value : Bool) :
    classifiedIds rows roots (rowNodeValues graph rows matched (assignmentOfSet {target})) value =
      if value then [] else roots := by
  have zero : ∀ root ∈ roots, (if valid : root < rows.length then
      rowNodeValues graph rows matched (assignmentOfSet {target}) ⟨root, valid⟩ else false) = false := by
    intro root member
    rw [rootsMatch] at member
    obtain ⟨node, nodeMember, rfl⟩ := List.mem_map.mp member
    have bound : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
    rw [dif_pos bound]
    change graph.evalTable (assignmentOfSet {target}) _ = false
    have castEq : Fin.cast matched.length_eq (⟨node.val, bound⟩ : Fin rows.length) = node := Fin.ext rfl
    rw [castEq, graph.evalTable_eq_eval]
    obtain ⟨position, rfl⟩ := List.mem_iff_get.mp nodeMember
    exact healthy position
  unfold classifiedIds
  cases value
  · simp only [Bool.false_eq_true, if_false]
    exact List.filter_eq_self.mpr (by intro root member; simp [zero root member])
  · simp only [if_true]
    apply List.filter_eq_nil_iff.mpr
    intro root member
    simp [zero root member]

def classificationTime (graph : DAG n) : Nat :=
  27 + 7 * (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length) +
    2 * n + 43 * graph.nodeCount + 18 * (graph.childIncidences + graph.guardIncidences) + 6

def classificationSpace (graph : DAG n) (rest output : List (Word width)) : Nat :=
  18 + (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length) +
    n + graph.nodeCount + (1 + rest.length) + output.length

def loadedTime (graph : DAG n) (rows : List Row) (roots : List Nat) : Nat :=
  28 + 7 * (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length) +
    (18 * (buildRoots graph).count + ForestWitnessAccept.sourceBudget graph graph.nodeCount + 12 * n +
      4 * sourceAllocatedCells graph rows roots + 4 * sourcePrefixCells rows + 37)

set_option maxHeartbeats 1800000 in
/-- The actual cold program consumes the original source packet, evaluates it,
classifies every root occurrence, loads the selected source, and emits a maximum
weight detecting set. Its resident image is the existing mixed assembly. -/
theorem execution (graph negativeGraph : DAG n) (forest : graph.FormulaForest)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched) (rootsMatch : RootsMatch graph roots)
    (negativeMatched : RowsMatch negativeGraph rows)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : Nat) (bridge : Physical.Bridge n) (positive : 0 < b)
    (healthy : ∀ position : Fin graph.roots.length,
      graph.eval (assignmentOfSet {bridge.target}) (graph.roots.get position) = false)
    (detectable : Physical.BridgeDetectable (b := b) bridge true graph.observations)
    (countFits : (buildRoots graph).count < 2 ^ width)
    (positionFits : ∀ entry ∈ (buildRoots graph).entries, entry.position < 2 ^ width)
    (rest output : List (Word width)) (address loaded temporary : Word width)
    (saved : Fin 8 → Word width)
    (evaluationRoom : (ForestInputPrefixStored.evaluationHeap
      (UniformDAGRun.packetHeaderHeap width n rows roots) rows roots (assignmentOfSet {bridge.target})
      (graph.evalTable (assignmentOfSet {bridge.target}))).size < 2 ^ width)
    (sourceRoom : sourceAllocatedCells graph rows roots < 2 ^ width)
    (packetRoom : sourcePrefixCells rows < 2 ^ width)
    (programRoom : (mixedResident
      (packetPrelude (classificationPrior width graph rows roots (assignmentOfSet {bridge.target})))
      graph negativeGraph rows roots [] negativeMatched weights b bridge.target countFits positionFits).size < 2 ^ width) :
    ∃ K final ticks peak,
      Execution (mixedResident
        (packetPrelude (classificationPrior width graph rows roots (assignmentOfSet {bridge.target})))
        graph negativeGraph rows roots [] negativeMatched weights b bridge.target countFits positionFits)
        (classificationInitial width graph rows roots (assignmentOfSet {bridge.target}) bridge.target
          rest output address loaded temporary saved) final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word width 1 ∧
      Admissible b bridge.target K ∧
      Physical.BridgeInputDetects bridge true graph.observations
        (Physical.realizeBridge bridge positive K) true ∧
      final.heap = #[] ∧ final.stack = rest ∧
      final.output = List.ofFn (fun channel : Channel n => boolWord width (decide (channel ∈ K))) ++ output ∧
      (∀ L, Admissible b bridge.target L →
        Physical.BridgeInputDetects bridge true graph.observations
          (Physical.realizeBridge bridge positive L) true →
        GenericWeight.total weights L ≤ GenericWeight.total weights K) ∧
      ticks ≤ classificationTime graph +
        (20 * roots.length + 12 * sourcePrefixCells rows + 4 *
          (ForestInputPrefixStored.evaluationHeap
            (UniformDAGRun.packetHeaderHeap width n rows roots) rows roots (assignmentOfSet {bridge.target})
            (graph.evalTable (assignmentOfSet {bridge.target}))).size + 66) + loadedTime graph rows roots ∧
      peak ≤ classificationSpace graph rest output + 2 * sourcePrefixCells rows + roots.length + 1 +
        3 * (buildRoots graph).count + 2 * n + 6 := by
  let assignment := assignmentOfSet {bridge.target}
  let prior := classificationPrior width graph rows roots assignment
  let sourceProgram := packetPrelude prior
  let resident := mixedResident sourceProgram graph negativeGraph rows roots []
    negativeMatched weights b bridge.target countFits positionFits
  have included := mixed_resident_prefix_size sourceProgram graph negativeGraph rows roots []
    negativeMatched weights b bridge.target countFits positionFits
  have codeRoom : prior.size + 145 < 2 ^ width := by
    dsimp only [sourceProgram] at included
    rw [packetPrelude_size] at included
    have room : resident.size < 2 ^ width := programRoom
    change prior.size + 145 ≤ resident.size at included
    omega
  have firstRoom : 159 + 2 * n < 2 ^ width := by
    dsimp only [prior] at codeRoom
    rw [classificationPrior_size] at codeRoom
    omega
  have sourceRoomEval : (cacheHeap width (UniformDAGRun.packetHeaderHeap width n rows roots)
      rows roots).size + n + graph.nodeCount ≤ 2 ^ width := by
    simpa only [ForestInputPrefixStored.evaluationHeap_size, ForestInputPrefixStored.channelHeap_size] using
      Nat.le_of_lt evaluationRoom
  obtain ⟨evaluated, firstTicks, firstPeak, firstTrace, firstTime, firstSpace,
      evaluatedHeap, evaluatedStack, evaluatedOutput, evaluatedPC, evaluatedRunning⟩ :=
    classification_execution resident graph rows roots matched heads rootsMatch assignment
      (word width bridge.target.val :: rest) output address loaded temporary saved
      (fun position before =>
        (mixed_resident_prior_fetch sourceProgram graph negativeGraph rows roots [] negativeMatched
          weights b bridge.target countFits positionFits position
          (by rw [packetPrelude_size]; exact Nat.lt_of_lt_of_le before (Nat.le_add_right _ _))).trans
          (packetPrelude_prior_fetch prior position before)) firstRoom sourceRoomEval
  have ids : ∀ root ∈ roots, root < rows.length := by
    intro root member
    rw [rootsMatch] at member
    obtain ⟨node, _, rfl⟩ := List.mem_map.mp member
    rw [matched.length_eq]
    exact node.isLt
  have evaluatedRoom : evaluated.heap.size < 2 ^ width := by
    rw [evaluatedHeap, ← evaluation_row_view graph rows roots matched assignment]
    exact evaluationRoom
  have evaluatedPosition : evaluated.pc = word width prior.size := by
    rw [classificationPrior_size]
    exact evaluatedPC
  obtain ⟨filtered, middleTicks, middlePeak, middleTrace, middleTime, middleSpace,
      filteredHeap, filteredStack, filteredOutput, filteredPC, filteredRunning, _⟩ :=
    packet_prelude_execution prior resident
      (fun position before => mixed_resident_prior_fetch sourceProgram graph negativeGraph rows roots []
        negativeMatched weights b bridge.target countFits positionFits position before)
      n rows roots assignment (rowNodeValues graph rows matched assignment) ids evaluated
      evaluatedPosition evaluatedRunning evaluatedHeap evaluatedRoom codeRoom
  have positiveIds := classified_zero graph bridge.target rows roots matched rootsMatch healthy false
  have negativeIds := classified_zero graph bridge.target rows roots matched rootsMatch healthy true
  have loadedStack : filtered.stack = (inputPacket n 0 rows roots).map (word width) ++
      (word width 0 :: ((inputPacket n 0 rows []).map (word width) ++
        (word width bridge.target.val :: rest))) := by
    rw [positiveIds, negativeIds, evaluatedStack] at filteredStack
    simpa only [Bool.false_eq_true, if_false, if_true, List.length_nil, List.append_assoc,
      List.singleton_append, List.cons_append, List.nil_append] using filteredStack
  have packetFits : (inputPacket n 0 rows roots).length ≤ 2 ^ width := by
    have actual := matched_input_packet_length 0 graph rows roots matched rootsMatch
    obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
    have rootLength : roots.length = graph.roots.length := by rw [rootsMatch]; simp
    unfold sourceAllocatedCells sourcePrefixCells at sourceRoom
    rw [matched.length_eq, children, guards, rootLength] at sourceRoom
    omega
  obtain ⟨clearAt, loaderAt⟩ := packetPrelude_loader_at prior resident
    (fun position before => mixed_resident_prior_fetch sourceProgram graph negativeGraph rows roots []
      negativeMatched weights b bridge.target countFits positionFits position before)
  obtain ⟨loadedState, loadTrace, loadedHeap, loadedSuffix, loadedOutput, loadedPC, loadedRunning, _⟩ :=
    projected_source_load_execution resident (prior.size + 111) graph rows roots matched rootsMatch
      filtered (word width 0 :: ((inputPacket n 0 rows []).map (word width) ++
        (word width bridge.target.val :: rest))) filteredPC filteredRunning filteredHeap loadedStack
      codeRoom packetFits clearAt (by simpa only [Nat.add_assoc, Nat.reduceAdd] using loaderAt)
  have loadedPosition : loadedState.pc = word width sourceProgram.size := by
    change loadedState.pc = word width (packetPrelude prior).size
    rw [packetPrelude_size]
    simpa only [Nat.add_assoc, Nat.reduceAdd] using loadedPC
  obtain ⟨K, final, lastTicks, lastPeak, lastTrace, halted, accepted, legal, detects,
      finalHeap, finalStack, emitted, optimal, lastTime, lastSpace⟩ :=
    ForestOriginalSemantics.original_weighted_physical_execution sourceProgram graph negativeGraph forest
      rows roots [] matched rootsMatch negativeMatched weights nonnegative b bridge positive healthy detectable
      countFits positionFits loadedState rest loadedPosition loadedRunning loadedHeap loadedSuffix
      sourceRoom (by simpa using packetRoom) programRoom
  have evaluatedLive := Execution.final_storage_le firstTrace
  have filteredLive := Execution.final_storage_le middleTrace
  have loadedLive := Execution.final_storage_le loadTrace
  have evaluatedSize : evaluated.heap.size = (ForestInputPrefixStored.evaluationHeap
      (UniformDAGRun.packetHeaderHeap width n rows roots) rows roots assignment
      (graph.evalTable assignment)).size := by
    rw [evaluatedHeap, ← evaluation_row_view graph rows roots matched assignment]
  refine ⟨K, final, firstTicks + middleTicks +
    (28 + 7 * (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length)) + lastTicks,
    max (max (max firstPeak middlePeak) filtered.liveWords) lastPeak,
    ((firstTrace.append middleTrace).append loadTrace).append lastTrace, halted, accepted, legal, detects,
    finalHeap, finalStack, ?_, optimal, ?_, ?_⟩
  · simpa only [loadedOutput, filteredOutput, evaluatedOutput] using emitted
  · rw [evaluatedSize] at middleTime
    dsimp only [assignment] at middleTime
    simp only [List.length_nil, Nat.add_zero] at lastTime
    dsimp only [classificationTime, loadedTime]
    omega
  · simp only [List.length_cons] at firstSpace
    have firstBound : firstPeak ≤ classificationSpace graph rest output := by
      unfold classificationSpace
      omega
    apply max_le
    · apply max_le
      · exact max_le (by omega) (by omega)
      · omega
    · omega

private theorem healthy_families (graph : DAG n) (target : Channel n)
    (healthy : ∀ position : Fin graph.roots.length,
      graph.eval (assignmentOfSet {target}) (graph.roots.get position) = false) :
    healthyGraph graph target false = graph ∧
      healthyRootIds graph target false = graph.roots.map Fin.val ∧
      healthyRootIds graph target true = [] := by
  simp only [List.get_eq_getElem] at healthy
  have selected : Forest.healthyPositions graph target false = List.finRange graph.roots.length := by
    apply List.filter_eq_self.mpr
    intro position _
    simp [healthy position]
  have excluded : Forest.healthyPositions graph target true = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro position _
    simp [healthy position]
  constructor
  · unfold healthyGraph Forest.rootFamily
    rw [selected, List.map_get_finRange]
  · constructor
    · unfold healthyRootIds Forest.familyRootIds
      rw [selected]
      simpa only [List.map_map, Function.comp_def] using
        congrArg (List.map Fin.val) (List.map_get_finRange graph.roots)
    · simp only [healthyRootIds, excluded, Forest.familyRootIds, List.map_nil]

/-- The original-root resident uses the computed word width and descriptor
capacities for the complete original source. -/
def program (graph : DAG n) (forest : graph.FormulaForest) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (weights : Channel n → W) (b : Nat) (target : Channel n) :
    Program (chosenMixedWidth graph) 8 :=
  mixedResident (packetPrelude (classificationPrior (chosenMixedWidth graph) graph rows roots
    (assignmentOfSet {target}))) (healthyGraph graph target false) (healthyGraph graph target true)
    rows (healthyRootIds graph target false) (healthyRootIds graph target true)
    (Forest.rootFamily_rows graph (Forest.healthyPositions graph target true) rows matched)
    weights b target (original_descriptor_capacity graph forest target).1
      (original_descriptor_capacity graph forest target).2

set_option maxHeartbeats 1800000 in
/-- The complete cold execution on the original computed capacities emits an
attained maximum physical detecting set. Both fetched time and live storage
are linear in the original forest size, including every declared occurrence. -/
theorem chosen_execution (graph : DAG n) (forest : graph.FormulaForest)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched) (rootsMatch : RootsMatch graph roots)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : Nat) (bridge : Physical.Bridge n) (positive : 0 < b)
    (healthy : ∀ position : Fin graph.roots.length,
      graph.eval (assignmentOfSet {bridge.target}) (graph.roots.get position) = false)
    (detectable : Physical.BridgeDetectable (b := b) bridge true graph.observations)
    (rest output : List (Word (chosenMixedWidth graph)))
    (address loaded temporary : Word (chosenMixedWidth graph))
    (saved : Fin 8 → Word (chosenMixedWidth graph)) :
    ∃ K final ticks peak,
      Execution (program graph forest rows roots matched weights b bridge.target)
        (classificationInitial (chosenMixedWidth graph) graph rows roots (assignmentOfSet {bridge.target})
          bridge.target rest output address loaded temporary saved) final ticks peak ∧
      final.halted = true ∧ final.reg 4 = word (chosenMixedWidth graph) 1 ∧
      Admissible b bridge.target K ∧
      Physical.BridgeInputDetects bridge true graph.observations
        (Physical.realizeBridge bridge positive K) true ∧
      final.heap = #[] ∧ final.stack = rest ∧
      final.output = List.ofFn (fun channel : Channel n =>
        boolWord (chosenMixedWidth graph) (decide (channel ∈ K))) ++ output ∧
      (∀ L, Admissible b bridge.target L →
        Physical.BridgeInputDetects bridge true graph.observations
          (Physical.realizeBridge bridge positive L) true →
        GenericWeight.total weights L ≤ GenericWeight.total weights K) ∧
      ticks ≤ 1000 * (forestSize graph + 1) ∧
      peak ≤ 200 * (forestSize graph + 1) + rest.length + output.length := by
  obtain ⟨sameGraph, positiveIds, negativeIds⟩ := healthy_families graph bridge.target healthy
  rw [← rootsMatch] at positiveIds
  have capacities := original_descriptor_capacity graph forest bridge.target
  rw [sameGraph] at capacities
  have rooms := original_numeric_capacity graph forest rows roots matched rootsMatch weights b bridge.target
    (original_descriptor_capacity graph forest bridge.target).1
    (original_descriptor_capacity graph forest bridge.target).2
  simp only [sameGraph, positiveIds, negativeIds, List.length_nil, Nat.add_zero] at rooms
  obtain ⟨K, final, ticks, peak, trace, halted, accepted, legal, detects,
      finalHeap, finalStack, emitted, optimal, time, space⟩ :=
    execution graph (healthyGraph graph bridge.target true) forest rows roots matched heads rootsMatch
      (Forest.rootFamily_rows graph (Forest.healthyPositions graph bridge.target true) rows matched)
      weights nonnegative b bridge positive healthy detectable capacities.1 capacities.2 rest output
      address loaded temporary saved rooms.1 rooms.2.1 rooms.2.2.1 rooms.2.2.2.1
  have prefixSize := source_prefix_size graph rows matched
  have rootLength : roots.length = graph.roots.length := by rw [rootsMatch]; simp
  have descriptorCount := actual_descriptor_count_bound graph forest
  have sourceBudget := ForestWeightedCaller.sourceBudget_exact graph
  have evaluationSize : (ForestInputPrefixStored.evaluationHeap
      (UniformDAGRun.packetHeaderHeap (chosenMixedWidth graph) n rows roots) rows roots
      (assignmentOfSet {bridge.target}) (graph.evalTable (assignmentOfSet {bridge.target}))).size =
      sourcePrefixCells rows + roots.length + n + graph.nodeCount := by
    simp only [ForestInputPrefixStored.evaluationHeap_size,
      cacheHeap_size, UniformDAGRun.packetHeaderHeap_size]
    unfold sourcePrefixCells
    omega
  refine ⟨K, final, ticks, peak, ?_, halted, accepted, legal, detects,
    finalHeap, finalStack, emitted, optimal, ?_, ?_⟩
  · simpa only [program, sameGraph, positiveIds, negativeIds] using trace
  · simp only [classificationTime, loadedTime, sourceAllocatedCells, evaluationSize,
      sourceBudget, prefixSize, rootLength] at time
    unfold forestSize
    omega
  · simp only [classificationSpace, prefixSize, rootLength] at space
    unfold forestSize
    omega

end Controller.Cost.ForestWeightedCold
