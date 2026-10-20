module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ResolvedNodeConstruction

@[expose] public section


/-! One source-order pass forms an expansion query. Cached row offsets, dense
selector ranks and the scalar source end are shared by all node records. The
clock counts indexed source-field reads, arithmetic and operand/list writes. -/
namespace Controller.Cost.ResolvedPlanProducer

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Cost.ForestIndexedOperands Controller.Extensions.ResolvedSourceEmit
open Controller.Cost.ResolvedNodeConstruction (literal)

def nodes (width : Nat) (graph : DAG n) (packet : Array (Word width))
    (cache : ResolvedPlanConstruction.Cache graph) (sourceEnd : Nat) :
    List (Fin graph.nodeCount) → List (Operand width) × Nat
  | [] => ([], 1)
  | index :: rest =>
      let current := ResolvedNodeConstruction.form width graph packet cache sourceEnd index
      let tail := nodes width graph packet cache sourceEnd rest
      (current.1 ++ tail.1, current.2 + tail.2 + 8 * current.1.length + 20)

def budget (graph : DAG n) (indices : List (Fin graph.nodeCount)) : Nat :=
  indices.length + (indices.map fun i => (graph.node i).children.length).sum +
    (indices.map fun i => (graph.node i).guardLabels.length).sum

theorem node_length (width : Nat) (graph : DAG n) (packet : Array (Word width))
    (cache : ResolvedPlanConstruction.Cache graph) (sourceEnd : Nat) (index : Fin graph.nodeCount) :
    (ResolvedNodeConstruction.form width graph packet cache sourceEnd index).1.length ≤
      4 + 2 * (graph.node index).children.length + (graph.node index).guardLabels.length := by
  cases gate : graph.node index <;> simp [ResolvedNodeConstruction.form, gate, Gate.children,
    Gate.guardLabels,
    List.length_flatMap] <;> omega

theorem nodes_clock (width : Nat) (graph : DAG n) (packet : Array (Word width))
    (cache : ResolvedPlanConstruction.Cache graph) (sourceEnd : Nat) (indices : List (Fin
      graph.nodeCount)) :
    (nodes width graph packet cache sourceEnd indices).2 ≤ 200 * budget graph indices + 1 := by
  induction indices with
  | nil => simp [nodes, budget]
  | cons index rest ih =>
      have formed := ResolvedNodeConstruction.clock width graph packet cache sourceEnd index
      have length := node_length width graph packet cache sourceEnd index
      simp only [nodes, budget, List.length_cons, List.map_cons, List.sum_cons] at *
      omega

theorem nodes_image (width : Nat) (graph : DAG n) (packet : Array (Word width))
    (rows : List Row) (roots : List Nat) (cache : ResolvedPlanConstruction.Cache graph) (sourceEnd :
      Nat)
    (storedEnd : sourceEnd = (cacheHeap width packet rows roots).size) (indices : List (Fin
      graph.nodeCount)) :
    (nodes width graph packet cache sourceEnd indices).1 =
      indices.flatMap (ResolvedPlanConstruction.node width graph packet rows roots cache) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      simp only [nodes, ResolvedNodeConstruction.image width graph packet rows roots cache sourceEnd
        storedEnd index,
        ih, List.flatMap_cons]

def touch (width ambient : Nat) : List (Operand width) :=
  (List.finRange ambient).flatMap fun coordinate => [literal width coordinate.val, literal width
    coordinate.val]

def channels (width n b : Nat) (target : Channel n) : List (Operand width) :=
  (List.finRange n).map (fun channel => literal width channel.val) ++
    if b = 1 then [literal width target.val] else []

def build (width : Nat) (graph : DAG n) (packet : Array (Word width)) (cache :
  ResolvedPlanConstruction.Cache graph)
    (sourceEnd b : Nat) (target : Channel n) (rootSlot : Nat) : List (Operand width) × Nat :=
  let emitted := nodes width graph packet cache sourceEnd (List.finRange graph.nodeCount)
  let image := touch width (n + graph.nodeCount) ++ emitted.1 ++ channels width n b target ++ [.read
    rootSlot (word width n)]
  (image, emitted.2 + 100 * (n + graph.nodeCount + 1) + 16 * image.length + 100)

theorem image (width : Nat) (graph : DAG n) (packet : Array (Word width)) (rows : List Row) (roots :
  List Nat)
    (cache : ResolvedPlanConstruction.Cache graph) (sourceEnd : Nat) (storedEnd : sourceEnd =
      (cacheHeap width packet rows roots).size)
    (b : Nat) (target : Channel n) (rootSlot : Nat) :
    (build width graph packet cache sourceEnd b target rootSlot).1 =
      ResolvedPlanConstruction.query width graph packet rows roots cache b target rootSlot := by
  have touched : touch width (n + graph.nodeCount) = ResolvedSourcePlan.literals width
    (ResolvedSourcePlan.touchCoordinates graph) := by
    simp [touch, ResolvedSourcePlan.literals, ResolvedSourcePlan.touchCoordinates,
      SharedZeroTemplate.touchRows,
      literal, List.flatten_eq_flatMap, List.flatMap_map, List.map_flatMap, List.map_map,
        Function.comp_def]
  have coordinateList : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem <;> simp
  have coordinates : (List.finRange n).map (fun channel => Operand.literal (word width channel.val))
    =
      (List.range n).map (fun value => Operand.literal (word width value)) := by
    simpa only [List.map_map, Function.comp_def] using congrArg (List.map (fun value =>
      Operand.literal (word width value))) coordinateList
  have channelWords : channels width n b target = ResolvedSourcePlan.literals width
    (ResolvedSourcePlan.channelCoordinates graph b target) := by
    by_cases one : b = 1 <;>
      simp [channels, coordinates, one, ResolvedSourcePlan.literals,
        ResolvedSourcePlan.channelCoordinates, ResolvedSourcePlan.coordinates,
        DAG.channelClauses, DAG.trueUnitClauses, DAG.falseUnitClauses, ZeroSystem.positiveClause,
        ZeroSystem.implicationClause, DAG.zeroIndex, literal, List.map_map, Function.comp_def]
  simp only [build, nodes_image width graph packet rows roots cache sourceEnd storedEnd,
    ResolvedPlanConstruction.query, ResolvedPlanConstruction.forwards, touched, channelWords,
      List.append_assoc]

theorem full_budget (graph : DAG n) :
    budget graph (List.finRange graph.nodeCount) =
      graph.nodeCount + graph.childIncidences + graph.guardIncidences := by
  simp only [budget, List.length_finRange, DAG.childIncidences, DAG.guardIncidences,
    List.ofFn_eq_map]

theorem clock (width : Nat) (graph : DAG n) (packet : Array (Word width)) (rows : List Row) (roots :
  List Nat)
    (matched : RowsMatch graph rows) (sourceEnd : Nat) (storedEnd : sourceEnd = (cacheHeap width
      packet rows roots).size)
    (b : Nat) (target : Channel n) (rootSlot : Nat) (reference : Fin graph.nodeCount) :
    (build width graph packet (ResolvedPlanConstruction.prepare graph rows) sourceEnd b target
      rootSlot).2 ≤
      1000 * (graph.countedSize + 1) := by
  have formed := nodes_clock width graph packet (ResolvedPlanConstruction.prepare graph rows)
    sourceEnd
    (List.finRange graph.nodeCount)
  rw [full_budget] at formed
  have size := graph.countedSize_eq
  have rowsBound := ResolvedResident.rows_bound graph ∅ b target reference
  have length : (build width graph packet (ResolvedPlanConstruction.prepare graph rows) sourceEnd b
    target rootSlot).1.length ≤
      11 * (graph.countedSize + 1) := by
    rw [image width graph packet rows roots _ sourceEnd storedEnd,
      ResolvedPlanConstruction.query_image width graph packet rows roots matched b target rootSlot,
      ResolvedSourcePlan.query_length graph packet rows roots b target reference]
    omega
  change (nodes width graph packet (ResolvedPlanConstruction.prepare graph rows) sourceEnd
      (List.finRange graph.nodeCount)).2 + 100 * (n + graph.nodeCount + 1) +
    16 * (build width graph packet (ResolvedPlanConstruction.prepare graph rows) sourceEnd b target
      rootSlot).1.length + 100 ≤ _
  omega

def sourceEnd (packet : Array (Word width)) (cache : ResolvedPlanConstruction.Cache graph) (roots :
  Nat) : Nat :=
  packet.size + 6 * cache.offsets.rows.size + cache.offsets.children + cache.offsets.guards + roots

theorem sourceEnd_image (graph : DAG n) (packet : Array (Word width)) (rows : List Row) (roots :
  List Nat) :
    sourceEnd packet (ResolvedPlanConstruction.prepare graph rows) roots.length = (cacheHeap width
      packet rows roots).size := by
  have counts := ForestCompilerOffsets.run_totals rows ForestCompilerOffsets.initial
  simp only [show ForestCompilerOffsets.initial.children = 0 from rfl,
    show ForestCompilerOffsets.initial.guards = 0 from rfl,
    show ForestCompilerOffsets.initial.rows.size = 0 from rfl, Nat.zero_add] at counts
  simp only [sourceEnd, ResolvedPlanConstruction.prepare, counts.1, counts.2.1, counts.2.2.1,
    cacheHeap_size]

def compile (width : Nat) (graph : DAG n) (packet : Array (Word width)) (rows : List Row) (roots :
  List Nat)
    (b : Nat) (target : Channel n) (rootSlot : Nat) : List (Operand width) × Nat :=
  let cache := ResolvedPlanConstruction.prepare graph rows
  let endAddress := sourceEnd packet cache roots.length
  let emitted := build width graph packet cache endAddress b target rootSlot
  (emitted.1, emitted.2 + 100 * (rows.length + (rowChildren rows).length + (rowGuards rows).length +
    roots.length + graph.nodeCount + 1))

theorem compile_image (width : Nat) (graph : DAG n) (packet : Array (Word width)) (rows : List Row)
  (roots : List Nat)
    (matched : RowsMatch graph rows) (b : Nat) (target : Channel n) (rootSlot : Nat) :
    (compile width graph packet rows roots b target rootSlot).1 =
      ResolvedSourcePlan.query width graph packet rows roots b target rootSlot := by
  simp only [compile, image width graph packet rows roots _ _ (sourceEnd_image graph packet rows
    roots),
    ResolvedPlanConstruction.query_image width graph packet rows roots matched b target rootSlot]

theorem compile_clock (width : Nat) (graph : DAG n) (packet : Array (Word width)) (rows : List Row)
  (roots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots) (b : Nat) (target :
      Channel n)
    (rootSlot : Nat) (reference : Fin graph.nodeCount) :
    (compile width graph packet rows roots b target rootSlot).2 ≤ 2000 * (graph.countedSize + 1) :=
      by
  have formed := clock width graph packet rows roots matched _ (sourceEnd_image graph packet rows
    roots) b target rootSlot reference
  have incidence := matched_incidence_lengths graph rows matched
  have rootsLength : roots.length = graph.roots.length := by rw [rootMatches, List.length_map]
  have size := graph.countedSize_eq
  simp only [compile]
  simp only [matched.length_eq, incidence.1, incidence.2, rootsLength] at formed ⊢
  omega

end Controller.Cost.ResolvedPlanProducer
