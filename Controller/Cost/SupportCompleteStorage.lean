module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.SupportAssemblyStorage

@[expose] public section


/-! Complete support-side assembly traces, including source preparation and
native finishing. Healthy values are runtime data, not constructor inputs. -/
namespace Controller.Cost.SupportCompleteStorage

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestIndexedOperands Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestClauseProgramConstruction (environment)
open Controller.Cost.AssemblyStorage Controller.Cost.ExtensionConstructionRecipes

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
attribute [local irreducible] SupportCandidateConstruction.callback
    SupportTraversalConstruction.build
  SupportColdConstruction.healthy SupportColdConstruction.build
      SupportNativeConstruction.continuation

theorem body (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (k b : Nat) (target : Channel n) (found done : Nat) :
    Bounded (SupportTraversalConstruction.build width graph rows roots k b target found done).1
      (1000 * (SupportTraversalConstruction.build width graph rows roots k b target found
          done).2) := by
  let packet := SupportCandidate.header width n rows roots (fun _ : Fin graph.nodeCount => false)
  let seek := SupportSearchBody.seek n
  let call := SupportSearchBody.call n
  let cleanup := SupportSearchBody.cleanup n b roots
  have first := SupportAssemblyStorage.mask width n
  have entry := wordCode (width := width) (environment [n, min (k + 1) n])
    (enter.constructionRecipe width)
  have tree := wordCode (width := width)
    (environment [seek, n, (cacheHeap width packet rows roots).size, call])
    (traversal.constructionRecipe width)
  have jump := branch (width := width) (registers := 8) 0 cleanup
  have callback := SupportAssemblyStorage.callback width n b packet rows roots target.val call found
    (SupportTraversal.backtrack seek)
  have ending := wordCode (width := width) (environment [cleanup, done, n])
    (SharedEvaluationReclaim.code.constructionRecipe width)
  have assembled := join (join (join (join (join first entry) tree) jump) callback) ending
  have maskClock := SupportTraversalConstruction.mask_clock width n
  unfold SupportTraversalConstruction.build
  dsimp only
  exact .enlarge assembled (by
    simp only [List.length_append, List.length_cons, List.length_nil,
      enter.constructionRecipe_work, traversal.constructionRecipe_work,
      SharedEvaluationReclaim.code.constructionRecipe_work]
    dsimp only [seek, call, cleanup, packet] at *
    omega)

theorem healthy (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots) (entry : Nat) :
    Bounded (SupportColdConstruction.healthy width n graph.nodeCount rows roots entry).1
      (1000000 * (graph.countedSize + 1)) := by
  let header := UniformDAGRun.packetHeaderHeap width n rows roots
  let source := (cacheHeap width header rows roots).size
  let operands := SupportHealthyLayout.plan width n graph.nodeCount header rows roots
  have round := SupportAssemblyStorage.sourceRound width n header rows roots entry
  have repack := SupportAssemblyStorage.repack width (entry + 126) (source + n + graph.nodeCount)
    operands
  have assembled := join round repack
  have length : (SupportControllerConstruction.sourceRound width n header rows roots entry).1.length
      = 126 := by
    rw [SupportControllerConstruction.sourceRound_image, Array.length_toList,
      SupportSourceRound.code_size]
  have planLength : operands.length = source + graph.nodeCount :=
    SupportHealthyLayout.plan_length header rows roots
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have rootLength : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have size := graph.countedSize_eq
  have sourceBound : source + graph.nodeCount ≤ 8 * graph.countedSize + 5 := by
    simp only [source, header, cacheHeap_size, UniformDAGRun.packetHeaderHeap_size,
      matched.length_eq, children, guards, rootLength]
    omega
  unfold SupportColdConstruction.healthy
  dsimp only
  exact .enlarge assembled (by omega)

theorem cold (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots) :
    Bounded (SupportColdConstruction.build width graph rows roots).1
      (2000000 * (graph.countedSize + 1)) := by
  have parked := SupportAssemblyStorage.park width 0 (SharedDetectorPrepared.packetSize graph)
  have preparation := healthy width graph rows roots matched rootMatches
    (2 * SharedDetectorPrepared.packetSize graph)
  have assembled := join parked preparation
  have count := SupportColdPrepare.packet_bound graph
  have length : (StackPacketConstruction.park width 0
      (SharedDetectorPrepared.packetSize graph)).1.length =
      2 * SharedDetectorPrepared.packetSize graph := by
    rw [StackPacketConstruction.park_image, SharedWitnessPark.code_length]
  unfold SupportColdConstruction.build
  dsimp only
  exact .enlarge assembled (by omega)

theorem continuation (parameters : Parameters) (width base entry : Nat) :
    Bounded (SupportNativeConstruction.continuation parameters width base entry).1
      (3000000 * ((selectedSize parameters).total + 1)) := by
  let first := SupportCandidateConstruction.prepare width parameters.buses
    (base + parameters.bridge.target.val)
  let cursor := entry + first.length
  have prepared : Bounded first 10000 := by
    dsimp only [first, SupportCandidateConstruction.prepare]
    split
    · exact .enlarge (wordCode _ _) (by
        rw [SupportTarget.saveCode.constructionRecipe_work]; decide)
    · exact .enlarge .empty (by omega)
  have copied := SupportAssemblyStorage.copy width cursor (cursor + 10) base parameters.channels
  have one := constant (width := width) (registers := 8) 4 1
  have native := AssemblyStorage.native parameters width (base + parameters.channels) (cursor + 11)
  have assembled := join (join (join prepared copied) one) native
  have firstLength : first.length ≤ 5 := by
    dsimp only [first]
    rw [SupportCandidateConstruction.prepare_image]
    by_cases bus : parameters.buses = 1 <;>
      simp [SupportCallback.prepareCode, bus, SupportTarget.saveCode]
  have copyLength : (StackPacketConstruction.copy width cursor (cursor + 10) base
      parameters.channels).length = 10 := by
    rw [StackPacketConstruction.copy_image, Array.length_toList, SharedWitnessCopy.code_size]
  unfold SupportNativeConstruction.continuation
  dsimp only
  exact .enlarge assembled (by
    simp only [List.length_append, List.length_cons, List.length_nil, copyLength]
    omega)

theorem support (parameters : Parameters) (width : Nat) (rows : List Row) (roots : List Nat)
    (k : Nat) (matched : RowsMatch parameters.decoder rows)
    (rootMatches : RootsMatch parameters.decoder roots) :
    Bounded (SupportNativeConstruction.build parameters width rows roots k).1
      (300000000 * (parameters.decoder.countedSize + 1) +
        4000000 * ((selectedSize parameters).total + 1)) := by
  let base := (SupportNativeSearch.source parameters width rows roots).size
  let native := SupportNativeConstruction.continuation parameters width base 0
  let start := SupportNativeSearch.start parameters roots
  have nativeTrace := continuation parameters width base 0
  have traversal := body width parameters.decoder rows roots k parameters.buses
    parameters.bridge.target start (start + native.1.length)
  have moved := relocate nativeTrace start
  have assembled := join traversal moved
  have bodyClock := SupportTraversalConstruction.clock width parameters.decoder rows roots k
    parameters.buses parameters.bridge.target start (start + native.1.length)
  have bodyLength : (SupportTraversalConstruction.build width parameters.decoder rows roots k
      parameters.buses parameters.bridge.target start (start + native.1.length)).1.length ≤
      300 * (parameters.decoder.countedSize + 1) := by
    rw [SupportTraversalConstruction.image width parameters.decoder rows roots (fun _ => false)]
    rw [SupportSearchBody.code_length]
    simp only [SupportSearchBody.cleanup, SupportSearchBody.call, SupportSearchBody.seek]
    have size := parameters.decoder.countedSize_eq
    have rootLength : roots.length = parameters.decoder.roots.length := by rw [rootMatches]; simp
    rw [rootLength]
    split <;> omega
  have nativeLength : native.1.length ≤ 34 * (selectedSize parameters).total + 17 := by
    dsimp only [native]
    rw [SupportNativeConstruction.continuation_image]
    exact SupportNativeSource.code_bound parameters
  obtain ⟨children, guards⟩ := matched_incidence_lengths parameters.decoder rows matched
  have rootLength : roots.length = parameters.decoder.roots.length := by rw [rootMatches]; simp
  simp only [matched.length_eq, children, guards, rootLength] at bodyClock
  have size := parameters.decoder.countedSize_eq
  dsimp only [SupportNativeConstruction.build]
  exact .enlarge assembled (by
    dsimp only [native] at *
    omega)

end Controller.Cost.SupportCompleteStorage
