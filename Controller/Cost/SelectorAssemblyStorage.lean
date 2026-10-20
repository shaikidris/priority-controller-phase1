module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.SupportAssemblyStorage
public import Controller.Cost.ResolvedSearchConstruction

@[expose] public section


/-! Source-driven selector assembly retains both layout materializations and
its shared returning/native callbacks. Word-list formation traces include every
emitted block and relocation. -/
namespace Controller.Cost.SelectorAssemblyStorage

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestIndexedOperands Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestClauseProgramConstruction (environment)
open Controller.Cost.AssemblyStorage Controller.Cost.ExtensionConstructionRecipes

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
attribute [local irreducible] ResolvedCallbackConstruction.build
  ResolvedBodyConstruction.build ResolvedNativeSourceConstruction.build
  ResolvedNativeQueryConstruction.build ResolvedFrontConstruction.prepare

theorem body (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots)
    (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount) (found done : Nat) :
    Bounded (ResolvedBodyConstruction.build width graph rows roots b target reference found done).1
      (150000000 * (graph.countedSize + 1)) := by
  let p := ResolvedOutputBody.positions graph found done
  let packet := ResolvedRootSource.packet width n rows roots (fun _ : Fin graph.nodeCount =>
      false) 0
  let source := cacheHeap width packet rows roots
  have mask := SupportAssemblyStorage.mask width graph.liveAndCount
  have zero := constant (width := width) (registers := 8) 3 0
  have driver := wordCode (width := width)
    (environment [p.loop, graph.roots.length, UniformDAGRuntimeOutputs.rootBase packet rows,
      4, 5, p.seek, p.done, graph.liveAndCount]) (rootDriver.constructionRecipe width)
  have advance := wordCode (width := width) (environment [p.loop])
    (ResolvedRootLoop.advanceCode.constructionRecipe width)
  have ending := wordCode (width := width)
    (environment [p.seek, graph.liveAndCount, source.size, p.call])
    (traversal.constructionRecipe width)
  have jump := branch (width := width) (registers := 8) 0 (p.loop + 23)
  obtain ⟨callback, callbackBound⟩ := ResolvedQueryStorage.callback width graph packet rows roots
    matched rootMatches b target reference 4 p.call (source.size + graph.liveAndCount) p.found
    (SupportTraversal.backtrack p.seek)
    (ResolvedRootSource.source_bound graph (fun _ => false) 0 matched rootMatches)
  have call : Bounded (ResolvedCallbackConstruction.build width graph packet rows roots b target
      reference 4 p.call (source.size + graph.liveAndCount) p.found
      (SupportTraversal.backtrack p.seek)).1
      (100000000 * (graph.countedSize + 1) + 1000 * packet.size) :=
    .enlarge (.callback graph packet rows roots b target reference 4 p.call
      (source.size + graph.liveAndCount) p.found (SupportTraversal.backtrack p.seek) callback)
      callbackBound
  have assembled := join (join (join (join (join (join mask zero) driver) advance) ending)
      jump) call
  have ands := graph.liveAndCount_le_nodeCount
  have size := graph.countedSize_eq
  have packetLength : packet.size = 5 + graph.nodeCount := ResolvedRootSource.packet_size _
  have maskLength : (SupportTraversalConstruction.mask width graph.liveAndCount).1.length =
      2 * graph.liveAndCount := by
    rw [SupportTraversalConstruction.mask_image]
    simp [SharedCoordinateTable.code, List.length_flatMap]
  unfold ResolvedBodyConstruction.build
  dsimp only
  exact .enlarge assembled (by
    simp only [List.length_append, List.length_cons, List.length_nil, evaluate, List.length_map,
      rootDriver.constructionRecipe_work, ResolvedRootLoop.advanceCode.constructionRecipe_work,
      traversal.constructionRecipe_work]
    have driverLength : (rootDriver.constructionRecipe width).length = 23 := rfl
    have advanceLength : (ResolvedRootLoop.advanceCode.constructionRecipe width).length = 5 := rfl
    have endingLength : (traversal.constructionRecipe width).length = 36 := rfl
    rw [driverLength, advanceLength, endingLength, maskLength]
    omega)

theorem nativeSource (parameters : Parameters) (width : Nat) (packet : Array (Word width))
    (rows : List Row) (roots : List Nat) (matched : RowsMatch parameters.decoder rows)
    (rootMatches : RootsMatch parameters.decoder roots)
    (reference : Fin parameters.decoder.nodeCount) (rootSlot entry sourceCount : Nat)
    (packetBound : packet.size + sourceCount ≤ 100 * (parameters.decoder.countedSize + 1)) :
    Bounded (ResolvedNativeSourceConstruction.build parameters width packet rows roots reference
      rootSlot entry sourceCount).1
      (3000000000 * (parameters.decoder.countedSize + 1) +
        200000000 * ((selectedSize parameters).total + 1)) := by
  let front := ResolvedFrontConstruction.prepare width parameters.decoder packet rows roots
    parameters.buses parameters.bridge.target rootSlot entry sourceCount
  obtain ⟨frontCertificate, frontBound⟩ := ResolvedFrontStorage.complete width parameters.decoder
    packet rows roots matched rootMatches parameters.buses parameters.bridge.target reference
    rootSlot entry sourceCount
  obtain ⟨nativeCertificate, nativeBound⟩ := ResolvedQueryStorage.native parameters width
    (entry + front.1.length) 0 reference
  have first := Trace.front parameters.decoder packet rows roots parameters.buses
    parameters.bridge.target rootSlot entry sourceCount frontCertificate
  have second := Trace.nativeQuery parameters (entry + front.1.length) 0 reference nativeCertificate
  have assembled := join first second
  have length : front.1.length ≤ 200 * (parameters.decoder.countedSize + 1) := by
    dsimp only [front]
    rw [ResolvedFrontConstruction.image width parameters.decoder packet rows roots matched
      parameters.buses parameters.bridge.target reference]
    exact ResolvedSourcePrepare.code_bound parameters.decoder packet rows roots parameters.buses
      parameters.bridge.target reference
  unfold ResolvedNativeSourceConstruction.build
  dsimp only
  exact .enlarge assembled (by
    dsimp only [front] at *
    omega)

theorem search (parameters : Parameters) (width : Nat) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch parameters.decoder rows) (rootMatches : RootsMatch parameters.decoder
        roots)
    (reference : Fin parameters.decoder.nodeCount) :
    Bounded (ResolvedSearchConstruction.build parameters width rows roots reference).1
      (4000000000 * (parameters.decoder.countedSize + 1) +
        300000000 * ((selectedSize parameters).total + 1)) := by
  let graph := parameters.decoder
  let packet := ResolvedRootSource.packet width parameters.channels rows roots
    (fun _ : Fin graph.nodeCount => false) 0
  let sourceCount := (cacheHeap width packet rows roots).size + graph.liveAndCount
  let provisional := ResolvedBodyConstruction.build width graph rows roots parameters.buses
    parameters.bridge.target reference 0 0
  let start := provisional.1.length
  let native := ResolvedNativeSourceConstruction.build parameters width packet rows roots reference
    4 0 sourceCount
  have first := body width graph rows roots matched rootMatches parameters.buses
    parameters.bridge.target reference 0 0
  have sourceBound := ResolvedRootSource.source_bound (width := width) graph (fun _ => false) 0
    matched rootMatches
  simp only [ResolvedRootSource.source] at sourceBound
  have size := graph.countedSize_eq
  have packetLength : packet.size = 5 + graph.nodeCount := ResolvedRootSource.packet_size _
  have packetBound : packet.size + sourceCount ≤ 100 * (graph.countedSize + 1) := by
    dsimp only [sourceCount, packet] at *
    omega
  have nativeTrace := nativeSource parameters width packet rows roots matched rootMatches reference
    4 0 sourceCount packetBound
  have bodyTrace := body width graph rows roots matched rootMatches parameters.buses
    parameters.bridge.target reference start (start + native.1.length)
  have moved := relocate nativeTrace start
  have zero := constant (width := width) (registers := 8) 4 0
  have halt := fixed (Instruction.halt : Instruction width 8) (by trivial)
  have assembled := join (join bodyTrace moved) (join zero halt)
  have bodyLength : (ResolvedBodyConstruction.build width graph rows roots parameters.buses
      parameters.bridge.target reference start (start + native.1.length)).1.length ≤
      1400 * (graph.countedSize + 1) := by
    rw [ResolvedBodyConstruction.image width graph rows roots matched]
    exact ResolvedOutputBody.code_bound graph rows roots matched rootMatches (fun _ => false)
      parameters.buses parameters.bridge.target reference start (start + native.1.length)
  have nativeLength : native.1.length ≤ 1200 * (graph.countedSize + 1) +
      34 * (selectedSize parameters).total := by
    dsimp only [native]
    rw [ResolvedNativeSourceConstruction.image parameters width packet rows roots matched]
    exact ResolvedNativeSource.code_bound parameters packet rows roots reference
  have firstLength : provisional.1.length ≤ 1400 * (graph.countedSize + 1) := by
    dsimp only [provisional]
    rw [ResolvedBodyConstruction.image width graph rows roots matched]
    exact ResolvedOutputBody.code_bound graph rows roots matched rootMatches (fun _ => false)
      parameters.buses parameters.bridge.target reference 0 0
  have movedLength : (ProgramRelocationConstruction.build start native.1).1.length =
      native.1.length := by
    rw [ProgramRelocationConstruction.build_image, ResidentSegment.code, List.length_map]
  dsimp only [ResolvedSearchConstruction.build]
  exact .enlarge (.preparation first assembled) (by
    simp only [List.length_append, List.length_cons, List.length_nil]
    dsimp only [native, graph, packet, sourceCount, provisional, start] at *
    omega)

end Controller.Cost.SelectorAssemblyStorage
