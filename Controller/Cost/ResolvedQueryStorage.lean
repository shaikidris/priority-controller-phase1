/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ResolvedFrontStorage
import Controller.Cost.ResolvedCallbackConstruction
import Controller.Cost.ResolvedNativeQueryConstruction

/-! Returning and native selector queries retain the source metadata, emitted
front, query image and return image. Every scalar placement is supported by the
same fixed-recipe traces; clause-profile scans have linear peak storage. -/
namespace Controller.Cost.ResolvedQueryStorage

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Extensions
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.ForestIndexedOperands

abbrev metadata (graph : DAG n) (b : Nat) (target : Channel n)
    (reference : Fin graph.nodeCount) :=
  (ResolvedNativeLayoutConstruction.build graph b target reference).1

abbrev solver (width : Nat) (graph : DAG n) (packet : Array (Word width))
    (rows : List Row) (roots : List Nat) (b : Nat) (target : Channel n)
    (rootSlot entry sourceCount : Nat) :=
  entry + 13 + (ResolvedFrontConstruction.prepare width graph packet rows roots b target rootSlot
    (entry + 13) sourceCount).1.length

structure Callback (width : Nat) (graph : DAG n) (packet : Array (Word width))
    (rows : List Row) (roots : List Nat) (b : Nat) (target : Channel n)
    (reference : Fin graph.nodeCount) (rootSlot entry sourceCount found rejected : Nat) where
  layout : ResolvedMetadataStorage.Certificate graph b target reference
  front : ResolvedFrontStorage.Certificate width graph packet rows roots b target rootSlot
    (entry + 13) sourceCount
  query : QuietQueryStorage.Certificate width
    (solver width graph packet rows roots b target rootSlot entry sourceCount)
    (metadata graph b target reference).protectedEnd (n + graph.nodeCount)
    (metadata graph b target reference).scratchEnd (metadata graph b target reference).references
  restored : PacketTransferStorage.ReturnCertificate width
    (solver width graph packet rows roots b target rootSlot entry sourceCount +
      (QuietQueryConstruction.build width
        (solver width graph packet rows roots b target rootSlot entry sourceCount)
        (metadata graph b target reference).protectedEnd (n + graph.nodeCount)
        (metadata graph b target reference).scratchEnd
        (metadata graph b target reference).references).1.length)
    (metadata graph b target reference).protectedEnd sourceCount found rejected
  fixed : PacketTransferStorage.Fixed width

def callbackBuffers (width : Nat) (graph : DAG n) (packet : Array (Word width))
    (rows : List Row) (roots : List Nat) (b : Nat) (target : Channel n)
    (reference : Fin graph.nodeCount) (rootSlot entry sourceCount found rejected : Nat)
    (certificate : Callback width graph packet rows roots b target reference rootSlot entry
      sourceCount found rejected) :=
  let data := metadata graph b target reference
  let cursor := solver width graph packet rows roots b target rootSlot entry sourceCount
  let query := QuietQueryConstruction.build width cursor data.protectedEnd (n + graph.nodeCount)
    data.scratchEnd data.references
  ResolvedMetadataStorage.buffers graph b target reference certificate.layout +
  ResolvedFrontStorage.buffers width graph packet rows roots b target rootSlot (entry + 13)
    sourceCount certificate.front +
  QuietQueryStorage.buffers width cursor data.protectedEnd (n + graph.nodeCount) data.scratchEnd
    data.references certificate.query +
  PacketTransferStorage.returnBuffers width (cursor + query.1.length) data.protectedEnd
    sourceCount found rejected certificate.restored +
  256 * ((ResolvedCallbackConstruction.build width graph packet rows roots b target reference
    rootSlot entry sourceCount found rejected).1.length + 1) + 100000

theorem callback (width : Nat) (graph : DAG n) (packet : Array (Word width))
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (rootMatches : RootsMatch graph roots) (b : Nat) (target : Channel n)
    (reference : Fin graph.nodeCount) (rootSlot entry sourceCount found rejected : Nat)
    (sourceBound : sourceCount ≤ 40 * (graph.countedSize + 1)) :
    ∃ certificate : Callback width graph packet rows roots b target reference rootSlot entry
      sourceCount found rejected,
      callbackBuffers width graph packet rows roots b target reference rootSlot entry sourceCount
        found rejected certificate ≤ 100000000 * (graph.countedSize + 1) + 1000 * packet.size := by
  let data := metadata graph b target reference
  let cursor := solver width graph packet rows roots b target rootSlot entry sourceCount
  let query := QuietQueryConstruction.build width cursor data.protectedEnd (n + graph.nodeCount)
    data.scratchEnd data.references
  obtain ⟨layout, layoutBound⟩ := ResolvedMetadataStorage.complete graph b target reference
  obtain ⟨front, frontBound⟩ := ResolvedFrontStorage.complete width graph packet rows roots matched
    rootMatches b target reference rootSlot (entry + 13) sourceCount
  obtain ⟨solved, queryBound⟩ := QuietQueryStorage.complete width cursor data.protectedEnd
    (n + graph.nodeCount) data.scratchEnd data.references
  obtain ⟨restored, returnBound⟩ := PacketTransferStorage.returning width (cursor + query.1.length)
    data.protectedEnd sourceCount found rejected
  have rowsBound := ResolvedResident.rows_bound graph ∅ b target reference
  have length : (ResolvedCallbackConstruction.build width graph packet rows roots b target
      reference rootSlot entry sourceCount found rejected).1.length ≤
      1200 * (graph.countedSize + 1) := by
    rw [ResolvedCallbackConstruction.image width graph packet rows roots matched b target reference]
    exact ResolvedSourceCallback.code_length_bound graph packet rows roots b target reference
      sourceBound
  have referencesBound : data.references.length + data.references.flatten.length ≤
      11 * (graph.countedSize + 1) := by
    dsimp only [data, metadata]
    rw [ResolvedNativeLayoutConstruction.references_value]
    simpa only [ResolvedResident.refs_length, ResolvedResident.refs_literals] using rowsBound
  refine ⟨⟨layout, front, solved, restored, PacketTransferStorage.fixed width⟩, ?_⟩
  change _ + _ + _ + _ + 256 * (_ + 1) + 100000 ≤ _
  dsimp only [data, cursor, query] at *
  omega

structure Native (parameters : Parameters) (width entry next : Nat)
    (reference : Fin parameters.decoder.nodeCount) where
  layout : ResolvedMetadataStorage.Certificate parameters.decoder parameters.buses
    parameters.bridge.target reference
  query : NativeQueryStorage.Certificate parameters width entry
    (metadata parameters.decoder parameters.buses parameters.bridge.target reference).protectedEnd
    (parameters.channels + parameters.decoder.nodeCount)
    (metadata parameters.decoder parameters.buses parameters.bridge.target reference).scratchEnd
    (metadata parameters.decoder parameters.buses parameters.bridge.target reference).nativeEnd
    (metadata parameters.decoder parameters.buses parameters.bridge.target reference).references

def nativeBuffers (parameters : Parameters) (width entry next : Nat)
    (reference : Fin parameters.decoder.nodeCount)
    (certificate : Native parameters width entry next reference) :=
  let data := metadata parameters.decoder parameters.buses parameters.bridge.target reference
  ResolvedMetadataStorage.buffers parameters.decoder parameters.buses parameters.bridge.target
    reference certificate.layout +
  NativeQueryStorage.buffers parameters width entry data.protectedEnd
    (parameters.channels + parameters.decoder.nodeCount) data.scratchEnd data.nativeEnd next
    data.references certificate.query +
  256 * ((ResolvedNativeQueryConstruction.build parameters width entry next reference).1.length + 1)

theorem native (parameters : Parameters) (width entry next : Nat)
    (reference : Fin parameters.decoder.nodeCount) :
    ∃ certificate : Native parameters width entry next reference,
      nativeBuffers parameters width entry next reference certificate ≤
        2000000000 * (parameters.decoder.countedSize + 1) +
        200000000 * ((selectedSize parameters).total + 1) := by
  let data := metadata parameters.decoder parameters.buses parameters.bridge.target reference
  obtain ⟨layout, layoutBound⟩ := ResolvedMetadataStorage.complete parameters.decoder
      parameters.buses
    parameters.bridge.target reference
  obtain ⟨query, queryBound⟩ := NativeQueryStorage.complete parameters width entry data.protectedEnd
    (parameters.channels + parameters.decoder.nodeCount) data.scratchEnd data.nativeEnd next
    data.references
  have rowsBound := ResolvedResident.rows_bound parameters.decoder ∅ parameters.buses
    parameters.bridge.target reference
  have length : (ResolvedNativeQueryConstruction.build parameters width entry next
      reference).1.length ≤
      1000 * (parameters.decoder.countedSize + 1) + 34 * (selectedSize parameters).total := by
    rw [ResolvedNativeQueryConstruction.image]
    have bound := ResolvedNativeResident.code_bound (width := width) (entry := entry)
      (keep := data.protectedEnd) (next := next) parameters parameters.decoder parameters.buses
      parameters.bridge.target reference
    dsimp only [data, metadata] at bound
    omega
  have referencesBound : data.references.length + data.references.flatten.length ≤
      11 * (parameters.decoder.countedSize + 1) := by
    dsimp only [data, metadata]
    rw [ResolvedNativeLayoutConstruction.references_value]
    simpa only [ResolvedResident.refs_length, ResolvedResident.refs_literals] using rowsBound
  refine ⟨⟨layout, query⟩, ?_⟩
  change _ + _ + 256 * (_ + 1) ≤ _
  dsimp only [data] at *
  omega

end Controller.Cost.ResolvedQueryStorage
