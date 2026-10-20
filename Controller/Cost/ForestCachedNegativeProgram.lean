module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ForestCompilerQueries
public import Controller.Cost.ForestZeroSourcePlan

@[expose] public section


/-! Native negative-query code generated from cached source metadata. The
constructor uses local counts and coverage from the epoch dictionary. It does
not materialize a hypothetical solver heap or rebuild a dense empty dictionary
for each query. The image agrees with the original resident kernels. -/
namespace Controller.Cost.ForestCachedNegativeProgram

open Controller Controller.CNF Controller.Cost
open Controller.Cost.GateProgram Controller.Cost.ForestZeroCompile
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroAdmissibleCaller Controller.Cost.ForestZeroResident
open Controller.Cost.ForestCompilerQueries

variable {ambient : Nat}

private def widen (code : GateProgram.Code width) : Program width 8 :=
  (code.map RegisterWiden.widenInstruction).toArray

def heapEnd (protectedEnd channels : Nat) (references : List (List (Reference ambient)))
    (summary : Summary ambient) : Nat :=
  protectedEnd + 5 + 2 * (references.length + 1) + 2 * references.flatten.length +
    (if summary.coverage.reason = .covered then 2 * channels else 0)

def chunks (width protectedEnd channels sourceEntry nextEntry : Nat)
    (references : List (List (Reference ambient))) (summary : Summary ambient) : List (Program width 8) :=
  let p := placement width protectedEnd sourceEntry nextEntry references
  let count := summary.coordinates.size
  let base := heapEnd protectedEnd channels references summary
  let recordStart := base + 5 * count + 4
  [reuseEntryCode width,
   widen (keepCode width),
   #[.constant 0 (word width (protectedEnd + 5 + 2 * (references.length + 1)))],
   widen (constructorCode width p.constructor protectedEnd protectedEnd (protectedEnd + 4) p.query references),
   scratchCountCode width,
   Controller.Horn.TrackedAllocate.code width (p.query + 11),
   scratchHeaderCode width,
   scratchEndpointCode,
   saveProjectionCode,
   Controller.Horn.NormalizeCNF.code width (p.query + 42) count base
     protectedEnd (protectedEnd + 1) (protectedEnd + 2) (protectedEnd + 3) (protectedEnd + 4),
   ForestZeroHeaderBridge.saveCode width protectedEnd,
   Controller.Horn.IndexScan.code (n := count) width base recordStart (p.query + 210),
   ForestZeroHeaderBridge.restoreCode width,
   ForestZeroReclaim.captureCode width,
   ForestZeroSeedSetup.code (n := count) width base protectedEnd recordStart p.scan,
   Controller.Horn.WorklistSeed.code (n := count) width base p.scan p.seedDone p.conflict,
   Controller.Horn.WorklistAccept.headSetupCode (n := count) width base p.fetch,
   Controller.Horn.WorklistFIFO.fetchCode (n := count) width base p.fetch p.success p.bucket,
   Controller.Horn.WorklistFIFO.advanceCode (n := count) width base p.fetch,
   Controller.Horn.WorklistBucketLoop.code width p.bucket p.advance p.ready,
   Controller.Horn.WorklistBucketReady.code (n := count) width base p.ready p.advance p.conflict p.bucket,
   ForestZeroAnswer.savedCode width 1 p.projection,
   ForestZeroAnswer.savedCode width 0 p.cleanup,
   projectionConstantsCode width,
   channelPrepareCode width,
   ForestZeroChannelEmit.code width (p.projection + 21) p.cleanup,
   ForestZeroReclaim.setupCode width,
   ForestZeroReclaim.code width (p.cleanup + 3) p.returned,
   widen ((resetPrepareCode width).toList),
   widen (ForestZeroReset.code width (p.returned + 15)),
   #[.pop 4],
   ForestZeroRootLoop.dispatchCode width nextEntry]

def instructions (width protectedEnd channels sourceEntry nextEntry : Nat)
    (references : List (List (Reference ambient))) (summary : Summary ambient) : List (Instruction width 8) :=
  (chunks width protectedEnd channels sourceEntry nextEntry references summary).flatMap Array.toList

set_option maxHeartbeats 1200000 in
/-- Equality of the complete generated image, including all absolute branches
and physical backend header addresses; no execution premise is used. -/
theorem chunks_eq (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient)
    (sourceEntry nextEntry : Nat) :
    chunks width heap.size channels sourceEntry nextEntry references
      (referenceSummary channels (ForestZeroAssembly.originalRows (reservedReferences references))) =
      ForestZeroResident.chunks heap layout references channels within sourceEntry nextEntry := by
  have base := constructorHeap_size heap layout (empty ambient) references channels
  unfold chunks ForestZeroResident.chunks
  dsimp only [referenceSummary, heapEnd, constructorDictionary, constructorFormulaBackend, backendLayout]
  rw [base]

/-- One query uses the shared arrays and the resulting cached counts directly.
The dense projection used by the proof does not occur in this definition. -/
def query (width protectedEnd channels sourceEntry nextEntry : Nat)
    (state : ForestCompilerDictionary.State ambient) (references : List (List (Reference ambient))) :
    ForestCompilerDictionary.State ambient × List (Instruction width 8) × Nat :=
  let compiled := ForestCompilerQueries.query channels state
    (ForestZeroAssembly.originalRows (reservedReferences references))
  (compiled.1, instructions width protectedEnd channels sourceEntry nextEntry references compiled.2.1,
    compiled.2.2)

theorem query_eq (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient)
    (sourceEntry nextEntry : Nat) (state : ForestCompilerDictionary.State ambient)
    (valid : ForestCompilerDictionary.Valid state) :
    (query width heap.size channels sourceEntry nextEntry state references).2.1 =
      ForestZeroResident.instructions heap layout references channels within sourceEntry nextEntry ∧
      ForestCompilerDictionary.Valid (query width heap.size channels sourceEntry nextEntry state references).1 := by
  have same := ForestCompilerQueries.query_project channels state valid
    (ForestZeroAssembly.originalRows (reservedReferences references))
  have summary : (ForestCompilerQueries.query channels state
      (ForestZeroAssembly.originalRows (reservedReferences references))).2.1 =
      referenceSummary channels (ForestZeroAssembly.originalRows (reservedReferences references)) := by
    cases fields : (ForestCompilerQueries.query channels state
      (ForestZeroAssembly.originalRows (reservedReferences references))).2.1 with
    | mk coordinates rows coverage =>
        simp only [fields] at same
        simp only [referenceSummary, Summary.mk.injEq]
        exact ⟨same.1, same.2.1, same.2.2⟩
  constructor
  · unfold query instructions
    dsimp only
    rw [summary, chunks_eq heap layout references channels within sourceEntry nextEntry]
    rfl
  · exact ForestCompilerQueries.query_valid channels state valid _

/-- The constructor retains one dictionary across all declared occurrences.
The provisional image fixes the next absolute entry; relocation changes only
jump operands. Its traversal cost is charged separately from metadata work. -/
def resident (width protectedEnd channels : Nat) (state : ForestCompilerDictionary.State ambient) :
    Nat → List (List (List (Reference ambient))) →
      ForestCompilerDictionary.State ambient × List (Instruction width 8) × Nat
  | _, [] => (state, (ForestZeroRootLoop.exhaustedCode width).toList, 0)
  | entry, references :: rest =>
      let compiled := ForestCompilerQueries.query channels state
        (ForestZeroAssembly.originalRows (reservedReferences references))
      let provisional := instructions width protectedEnd channels entry 0 references compiled.2.1
      let next := entry + provisional.length
      let current := instructions width protectedEnd channels entry next references compiled.2.1
      let tail := resident width protectedEnd channels compiled.1 next rest
      (tail.1, current ++ tail.2.1, compiled.2.2 + tail.2.2 + 1)

set_option maxHeartbeats 1200000 in
theorem resident_eq (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (channels : Nat) (within : channels ≤ ambient) (state : ForestCompilerDictionary.State ambient)
    (valid : ForestCompilerDictionary.Valid state) (entry : Nat)
    (packets : List (List (List (Reference ambient)))) :
    (resident width heap.size channels state entry packets).2.1 =
      ForestZeroSourcePlan.residentInstructions heap layout channels within entry packets ∧
      ForestCompilerDictionary.Valid (resident width heap.size channels state entry packets).1 := by
  induction packets generalizing entry state with
  | nil => exact ⟨rfl, valid⟩
  | cons references rest ih =>
      have first := (query_eq heap layout references channels within entry 0 state valid).1
      have stateValid := ForestCompilerQueries.query_valid channels state valid
        (ForestZeroAssembly.originalRows (reservedReferences references))
      let compiled := ForestCompilerQueries.query channels state
        (ForestZeroAssembly.originalRows (reservedReferences references))
      let next := entry + (instructions width heap.size channels entry 0 references compiled.2.1).length
      have tail := ih compiled.1 stateValid next
      have shifted := (query_eq heap layout references channels within entry next state valid).1
      change instructions width heap.size channels entry 0 references compiled.2.1 = _ at first
      change instructions width heap.size channels entry next references compiled.2.1 = _ at shifted
      constructor
      · simp only [resident, ForestZeroSourcePlan.residentInstructions]
        change instructions width heap.size channels entry next references compiled.2.1 ++
          (resident width heap.size channels compiled.1 next rest).2.1 = _
        rw [shifted, tail.1]
        dsimp only [next]
        rw [first]
      · exact tail.2

theorem resident_metadata_work (width protectedEnd channels : Nat)
    (state : ForestCompilerDictionary.State ambient) (entry : Nat)
    (packets : List (List (List (Reference ambient)))) :
    (resident width protectedEnd channels state entry packets).2.2 ≤
      14 * packets.flatten.flatten.length + packets.flatten.length + 18 * packets.length := by
  induction packets generalizing state entry with
  | nil => simp [resident]
  | cons references rest ih =>
      let compiled := ForestCompilerQueries.query channels state
        (ForestZeroAssembly.originalRows (reservedReferences references))
      let next := entry + (instructions width protectedEnd channels entry 0 references compiled.2.1).length
      have one := ForestCompilerQueries.query_work channels state
        (ForestZeroAssembly.originalRows (reservedReferences references))
      have tail := ih compiled.1 next
      have rows : (ForestZeroAssembly.originalRows (reservedReferences references)).length = references.length + 1 := by
        simp [ForestZeroAssembly.originalRows, reservedReferences]
      have literals : (ForestZeroAssembly.originalRows (reservedReferences references)).flatten.length =
          references.flatten.length := by
        simp [List.length_flatten, ForestZeroAssembly.originalRows, reservedReferences,
          List.map_map, Function.comp_def]
      rw [rows, literals] at one
      simp only [resident, List.flatten_cons, List.flatten_append, List.length_append, List.length_cons]
      change compiled.2.2 + (resident width protectedEnd channels compiled.1 next rest).2.2 + 1 ≤ _
      change compiled.2.2 ≤ _ at one
      omega

/-- The entire image is written into the supplied prefix in one final pass. -/
def compile (width protectedEnd channels : Nat) (prior : Program width 8)
    (packets : List (List (List (Reference ambient)))) : Program width 8 :=
  (resident width protectedEnd channels (ForestCompilerDictionary.initial ambient) prior.size packets).2.1.toArrayAux prior

theorem compile_eq (heap : Array (Word width)) (layout : Layout ambient heap.size)
    (channels : Nat) (within : channels ≤ ambient) (prior : Program width 8)
    (packets : List (List (List (Reference ambient)))) :
    compile width heap.size channels prior packets =
      ForestZeroSourcePlan.residentProgram prior heap layout channels within packets := by
  unfold compile
  rw [(resident_eq heap layout channels within _ ForestCompilerDictionary.initial_valid prior.size packets).1]
  unfold ForestZeroSourcePlan.residentProgram ForestZeroResident.materialize
  rfl

end Controller.Cost.ForestCachedNegativeProgram
