module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ForestSourceStorage
public import Controller.Cost.ForestSourcePreparationStorage
public import Controller.Cost.UniformSourceStorage
public import Controller.Cost.ForestPreparedPositiveStorage
public import Controller.Cost.ForestNegativeStorage
public import Controller.Cost.ForestQueryPacketStorage

@[expose] public section


/-! Storage composition for the source-only forest compiler in the source/list
and first-order word-construction models. Original source and scalar inputs
are read-only. The envelope conservatively retains the stage buffers together;
generic weight encoding and arithmetic storage remain separate. -/
namespace Controller.Cost.ForestCompilerStorage

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestRootProjection
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestCursorAllRoots
open Controller.Cost.ForestCursorDescriptors

variable {n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

def cache (rows : List Row) := ForestCompilerOffsets.run rows ForestCompilerOffsets.initial

def prior (width channels : Nat) (rows : List Row) (roots : List Nat) :=
  ForestSourceImage.prelude width channels rows roots (cache rows)

def computed (graph : DAG n) (rows : List Row) (weights : Channel n → W) (b : Nat) (target : Channel n) :=
  (runAll (source n rows) weights b target (healthyRootIds graph target false)).2

def positive (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (weights : Channel n → W) (b : Nat) (target : Channel n) :=
  ForestPreparedPositive.form (prior width n rows roots) rows.length (cache rows).children (cache rows).guards
    (healthyRootIds graph target false).length (computed graph rows weights b target)

def allocated (graph : DAG n) (rows : List Row) (target : Channel n) :=
  5 + 6 * rows.length + (cache rows).children + (cache rows).guards + (healthyRootIds graph target false).length

def healthyInitial (width : Nat) (rows : List Row) (roots : List Nat) (target : Channel n) : Controller.Cost.State width 4 :=
  (ForestCounter.counterState (#[] : Array (Word width)) 0 (word width 0) (word width 0) (word width 0)).frame
    ((inputPacket n 0 rows roots).map (word width) ++
      List.ofFn (fun i => boolWord width (assignmentOfSet {target} i)) ++ []) []

/-- The negative-loop witness refers to the actual checked-root and packet
producers. Its word count includes final instruction materialization. -/
def NegativeEvidence (prior : Program width 8) (allocated : Nat) (graph : DAG n)
    (rows : List Row) (roots : List Nat) (b : Nat) (target : Channel n) (words : Nat) : Prop :=
  let start := ForestPreparedNegative.front prior allocated
  let packets := (ForestQueryPackets.queries (source n rows) (cache rows) graph.roots b target).1
  let protectedEnd := 6 + 6 * graph.nodeCount + (cache rows).children + (cache rows).guards + roots.length + 2 * (n + graph.nodeCount)
  let initial := ForestStreamingConstruction.initial (n + graph.nodeCount) width start.size
  let final := ForestStreamingConstruction.run protectedEnd n initial packets
  ∃ peak, ForestStreamingStorage.Trace protectedEnd n initial packets final peak ∧
    ForestPreparedNegative.form prior graph.nodeCount allocated (source n rows) (cache rows) roots b target =
      ForestStreamingConstruction.compile protectedEnd n initial packets start ∧
    words = peak + 32 * ForestStreamingConstruction.buffered final + 2 * final.blocks.length + 8 * start.size + 50000

omit [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W] in
private theorem negative_evidence (prior : Program width 8) (allocated : Nat) (graph : DAG n)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots)
    (forest : graph.FormulaForest) (b : Nat) (target : Channel n) :
    ∃ words, NegativeEvidence prior allocated graph rows roots b target words ∧
      words ≤ 10000000 * (graph.countedSize + 1) + 8 * prior.size := by
  obtain ⟨peak, trace, image, bound⟩ := ForestNegativeStorage.construction prior allocated graph rows roots matched rootMatches forest b target
  exact ⟨_, ⟨peak, trace, image, rfl⟩, bound⟩

/-- A certificate ties each retained construction stage to the original source
and to the computed selector state. Healthy families are specifications of
executed classification, not constructor inputs. -/
structure Certificate (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (weights : Channel n → W) (b : Nat) (target : Channel n) where
  sourcePeak : Nat
  cachePeak : Nat
  interpreter : UniformSourceStorage.Certificate width n rows.length (rowChildren rows).length (rowGuards rows).length roots.length
  classificationFinal : Controller.Cost.State width 4
  classificationTicks : Nat
  classificationPeak : Nat
  selectorTicks : Nat
  selectorPeak : Nat
  positivePeak : Nat
  negativeWords : Nat
  sourceTrace : ForestSourcePreparationStorage.ItemsTrace n 0 rows sourcePeak
  sourceArray : CompilerArrayTrace.Trace (ForestSourceConstruction.items n 0 rows).1 #[] (source n rows) rows.length
  cacheTrace : ForestSourcePreparationStorage.CacheTrace rows ForestCompilerOffsets.initial (cache rows) cachePeak
  classification : Execution (ForestRootClassification.program width n rows.length (rowChildren rows).length
    (rowGuards rows).length roots.length) (healthyInitial width rows roots target)
    classificationFinal classificationTicks classificationPeak
  selector : ForestSelectionMachine.SpaceTrace (source n rows) weights (ForestSelectionMachine.totalWeight weights) b target
    (ForestSelectionMachine.initial (healthyRootIds graph target false))
    ⟨computed graph rows weights b target, []⟩ selectorTicks selectorPeak
  positiveTrace : ForestPreparedPositiveStorage.Trace (prior width n rows roots) rows.length (cache rows).children (cache rows).guards
    (healthyRootIds graph target false).length (computed graph rows weights b target) positivePeak
  negativeTrace : NegativeEvidence (positive width graph rows roots weights b target) (allocated graph rows target)
    (healthyGraph graph target true) rows (healthyRootIds graph target true) b target negativeWords
  dataFlow : ForestSourceDriver.prepare width rows roots weights b target =
    ⟨source n rows, cache rows, healthyRootIds graph target false, healthyRootIds graph target true,
      ⟨computed graph rows weights b target, []⟩⟩
  assembled : ForestSourceImage.build width rows roots weights b target =
    ForestPreparedNegative.form (positive width graph rows roots weights b target) graph.nodeCount (allocated graph rows target)
      (source n rows) (cache rows) (healthyRootIds graph target true) b target

/-- Input/serialization/partition records, source-array materialization and
all retained stage buffers. Query-record allocation is counted before the
negative loop, so original source rows are not treated as free generated data. -/
def words (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat) (weights : Channel n → W)
    (b : Nat) (target : Channel n) (certificate : Certificate width graph rows roots weights b target) : Nat :=
  certificate.sourcePeak + certificate.cachePeak +
    UniformSourceStorage.buffers width n rows.length (rowChildren rows).length (rowGuards rows).length roots.length certificate.interpreter +
    certificate.classificationPeak + certificate.selectorPeak + certificate.positivePeak + certificate.negativeWords +
    ForestQueryPacketStorage.allocated (source n rows) (cache rows) (healthyGraph graph target true).roots b target +
    512 * (graph.countedSize + 1) + 8 * rows.length +
    programWords (ForestSourceImage.build width rows roots weights b target)

/-- Full retained-stage composition, including actual instruction backing and
source query records, is linear in the original counted forest. This concerns
the stated construction models; it is not a claim about Lean/C allocation. -/
theorem construction (graph : DAG n) (forest : graph.FormulaForest) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (weights : Channel n → W) (b : Nat) (target : Channel n)
    (width : Nat) (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (countFits : (buildRoots (healthyGraph graph target false)).count < 2 ^ width)
    (positionFits : ∀ record ∈ (buildRoots (healthyGraph graph target false)).entries, record.position < 2 ^ width) :
    ∃ certificate : Certificate width graph rows roots weights b target,
      words width graph rows roots weights b target certificate ≤ 20000000 * (graph.countedSize + 1) := by
  let pg := healthyGraph graph target false
  let ng := healthyGraph graph target true
  have pRows : RowsMatch pg rows := Forest.rootFamily_rows graph _ rows matched
  have pRoots : RootsMatch pg (healthyRootIds graph target false) := Forest.rootFamily_rootIds graph _
  have nRows : RowsMatch ng rows := Forest.rootFamily_rows graph _ rows matched
  have nRoots : RootsMatch ng (healthyRootIds graph target true) := Forest.rootFamily_rootIds graph _
  have pForest : pg.FormulaForest := Forest.rootFamily_forest graph forest _ (Forest.healthyPositions_nodup graph target false)
  have nForest : ng.FormulaForest := Forest.rootFamily_forest graph forest _ (Forest.healthyPositions_nodup graph target true)
  obtain ⟨sourcePeak, sourceTrace, sourceBound⟩ := ForestSourcePreparationStorage.items_space n 0 rows
  have array := (ForestSourceConstruction.source_preparation n rows).2.1
  obtain ⟨cachePeak, cacheTrace, cacheBound⟩ := ForestSourcePreparationStorage.cache_space rows ForestCompilerOffsets.initial
  obtain ⟨interpreter, interpreterBound⟩ := UniformSourceStorage.construction width n rows.length (rowChildren rows).length
    (rowGuards rows).length roots.length
  obtain ⟨classificationFinal, classificationTicks, classificationPeak, classification, classTime, classBound,
      classStack, classOutput, classHalted⟩ := ForestRootClassification.execution graph rows roots matched heads rootMatches
    (assignmentOfSet {target}) width capacity [] [] (word width 0) (word width 0) (word width 0)
  obtain ⟨selectorTicks, selectorPeak, selector, selectorTime, selectorBound⟩ := ForestSelectionMachine.linear_resources
    pg pForest rows (healthyRootIds graph target false) pRows pRoots weights b target
  obtain ⟨positivePeak, positiveTrace, positiveBound⟩ := ForestPreparedPositiveStorage.construction (prior width n rows roots)
    rows.length (cache rows).children (cache rows).guards (healthyRootIds graph target false).length (computed graph rows weights b target)
  obtain ⟨negativeWords, negativeTrace, negativeBound⟩ := negative_evidence (positive width graph rows roots weights b target)
    (allocated graph rows target) ng rows (healthyRootIds graph target true) nRows nRoots nForest b target
  have dataFlow := ForestSourceImage.prepared_image graph forest rows roots matched heads rootMatches weights b target width capacity
  have assembled : ForestSourceImage.build width rows roots weights b target =
      ForestPreparedNegative.form (positive width graph rows roots weights b target) graph.nodeCount (allocated graph rows target)
        (source n rows) (cache rows) (healthyRootIds graph target true) b target := by
    rw [ForestSourceImage.build, dataFlow]
    dsimp only [ForestSourceImage.assemble]
    change ForestPreparedNegative.form (positive width graph rows roots weights b target) rows.length (allocated graph rows target)
      (source n rows) (cache rows) (healthyRootIds graph target true) b target = _
    exact congrArg (fun nodes => ForestPreparedNegative.form (positive width graph rows roots weights b target) nodes
      (allocated graph rows target) (source n rows) (cache rows) (healthyRootIds graph target true) b target) matched.length_eq
  let certificate : Certificate width graph rows roots weights b target :=
    ⟨sourcePeak, cachePeak, interpreter, classificationFinal, classificationTicks, classificationPeak,
      selectorTicks, selectorPeak, positivePeak, negativeWords, sourceTrace, array, cacheTrace, classification,
      selector, positiveTrace, negativeTrace, dataFlow, assembled⟩
  refine ⟨certificate, ?_⟩
  have referenceBound := ForestQueryPacketStorage.bound width ng rows (healthyRootIds graph target true) nRows nRoots nForest b target
  have programBound := ForestSourceStorage.program_bound graph forest rows roots matched heads rootMatches weights b target width capacity countFits positionFits
  have pSize : pg.countedSize ≤ graph.countedSize := Forest.healthyFamily_countedSize_le graph target false
  have nSize : ng.countedSize ≤ graph.countedSize := Forest.healthyFamily_countedSize_le graph target true
  have incidence := matched_incidence_lengths graph rows matched
  have descriptors := actual_descriptor_count_bound pg pForest
  have entryCount : (computed graph rows weights b target).descriptors.entries.length = (buildRoots pg).count := by
    rw [computed, runAll_descriptors pg rows _ pRows pRoots weights b target]
    exact (buildRoots_valid pg).count
  rw [entryCount] at positiveBound
  have offsets := ForestCompilerOffsets.run_totals rows ForestCompilerOffsets.initial
  have childCount : (cache rows).children = (rowChildren rows).length := by
    simpa only [cache, ForestCompilerOffsets.initial, Nat.zero_add] using offsets.1
  have guardCount : (cache rows).guards = (rowGuards rows).length := by
    simpa only [cache, ForestCompilerOffsets.initial, Nat.zero_add] using offsets.2.1
  have priorSize : (prior width n rows roots).size = 304 + 2 * n := by
    dsimp only [prior, cache]
    rw [ForestSourceImage.prelude_image width graph rows roots (assignmentOfSet {target}), packetPrelude_size, classificationPrior_size]
    omega
  have positiveImage : positive width graph rows roots weights b target =
      mixedPositiveProgram (prior width n rows roots) pg rows (healthyRootIds graph target false) weights b target countFits positionFits := by
    dsimp only [positive]
    rw [childCount, guardCount]
    exact ForestPreparedPositive.form_image _ pg rows _ pRows pRoots weights b target countFits positionFits
  have positiveSize := mixed_positive_size_bound (prior width n rows roots) pg rows _ pRows pRoots weights b target countFits positionFits
  rw [← positiveImage] at positiveSize
  have pCounts := Forest.rootFamily_incidence_counts graph (Forest.healthyPositions graph target false)
  have pRootBound := Forest.healthyPositions_length_le graph target false
  change pg.nodeCount = _ ∧ pg.childIncidences = _ ∧ pg.guardIncidences = _ ∧ pg.roots.length = _ at pCounts
  unfold ForestSelectionMachine.fuelBound at selectorBound
  rw [pCounts.2.1, pCounts.2.2.1, pCounts.2.2.2] at descriptors selectorBound
  rw [matched.length_eq, incidence.1, incidence.2] at sourceBound
  simp only [ForestSourcePreparationStorage.cacheWords, ForestCompilerOffsets.initial, Array.size_empty] at cacheBound
  simp only [List.length_nil, Nat.add_zero] at classBound
  rw [priorSize] at positiveBound positiveSize
  have size := graph.countedSize_eq
  have rowCount : rows.length = graph.nodeCount := matched.length_eq
  have sourceLarge : sourcePeak ≤ 128 * (graph.countedSize + 1) := by omega
  have cacheLarge : cachePeak ≤ 64 * (graph.countedSize + 1) := by omega
  have selectorLarge : selectorPeak ≤ 500 * (graph.countedSize + 1) := by omega
  have positiveLarge : positivePeak ≤ 120000 * (graph.countedSize + 1) := by omega
  have negativeLarge : negativeWords ≤ 11000000 * (graph.countedSize + 1) := by omega
  have referenceLarge : ForestQueryPacketStorage.allocated (source n rows) (cache rows)
      (healthyGraph graph target true).roots b target ≤ 5000 * (graph.countedSize + 1) := by
    exact referenceBound.trans (by omega)
  dsimp only [words, certificate]
  omega

end Controller.Cost.ForestCompilerStorage
