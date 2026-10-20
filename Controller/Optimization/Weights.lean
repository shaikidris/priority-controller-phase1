module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Physical.DetectCorrect
public import Controller.Decoder.ZeroSystem
public import Controller.Decoder.ForestGeneric
public import Controller.Cost.ForestWeightedIndexed
public import Controller.Cost.ForestWeightedOptimal

@[expose] public section

/-!
# Nonnegative-weight witnesses: the polynomial directions

For one guarded output and nonnegative channel weights in an ordered group:

* a healthy-zero output has a minimum-weight detecting set among the small
  one-head candidates;
* a healthy-one output has a maximum-weight detecting set, the greatest
  eligible zero;
* on a formula forest, a returned indexed-traversal candidate bounds the
  weight of every admissible true set, with linear operation counts.

Weights may be zero. Nothing is claimed for negative weights. Arithmetic is
counted in operations; the bit cost of weights is a separate contract.
-/

namespace Controller.Optimization.Weights
open Controller Controller.Decoder Controller.Decoder.DAG

variable {n : ℕ} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- One-head shrinking: every admissible true set contains an admissible true
small candidate of no greater weight. -/
theorem healthyZero_shrink (graph : DAG n) (guarded : graph.Guarded)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount)
    (K : Finset (Channel n)) (eligible : Admissible b target K)
    (value : graph.eval (assignmentOfSet K) root = true) :
    ∃ head ∈ K, trueCandidate b target head ⊆ K ∧
      graph.eval (assignmentOfSet (trueCandidate b target head)) root = true ∧
      GenericWeight.total weights (trueCandidate b target head) ≤ GenericWeight.total weights K := by
  obtain ⟨head, blocked, path, headTrue, avoids⟩ :=
    graph.exists_livePath_of_eval_true guarded K root value
  have feasible : pathFeasible b target head blocked := by
    refine ⟨?_, ?_⟩
    · intro forbidden
      exact Finset.disjoint_left.mp avoids forbidden headTrue
    · intro one forbidden
      exact Finset.disjoint_left.mp avoids forbidden (eligible.2 one)
  have inside := trueCandidate_subset eligible headTrue
  exact ⟨head, headTrue, inside, path.smallSet_true b target feasible,
    GenericWeight.mono weights nonnegative _ _ inside⟩

/-- Minimum-weight detection for a healthy-zero output is attained by one of
the at most `n` small candidates. -/
theorem healthyZero_minimum (graph : DAG n) (guarded : graph.Guarded)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount)
    (healthy : graph.eval (assignmentOfSet {target}) root = false)
    (detectable : ∃ K, Admissible b target K ∧
      graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root) :
    ∃ head, Admissible b target (trueCandidate b target head) ∧
      graph.eval (assignmentOfSet (trueCandidate b target head)) root ≠
        graph.eval (assignmentOfSet {target}) root ∧
      ∀ K, Admissible b target K →
        graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root →
        GenericWeight.total weights (trueCandidate b target head) ≤ GenericWeight.total weights K := by
  have trueOf : ∀ K, graph.eval (assignmentOfSet K) root ≠
      graph.eval (assignmentOfSet {target}) root → graph.eval (assignmentOfSet K) root = true := by
    intro K differs
    cases actual : graph.eval (assignmentOfSet K) root <;> simp_all
  let good : Finset (Channel n) := Finset.univ.filter fun head =>
    graph.eval (assignmentOfSet (trueCandidate b target head)) root = true
  have nonempty : good.Nonempty := by
    obtain ⟨K, eligible, differs⟩ := detectable
    obtain ⟨head, _, _, value, _⟩ := healthyZero_shrink graph guarded weights nonnegative b target
      root K eligible (trueOf K differs)
    exact ⟨head, by simp [good, value]⟩
  obtain ⟨best, member, least⟩ := Finset.exists_min_image good
    (fun head => GenericWeight.total weights (trueCandidate b target head)) nonempty
  have bestTrue : graph.eval (assignmentOfSet (trueCandidate b target best)) root = true := by
    simpa [good] using member
  refine ⟨best, trueCandidate_admissible b target best, by rw [bestTrue, healthy]; decide, ?_⟩
  intro K eligible differs
  obtain ⟨head, _, _, value, bound⟩ := healthyZero_shrink graph guarded weights nonnegative b target
    root K eligible (trueOf K differs)
  exact (least head (by simp [good, value])).trans bound

/-- Maximum-weight detection for a healthy-one output is attained by the
greatest eligible zero, which contains every other eligible zero. -/
theorem healthyOne_maximum (graph : DAG n) (guarded : graph.Guarded)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount)
    (healthy : graph.eval (assignmentOfSet {target}) root = true)
    (detectable : ∃ K, Admissible b target K ∧
      graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root) :
    ∃ greatest, Admissible b target greatest ∧
      graph.eval (assignmentOfSet greatest) root ≠ graph.eval (assignmentOfSet {target}) root ∧
      ∀ K, Admissible b target K →
        graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root →
        K ⊆ greatest ∧ GenericWeight.total weights K ≤ GenericWeight.total weights greatest := by
  have zeroOf : ∀ K, graph.eval (assignmentOfSet K) root ≠
      graph.eval (assignmentOfSet {target}) root → graph.eval (assignmentOfSet K) root = false := by
    intro K differs
    cases actual : graph.eval (assignmentOfSet K) root <;> simp_all
  have fixed : ∀ K : Finset (Channel n), ExtendsFixed ∅ ∅ K := by
    intro K
    simp [ExtendsFixed]
  obtain ⟨K, eligible, differs⟩ := detectable
  obtain ⟨greatest, ⟨admissible, _, zero⟩, contains⟩ :=
    graph.exists_greatest_zero guarded b target root ∅ ∅ ⟨K, eligible, fixed K, zeroOf K differs⟩
  refine ⟨greatest, admissible, by rw [zero, healthy]; decide, ?_⟩
  intro other otherEligible otherDiffers
  have inside := contains other otherEligible (fixed other) (zeroOf other otherDiffers)
  exact ⟨inside, GenericWeight.mono weights nonnegative _ _ inside⟩

open Controller.Cost Controller.Cost.ForestIndexedOperands in
/-- Formula forests: the costed indexed traversal's selected score bounds the
weight of every admissible true set at every output, and the run uses linearly
many indexed and arithmetic operations. The weight function is the one supplied;
the statement assumes a returned candidate and does not prove score attainment. -/
theorem forest_maximum_weight (graph : DAG n) (guarded : graph.Guarded)
    (forest : graph.FormulaForest) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootsMatch : RootsMatch graph roots)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : ℕ) (target : Channel n) (candidate : ForestWeightedTagged.Candidate W)
    (selected : (ForestWeightedIndexed.view
      (ForestWeightedIndexed.runAll (ForestWeightedIndexed.source n rows) weights b target roots).2).data.selected =
        some candidate) :
    (∀ (position : Fin graph.roots.length) (K : Finset (Channel n)), Admissible b target K →
      graph.eval (assignmentOfSet K) (graph.roots.get position) = true →
      GenericWeight.total weights K ≤ candidate.score) ∧
    (ForestWeightedIndexed.runAll (ForestWeightedIndexed.source n rows) weights b target roots).2.operations ≤
      4 * (graph.roots.length + graph.childIncidences) + 2 * graph.guardIncidences ∧
    (ForestWeightedIndexed.runAll (ForestWeightedIndexed.source n rows) weights b target roots).2.arithmetic ≤
      n + 8 * (graph.roots.length + graph.childIncidences) + 4 * graph.guardIncidences := by
  have projected := (ForestWeightedIndexed.runAll_projection graph rows roots matched rootsMatch
    weights b target).2
  have direct := (ForestWeightedDirect.runAll_projection graph weights b target).1
  rw [projected, direct] at selected
  exact ⟨fun position K eligible trueAt =>
      ForestWeightedOptimal.global_optimal_bound graph guarded weights nonnegative b target candidate
        selected position K eligible trueAt,
    ForestWeightedIndexed.runAll_operations_bound graph forest rows roots matched rootsMatch weights b target,
    ForestWeightedIndexed.runAll_arithmetic_bound graph rows roots matched rootsMatch forest weights b target⟩

end Controller.Optimization.Weights



namespace Controller.Optimization.Weights

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestWeightedTagged

variable {n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- The source-indexed algorithm either certifies absence of admissible true
sets or returns an attained maximum, with linear indexed and arithmetic counts.
There is no hypothesis that the algorithm has already returned a candidate. -/
theorem forest_attained_maximum (graph : DAG n) (forest : graph.FormulaForest)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (rootsMatch : RootsMatch graph roots) (weights : Channel n → W)
    (nonnegative : ∀ channel, 0 ≤ weights channel) (b : Nat) (target : Channel n) :
    let result := (ForestWeightedIndexed.runAll (ForestWeightedIndexed.source n rows)
      weights b target roots).2
    (result.selected = none ↔ ¬ ∃ position : Fin graph.roots.length, ∃ K : Finset (Channel n),
      Admissible b target K ∧ graph.eval (assignmentOfSet K) (graph.roots.get position) = true) ∧
    (∀ candidate, result.selected = some candidate →
      ∃ position : Fin graph.roots.length, candidate.root = position.val ∧
        ∃ K : Finset (Channel n), Admissible b target K ∧
          graph.eval (assignmentOfSet K) (graph.roots.get position) = true ∧
          candidate.score = GenericWeight.total weights K ∧
          ∀ other L, Admissible b target L →
            graph.eval (assignmentOfSet L) (graph.roots.get other) = true →
            GenericWeight.total weights L ≤ GenericWeight.total weights K) ∧
    result.operations ≤ 4 * (graph.roots.length + graph.childIncidences) + 2 * graph.guardIncidences ∧
    result.arithmetic ≤ n + 8 * (graph.roots.length + graph.childIncidences) + 4 * graph.guardIncidences := by
  intro result
  have indexed := congrArg (fun state : ForestWeightedDirect.State n W => state.data.selected)
    (ForestWeightedIndexed.runAll_projection graph rows roots matched rootsMatch weights b target).2
  have direct := congrArg TaggedState.selected
    (ForestWeightedDirect.runAll_projection graph weights b target).1
  have projected : result.selected = (ForestWeightedTagged.runGlobal graph weights b target).2.1.selected :=
    indexed.trans direct
  refine ⟨ForestWeightedIndexed.indexed_none_iff graph forest.1 rows roots matched rootsMatch
    weights nonnegative b target, ?_,
    ForestWeightedIndexed.runAll_operations_bound graph forest rows roots matched rootsMatch weights b target,
    ForestWeightedIndexed.runAll_arithmetic_bound graph rows roots matched rootsMatch forest weights b target⟩
  intro candidate selected
  have globalSelected := projected.symm.trans selected
  obtain ⟨position, rootEq, K, eligible, trueAt, score⟩ :=
    ForestWeightedOptimal.global_sound graph weights b target candidate globalSelected
  refine ⟨position, rootEq, K, eligible, trueAt, score, ?_⟩
  intro other L legal value
  rw [← score]
  exact ForestWeightedOptimal.global_optimal_bound graph forest.1 weights nonnegative b target
    candidate globalSelected other L legal value

/-- On healthy-zero forest observations, detectability forces the indexed
algorithm to return a candidate whose attained weight is a maximum among all
admissible detecting eligible sets. The set realizes a physical detecting test. -/
theorem forest_physical_maximum (graph : DAG n) (forest : graph.FormulaForest)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows)
    (rootsMatch : RootsMatch graph roots) (weights : Channel n → W)
    (nonnegative : ∀ channel, 0 ≤ weights channel) (b : Nat) (bridge : Physical.Bridge n)
    (positive : 0 < b)
    (healthy : ∀ position : Fin graph.roots.length,
      graph.eval (assignmentOfSet {bridge.target}) (graph.roots.get position) = false)
    (detectable : Physical.BridgeDetectable (b := b) bridge true graph.observations) :
    ∃ candidate K,
      (ForestWeightedIndexed.runAll (ForestWeightedIndexed.source n rows)
        weights b bridge.target roots).2.selected = some candidate ∧
      Admissible b bridge.target K ∧
      Physical.BridgeInputDetects bridge true graph.observations
        (Physical.realizeBridge bridge positive K) true ∧
      candidate.score = GenericWeight.total weights K ∧
      ∀ L, Admissible b bridge.target L →
        Physical.BridgeInputDetects bridge true graph.observations
          (Physical.realizeBridge bridge positive L) true →
        GenericWeight.total weights L ≤ GenericWeight.total weights K := by
  have closure := forest_attained_maximum graph forest rows roots matched rootsMatch
    weights nonnegative b bridge.target
  obtain ⟨_, root, member, initialK, initialLegal, different⟩ :=
    (Physical.bridge_detectable_iff_root bridge positive true graph).mp detectable
  obtain ⟨position, rootEq⟩ := List.mem_iff_get.mp member
  rw [← rootEq, healthy position] at different
  have initialTrue : graph.eval (assignmentOfSet initialK) (graph.roots.get position) = true := by
    cases value : graph.eval (assignmentOfSet initialK) (graph.roots.get position) with
    | false => exact False.elim (different value)
    | true => rfl
  cases selected : (ForestWeightedIndexed.runAll (ForestWeightedIndexed.source n rows)
      weights b bridge.target roots).2.selected with
  | none => exact False.elim (closure.1.mp selected ⟨position, initialK, initialLegal, initialTrue⟩)
  | some candidate =>
    obtain ⟨returned, _, K, legal, value, score, best⟩ := closure.2.1 candidate selected
    refine ⟨candidate, K, rfl, legal, ?_, score, ?_⟩
    · apply (Physical.realizeBridge_detects_iff bridge positive K legal graph.observations).mpr
      refine ⟨returned, ?_⟩
      change graph.eval (assignmentOfSet {bridge.target}) (graph.roots.get returned) ≠
        graph.eval (assignmentOfSet K) (graph.roots.get returned)
      rw [healthy returned, value]
      decide
    · intro L legalL detects
      obtain ⟨other, discrepancy⟩ :=
        (Physical.realizeBridge_detects_iff bridge positive L legalL graph.observations).mp detects
      change graph.eval (assignmentOfSet {bridge.target}) (graph.roots.get other) ≠
        graph.eval (assignmentOfSet L) (graph.roots.get other) at discrepancy
      rw [healthy other] at discrepancy
      have trueAt : graph.eval (assignmentOfSet L) (graph.roots.get other) = true := by
        cases equation : graph.eval (assignmentOfSet L) (graph.roots.get other) with
        | false => exact False.elim (discrepancy equation.symm)
        | true => rfl
      exact best other L legalL trueAt


end Controller.Optimization.Weights
