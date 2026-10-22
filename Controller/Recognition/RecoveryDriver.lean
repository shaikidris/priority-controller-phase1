module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Recognition.ProducerCompletion

@[expose] public section

/-! Finite producer recovery by repeated candidate scans. The computation
receives roots and candidates; it does not receive an intended gate map or a
topological rank. Correctness retains the candidate promise. -/

namespace Controller.Recognition.RecoveryDriver
variable [DecidableEq α]

/-- Each successful scan selects the first ready candidate and consumes one
unit of fuel. Exhaustion and an unsuccessful scan both return the current state. -/
def scan (candidates : List (Producer α)) :
    Nat → Finset α → List (Producer α) → Finset α × List (Producer α)
  | 0, known, trace => (known, trace)
  | fuel + 1, known, trace =>
    match candidates.find? (fun p => decide (p.Ready known)) with
    | none => (known, trace)
    | some p => scan candidates fuel (insert p.output.1 known) (p :: trace)

/-- With enough fuel to insert every unknown signal, the returned run is
saturated. The rank and candidate promise are used in the proof only. -/
theorem scan_correct [Fintype α] (dag : IntendedDAG α) (promise : dag.CandidatePromise)
    (fuel : Nat) (known : Finset α) (trace : List (Producer α))
    (run : dag.Run promise known trace)
    (enough : Fintype.card α ≤ known.card + fuel) :
    dag.Run promise (scan promise.candidates fuel known trace).1
      (scan promise.candidates fuel known trace).2 ∧
    (∀ p ∈ promise.candidates, ¬p.Ready (scan promise.candidates fuel known trace).1) := by
  induction fuel generalizing known trace with
  | zero =>
    simp only [scan]
    have full : known = Finset.univ := known.eq_univ_of_card (by
      have bound := known.card_le_univ
      omega)
    refine ⟨run, ?_⟩
    intro p _ ready
    exact ready.1 (by simp [full])
  | succ fuel ih =>
    cases found : promise.candidates.find? (fun p => decide (p.Ready known)) with
    | none =>
      refine ⟨?_, ?_⟩
      · simpa [scan, found] using run
      · intro p member ready
        have notReady := (List.find?_eq_none.mp found) p member
        exact notReady (by simpa [scan, found] using ready)
    | some p =>
      have ready : p.Ready known := by simpa using List.find?_some found
      have member : p ∈ promise.candidates := List.mem_of_find?_eq_some found
      have next : dag.Run promise (insert p.output.1 known) (p :: trace) :=
        .step run p member ready
      have capacity : Fintype.card α ≤ (insert p.output.1 known).card + fuel := by
        rw [Finset.card_insert_of_notMem ready.1]
        omega
      simpa [scan, found] using ih _ _ next capacity

/-- At most one insertion per nonroot is enough. No execution or maximality
certificate is supplied by a caller. -/
def recover [Fintype α] (roots : Finset α) (candidates : List (Producer α)) :
    Finset α × List (Producer α) :=
  scan candidates (Fintype.card α - roots.card) roots []

theorem recover_run_saturated [Fintype α] (dag : IntendedDAG α)
    (promise : dag.CandidatePromise) :
    dag.Run promise (recover dag.roots promise.candidates).1
      (recover dag.roots promise.candidates).2 ∧
    (∀ p ∈ promise.candidates, ¬p.Ready (recover dag.roots promise.candidates).1) := by
  apply scan_correct dag promise _ _ _ .start
  have bound := dag.roots.card_le_univ
  omega

/-- The actual finite driver returns every signal, every intended nonroot
producer exactly once, and no alternative producer. -/
theorem recover_exact [Fintype α] (dag : IntendedDAG α) (promise : dag.CandidatePromise) :
    let result := recover dag.roots promise.candidates
    result.1 = Finset.univ ∧
      (∀ p ∈ result.2, p = dag.producer p.output.1 ∧ p.output.1 ∉ dag.roots) ∧
      (∀ v, v ∉ dag.roots → dag.producer v ∈ result.2) ∧
      (result.2.map (fun p => p.output.1)).Nodup ∧
      result.2.length = Fintype.card α - dag.roots.card := by
  obtain ⟨run, saturated⟩ := recover_run_saturated dag promise
  have allKnown := dag.saturated_complete promise run saturated
  have full : (recover dag.roots promise.candidates).1 = Finset.univ := by
    ext v
    simp [allKnown v]
  obtain ⟨sound, complete, nodup⟩ := dag.recovery_exact promise run saturated
  refine ⟨full, sound, complete, nodup, ?_⟩
  have size := run.size_eq
  rw [full, Finset.card_univ] at size
  omega

#print axioms scan_correct
#print axioms recover_exact

end Controller.Recognition.RecoveryDriver
