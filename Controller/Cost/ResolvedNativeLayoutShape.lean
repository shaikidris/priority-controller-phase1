/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.FullDictionaryProfile
import Controller.Cost.ResolvedSourceProfile

/-! The native continuation address is a scalar function of source row sizes
and normalization counts. Full coordinate coverage fixes the optional row. -/
namespace Controller.Cost.ResolvedNativeLayoutShape

open Controller Controller.Decoder Controller.Decoder.DAG Controller.CNF Controller.Cost
  Controller.Extensions
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroAdmissibleCaller

theorem endpoint (clauses : List (Clause (Fin ambient))) (start : Nat) :
    Horn.NormalizeLoop.recordOffset clauses start clauses.length +
      2 * (Horn.IndexScan.occurrences clauses start).length =
    start + 3 * clauses.length + 3 * (SharedNormalizationShape.profile clauses).sum := by
  rw [SharedNormalizationShape.incidence_length]
  simp only [Horn.NormalizeLoop.recordOffset, List.take_length]
  have summed : ((clauses.map (fun clause => 3 + (Horn.Worklist.compileClause
    clause).positives.length))).sum =
      3 * clauses.length + (SharedNormalizationShape.profile clauses).sum := by
    induction clauses with
    | nil => simp [SharedNormalizationShape.profile]
    | cons clause rest ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, SharedNormalizationShape.profile]
          at *
        omega
  rw [summed]
  omega

theorem base (graph : DAG n) (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount)
    (heap : Array (Word width)) (layout : ForestZeroDictionary.Layout (n + graph.nodeCount)
      heap.size) :
    SharedZeroNativeQuery.nativeBase heap layout (ResolvedResident.refs 2 (ResolvedResident.rows
      graph ∅ b target reference)) n (by omega) =
      heap.size + 14 + 5 * (ResolvedResident.rows graph ∅ b target reference).length +
        2 * (ResolvedResident.rows graph ∅ b target reference).flatten.length + 5 * n +
        5 * (n + graph.nodeCount) + 3 * (ResolvedSourceProfile.rows graph b).1.sum := by
  let refs := ResolvedResident.refs 2 (ResolvedResident.rows graph ∅ b target reference)
  let dictionary := (compileRows (empty _) (SharedZeroTemplate.touchRows (n + graph.nodeCount))).1
  have coherent : Coherent dictionary := (rows_dictionary (empty _) (empty_coherent _) _).1
  have full : ∀ coordinate : Fin (n + graph.nodeCount), dictionary.slots[coordinate.val] ≠ 0 :=
    SharedZeroDictionary.touch_rows_full
  have covered := FullDictionaryProfile.covered dictionary coherent full n (by omega)
  have dictionaryCard : dictionary.coordinates.size = n + graph.nodeCount := by
    simpa only [dictionary, List.append_nil] using
      SharedZeroDictionary.dictionary_size ([] : List (Clause (Fin (n + graph.nodeCount))))
  have coveredCount := covered
  rw [dictionaryCard] at coveredCount
  have positive := FullDictionaryProfile.positive dictionary coherent full n (by omega)
  have dictionaryEq := ResolvedResident.dictionary_fixed graph ∅ b target reference heap layout
    (base := 2)
  have profile := SharedNormalizationShape.constructor_profile heap layout (empty _) (empty_coherent
    _) refs n (by omega)
  change SharedNormalizationShape.profile (constructorClauses heap layout (empty _) (empty_coherent
    _) refs n _) = _ at profile
  have coverageEq : (ForestZeroNonempty.search (constructorDictionary heap layout (empty _) refs)
      ((constructorDictionary heap layout (empty _) refs).coordinates.size + 1) n 0).reason =
        .covered := by
    rw [dictionaryEq]
    exact covered
  have positiveEq : (Horn.Worklist.compileClause (ForestZeroPositive.positiveClause
      (constructorDictionary heap layout (empty _) refs) n)).positives.length = n := by
    rw [dictionaryEq]
    exact positive
  rw [coverageEq, if_pos rfl, positiveEq, ResolvedResident.original_rows,
    ← ResolvedSourceProfile.rows_value] at profile
  let clauses := constructorClauses heap layout (empty _) (empty_coherent _) refs n (by omega)
  have rowsLength : clauses.length = (ResolvedResident.rows graph ∅ b target reference).length + 1
    := by
    have length := congrArg List.length profile
    simp only [SharedNormalizationShape.profile, List.length_map, List.length_append,
      List.length_cons, List.length_nil, ResolvedSourceProfile.rows_value] at length
    rw [ResolvedSourceProfile.rows_value graph b target reference] at length
    simpa only [SharedNormalizationShape.profile, List.length_map, Nat.zero_add] using length
  have heapSize := ResolvedResident.constructor_size graph ∅ b target reference heap layout
  have scratch : ResolvedResident.scratchSize heap.size n (n + graph.nodeCount)
      (ResolvedResident.rows graph ∅ b target reference) =
      heap.size + 7 + 2 * (ResolvedResident.rows graph ∅ b target reference).length +
        2 * (ResolvedResident.rows graph ∅ b target reference).flatten.length + 2 * n := by
    simp only [ResolvedResident.scratchSize, EnumerationFixedResident.heapSize,
      List.length_nil, Nat.add_zero, ResolvedResident.refs_length, ResolvedResident.refs_literals]
    change _ + (if (ForestZeroNonempty.search dictionary (_ + 1) n 0).reason = .covered then 2 * n
      else 0) = _
    rw [coveredCount, if_pos rfl]
    omega
  have dictionarySize := ResolvedResident.dictionary_size graph ∅ b target reference heap layout
    (base := 2)
  unfold SharedZeroNativeQuery.nativeBase
  simp only [constructorFormula_rows]
  rw [endpoint]
  change (constructorHeap heap layout (empty _) refs n).size +
    5 * (constructorDictionary heap layout (empty _) refs).coordinates.size + 4 +
    3 * clauses.length + 3 * (SharedNormalizationShape.profile clauses).sum = _
  have scalarHeap : (constructorHeap heap layout (empty _) refs n).size =
      heap.size + 7 + 2 * (ResolvedResident.rows graph ∅ b target reference).length +
        2 * (ResolvedResident.rows graph ∅ b target reference).flatten.length + 2 * n :=
          heapSize.trans scratch
  have scalarDictionary : (constructorDictionary heap layout (empty _) refs).coordinates.size = n +
    graph.nodeCount := dictionarySize
  rw [profile, List.sum_append, List.sum_cons, List.sum_nil, rowsLength]
  rw [scalarHeap, scalarDictionary]
  omega

end Controller.Cost.ResolvedNativeLayoutShape
