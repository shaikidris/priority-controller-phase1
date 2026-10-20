module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ForestSelectionMachine
public import Controller.Cost.ForestRootProjection

import all Init.Data.List.ToArrayImpl

@[expose] public section


/-! A source constructor for the variable descriptor/candidate prefix. The
machine reverses the retained parent records and emits instructions one at a
time. Parent fields and selected identifiers are read from the computed state;
no selector or graph traversal is called while writing the image. Counts are
source constructor transitions, separate from fetched detector instructions. -/
namespace Controller.Cost.ForestDescriptorConstruction

open Controller Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestCursorDescriptors Controller.Cost.ForestCursorMaterialize
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestWeightedTagged

inductive Phase where
  | reverse (pending saved : List ParentEntry)
  | records (pending : List ParentEntry)
  | parentAllocate (entry : ParentEntry) (rest : List ParentEntry)
  | positionConstant (entry : ParentEntry) (rest : List ParentEntry)
  | positionAllocate (rest : List ParentEntry)
  | zeroes (remaining : Nat)
  | zeroAllocate (remaining : Nat)
  | root
  | pointer
  | done

structure Configuration (width : Nat) where
  phase : Phase
  image : Program width 4

def step (width channels root pointer : Nat) (state : Configuration width) :
    Option (Configuration width) :=
  match state.phase with
  | .reverse (entry :: rest) saved => some ⟨.reverse rest (entry :: saved), state.image⟩
  | .reverse [] saved => some ⟨.records saved, state.image⟩
  | .records (entry :: rest) =>
      some ⟨.parentAllocate entry rest, state.image.push (.constant 2 (word width entry.parent))⟩
  | .parentAllocate entry rest => some ⟨.positionConstant entry rest, state.image.push (.allocate 2)⟩
  | .positionConstant entry rest =>
      some ⟨.positionAllocate rest, state.image.push (.constant 2 (word width entry.position))⟩
  | .positionAllocate rest => some ⟨.records rest, state.image.push (.allocate 2)⟩
  | .records [] => some ⟨.zeroes (channels + 3), state.image⟩
  | .zeroes (remaining + 1) =>
      some ⟨.zeroAllocate remaining, state.image.push (.constant 2 (word width 0))⟩
  | .zeroAllocate remaining => some ⟨.zeroes remaining, state.image.push (.allocate 2)⟩
  | .zeroes 0 => some ⟨.root, state.image⟩
  | .root => some ⟨.pointer, state.image.push (.constant 1 (word width root))⟩
  | .pointer => some ⟨.done, state.image.push (.constant 2 (word width pointer))⟩
  | .done => none

inductive Trace (width channels root pointer : Nat) :
    Configuration width → Configuration width → Nat → Prop
  | refl (state) : Trace width channels root pointer state state 0
  | next {first middle last ticks}
      (transition : step width channels root pointer first = some middle)
      (tail : Trace width channels root pointer middle last ticks) :
      Trace width channels root pointer first last (ticks + 1)

theorem Trace.single {first last : Configuration width}
    (transition : step width channels root pointer first = some last) :
    Trace width channels root pointer first last 1 := .next transition (.refl last)

theorem Trace.append {first middle last : Configuration width} {left right : Nat}
    (earlier : Trace width channels root pointer first middle left)
    (later : Trace width channels root pointer middle last right) :
    Trace width channels root pointer first last (left + right) := by
  induction earlier with
  | refl => simpa using later
  | next transition tail ih =>
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.next transition (ih later)

private theorem reverse_trace (pending saved : List ParentEntry) (image : Program width 4) :
    Trace width channels root pointer ⟨.reverse pending saved, image⟩
      ⟨.records (pending.reverse ++ saved), image⟩ (pending.length + 1) := by
  induction pending generalizing saved with
  | nil => simpa using Trace.single (width := width) (channels := channels) (root := root) (pointer := pointer) rfl
  | cons entry rest ih =>
      have first : Trace width channels root pointer ⟨.reverse (entry :: rest) saved, image⟩
          ⟨.reverse rest (entry :: saved), image⟩ 1 := Trace.single rfl
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        first.append (ih (entry :: saved))

private theorem records_trace (pending : List ParentEntry) (image : Program width 4) :
    Trace width channels root pointer ⟨.records pending, image⟩
      ⟨.zeroes (channels + 3), (writeCode width (fields pending)).toArrayAux image⟩
      (4 * pending.length + 1) := by
  induction pending generalizing image with
  | nil => exact Trace.single rfl
  | cons entry rest ih =>
      let first := image.push (.constant 2 (word width entry.parent))
      let second := first.push (.allocate 2)
      let third := second.push (.constant 2 (word width entry.position))
      let fourth := third.push (.allocate 2)
      have a : Trace width channels root pointer ⟨.records (entry :: rest), image⟩
          ⟨.parentAllocate entry rest, first⟩ 1 := Trace.single rfl
      have b : Trace width channels root pointer ⟨.parentAllocate entry rest, first⟩
          ⟨.positionConstant entry rest, second⟩ 1 := Trace.single rfl
      have c : Trace width channels root pointer ⟨.positionConstant entry rest, second⟩
          ⟨.positionAllocate rest, third⟩ 1 := Trace.single rfl
      have d : Trace width channels root pointer ⟨.positionAllocate rest, third⟩
          ⟨.records rest, fourth⟩ 1 := Trace.single rfl
      simpa [fields, writeCode, cellCode, List.toArrayAux, first, second, third, fourth,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (((a.append b).append c).append d).append (ih fourth)

private theorem zeroes_trace (remaining : Nat) (image : Program width 4) :
    Trace width channels root pointer ⟨.zeroes remaining, image⟩
      ⟨.root, (writeCode width (List.replicate remaining 0)).toArrayAux image⟩
      (2 * remaining + 1) := by
  induction remaining generalizing image with
  | zero => exact Trace.single rfl
  | succ remaining ih =>
      let first := image.push (.constant 2 (word width 0))
      let second := first.push (.allocate 2)
      have a : Trace width channels root pointer ⟨.zeroes (remaining + 1), image⟩
          ⟨.zeroAllocate remaining, first⟩ 1 := Trace.single rfl
      have b : Trace width channels root pointer ⟨.zeroAllocate remaining, first⟩
          ⟨.zeroes remaining, second⟩ 1 := Trace.single rfl
      simpa [List.replicate_succ, writeCode, cellCode, List.toArrayAux, first, second,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (a.append b).append (ih second)

private theorem writeCode_append (left right : List Nat) :
    writeCode width (left ++ right) = writeCode width left ++ writeCode width right := by
  induction left with
  | nil => rfl
  | cons value rest ih => simp only [List.cons_append, writeCode, ih, List.append_assoc]

/-- Every emitted instruction is produced by the fixed transition function.
The trace includes descriptor reversal, both fields of every parent record,
the counter/metadata zero region, and both selected identifier constants. -/
theorem complete (channels : Nat) (entries : List ParentEntry) (root pointer : Nat)
    (image : Program width 4) :
    Trace width channels root pointer ⟨.reverse entries [], image⟩
      ⟨.done, ((writeCode width (fields entries.reverse ++ List.replicate (channels + 3) 0)) ++
        ([Instruction.constant 1 (word width root), Instruction.constant 2 (word width pointer)] : List (Instruction width 4))).toArrayAux image⟩
      (5 * entries.length + 2 * channels + 11) := by
  have a := reverse_trace (width := width) (channels := channels) (root := root) (pointer := pointer) entries [] image
  simp only [List.append_nil] at a
  have b := records_trace (channels := channels) (root := root) (pointer := pointer) entries.reverse image
  let parents := (writeCode width (fields entries.reverse)).toArrayAux image
  have c := zeroes_trace (channels := channels) (root := root) (pointer := pointer) (channels + 3) parents
  let zeroed := (writeCode width (List.replicate (channels + 3) 0)).toArrayAux parents
  have d : Trace width channels root pointer ⟨.root, zeroed⟩
      ⟨.pointer, zeroed.push (.constant 1 (word width root))⟩ 1 := Trace.single rfl
  have e : Trace width channels root pointer ⟨.pointer, zeroed.push (.constant 1 (word width root))⟩
      ⟨.done, (zeroed.push (.constant 1 (word width root))).push (.constant 2 (word width pointer))⟩ 1 := Trace.single rfl
  have trace := (((a.append b).append c).append d).append e
  have contents : ((zeroed.push (.constant 1 (word width root))).push (.constant 2 (word width pointer))) =
      ((writeCode width (fields entries.reverse ++ List.replicate (channels + 3) 0)) ++
        ([Instruction.constant 1 (word width root), Instruction.constant 2 (word width pointer)] : List (Instruction width 4))).toArrayAux image := by
    apply Array.toList_inj.mp
    simp [zeroed, parents, writeCode_append, List.append_assoc]
  rw [contents] at trace
  convert trace using 1
  simp only [List.length_reverse]
  omega

theorem prefix_exact (state : ForestWeightedIndexed.State n W) (candidate : Candidate W)
    (image : Program width 4) :
    Trace width n candidate.root candidate.pointer ⟨.reverse state.descriptors.entries [], image⟩
      ⟨.done, (descriptorCode width state ++ candidateCode width candidate).toArrayAux image⟩
      (5 * state.descriptors.entries.length + 2 * n + 11) := complete n _ _ _ _

def run (width channels root pointer : Nat) : Nat → Configuration width → Configuration width
  | 0, state => state
  | fuel + 1, state =>
      match step width channels root pointer state with
      | none => state
      | some next => run width channels root pointer fuel next

theorem Trace.run {first last : Configuration width} {ticks : Nat}
    (trace : Trace width channels root pointer first last ticks) :
    run width channels root pointer ticks first = last := by
  induction trace with
  | refl => rfl
  | next transition tail ih => simp only [ForestDescriptorConstruction.run, transition]; exact ih

end Controller.Cost.ForestDescriptorConstruction
