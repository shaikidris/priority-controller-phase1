/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ForestCompilerMarks
import Controller.Cost.ForestScalarNegativeConstruction
import Controller.Cost.ForestFixedControlRecipes

/-! Tail-recursive negative-resident assembly. The runtime state carries one
mark table, scalar placement operands and completed output blocks. Local
coordinate inverses and relabelled clauses occur only in refinement proofs. -/
set_option maxRecDepth 10000

namespace Controller.Cost.ForestStreamingConstruction

open Controller.Cost Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestFixedControlRecipes Controller.Cost.ForestZeroAdmissibleCaller

variable {ambient : Nat}

structure State (ambient width : Nat) where
  marks : ForestCompilerMarks.State ambient
  cursor : Nat
  blocks : List (List (Instruction width 8))
  operations : Nat

def initial (ambient width entry : Nat) : State ambient width :=
  ⟨ForestCompilerMarks.initial ambient, entry, [], ambient + 16⟩

def step (protectedEnd channels : Nat) (state : State ambient width)
    (refs : List (List (Reference ambient))) : State ambient width :=
  let compiled := ForestCompilerMarks.query channels state.marks
    (ForestZeroAssembly.originalRows (reservedReferences refs))
  let provisional := ForestScalarNegativeConstruction.form width protectedEnd channels state.cursor 0
    refs compiled.1.count compiled.2.1
  let next := state.cursor + provisional.1.length
  let current := ForestScalarNegativeConstruction.form width protectedEnd channels state.cursor next
    refs compiled.1.count compiled.2.1
  ⟨compiled.1, next, current.1 :: state.blocks,
    state.operations + compiled.2.2 + provisional.2 + current.2 +
      2 * provisional.1.length + current.1.length + 4 * refs.length +
      4 * refs.flatten.length + 10⟩

def run (protectedEnd channels : Nat) (state : State ambient width) :
    List (List (List (Reference ambient))) → State ambient width
  | [] => state
  | refs :: rest => run protectedEnd channels (step protectedEnd channels state refs) rest

def image (state : State ambient width) : List (Instruction width 8) :=
  state.blocks.reverse.flatten ++
    evaluate (fun i : Fin 0 => [].getD i.val 0) (exhausted.constructionRecipe width)

/-- Materialization copies the accumulated blocks once; no append traverses
an accumulated instruction prefix during the packet loop. -/
def compile (protectedEnd channels : Nat) (state : State ambient width)
    (packets : List (List (List (Reference ambient)))) (prior : Array (Instruction width 8)) :
    Array (Instruction width 8) :=
  (image (run protectedEnd channels state packets)).toArrayAux prior

private theorem rows_length (refs : List (List (Reference ambient))) :
    (ForestZeroAssembly.originalRows (reservedReferences refs)).length = refs.length + 1 := by
  simp [ForestZeroAssembly.originalRows, reservedReferences]

private theorem literals_length (refs : List (List (Reference ambient))) :
    (ForestZeroAssembly.originalRows (reservedReferences refs)).flatten.length = refs.flatten.length := by
  simp [ForestZeroAssembly.originalRows, reservedReferences, List.length_flatten,
    List.map_map, Function.comp_def]

/-- The proof dictionary is compressed to the actual count-only state. It is
not stored by the executable constructor. -/
theorem step_refines (protectedEnd channels : Nat) (state : State ambient width)
    (dictionary : ForestCompilerDictionary.State ambient)
    (valid : ForestCompilerDictionary.Valid dictionary)
    (same : state.marks = ForestCompilerMarks.compress dictionary)
    (refs : List (List (Reference ambient))) :
    let compiled := ForestCompilerQueries.query channels dictionary
      (ForestZeroAssembly.originalRows (reservedReferences refs))
    let provisional := ForestCachedNegativeProgram.instructions width protectedEnd channels
      state.cursor 0 refs compiled.2.1
    let next := state.cursor + provisional.length
    let current := ForestCachedNegativeProgram.instructions width protectedEnd channels
      state.cursor next refs compiled.2.1
    (step protectedEnd channels state refs).marks = ForestCompilerMarks.compress compiled.1 ∧
      (step protectedEnd channels state refs).cursor = next ∧
      (step protectedEnd channels state refs).blocks = current :: state.blocks := by
  have metadata := ForestCompilerMarks.query_refines channels dictionary valid
    (ForestZeroAssembly.originalRows (reservedReferences refs))
  have count : (ForestCompilerQueries.query channels dictionary
      (ForestZeroAssembly.originalRows (reservedReferences refs))).1.coordinates.size =
      (ForestCompilerQueries.query channels dictionary
      (ForestZeroAssembly.originalRows (reservedReferences refs))).2.1.coordinates.size := rfl
  dsimp only [step]
  rw [same, metadata.1, metadata.2]
  change ForestCompilerMarks.compress _ = ForestCompilerMarks.compress _ ∧ _
  dsimp only [ForestCompilerMarks.compress]
  rw [count, ForestScalarNegativeConstruction.form_refines,
    ForestNegativeConstruction.form_image, ForestScalarNegativeConstruction.form_refines,
    ForestNegativeConstruction.form_image]
  exact ⟨rfl, rfl, rfl⟩

theorem run_refines (protectedEnd channels : Nat) (state : State ambient width)
    (dictionary : ForestCompilerDictionary.State ambient)
    (valid : ForestCompilerDictionary.Valid dictionary)
    (same : state.marks = ForestCompilerMarks.compress dictionary)
    (packets : List (List (List (Reference ambient)))) :
    (run protectedEnd channels state packets).marks =
      ForestCompilerMarks.compress
        (ForestCachedNegativeProgram.resident width protectedEnd channels dictionary state.cursor packets).1 ∧
    image (run protectedEnd channels state packets) = state.blocks.reverse.flatten ++
      (ForestCachedNegativeProgram.resident width protectedEnd channels dictionary state.cursor packets).2.1 := by
  induction packets generalizing state dictionary with
  | nil =>
      simp only [run, image, ForestCachedNegativeProgram.resident]
      exact ⟨same, congrArg (List.append _) (exhausted.constructionRecipe_eq width)⟩
  | cons refs rest ih =>
      let compiled := ForestCompilerQueries.query channels dictionary
        (ForestZeroAssembly.originalRows (reservedReferences refs))
      have one := step_refines protectedEnd channels state dictionary valid same refs
      have tail := ih (step protectedEnd channels state refs) compiled.1
        (ForestCompilerQueries.query_valid channels dictionary valid _) one.1
      constructor
      · simpa only [run, ForestCachedNegativeProgram.resident, ← one.2.1] using tail.1
      · rw [run, tail.2, one.2.2, List.reverse_cons, List.flatten_append,
          List.flatten_cons, List.flatten_nil, List.append_nil]
        rw [one.2.1]
        simp only [ForestCachedNegativeProgram.resident, List.append_assoc]
        rfl

theorem step_work (protectedEnd channels : Nat) (state : State ambient width)
    (refs : List (List (Reference ambient))) :
    (step protectedEnd channels state refs).operations ≤ state.operations +
      40000 + 600 * refs.length + 2500 * refs.flatten.length := by
  let compiled := ForestCompilerMarks.query channels state.marks
    (ForestZeroAssembly.originalRows (reservedReferences refs))
  let provisional := ForestScalarNegativeConstruction.form width protectedEnd channels state.cursor 0
    refs compiled.1.count compiled.2.1
  let next := state.cursor + provisional.1.length
  have metadata := ForestCompilerMarks.query_work channels state.marks
    (ForestZeroAssembly.originalRows (reservedReferences refs))
  rw [rows_length, literals_length] at metadata
  have first := ForestScalarNegativeConstruction.form_work width protectedEnd channels state.cursor 0
    refs compiled.1.count compiled.2.1
  have second := ForestScalarNegativeConstruction.form_work width protectedEnd channels state.cursor next
    refs compiled.1.count compiled.2.1
  have firstSize := ForestScalarNegativeConstruction.instruction_bound width protectedEnd channels state.cursor 0
    refs compiled.1.count compiled.2.1
  have secondSize := ForestScalarNegativeConstruction.instruction_bound width protectedEnd channels state.cursor next
    refs compiled.1.count compiled.2.1
  change compiled.2.2 ≤ _ at metadata
  change provisional.2 ≤ _ at first
  change provisional.1.length ≤ _ at firstSize
  change state.operations + compiled.2.2 + provisional.2 +
    (ForestScalarNegativeConstruction.form width protectedEnd channels state.cursor next
      refs compiled.1.count compiled.2.1).2 + 2 * provisional.1.length +
    (ForestScalarNegativeConstruction.form width protectedEnd channels state.cursor next
      refs compiled.1.count compiled.2.1).1.length + 4 * refs.length +
      4 * refs.flatten.length + 10 ≤ _
  omega

theorem run_work (protectedEnd channels : Nat) (state : State ambient width)
    (packets : List (List (List (Reference ambient)))) :
    (run protectedEnd channels state packets).operations ≤ state.operations +
      40000 * packets.length + 600 * packets.flatten.length +
        2500 * packets.flatten.flatten.length := by
  induction packets generalizing state with
  | nil => simp [run]
  | cons refs rest ih =>
      have one := step_work protectedEnd channels state refs
      have tail := ih (step protectedEnd channels state refs)
      simp only [run, List.length_cons, List.flatten_cons, List.flatten_append, List.length_append]
      omega

def buffered (state : State ambient width) : Nat := state.blocks.flatten.length

theorem step_buffered (protectedEnd channels : Nat) (state : State ambient width)
    (refs : List (List (Reference ambient))) :
    buffered (step protectedEnd channels state refs) ≤ buffered state +
      584 + 5 * refs.length + 28 * refs.flatten.length := by
  have current := ForestScalarNegativeConstruction.instruction_bound width protectedEnd channels
    state.cursor
    (state.cursor + (ForestScalarNegativeConstruction.form width protectedEnd channels state.cursor 0
      refs (ForestCompilerMarks.query channels state.marks
        (ForestZeroAssembly.originalRows (reservedReferences refs))).1.count
      (ForestCompilerMarks.query channels state.marks
        (ForestZeroAssembly.originalRows (reservedReferences refs))).2.1).1.length)
    refs (ForestCompilerMarks.query channels state.marks
      (ForestZeroAssembly.originalRows (reservedReferences refs))).1.count
    (ForestCompilerMarks.query channels state.marks
      (ForestZeroAssembly.originalRows (reservedReferences refs))).2.1
  simp only [buffered, step, List.flatten_cons, List.length_append]
  omega

theorem run_buffered (protectedEnd channels : Nat) (state : State ambient width)
    (packets : List (List (List (Reference ambient)))) :
    buffered (run protectedEnd channels state packets) ≤ buffered state +
      584 * packets.length + 5 * packets.flatten.length + 28 * packets.flatten.flatten.length := by
  induction packets generalizing state with
  | nil => simp [run]
  | cons refs rest ih =>
      have one := step_buffered protectedEnd channels state refs
      have tail := ih (step protectedEnd channels state refs)
      simp only [run, List.length_cons, List.flatten_cons, List.flatten_append, List.length_append]
      omega


/-- Storage retained at packet boundaries. Each packed instruction is charged
an eight-word record/list allowance. The shared mark table has one word per
ambient coordinate; no prior dictionary version is a state field. Temporary
storage inside a single image formation is a separate obligation. -/
def retainedWords (state : State ambient width) : Nat :=
  ambient + 24 + 8 * buffered state + 2 * state.blocks.length

theorem step_blocks (protectedEnd channels : Nat) (state : State ambient width)
    (refs : List (List (Reference ambient))) :
    (step protectedEnd channels state refs).blocks.length = state.blocks.length + 1 := rfl

theorem step_retained (protectedEnd channels : Nat) (state : State ambient width)
    (refs : List (List (Reference ambient))) :
    retainedWords (step protectedEnd channels state refs) ≤ retainedWords state +
      4674 + 40 * refs.length + 224 * refs.flatten.length := by
  have size := step_buffered protectedEnd channels state refs
  simp only [retainedWords, step_blocks]
  omega

/-- A trace of the actual tail loop, recording its boundary storage. This
covers retained compiler state, not transient allocations inside `step`. -/
inductive BoundaryTrace (protectedEnd channels : Nat) : State ambient width →
    List (List (List (Reference ambient))) → State ambient width → Nat → Prop
  | nil (state) : BoundaryTrace protectedEnd channels state [] state (retainedWords state)
  | cons (state refs rest final peak)
      (tail : BoundaryTrace protectedEnd channels (step protectedEnd channels state refs) rest final peak) :
      BoundaryTrace protectedEnd channels state (refs :: rest) final (max (retainedWords state) peak)

theorem run_retained (protectedEnd channels : Nat) (state : State ambient width)
    (packets : List (List (List (Reference ambient)))) :
    ∃ peak, BoundaryTrace protectedEnd channels state packets (run protectedEnd channels state packets) peak ∧
      peak ≤ retainedWords state + 4674 * packets.length +
        40 * packets.flatten.length + 224 * packets.flatten.flatten.length := by
  induction packets generalizing state with
  | nil => exact ⟨retainedWords state, .nil state, by simp⟩
  | cons refs rest ih =>
      obtain ⟨peak, trace, bound⟩ := ih (step protectedEnd channels state refs)
      have one := step_retained protectedEnd channels state refs
      refine ⟨max (retainedWords state) peak, .cons state refs rest _ _ trace, ?_⟩
      simp only [List.length_cons, List.flatten_cons, List.flatten_append, List.length_append]
      apply Nat.max_le.mpr
      constructor <;> omega

theorem compile_contents (protectedEnd channels : Nat) (state : State ambient width)
    (dictionary : ForestCompilerDictionary.State ambient)
    (valid : ForestCompilerDictionary.Valid dictionary)
    (same : state.marks = ForestCompilerMarks.compress dictionary)
    (packets : List (List (List (Reference ambient)))) (prior : Array (Instruction width 8)) :
    (compile protectedEnd channels state packets prior).toList = prior.toList ++ state.blocks.reverse.flatten ++
      (ForestCachedNegativeProgram.resident width protectedEnd channels dictionary state.cursor packets).2.1 := by
  have exactImage := (run_refines protectedEnd channels state dictionary valid same packets).2
  simp only [compile, Array.toArrayAux_eq, exactImage, List.append_assoc]


theorem run_blocks (protectedEnd channels : Nat) (state : State ambient width)
    (packets : List (List (List (Reference ambient)))) :
    (run protectedEnd channels state packets).blocks.length = state.blocks.length + packets.length := by
  induction packets generalizing state with
  | nil => simp [run]
  | cons refs rest ih => simp only [run, ih, step_blocks, List.length_cons]; omega

/-- Loop charges plus reversal/flattening and one final program-array write.
The byte cost of the fixed-width backing words remains separate. -/
def constructionWork (protectedEnd channels : Nat) (state : State ambient width)
    (packets : List (List (List (Reference ambient)))) (prior : Array (Instruction width 8)) : Nat :=
  let final := run protectedEnd channels state packets
  final.operations + 8 * buffered final + 4 * final.blocks.length + 2 * prior.size + 100

theorem construction_bound (protectedEnd channels : Nat) (state : State ambient width)
    (packets : List (List (List (Reference ambient)))) (prior : Array (Instruction width 8)) :
    constructionWork protectedEnd channels state packets prior ≤ state.operations +
      8 * buffered state + 4 * state.blocks.length + 2 * prior.size +
        50000 * packets.length + 1000 * packets.flatten.length +
          3000 * packets.flatten.flatten.length + 100 := by
  have instructions := run_buffered protectedEnd channels state packets
  have computation := run_work protectedEnd channels state packets
  have blocks := run_blocks protectedEnd channels state packets
  dsimp only [constructionWork]
  rw [blocks]
  omega

end Controller.Cost.ForestStreamingConstruction
