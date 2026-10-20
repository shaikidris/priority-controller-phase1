module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Optimization.Weights

@[expose] public section


/-! A deterministic continuation machine for the source-indexed forest
selector. A transition consumes one source/control occurrence. It never calls
the recursive selector to obtain an answer. Generic weight operations retain
the existing separate arithmetic count; refinement to fixed-width instructions
and instruction-image generation have separate interfaces. -/
namespace Controller.Cost.ForestSelectionMachine

open Controller Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestWeightedIndexed Controller.Cost.ForestCursorTraversal

variable {n : Nat} {W : Type} [AddCommGroup W] [LinearOrder W]

inductive Task (n : Nat) where
  | visit (root owner : Nat)
  | children (root owner position : Nat) (remaining : List (Fin owner))
  | enterGuards (root owner child position : Nat) (remaining : List (Channel n))
      (seen : List (Channel n × Nat))
  | leaveGuards (root owner : Nat) (remaining : List (Channel n × Nat))
  | operation (root : Nat) (operation : CursorOp n)
  | roots (position : Nat) (remaining : List Nat)

structure Configuration (n : Nat) (W : Type) where
  data : ForestWeightedIndexed.State n W
  tasks : List (Task n)

/-- Node reads are indexed. The continuation retains child-list tails and
guard occurrence pairs, rather than materialized paths or cursor-operation lists. -/
def step (table : Source n) (weights : Channel n → W) (total : W) (b : Nat)
    (target : Channel n) (state : Configuration n W) : Option (Configuration n W) :=
  match state.tasks with
  | [] => none
  | task :: rest =>
    match task with
    | .operation root operation =>
        some ⟨emit weights total root b target state.data operation, rest⟩
    | .visit root owner =>
        let entered := emit weights total root b target state.data (.node owner)
        let tasks := match readNode table owner with
          | .zero => rest
          | .liveAnd _ _ => rest
          | .input head => .operation root (.leaf owner [] head) :: rest
          | .disj children => .children root owner 0 children :: rest
          | .guard child labels => .enterGuards root owner child.val 0 labels [] :: rest
        some ⟨entered, tasks⟩
    | .children _ _ _ [] => some ⟨state.data, rest⟩
    | .children root owner position (child :: children) =>
        some ⟨emit weights total root b target state.data (.down owner position child.val),
          .visit root child.val :: .operation root .up ::
            .children root owner (position + 1) children :: rest⟩
    | .enterGuards root owner child position (channel :: labels) seen =>
        some ⟨emit weights total root b target state.data (.enter owner position channel),
          .enterGuards root owner child (position + 1) labels ((channel, position) :: seen) :: rest⟩
    | .enterGuards root owner child _ [] seen =>
        some ⟨emit weights total root b target state.data (.down owner 0 child),
          .visit root child :: .operation root .up :: .leaveGuards root owner seen :: rest⟩
    | .leaveGuards _ _ [] => some ⟨state.data, rest⟩
    | .leaveGuards root owner ((channel, position) :: labels) =>
        some ⟨emit weights total root b target state.data (.leave owner position channel),
          .leaveGuards root owner labels :: rest⟩
    | .roots _ [] => some ⟨state.data, rest⟩
    | .roots position (owner :: roots) =>
        some ⟨startRoot state.data, .visit position owner :: .roots (position + 1) roots :: rest⟩

inductive Trace (table : Source n) (weights : Channel n → W) (total : W)
    (b : Nat) (target : Channel n) : Configuration n W → Configuration n W → Nat → Prop
  | refl (state) : Trace table weights total b target state state 0
  | step {first middle last ticks}
      (transition : step table weights total b target first = some middle)
      (tail : Trace table weights total b target middle last ticks) :
      Trace table weights total b target first last (ticks + 1)

theorem Trace.single {first last : Configuration n W}
    (transition : ForestSelectionMachine.step table weights total b target first = some last) :
    Trace table weights total b target first last 1 :=
  .step transition (.refl last)

theorem Trace.append {first middle last : Configuration n W} {left right : Nat}
    (earlier : Trace table weights total b target first middle left)
    (later : Trace table weights total b target middle last right) :
    Trace table weights total b target first last (left + right) := by
  induction earlier with
  | refl => simpa using later
  | step transition tail ih =>
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.step transition (ih later)

@[simp] theorem emit_operations (weights : Channel n → W) (total : W)
    (root b : Nat) (target : Channel n) (state : ForestWeightedIndexed.State n W)
    (operation : CursorOp n) :
    (emit weights total root b target state operation).operations = state.operations + 1 := by
  cases operation <;> simp only [emit]
  all_goals split_ifs <;> rfl

def childrenResult (table : Source n) (weights : Channel n → W) (total : W)
    (root owner b : Nat) (target : Channel n) (children : List (Fin owner))
    (position : Nat) (state : ForestWeightedIndexed.State n W) : ForestWeightedIndexed.State n W :=
  (children.zipIdx position).foldl (fun current item =>
    emit weights total root b target
      (runNode table weights total root b target item.1.val
        (emit weights total root b target current (.down owner item.2 item.1.val))) .up) state

private theorem children_trace (table : Source n) (weights : Channel n → W) (total : W)
    (root owner b : Nat) (target : Channel n)
    (childTrace : ∀ (child : Fin owner) (state : ForestWeightedIndexed.State n W) (rest : List (Task n)),
      ∃ ticks, Trace table weights total b target ⟨state, .visit root child.val :: rest⟩
        ⟨runNode table weights total root b target child.val state, rest⟩ ticks ∧
        ticks + 3 * state.operations ≤ 3 * (runNode table weights total root b target child.val state).operations)
    (children : List (Fin owner)) (position : Nat)
    (state : ForestWeightedIndexed.State n W) (rest : List (Task n)) :
    ∃ ticks, Trace table weights total b target
      ⟨state, .children root owner position children :: rest⟩
      ⟨childrenResult table weights total root owner b target children position state, rest⟩ ticks ∧
      ticks + 3 * state.operations ≤
        3 * (childrenResult table weights total root owner b target children position state).operations + 1 := by
  induction children generalizing position state with
  | nil => exact ⟨1, Trace.single rfl, by simp [childrenResult, Nat.add_comm]⟩
  | cons child children ih =>
      let down := emit weights total root b target state (.down owner position child.val)
      let visited := runNode table weights total root b target child.val down
      let up := emit weights total root b target visited .up
      obtain ⟨childTicks, childRun, childBound⟩ := childTrace child down
        (.operation root .up :: .children root owner (position + 1) children :: rest)
      obtain ⟨tailTicks, tailRun, tailBound⟩ := ih (position + 1) up
      have start : Trace table weights total b target
          ⟨state, .children root owner position (child :: children) :: rest⟩
          ⟨down, .visit root child.val :: .operation root .up ::
            .children root owner (position + 1) children :: rest⟩ 1 := Trace.single rfl
      have pop : Trace table weights total b target
          ⟨visited, .operation root .up :: .children root owner (position + 1) children :: rest⟩
          ⟨up, .children root owner (position + 1) children :: rest⟩ 1 := Trace.single rfl
      refine ⟨1 + childTicks + 1 + tailTicks, ?_, ?_⟩
      · simpa only [childrenResult, List.zipIdx_cons, List.foldl_cons] using
          ((start.append childRun).append pop).append tailRun
      · have downOps : down.operations = state.operations + 1 := emit_operations ..
        have upOps : up.operations = visited.operations + 1 := emit_operations ..
        change childTicks + 3 * down.operations ≤ 3 * visited.operations at childBound
        simp only [childrenResult, List.zipIdx_cons, List.foldl_cons] at tailBound ⊢
        change tailTicks + 3 * up.operations ≤
          3 * (childrenResult table weights total root owner b target children (position + 1) up).operations + 1 at tailBound
        change 1 + childTicks + 1 + tailTicks + 3 * state.operations ≤
          3 * (childrenResult table weights total root owner b target children (position + 1) up).operations + 1
        omega

def enteredGuards (weights : Channel n → W) (total : W) (root owner b : Nat)
    (target : Channel n) (labels : List (Channel n)) (position : Nat)
    (state : ForestWeightedIndexed.State n W) : ForestWeightedIndexed.State n W :=
  (labels.zipIdx position).foldl (fun current item =>
    emit weights total root b target current (.enter owner item.2 item.1)) state

private theorem enter_trace (table : Source n) (weights : Channel n → W) (total : W)
    (root owner child b : Nat) (target : Channel n) (labels : List (Channel n))
    (position : Nat) (seen : List (Channel n × Nat))
    (state : ForestWeightedIndexed.State n W) (rest : List (Task n)) :
    Trace table weights total b target
      ⟨state, .enterGuards root owner child position labels seen :: rest⟩
      ⟨enteredGuards weights total root owner b target labels position state,
        .enterGuards root owner child (position + labels.length) []
          ((labels.zipIdx position).reverse ++ seen) :: rest⟩ labels.length ∧
      (enteredGuards weights total root owner b target labels position state).operations =
        state.operations + labels.length := by
  induction labels generalizing position seen state with
  | nil =>
      constructor
      · simp only [enteredGuards, List.zipIdx_nil, List.foldl_nil, List.length_nil,
          Nat.add_zero, List.reverse_nil, List.nil_append]
        exact .refl _
      · simp [enteredGuards]
  | cons channel labels ih =>
      let next := emit weights total root b target state (.enter owner position channel)
      obtain ⟨tail, operations⟩ := ih (position + 1) ((channel, position) :: seen) next
      constructor
      · have first : Trace table weights total b target
            ⟨state, .enterGuards root owner child position (channel :: labels) seen :: rest⟩
            ⟨next, .enterGuards root owner child (position + 1) labels ((channel, position) :: seen) :: rest⟩ 1 :=
          Trace.single rfl
        simpa [enteredGuards, List.zipIdx_cons, List.reverse_cons, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using first.append tail
      · simp only [enteredGuards, List.zipIdx_cons, List.foldl_cons, List.length_cons]
        change (enteredGuards weights total root owner b target labels (position + 1) next).operations = _
        rw [operations]
        have nextOps : next.operations = state.operations + 1 := emit_operations ..
        omega

def leftGuards (weights : Channel n → W) (total : W) (root owner b : Nat)
    (target : Channel n) (labels : List (Channel n × Nat))
    (state : ForestWeightedIndexed.State n W) : ForestWeightedIndexed.State n W :=
  labels.foldl (fun current item => emit weights total root b target current (.leave owner item.2 item.1)) state

private theorem leave_trace (table : Source n) (weights : Channel n → W) (total : W)
    (root owner b : Nat) (target : Channel n) (labels : List (Channel n × Nat))
    (state : ForestWeightedIndexed.State n W) (rest : List (Task n)) :
    Trace table weights total b target ⟨state, .leaveGuards root owner labels :: rest⟩
      ⟨leftGuards weights total root owner b target labels state, rest⟩ (labels.length + 1) ∧
      (leftGuards weights total root owner b target labels state).operations =
        state.operations + labels.length := by
  induction labels generalizing state with
  | nil => exact ⟨Trace.single rfl, by simp [leftGuards]⟩
  | cons item labels ih =>
      let next := emit weights total root b target state (.leave owner item.2 item.1)
      obtain ⟨tail, operations⟩ := ih next
      constructor
      · have first : Trace table weights total b target
            ⟨state, .leaveGuards root owner (item :: labels) :: rest⟩
            ⟨next, .leaveGuards root owner labels :: rest⟩ 1 := Trace.single rfl
        simpa [leftGuards, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using first.append tail
      · change (leftGuards weights total root owner b target labels next).operations = _
        rw [operations]
        have nextOps : next.operations = state.operations + 1 := emit_operations ..
        simp only [List.length_cons]
        omega

/-- The continuation loop realizes the exact recursive selector for every
rank-checked source table. Its control steps are bounded by the indexed
operations already counted by that selector. -/
theorem visit_trace (table : Source n) (weights : Channel n → W) (total : W)
    (root b : Nat) (target : Channel n) (owner : Nat)
    (state : ForestWeightedIndexed.State n W) (rest : List (Task n)) :
    ∃ ticks, Trace table weights total b target ⟨state, .visit root owner :: rest⟩
      ⟨runNode table weights total root b target owner state, rest⟩ ticks ∧
      ticks + 3 * state.operations ≤
        3 * (runNode table weights total root b target owner state).operations := by
  induction owner using Nat.strong_induction_on generalizing state rest with
  | h owner ih =>
      let entered := emit weights total root b target state (.node owner)
      have enteredOps : entered.operations = state.operations + 1 := emit_operations ..
      cases kind : readNode table owner with
      | zero =>
          have result : runNode table weights total root b target owner state = entered := by
            rw [runNode.eq_def, kind]
          rw [result]
          exact ⟨1, Trace.single (by simp [step, kind, entered]), by omega⟩
      | liveAnd first second =>
          have result : runNode table weights total root b target owner state = entered := by
            rw [runNode.eq_def, kind]
          rw [result]
          exact ⟨1, Trace.single (by simp [step, kind, entered]), by omega⟩
      | input head =>
          let final := emit weights total root b target entered (.leaf owner [] head)
          have result : runNode table weights total root b target owner state = final := by
            rw [runNode.eq_def, kind]
          rw [result]
          have first : Trace table weights total b target ⟨state, .visit root owner :: rest⟩
              ⟨entered, .operation root (.leaf owner [] head) :: rest⟩ 1 :=
            Trace.single (by simp [step, kind, entered])
          have last : Trace table weights total b target
              ⟨entered, .operation root (.leaf owner [] head) :: rest⟩ ⟨final, rest⟩ 1 := Trace.single rfl
          have finalOps : final.operations = entered.operations + 1 := emit_operations ..
          exact ⟨2, first.append last, by omega⟩
      | disj children =>
          have result : runNode table weights total root b target owner state =
              childrenResult table weights total root owner b target children 0 entered := by
            rw [runNode.eq_def, kind]
            rfl
          rw [result]
          obtain ⟨ticks, tail, bound⟩ := children_trace table weights total root owner b target
            (fun child current remaining => ih child.val child.isLt current remaining)
            children 0 entered rest
          have first : Trace table weights total b target ⟨state, .visit root owner :: rest⟩
              ⟨entered, .children root owner 0 children :: rest⟩ 1 :=
            Trace.single (by simp [step, kind, entered])
          exact ⟨1 + ticks, first.append tail, by omega⟩
      | guard child labels =>
          let indexed := labels.zipIdx
          let guarded := enteredGuards weights total root owner b target labels 0 entered
          let down := emit weights total root b target guarded (.down owner 0 child.val)
          let visited := runNode table weights total root b target child.val down
          let up := emit weights total root b target visited .up
          let final := leftGuards weights total root owner b target indexed.reverse up
          have result : runNode table weights total root b target owner state = final := by
            rw [runNode.eq_def, kind]
            rfl
          rw [result]
          obtain ⟨enterRun, enterOps⟩ := enter_trace table weights total root owner child.val b target
            labels 0 [] entered rest
          have enters : Trace table weights total b target
              ⟨entered, .enterGuards root owner child.val 0 labels [] :: rest⟩
              ⟨guarded, .enterGuards root owner child.val labels.length [] indexed.reverse :: rest⟩
              labels.length := by
            simpa only [Nat.zero_add, List.append_nil] using enterRun
          obtain ⟨childTicks, childRun, childBound⟩ := ih child.val child.isLt down
            (.operation root .up :: .leaveGuards root owner indexed.reverse :: rest)
          obtain ⟨leaveRun, leaveOps⟩ := leave_trace table weights total root owner b target indexed.reverse up rest
          have first : Trace table weights total b target ⟨state, .visit root owner :: rest⟩
              ⟨entered, .enterGuards root owner child.val 0 labels [] :: rest⟩ 1 :=
            Trace.single (by simp [step, kind, entered])
          have descend : Trace table weights total b target
              ⟨guarded, .enterGuards root owner child.val labels.length [] indexed.reverse :: rest⟩
              ⟨down, .visit root child.val :: .operation root .up :: .leaveGuards root owner indexed.reverse :: rest⟩ 1 :=
            Trace.single rfl
          have ascend : Trace table weights total b target
              ⟨visited, .operation root .up :: .leaveGuards root owner indexed.reverse :: rest⟩
              ⟨up, .leaveGuards root owner indexed.reverse :: rest⟩ 1 := Trace.single rfl
          refine ⟨1 + labels.length + 1 + childTicks + 1 + (indexed.reverse.length + 1),
            ((((first.append enters).append descend).append childRun).append ascend).append leaveRun, ?_⟩
          have downOps : down.operations = guarded.operations + 1 := emit_operations ..
          have upOps : up.operations = visited.operations + 1 := emit_operations ..
          change guarded.operations = entered.operations + labels.length at enterOps
          change final.operations = up.operations + indexed.reverse.length at leaveOps
          change childTicks + 3 * down.operations ≤ 3 * visited.operations at childBound
          have length : indexed.reverse.length = labels.length := by simp [indexed]
          omega

def rootsResult (table : Source n) (weights : Channel n → W) (total : W)
    (b : Nat) (target : Channel n) (roots : List Nat) (position : Nat)
    (state : ForestWeightedIndexed.State n W) : ForestWeightedIndexed.State n W :=
  (roots.zipIdx position).foldl (fun current item =>
    runNode table weights total item.2 b target item.1 (startRoot current)) state

/-- One persistent counter array serves every root occurrence, including
repeated roots. Root dispatch and termination are included in the step count. -/
theorem roots_trace (table : Source n) (weights : Channel n → W) (total : W)
    (b : Nat) (target : Channel n) (roots : List Nat) (position : Nat)
    (state : ForestWeightedIndexed.State n W) (rest : List (Task n)) :
    ∃ ticks, Trace table weights total b target ⟨state, .roots position roots :: rest⟩
      ⟨rootsResult table weights total b target roots position state, rest⟩ ticks ∧
      ticks + 3 * state.operations ≤
        3 * (rootsResult table weights total b target roots position state).operations + roots.length + 1 := by
  induction roots generalizing position state with
  | nil => exact ⟨1, Trace.single rfl, by simp [rootsResult, Nat.add_comm]⟩
  | cons owner roots ih =>
      let started := startRoot state
      let visited := runNode table weights total position b target owner started
      obtain ⟨nodeTicks, nodeRun, nodeBound⟩ := visit_trace table weights total position b target
        owner started (.roots (position + 1) roots :: rest)
      obtain ⟨tailTicks, tailRun, tailBound⟩ := ih (position + 1) visited
      have first : Trace table weights total b target ⟨state, .roots position (owner :: roots) :: rest⟩
          ⟨started, .visit position owner :: .roots (position + 1) roots :: rest⟩ 1 := Trace.single rfl
      refine ⟨1 + nodeTicks + tailTicks, ?_, ?_⟩
      · simpa only [rootsResult, List.zipIdx_cons, List.foldl_cons] using
          (first.append nodeRun).append tailRun
      · have startOps : started.operations = state.operations := rfl
        change nodeTicks + 3 * started.operations ≤ 3 * visited.operations at nodeBound
        change tailTicks + 3 * visited.operations ≤
          3 * (rootsResult table weights total b target roots (position + 1) visited).operations + roots.length + 1 at tailBound
        change 1 + nodeTicks + tailTicks + 3 * state.operations ≤
          3 * (rootsResult table weights total b target roots (position + 1) visited).operations + (owner :: roots).length + 1
        simp only [List.length_cons]
        omega

/-- Fuel is an executable stopping mechanism; the trace below proves that a
source-size bound suffices. Empty control is a terminal configuration. -/
def run (table : Source n) (weights : Channel n → W) (total : W) (b : Nat)
    (target : Channel n) : Nat → Configuration n W → Configuration n W
  | 0, state => state
  | fuel + 1, state => match step table weights total b target state with
      | none => state
      | some next => run table weights total b target fuel next

theorem run_stopped {state : Configuration n W}
    (stopped : step table weights total b target state = none) (fuel : Nat) :
    run table weights total b target fuel state = state := by
  induction fuel with
  | zero => rfl
  | succ fuel => simp only [run, stopped]

theorem Trace.run_of_le {first last : Configuration n W} {ticks : Nat}
    (trace : Trace table weights total b target first last ticks)
    (stopped : ForestSelectionMachine.step table weights total b target last = none)
    (fuel : Nat) (enough : ticks ≤ fuel) : run table weights total b target fuel first = last := by
  induction trace generalizing fuel with
  | refl state => exact run_stopped stopped fuel
  | @step first middle last ticks transition tail ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [run, transition]
          exact ih stopped fuel (by omega)

def initialData : ForestWeightedIndexed.State n W :=
  ⟨Array.replicate n 0, 0, ForestCursorDescriptors.initial, none, 0, n⟩

def initial (roots : List Nat) : Configuration n W := ⟨initialData, [.roots 0 roots]⟩

def totalWeight (weights : Channel n → W) : W :=
  (List.finRange n).foldl (fun value channel => value + weights channel) 0

def fuelBound (graph : DAG n) : Nat :=
  14 * (graph.roots.length + graph.childIncidences + graph.guardIncidences) + 1

/-- Source-list tails are shared references. Guard exit pairs are newly
allocated cells and are counted in addition to each fixed-size control frame. -/
def taskWords : Task n → Nat
  | .enterGuards _ _ _ _ _ seen => 8 + 2 * seen.length
  | .leaveGuards _ _ seen => 8 + 2 * seen.length
  | _ => 8

def liveWords (state : Configuration n W) : Nat :=
  liveCells state.data + (state.tasks.map taskWords).sum

variable [IsOrderedAddMonoid W]

theorem step_liveWords {first last : Configuration n W}
    (transition : step table weights total b target first = some last) :
    liveWords last ≤ liveWords first + 32 := by
  obtain ⟨data, tasks⟩ := first
  cases tasks with
  | nil => simp [step] at transition
  | cons task rest =>
      cases task with
      | visit root owner =>
          have bound := emit_liveCells weights total root b target data (.node owner)
          cases kind : readNode table owner <;>
            simp only [step, kind, Option.some.injEq] at transition <;>
            subst last <;>
            simp only [liveWords, taskWords, List.map_cons, List.sum_cons,
              List.length_nil, Nat.mul_zero, Nat.add_zero] <;> omega
      | operation root operation =>
          have bound := emit_liveCells weights total root b target data operation
          simp only [step, Option.some.injEq] at transition
          subst last
          simp only [liveWords, taskWords, List.map_cons, List.sum_cons]
          omega
      | children root owner position children =>
          cases children with
          | nil =>
              simp only [step, Option.some.injEq] at transition
              subst last
              simp only [liveWords, taskWords, List.map_cons, List.sum_cons]
              omega
          | cons child children =>
              have bound := emit_liveCells weights total root b target data (.down owner position child.val)
              simp only [step, Option.some.injEq] at transition
              subst last
              simp only [liveWords, taskWords, List.map_cons, List.sum_cons]
              omega
      | enterGuards root owner child position labels seen =>
          cases labels with
          | nil =>
              have bound := emit_liveCells weights total root b target data (.down owner 0 child)
              simp only [step, Option.some.injEq] at transition
              subst last
              simp only [liveWords, taskWords, List.map_cons, List.sum_cons]
              omega
          | cons channel labels =>
              have bound := emit_liveCells weights total root b target data (.enter owner position channel)
              simp only [step, Option.some.injEq] at transition
              subst last
              simp only [liveWords, taskWords, List.map_cons, List.sum_cons, List.length_cons]
              omega
      | leaveGuards root owner labels =>
          cases labels with
          | nil =>
              simp only [step, Option.some.injEq] at transition
              subst last
              simp only [liveWords, taskWords, List.map_cons, List.sum_cons, List.length_nil]
              omega
          | cons item labels =>
              obtain ⟨channel, position⟩ := item
              have bound := emit_liveCells weights total root b target data (.leave owner position channel)
              simp only [step, Option.some.injEq] at transition
              subst last
              simp only [liveWords, taskWords, List.map_cons, List.sum_cons, List.length_cons]
              omega
      | roots position roots =>
          cases roots with
          | nil =>
              simp only [step, Option.some.injEq] at transition
              subst last
              simp only [liveWords, taskWords, List.map_cons, List.sum_cons]
              omega
          | cons owner roots =>
              have bound := startRoot_liveCells data
              simp only [step, Option.some.injEq] at transition
              subst last
              simp only [liveWords, taskWords, List.map_cons, List.sum_cons]
              omega

/-- Actual configurations before and after every step are included in the
retained-store maximum. Generic weight bit lengths and the immutable source
table are accounted for separately. -/
inductive SpaceTrace (table : Source n) (weights : Channel n → W) (total : W)
    (b : Nat) (target : Channel n) : Configuration n W → Configuration n W → Nat → Nat → Prop
  | refl (state) : SpaceTrace table weights total b target state state 0 (liveWords state)
  | next {first middle last ticks peak}
      (transition : step table weights total b target first = some middle)
      (tail : SpaceTrace table weights total b target middle last ticks peak) :
      SpaceTrace table weights total b target first last (ticks + 1) (max (liveWords first) peak)

theorem Trace.space {first last : Configuration n W} {ticks : Nat}
    (trace : Trace table weights total b target first last ticks) :
    ∃ peak, SpaceTrace table weights total b target first last ticks peak ∧
      liveWords last ≤ peak ∧ peak ≤ liveWords first + 32 * ticks := by
  induction trace with
  | refl state => exact ⟨_, .refl state, Nat.le_refl _, by simp⟩
  | step transition tail ih =>
      obtain ⟨peak, stored, finalBound, peakBound⟩ := ih
      have localBound := step_liveWords transition
      exact ⟨_, .next transition stored, finalBound.trans (le_max_right _ _),
        max_le (by omega) (by omega)⟩

/-- From a validated decoded source table, one fixed transition function
terminates within a linear clock and returns the original selector's exact
state. Source decoding, counter initialization and cached-weight formation
are represented by their separate preparation interfaces. -/
theorem linear_execution (graph : DAG n) (forest : graph.FormulaForest)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (rootMatches : ForestIndexedOperands.RootsMatch graph roots)
    (weights : Channel n → W) (b : Nat) (target : Channel n) :
    let table := source n rows
    let selected := runAll table weights b target roots
    (∃ ticks, Trace table weights selected.1 b target (initial roots) ⟨selected.2, []⟩ ticks ∧
      ticks ≤ fuelBound graph) ∧
    run table weights selected.1 b target (fuelBound graph) (initial roots) = ⟨selected.2, []⟩ := by
  intro table selected
  obtain ⟨ticks, trace, time⟩ := roots_trace table weights (totalWeight weights) b target roots 0 initialData []
  have result : rootsResult table weights (totalWeight weights) b target roots 0 initialData = selected.2 := rfl
  have total : totalWeight weights = selected.1 := rfl
  rw [result] at trace time
  rw [total] at trace
  have ops := runAll_operations_bound graph forest rows roots matched rootMatches weights b target
  have length : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have clock : ticks ≤ fuelBound graph := by
    change ticks + 3 * 0 ≤ 3 * selected.2.operations + roots.length + 1 at time
    change selected.2.operations ≤ _ at ops
    unfold fuelBound
    omega
  have actual : Trace table weights selected.1 b target (initial roots) ⟨selected.2, []⟩ ticks := trace
  exact ⟨⟨ticks, actual, clock⟩, actual.run_of_le rfl _ clock⟩

/-- Both the live selector records and the live continuation frames have a
linear bound. The initial source table and encoded weight sizes remain inputs. -/
theorem linear_resources (graph : DAG n) (forest : graph.FormulaForest)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (rootMatches : ForestIndexedOperands.RootsMatch graph roots)
    (weights : Channel n → W) (b : Nat) (target : Channel n) :
    let table := source n rows
    let selected := runAll table weights b target roots
    ∃ ticks peak, SpaceTrace table weights selected.1 b target
      (initial roots) ⟨selected.2, []⟩ ticks peak ∧ ticks ≤ fuelBound graph ∧
      peak ≤ n + 17 + 32 * fuelBound graph := by
  intro table selected
  obtain ⟨ticks, trace, time⟩ :=
    (linear_execution graph forest rows roots matched rootMatches weights b target).1
  obtain ⟨peak, stored, _, space⟩ := trace.space
  have initialSize : liveWords (initial (W := W) (n := n) roots) = n + 17 := by
    simp [liveWords, initial, initialData, liveCells, taskWords, ForestCursorDescriptors.initial]
  rw [initialSize] at space
  exact ⟨ticks, peak, stored, time, by omega⟩

/-- The executed continuation loop attains a maximum-weight physical test on
healthy-zero forests. No returned-candidate premise or answer oracle occurs
in the transition function. -/
theorem physical_maximum (graph : DAG n) (forest : graph.FormulaForest)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (rootMatches : ForestIndexedOperands.RootsMatch graph roots)
    (weights : Channel n → W) (nonnegative : ∀ channel, 0 ≤ weights channel)
    (b : Nat) (bridge : Physical.Bridge n) (positive : 0 < b)
    (healthy : ∀ position : Fin graph.roots.length,
      graph.eval (assignmentOfSet {bridge.target}) (graph.roots.get position) = false)
    (detectable : Physical.BridgeDetectable (b := b) bridge true graph.observations) :
    let final := run (source n rows) weights (totalWeight weights) b bridge.target
      (fuelBound graph) (initial roots)
    final.tasks = [] ∧ ∃ candidate K,
      final.data.selected = some candidate ∧ Admissible b bridge.target K ∧
      Physical.BridgeInputDetects bridge true graph.observations
        (Physical.realizeBridge bridge positive K) true ∧
      candidate.score = GenericWeight.total weights K ∧
      ∀ L, Admissible b bridge.target L →
        Physical.BridgeInputDetects bridge true graph.observations
          (Physical.realizeBridge bridge positive L) true →
        GenericWeight.total weights L ≤ GenericWeight.total weights K := by
  intro final
  have executed := (linear_execution graph forest rows roots matched rootMatches weights b bridge.target).2
  change final = ⟨(runAll (source n rows) weights b bridge.target roots).2, []⟩ at executed
  rw [executed]
  exact ⟨rfl, Controller.Optimization.Weights.forest_physical_maximum graph forest rows roots
    matched rootMatches weights nonnegative b bridge positive healthy detectable⟩

end Controller.Cost.ForestSelectionMachine
