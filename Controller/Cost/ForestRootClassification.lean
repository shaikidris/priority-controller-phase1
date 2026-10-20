/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.UniformSourceConstruction
import Controller.Cost.BoundedRun
import Controller.Cost.UniformDAGRuntimeOutputs
import Controller.Cost.ForestRootProjection

/-! Source-driven healthy-root classification before image construction.
A counts-only resident evaluates the original packet and emits its root flags;
the ordered partition consumes those flags, retaining repeated roots. -/
namespace Controller.Cost.ForestRootClassification

open Controller Controller.Decoder Controller.Decoder.DAG
open Controller.Cost Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGRun
open Controller.Cost.ForestRootProjection

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def tailCode (width channels nodes children guards roots : Nat) : GateProgram.Code width :=
  SharedRootLoop.setupCode width (5 + 6 * nodes + children + guards) roots ++
    SharedRootLoop.code width (161 + 2 * channels) (5 + 6 * nodes + children + guards + roots + channels) ++ [.halt]

derive_word_recipe tailCode

def program (width channels nodes children guards roots : Nat) : Program width 4 :=
  (UniformSourceConstruction.code width channels nodes children guards roots ++
    evaluate (fun i => [channels, nodes, children, guards, roots].getD i.val 0)
      (tailCode.constructionRecipe width)).toArray

theorem program_image (width : Nat) (rows : List Row) (roots : List Nat) (values : Assignment n) :
    program width n rows.length (rowChildren rows).length (rowGuards rows).length roots.length =
      UniformDAGRuntimeOutputs.program width n rows roots values := by
  simp only [program, UniformSourceConstruction.code_image width rows roots values,
    tailCode.constructionRecipe_eq, tailCode, UniformDAGRuntimeOutputs.program,
    UniformDAGRuntimeOutputs.code, UniformDAGRuntimeOutputs.rootBase,
    ForestIndexedOperands.cacheHeap_size, packetHeaderHeap_size,
    List.append_assoc]

/-- Includes final program materialization and the scalar tail formation. -/
def constructionWork (width channels : Nat) : Nat :=
  UniformSourceConstruction.work width channels + work (tailCode.constructionRecipe width) +
    (174 + 2 * channels) + 40

theorem construction_bound (width channels : Nat) : constructionWork width channels ≤ 6000 + 26 * channels := by
  have interpreter := UniformSourceConstruction.work_bound width channels
  simp only [constructionWork, tailCode.constructionRecipe_work]
  omega

/-- The flags are produced by actual fetched evaluation of the original source
packet. No graph evaluation appears in the resident constructor's arguments. -/
theorem execution (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (values : Assignment n)
    (width : Nat) (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (suffix output : List (Word width)) (address loaded temporary : Word width) :
    ∃ final ticks peak,
      Execution (program width n rows.length (rowChildren rows).length (rowGuards rows).length roots.length)
        ((ForestCounter.counterState (#[] : Array (Word width)) 0 address loaded temporary).frame
          ((inputPacket n 0 rows roots).map (word width) ++ List.ofFn (fun i => boolWord width (values i)) ++ suffix) output)
        final ticks peak ∧ ticks ≤ 97 * graph.countedSize + 37 ∧
      peak ≤ 8 * graph.countedSize + 14 + suffix.length + output.length ∧
      final.stack = suffix ∧ final.output = ((graph.outputValues values).map (boolWord width)).reverse ++ output ∧
      final.halted = true := by
  rw [program_image width rows roots values]
  exact UniformDAGRuntimeOutputs.execution_at_width graph rows roots matched heads rootMatches values width capacity
    suffix output address loaded temporary

def decodeFlags (output : List (Word width)) : List Bool :=
  output.reverse.map (fun value => value.val != 0)

theorem decoded_flags (values : List Bool) (capacity : 1 < 2 ^ width) :
    decodeFlags ((values.map (boolWord width)).reverse) = values := by
  have bit : ∀ value : Bool, ((boolWord width value).val != 0) = value := by
    intro value
    cases value <;> simp [boolWord, word, Nat.mod_eq_of_lt capacity]
  simp only [decodeFlags, List.reverse_reverse, List.map_map, Function.comp_def, bit]
  exact List.map_id' _

/-- The clock includes one flag read, case split, branch/list update and two
source-list advances at every original root occurrence. -/
def partition : List α → List Bool → List α × List α × Nat
  | root :: roots, flag :: flags =>
      let tail := partition roots flags
      if flag then (tail.1, root :: tail.2.1, tail.2.2 + 6)
      else (root :: tail.1, tail.2.1, tail.2.2 + 6)
  | _, _ => ([], [], 1)

theorem partition_spec (roots : List α) (f : α → β) (predicate : α → Bool) :
    partition (roots.map f) (roots.map predicate) =
      ((roots.filter (fun root => !predicate root)).map f,
        (roots.filter predicate).map f, 6 * roots.length + 1) := by
  induction roots with
  | nil => rfl
  | cons root rest ih =>
      simp only [List.map_cons, partition, ih, List.length_cons]
      cases flag : predicate root <;> simp [flag, Nat.mul_add, Nat.add_assoc]

private theorem filter_positions (roots : List α) (predicate : α → Bool) (f : α → β) :
    ((List.finRange roots.length).filter (fun i => predicate (roots.get i))).map (fun i => f (roots.get i)) =
      (roots.filter predicate).map f := by
  have represented : (List.finRange roots.length).map roots.get = roots := List.map_get_finRange roots
  have same := congrArg (fun items => (items.filter predicate).map f) represented
  simpa only [List.filter_map, List.map_map, Function.comp_def] using same

/-- The partition matches the exact root families consumed by the original
forest resident. The classifier's mathematical evaluator is used only here
as the specification of flags already emitted by its execution. -/
theorem healthy_partition (graph : DAG n) (target : Channel n) (width : Nat) (capacity : 1 < 2 ^ width) :
    partition (graph.roots.map Fin.val)
      (decodeFlags (((graph.outputValues (assignmentOfSet {target})).map (boolWord width)).reverse)) =
      (healthyRootIds graph target false, healthyRootIds graph target true, 6 * graph.roots.length + 1) := by
  rw [decoded_flags _ capacity]
  rw [DAG.outputValues, partition_spec graph.roots Fin.val (graph.eval (assignmentOfSet {target}))]
  unfold healthyRootIds Forest.familyRootIds Forest.healthyPositions
  have zero : ∀ value : Bool, (value == false) = !value := by intro value; cases value <;> rfl
  have one : ∀ value : Bool, (value == true) = value := by intro value; cases value <;> rfl
  simp only [zero, one]
  rw [filter_positions graph.roots (fun root => !graph.eval (assignmentOfSet {target}) root) Fin.val,
    filter_positions graph.roots (graph.eval (assignmentOfSet {target})) Fin.val]

/-- The implementation consumes the interpreter's returned words. Source
counts determine both its instruction image and its finite execution budget. -/
def classify (width channels nodes children guards rootCount : Nat)
    (rawRoots : List Nat) (initial : State width 4) : List Nat × List Nat × Nat :=
  let resident := program width channels nodes children guards rootCount
  let final := BoundedRun.run resident (97 * (channels + nodes + children + guards + rootCount) + 37) initial
  partition rawRoots (decodeFlags final.output)

/-- This data-flow theorem executes the concrete preprocessing driver; the
healthy families do not occur among `classify`'s inputs. -/
theorem classify_correct (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (target : Channel n) (width : Nat)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width) :
    classify width n rows.length (rowChildren rows).length (rowGuards rows).length roots.length roots
      ((ForestCounter.counterState (#[] : Array (Word width)) 0 (word width 0) (word width 0) (word width 0)).frame
        ((inputPacket n 0 rows roots).map (word width) ++
          List.ofFn (fun i => boolWord width (assignmentOfSet {target} i)) ++ []) []) =
      (healthyRootIds graph target false, healthyRootIds graph target true, 6 * graph.roots.length + 1) := by
  obtain ⟨final, ticks, peak, trace, time, space, stack, output, stopped⟩ :=
    execution graph rows roots matched heads rootMatches (assignmentOfSet {target}) width capacity [] []
      (word width 0) (word width 0) (word width 0)
  have rootsLength : roots.length = graph.roots.length := by rw [rootMatches, List.length_map]
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have size : n + rows.length + (rowChildren rows).length + (rowGuards rows).length + roots.length =
      graph.countedSize := by rw [matched.length_eq, children, guards, rootsLength, graph.countedSize_eq]
  dsimp only [classify]
  rw [BoundedRun.of_execution trace stopped _ (by rw [size]; exact time), output]
  simp only [List.append_nil]
  rw [show roots = graph.roots.map Fin.val from rootMatches]
  exact healthy_partition graph target width (by omega)

end Controller.Cost.ForestRootClassification
