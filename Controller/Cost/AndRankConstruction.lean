module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Extensions.ResolvedSourcePlan
public import Controller.Cost.ForestCompilerOffsets

@[expose] public section


/-! Dense selector ranks are assigned once in occurrence order. The resulting
word vector supports constant-time rank reads during query construction. -/
namespace Controller.Cost.AndRankConstruction

open Controller.Decoder Controller.Decoder.DAG Controller.Extensions.BoundedAnd

variable {size : Nat}

def run (indices : List (Fin size)) (next : Nat) (table : Vector Nat size) : Vector Nat size :=
  match indices with
  | [] => table
  | index :: rest => run rest (next + 1) (table.set index next)

theorem untouched (indices : List (Fin size)) (next : Nat) (table : Vector Nat size)
    (index : Fin size) (absent : index ∉ indices) : (run indices next table)[index.val] = table[index.val] := by
  induction indices generalizing next table with
  | nil => rfl
  | cons head rest ih =>
      have different : index ≠ head := by intro same; apply absent; simp [same]
      have missing : index ∉ rest := fun member => absent (List.mem_cons_of_mem head member)
      simp only [run, ih (next + 1) (table.set head next) missing]
      exact Vector.getElem_set_ne head.isLt index.isLt (fun same => different (Fin.ext same.symm))

theorem lookup (indices : List (Fin size)) (distinct : indices.Nodup) (next : Nat) (table : Vector Nat size)
    (index : Fin size) (member : index ∈ indices) :
    (run indices next table)[index.val] = next + indices.idxOf index := by
  induction indices generalizing next table with
  | nil => simp at member
  | cons head rest ih =>
      have nodup := List.nodup_cons.mp distinct
      by_cases same : index = head
      · subst index
        rw [run, untouched rest (next + 1) (table.set head next) head nodup.1]
        simp
      · have present : index ∈ rest := (List.mem_cons.mp member).resolve_left same
        rw [run, ih nodup.2 (next + 1) (table.set head next) present]
        simp [List.idxOf_cons, Ne.symm same, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def build (graph : DAG n) : Vector Nat graph.nodeCount :=
  run (andIdentities graph) 0 (Vector.replicate graph.nodeCount 0)

theorem build_rank (graph : DAG n) (index : Fin graph.nodeCount)
    (live : (graph.node index).isLiveAnd = true) :
    (build graph)[index.val] = Controller.Extensions.ResolvedSourcePlan.rank graph index := by
  have member : index ∈ andIdentities graph := by simp [andIdentities, live]
  have distinct : (andIdentities graph).Nodup := (List.nodup_finRange _).filter _
  simpa only [build, Controller.Extensions.ResolvedSourcePlan.rank, Nat.zero_add] using
    lookup (andIdentities graph) distinct 0 (Vector.replicate graph.nodeCount 0) index member

inductive Trace : List (Fin size) → Nat → Vector Nat size → Vector Nat size → Nat → Prop
  | nil (next table) : Trace [] next table table 0
  | cons (index rest next table final ticks)
      (tail : Trace rest (next + 1) (table.set index next) final ticks) :
      Trace (index :: rest) next table final (ticks + 8)

theorem complete (indices : List (Fin size)) (next : Nat) (table : Vector Nat size) :
    Trace indices next table (run indices next table) (8 * indices.length) := by
  induction indices generalizing next table with
  | nil => exact .nil next table
  | cons index rest ih =>
      simpa only [List.length_cons, Nat.mul_add, Nat.mul_one] using .cons index rest next table _ _
        (ih (next + 1) (table.set index next))

end Controller.Cost.AndRankConstruction
