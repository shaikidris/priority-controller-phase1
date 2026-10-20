module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Graph.Minor
public import Controller.Graph.NetWidth
public import Controller.Native.Encode
public import Controller.Native.BoundedEncode

@[expose] public section

/-! Complete-bipartite width and native clause graphs. -/
namespace Controller.Graph

namespace TreeDecomposition
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
/-- A deepest highest-occurrence bag contains a vertex and every neighbor.
This gives the minimum-degree lower bound without a Graph Minors theorem. -/
theorem closedNeighborhood_bag (D : TreeDecomposition G) (nonempty : Nonempty V) :
    ∃ v, ∀ u, u = v ∨ G.Adj u v → u ∈ D.bag (D.home v) := by
  obtain ⟨start⟩ := nonempty
  obtain ⟨v, hv⟩ := Finset.univ.exists_maximalFor D.home
    (show (Finset.univ : Finset V).Nonempty from ⟨start, Finset.mem_univ _⟩)
  refine ⟨v, ?_⟩
  intro u h
  rcases h with h | h
  · simpa only [h] using D.home_mem v
  obtain ⟨i, hui, hvi⟩ := D.edge h
  have hu := D.above_home u i hui
  have hv' := D.above_home v i hvi
  have huv : D.home u ≤ D.home v := by
    rcases le_total_of_directed hu hv' with h | h
    · exact hv.2 (Finset.mem_univ _) h
    · exact h
  exact D.interval u i (D.home v) hui huv hv'

end TreeDecomposition

noncomputable def bipartiteBag (n b : ℕ) (index : Fin (b + 1)) :
    Finset (Fin n ⊕ Fin b) := by
  classical
  exact Finset.univ.filter fun v => match v with
    | .inl _ => True
    | .inr j => index.val = j.val + 1

/-- All left vertices in each bag and one right vertex at a time. -/
noncomputable def bipartiteDecomposition (n b : ℕ) :
    TreeDecomposition (completeBipartiteGraph (Fin n) (Fin b)) where
  tree := NetSystem.pathTree b
  finite := inferInstanceAs (Fintype (Fin (b + 1)))
  bag := bipartiteBag n b
  home v := match v with
    | .inl _ => ⟨0, by omega⟩
    | .inr j => ⟨j.val + 1, by omega⟩
  home_mem v := by classical
                   cases v <;> simp [bipartiteBag]
  above_home v i h := by
    classical
    cases v with
    | inl u => change 0 ≤ i.val; omega
    | inr j =>
      change j.val + 1 ≤ i.val
      have : i.val = j.val + 1 := by simpa [bipartiteBag] using h
      omega
  interval v i j hi hj hji := by
    classical
    cases v with
    | inl u => simp [bipartiteBag]
    | inr u =>
      change u.val + 1 ≤ j.val at hj
      change j.val ≤ i.val at hji
      have : i.val = u.val + 1 := by simpa [bipartiteBag] using hi
      simp only [bipartiteBag, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
  edge := by
    classical
    intro u v h
    cases u with
    | inl i =>
      cases v with
      | inl k => simp [completeBipartiteGraph] at h
      | inr j => exact ⟨⟨j.val + 1, by omega⟩, by simp [bipartiteBag],
          by simp [bipartiteBag]⟩
    | inr j =>
      cases v with
      | inr k => simp [completeBipartiteGraph] at h
      | inl i => exact ⟨⟨j.val + 1, by omega⟩, by simp [bipartiteBag],
          by simp [bipartiteBag]⟩

theorem bipartiteDecomposition_capacity (n b : ℕ) :
    (bipartiteDecomposition n b).Capacity (n + 1) := by
  classical
  intro i
  let f : (bipartiteDecomposition n b).bag i → Fin n ⊕ Unit := fun v =>
    match v.val with
    | .inl u => .inl u
    | .inr _ => .inr ()
  have injective : Function.Injective f := by
    intro ⟨u, hu⟩ ⟨v, hv⟩ eq
    apply Subtype.ext
    cases u with
    | inl u =>
      cases v with
      | inl v => simpa [f] using eq
      | inr v => simp [f] at eq
    | inr u =>
      cases v with
      | inl v => simp [f] at eq
      | inr v =>
        have hu : i.val = u.val + 1 := by simpa [bipartiteDecomposition, bipartiteBag] using hu
        have hv : i.val = v.val + 1 := by simpa [bipartiteDecomposition, bipartiteBag] using hv
        exact congrArg Sum.inr (Fin.ext (by omega))
  have bound := Fintype.card_le_of_injective f injective
  simpa only [Fintype.card_coe, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] using bound

private def leftStar (i : Fin n) : Option (Fin b) → Fin n ⊕ Fin b
  | none => .inl i
  | some j => .inr j

private theorem leftStar_injective (i : Fin n) : Function.Injective (leftStar (b := b) i) := by
  intro x y eq
  cases x <;> cases y <;> simp_all [leftStar]

private def rightStar (j : Fin b) : Option (Fin n) → Fin n ⊕ Fin b
  | none => .inr j
  | some i => .inl i

private theorem rightStar_injective (j : Fin b) : Function.Injective (rightStar (n := n) j) := by
  intro x y eq
  cases x <;> cases y <;> simp_all [rightStar]

/-- Every width bound for K_(n,b) is at least min(n,b), including empty sides. -/
theorem completeBipartite_treewidth_lower (n b w : ℕ)
    (bound : TreewidthLE (completeBipartiteGraph (Fin n) (Fin b)) w) :
    min n b ≤ w := by
  classical
  by_cases hn : n = 0
  · simp [hn]
  by_cases hb : b = 0
  · simp [hb]
  obtain ⟨D, capacity⟩ := bound
  have nonempty : Nonempty (Fin n ⊕ Fin b) :=
    ⟨.inl ⟨0, by omega⟩⟩
  obtain ⟨v, contains⟩ := D.closedNeighborhood_bag nonempty
  cases v with
  | inl i =>
    have inside (x : Option (Fin b)) : leftStar i x ∈ D.bag (D.home (.inl i)) := by
      apply contains
      cases x with
      | none => exact Or.inl rfl
      | some j => exact Or.inr (by simp [leftStar, completeBipartiteGraph])
    have count := Fintype.card_le_of_injective
      (fun x => (⟨leftStar i x, inside x⟩ : D.bag (D.home (.inl i))))
      (fun x y eq => leftStar_injective i (congrArg Subtype.val eq))
    rw [Fintype.card_option, Fintype.card_fin, Fintype.card_coe] at count
    have room := capacity (D.home (.inl i))
    have := Nat.min_le_right n b
    omega
  | inr j =>
    have inside (x : Option (Fin n)) : rightStar j x ∈ D.bag (D.home (.inr j)) := by
      apply contains
      cases x with
      | none => exact Or.inl rfl
      | some i => exact Or.inr (by simp [rightStar, completeBipartiteGraph])
    have count := Fintype.card_le_of_injective
      (fun x => (⟨rightStar j x, inside x⟩ : D.bag (D.home (.inr j))))
      (fun x y eq => rightStar_injective j (congrArg Subtype.val eq))
    rw [Fintype.card_option, Fintype.card_fin, Fintype.card_coe] at count
    have room := capacity (D.home (.inr j))
    have := Nat.min_le_left n b
    omega

/-- Exact treewidth formula in the width-at-most vocabulary, also for empty sides. -/
theorem completeBipartite_treewidth_iff (n b w : ℕ) :
    TreewidthLE (completeBipartiteGraph (Fin n) (Fin b)) w ↔ min n b ≤ w := by
  constructor
  · exact completeBipartite_treewidth_lower n b w
  · intro h
    by_cases order : n ≤ b
    · refine ⟨bipartiteDecomposition n b, ?_⟩
      intro i
      exact (bipartiteDecomposition_capacity n b i).trans
        (Nat.add_le_add_right (by simpa [Nat.min_eq_left order] using h) 1)
    · have smaller : b ≤ n := by omega
      let D := bipartiteDecomposition b n
      have edges : ∀ ⦃u v : Fin n ⊕ Fin b⦄,
          (completeBipartiteGraph (Fin n) (Fin b)).Adj u v →
          (completeBipartiteGraph (Fin b) (Fin n)).Adj (Sum.swap u) (Sum.swap v) := by
        intro u v h
        cases u <;> cases v <;> simp_all [completeBipartiteGraph]
      refine ⟨D.comap Sum.swap edges, ?_⟩
      have injective : Function.Injective (Sum.swap : Fin n ⊕ Fin b → Fin b ⊕ Fin n) := by
        intro u v h
        simpa using congrArg Sum.swap h
      have capacity := D.comap_capacity Sum.swap injective edges (b + 1)
        (bipartiteDecomposition_capacity b n)
      intro i
      exact (capacity i).trans
        (Nat.add_le_add_right (by simpa [Nat.min_eq_right smaller] using h) 1)
end Controller.Graph

namespace Controller.Graph

variable {V : Type} [DecidableEq V]

/-- The primal graph of the complete clause list, independent of literal signs. -/
def clausePrimal (clauses : List (Controller.CNF.Clause V)) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ row ∈ clauses, u ∈ row.map Prod.fst ∧ v ∈ row.map Prod.fst
  symm := ⟨by
    intro u v h
    obtain ⟨ne, row, hr, hu, hv⟩ := h
    exact ⟨ne.symm, row, hr, hv, hu⟩⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

omit [DecidableEq V] in
private theorem connected_star {G : SimpleGraph V} (S : Finset V) (hub : V)
    (member : hub ∈ S) (spokes : ∀ x ∈ S, x = hub ∨ G.Adj hub x) :
    ConnectedWithin G S := by
  refine ⟨⟨hub, member⟩, ?_⟩
  have paths (x : V) (hx : x ∈ S) :
      Relation.ReflTransGen (fun u v => u ∈ S ∧ v ∈ S ∧ G.Adj u v) x hub ∧
      Relation.ReflTransGen (fun u v => u ∈ S ∧ v ∈ S ∧ G.Adj u v) hub x := by
    rcases spokes x hx with eq | edge
    · subst x; exact ⟨.refl, .refl⟩
    · exact ⟨.single ⟨hx, member, edge.symm⟩, .single ⟨member, hx, edge⟩⟩
  intro u hu v hv
  exact (paths u hu).1.trans (paths v hv).2

namespace NativeWidth
open Controller.Native
open Controller.Native.Parameters

variable (p : Parameters)

def clauses : List (CNF.Clause (Variable p)) :=
  p.equationClauses ++ p.assertions.map (fun literal => [literal])

def primal : SimpleGraph (Variable p) := clausePrimal (clauses p)

def qualifier (i : Fin p.channels) : Variable p := .internal (.qualifier .faulty i)
def factor (i : Fin p.channels) (j : Fin p.buses) : Variable p :=
  .internal (.qualifierGuard .faulty j i)
def flag (j : Fin p.buses) : Variable p := .internal (.flag .faulty j)

private theorem row_mem {role : Internal p} {row : CNF.Clause (Variable p)}
    (h : row ∈ (p.gate role).clauses (internal p role)) : row ∈ clauses p := by
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨role, p.mem_roles role, h⟩

theorem qualifier_factor_adj (i : Fin p.channels) (j : Fin p.buses) :
    (primal p).Adj (qualifier p i) (factor p i j) := by
  refine ⟨by simp [qualifier, factor], ?_⟩
  refine ⟨[negative (qualifier p i), positive (factor p i j)], ?_, ?_, ?_⟩
  · apply row_mem p (role := .qualifier .faulty i)
    change _ ∈ (CNF.Gate.and _).clauses _
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨internal p (.qualifierGuard .faulty j i), ?_, rfl⟩
    simp [List.mem_map]
  · simp [negative]
  · simp [positive]

theorem factor_flag_adj (i : Fin p.channels) (j : Fin p.buses) :
    (primal p).Adj (factor p i j) (flag p j) := by
  refine ⟨by simp [factor, flag], ?_⟩
  refine ⟨[positive (factor p i j), positive (flag p j)], ?_, ?_, ?_⟩
  · apply row_mem p (role := .qualifierGuard .faulty j i)
    simp [gate, CNF.Gate.clauses, factor, flag, internal, positive, negative, CNF.negate,
      Std.Sat.Literal.negate]
  · simp [positive]
  · simp [positive]

def channelBranch (i : Fin p.channels) : Finset (Variable p) :=
  insert (qualifier p i) (Finset.univ.image (factor p i))

/-- Explicit branch sets in the uncontracted complete native primal graph. -/
def primalMinor : MinorModel (completeBipartiteGraph (Fin p.channels) (Fin p.buses))
    (primal p) where
  branch v := match v with
    | .inl i => channelBranch p i
    | .inr j => {flag p j}
  connected v := by
    cases v with
    | inl i =>
      apply connected_star _ (qualifier p i) (Finset.mem_insert_self _ _)
      intro x hx
      rcases Finset.mem_insert.mp hx with eq | member
      · exact Or.inl eq
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp member
      exact Or.inr (qualifier_factor_adj p i j)
    | inr j =>
      apply connected_star _ (flag p j) (Finset.mem_singleton_self _)
      intro x hx
      exact Or.inl (Finset.mem_singleton.mp hx)
  disjoint := by
    intro u v ne
    cases u <;> cases v <;>
      simp_all [channelBranch, qualifier, factor, flag, Finset.disjoint_left]
    all_goals simp_all [eq_comm]
  edge := by
    intro u v h
    cases u with
    | inl i =>
      cases v with
      | inl k => simp [completeBipartiteGraph] at h
      | inr j => exact ⟨factor p i j, Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩),
          flag p j, Finset.mem_singleton_self _, factor_flag_adj p i j⟩
    | inr j =>
      cases v with
      | inr k => simp [completeBipartiteGraph] at h
      | inl i => exact ⟨flag p j, Finset.mem_singleton_self _, factor p i j,
          Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩),
          (factor_flag_adj p i j).symm⟩

theorem primal_treewidth_lower (w : ℕ) (bound : TreewidthLE (primal p) w) :
    min p.channels p.buses ≤ w :=
  completeBipartite_treewidth_lower _ _ _ ((primalMinor p).treewidth_mono bound)

/-- Every equation row retains its producer and its position in that producer's
complete block. Assertion rows have separate positions. Duplicate rows remain
distinct occurrences. Flattening these blocks is `equationClauses`. -/
abbrev EquationAddress := (role : Internal p) ×
  Fin ((p.gate role).clauses (internal p role)).length

abbrev RowAddress := EquationAddress p ⊕ Fin p.assertions.length
abbrev IncidenceVertex := Variable p ⊕ RowAddress p

def rowClause : RowAddress p → CNF.Clause (Variable p)
  | .inl ⟨role, index⟩ => ((p.gate role).clauses (internal p role))[index.val]
  | .inr index => [p.assertions[index.val]]

def rowAddresses : List (RowAddress p) :=
  (p.roles.flatMap fun role =>
    (List.finRange ((p.gate role).clauses (internal p role)).length).map
      (fun index => Sum.inl ⟨role, index⟩)) ++
    (List.finRange p.assertions.length).map Sum.inr

def rowRole : RowAddress p → Option (Internal p)
  | .inl ⟨role, _⟩ => some role
  | .inr _ => none

theorem mem_rowAddresses (row : RowAddress p) : row ∈ rowAddresses p := by
  cases row with
  | inl row =>
    obtain ⟨role, index⟩ := row
    exact List.mem_append_left _ (List.mem_flatMap.mpr
      ⟨role, p.mem_roles role, List.mem_map.mpr ⟨index, by simp, rfl⟩⟩)
  | inr index =>
    exact List.mem_append_right _ (List.mem_map.mpr ⟨index, by simp, rfl⟩)

/-- Addresses enumerate occurrences once, even when clause contents coincide. -/
theorem rowAddresses_nodup : (rowAddresses p).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨?_, (List.nodup_finRange _).map Sum.inr_injective, ?_⟩
  · apply List.nodup_flatMap.mpr
    constructor
    · intro role _
      apply (List.nodup_finRange _).map
      intro i j h
      simpa using h
    · apply p.roles_nodup.imp
      intro role other ne
      apply List.disjoint_left.mpr
      intro row hrow hother
      obtain ⟨i, _, hi⟩ := List.mem_map.mp hrow
      obtain ⟨j, _, hj⟩ := List.mem_map.mp hother
      have eq := congrArg (rowRole p) (hi.trans hj.symm)
      exact ne (Option.some.inj eq)
  · intro row hrow other hassertion equal
    obtain ⟨role, _, hrole⟩ := List.mem_flatMap.mp hrow
    obtain ⟨index, _, hindex⟩ := List.mem_map.mp hrole
    obtain ⟨assertion, _, heq⟩ := List.mem_map.mp hassertion
    have eq := congrArg (rowRole p) (hindex.trans (equal.trans heq.symm))
    simp [rowRole] at eq

/-- Naming rows by producer and position reproduces the complete clause list. -/
theorem rowAddresses_clauses : (rowAddresses p).map (rowClause p) = clauses p := by
  simp only [rowAddresses, List.map_append, List.map_flatMap, List.map_map,
    Function.comp_def, rowClause, clauses, equationClauses]
  congr 1
  · congr 1
    funext role
    rw [← List.ofFn_eq_map]
    exact List.ofFn_getElem

theorem clauses_specification : CNF.ofClauses (clauses p) = p.specificationFormula := by
  change (⟨(p.equationClauses ++ p.assertions.map (fun literal => [literal])).toArray⟩ :
    CNF.Formula (Variable p)) =
      ⟨p.equationClauses.toArray ++ (p.assertions.map (fun literal => [literal])).toArray⟩
  rw [List.append_toArray]

def incidenceAdj : IncidenceVertex p → IncidenceVertex p → Prop
  | .inl v, .inr row => v ∈ (rowClause p row).map Prod.fst
  | .inr row, .inl v => v ∈ (rowClause p row).map Prod.fst
  | _, _ => False

def incidence : SimpleGraph (IncidenceVertex p) where
  Adj := incidenceAdj p
  symm := ⟨by intro u v h; cases u <;> cases v <;> exact h⟩
  loopless := ⟨by intro v h; cases v <;> exact h⟩

/-- Choose an actual row position, with no clause normalization. -/
def address (role : Internal p) (row : CNF.Clause (Variable p))
    (member : row ∈ (p.gate role).clauses (internal p role)) : EquationAddress p :=
  ⟨role, ⟨((p.gate role).clauses (internal p role)).idxOf row,
    List.idxOf_lt_length_of_mem member⟩⟩

@[simp] theorem rowClause_address (role : Internal p) (row : CNF.Clause (Variable p))
    (member : row ∈ (p.gate role).clauses (internal p role)) :
    rowClause p (.inl (address p role row member)) = row := by
  exact List.getElem_idxOf _

theorem qualifier_row (i : Fin p.channels) (j : Fin p.buses) :
    [negative (qualifier p i), positive (factor p i j)] ∈
      (p.gate (.qualifier .faulty i)).clauses (internal p (.qualifier .faulty i)) := by
  change _ ∈ (CNF.Gate.and _).clauses _
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨internal p (.qualifierGuard .faulty j i), ?_, rfl⟩
  simp [List.mem_map]

theorem factor_row (i : Fin p.channels) (j : Fin p.buses) :
    [positive (factor p i j), positive (flag p j)] ∈
      (p.gate (.qualifierGuard .faulty j i)).clauses
        (internal p (.qualifierGuard .faulty j i)) := by
  simp [gate, CNF.Gate.clauses, factor, flag, internal, positive, negative,
    CNF.negate, Std.Sat.Literal.negate]

def andRow (i : Fin p.channels) (j : Fin p.buses) : IncidenceVertex p :=
  .inr (.inl (address p (.qualifier .faulty i)
    [negative (qualifier p i), positive (factor p i j)] (qualifier_row p i j)))

def orRow (i : Fin p.channels) (j : Fin p.buses) : IncidenceVertex p :=
  .inr (.inl (address p (.qualifierGuard .faulty j i)
    [positive (factor p i j), positive (flag p j)] (factor_row p i j)))

theorem incidence_arm_edges (i : Fin p.channels) (j : Fin p.buses) :
    (incidence p).Adj (.inl (qualifier p i)) (andRow p i j) ∧
    (incidence p).Adj (andRow p i j) (.inl (factor p i j)) ∧
    (incidence p).Adj (.inl (factor p i j)) (orRow p i j) ∧
    (incidence p).Adj (orRow p i j) (.inl (flag p j)) := by
  simp [incidence, incidenceAdj, andRow, orRow, positive, negative]

def incidenceChannelBranch (i : Fin p.channels) : Finset (IncidenceVertex p) :=
  insert (.inl (qualifier p i)) (Finset.univ.biUnion fun j =>
    {andRow p i j, .inl (factor p i j), orRow p i j})

def owner : IncidenceVertex p → Option (Fin p.channels)
  | .inl (.internal (.qualifier _ i)) => some i
  | .inl (.internal (.qualifierGuard _ _ i)) => some i
  | .inr (.inl ⟨.qualifier _ i, _⟩) => some i
  | .inr (.inl ⟨.qualifierGuard _ _ i, _⟩) => some i
  | _ => none

theorem incidence_owner (i : Fin p.channels) {x : IncidenceVertex p}
    (member : x ∈ incidenceChannelBranch p i) : owner p x = some i := by
  rcases Finset.mem_insert.mp member with eq | member
  · subst x; rfl
  obtain ⟨j, _, member⟩ := Finset.mem_biUnion.mp member
  simp only [Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with eq | eq | eq <;> subst x <;> rfl

theorem incidence_arm_mem (i : Fin p.channels) (j : Fin p.buses) :
    andRow p i j ∈ incidenceChannelBranch p i ∧
    (.inl (factor p i j) : IncidenceVertex p) ∈ incidenceChannelBranch p i ∧
    orRow p i j ∈ incidenceChannelBranch p i := by
  have contained : {andRow p i j, (.inl (factor p i j) : IncidenceVertex p), orRow p i j} ⊆
      incidenceChannelBranch p i := by
    intro x hx
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hx⟩)
  exact ⟨contained (by simp), contained (by simp), contained (by simp)⟩

theorem incidence_channel_connected (i : Fin p.channels) :
    ConnectedWithin (incidence p) (incidenceChannelBranch p i) := by
  let S := incidenceChannelBranch p i
  let q : IncidenceVertex p := .inl (qualifier p i)
  let R := fun x y => x ∈ S ∧ y ∈ S ∧ (incidence p).Adj x y
  let : Std.Symm R := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  have qmem : q ∈ S := Finset.mem_insert_self _ _
  have fromHub (x : IncidenceVertex p) (hx : x ∈ S) : Relation.ReflTransGen R q x := by
    rcases Finset.mem_insert.mp hx with eq | member
    · subst x; exact .refl
    obtain ⟨j, _, member⟩ := Finset.mem_biUnion.mp member
    have amem : andRow p i j ∈ S := (incidence_arm_mem p i j).1
    have fmem : (.inl (factor p i j) : IncidenceVertex p) ∈ S :=
      (incidence_arm_mem p i j).2.1
    have omem : orRow p i j ∈ S := (incidence_arm_mem p i j).2.2
    have edges := incidence_arm_edges p i j
    have toAnd : Relation.ReflTransGen R q (andRow p i j) :=
      .single ⟨qmem, amem, edges.1⟩
    have toFactor : Relation.ReflTransGen R q (.inl (factor p i j)) :=
      toAnd.tail ⟨amem, fmem, edges.2.1⟩
    have toOr : Relation.ReflTransGen R q (orRow p i j) :=
      toFactor.tail ⟨fmem, omem, edges.2.2.1⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with eq | eq | eq
    · exact eq.symm ▸ toAnd
    · exact eq.symm ▸ toFactor
    · exact eq.symm ▸ toOr
  refine ⟨⟨q, qmem⟩, ?_⟩
  intro u hu v hv
  exact (symm (fromHub u hu)).trans (fromHub v hv)

/-- Explicit clause-inclusive branches for the native incidence graph. -/
def incidenceMinor : MinorModel (completeBipartiteGraph (Fin p.channels) (Fin p.buses))
    (incidence p) where
  branch v := match v with
    | .inl i => incidenceChannelBranch p i
    | .inr j => {.inl (flag p j)}
  connected v := by
    cases v with
    | inl i => exact incidence_channel_connected p i
    | inr j =>
      apply connected_star (G := incidence p) _
        (Sum.inl (flag p j) : IncidenceVertex p) (Finset.mem_singleton_self _)
      intro x hx
      exact Or.inl (Finset.mem_singleton.mp hx)
  disjoint := by
    intro u v ne
    cases u with
    | inl i =>
      cases v with
      | inl k =>
        apply Finset.disjoint_left.mpr
        intro x hx hy
        have eq := (incidence_owner p i hx).symm.trans (incidence_owner p k hy)
        exact ne (congrArg Sum.inl (Option.some.inj eq))
      | inr j =>
        apply Finset.disjoint_left.mpr
        intro x hx hy
        have eq := incidence_owner p i hx
        have hx : x = .inl (flag p j) := Finset.mem_singleton.mp hy
        simp [hx, owner, flag] at eq
    | inr j =>
      cases v with
      | inl i =>
        apply Finset.disjoint_left.mpr
        intro x hx hy
        have eq := incidence_owner p i hy
        have hx : x = .inl (flag p j) := Finset.mem_singleton.mp hx
        simp [hx, owner, flag] at eq
      | inr k => simp_all [Finset.disjoint_singleton_left, flag]
  edge := by
    intro u v h
    cases u with
    | inl i =>
      cases v with
      | inl k => simp [completeBipartiteGraph] at h
      | inr j =>
        refine ⟨orRow p i j, ?_, .inl (flag p j), Finset.mem_singleton_self _,
          (incidence_arm_edges p i j).2.2.2⟩
        exact (incidence_arm_mem p i j).2.2
    | inr j =>
      cases v with
      | inr k => simp [completeBipartiteGraph] at h
      | inl i =>
        refine ⟨.inl (flag p j), Finset.mem_singleton_self _, orRow p i j, ?_,
          (incidence_arm_edges p i j).2.2.2.symm⟩
        exact (incidence_arm_mem p i j).2.2

theorem incidence_treewidth_lower (w : ℕ) (bound : TreewidthLE (incidence p) w) :
    min p.channels p.buses ≤ w :=
  completeBipartite_treewidth_lower _ _ _ ((incidenceMinor p).treewidth_mono bound)

end NativeWidth
end Controller.Graph

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace Controller.Graph.BoundedNativeWidth

open Controller Controller.Native Controller.Native.Parameters Controller.Native.Bounded

variable (p : Parameters)

/-- The graph is taken from the complete binary-expanded native formula. -/
def clauses : List (CNF.Clause (GlobalVariable p)) := (globalFormula p).clauses.toList

def primal : SimpleGraph (GlobalVariable p) := clausePrimal (clauses p)

def inputs (i : Fin p.channels) : List (CNF.Literal (Variable p)) :=
  enable p i :: (List.finRange p.buses).map (fun j => internal p (.qualifierGuard .faulty j i))

@[simp] theorem inputs_length (i : Fin p.channels) : (inputs p i).length = p.buses + 1 := by
  simp [inputs]

def prefixWire (i : Fin p.channels) (j : Fin p.buses) : GlobalVariable p :=
  localSlots p (.qualifier .faulty i) (by
    change LocalVariable (Variable p) ((inputs p i).length - 2)
    exact (foldOutput (inputs p i) (internal p (.qualifier .faulty i))
      ⟨j.val, by simp only [inputs_length, Nat.add_sub_cancel]; exact j.isLt⟩).1)

def factor (i : Fin p.channels) (j : Fin p.buses) : GlobalVariable p :=
  .original (.internal (.qualifierGuard .faulty j i))

def flag (j : Fin p.buses) : GlobalVariable p := .original (.internal (.flag .faulty j))

def previous (i : Fin p.channels) (j : Fin p.buses) : GlobalVariable p :=
  if first : j.val = 0 then .original (.primary (.enable i))
  else prefixWire p i ⟨j.val - 1, by omega⟩

theorem mapped_foldInputs (i : Fin p.channels) (j : Fin p.buses) :
    (foldInputs (inputs p i) (by simp; have := p.positiveBuses; omega)
      ⟨j.val, by simp only [inputs_length, Nat.add_sub_cancel]; exact j.isLt⟩).map
        (fun literal => (localSlots p (.qualifier .faulty i) literal.1, literal.2)) =
      [(previous p i j, true), (factor p i j, true)] := by
  simp only [foldInputs, inputs, List.length_cons,
    List.map_cons, List.map_nil, originalLiteral, List.get_eq_getElem,
    List.getElem_cons_succ, List.getElem_map, List.getElem_finRange]
  by_cases first : j.val = 0
  · simp [first, previous, localSlots, enable, internal, positive, factor, Fin.ext_iff]
  · have earlier : j.val - 1 < p.buses - 1 := by omega
    simp [first, previous, prefixWire, foldOutput, inputs, localSlots, internal, positive, factor, earlier]
    rfl

theorem local_row_mem (owner : Internal p)
    (row : CNF.Clause (LocalVariable (Variable p) (auxiliaryCount (p.gate owner))))
    (member : row ∈ rows (internal p owner) (p.gate owner)) :
    row.map (fun literal => (localSlots p owner literal.1, literal.2)) ∈ clauses p := by
  have localMember : row.map (fun literal => (localSlots p owner literal.1, literal.2)) ∈
      (producerFormula p owner).clauses.toList := by
    change _ ∈ ((rows (internal p owner) (p.gate owner)).toArray.map
      (Controller.CNF.OrderedFormula.Clause.relabel (localSlots p owner))).toList
    simp only [Array.toList_map]
    exact List.mem_map.mpr ⟨row, member, rfl⟩
  have inEquations : ∀ owners : List (Internal p), owner ∈ owners →
      row.map (fun literal => (localSlots p owner literal.1, literal.2)) ∈
        (owners.foldr (fun role suffix => producerFormula p role ++ suffix)
          Controller.CNF.OrderedFormula.empty).clauses.toList := by
    intro owners
    induction owners with
    | nil => simp
    | cons head tail ih =>
      intro occurs
      change _ ∈ ((producerFormula p head).clauses ++ _).toList
      rw [Array.toList_append]
      rcases List.mem_cons.mp occurs with same | later
      · subst head; exact List.mem_append_left _ localMember
      · exact List.mem_append_right _ (ih later)
  change _ ∈ ((globalEquationFormula p).clauses ++ _).toList
  rw [Array.toList_append]
  exact List.mem_append_left _ (inEquations p.roles (p.mem_roles owner))

/-- Each binary qualifier producer joins its output to either of its inputs. -/
theorem qualifier_link_row (i : Fin p.channels) (j : Fin p.buses)
    (input : GlobalVariable p) (member : input = previous p i j ∨ input = factor p i j) :
    [(prefixWire p i j, false), (input, true)] ∈ clauses p := by
  let output := foldOutput (inputs p i) (internal p (.qualifier .faulty i))
    ⟨j.val, by simp only [inputs_length, Nat.add_sub_cancel]; exact j.isLt⟩
  let arguments := foldInputs (inputs p i) (by simp; have := p.positiveBuses; omega)
    ⟨j.val, by simp only [inputs_length, Nat.add_sub_cancel]; exact j.isLt⟩
  have argumentsMap := mapped_foldInputs p i j
  have inputMember : (input, true) ∈ arguments.map
      (fun literal => (localSlots p (.qualifier .faulty i) literal.1, literal.2)) := by
    rw [argumentsMap]
    rcases member with rfl | rfl <;> simp
  obtain ⟨literal, literalMember, same⟩ := List.mem_map.mp inputMember
  have producerMember : (⟨output, .and arguments⟩ : Producer _) ∈
      expand (internal p (.qualifier .faulty i)) (p.gate (.qualifier .faulty i)) := by
    change _ ∈ foldProducers .conjunction (inputs p i) (internal p (.qualifier .faulty i))
    rw [foldProducers]
    simp only [inputs_length]
    have positive := p.positiveBuses
    simp only [show p.buses + 1 ≠ 0 by omega, show p.buses + 1 ≠ 1 by omega,
      dite_false]
    exact List.mem_map.mpr ⟨⟨j.val, by simp only [inputs_length, Nat.add_sub_cancel]; exact j.isLt⟩, by simp, rfl⟩
  have rowMember : [CNF.negate output, literal] ∈
      (⟨output, .and arguments⟩ : Producer _).rows := by
    change _ ∈ (CNF.Gate.and arguments).clauses output
    exact List.mem_append_left _ (List.mem_map.mpr ⟨literal, literalMember, rfl⟩)
  have allRows := local_row_mem p (.qualifier .faulty i) _
    (List.mem_flatMap.mpr ⟨_, producerMember, rowMember⟩)
  have outputPhase : output.2 = true := by
    dsimp [output, foldOutput]
    split <;> rfl
  have mappedNegative : (localSlots p (.qualifier .faulty i) (CNF.negate output).1,
      (CNF.negate output).2) = (prefixWire p i j, false) := by
    change (localSlots p (.qualifier .faulty i) output.1, !output.2) = _
    rw [outputPhase]
    rfl
  change [(localSlots p (.qualifier .faulty i) (CNF.negate output).1, (CNF.negate output).2),
    (localSlots p (.qualifier .faulty i) literal.1, literal.2)] ∈ clauses p at allRows
  rw [mappedNegative, same] at allRows
  exact allRows

def channelBranch (i : Fin p.channels) : Finset (GlobalVariable p) :=
  insert (.original (.primary (.enable i)))
    ((Finset.univ.image (prefixWire p i)) ∪ Finset.univ.image (factor p i))

theorem prefix_mem (i : Fin p.channels) (j : Fin p.buses) :
    prefixWire p i j ∈ channelBranch p i := by simp [channelBranch]

theorem factor_mem (i : Fin p.channels) (j : Fin p.buses) :
    factor p i j ∈ channelBranch p i := by simp [channelBranch]

theorem previous_mem (i : Fin p.channels) (j : Fin p.buses) :
    previous p i j ∈ channelBranch p i := by
  unfold previous
  split
  · exact Finset.mem_insert_self _ _
  · exact prefix_mem p i _

def owner : GlobalVariable p → Option (Fin p.channels)
  | .original (.primary (.enable i)) => some i
  | .original (.internal (.qualifier _ i)) => some i
  | .original (.internal (.qualifierGuard _ _ i)) => some i
  | .auxiliary (.qualifier _ i) _ => some i
  | _ => none

theorem prefix_owner (i : Fin p.channels) (j : Fin p.buses) :
    owner p (prefixWire p i j) = some i := by
  unfold prefixWire foldOutput
  split <;> rfl

theorem channel_owner (i : Fin p.channels) (x : GlobalVariable p)
    (member : x ∈ channelBranch p i) : owner p x = some i := by
  rcases Finset.mem_insert.mp member with rfl | member
  · rfl
  rcases Finset.mem_union.mp member with member | member
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp member
    exact prefix_owner p i j
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp member
    rfl

theorem row_path (S : Finset (GlobalVariable p)) (x y : GlobalVariable p)
    (hx : x ∈ S) (hy : y ∈ S) (row : CNF.Clause (GlobalVariable p))
    (member : row ∈ clauses p) (inX : x ∈ row.map Prod.fst) (inY : y ∈ row.map Prod.fst) :
    Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ (primal p).Adj a b) x y := by
  by_cases equal : x = y
  · subst y; exact .refl
  · exact .single ⟨hx, hy, equal, row, member, inX, inY⟩

theorem channel_connected (i : Fin p.channels) : ConnectedWithin (primal p) (channelBranch p i) := by
  let S := channelBranch p i
  let hub : GlobalVariable p := .original (.primary (.enable i))
  let R := fun a b => a ∈ S ∧ b ∈ S ∧ (primal p).Adj a b
  let : Std.Symm R := ⟨fun _ _ edge => ⟨edge.2.1, edge.1, edge.2.2.symm⟩⟩
  have hubMem : hub ∈ S := Finset.mem_insert_self _ _
  have prefixPath : ∀ k (below : k < p.buses),
      Relation.ReflTransGen R hub (prefixWire p i ⟨k, below⟩) := by
    intro k
    induction k with
    | zero =>
      intro below
      have row := qualifier_link_row p i ⟨0, below⟩ hub (Or.inl (by simp [hub, previous]))
      exact row_path p S hub _ hubMem (prefix_mem p i _) _ row (by simp) (by simp)
    | succ k ih =>
      intro below
      have previousEq : previous p i ⟨k + 1, below⟩ = prefixWire p i ⟨k, by omega⟩ := by
        simp [previous]
      have row := qualifier_link_row p i ⟨k + 1, below⟩ _ (Or.inl previousEq.symm)
      exact (ih (by omega)).trans
        (row_path p S _ _ (prefix_mem p i _) (prefix_mem p i _) _ row (by simp) (by simp))
  have factorPath (j : Fin p.buses) : Relation.ReflTransGen R hub (factor p i j) := by
    have row := qualifier_link_row p i j _ (Or.inr rfl)
    exact (prefixPath j.val j.isLt).trans
      (row_path p S _ _ (prefix_mem p i _) (factor_mem p i j) _ row (by simp) (by simp))
  have fromHub (x : GlobalVariable p) (member : x ∈ S) : Relation.ReflTransGen R hub x := by
    rcases Finset.mem_insert.mp member with rfl | member
    · exact .refl
    rcases Finset.mem_union.mp member with member | member
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp member
      exact prefixPath j.val j.isLt
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp member
      exact factorPath j
  refine ⟨⟨hub, hubMem⟩, ?_⟩
  intro x hx y hy
  exact (symm (fromHub x hx)).trans (fromHub y hy)

theorem factor_flag_row (i : Fin p.channels) (j : Fin p.buses) :
    [(factor p i j, true), (flag p j, true)] ∈ clauses p := by
  let role : Internal p := .qualifierGuard .faulty j i
  let localRow : CNF.Clause (LocalVariable (Variable p) (auxiliaryCount (p.gate role))) :=
    [(.original (.internal role), true), (.original (.internal (.flag .faulty j)), true)]
  have localMember : localRow ∈ rows (internal p role) (p.gate role) := by
    change localRow ∈ localRow :: _
    exact List.mem_cons_self
  simpa [localRow, localSlots, factor, flag, role] using local_row_mem p role localRow localMember

theorem factor_flag_adj (i : Fin p.channels) (j : Fin p.buses) :
    (primal p).Adj (factor p i j) (flag p j) := by
  exact ⟨by simp [factor, flag], _, factor_flag_row p i j, by simp, by simp⟩

/-- The actual binary prefix wires give the required channel branches. -/
def primalMinor : MinorModel (completeBipartiteGraph (Fin p.channels) (Fin p.buses))
    (primal p) where
  branch vertex := match vertex with
    | .inl i => channelBranch p i
    | .inr j => {flag p j}
  connected vertex := by
    cases vertex with
    | inl i => exact channel_connected p i
    | inr j =>
      refine ⟨Finset.singleton_nonempty _, ?_⟩
      intro x hx y hy
      have same : x = y := (Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm
      subst y
      exact .refl
  disjoint := by
    intro x y different
    apply Finset.disjoint_left.mpr
    intro v hx hy
    cases x with
    | inl i =>
      cases y with
      | inl k =>
        have equal := (channel_owner p i v hx).symm.trans (channel_owner p k v hy)
        exact different (congrArg Sum.inl (Option.some.inj equal))
      | inr j =>
        have same := Finset.mem_singleton.mp hy
        have contradiction := channel_owner p i v hx
        rw [same] at contradiction
        cases contradiction
    | inr j =>
      cases y with
      | inl i =>
        have same := Finset.mem_singleton.mp hx
        have contradiction := channel_owner p i v hy
        rw [same] at contradiction
        cases contradiction
      | inr k =>
        have same := (Finset.mem_singleton.mp hx).symm.trans (Finset.mem_singleton.mp hy)
        have equal : j = k := by simpa [flag] using same
        exact different (congrArg Sum.inr equal)
  edge := by
    intro x y adjacent
    cases x with
    | inl i =>
      cases y with
      | inl k => simp [completeBipartiteGraph] at adjacent
      | inr j => exact ⟨factor p i j, factor_mem p i j,
          flag p j, Finset.mem_singleton_self _, factor_flag_adj p i j⟩
    | inr j =>
      cases y with
      | inr k => simp [completeBipartiteGraph] at adjacent
      | inl i => exact ⟨flag p j, Finset.mem_singleton_self _,
          factor p i j, factor_mem p i j, (factor_flag_adj p i j).symm⟩

/-- The complete bounded-gate native CNF has treewidth at least min(n,b). -/
theorem primal_treewidth_lower (w : Nat) (bound : TreewidthLE (primal p) w) :
    min p.channels p.buses ≤ w :=
  completeBipartite_treewidth_lower _ _ _ ((primalMinor p).treewidth_mono bound)

abbrev RowAddress := Fin (clauses p).length
abbrev IncidenceVertex := GlobalVariable p ⊕ RowAddress p

def rowClause (address : RowAddress p) : CNF.Clause (GlobalVariable p) := (clauses p)[address.val]

def incidenceAdj : IncidenceVertex p → IncidenceVertex p → Prop
  | .inl x, .inr address => x ∈ (rowClause p address).map Prod.fst
  | .inr address, .inl x => x ∈ (rowClause p address).map Prod.fst
  | _, _ => False

def incidence : SimpleGraph (IncidenceVertex p) where
  Adj := incidenceAdj p
  symm := ⟨by intro x y edge; cases x <;> cases y <;> exact edge⟩
  loopless := ⟨by intro x edge; cases x <;> exact edge⟩

def rowVertex (row : CNF.Clause (GlobalVariable p)) (member : row ∈ clauses p) : IncidenceVertex p :=
  .inr ⟨(clauses p).idxOf row, List.idxOf_lt_length_of_mem member⟩

@[simp] theorem rowVertex_clause (row : CNF.Clause (GlobalVariable p)) (member : row ∈ clauses p) :
    rowClause p ⟨(clauses p).idxOf row, List.idxOf_lt_length_of_mem member⟩ = row :=
  List.getElem_idxOf _

@[simp] theorem rowVertex_adj_left (row : CNF.Clause (GlobalVariable p))
    (member : row ∈ clauses p) (x : GlobalVariable p) :
    (incidence p).Adj (.inl x) (rowVertex p row member) ↔ x ∈ row.map Prod.fst := by
  change x ∈ (rowClause p _).map Prod.fst ↔ _
  rw [rowVertex_clause p row member]

@[simp] theorem rowVertex_adj_right (row : CNF.Clause (GlobalVariable p))
    (member : row ∈ clauses p) (x : GlobalVariable p) :
    (incidence p).Adj (rowVertex p row member) (.inl x) ↔ x ∈ row.map Prod.fst := by
  change x ∈ (rowClause p _).map Prod.fst ↔ _
  rw [rowVertex_clause p row member]

def previousRow (i : Fin p.channels) (j : Fin p.buses) : IncidenceVertex p :=
  rowVertex p [(prefixWire p i j, false), (previous p i j, true)]
    (qualifier_link_row p i j _ (Or.inl rfl))

def factorRow (i : Fin p.channels) (j : Fin p.buses) : IncidenceVertex p :=
  rowVertex p [(prefixWire p i j, false), (factor p i j, true)]
    (qualifier_link_row p i j _ (Or.inr rfl))

def flagRow (i : Fin p.channels) (j : Fin p.buses) : IncidenceVertex p :=
  rowVertex p [(factor p i j, true), (flag p j, true)] (factor_flag_row p i j)

def incidenceChannelBranch (i : Fin p.channels) : Finset (IncidenceVertex p) :=
  (channelBranch p i).image Sum.inl ∪
    Finset.univ.biUnion (fun j => {previousRow p i j, factorRow p i j, flagRow p i j})

def incidenceOwner : IncidenceVertex p → Option (Fin p.channels)
  | .inl x => owner p x
  | .inr address => (rowClause p address).head?.bind (fun literal => owner p literal.1)

@[simp] theorem incidenceOwner_rowVertex (row : CNF.Clause (GlobalVariable p))
    (member : row ∈ clauses p) : incidenceOwner p (rowVertex p row member) =
      row.head?.bind (fun literal => owner p literal.1) := by
  change (rowClause p _).head?.bind _ = _
  rw [rowVertex_clause p row member]

theorem incidence_variable_mem (i : Fin p.channels) (x : GlobalVariable p)
    (member : x ∈ channelBranch p i) : (.inl x : IncidenceVertex p) ∈ incidenceChannelBranch p i :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, member, rfl⟩)

theorem incidence_rows_mem (i : Fin p.channels) (j : Fin p.buses) :
    previousRow p i j ∈ incidenceChannelBranch p i ∧
    factorRow p i j ∈ incidenceChannelBranch p i ∧
    flagRow p i j ∈ incidenceChannelBranch p i := by
  have contains (x : IncidenceVertex p) (member : x ∈ {previousRow p i j, factorRow p i j, flagRow p i j}) :
      x ∈ incidenceChannelBranch p i :=
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, member⟩)
  exact ⟨contains _ (by simp), contains _ (by simp), contains _ (by simp)⟩

theorem incidence_channel_owner (i : Fin p.channels) (x : IncidenceVertex p)
    (member : x ∈ incidenceChannelBranch p i) : incidenceOwner p x = some i := by
  rcases Finset.mem_union.mp member with storedVariable | row
  · obtain ⟨v, sourceMember, same⟩ := Finset.mem_image.mp storedVariable
    subst x
    exact channel_owner p i v sourceMember
  · obtain ⟨j, _, member⟩ := Finset.mem_biUnion.mp row
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl
    · simp [previousRow, prefix_owner]
    · simp [factorRow, prefix_owner]
    · simp [flagRow, factor, owner]

theorem incidence_channel_connected (i : Fin p.channels) :
    ConnectedWithin (incidence p) (incidenceChannelBranch p i) := by
  let S := incidenceChannelBranch p i
  let hub : IncidenceVertex p := .inl (.original (.primary (.enable i)))
  let R := fun x y => x ∈ S ∧ y ∈ S ∧ (incidence p).Adj x y
  let : Std.Symm R := ⟨fun _ _ edge => ⟨edge.2.1, edge.1, edge.2.2.symm⟩⟩
  have hubMem : hub ∈ S := incidence_variable_mem p i _ (Finset.mem_insert_self _ _)
  have previousEdges (j : Fin p.buses) :
      (incidence p).Adj (.inl (previous p i j)) (previousRow p i j) ∧
      (incidence p).Adj (previousRow p i j) (.inl (prefixWire p i j)) := by
    simp [previousRow]
  have factorEdges (j : Fin p.buses) :
      (incidence p).Adj (.inl (prefixWire p i j)) (factorRow p i j) ∧
      (incidence p).Adj (factorRow p i j) (.inl (factor p i j)) := by
    simp [factorRow]
  have flagEdges (j : Fin p.buses) :
      (incidence p).Adj (.inl (factor p i j)) (flagRow p i j) := by
    simp [flagRow]
  have prefixPath : ∀ k (below : k < p.buses),
      Relation.ReflTransGen R hub (.inl (prefixWire p i ⟨k, below⟩)) := by
    intro k
    induction k with
    | zero =>
      intro below
      have edge := previousEdges ⟨0, below⟩
      have first : previous p i ⟨0, below⟩ = .original (.primary (.enable i)) := by simp [previous]
      rw [first] at edge
      exact (Relation.ReflTransGen.single
        (r := R) ⟨hubMem, (incidence_rows_mem p i _).1, edge.1⟩).tail
        ⟨(incidence_rows_mem p i _).1, incidence_variable_mem p i _ (prefix_mem p i _), edge.2⟩
    | succ k ih =>
      intro below
      have edge := previousEdges ⟨k + 1, below⟩
      have previousEq : previous p i ⟨k + 1, below⟩ = prefixWire p i ⟨k, by omega⟩ := by simp [previous]
      rw [previousEq] at edge
      exact ((ih (by omega)).tail
        ⟨incidence_variable_mem p i _ (prefix_mem p i _), (incidence_rows_mem p i _).1, edge.1⟩).tail
        ⟨(incidence_rows_mem p i _).1, incidence_variable_mem p i _ (prefix_mem p i _), edge.2⟩
  have factorPath (j : Fin p.buses) : Relation.ReflTransGen R hub (.inl (factor p i j)) :=
    ((prefixPath j.val j.isLt).tail
      ⟨incidence_variable_mem p i _ (prefix_mem p i j), (incidence_rows_mem p i j).2.1,
        (factorEdges j).1⟩).tail
      ⟨(incidence_rows_mem p i j).2.1, incidence_variable_mem p i _ (factor_mem p i j), (factorEdges j).2⟩
  have fromHub (x : IncidenceVertex p) (member : x ∈ S) : Relation.ReflTransGen R hub x := by
    rcases Finset.mem_union.mp member with storedVariable | row
    · obtain ⟨v, sourceMember, same⟩ := Finset.mem_image.mp storedVariable
      subst x
      rcases Finset.mem_insert.mp sourceMember with rfl | sourceMember
      · exact .refl
      rcases Finset.mem_union.mp sourceMember with prefixMember | factorMember
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp prefixMember
        exact prefixPath j.val j.isLt
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp factorMember
        exact factorPath j
    · obtain ⟨j, _, member⟩ := Finset.mem_biUnion.mp row
      simp only [Finset.mem_insert, Finset.mem_singleton] at member
      rcases member with rfl | rfl | rfl
      · exact (prefixPath j.val j.isLt).tail
          ⟨incidence_variable_mem p i _ (prefix_mem p i j), (incidence_rows_mem p i j).1,
            (previousEdges j).2.symm⟩
      · exact (prefixPath j.val j.isLt).tail
          ⟨incidence_variable_mem p i _ (prefix_mem p i j), (incidence_rows_mem p i j).2.1,
            (factorEdges j).1⟩
      · exact (factorPath j).tail
          ⟨incidence_variable_mem p i _ (factor_mem p i j), (incidence_rows_mem p i j).2.2, flagEdges j⟩
  refine ⟨⟨hub, hubMem⟩, ?_⟩
  intro x hx y hy
  exact (symm (fromHub x hx)).trans (fromHub y hy)

def incidenceMinor : MinorModel (completeBipartiteGraph (Fin p.channels) (Fin p.buses))
    (incidence p) where
  branch vertex := match vertex with
    | .inl i => incidenceChannelBranch p i
    | .inr j => {.inl (flag p j)}
  connected vertex := by
    cases vertex with
    | inl i => exact incidence_channel_connected p i
    | inr j =>
      refine ⟨Finset.singleton_nonempty _, ?_⟩
      intro x hx y hy
      have same := (Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm
      subst y
      exact .refl
  disjoint := by
    intro x y different
    apply Finset.disjoint_left.mpr
    intro v hx hy
    cases x with
    | inl i =>
      cases y with
      | inl k =>
        have equal := (incidence_channel_owner p i v hx).symm.trans (incidence_channel_owner p k v hy)
        exact different (congrArg Sum.inl (Option.some.inj equal))
      | inr j =>
        have contradiction := incidence_channel_owner p i v hx
        rw [Finset.mem_singleton.mp hy] at contradiction
        cases contradiction
    | inr j =>
      cases y with
      | inl i =>
        have contradiction := incidence_channel_owner p i v hy
        rw [Finset.mem_singleton.mp hx] at contradiction
        cases contradiction
      | inr k =>
        have same := (Finset.mem_singleton.mp hx).symm.trans (Finset.mem_singleton.mp hy)
        have equal : j = k := by simpa [flag] using same
        exact different (congrArg Sum.inr equal)
  edge := by
    have edge (i : Fin p.channels) (j : Fin p.buses) :
        (incidence p).Adj (flagRow p i j) (.inl (flag p j)) := by
      simp [flagRow]
    intro x y adjacent
    cases x with
    | inl i =>
      cases y with
      | inl k => simp [completeBipartiteGraph] at adjacent
      | inr j => exact ⟨flagRow p i j, (incidence_rows_mem p i j).2.2,
          .inl (flag p j), Finset.mem_singleton_self _, edge i j⟩
    | inr j =>
      cases y with
      | inr k => simp [completeBipartiteGraph] at adjacent
      | inl i => exact ⟨.inl (flag p j), Finset.mem_singleton_self _,
          flagRow p i j, (incidence_rows_mem p i j).2.2, (edge i j).symm⟩

/-- Row occurrences, including repeated clauses, are vertices of this graph. -/
theorem incidence_treewidth_lower (w : Nat) (bound : TreewidthLE (incidence p) w) :
    min p.channels p.buses ≤ w :=
  completeBipartite_treewidth_lower _ _ _ ((incidenceMinor p).treewidth_mono bound)


end Controller.Graph.BoundedNativeWidth
