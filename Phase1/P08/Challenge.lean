module
public meta import Lean.Elab.Command
public meta import Lean.Meta.Match.Match
meta import all Lean.Meta.Match.Match
public meta import Lean.Meta.Tactic.AuxLemma
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.List.Count
public import Mathlib.Data.List.Dedup
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Forall2
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.WellFounded
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto
public import Std.Sat.CNF
public import Std.Tactic.BVDecide.LRAT.Checker
open Lean Elab Command in
elab "source_context " source:str : command => do
  let root := (← getOptions).get `sourceContextRoot ""
  if root.isEmpty then
    let original := (← getEnv).mainModule
    modifyScope fun scope => { scope with opts := scope.opts.set `sourceContextRoot original.toString }
  modifyEnv fun env =>
    let env := env.setMainModule source.getString.toName
    let env := Meta.auxLemmasExt.setState env {}
    (private_decl% Lean.Meta.Match.matcherExt).setState env {}
open Lean Elab Command in
elab "end_source_context" : command => do
  let root := (← getOptions).get `sourceContextRoot ""
  if root.isEmpty then throwError "missing original Challenge module"
  modifyEnv (·.setMainModule root.toName)
@[expose] public section
/-!
# Observation projection, producer recovery and typed certificates
The grammar, state transitions, resource measures and mathematical predicates
are explicit. The statements retain their explicit grammar, candidate and acceptance premises.
-/
source_context "Controller.CNF.Basic" namespace Controller.CNF
abbrev Literal (α : Type*) := Std.Sat.Literal α
abbrev OrderedFormula.Clause (α : Type u) : Type u := List (Literal α)
structure OrderedFormula (α : Type u) where
  (clauses : Array (OrderedFormula.Clause α))
namespace OrderedFormula
def Clause.eval (a : α → Bool) (c : Clause α) : Bool := c.any fun (i, n) => a i == n
def eval (a : α → Bool) (f : OrderedFormula α) : Bool := f.clauses.all fun c => c.eval a
def append (left right : OrderedFormula α) : OrderedFormula α := ⟨left.clauses ++ right.clauses⟩
instance : Append (OrderedFormula α) := ⟨append⟩
def Clause.relabel (r : α → β) (c : Clause α) : Clause β := c.map (fun (i, n) => (r i, n))
def relabel (r : α → β) (f : OrderedFormula α) : OrderedFormula β := ⟨f.clauses.map (Clause.relabel r)⟩
def toStd (f : OrderedFormula α) : Std.Sat.CNF α := ⟨f.clauses.map Std.Sat.CNF.Clause.ofLiterals⟩
end OrderedFormula
abbrev Clause (α : Type*) := Controller.CNF.OrderedFormula.Clause α
abbrev Formula (α : Type*) := Controller.CNF.OrderedFormula α
abbrev FiniteFormula (v : Nat) := Formula (Fin v)
abbrev negate (l : Literal α) : Literal α := Std.Sat.Literal.negate l
def LiteralHolds (a : α → Bool) (l : Literal α) : Prop := a l.1 = l.2
def ClauseHolds (a : α → Bool) (c : Clause α) : Prop := ∃ l, l ∈ c ∧ LiteralHolds a l
def Satisfies (a : α → Bool) (f : Formula α) : Prop := ∀ c, c ∈ f.clauses → ClauseHolds a c
def Satisfiable (f : Formula α) : Prop := ∃ a, Satisfies a f
def Unsatisfiable (f : Formula α) : Prop := ¬Satisfiable f
def SameLiterals (c d : Clause α) : Prop := ∀ l, l ∈ c ↔ l ∈ d
def normalizeClause [DecidableEq α] (c : Clause α) : Clause α := c.eraseDups
def ofClauses (cs : List (Clause α)) : Formula α := ⟨cs.toArray⟩
@[simp] theorem clauseHolds_cons (a : α → Bool) (l : Literal α) (c : Clause α) :
    ClauseHolds a (l :: c) ↔ LiteralHolds a l ∨ ClauseHolds a c := by
  simp [ClauseHolds, or_and_right, exists_or]
end Controller.CNF source_context "Controller.CNF.Relabel" namespace Controller.CNF
abbrev relabel (r : α → β) (f : Formula α) : Formula β := Controller.CNF.OrderedFormula.relabel r f
def signedLiteral (r : α → β) (phase : α → Bool) (l : Literal α) : Literal β := (r l.1, phase l.1 == l.2)
def signedPullback (r : α → β) (phase : α → Bool) (a : β → Bool) : α → Bool := fun i => a (r i) == phase i
def signedRelabel (r : α → β) (phase : α → Bool) (f : Formula α) : Formula β := ⟨f.clauses.map (List.map (signedLiteral r phase))⟩
end Controller.CNF source_context "Controller.CNF.Gates" namespace Controller.CNF
def literalValue (a : α → Bool) (l : Literal α) : Bool := a l.1 == l.2
inductive Gate (α : Type*) where
  | and (inputs : List (Literal α)) | or (inputs : List (Literal α)) | xor (left right : Literal α) | alias (input : Literal α) | not (input : Literal α) | constant (value : Bool)
  deriving DecidableEq, Repr
namespace Gate
def inputs : Gate α → List (Literal α) | .and ls | .or ls => ls | .xor l r => [l, r] | .alias l | .not l => [l] | .constant _ => []
def clauses (out : Literal α) : Gate α → List (Clause α) | .and ls => ls.map (fun l => [negate out, l]) ++ [out :: ls.map negate] | .or ls => ls.map (fun l => [out, negate l]) ++ [negate out :: ls] | .xor l r => [[l, r, negate out], [negate l, negate r, negate out], [l, negate r, out], [negate l, r, out]] | .alias l => [[negate out, l], [out, negate l]] | .not l => [[out, l], [negate out, negate l]] | .constant b => [[if b then out else negate out]]
def ContainsBlock [DecidableEq α] (f : Formula α) (out : Literal α) (g : Gate α) : Prop := ∀ i : Fin (g.clauses out).length, ∃ j : Fin f.clauses.size, (g.clauses out)[i].toFinset = f.clauses[j].toFinset
instance [DecidableEq α] (f : Formula α) (out : Literal α) (g : Gate α) : Decidable (ContainsBlock f out g) := inferInstanceAs (Decidable (∀ _, ∃ _, _))
def CompleteProducer [DecidableEq α] (f : Formula α) (out : Literal α) (g : Gate α) : Prop := ContainsBlock f out g ∧ ∀ j : Fin f.clauses.size, ∃ i : Fin (g.clauses out).length, f.clauses[j].toFinset = (g.clauses out)[i].toFinset
instance [DecidableEq α] (f : Formula α) (out : Literal α) (g : Gate α) : Decidable (CompleteProducer f out g) := inferInstanceAs (Decidable (_ ∧ ∀ _, ∃ _, _))
end Gate end Controller.CNF source_context "Controller.Native.ObservationProjection" namespace Controller.Native.ObservationProjection
open CNF
def joint (signals : σ → Bool) (auxiliary : α → Bool) : Sum σ α → Bool := Sum.elim signals auxiliary
def Discrepant (signals : σ → Bool) (pair : Literal σ × Literal σ) : Prop := literalValue signals pair.1 ≠ literalValue signals pair.2
inductive UnitDerived (formula : Formula α) : Clause α → Prop where
  | source (clause : Clause α) (membership : clause ∈ formula.clauses) : UnitDerived formula clause | reorder {left right : Clause α} (proof : UnitDerived formula left) (permutation : left.Perm right) : UnitDerived formula right | propagate (literal : Literal α) (tail : Clause α) (clause : UnitDerived formula (literal :: tail)) (unit : UnitDerived formula [negate literal]) : UnitDerived formula tail
def inactiveFormula (pure : Formula α) (activities : ρ → Literal α) (accepted : List ρ) : Formula α := pure ++ ofClauses (accepted.map fun i => [negate (activities i)])
/-- Typed projection and certificate law. -/ theorem observation_projection_of_unit_conflict (definitions : Formula σ) (wrapper : Formula (Sum σ α)) (pure : Formula α) (pairs : ρ → Literal σ × Literal σ) (activities : ρ → Literal α) (accepted : List ρ) (pureCovered : ∀ signals values, Satisfies (joint signals values) wrapper → Satisfies values pure) (guards : ∀ signals values, Satisfies (joint signals values) wrapper → ∀ i, LiteralHolds values (activities i) → Discrepant signals (pairs i)) (conflict : UnitDerived (inactiveFormula pure activities accepted) []) (uniform : ∀ i ∈ accepted, ∀ left right : Bool, left ≠ right → (¬∃ signals, Satisfies signals definitions ∧ literalValue signals (pairs i).1 = left ∧ literalValue signals (pairs i).2 = right) ∨ ∃ values, ∀ signals, Satisfies signals definitions → literalValue signals (pairs i).1 = left → literalValue signals (pairs i).2 = right → Satisfies (joint signals values) wrapper) (signals : σ → Bool) (model : Satisfies signals definitions) : (∃ values, Satisfies (joint signals values) wrapper) ↔ ∃ i ∈ accepted, Discrepant signals (pairs i) := by sorry
inductive RequirementTree (ρ : Type*) where
  | leaf (observation : ρ) | branch (left right : RequirementTree ρ)
def RequirementTree.leaves : RequirementTree ρ → List ρ | .leaf i => [i] | .branch left right => left.leaves ++ right.leaves
inductive PrivateActivity (ι ρ : Type*) where
  | internal (activity : ι) | observed (observation : ρ) | tree (path : List Bool)
def RequirementTree.root (tree : RequirementTree ρ) (path : List Bool) : PrivateActivity ι ρ := match tree with | .leaf i => .observed i | .branch _ _ => .tree path
structure OptionalClause (σ ι ρ : Type*) where
  (premise : ι) (alternatives : List (PrivateActivity ι ρ)) (signals : Clause σ)
structure OptionalWrapper (σ ι ρ : Type*) where
  (tree : RequirementTree ρ) (distinctLeaves : tree.leaves.Nodup) (observedPairs : ρ → Literal σ × Literal σ) (internalPairs : ι → Literal σ × Literal σ) (clauses : List (OptionalClause σ ι ρ))
def guardRows (activity : α) (pair : Literal σ × Literal σ) : List (Clause (Sum σ α)) := [[(Sum.inr activity, false), (Sum.inl pair.1.1, pair.1.2), (Sum.inl pair.2.1, pair.2.2)], [(Sum.inr activity, false), (Sum.inl pair.1.1, !pair.1.2), (Sum.inl pair.2.1, !pair.2.2)]]
def requirementRow (parent left right : α) : Clause (Sum σ α) := [(Sum.inr parent, false), (Sum.inr left, true), (Sum.inr right, true)]
def RequirementTree.rows (tree : RequirementTree ρ) (path : List Bool) : List (Clause (Sum σ (PrivateActivity ι ρ))) := match tree with | .leaf _ => [] | .branch left right => requirementRow (.tree path) (left.root (path ++ [false])) (right.root (path ++ [true])) :: left.rows (path ++ [false]) ++ right.rows (path ++ [true])
def OptionalClause.clause (clause : OptionalClause σ ι ρ) : Clause (Sum σ (PrivateActivity ι ρ)) := (Sum.inr (.internal clause.premise), false) :: (clause.alternatives.map (fun alternative => (Sum.inr alternative, true)) ++ clause.signals.map (fun literal => (Sum.inl literal.1, literal.2)))
noncomputable def OptionalWrapper.formula [Fintype ι] (wrapper : OptionalWrapper σ ι ρ) : Formula (Sum σ (PrivateActivity ι ρ)) := by
  classical
  exact ofClauses ((Finset.univ.toList.flatMap fun i => guardRows (.internal i) (wrapper.internalPairs i)) ++
    (wrapper.tree.leaves.flatMap fun i => guardRows (.observed i) (wrapper.observedPairs i)) ++
    wrapper.clauses.map OptionalClause.clause ++ wrapper.tree.rows [] ++
    [[(Sum.inr (wrapper.tree.root []), true)]])
noncomputable def selectedFormula [Fintype ι] (wrapper : OptionalWrapper σ ι ρ) (selected : List ρ) : Formula (Sum σ (PrivateActivity ι ρ)) := wrapper.formula ++ ofClauses [selected.map (fun i => (Sum.inr (.observed i), true))]
noncomputable def formulaAuxiliarySupport (formula : Formula (Sum σ α)) : Finset α := by
  classical
  exact (formula.clauses.toList.flatMap fun clause => clause.flatMap fun literal =>
    match literal.1 with
    | .inl _ => []
    | .inr a => [a]).toFinset
def RequirementTree.branchPositions (tree : RequirementTree ρ) (path : List Bool) : List (List Bool) := match tree with | .leaf _ => [] | .branch left right => path :: left.branchPositions (path ++ [false]) ++ right.branchPositions (path ++ [true])
noncomputable def OptionalWrapper.declaredAuxiliaries [Fintype ι] (wrapper : OptionalWrapper σ ι ρ) : Finset (PrivateActivity ι ρ) := by
  classical
  exact ((Finset.univ.toList.map PrivateActivity.internal) ++
    wrapper.tree.leaves.map PrivateActivity.observed ++
    (wrapper.tree.branchPositions []).map PrivateActivity.tree).toFinset
def OptionalWrapper.DeclaredPrivate [Fintype ι] (wrapper : OptionalWrapper σ ι ρ) : Prop := formulaAuxiliarySupport wrapper.formula ⊆ wrapper.declaredAuxiliaries
noncomputable def extendDeclaredAuxiliaries (support : Finset α) (values : {a // a ∈ support} → Bool) : α → Bool := by
  classical
  exact fun a => if membership : a ∈ support then values ⟨a, membership⟩ else false
/-- Typed projection and certificate law. -/ theorem optional_declared_cnf_projection [Fintype ι] (wrapper : OptionalWrapper σ ι ρ) (valid : wrapper.DeclaredPrivate) (signals : σ → Bool) : (∃ values : {a // a ∈ wrapper.declaredAuxiliaries} → Bool, Satisfies (joint signals (extendDeclaredAuxiliaries wrapper.declaredAuxiliaries values)) wrapper.formula) ↔ ∃ i ∈ wrapper.tree.leaves, Discrepant signals (wrapper.observedPairs i) := by sorry
/-- Typed projection and certificate law. -/ theorem selected_declared_cnf_projection [Fintype ι] (wrapper : OptionalWrapper σ ι ρ) (valid : wrapper.DeclaredPrivate) (selected : List ρ) (allLeaves : ∀ i ∈ selected, i ∈ wrapper.tree.leaves) (signals : σ → Bool) : (∃ values : {a // a ∈ wrapper.declaredAuxiliaries} → Bool, Satisfies (joint signals (extendDeclaredAuxiliaries wrapper.declaredAuxiliaries values)) (selectedFormula wrapper selected)) ↔ ∃ i ∈ selected, Discrepant signals (wrapper.observedPairs i) := by sorry
end Controller.Native.ObservationProjection source_context "Controller.Recognition.Producers"
section
attribute [local instance 2000] List.decidableBAll
namespace Controller.Recognition open Controller.CNF
structure Producer (α : Type*) where
  (output : Literal α) (gate : Gate α)
  deriving DecidableEq
namespace Producer
def Ready [DecidableEq α] (known : Finset α) (p : Producer α) : Prop := p.output.1 ∉ known ∧ ∀ l ∈ p.gate.inputs, l.1 ∈ known
def Complete [DecidableEq α] (p : Producer α) (block : Formula α) : Prop := Gate.CompleteProducer block p.output p.gate
instance [DecidableEq α] (known : Finset α) (p : Producer α) : Decidable (p.Ready known) := inferInstanceAs (Decidable (_ ∧ ∀ _, ∀ _, _))
instance [DecidableEq α] (p : Producer α) (block : Formula α) : Decidable (p.Complete block) := inferInstanceAs (Decidable (Gate.CompleteProducer block p.output p.gate))
end Producer
structure BlockRecord (α : Type*) (source : Formula α) where
  (producer : Producer α) (origins : List (Fin source.clauses.size))
namespace BlockRecord
def localFormula (b : BlockRecord α source) : Formula α := ofClauses (b.origins.map (fun i => source.clauses[i]))
def Valid [DecidableEq α] (b : BlockRecord α source) : Prop := b.producer.Complete b.localFormula
instance [DecidableEq α] (b : BlockRecord α source) : Decidable b.Valid := inferInstanceAs (Decidable (b.producer.Complete b.localFormula))
end BlockRecord
structure IntendedDAG (α : Type*) [DecidableEq α] where
  (roots : Finset α) (gate : α → Gate α) (phase : α → Bool) (rank : α → Nat) (roots_empty : ∀ v ∈ roots, (gate v).inputs = []) (earlier : ∀ v l, l ∈ (gate v).inputs → rank l.1 < rank v)
namespace IntendedDAG variable [DecidableEq α]
def producer (dag : IntendedDAG α) (v : α) : Producer α := ⟨(v, dag.phase v), dag.gate v⟩
inductive Descendant (dag : IntendedDAG α) : α → α → Prop where
  | edge {x y : α} (l : Literal α) (member : l ∈ (dag.gate y).inputs) (source : l.1 = x) : Descendant dag x y | trans {x y z : α} : Descendant dag x y → Descendant dag y z → Descendant dag x z
structure CandidatePromise (dag : IntendedDAG α) where
  (candidates : List (Producer α)) (coverage : ∀ v, v ∉ dag.roots → dag.producer v ∈ candidates) (no_root : ∀ p ∈ candidates, p.output.1 ∉ dag.roots) (alternatives : ∀ p ∈ candidates, p = dag.producer p.output.1 ∨ ∃ l ∈ p.gate.inputs, dag.Descendant p.output.1 l.1)
inductive Run (dag : IntendedDAG α) (promise : dag.CandidatePromise) :
  Finset α → List (Producer α) → Prop where
  | start : Run dag promise dag.roots [] | step {known trace} (previous : Run dag promise known trace) (p : Producer α) (member : p ∈ promise.candidates) (ready : p.Ready known) : Run dag promise (insert p.output.1 known) (p :: trace)
end IntendedDAG
def ValidSelection [DecidableEq α] (roots : Finset α) (rank : α → Nat) (selected : List (Producer α)) : Prop := (selected.map (fun p => p.output.1)).Nodup ∧ (∀ p ∈ selected, p.output.1 ∉ roots) ∧ (∀ v, v ∉ roots → ∃ p ∈ selected, p.output.1 = v) ∧ (∀ p ∈ selected, ∀ l ∈ p.gate.inputs, rank l.1 < rank p.output.1)
attribute [-instance] Nat.decLt
instance [DecidableEq α] [Fintype α] (roots : Finset α) (rank : α → Nat) (selected : List (Producer α)) : Decidable (ValidSelection roots rank selected) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
attribute [instance 1000] Nat.decLt
end Controller.Recognition end source_context "Controller.Recognition.ProducerCompletion" namespace Controller.Recognition.IntendedDAG
variable [DecidableEq α]
/-- Typed projection and certificate law. -/ theorem recovery_exact (dag : IntendedDAG α) (promise : dag.CandidatePromise) {known trace} (run : dag.Run promise known trace) (saturated : ∀ p ∈ promise.candidates, ¬p.Ready known) : (∀ p ∈ trace, p = dag.producer p.output.1 ∧ p.output.1 ∉ dag.roots) ∧ (∀ v, v ∉ dag.roots → dag.producer v ∈ trace) ∧ (trace.map (fun p => p.output.1)).Nodup := by sorry
end Controller.Recognition.IntendedDAG source_context "Controller.Recognition.Coverage" namespace Controller.Recognition.Coverage open Controller.CNF
abbrev Origins (source : Formula α) := List (Fin source.clauses.size)
def block (source : Formula α) (origins : Origins source) : Formula α := ofClauses (origins.map fun i => source.clauses[i])
end Controller.Recognition.Coverage source_context "Controller.Recognition.Normalization" namespace Controller.Recognition open Controller.CNF
structure AliasEdge (α : Type*) where
  (left : α) (right : α) (phase : Bool)
inductive AliasPath (edges : List (AliasEdge α)) : α → α → Bool → Prop where
  | refl (i) : AliasPath edges i i true | edge (e) (member : e ∈ edges) : AliasPath edges e.left e.right e.phase | symm {i j phase} : AliasPath edges i j phase → AliasPath edges j i phase | trans {i j k first second} : AliasPath edges i j first → AliasPath edges j k second → AliasPath edges i k (second == first)
end Controller.Recognition source_context "Controller.Recognition.Record" namespace Controller.Recognition open Controller.CNF
structure Record (source : Formula (Fin original)) (recovered : Nat) where
  (expected : Formula (Fin recovered)) (coordinate : Fin original → Fin recovered) (phase : Fin original → Bool) (anchor : Fin recovered → Fin original) (aliases : Fin original → Coverage.Origins source) (sourceRows : Fin source.clauses.size → Option (Fin expected.clauses.size)) (expectedRows : Fin expected.clauses.size → Fin source.clauses.size)
namespace Record variable {original recovered : Nat} {source : Formula (Fin original)}
def mappedRow (record : Record source recovered) (i : Fin source.clauses.size) : Clause (Fin recovered) := source.clauses[i].map (signedLiteral record.coordinate record.phase)
def Tautological (clause : Clause (Fin recovered)) : Prop := ∃ literal ∈ clause, negate literal ∈ clause
instance (clause : Clause (Fin recovered)) : Decidable (Tautological clause) := by
  unfold Tautological
  infer_instance
def RowChecks (record : Record source recovered) : Prop := (∀ i, match record.sourceRows i with | none => Tautological (record.mappedRow i) | some j => SameLiterals (record.mappedRow i) record.expected.clauses[j]) ∧ (∀ j, SameLiterals (record.mappedRow (record.expectedRows j)) record.expected.clauses[j])
instance (record : Record source recovered) : Decidable record.RowChecks := by
  letI : ∀ c d : Clause (Fin recovered), Decidable (SameLiterals c d) := fun c d => by
    unfold SameLiterals
    infer_instance
  letI : ∀ i : Fin source.clauses.size, Decidable (match record.sourceRows i with
      | none => Tautological (record.mappedRow i)
      | some j => SameLiterals (record.mappedRow i) record.expected.clauses[j]) := fun i => by
    cases choice : record.sourceRows i with
    | none => simp only [choice]; infer_instance
    | some j => simp only [choice]; unfold SameLiterals; infer_instance
  unfold RowChecks
  infer_instance
def lift (record : Record source recovered) (assignment : Fin recovered → Bool) : Fin original → Bool := signedPullback record.coordinate record.phase assignment
end Record namespace AliasTrace
open Controller.Recognition
structure Result (edges : List (AliasEdge (Fin original))) (start : Fin original) where
  (endpoint : Fin original) (phase : Bool) (sound : AliasPath edges start endpoint phase)
def replay (edges : List (AliasEdge (Fin original))) (start : Fin original) :
    List (Fin edges.length × Bool) → Option (Result edges start)
  | [] => some ⟨start, true, .refl start⟩
  | (index, direction) :: rest =>
      let edge := edges.get index
      if direction then
        if connected : start = edge.left then
          match replay edges edge.right rest with
          | none => none
          | some tail => some ⟨tail.endpoint, tail.phase == edge.phase, by subst start; exact .trans (.edge edge (List.get_mem ..)) tail.sound⟩
        else none
      else
        if connected : start = edge.right then
          match replay edges edge.left rest with
          | none => none
          | some tail => some ⟨tail.endpoint, tail.phase == edge.phase, by subst start; exact .trans (.symm (.edge edge (List.get_mem ..))) tail.sound⟩
        else none
structure Record (source : Formula (Fin original)) (recovered : Nat) where
  (base : Recognition.Record source recovered) (edges : List (AliasEdge (Fin original))) (origins : Fin edges.length → Coverage.Origins source) (paths : Fin original → List (Fin edges.length × Bool))
namespace Record variable {original recovered : Nat} {source : Formula (Fin original)}
def EdgeChecks (record : Record source recovered) : Prop := ∀ i : Fin record.edges.length, Gate.CompleteProducer (Coverage.block source (record.origins i)) ((record.edges.get i).left, true) (.alias ((record.edges.get i).right, (record.edges.get i).phase))
instance (record : Record source recovered) : Decidable record.EdgeChecks := by
  unfold EdgeChecks
  infer_instance
def pathCheck (record : Record source recovered) (i : Fin original) : Bool := match replay record.edges i (record.paths i) with | none => false | some result => decide (result.endpoint = record.base.anchor (record.base.coordinate i) ∧ result.phase = record.base.phase i)
def AnchorChecks (record : Record source recovered) : Prop := ∀ j, record.base.coordinate (record.base.anchor j) = j ∧ record.base.phase (record.base.anchor j) = true
instance (record : Record source recovered) : Decidable record.AnchorChecks := by
  unfold AnchorChecks
  infer_instance
def check (record : Record source recovered) : Bool := decide record.EdgeChecks && decide record.base.RowChecks && decide record.AnchorChecks && decide (∀ i, record.pathCheck i = true)
end Record end AliasTrace namespace ProducerMetadata
def replay (known : Finset (Fin count)) (source : Formula (Fin count)) : List (BlockRecord (Fin count) source) → Option (Finset (Fin count)) | [] => some known | block :: rest => if decide block.Valid && decide (block.producer.Ready known) then replay (insert block.producer.output.1 known) source rest else none
structure Record (source : Formula (Fin count)) where
  (roots : Finset (Fin count)) (rank : Fin count → Nat) (blocks : List (BlockRecord (Fin count) source))
namespace Record variable {count : Nat} {source : Formula (Fin count)}
def selected (record : Record source) : List (Producer (Fin count)) := record.blocks.map BlockRecord.producer
def Checks (record : Record source) : Prop := ValidSelection record.roots record.rank record.selected ∧ (∀ block ∈ record.blocks, block.Valid) ∧ replay record.roots source record.blocks = some Finset.univ
instance (record : Record source) : Decidable record.Checks := by
  unfold Checks
  infer_instance
def check (record : Record source) : Bool := decide record.Checks
end Record end ProducerMetadata end Controller.Recognition source_context "Controller.Basic.Assignments" namespace Controller
abbrev Channel (n : ℕ) := Fin n
abbrev Assignment (n : ℕ) := Channel n → Bool
def assignmentOfSet {n : ℕ} (K : Finset (Channel n)) : Assignment n := fun i => decide (i ∈ K)
def setOfAssignment {n : ℕ} (a : Assignment n) : Finset (Channel n) := Finset.univ.filter (fun i => a i = true)
end Controller source_context "Controller.Decoder.Syntax" namespace Controller.Decoder
inductive Gate (n available : ℕ) where
  | zero : Gate n available | input (channel : Channel n) : Gate n available | disj (children : List (Fin available)) : Gate n available | guard (child : Fin available) (labels : List (Channel n)) : Gate n available | liveAnd (left right : Fin available) : Gate n available
  deriving DecidableEq, Repr
namespace Gate variable {n available : ℕ}
def children : Gate n available → List (Fin available)
  | .zero => [] | .input _ => [] | .disj refs => refs
  | .guard child _ => [child] | .liveAnd left right => [left, right]
def isLiveAnd : Gate n available → Bool | .liveAnd _ _ => true | _ => false
def IsGuarded (gate : Gate n available) : Prop := gate.isLiveAnd = false
def eval (gate : Gate n available) (assignment : Assignment n) (earlier : Fin available → Bool) : Bool := match gate with | .zero => false | .input channel => assignment channel | .disj refs => refs.any earlier | .guard child labels => earlier child && !(labels.any assignment) | .liveAnd left right => earlier left && earlier right
end Gate
structure DAG (n : ℕ) where
  (nodeCount : ℕ) (node : (index : Fin nodeCount) → Gate n index.val) (roots : List (Fin nodeCount))
namespace DAG variable {n : ℕ}
def childIndex (graph : DAG n) (parent : Fin graph.nodeCount) (child : Fin parent.val) : Fin graph.nodeCount := ⟨child.val, Nat.lt_trans child.isLt parent.isLt⟩
theorem childIndex_lt (graph : DAG n) (parent : Fin graph.nodeCount) (child : Fin parent.val) : (graph.childIndex parent child).val < parent.val := child.isLt
def Guarded (graph : DAG n) : Prop := ∀ index, (graph.node index).IsGuarded
end DAG end Controller.Decoder source_context "Controller.Decoder.Eval" namespace Controller.Decoder
namespace DAG variable {n : ℕ}
def eval (graph : DAG n) (assignment : Assignment n) (index : Fin graph.nodeCount) : Bool :=
  (graph.node index).eval assignment (fun child => graph.eval assignment (graph.childIndex index child))
termination_by index.val
decreasing_by exact graph.childIndex_lt index child
def evalPrefix (graph : DAG n) (assignment : Assignment n) :
    (length : ℕ) → length ≤ graph.nodeCount → Fin length → Bool
  | 0, _ => Fin.elim0
  | length + 1, bound =>
      let earlier := graph.evalPrefix assignment length
        (Nat.le_trans (Nat.le_succ length) bound)
      let gate := graph.node ⟨length, Nat.lt_of_lt_of_le (Nat.lt_succ_self length) bound⟩
      Fin.lastCases (gate.eval assignment earlier) earlier
def evalTable (graph : DAG n) (assignment : Assignment n) : Fin graph.nodeCount → Bool := graph.evalPrefix assignment graph.nodeCount (Nat.le_refl graph.nodeCount)
end DAG end Controller.Decoder source_context "Controller.Physical.Controller" namespace Controller.Physical
structure PrimaryInput (n b : ℕ) where
  (positiveBuses : 0 < b) (enable : Assignment n) (request : Fin b → Assignment n)
def PrimaryInput.firstBus {n b : ℕ} (input : PrimaryInput n b) : Fin b := ⟨0, input.positiveBuses⟩
def anyTrue {n : ℕ} (a : Assignment n) : Bool := decide (∃ i, a i = true)
def stageTerms {n : ℕ} (active request : Assignment n) : Assignment n := fun i => active i && request i
def stageFlag {n : ℕ} (active request : Assignment n) : Bool := anyTrue (stageTerms active request)
def stageMask {n : ℕ} (flag : Bool) (terms : Assignment n) : Assignment n := fun i => flag ^^ !(terms i)
def nextActive {n : ℕ} (active request : Assignment n) (flag : Bool) : Assignment n := fun i => active i && stageMask flag (stageTerms active request) i
structure SelectorRun (n b : ℕ) where
  (flags : Fin b → Bool) (activeBefore : Fin b → Assignment n) (terms : Fin b → Assignment n) (masks : Fin b → Assignment n) (finalActive : Assignment n)
def runMasks {n : ℕ} : (b : ℕ) → Assignment n → (Fin b → Assignment n) →
    Option Bool → SelectorRun n b
  | 0, active, _, _ =>
      { flags := Fin.elim0
        activeBefore := Fin.elim0
        terms := Fin.elim0
        masks := Fin.elim0
        finalActive := active }
  | b + 1, active, request, override =>
      let flag := override.getD (stageFlag active (request 0))
      let rest := runMasks b (nextActive active (request 0) flag)
        (fun j => request j.succ) none
      { flags := Fin.cases flag rest.flags
        activeBefore := Fin.cases active rest.activeBefore
        terms := Fin.cases (stageTerms active (request 0)) rest.terms
        masks := Fin.cases (stageMask flag (stageTerms active (request 0))) rest.masks
        finalActive := rest.finalActive }
def qualifiers {n b : ℕ} (enable : Assignment n) (request : Fin b → Assignment n) (flags : Fin b → Bool) : Assignment n := fun i => enable i && decide (∀ j, flags j = true → request j i = true)
def healthyRun {n b : ℕ} (input : PrimaryInput n b) : SelectorRun n b := runMasks b input.enable input.request none
def runFromFirst {n b : ℕ} (input : PrimaryInput n b) (first : Bool) : SelectorRun n b := runMasks b input.enable input.request (some first)
def healthyQualifiers {n b : ℕ} (input : PrimaryInput n b) : Assignment n := qualifiers input.enable input.request (healthyRun input).flags
def qualifiersFromFirst {n b : ℕ} (input : PrimaryInput n b) (first : Bool) : Assignment n := qualifiers input.enable input.request (runFromFirst input first).flags
def ObservationsDiffer {n q : ℕ} (outputs : Fin q → Assignment n → Bool) (healthy faulty : Assignment n) : Prop := ∃ k, outputs k healthy ≠ outputs k faulty
end Controller.Physical source_context "Controller.Physical.Faults" namespace Controller.Physical
structure Bridge (n : ℕ) where
  (target : Channel n) (drivers : Finset (Channel n)) (drivers_nonempty : drivers.Nonempty) (target_not_mem : target ∉ drivers)
def Bridge.remaining {n : ℕ} (bridge : Bridge n) : Finset (Channel n) := Finset.univ \ insert bridge.target bridge.drivers
def firstTerms {n b : ℕ} (input : PrimaryInput n b) : Assignment n := stageTerms input.enable (input.request input.firstBus)
def bridgeU {n b : ℕ} (bridge : Bridge n) (input : PrimaryInput n b) : Bool := !(firstTerms input bridge.target)
def bridgeD {n b : ℕ} (bridge : Bridge n) (input : PrimaryInput n b) : Bool := decide (∀ i ∈ bridge.drivers, firstTerms input i = false)
def bridgeR {n b : ℕ} (bridge : Bridge n) (input : PrimaryInput n b) : Bool := decide (∀ i ∈ bridge.remaining, firstTerms input i = false)
def BridgeInterfaceSatisfied {n b : ℕ} (bridge : Bridge n) (input : PrimaryInput n b) (drive wire : Bool) : Prop := bridgeU bridge input = !drive ∧ bridgeD bridge input = drive ∧ wire = drive
def bridgeFirstFlag {n b : ℕ} (bridge : Bridge n) (input : PrimaryInput n b) (wire : Bool) : Bool := !(wire && bridgeD bridge input && bridgeR bridge input)
def bridgeQualifiers {n b : ℕ} (bridge : Bridge n) (input : PrimaryInput n b) (wire : Bool) : Assignment n := qualifiersFromFirst input (bridgeFirstFlag bridge input wire)
def BridgeInputDetects {n b q : ℕ} (bridge : Bridge n) (drive : Bool) (outputs : Fin q → Assignment n → Bool) (input : PrimaryInput n b) (wire : Bool) : Prop := BridgeInterfaceSatisfied bridge input drive wire ∧ ObservationsDiffer outputs (healthyQualifiers input) (bridgeQualifiers bridge input wire)
def BridgeDetectable {n b q : ℕ} (bridge : Bridge n) (drive : Bool) (outputs : Fin q → Assignment n → Bool) : Prop := ∃ input : PrimaryInput n b, ∃ wire, BridgeInputDetects bridge drive outputs input wire
end Controller.Physical source_context "Controller.Native.Encode" namespace Controller.Native
inductive Side where
  | healthy | faulty
  deriving DecidableEq, Repr
def Side.all : List Side := [.healthy, .faulty]
@[simp] theorem Side.mem_all (side : Side) : side ∈ Side.all := by cases side <;> simp [Side.all]
inductive PrefixLayout where
  | raw | shared
  deriving DecidableEq, Repr
def PrefixLayout.activeCount : PrefixLayout → ℕ → ℕ | .raw, _ => 0 | .shared, buses => buses
inductive PrimaryRole (n b : ℕ) where
  | enable (channel : Fin n) | request (bus : Fin b) (channel : Fin n) | wire
  deriving DecidableEq, Repr
inductive Role (layout : PrefixLayout) (n b m q : ℕ) where
  | driver | remaining | firstProduct (side : Side) | term (side : Side) (bus : Fin b) (channel : Fin n) | absent (side : Side) (bus : Fin b) (channel : Fin n) | flag (side : Side) (bus : Fin b) | mask (side : Side) (bus : Fin b) (channel : Fin n) | active (side : Side) (bus : Fin (layout.activeCount b)) (channel : Fin n) | qualifierGuard (side : Side) (bus : Fin b) (channel : Fin n) | qualifier (side : Side) (channel : Fin n) | decoder (side : Side) (node : Fin m) | difference (output : Fin q) | detected
  deriving DecidableEq, Repr
structure Parameters where
  (channels : ℕ) (buses : ℕ) (positiveBuses : 0 < buses) (bridge : Physical.Bridge channels) (decoder : Decoder.DAG channels) (layout : PrefixLayout) (drive : Bool)
abbrev Internal (params : Parameters) := Role params.layout params.channels params.buses params.decoder.nodeCount params.decoder.roots.length
inductive Variable (params : Parameters) where
  | primary (role : PrimaryRole params.channels params.buses) | internal (role : Internal params)
  deriving DecidableEq, Repr
abbrev Lit (params : Parameters) := CNF.Literal (Variable params)
namespace Parameters
def positive (slot : Variable params) : Lit params := (slot, true)
def negative (slot : Variable params) : Lit params := (slot, false)
def enable (params : Parameters) (channel : Fin params.channels) : Lit params := positive (.primary (.enable channel))
def request (params : Parameters) (bus : Fin params.buses) (channel : Fin params.channels) : Lit params := positive (.primary (.request bus channel))
def internal (params : Parameters) (role : Internal params) : Lit params := positive (.internal role)
def firstBus (params : Parameters) : Fin params.buses := ⟨0, params.positiveBuses⟩
def targetAbsent (params : Parameters) : Lit params := internal params (.absent .healthy params.firstBus params.bridge.target)
def primaryRoles (params : Parameters) : List (PrimaryRole params.channels params.buses) := (List.finRange params.channels).map .enable ++ (List.finRange params.buses).flatMap (fun bus => (List.finRange params.channels).map (.request bus)) ++ [.wire]
def roles (params : Parameters) : List (Internal params) := [.driver, .remaining] ++ Side.all.map .firstProduct ++ Side.all.flatMap (fun side => (List.finRange params.buses).flatMap fun bus => (List.finRange params.channels).map (.term side bus)) ++ Side.all.flatMap (fun side => (List.finRange params.buses).flatMap fun bus => (List.finRange params.channels).map (.absent side bus)) ++ Side.all.flatMap (fun side => (List.finRange params.buses).map (.flag side)) ++ Side.all.flatMap (fun side => (List.finRange params.buses).flatMap fun bus => (List.finRange params.channels).map (.mask side bus)) ++ Side.all.flatMap (fun side => (List.finRange (params.layout.activeCount params.buses)).flatMap fun bus => (List.finRange params.channels).map (.active side bus)) ++ Side.all.flatMap (fun side => (List.finRange params.buses).flatMap fun bus => (List.finRange params.channels).map (.qualifierGuard side bus)) ++ Side.all.flatMap (fun side => (List.finRange params.channels).map (.qualifier side)) ++ Side.all.flatMap (fun side => (List.finRange params.decoder.nodeCount).map (.decoder side)) ++ (List.finRange params.decoder.roots.length).map .difference ++ [.detected]
@[simp] theorem mem_primaryRoles (params : Parameters) (role) :
    role ∈ params.primaryRoles := by
  cases role <;> simp [primaryRoles]
@[simp] theorem mem_roles (params : Parameters) (role) : role ∈ params.roles := by cases role <;> simp [roles]
def variableRoles (params : Parameters) : List (Variable params) := params.primaryRoles.map .primary ++ params.roles.map .internal
@[simp] theorem mem_variableRoles (params : Parameters) (slot : Variable params) :
    slot ∈ params.variableRoles := by
  cases slot <;> simp [variableRoles]
instance (params : Parameters) : Fintype (Variable params) := Fintype.ofList params.variableRoles (mem_variableRoles params)
def decoderGate (params : Parameters) (side : Side) (index : Fin params.decoder.nodeCount) : CNF.Gate (Variable params) := match params.decoder.node index with | .zero => .or [] | .input channel => .alias (internal params (.qualifier side channel)) | .disj children => .or (children.map fun child => internal params (.decoder side (params.decoder.childIndex index child))) | .guard child labels => .and (internal params (.decoder side (params.decoder.childIndex index child)) :: labels.map fun channel => negative (.internal (.qualifier side channel))) | .liveAnd left right => .and [internal params (.decoder side (params.decoder.childIndex index left)), internal params (.decoder side (params.decoder.childIndex index right))]
def rawTermInputs (params : Parameters) (side : Side) (bus : Fin params.buses) (channel : Fin params.channels) : List (Lit params) := [enable params channel, request params bus channel] ++ ((List.finRange params.buses).filter (fun earlier => earlier < bus)).map (fun earlier => internal params (.mask side earlier channel))
def termGate (params : Parameters) (side : Side) (bus : Fin params.buses) (channel : Fin params.channels) : CNF.Gate (Variable params) :=
  match layoutEquation : params.layout with
  | .raw => .and (rawTermInputs params side bus channel)
  | .shared => .and
      [internal params (.active side ⟨bus.val, by simpa [layoutEquation, PrefixLayout.activeCount] using bus.isLt⟩ channel), request params bus channel]
def activeGate (params : Parameters) (side : Side) (bus : Fin (params.layout.activeCount params.buses)) (channel : Fin params.channels) : CNF.Gate (Variable params) :=
  match layoutEquation : params.layout with
  | .raw => False.elim (Nat.not_lt_zero bus.val (by simpa [layoutEquation, PrefixLayout.activeCount] using bus.isLt))
  | .shared =>
      if first : bus.val = 0 then .alias (enable params channel)
      else .and
        [internal params (.active side ⟨bus.val - 1, by omega⟩ channel),
          internal params (.mask side ⟨bus.val - 1, by
            have bound : bus.val < params.buses := by simpa [layoutEquation, PrefixLayout.activeCount] using bus.isLt
            omega⟩ channel)]
def gate (params : Parameters) : Internal params → CNF.Gate (Variable params) | .driver => .and (params.bridge.drivers.sort.map fun channel => internal params (.absent .healthy params.firstBus channel)) | .remaining => .and (params.bridge.remaining.sort.map fun channel => internal params (.absent .healthy params.firstBus channel)) | .firstProduct side => .and [match side with | .healthy => targetAbsent params | .faulty => positive (.primary .wire), internal params .driver, internal params .remaining] | .term side bus channel => termGate params side bus channel | .absent side bus channel => .not (internal params (.term side bus channel)) | .flag side bus => if bus.val = 0 then .not (internal params (.firstProduct side)) else .or ((List.finRange params.channels).map fun channel => internal params (.term side bus channel)) | .mask side bus channel => .xor (internal params (.flag side bus)) (internal params (.absent side bus channel)) | .active side bus channel => activeGate params side bus channel | .qualifierGuard side bus channel => .or [negative (.internal (.flag side bus)), request params bus channel] | .qualifier side channel => .and (enable params channel :: (List.finRange params.buses).map fun bus => internal params (.qualifierGuard side bus channel)) | .decoder side index => decoderGate params side index | .difference output => .xor (internal params (.decoder .healthy (params.decoder.roots.get output))) (internal params (.decoder .faulty (params.decoder.roots.get output))) | .detected => .or ((List.finRange params.decoder.roots.length).map fun output => internal params (.difference output))
def assertions (params : Parameters) : List (Lit params) := [(params.targetAbsent.1, !params.drive), (.internal .driver, params.drive), (.primary .wire, params.drive), internal params .detected]
def equationClauses (params : Parameters) : List (CNF.Clause (Variable params)) := params.roles.flatMap fun role => (params.gate role).clauses (internal params role)
def equationFormula (params : Parameters) : CNF.Formula (Variable params) := CNF.ofClauses params.equationClauses
def assertionFormula (params : Parameters) : CNF.Formula (Variable params) := CNF.ofClauses (params.assertions.map fun literal => [literal])
def specificationFormula (params : Parameters) : CNF.Formula (Variable params) := params.equationFormula ++ params.assertionFormula
def primaryAssignment {n b : ℕ} (input : Physical.PrimaryInput n b) (wire : Bool) :
    PrimaryRole n b → Bool
  | .enable channel => input.enable channel
  | .request bus channel => input.request bus channel
  | .wire => wire
def selectorRun (params : Parameters) (input : Physical.PrimaryInput params.channels params.buses) (wire : Bool) : Side → Physical.SelectorRun params.channels params.buses | .healthy => Physical.healthyRun input | .faulty => Physical.runFromFirst input (Physical.bridgeFirstFlag params.bridge input wire)
def qualifiers (params : Parameters) (input : Physical.PrimaryInput params.channels params.buses) (wire : Bool) (side : Side) : Assignment params.channels := Physical.qualifiers input.enable input.request (params.selectorRun input wire side).flags
def roleValue (params : Parameters) (input : Physical.PrimaryInput params.channels params.buses)
    (wire : Bool) : Internal params → Bool
  | .driver => Physical.bridgeD params.bridge input
  | .remaining => Physical.bridgeR params.bridge input
  | .firstProduct side =>
      (match side with | .healthy => Physical.bridgeU params.bridge input | .faulty => wire) &&
        Physical.bridgeD params.bridge input && Physical.bridgeR params.bridge input
  | .term side bus channel => (params.selectorRun input wire side).terms bus channel
  | .absent side bus channel => !(params.selectorRun input wire side).terms bus channel
  | .flag side bus => (params.selectorRun input wire side).flags bus
  | .mask side bus channel => (params.selectorRun input wire side).masks bus channel
  | .active side bus channel =>
      match layoutEquation : params.layout with
      | .raw => False.elim (Nat.not_lt_zero bus.val (by simpa [layoutEquation, PrefixLayout.activeCount] using bus.isLt))
      | .shared => (params.selectorRun input wire side).activeBefore
          ⟨bus.val, by simpa [layoutEquation, PrefixLayout.activeCount] using bus.isLt⟩ channel
  | .qualifierGuard side bus channel => !(params.selectorRun input wire side).flags bus || input.request bus channel
  | .qualifier side channel => params.qualifiers input wire side channel
  | .decoder side index => params.decoder.eval (params.qualifiers input wire side) index
  | .difference output =>
      params.decoder.eval (params.qualifiers input wire .healthy) (params.decoder.roots.get output) ^^
        params.decoder.eval (params.qualifiers input wire .faulty) (params.decoder.roots.get output)
  | .detected => params.decoder.roots.any fun root =>
      params.decoder.eval (params.qualifiers input wire .healthy) root ^^
        params.decoder.eval (params.qualifiers input wire .faulty) root
def physicalAssignment (params : Parameters) (input : Physical.PrimaryInput params.channels params.buses) (wire : Bool) : Variable params → Bool | .primary role => primaryAssignment input wire role | .internal role => params.roleValue input wire role
def observations (params : Parameters) : Fin params.decoder.roots.length → Assignment params.channels → Bool := fun output assignment => params.decoder.eval assignment (params.decoder.roots.get output)
end Parameters end Controller.Native source_context "Controller.Resolution.Trace"
attribute [-instance] instIsPartialOrder_mathlib
namespace Controller.Resolution open CNF
abbrev Rows (v : Nat) := Nat → Option (Clause (Fin v))
structure State (v : Nat) where
  (rows : Rows v) (lastId : Nat)
structure Step (v : Nat) where
  (id : Nat) (left : Nat) (right : Nat) (pivot : Literal (Fin v)) (clause : Clause (Fin v))
  deriving DecidableEq, Repr
structure Trace (v : Nat) where
  (originalClauseCount : Nat) (steps : List (Step v)) (finalClauseId : Nat)
  deriving DecidableEq, Repr
def initialState (f : FiniteFormula v) : State v := ⟨fun id => if id = 0 then none else f.clauses[id - 1]?, f.clauses.size⟩
def insertRow (state : State v) (id : Nat) (c : Clause (Fin v)) : State v := ⟨fun j => if j = id then some c else state.rows j, id⟩
def resolvent (pivot : Literal (Fin v)) (left right : Clause (Fin v)) : Clause (Fin v) := normalizeClause ((left.filter (fun l => decide (l ≠ negate pivot))) ++ (right.filter (fun l => decide (l ≠ pivot))))
def ExactRule (pivot : Literal (Fin v)) (left right out : Clause (Fin v)) : Prop := negate pivot ∈ left ∧ pivot ∈ right ∧ out.Nodup ∧ out.toFinset = (resolvent pivot left right).toFinset
instance (pivot : Literal (Fin v)) (left right out : Clause (Fin v)) : Decidable (ExactRule pivot left right out) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
def StepOK (state : State v) (step : Step v) (left right : Clause (Fin v)) : Prop := state.lastId < step.id ∧ step.left < step.id ∧ step.right < step.id ∧ ExactRule step.pivot left right step.clause
instance (state : State v) (step : Step v) (left right : Clause (Fin v)) : Decidable (StepOK state step left right) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
def applyStep (state : State v) (step : Step v) : Option (State v) := match state.rows step.left, state.rows step.right with | some left, some right => if StepOK state step left right then some (insertRow state step.id step.clause) else none | _, _ => none
def runSteps : State v → List (Step v) → Option (State v) | state, [] => some state | state, step :: steps => match applyStep state step with | none => none | some next => runSteps next steps
def check (f : FiniteFormula v) (trace : Trace v) : Bool := if trace.originalClauseCount = f.clauses.size then match runSteps (initialState f) trace.steps with | none => false | some state => match state.rows trace.finalClauseId with | none => false | some c => c.isEmpty else false
end Controller.Resolution
attribute [instance 1000] instIsPartialOrder_mathlib
source_context "Controller.Certificate.LRATAdapter" namespace Controller.Certificate open Controller.CNF
structure FiniteIdentifiers (varCount : ℕ) where
  (identify : Fin varCount → ℕ) (injective : Function.Injective identify)
namespace FiniteIdentifiers
def canonical (varCount : ℕ) : FiniteIdentifiers varCount := ⟨Fin.val, fun _ _ equal => Fin.ext equal⟩
def encode (identifiers : FiniteIdentifiers varCount) (source : FiniteFormula varCount) : Formula ℕ := relabel identifiers.identify source
end FiniteIdentifiers namespace LRATAdapter
abbrev Actions := Array Std.Tactic.BVDecide.LRAT.IntAction
def check (identifiers : FiniteIdentifiers varCount) (source : FiniteFormula varCount) (actions : Actions) : Bool := Std.Tactic.BVDecide.LRAT.check actions (OrderedFormula.toStd (identifiers.encode source))
end LRATAdapter
inductive Certificate (varCount : ℕ) where
  | resolution (trace : Controller.Resolution.Trace varCount) | lrat (actions : LRATAdapter.Actions)
def checkTyped (source : FiniteFormula varCount) : Certificate varCount → Bool | .resolution trace => Controller.Resolution.check source trace | .lrat actions => LRATAdapter.check (FiniteIdentifiers.canonical varCount) source actions
end Controller.Certificate source_context "Controller.Recognition.BridgeProjection" namespace Controller.Recognition.Attachment open Controller.CNF
open Controller.Certificate
def negativeUnits (clause : Clause (Fin count)) : Formula (Fin count) := ofClauses (clause.map fun literal => [negate literal])
def entailCheck (premise : Formula (Fin count)) (conclusion : Clause (Fin count)) (certificate : Certificate count) : Bool := checkTyped (premise ++ negativeUnits conclusion) certificate
def flatten (formula : Formula (Fin boundary ⊕ Fin auxCount)) : Formula (Fin (boundary + auxCount)) := relabel finSumFinEquiv formula
def flattenRow (clause : Clause (Fin boundary ⊕ Fin auxCount)) : Clause (Fin (boundary + auxCount)) := clause.map fun literal => (finSumFinEquiv literal.1, literal.2)
def substitutePrivate (values : Fin auxCount → Bool) : Clause (Fin boundary ⊕ Fin auxCount) → Option (Clause (Fin boundary)) | [] => some [] | (Sum.inl channel, polarity) :: rest => (substitutePrivate values rest).map fun row => (channel, polarity) :: row | (Sum.inr channel, polarity) :: rest => if values channel = polarity then none else substitutePrivate values rest
theorem substitutePrivate_sound (values : Fin auxCount → Bool)
    (signals : Fin boundary → Bool) (clause : Clause (Fin boundary ⊕ Fin auxCount)) :
    ClauseHolds (Native.ObservationProjection.joint signals values) clause ↔
      match substitutePrivate values clause with
      | none => True
      | some row => ClauseHolds signals row := by
  induction clause with
  | nil => simp [substitutePrivate, ClauseHolds]
  | cons literal rest ih =>
    rcases literal with ⟨channel, polarity⟩
    cases channel with
    | inl channel =>
      cases reduced : substitutePrivate values rest <;>
        simp [substitutePrivate, reduced, LiteralHolds,
          Native.ObservationProjection.joint] at ih ⊢ <;> tauto
    | inr channel =>
      rw [clauseHolds_cons]
      change (values channel = polarity ∨
        ClauseHolds (Native.ObservationProjection.joint signals values) rest) ↔
        match (if values channel = polarity then none else substitutePrivate values rest) with
        | none => True
        | some row => ClauseHolds signals row
      by_cases active : values channel = polarity
      · simp only [active, ite_true, true_or]
      · simp only [active, ite_false, false_or]
        exact ih
def orientationFormula (definitions : Formula (Fin boundary)) (pair : Literal (Fin boundary) × Literal (Fin boundary)) (left right : Bool) : Formula (Fin boundary) := definitions ++ ofClauses [[(pair.1.1, pair.1.2 == left)], [(pair.2.1, pair.2.2 == right)]]
inductive OrientationEvidence (boundary auxCount rows : Nat) where
  | impossible (certificate : Certificate boundary) | extension (values : Fin auxCount → Bool) (certificates : Fin rows → Certificate boundary)
def orientationCheck (definitions : Formula (Fin boundary))
    (wrapper : Formula (Fin boundary ⊕ Fin auxCount))
    (pair : Literal (Fin boundary) × Literal (Fin boundary)) (left right : Bool) :
    OrientationEvidence boundary auxCount wrapper.clauses.size → Bool
  | .impossible certificate => checkTyped (orientationFormula definitions pair left right) certificate
  | .extension values certificates =>
      letI : ∀ i : Fin wrapper.clauses.size, Decidable
          (match substitutePrivate values wrapper.clauses[i] with
          | none => True
          | some row => entailCheck (orientationFormula definitions pair left right) row (certificates i) = true) :=
        fun i => by
          cases reduced : substitutePrivate values wrapper.clauses[i] <;>
            simp only [reduced] <;> infer_instance
      decide (∀ i : Fin wrapper.clauses.size,
        match substitutePrivate values wrapper.clauses[i] with
        | none => True
        | some row => entailCheck (orientationFormula definitions pair left right) row (certificates i) = true)
structure WrapperRecord (boundary auxCount observations : Nat) where
  (definitions : Formula (Fin boundary)) (wrapper : Formula (Fin boundary ⊕ Fin auxCount)) (pairs : Fin observations → Literal (Fin boundary) × Literal (Fin boundary)) (activities : Fin observations → Fin auxCount) (selected : List (Fin observations)) (guards : Fin observations → Fin 2 → Certificate (boundary + auxCount)) (necessity : Certificate (boundary + auxCount)) (orientations : Fin observations → Bool → Bool → OrientationEvidence boundary auxCount wrapper.clauses.size)
namespace WrapperRecord variable {boundary auxCount observations : Nat}
def guardRow (record : WrapperRecord boundary auxCount observations) (i : Fin observations) (slot : Fin 2) : Clause (Fin boundary ⊕ Fin auxCount) :=
  (Native.ObservationProjection.guardRows (record.activities i) (record.pairs i))[slot.val]'(by exact (@of_eq_true (slot.val < (Native.ObservationProjection.guardRows (record.activities i) (record.pairs i)).length)
    (@Eq.trans Prop (slot.val < (Native.ObservationProjection.guardRows (record.activities i) (record.pairs i)).length) (slot.val < (2 : Nat)) True
      (@congrArg Nat Prop (Native.ObservationProjection.guardRows (record.activities i) (record.pairs i)).length (2 : Nat) (LT.lt (@Fin.val 2 slot))
        (@congrFun' Nat Nat ((@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)) ([[ (Sum.inr (record.activities i), false), (Sum.inl (record.pairs i).1.1, !(record.pairs i).1.2), (Sum.inl (record.pairs i).2.1, !(record.pairs i).2.2) ]] : List (Clause (Fin boundary ⊕ Fin auxCount))).length) ((@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)) (1 : Nat))
          (@congrArg Nat (Nat → Nat) ([[ (Sum.inr (record.activities i), false), (Sum.inl (record.pairs i).1.1, !(record.pairs i).1.2), (Sum.inl (record.pairs i).2.1, !(record.pairs i).2.2) ]] : List (Clause (Fin boundary ⊕ Fin auxCount))).length (1 : Nat) (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat))
            (@zero_add Nat Nat.instAddMonoid.toAddZeroClass (1 : Nat))) (1 : Nat)))
      (@Fin.is_lt._simp_1 2 slot))))
def necessaryRow (record : WrapperRecord boundary auxCount observations) : Clause (Fin boundary ⊕ Fin auxCount) := record.selected.map fun i => (Sum.inr (record.activities i), true)
def Checks (record : WrapperRecord boundary auxCount observations) : Prop := (∀ i slot, entailCheck (flatten record.wrapper) (flattenRow (record.guardRow i slot)) (record.guards i slot) = true) ∧ entailCheck (flatten record.wrapper) (flattenRow record.necessaryRow) record.necessity = true ∧ (∀ i left right, i ∈ record.selected → left ≠ right → orientationCheck record.definitions record.wrapper (record.pairs i) left right (record.orientations i left right) = true)
instance (record : WrapperRecord boundary auxCount observations) : Decidable record.Checks := by
  unfold Checks
  infer_instance
def check (record : WrapperRecord boundary auxCount observations) : Bool := decide record.Checks
end WrapperRecord namespace TargetLink
structure Record (boundary observations : Nat) where
  (definitions : Formula (Fin boundary)) (target : Literal (Fin boundary)) (pairs : Fin observations → Literal (Fin boundary) × Literal (Fin boundary)) (selected : List (Fin observations)) (forward : Fin observations → Bool → Bool → Certificate boundary) (necessary : Certificate boundary)
namespace Record variable {boundary observations : Nat}
def equalFormula (record : Record boundary observations) : Formula (Fin boundary) := ofClauses (record.selected.flatMap fun i => (Gate.alias (record.pairs i).2).clauses (record.pairs i).1)
def contradictionFormula (record : Record boundary observations) : Formula (Fin boundary) := (record.definitions ++ ofClauses [[record.target]]) ++ record.equalFormula
def Checks (record : Record boundary observations) : Prop := (∀ i left right, i ∈ record.selected → left ≠ right → entailCheck (orientationFormula record.definitions (record.pairs i) left right) [record.target] (record.forward i left right) = true) ∧ checkTyped record.contradictionFormula record.necessary = true
instance (record : Record boundary observations) : Decidable record.Checks := by
  unfold Checks
  infer_instance
def check (record : Record boundary observations) : Bool := decide record.Checks
end Record end TargetLink namespace WrapperRecord
variable {boundary auxCount observations : Nat}
instance (signals : Fin boundary → Bool) (pair : Literal (Fin boundary) × Literal (Fin boundary)) : Decidable (Native.ObservationProjection.Discrepant signals pair) := by
  unfold Native.ObservationProjection.Discrepant
  infer_instance
def extension (record : WrapperRecord boundary auxCount observations) (signals : Fin boundary → Bool) : Fin auxCount → Bool := match record.selected.find? (fun i => decide (Native.ObservationProjection.Discrepant signals (record.pairs i))) with | none => fun _ => false | some i => match record.orientations i (literalValue signals (record.pairs i).1) (literalValue signals (record.pairs i).2) with | .impossible _ => fun _ => false | .extension values _ => values
end WrapperRecord end Controller.Recognition.Attachment source_context "Controller.Recognition.Check" namespace Controller.Recognition open Controller.CNF
structure SerializedRecord where
  (sourceClauses : List (List (Nat × Bool))) (expectedClauses : List (List (Nat × Bool))) (coordinates : List Nat) (phases : List Bool) (anchors : List Nat) (aliasOrigins : List (List Nat)) (sourceRows : List (Option Nat)) (expectedRows : List Nat)
  deriving DecidableEq
namespace Record variable {original recovered : Nat} {source : Formula (Fin original)}
def serialize (record : Record source recovered) : SerializedRecord where
  sourceClauses := source.clauses.toList.map (List.map fun literal => (literal.1.val, literal.2)); expectedClauses := record.expected.clauses.toList.map (List.map fun literal => (literal.1.val, literal.2)); coordinates := (List.finRange original).map (fun i => (record.coordinate i).val); phases := (List.finRange original).map record.phase; anchors := (List.finRange recovered).map (fun i => (record.anchor i).val)
  aliasOrigins := (List.finRange original).map (fun i => (record.aliases i).map Fin.val); sourceRows := (List.finRange source.clauses.size).map (fun i => (record.sourceRows i).map Fin.val); expectedRows := (List.finRange record.expected.clauses.size).map (fun i => (record.expectedRows i).val)
end Record namespace SerializedRecord
def decodeID (bound value : Nat) : Option (Fin bound) := if valid : value < bound then some ⟨value, valid⟩ else none
def decodeLiteral (bound : Nat) (literal : Nat × Bool) : Option (Literal (Fin bound)) := do
  let coordinate ← decodeID bound literal.1
  pure (coordinate, literal.2)
def decodeVector {α : Type} (count : Nat) (values : List α) : Option (Fin count → α) :=
  if lengthMatches : values.length = count then some (fun i => values[i.val]'(by omega))
  else none
def decodeOptionalID (bound : Nat) : Option Nat → Option (Option (Fin bound)) | none => some none | some value => (decodeID bound value).map some
def decodeRaw {original : Nat} (source : Formula (Fin original)) (recovered : Nat) (payload : SerializedRecord) : Option (Record source recovered) := do
  let expectedClauses ← payload.expectedClauses.mapM
    (fun clause => clause.mapM (decodeLiteral recovered))
  let expected := ofClauses expectedClauses
  let coordinates ← payload.coordinates.mapM (decodeID recovered)
  let coordinate ← decodeVector original coordinates
  let phase ← decodeVector original payload.phases
  let anchors ← payload.anchors.mapM (decodeID original)
  let anchor ← decodeVector recovered anchors
  let originLists ← payload.aliasOrigins.mapM
    (fun origins => origins.mapM (decodeID source.clauses.size))
  let aliases ← decodeVector original originLists
  let rowChoices ← payload.sourceRows.mapM (decodeOptionalID expected.clauses.size)
  let sourceRows ← decodeVector source.clauses.size rowChoices
  let rowOrigins ← payload.expectedRows.mapM (decodeID source.clauses.size)
  let expectedRows ← decodeVector expected.clauses.size rowOrigins
  pure { expected, coordinate, phase, anchor, aliases, sourceRows, expectedRows }
end SerializedRecord namespace FamilyRecord
structure Roles (params : Native.Parameters) (recovered : Nat) where
  (identify : Native.Variable params → Fin recovered) (name : Fin recovered → Native.Variable params) (phase : Native.Variable params → Bool)
namespace Roles variable {params : Native.Parameters} {recovered : Nat}
def Valid (roles : Roles params recovered) : Prop := (∀ named, roles.name (roles.identify named) = named) ∧ (∀ index, roles.identify (roles.name index) = index)
instance (roles : Roles params recovered) : Decidable roles.Valid := by
  unfold Valid
  infer_instance
def check (roles : Roles params recovered) : Bool := decide roles.Valid
end Roles end FamilyRecord
structure SerializedChainedRecord where
  (base : SerializedRecord) (edges : List ((Nat × Nat) × Bool)) (origins : List (List Nat)) (paths : List (List (Nat × Bool)))
  deriving DecidableEq
namespace AliasTrace.Record variable {original recovered : Nat} {source : Formula (Fin original)}
def serialize (record : AliasTrace.Record source recovered) : SerializedChainedRecord where
  base := record.base.serialize; edges := record.edges.map fun edge => ((edge.left.val, edge.right.val), edge.phase); origins := (List.finRange record.edges.length).map fun i => (record.origins i).map Fin.val; paths := (List.finRange original).map fun i => (record.paths i).map fun step => (step.1.val, step.2)
def serializedCheck (record : AliasTrace.Record source recovered) (payload : SerializedChainedRecord) : Bool := decide (payload = record.serialize) && record.check
end AliasTrace.Record namespace SerializedChainedRecord
def decodeEdge (original : Nat) (edge : (Nat × Nat) × Bool) : Option (AliasEdge (Fin original)) := do
  let left ← SerializedRecord.decodeID original edge.1.1
  let right ← SerializedRecord.decodeID original edge.1.2
  pure ⟨left, right, edge.2⟩
def decodeRaw {original : Nat} (source : Formula (Fin original)) (recovered : Nat) (payload : SerializedChainedRecord) : Option (AliasTrace.Record source recovered) := do
  let base ← SerializedRecord.decodeRaw source recovered payload.base
  let edges ← payload.edges.mapM (decodeEdge original)
  let decodedOrigins ← payload.origins.mapM fun row => row.mapM (SerializedRecord.decodeID source.clauses.size)
  let origins ← SerializedRecord.decodeVector edges.length decodedOrigins
  let decodedPaths ← payload.paths.mapM fun path =>
    path.mapM fun step => do
      let index ← SerializedRecord.decodeID edges.length step.1
      pure (index, step.2)
  let paths ← SerializedRecord.decodeVector original decodedPaths
  pure ⟨base, edges, origins, paths⟩
def decodeChecked {original : Nat} (source : Formula (Fin original)) (recovered : Nat) (payload : SerializedChainedRecord) : Option (AliasTrace.Record source recovered) := match decodeRaw source recovered payload with | none => none | some record => if record.serializedCheck payload then some record else none
end SerializedChainedRecord
structure SerializedRoles where
  (coordinates : List Nat) (names : List Nat) (phases : List Bool)
  deriving DecidableEq
namespace FamilyRecord.Roles variable {params : Native.Parameters} {recovered : Nat}
def serialize (roles : FamilyRecord.Roles params recovered) : SerializedRoles where
  coordinates := params.variableRoles.map fun role => (roles.identify role).val; names := (List.finRange recovered).map fun i => params.variableRoles.idxOf (roles.name i); phases := params.variableRoles.map roles.phase
def serializedCheck (roles : FamilyRecord.Roles params recovered) (payload : SerializedRoles) : Bool := decide (payload = roles.serialize) && roles.check
end FamilyRecord.Roles namespace SerializedRoles
def roleIndex (params : Native.Parameters) (role : Native.Variable params) : Fin params.variableRoles.length := ⟨params.variableRoles.idxOf role, List.idxOf_lt_length_of_mem (params.mem_variableRoles role)⟩
def decodeRaw (params : Native.Parameters) (recovered : Nat) (payload : SerializedRoles) : Option (FamilyRecord.Roles params recovered) := do
  let decodedIDs ← payload.coordinates.mapM (SerializedRecord.decodeID recovered)
  let coordinates ← SerializedRecord.decodeVector params.variableRoles.length decodedIDs
  let decodedNames ← payload.names.mapM
    (SerializedRecord.decodeID params.variableRoles.length)
  let names ← SerializedRecord.decodeVector recovered decodedNames
  let phases ← SerializedRecord.decodeVector params.variableRoles.length payload.phases
  pure {
    identify := fun role => coordinates (roleIndex params role)
    name := fun index => params.variableRoles.get (names index)
    phase := fun role => phases (roleIndex params role) }
def decodeChecked (params : Native.Parameters) (recovered : Nat) (payload : SerializedRoles) : Option (FamilyRecord.Roles params recovered) := match decodeRaw params recovered payload with | none => none | some roles => if roles.serializedCheck payload then some roles else none
end SerializedRoles namespace PrivateFamily
open Controller.Certificate
structure Cuts (left right : Formula (Fin count)) where
  (forward : Fin right.clauses.size → Certificate count) (backward : Fin left.clauses.size → Certificate count)
namespace Cuts variable {count : Nat} {left right : Formula (Fin count)}
def check (cuts : Cuts left right) : Bool := decide (∀ i, Attachment.entailCheck left right.clauses[i] (cuts.forward i) = true) && decide (∀ i, Attachment.entailCheck right left.clauses[i] (cuts.backward i) = true)
end Cuts
structure Partition (boundary auxCount recovered : Nat) where
  (identify : Fin boundary ⊕ Fin auxCount → Fin recovered) (name : Fin recovered → Fin boundary ⊕ Fin auxCount) (phase : Fin boundary ⊕ Fin auxCount → Bool)
namespace Partition variable {boundary auxCount recovered : Nat}
def Valid (partition : Partition boundary auxCount recovered) : Prop := (∀ coordinate, partition.name (partition.identify coordinate) = coordinate) ∧ (∀ index, partition.identify (partition.name index) = index)
instance (partition : Partition boundary auxCount recovered) : Decidable partition.Valid := by
  unfold Valid
  infer_instance
def check (partition : Partition boundary auxCount recovered) : Bool := decide partition.Valid
end Partition
def driveFormula (params : Native.Parameters) : Formula (Native.Variable params) := params.equationFormula ++ ofClauses ((params.assertions.take 3).map fun literal => [literal])
structure Record (source : Formula (Fin original)) (recovered : Nat)
  (params : Native.Parameters) (boundary auxCount : Nat) where
  (aliases : AliasTrace.Record source recovered) (roles : FamilyRecord.Roles params boundary) (partition : Partition boundary auxCount recovered) (wrapper : Attachment.WrapperRecord boundary auxCount params.decoder.roots.length) (targetLink : Attachment.TargetLink.Record boundary params.decoder.roots.length) (metadata : ProducerMetadata.Record wrapper.definitions) (namedDrive : Formula (Fin boundary)) (bundle : Formula (Fin recovered))
  (coreCuts : Cuts wrapper.definitions namedDrive) (sourceCuts : Cuts aliases.base.expected bundle)
namespace Record variable {original recovered boundary auxCount : Nat} {source : Formula (Fin original)} {params : Native.Parameters}
def signalBundle (record : Record source recovered params boundary auxCount) : Formula (Fin boundary ⊕ Fin auxCount) := relabel Sum.inl record.wrapper.definitions ++ record.wrapper.wrapper
def physicalPairs (record : Record source recovered params boundary auxCount) (i : Fin params.decoder.roots.length) : Literal (Fin boundary) × Literal (Fin boundary) := (signedLiteral record.roles.identify record.roles.phase (Native.Parameters.internal params (.decoder .healthy (params.decoder.roots.get i))), signedLiteral record.roles.identify record.roles.phase (Native.Parameters.internal params (.decoder .faulty (params.decoder.roots.get i))))
def physicalRoots (record : Record source recovered params boundary auxCount) : Finset (Fin boundary) := (params.primaryRoles.map fun role => record.roles.identify (.primary role)).toFinset
def Checks (record : Record source recovered params boundary auxCount) : Prop := record.aliases.check = true ∧ record.roles.check = true ∧ record.partition.check = true ∧ record.coreCuts.check = true ∧ record.sourceCuts.check = true ∧ record.wrapper.check = true ∧ record.targetLink.check = true ∧ record.metadata.check = true ∧ record.namedDrive.clauses = (signedRelabel record.roles.identify record.roles.phase (driveFormula params)).clauses ∧ record.bundle.clauses = (signedRelabel record.partition.identify record.partition.phase record.signalBundle).clauses ∧ record.targetLink.definitions.clauses = record.wrapper.definitions.clauses ∧ record.targetLink.pairs = record.wrapper.pairs ∧ record.targetLink.selected = record.wrapper.selected ∧ record.targetLink.target = signedLiteral record.roles.identify record.roles.phase (Native.Parameters.internal params .detected) ∧ record.wrapper.pairs = record.physicalPairs ∧ record.wrapper.selected = List.finRange params.decoder.roots.length ∧ record.metadata.roots = record.physicalRoots
instance (record : Record source recovered params boundary auxCount) : Decidable record.Checks := by
  unfold Checks
  infer_instance
def check (record : Record source recovered params boundary auxCount) : Bool := decide record.Checks
def signalsOfNative (record : Record source recovered params boundary auxCount) (assignment : Native.Variable params → Bool) : Fin boundary → Bool := fun index => assignment (record.roles.name index) == record.roles.phase (record.roles.name index)
def liftNative (record : Record source recovered params boundary auxCount) (assignment : Native.Variable params → Bool) : Fin original → Bool :=
  let signals := record.signalsOfNative assignment
  let joined := Native.ObservationProjection.joint signals (record.wrapper.extension signals)
  record.aliases.base.lift (fun index => joined (record.partition.name index) ==
    record.partition.phase (record.partition.name index))
end Record
structure SerializedPartition where
  (coordinates : List Nat) (names : List Nat) (phases : List Bool)
  deriving DecidableEq
namespace Partition variable {boundary auxCount recovered : Nat}
def serialize (partition : Partition boundary auxCount recovered) : SerializedPartition where
  coordinates := (List.finRange (boundary + auxCount)).map fun index => (partition.identify (finSumFinEquiv.symm index)).val; names := (List.finRange recovered).map fun index => (finSumFinEquiv (partition.name index)).val; phases := (List.finRange (boundary + auxCount)).map fun index => partition.phase (finSumFinEquiv.symm index)
def serializedCheck (partition : Partition boundary auxCount recovered) (payload : SerializedPartition) : Bool := decide (payload = partition.serialize) && partition.check
end Partition namespace SerializedPartition
def decodeRaw (boundary auxCount recovered : Nat) (payload : SerializedPartition) : Option (Partition boundary auxCount recovered) := do
  let decodedIDs ← payload.coordinates.mapM (SerializedRecord.decodeID recovered)
  let coordinates ← SerializedRecord.decodeVector (boundary + auxCount) decodedIDs
  let decodedNames ← payload.names.mapM (SerializedRecord.decodeID (boundary + auxCount))
  let names ← SerializedRecord.decodeVector recovered decodedNames
  let phases ← SerializedRecord.decodeVector (boundary + auxCount) payload.phases
  pure {
    identify := fun coordinate => coordinates (finSumFinEquiv coordinate)
    name := fun index => finSumFinEquiv.symm (names index)
    phase := fun coordinate => phases (finSumFinEquiv coordinate) }
def decodeChecked (boundary auxCount recovered : Nat) (payload : SerializedPartition) : Option (Partition boundary auxCount recovered) := match decodeRaw boundary auxCount recovered payload with | none => none | some partition => if partition.serializedCheck payload then some partition else none
end SerializedPartition
structure CompletePayload (source : Formula (Fin original)) (recovered : Nat)
  (params : Native.Parameters) (boundary auxCount : Nat) where
  (aliases : SerializedChainedRecord) (roles : SerializedRoles) (partition : SerializedPartition) (expected : Formula (Fin recovered)) (wrapper : Attachment.WrapperRecord boundary auxCount params.decoder.roots.length) (targetLink : Attachment.TargetLink.Record boundary params.decoder.roots.length) (metadata : ProducerMetadata.Record wrapper.definitions) (namedDrive : Formula (Fin boundary)) (bundle : Formula (Fin recovered))
  (coreCuts : Cuts wrapper.definitions namedDrive) (sourceCuts : Cuts expected bundle)
namespace CompletePayload variable {original recovered boundary auxCount : Nat} {source : Formula (Fin original)} {params : Native.Parameters}
theorem formula_of_rows {left right : Formula α} (same : left.clauses = right.clauses) : left = right := by cases left; cases right; exact congrArg Controller.CNF.OrderedFormula.mk same
def decodeRaw (payload : CompletePayload source recovered params boundary auxCount) : Option (Record source recovered params boundary auxCount) := do
  let aliases ← SerializedChainedRecord.decodeChecked source recovered payload.aliases
  let roles ← SerializedRoles.decodeChecked params boundary payload.roles
  let partition ← SerializedPartition.decodeChecked boundary auxCount recovered payload.partition
  if rows : aliases.base.expected.clauses = payload.expected.clauses then
    let same := formula_of_rows rows
    pure {
      aliases := aliases
      roles := roles
      partition := partition
      wrapper := payload.wrapper
      targetLink := payload.targetLink
      metadata := payload.metadata
      namedDrive := payload.namedDrive
      bundle := payload.bundle
      coreCuts := payload.coreCuts
      sourceCuts := same.symm ▸ payload.sourceCuts }
  else none
def decodeChecked (payload : CompletePayload source recovered params boundary auxCount) : Option (Record source recovered params boundary auxCount) := match payload.decodeRaw with | none => none | some record => if record.check then some record else none
end CompletePayload end PrivateFamily end Controller.Recognition source_context "Controller.Recognition.FamilyRecord" namespace Controller.Recognition.GuardedFamily open Controller.Decoder Controller.CNF
def guardedCheck (graph : DAG n) : Bool := (List.finRange graph.nodeCount).all fun i => !(graph.node i).isLiveAnd
def decodeChecked (payload : PrivateFamily.CompletePayload source recovered params boundary auxCount) : Option (PrivateFamily.Record source recovered params boundary auxCount) := if guardedCheck params.decoder then payload.decodeChecked else none
/-- Typed projection and certificate law. -/ theorem decodeChecked_sound (payload : PrivateFamily.CompletePayload source recovered params boundary auxCount) (record : PrivateFamily.Record source recovered params boundary auxCount) (accepted : decodeChecked payload = some record) : params.decoder.Guarded ∧ record.check = true ∧ (Satisfiable source ↔ Physical.BridgeDetectable (b := params.buses) params.bridge params.drive params.observations) := by sorry
/-- Typed projection and certificate law. -/ theorem decodeChecked_lifting (payload : PrivateFamily.CompletePayload source recovered params boundary auxCount) (record : PrivateFamily.Record source recovered params boundary auxCount) (accepted : decodeChecked payload = some record) (assignment : Native.Variable params → Bool) (model : Satisfies assignment params.specificationFormula) : Satisfies (record.liftNative assignment) source := by sorry
/-- An accepted positive-output wrapper needs more source coordinates than native variables. -/ theorem decodeChecked_requires_extra_coordinates {original recovered boundary auxCount : Nat} {source : Formula (Fin original)} {params : Native.Parameters} (payload : PrivateFamily.CompletePayload source recovered params boundary auxCount) (record : PrivateFamily.Record source recovered params boundary auxCount) (positive : 0 < params.decoder.roots.length) (accepted : decodeChecked payload = some record) : Fintype.card (Native.Variable params) < original := by sorry
end Controller.Recognition.GuardedFamily source_context "Controller.Certificate.InputBinding" namespace Controller.Certificate
open Controller.CNF
structure InputPacket where
  (declaredVariables : ℕ) (rows : List (List (ℕ × Bool)))
  deriving DecidableEq
namespace InputPacket
def encodeLiteral (literal : Literal (Fin varCount)) : ℕ × Bool := (literal.1.val, literal.2)
def decodeLiteral (varCount : ℕ) (literal : ℕ × Bool) : Option (Literal (Fin varCount)) := if lower : literal.1 < varCount then some (⟨literal.1, lower⟩, literal.2) else none
def decodeClause (varCount : ℕ) : List (ℕ × Bool) → Option (Clause (Fin varCount))
  | [] => some []
  | literal :: rest => do
    let decoded ← decodeLiteral varCount literal
    let tail ← decodeClause varCount rest
    pure (decoded :: tail)
def decodeRows (varCount : ℕ) : List (List (ℕ × Bool)) → Option (List (Clause (Fin varCount)))
  | [] => some []
  | clause :: rest => do
    let decoded ← decodeClause varCount clause
    let tail ← decodeRows varCount rest
    pure (decoded :: tail)
def serialize (source : FiniteFormula varCount) : InputPacket := ⟨varCount, source.clauses.toList.map (List.map encodeLiteral)⟩
def decode (varCount : ℕ) (packet : InputPacket) : Option (FiniteFormula varCount) := if packet.declaredVariables = varCount then (decodeRows varCount packet.rows).map ofClauses else none
end InputPacket
inductive SubmittedInput where
  | structured (packet : InputPacket) | dimacsText (text : String) | jsonText (text : String)
def checkPacket (source : FiniteFormula varCount) (packet : InputPacket) (certificate : Certificate varCount) : Bool := if packet = InputPacket.serialize source then match InputPacket.decode varCount packet with | none => false | some decoded => checkTyped decoded certificate else false
def checkSubmitted (source : FiniteFormula varCount) (input : SubmittedInput) (certificate : Certificate varCount) : Bool := match input with | .structured packet => checkPacket source packet certificate | .dimacsText _ => false | .jsonText _ => false
end Controller.Certificate source_context "Controller.Certificate.ModelCheck" namespace Controller.Certificate.ModelCheck
open Controller
def check (formula : CNF.Formula α) (assignment : α → Bool) : Bool := Controller.CNF.OrderedFormula.eval assignment formula
end Controller.Certificate.ModelCheck source_context "Controller.Horn.GreatestModel" namespace Controller.Horn
open CNF
def forceFalse [DecidableEq α] (current : α → Bool) (i : α) : α → Bool := fun j => if j = i then false else current j
end Controller.Horn source_context "Controller.Decoder.ZeroSystem" namespace Controller.Decoder.ZeroSystem
open CNF
def positiveClause (entries : List α) : Clause α := entries.map (fun v => (v, true))
def implicationClause (premise : α) (alternatives : List α) : Clause α := (premise, false) :: positiveClause alternatives
end Controller.Decoder.ZeroSystem namespace Controller.Decoder.DAG
open CNF ZeroSystem
variable {n : ℕ}
abbrev ZeroVar (graph : DAG n) := Channel n ⊕ Fin graph.nodeCount
def nodeClauses (graph : DAG n) (index : Fin graph.nodeCount) : List (Clause graph.ZeroVar) := match graph.node index with | .zero => [implicationClause (.inr index) []] | .input channel => [implicationClause (.inl channel) [.inr index], implicationClause (.inr index) [.inl channel]] | .disj refs => refs.map fun child => implicationClause (.inr (graph.childIndex index child)) [.inr index] | .guard child labels => [implicationClause (.inr (graph.childIndex index child)) (labels.map Sum.inl ++ [.inr index])] | .liveAnd left right => [[(.inr (graph.childIndex index left), false), (.inr (graph.childIndex index right), false), (.inr index, true)]]
def forwardClauses (graph : DAG n) : List (Clause graph.ZeroVar) := (List.finRange graph.nodeCount).flatMap graph.nodeClauses
end Controller.Decoder.DAG namespace Controller.Decoder.DAG
open CNF ZeroSystem
variable {n : ℕ}
def trueUnitClauses (graph : DAG n) (T : Finset (Channel n)) : List (Clause graph.ZeroVar) := ((List.finRange n).filter fun channel => decide (channel ∈ T)).map fun channel => positiveClause [.inl channel]
def falseUnitClauses (graph : DAG n) (F : Finset (Channel n)) : List (Clause graph.ZeroVar) := ((List.finRange n).filter fun channel => decide (channel ∈ F)).map fun channel => implicationClause (.inl channel) []
def channelClauses (graph : DAG n) (b : ℕ) (target : Channel n) (T F : Finset (Channel n)) : List (Clause graph.ZeroVar) := (([positiveClause ((List.finRange n).map Sum.inl)] ++ (if b = 1 then [positiveClause [.inl target]] else [])) ++ graph.trueUnitClauses T) ++ graph.falseUnitClauses F
def zeroSystem (graph : DAG n) (b : ℕ) (target : Channel n) (root : Fin graph.nodeCount) (T F : Finset (Channel n)) : Formula graph.ZeroVar := ofClauses ((graph.forwardClauses ++ graph.channelClauses b target T F) ++ [implicationClause (.inr root) []])
def zeroChannelSet (graph : DAG n) (assignment : graph.ZeroVar → Bool) : Finset (Channel n) := setOfAssignment (fun channel => assignment (.inl channel))
end Controller.Decoder.DAG source_context "Controller.Horn.Rules" namespace Controller.Horn.Worklist
open CNF
inductive Rule (α : Type*) where
  | skip | positive (positive : List α) | negative (head : α) (positive : List α)
  deriving DecidableEq, Repr
namespace Rule
def positives : Rule α → List α | .skip => [] | .positive labels => labels | .negative _ labels => labels
def Holds (assignment : α → Bool) : Rule α → Prop
  | .skip => True
  | .positive labels => ∃ label ∈ labels, assignment label = true
  | .negative head labels => assignment head = false ∨ ∃ label ∈ labels, assignment label = true
end Rule variable [DecidableEq α]
def signedLabels (clause : Clause α) (polarity : Bool) : List α := ((clause.filter fun literal => decide (literal.2 = polarity)).map Prod.fst).dedup
def tautologyCheck (clause : Clause α) : Bool := clause.any fun literal => clause.contains (negate literal)
def compileClause (clause : Clause α) : Rule α := if tautologyCheck clause then .skip else match signedLabels clause false with | [] => .positive (signedLabels clause true) | head :: _ => .negative head (signedLabels clause true)
def compileFormula (formula : Formula α) : Array (Rule α) := formula.clauses.map compileClause
@[simp] theorem compileFormula_size (formula : Formula α) :
    (compileFormula formula).size = formula.clauses.size := by simp [compileFormula]
end Controller.Horn.Worklist source_context "Controller.Horn.IndexedState" namespace Controller.Horn.Worklist
abbrev RuleTable (n m : Nat) := Vector (Rule (Fin n)) m
def normalizedTable (formula : CNF.Formula (Fin n)) : RuleTable n formula.clauses.size := ⟨compileFormula formula, compileFormula_size formula⟩
def Normalized (rules : RuleTable n m) : Prop := ∀ row : Fin m, (rules[row.val]).positives.Nodup
def positiveIncidences (rules : RuleTable n m) : List (Fin n × Fin m) := (List.finRange m).flatMap fun row => (rules[row.val]).positives.map fun label => (label, row)
def bucketIncidences : List (Fin n × Fin m) → Vector (List (Fin m)) n
  | [] => Vector.replicate n []
  | (label, row) :: rest =>
      let table := bucketIncidences rest
      table.set label.val (row :: table[label.val]) label.isLt
def occurrences (rules : RuleTable n m) : Vector (List (Fin m)) n := bucketIncidences (positiveIncidences rules)
theorem countP_forceFalse [DecidableEq α] (labels : List α) (noDuplicates : labels.Nodup) (assignment : α → Bool) (label : α) : labels.countP (forceFalse assignment label) = labels.countP assignment - if label ∈ labels ∧ assignment label = true then 1 else 0 := by
  calc
    labels.countP (forceFalse assignment label) = (labels.erase label).countP assignment := by
      rw [noDuplicates.erase_eq_filter, List.countP_filter]
      apply List.countP_congr
      intro current _
      by_cases equal : current = label <;> simp [forceFalse, equal]
    _ = _ := List.countP_erase assignment labels label
structure CountedState (n m : Nat) where
  (values : Vector Bool n) (counts : Vector Nat m)
namespace CountedState
def assignment (state : CountedState n m) : Fin n → Bool := fun label => state.values[label.val]
def initial (rules : RuleTable n m) : CountedState n m where
  values := Vector.replicate n true; counts := Vector.ofFn fun row => (rules[row.val]).positives.length
end CountedState
def decrementRows : List (Fin m) → Vector Nat m → Vector Nat m | [], counts => counts | row :: rest, counts => decrementRows rest (counts.set row.val (counts[row.val] - 1) row.isLt)
namespace CountedState
def turnOff (index : Vector (List (Fin m)) n) (state : CountedState n m) (label : Fin n) : CountedState n m where
  values := state.values.set label.val false label.isLt; counts := decrementRows index[label.val] state.counts
@[simp] theorem turnOff_assignment (index : Vector (List (Fin m)) n)
    (state : CountedState n m) (label : Fin n) :
    (turnOff index state label).assignment = forceFalse state.assignment label := by
  funext current
  simp only [assignment, turnOff, Vector.getElem_set, forceFalse]
  by_cases equal : current = label
  · subst current
    simp
  · have unequalValues : label.val ≠ current.val :=
      fun same => equal (Fin.ext same.symm)
    simp [equal, unequalValues]
end CountedState end Controller.Horn.Worklist source_context "Controller.Horn.Worklist" namespace Controller.Horn.Worklist
def Models (rules : RuleTable n m) (assignment : Fin n → Bool) : Prop := ∀ row : Fin m, (rules[row.val]).Holds assignment
structure Agenda (m : Nat) where
  (fired : Vector Bool m) (pending : List (Fin m)) (failed : Bool)
namespace Agenda
def empty (m : Nat) : Agenda m where
  fired := Vector.replicate m false; pending := []; failed := false
def schedule (rules : RuleTable n m) (counted : CountedState n m) (row : Fin m) (agenda : Agenda m) : Agenda m :=
  if counted.counts[row.val] = 0 ∧ agenda.fired[row.val] = false then
    match rules[row.val] with
    | .skip => agenda
    | .positive _ => { agenda with fired := agenda.fired.set row.val true row.isLt, failed := true }
    | .negative _ _ =>
        { agenda with
          fired := agenda.fired.set row.val true row.isLt
          pending := row :: agenda.pending }
  else agenda
def scheduleRows (rules : RuleTable n m) (counted : CountedState n m) : List (Fin m) → Agenda m → Agenda m | [], agenda => agenda | row :: rest, agenda => scheduleRows rules counted rest (schedule rules counted row agenda)
end Agenda
structure State (n m : Nat) where
  (counted : CountedState n m) (agenda : Agenda m)
namespace State
def initial (rules : RuleTable n m) : State n m where
  counted := CountedState.initial rules
  agenda := Agenda.scheduleRows rules (CountedState.initial rules) (List.finRange m)
    (Agenda.empty m)
def propagate (rules : RuleTable n m) (index : Vector (List (Fin m)) n) (state : State n m) (head : Fin n) (rest : List (Fin m)) : State n m :=
  let counted := state.counted.turnOff index head
  let agenda := { state.agenda with pending := rest }
  { counted := counted, agenda := Agenda.scheduleRows rules counted index[head.val] agenda }
def discard (state : State n m) (rest : List (Fin m)) : State n m := { state with agenda := { state.agenda with pending := rest } }
def remaining (state : State n m) : Nat := (List.finRange n).countP state.counted.assignment
theorem propagate_remaining_lt (rules : RuleTable n m) (index : Vector (List (Fin m)) n) (state : State n m) (head : Fin n) (rest : List (Fin m)) (wasTrue : state.counted.assignment head = true) : remaining (propagate rules index state head rest) < remaining state := by
  have positive : 0 < remaining state := List.countP_pos_iff.mpr ⟨head, List.mem_finRange head, wasTrue⟩
  change (List.finRange n).countP (state.counted.turnOff index head).assignment < remaining state
  rw [CountedState.turnOff_assignment, countP_forceFalse _ (List.nodup_finRange n)]
  simp only [List.mem_finRange, wasTrue, and_self, ite_true]
  exact Nat.sub_lt positive (by decide)
def run (rules : RuleTable n m) (index : Vector (List (Fin m)) n) (state : State n m) : Option (Vector Bool n) :=
  if state.agenda.failed then none
  else match pendingEquation : state.agenda.pending with
    | [] => some state.counted.values
    | row :: rest =>
      match rules[row.val] with
      | .negative head _ =>
        if wasTrue : state.counted.assignment head = true then run rules index (propagate rules index state head rest)
        else run rules index (discard state rest)
      | _ => run rules index (discard state rest)
termination_by (remaining state, state.agenda.pending.length)
decreasing_by
  all_goals first
    | exact Prod.Lex.left _ _ (propagate_remaining_lt rules index state head rest wasTrue)
    | apply Prod.Lex.right
      simp only [discard, pendingEquation, List.length_cons, Nat.lt_add_one._simp_1]
end State
def solveRules (rules : RuleTable n m) : Option (Vector Bool n) :=
  let index := occurrences rules
  State.run rules index (State.initial rules)
end Controller.Horn.Worklist source_context "Controller.Horn.WorklistCorrect" namespace Controller.Horn.Worklist
open CNF
def solveFormula (formula : Formula (Fin n)) : Option (Vector Bool n) := solveRules (normalizedTable formula)
end Controller.Horn.Worklist source_context "Controller.Decoder.Detect" namespace Controller.Decoder
def trueCandidate (b : Nat) (target head : Channel n) : Finset (Channel n) := if b = 1 then {head, target} else {head}
namespace DAG
def zeroIndex (graph : DAG n) : graph.ZeroVar ≃ Fin (n + graph.nodeCount) := finSumFinEquiv
def finiteZeroSystem (graph : DAG n) (b : Nat) (target : Channel n) (root : Fin graph.nodeCount) (T F : Finset (Channel n)) : CNF.FiniteFormula (n + graph.nodeCount) := CNF.relabel graph.zeroIndex (graph.zeroSystem b target root T F)
def solveZero (graph : DAG n) (b : Nat) (target : Channel n) (root : Fin graph.nodeCount) (T F : Finset (Channel n)) : Option (Finset (Channel n)) := (Horn.Worklist.solveFormula (graph.finiteZeroSystem b target root T F)).map (fun values => graph.zeroChannelSet (fun coordinate => values[(graph.zeroIndex coordinate).val]))
def firstSuccess (query : α → Option β) : List α → Option β | [] => none | head :: tail => match query head with | some value => some value | none => firstSuccess query tail
def trueQuery (graph : DAG n) (b : Nat) (target : Channel n) (healthy : Fin graph.nodeCount → Bool) (head : Channel n) : Option (Finset (Channel n)) :=
  let candidate := trueCandidate b target head
  let values := graph.evalTable (assignmentOfSet candidate)
  if graph.roots.any (fun root => !healthy root && values root) then some candidate else none
def zeroQuery (graph : DAG n) (b : Nat) (target : Channel n) (healthy : Fin graph.nodeCount → Bool) (root : Fin graph.nodeCount) : Option (Finset (Channel n)) := if healthy root then graph.solveZero b target root ∅ ∅ else none
def scanCandidates (graph : DAG n) (b : Nat) (target : Channel n) (healthy : Fin graph.nodeCount → Bool) : Option (Finset (Channel n)) := if graph.roots.all healthy then none else firstSuccess (graph.trueQuery b target healthy) (List.finRange n)
def detectSet (graph : DAG n) (b : Nat) (target : Channel n) (drive : Bool) : Option (Finset (Channel n)) :=
  if drive then
    let healthy := graph.evalTable (assignmentOfSet {target})
    match graph.scanCandidates b target healthy with
    | some K => some K
    | none => firstSuccess (graph.zeroQuery b target healthy) graph.roots
  else none
end DAG end Controller.Decoder source_context "Controller.Physical.Realize" namespace Controller.Physical
def realizeTailRequests {n : ℕ} (target : Channel n) (K : Finset (Channel n)) :
    (b : ℕ) → Fin b → Assignment n
  | 0 => Fin.elim0
  | _ + 1 => Fin.cases (if target ∈ K then (fun _ => false) else assignmentOfSet K)
      (fun _ _ => false)
def realizeRequests {n : ℕ} (target : Channel n) (K : Finset (Channel n)) :
    (b : ℕ) → Fin b → Assignment n
  | 0 => Fin.elim0
  | b + 1 => Fin.cases (assignmentOfSet {target}) (realizeTailRequests target K b)
def realizeBridge {n b : ℕ} (bridge : Bridge n) (hb : 0 < b) (K : Finset (Channel n)) : PrimaryInput n b where
  positiveBuses := hb; enable := assignmentOfSet (insert bridge.target K); request := realizeRequests bridge.target K b
end Controller.Physical source_context "Controller.Physical.DetectCorrect" namespace Controller.Physical
def detectInput {n b : Nat} (bridge : Bridge n) (hb : 0 < b) (drive : Bool) (graph : Decoder.DAG n) : Option (PrimaryInput n b) := (graph.detectSet b bridge.target drive).map (realizeBridge bridge hb)
end Controller.Physical source_context "Controller.Native.Lift" namespace Controller.Native.Lift
open Controller
def named (params : Parameters) (input : Physical.PrimaryInput params.channels params.buses) (wire : Bool) := params.physicalAssignment input wire
def detectNamed (params : Parameters) := (Physical.detectInput params.bridge params.positiveBuses params.drive params.decoder).map (fun input => named params input true)
end Controller.Native.Lift source_context "Controller.Certificate.Pipeline" namespace Controller.Certificate.Pipeline
open Controller Controller.CNF
inductive Candidate (varCount : Nat) where
  | sat (assignment : Fin varCount → Bool) | unsat (certificate : Certificate varCount) | outside | invalid | timeout
inductive Verdict where
  | sat | unsat | outside | invalid | timeout
  deriving DecidableEq, Repr
def checkModelInput (source : FiniteFormula varCount) (input : SubmittedInput) (assignment : Fin varCount → Bool) : Bool := match input with | .structured packet => if packet = InputPacket.serialize source then ModelCheck.check source assignment else false | .dimacsText _ | .jsonText _ => false
def validate (source : FiniteFormula varCount) (input : SubmittedInput) : Candidate varCount → Verdict | .sat assignment => if checkModelInput source input assignment then .sat else .invalid | .unsat certificate => if checkSubmitted source input certificate then .unsat else .invalid | .outside => .outside | .invalid => .invalid | .timeout => .timeout
def familyCandidate {source : FiniteFormula varCount} (payload : Recognition.PrivateFamily.CompletePayload source recovered params boundary auxCount) (refutation : Option (Certificate varCount)) : Candidate varCount := match Recognition.GuardedFamily.decodeChecked payload with | none => .outside | some record => match Native.Lift.detectNamed params with | some assignment => .sat (record.liftNative assignment) | none => match refutation with | some certificate => .unsat certificate | none => .timeout
def runFamily (source : FiniteFormula varCount) (input : SubmittedInput) (payload : Recognition.PrivateFamily.CompletePayload source recovered params boundary auxCount) (refutation : Option (Certificate varCount)) : Verdict := validate source input (familyCandidate payload refutation)
/-- Typed projection and certificate law. -/ theorem runFamily_sat_sound (source : FiniteFormula varCount) (input : SubmittedInput) (payload : Recognition.PrivateFamily.CompletePayload source recovered params boundary auxCount) (refutation : Option (Certificate varCount)) (accepted : runFamily source input payload refutation = .sat) : Satisfiable source := by sorry
/-- Typed projection and certificate law. -/ theorem runFamily_unsat_sound (source : FiniteFormula varCount) (input : SubmittedInput) (payload : Recognition.PrivateFamily.CompletePayload source recovered params boundary auxCount) (refutation : Option (Certificate varCount)) (accepted : runFamily source input payload refutation = .unsat) : Unsatisfiable source := by sorry
/-- Typed projection and certificate law. -/ theorem runFamily_sat_iff (source : FiniteFormula varCount) (payload : Recognition.PrivateFamily.CompletePayload source recovered params boundary auxCount) (record : Recognition.PrivateFamily.Record source recovered params boundary auxCount) (recognized : Recognition.GuardedFamily.decodeChecked payload = some record) (refutation : Option (Certificate varCount)) : runFamily source (.structured (InputPacket.serialize source)) payload refutation = .sat ↔ Satisfiable source := by sorry
/-- Typed projection and certificate law. -/ theorem runFamily_certified_unsat (source : FiniteFormula varCount) (payload : Recognition.PrivateFamily.CompletePayload source recovered params boundary auxCount) (record : Recognition.PrivateFamily.Record source recovered params boundary auxCount) (recognized : Recognition.GuardedFamily.decodeChecked payload = some record) (certificate : Certificate varCount) (checked : checkTyped source certificate = true) : runFamily source (.structured (InputPacket.serialize source)) payload (some certificate) = .unsat := by sorry
end Controller.Certificate.Pipeline end_source_context source_context "Controller.Recognition.ObservationDetection" namespace Controller.Recognition.ObservationDetection open Controller.CNF Controller.Native.ObservationProjection
def observedPair (params : Native.Parameters)
    (i : Fin params.decoder.roots.length) :
    Literal (Native.Variable params) × Literal (Native.Variable params) :=
  (Native.Parameters.internal params (.decoder .healthy (params.decoder.roots.get i)),
   Native.Parameters.internal params (.decoder .faulty (params.decoder.roots.get i)))
/-- The guarded detector decides the represented optional-wrapper family. -/ theorem optional_native_decision [Fintype ι] (params : Native.Parameters) (guarded : params.decoder.Guarded) (wrapper : OptionalWrapper (Native.Variable params) ι (Fin params.decoder.roots.length)) (declared : wrapper.DeclaredPrivate) (pairs : wrapper.observedPairs = observedPair params) (allRoots : ∀ i, i ∈ wrapper.tree.leaves) : (∃ (signals : Native.Variable params → Bool) (privateValues : {a // a ∈ wrapper.declaredAuxiliaries} → Bool), Satisfies (joint signals (extendDeclaredAuxiliaries wrapper.declaredAuxiliaries privateValues)) (relabel Sum.inl (PrivateFamily.driveFormula params) ++ wrapper.formula)) ↔ (Physical.detectInput params.bridge params.positiveBuses params.drive params.decoder).isSome = true := by sorry
end Controller.Recognition.ObservationDetection end_source_context source_context "Controller.Recognition.RecoveryDriver" namespace Controller.Recognition.RecoveryDriver
variable [DecidableEq α]
def scan (candidates : List (Producer α)) :
    Nat → Finset α → List (Producer α) → Finset α × List (Producer α)
  | 0, known, trace => (known, trace)
  | fuel + 1, known, trace =>
    match candidates.find? (fun p => decide (p.Ready known)) with
    | none => (known, trace)
    | some p => scan candidates fuel (insert p.output.1 known) (p :: trace)
def recover [Fintype α] (roots : Finset α) (candidates : List (Producer α)) :
    Finset α × List (Producer α) :=
  scan candidates (Fintype.card α - roots.card) roots []
/-- Finite scanning recovers the intended producers under CandidatePromise. -/ theorem recover_exact [Fintype α] (dag : IntendedDAG α) (promise : dag.CandidatePromise) : let result := recover dag.roots promise.candidates; result.1 = Finset.univ ∧ (∀ p ∈ result.2, p = dag.producer p.output.1 ∧ p.output.1 ∉ dag.roots) ∧ (∀ v, v ∉ dag.roots → dag.producer v ∈ result.2) ∧ (result.2.map (fun p => p.output.1)).Nodup ∧ result.2.length = Fintype.card α - dag.roots.card := by sorry
end Controller.Recognition.RecoveryDriver end_source_context source_context "Controller.Recognition.AcceptanceInhabited" namespace Controller.Recognition open Controller.CNF Controller.Certificate
/-- A full accepted positive-output packet has a physical detecting input and a source model. -/ theorem exists_accepted_positive_output : ∃ (params : Native.Parameters) (source : Formula (Fin 36)) (payload : PrivateFamily.CompletePayload source 36 params 35 1) (record : PrivateFamily.Record source 36 params 35 1), params.channels = 2 ∧ params.buses = 1 ∧ params.drive = true ∧ params.decoder.roots.length = 1 ∧ source.clauses.size = 91 ∧ GuardedFamily.decodeChecked payload = some record ∧ Physical.BridgeDetectable (b := params.buses) params.bridge params.drive params.observations ∧ Pipeline.runFamily source (.structured (InputPacket.serialize source)) payload none = .sat ∧ Satisfiable source := by sorry
end Controller.Recognition end_source_context
