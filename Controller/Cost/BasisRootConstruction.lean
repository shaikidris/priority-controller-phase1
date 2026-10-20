module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.WitnessEmissionConstruction

@[expose] public section


/-! Fixed proper-basis root decision kernels. Finite source-index fields stay
explicit, and source comparisons determine only scalar jump destinations. -/
namespace Controller.Cost.BasisRootConstruction

open Controller Controller.Decoder Controller.Cost Controller.Extensions
open Controller.Cost.WordConstructionRecipe Controller.Cost.ProperBasisConstructionRecipes
open Controller.Cost.ForestClauseProgramConstruction (environment)

def monotone (width b : Nat) (target : Channel n) (nodes base entry absent full single : Nat) : List
  (Instruction width 8) :=
  evaluate (environment [n, target.val, nodes, base, entry, absent, full, single])
    (if b = 1 then monotoneOne.constructionRecipe width else monotoneMany.constructionRecipe width)

theorem monotone_image (width b : Nat) (target : Channel n) (nodes base entry absent full single :
  Nat) :
    monotone width b target nodes base entry absent full single = MonotoneRoot.code b target nodes
      base entry absent full single := by
  have one : evaluate (environment [n, target.val, nodes, base, entry, absent, full, single])
      (monotoneOne.constructionRecipe width) = monotoneOne width n target nodes base entry absent
        full single :=
    monotoneOne.constructionRecipe_eq width n target nodes base entry absent full single
  have many : evaluate (environment [n, target.val, nodes, base, entry, absent, full, single])
      (monotoneMany.constructionRecipe width) = monotoneMany width n target nodes base entry absent
        full single :=
    monotoneMany.constructionRecipe_eq width n target nodes base entry absent full single
  by_cases bus : b = 1 <;> simp only [monotone, bus, if_true, if_false, one, many, monotoneOne,
    monotoneMany,
    MonotoneRoot.code] <;> simp [bus]

def literal (width b : Nat) (target : Channel n) (nodes base entry absent keep single : Nat) : List
  (Instruction width 8) :=
  let otherChannel := if target.val = 0 then 1 else 0
  let destination := if b ≠ 1 ∧ 2 ≤ n then single else absent
  let front := evaluate (environment [n, target.val, nodes, base, entry, absent, single,
    destination, otherChannel])
    (literalPrefix.constructionRecipe width)
  let tailEntry := LiteralRootRun.unhealthyEntry entry + 22
  let tail := if b = 1 then
    evaluate (environment [n, target.val, nodes, base, tailEntry, absent, keep])
      (literalOneTail.constructionRecipe width)
  else evaluate (environment [n, nodes, base, tailEntry, absent, keep, single])
    (literalManyTail.constructionRecipe width)
  front ++ tail

theorem literal_image (width b : Nat) (target : Channel n) (nodes base entry absent keep single :
  Nat) :
    literal width b target nodes base entry absent keep single = LiteralRootRun.code b target nodes
      base entry absent keep single := by
  let otherChannel := if target.val = 0 then 1 else 0
  let destination := if b ≠ 1 ∧ 2 ≤ n then single else absent
  let tailEntry := LiteralRootRun.unhealthyEntry entry + 22
  have front : evaluate (environment [n, target.val, nodes, base, entry, absent, single,
    destination, otherChannel])
      (literalPrefix.constructionRecipe width) = literalPrefix width n target nodes base entry
        absent single destination otherChannel :=
    literalPrefix.constructionRecipe_eq width n target nodes base entry absent single destination
      otherChannel
  have one : evaluate (environment [n, target.val, nodes, base, tailEntry, absent, keep])
    (literalOneTail.constructionRecipe width) =
      literalOneTail width n target nodes base tailEntry absent keep :=
        literalOneTail.constructionRecipe_eq width n target nodes base tailEntry absent keep
  have many : evaluate (environment [n, nodes, base, tailEntry, absent, keep, single])
    (literalManyTail.constructionRecipe width) =
      literalManyTail width n nodes base tailEntry absent keep single :=
        literalManyTail.constructionRecipe_eq width n nodes base tailEntry absent keep single
  dsimp only [otherChannel, destination, tailEntry] at front one many
  simp only [literal, front, one, many, literalPrefix, literalOneTail, literalManyTail,
    LiteralRootRun.code, LiteralRootRun.tailCode, LiteralRootRun.other, List.append_assoc]

end Controller.Cost.BasisRootConstruction
