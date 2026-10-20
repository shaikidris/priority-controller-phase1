/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ForestConstructionRecipes

/-! Fixed scalar templates for the forest loader, selector flag and final halt. -/
namespace Controller.Cost.ForestFixedControlRecipes

open Controller.Cost

def cold (width entry : Nat) : GateProgram.Code width :=
  ForestZeroControlLoad.code width entry ++ [.pop 2]

def selector (width failure present : Nat) : List (Instruction width 8) :=
  [.constant 4 (word width present), .branchZero 4 (word width failure)]

def exhausted (width : Nat) : List (Instruction width 8) :=
  (ForestZeroRootLoop.exhaustedCode width).toList

derive_word_recipe cold
derive_word_recipe selector
derive_word_recipe exhausted

end Controller.Cost.ForestFixedControlRecipes
