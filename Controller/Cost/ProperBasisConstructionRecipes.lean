module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public meta import Controller.Cost.DeriveBasisRecipe
public import Controller.Cost.UniformSourceConstruction
public import Controller.Extensions.ProperBasisComplete

public import Controller.Cost.WordConstructionRecipe

@[expose] public section


/-! Fixed proper-basis kernels use explicit scalar fields, including the value
of a typed source index. Recipe identity keeps the original finite-index types. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Controller.Cost.ProperBasisConstructionRecipes

open Controller.Cost Controller.Extensions Controller.Decoder

def positive (width channels nodes children guards roots : Nat) : List (Instruction width 4) :=
  LiteralSourceRun.code LiteralSourceConstruction.positive width 0 1
    (UniformSourceConstruction.layout channels nodes children guards roots)

def negative (width channels nodes children guards roots : Nat) : List (Instruction width 4) :=
  LiteralSourceRun.code LiteralSourceConstruction.negative width 0 1
    (UniformSourceConstruction.layout channels nodes children guards roots)

def zero (width channels nodes children guards roots : Nat) : List (Instruction width 4) :=
  LiteralSourceRun.code LiteralSourceConstruction.zero width 0 1
    (UniformSourceConstruction.layout channels nodes children guards roots)

derive_basis_recipe positive

derive_basis_recipe negative

derive_basis_recipe zero

def emitOne (width : Nat) : List (Instruction width 8) := LiteralWitnessEmit.constantCode (width :=
  width) true

def emitStored (width offset : Nat) : List (Instruction width 8) := LiteralWitnessEmit.storedCode
  (width := width) offset

def emitSelected (width entry channel : Nat) : List (Instruction width 8) :=
  LiteralWitnessEmit.selectedCode (width := width) entry channel

derive_basis_recipe emitOne


derive_basis_recipe emitStored

derive_basis_recipe emitSelected

def monotoneOne (width n : Nat) (target : Channel n) (nodes base entry absent full single : Nat) :
  List (Instruction width 8) :=
  MonotoneRoot.code 1 target nodes base entry absent full single

def monotoneMany (width n : Nat) (target : Channel n) (nodes base entry absent full single : Nat) :
  List (Instruction width 8) :=
  MonotoneRoot.code 2 target nodes base entry absent full single

derive_basis_recipe monotoneOne

derive_basis_recipe monotoneMany



def literalPrefix (width n : Nat) (target : Channel n)
    (nodes base entry none single singleDestination otherChannel : Nat) : List (Instruction width 8)
      :=
  let nonzero := LiteralRootRun.nonzero entry
  let healthy := LiteralRootRun.healthyEntry entry
  let unhealthy := LiteralRootRun.unhealthyEntry entry
  LiteralRootRun.readCode base nonzero none 0 ++
    (LiteralRoot.callCode LiteralTests.positiveTest n nodes base 0 target.val nonzero unhealthy
      (nonzero + 21) ++
    (LiteralRoot.callCode LiteralTests.positiveTest n nodes base (target.val + 1) (n - target.val -
      1) (nonzero + 21)
      unhealthy (nonzero + 42) ++
    (LiteralRootRun.readCode (base + (n - target.val) * nodes) healthy unhealthy 0 ++
    (LiteralRoot.callCode LiteralTests.negativeTest n nodes base 0 n healthy single (healthy + 21)
      ++
    (LiteralRootRun.readCode (base + n * nodes + (n - target.val) * nodes) none singleDestination
      otherChannel ++
    LiteralRoot.callCode LiteralTests.conflictTest n nodes base 0 n unhealthy none (unhealthy +
      22))))))

derive_basis_recipe literalPrefix

def literalOneTail (width n : Nat) (target : Channel n) (nodes base _entry none keep : Nat) : List
  (Instruction width 8) :=
  LiteralRootRun.readCode (base + (n - target.val) * nodes) keep none 0

def literalManyTail (width n nodes base entry none keep single : Nat) : List (Instruction width 8)
  :=
  LiteralRoot.callCode LiteralTests.positiveTest n nodes base 0 n entry keep (entry + 21) ++
    LiteralRoot.callCode LiteralTests.freeTest n nodes base 0 n (entry + 21) single none

derive_basis_recipe literalOneTail

derive_basis_recipe literalManyTail

end Controller.Cost.ProperBasisConstructionRecipes
