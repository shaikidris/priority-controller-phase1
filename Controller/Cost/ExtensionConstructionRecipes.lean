module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public meta import Controller.Cost.DeriveExtensionRecipe
public import Controller.Extensions.BoundedNativeDetector
public import Controller.Extensions.ProperBasisComplete

public import Controller.Cost.WordConstructionRecipe

@[expose] public section


/-! First-order construction recipes for the fixed extension-controller blocks.
All varying addresses and counts are explicit numeric input slots. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Controller.Cost.ExtensionConstructionRecipes

open Controller.Cost Controller.Extensions

def traversal (width entry limit base query : Nat) : List (Instruction width 8) :=
  SupportTraversal.endingCode width entry limit base query (.constant 0 (word width 0))

derive_extension_recipe traversal

derive_extension_recipe SupportHealthyScan.nodeCode

derive_extension_recipe SupportRootScan.nodeCode



derive_extension_recipe ResolvedRootLoop.advanceCode

derive_extension_recipe SupportTarget.saveCode

derive_extension_recipe SupportTarget.restoreCode

derive_extension_recipe ResolvedSourceRead.readCode

derive_extension_recipe ResolvedSourceRead.choiceCode

derive_extension_recipe ResolvedSourcePark.code

derive_extension_recipe ResolvedSourceReturn.routeCode

derive_extension_recipe SharedWitnessCopy.code

derive_extension_recipe SharedEvaluationReclaim.code

def enter (width n capacity : Nat) : List (Instruction width 8) :=
  [.constant 5 (word width 0), .push 5, .constant 3 (word width n), .push 3,
    .constant 3 (word width 0), .constant 5 (word width capacity)]

derive_extension_recipe enter

def rootDriver (width loop count rootBase slot healthyBase seek done ands : Nat) :
    List (Instruction width 8) :=
  (SharedTagCompare.code width done count 3).toList ++
    (ResolvedRootRead.code width rootBase slot healthyBase (loop + 23) ++
      (enter width ands ands ++ EnumerationDriverCode.jump width seek))

derive_extension_recipe rootDriver

theorem rootDriver_image (width loop count rootBase slot healthyBase seek done ands : Nat) :
    rootDriver width loop count rootBase slot healthyBase seek done ands =
      ResolvedRootLoop.driverCode width loop count rootBase slot healthyBase seek done ands := by
  simp only [rootDriver, ResolvedRootLoop.driverCode, ResolvedRootLoop.attemptCode,
    enter, SupportSearchInit.enterCode, Nat.min_self]

def sourceLayout (channels header nodes children guards roots : Nat) : UniformDAGNode.Layout where
  tagBase := header
  headBase := header + 1
  channelBase := header + 6 * nodes + children + guards + roots
  nodeBase := header + 6 * nodes + children + guards + roots + channels
  childArityBase := header + 4 * nodes
  childSourceBase := header + 2 * nodes
  guardArityBase := header + 4 * nodes + 1
  guardSourceBase := header + 2 * nodes + 1

def sourceKernel (width channels header nodes children guards roots : Nat) : GateProgram.Code width :=
  UniformDAGLoop.code width 0 1 (sourceLayout channels header nodes children guards roots)

derive_extension_recipe sourceKernel

theorem sourceLayout_image (width channels : Nat) (header : Array (Word width))
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) :
    sourceLayout channels header.size rows.length (ForestIndexedOperands.rowChildren rows).length
      (ForestIndexedOperands.rowGuards rows).length roots.length =
      UniformDAGTypedNode.layout header rows roots (fun _ : Fin channels => false) := by
  simp only [sourceLayout, UniformDAGTypedNode.layout, ForestIndexedOperands.cacheHeap_size,
    ForestInputPrefixStored.channelHeap_size]

def literalOperand (width value : Nat) : List (Instruction width 8) :=
  ResolvedSourceEmit.oneCode width 0 (.literal (word width value))

def readOperand (width address offset : Nat) : List (Instruction width 8) :=
  ResolvedSourceEmit.oneCode width 0 (.read address (word width offset))

def choiceOperand (width entry flag left right offset : Nat) : List (Instruction width 8) :=
  ResolvedSourceEmit.oneCode width entry (.choice flag left right (word width offset))

derive_extension_recipe literalOperand

derive_extension_recipe readOperand

derive_extension_recipe choiceOperand

derive_extension_recipe SupportCandidate.finishCode

def returnPlain (width destination : Nat) : List (Instruction width 8) :=
  [.constant 0 (word width 0), .branchZero 0 (word width destination)]

def returnSingle (width address destination : Nat) : List (Instruction width 8) :=
  SupportTarget.restoreCode width address ++ returnPlain width destination

derive_extension_recipe returnPlain

derive_extension_recipe returnSingle


end Controller.Cost.ExtensionConstructionRecipes
