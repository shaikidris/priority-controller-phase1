module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ForestSourceConstruction
public import Controller.Cost.ForestCompilerOffsets
public import Controller.Cost.ForestConstructionRecipes
public import Controller.Cost.UniformDAGResources

@[expose] public section


/-! Interpreter image construction from scalar source counts. The constructor
never materializes a hypothetical source or evaluation heap to read its size.
The actual healthy evaluation is the existing cold interpreter execution. -/
namespace Controller.Cost.UniformSourceConstruction

open Controller Controller.Decoder Controller.Decoder.DAG
open Controller.Cost Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputPrefixStored
open Controller.Cost.UniformDAGRun

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def layout (channels nodes children guards roots : Nat) : UniformDAGNode.Layout where
  tagBase := 5
  headBase := 6
  channelBase := 5 + 6 * nodes + children + guards + roots
  nodeBase := 5 + 6 * nodes + children + guards + roots + channels
  childArityBase := 5 + 4 * nodes
  childSourceBase := 5 + 2 * nodes
  guardArityBase := 5 + 4 * nodes + 1
  guardSourceBase := 5 + 2 * nodes + 1

def kernel (width channels nodes children guards roots : Nat) : GateProgram.Code width :=
  UniformDAGLoop.code width (33 + 2 * channels) 1 (layout channels nodes children guards roots)

derive_word_recipe kernel

theorem layout_eq (width : Nat) (rows : List Row) (roots : List Nat) (values : Channel n → Bool) :
    layout n rows.length (rowChildren rows).length (rowGuards rows).length roots.length =
      UniformDAGTypedNode.layout (packetHeaderHeap width n rows roots) rows roots values := by
  simp only [layout, UniformDAGTypedNode.layout, packetHeaderHeap_size, channelHeap_size, cacheHeap_size]

/-- Fixed-shape channel loader formation and append copy are both charged. -/
def loads (width : Nat) : Nat → GateProgram.Code width × Nat
  | 0 => ([], 1)
  | count + 1 =>
      let tail := loads width count
      ([.pop 0, .allocate 0] ++ tail.1, tail.2 + 20)

theorem loads_image (width count : Nat) : (loads width count).1 = InputLoad.code count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [loads, InputLoad.code, ih]; rfl

theorem loads_work (width count : Nat) : (loads width count).2 = 20 * count + 1 := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [loads, ih]; omega

/-- Only input counts determine the resident interpreter. The supplied
assignment is heap input, and never becomes an immediate answer constant. -/
def code (width channels nodes children guards rootCount : Nat) : GateProgram.Code width :=
  evaluate (fun index => [0].getD index.val 0) (ForestInputMetadata.fullCode.constructionRecipe width) ++
    (loads width channels).1 ++
    evaluate (fun index => [channels, nodes, children, guards, rootCount].getD index.val 0)
      (kernel.constructionRecipe width)

theorem code_image (width : Nat) (rows : List Row) (roots : List Nat) (values : Channel n → Bool) :
    code width n rows.length (rowChildren rows).length (rowGuards rows).length roots.length =
      UniformDAGResources.code width n rows roots values := by
  simp only [code, ForestInputMetadata.fullCode.constructionRecipe_eq, kernel.constructionRecipe_eq,
    loads_image, kernel, UniformDAGResources.code, List.append_assoc]
  rw [layout_eq width rows roots values]

/-- Generation includes recipe arithmetic, instruction/backing fields, loader
formation, instruction copies, final array pushes and layout arithmetic. -/
def work (width channels : Nat) : Nat :=
  WordConstructionRecipe.work (ForestInputMetadata.fullCode.constructionRecipe width) +
    (loads width channels).2 + WordConstructionRecipe.work (kernel.constructionRecipe width) +
    2 * (159 + 2 * channels) + 100

theorem work_bound (width channels : Nat) : work width channels ≤ 5000 + 24 * channels := by
  simp only [work, ForestInputMetadata.fullCode.constructionRecipe_work, kernel.constructionRecipe_work, loads_work]
  omega

end Controller.Cost.UniformSourceConstruction
