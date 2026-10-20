/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ForestRootClassification
import Controller.Cost.WordConstructionStorage

/-! Construction storage of the counts-only source interpreter. No hypothetical
source/evaluation heap is materialized to obtain layout operands. -/
namespace Controller.Cost.UniformSourceStorage

open Controller.Cost Controller.Cost.WordConstructionRecipe

inductive LoadsTrace (width : Nat) : Nat → GateProgram.Code width → Nat → Nat → Prop
  | nil : LoadsTrace width 0 [] 1 32
  | cons {count code ticks peak} (tail : LoadsTrace width count code ticks peak) :
      LoadsTrace width (count + 1) ([.pop 0, .allocate 0] ++ code) (ticks + 20) (peak + 32)

theorem loads (width count : Nat) :
    LoadsTrace width count (UniformSourceConstruction.loads width count).1
      (UniformSourceConstruction.loads width count).2 (32 * count + 32) := by
  induction count with
  | zero => exact .nil
  | succ count ih =>
      simpa only [UniformSourceConstruction.loads, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using LoadsTrace.cons ih

structure Certificate (width channels nodes children guards roots : Nat) where
  headerPeak : Nat
  kernelPeak : Nat
  tailPeak : Nat
  header : WordConstructionStorage.Trace (fun i : Fin 1 => [0].getD i.val 0)
    (ForestInputMetadata.fullCode.constructionRecipe width)
    (evaluate (fun i : Fin 1 => [0].getD i.val 0) (ForestInputMetadata.fullCode.constructionRecipe width)) 292 headerPeak
  kernel : WordConstructionStorage.Trace
    (fun i : Fin 5 => [channels, nodes, children, guards, roots].getD i.val 0)
    (UniformSourceConstruction.kernel.constructionRecipe width)
    (evaluate (fun i : Fin 5 => [channels, nodes, children, guards, roots].getD i.val 0)
      (UniformSourceConstruction.kernel.constructionRecipe width)) 1478 kernelPeak
  tail : WordConstructionStorage.Trace
    (fun i : Fin 5 => [channels, nodes, children, guards, roots].getD i.val 0)
    (ForestRootClassification.tailCode.constructionRecipe width)
    (evaluate (fun i : Fin 5 => [channels, nodes, children, guards, roots].getD i.val 0)
      (ForestRootClassification.tailCode.constructionRecipe width)) 168 tailPeak
  loader : LoadsTrace width channels (UniformSourceConstruction.loads width channels).1
    (UniformSourceConstruction.loads width channels).2 (32 * channels + 32)

def buffers (width channels nodes children guards roots : Nat)
    (certificate : Certificate width channels nodes children guards roots) : Nat :=
  certificate.headerPeak + certificate.kernelPeak + certificate.tailPeak + 32 * channels + 32 +
    32 * (ForestRootClassification.program width channels nodes children guards roots).size + 512

theorem construction (width channels nodes children guards roots : Nat) :
    ∃ certificate : Certificate width channels nodes children guards roots,
      buffers width channels nodes children guards roots certificate ≤ 100000 + 200 * channels := by
  obtain ⟨headerPeak, header, headerBound⟩ := WordConstructionStorage.construction
    (fun i : Fin 1 => [0].getD i.val 0) (ForestInputMetadata.fullCode.constructionRecipe width)
  rw [ForestInputMetadata.fullCode.constructionRecipe_work] at header headerBound
  obtain ⟨kernelPeak, kernel, kernelBound⟩ := WordConstructionStorage.construction
    (fun i : Fin 5 => [channels, nodes, children, guards, roots].getD i.val 0)
    (UniformSourceConstruction.kernel.constructionRecipe width)
  rw [UniformSourceConstruction.kernel.constructionRecipe_work] at kernel kernelBound
  obtain ⟨tailPeak, tail, tailBound⟩ := WordConstructionStorage.construction
    (fun i : Fin 5 => [channels, nodes, children, guards, roots].getD i.val 0)
    (ForestRootClassification.tailCode.constructionRecipe width)
  rw [ForestRootClassification.tailCode.constructionRecipe_work] at tail tailBound
  have size : (ForestRootClassification.program width channels nodes children guards roots).size = 174 + 2 * channels := by
    simp only [ForestRootClassification.program, List.size_toArray, List.length_append,
      UniformSourceConstruction.code, evaluate, List.length_map,
      UniformSourceConstruction.loads_image, InputLoad.code_length]
    change 33 + 2 * channels + 126 + 15 = 174 + 2 * channels
    omega
  refine ⟨⟨headerPeak, kernelPeak, tailPeak, header, kernel, tail, loads width channels⟩, ?_⟩
  dsimp only [buffers]
  rw [size]
  omega

end Controller.Cost.UniformSourceStorage
