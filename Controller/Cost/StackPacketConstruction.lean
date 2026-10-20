module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ExtensionNativeRecipes
public import Controller.Cost.TemplateStreamConstruction
public import Controller.Cost.SupportTraversalConstruction

@[expose] public section


/-! First-order source-packet transfer and restoration. Runtime words are moved
by the emitted instructions; construction sees only addresses and lengths. -/
set_option maxRecDepth 10000

namespace Controller.Cost.StackPacketConstruction

open Controller.Cost Controller.Extensions Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestClauseProgramConstruction (environment)

derive_extension_recipe ResolvedPacketHandoff.abi

derive_extension_recipe ResolvedSourceRead.pushCode

def parkRecipes (width : Nat) : List (InstructionRecipe 0 width 8) := [.plain (.pop 3), .plain
  (.allocate 3)]

def park (width start count : Nat) : List (Instruction width 8) × Nat :=
  TemplateStreamConstruction.build (parkRecipes width) (fun _ index => Fin.elim0 index) start count

theorem park_image (width start count : Nat) : (park width start count).1 = SharedWitnessPark.code
  width count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      change [.pop 3, .allocate 3] ++ (park width (start + 1) count).1 = _
      rw [ih]
      rfl

theorem park_clock (width start count : Nat) : (park width start count).2 = 42 * count + 1 := by
  rw [park, TemplateStreamConstruction.clock]
  simp [parkRecipes, work, InstructionRecipe.work, Nat.mul_comm]

def reclaim (width entry done count : Nat) : List (Instruction width 8) :=
  evaluate (environment [entry, done, count]) (SharedEvaluationReclaim.code.constructionRecipe
    width)

theorem reclaim_image (width entry done count : Nat) :
    reclaim width entry done count = (SharedEvaluationReclaim.code width entry done count).toList :=
  SharedEvaluationReclaim.code.constructionRecipe_eq width entry done count

def copy (width entry done base count : Nat) : List (Instruction width 8) :=
  evaluate (environment [entry, done, base, count]) (SharedWitnessCopy.code.constructionRecipe
    width)

theorem copy_image (width entry done base count : Nat) :
    copy width entry done base count = (SharedWitnessCopy.code width entry done base count).toList
      :=
  SharedWitnessCopy.code.constructionRecipe_eq width entry done base count

def handoff (width entry oldCount sourceEnd ambient : Nat) : List (Instruction width 8) × Nat :=
  let parked := park width 0 sourceEnd
  let zeros := SupportTraversalConstruction.mask width (2 * ambient)
  let abi := evaluate (environment [sourceEnd, ambient])
    (ResolvedPacketHandoff.abi.constructionRecipe width)
  let image := reclaim width entry (entry + 7) oldCount ++ parked.1 ++ zeros.1 ++ abi
  (image, parked.2 + zeros.2 + 16 * image.length + 1000)

theorem handoff_image (width entry oldCount sourceEnd ambient : Nat) :
    (handoff width entry oldCount sourceEnd ambient).1 = ResolvedPacketHandoff.code width entry
      oldCount sourceEnd ambient := by
  have abi : evaluate (environment [sourceEnd, ambient])
    (ResolvedPacketHandoff.abi.constructionRecipe width) =
      ResolvedPacketHandoff.abi width sourceEnd ambient :=
        ResolvedPacketHandoff.abi.constructionRecipe_eq width sourceEnd ambient
  simp only [handoff, reclaim_image, park_image, SupportTraversalConstruction.mask_image,
    abi, ResolvedPacketHandoff.code, List.append_assoc]

theorem handoff_clock (width entry oldCount sourceEnd ambient : Nat) :
    (handoff width entry oldCount sourceEnd ambient).2 ≤ 2000 + 100 * sourceEnd + 200 * ambient :=
      by
  have parked := park_clock width 0 sourceEnd
  have zeros := SupportTraversalConstruction.mask_clock width (2 * ambient)
  have length : (handoff width entry oldCount sourceEnd ambient).1.length = 10 + 2 * sourceEnd + 4 *
    ambient := by
    rw [handoff_image, ResolvedPacketHandoff.code_length]
  change (park width 0 sourceEnd).2 + (SupportTraversalConstruction.mask width (2 * ambient)).2 +
    16 * (handoff width entry oldCount sourceEnd ambient).1.length + 1000 ≤ _
  rw [length]
  omega

def returning (width entry oldCount retainedCount found rejected : Nat) : List (Instruction width 8)
  × Nat :=
  let restored := park width 0 retainedCount
  let route := evaluate (environment [entry + 7 + 2 * retainedCount, found, rejected])
    (ResolvedSourceReturn.routeCode.constructionRecipe width)
  let image := reclaim width entry (entry + 7) oldCount ++ restored.1 ++ route
  (image, restored.2 + 16 * image.length + 1000)

theorem returning_image (width entry oldCount retainedCount found rejected : Nat) :
    (returning width entry oldCount retainedCount found rejected).1 =
      ResolvedSourceReturn.code width entry oldCount retainedCount found rejected := by
  have route : evaluate (environment [entry + 7 + 2 * retainedCount, found, rejected])
      (ResolvedSourceReturn.routeCode.constructionRecipe width) =
      ResolvedSourceReturn.routeCode width (entry + 7 + 2 * retainedCount) found rejected :=
    ResolvedSourceReturn.routeCode.constructionRecipe_eq width (entry + 7 + 2 * retainedCount) found
      rejected
  simp only [returning, reclaim_image, park_image, route, ResolvedSourceReturn.code,
    List.append_assoc]

theorem returning_clock (width entry oldCount retainedCount found rejected : Nat) :
    (returning width entry oldCount retainedCount found rejected).2 ≤ 2000 + 100 * retainedCount :=
      by
  have restored := park_clock width 0 retainedCount
  have length : (returning width entry oldCount retainedCount found rejected).1.length = 12 + 2 *
    retainedCount := by
    rw [returning_image, ResolvedSourceReturn.code_length]
  change (park width 0 retainedCount).2 + 16 * (returning width entry oldCount retainedCount found
    rejected).1.length + 1000 ≤ _
  rw [length]
  omega

end Controller.Cost.StackPacketConstruction
