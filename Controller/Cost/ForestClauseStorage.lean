module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ForestClauseProgramConstruction
public import Controller.Cost.ForestDirectoryStorage
public import Controller.Cost.ForestLiteralStorage

@[expose] public section


/-! Storage certificate for complete variable source-clause image generation.
Every profile, directory, literal and fixed-operand pass has an actual trace.
The envelope includes all live output buffers and append materialization. -/
namespace Controller.Cost.ForestClauseStorage

open Controller.Cost Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestClauseProgramConstruction
open Controller.Cost.ForestZeroQueryCaller

variable {ambient : Nat}

def buffers (width base protectedEnd : Nat) (refs : List (List (Reference ambient)))
    (profilePeak headerPeak directoryPeak literalPeak finalPeak : Nat) : Nat :=
  profilePeak + headerPeak + directoryPeak + literalPeak + finalPeak +
    32 * (query width base protectedEnd refs).1.length + 32 * refs.length +
      32 * refs.flatten.length + 512

structure Certificate (width base protectedEnd : Nat) (refs : List (List (Reference ambient))) where
  profilePeak : Nat
  headerPeak : Nat
  directoryPeak : Nat
  literalPeak : Nat
  finalPeak : Nat
  profileTrace : ForestDirectoryStorage.ProfileTrace refs (ForestDirectoryConstruction.profile refs).1
    (ForestDirectoryConstruction.profile refs).2.1 (ForestDirectoryConstruction.profile refs).2.2 profilePeak
  headerTrace : WordConstructionStorage.Trace
    (environment [protectedEnd, (ForestDirectoryConstruction.profile refs).1,
      (ForestDirectoryConstruction.profile refs).2.1])
    (preservingHeaderCode.constructionRecipe width)
    (evaluate (environment [protectedEnd, (ForestDirectoryConstruction.profile refs).1,
      (ForestDirectoryConstruction.profile refs).2.1]) (preservingHeaderCode.constructionRecipe width)) 138 headerPeak
  directoryTrace : ForestDirectoryStorage.Trace width refs (ForestDirectoryConstruction.directory width refs).1
    (ForestDirectoryConstruction.directory width refs).2 directoryPeak
  literalTrace : ForestLiteralStorage.Trace width
    (base + 14 + (ForestDirectoryConstruction.directory width refs).1.length) refs.flatten
    (ForestQueryConstruction.emit width (base + 14 + (ForestDirectoryConstruction.directory width refs).1.length) refs.flatten).1
    (ForestQueryConstruction.emit width (base + 14 + (ForestDirectoryConstruction.directory width refs).1.length) refs.flatten).2 literalPeak
  finalTrace : WordConstructionStorage.Trace (environment [protectedEnd + 1])
    (countCode.constructionRecipe width)
    (evaluate (environment [protectedEnd + 1]) (countCode.constructionRecipe width)) 18 finalPeak

theorem construction (width base protectedEnd : Nat) (refs : List (List (Reference ambient))) :
    ∃ certificate : Certificate width base protectedEnd refs,
      buffers width base protectedEnd refs certificate.profilePeak certificate.headerPeak certificate.directoryPeak
        certificate.literalPeak certificate.finalPeak ≤ 50000 + 10000 * refs.length + 30000 * refs.flatten.length := by
  obtain ⟨profilePeak, profileTrace, profileBound⟩ := ForestDirectoryStorage.profile_space refs
  obtain ⟨headerPeak, headerTrace, headerBound⟩ := WordConstructionStorage.construction
    (environment [protectedEnd, (ForestDirectoryConstruction.profile refs).1,
      (ForestDirectoryConstruction.profile refs).2.1]) (preservingHeaderCode.constructionRecipe width)
  rw [preservingHeaderCode.constructionRecipe_work] at headerTrace headerBound
  obtain ⟨directoryPeak, directoryTrace, directoryBound⟩ := ForestDirectoryStorage.bound width refs
  obtain ⟨literalPeak, literalTrace, literalBound⟩ := ForestLiteralStorage.bound width
    (base + 14 + (ForestDirectoryConstruction.directory width refs).1.length) refs.flatten
  obtain ⟨finalPeak, finalTrace, finalBound⟩ := WordConstructionStorage.construction
    (environment [protectedEnd + 1]) (countCode.constructionRecipe width)
  rw [countCode.constructionRecipe_work] at finalTrace finalBound
  have codeSize := queryCode_length width base protectedEnd refs
  rw [← query_image] at codeSize
  refine ⟨⟨profilePeak, headerPeak, directoryPeak, literalPeak, finalPeak,
    profileTrace, headerTrace, directoryTrace, literalTrace, finalTrace⟩, ?_⟩
  dsimp only [buffers]
  omega

end Controller.Cost.ForestClauseStorage
