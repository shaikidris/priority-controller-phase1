module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.NativeQueryStorage
public import Controller.Cost.StackPacketConstruction

@[expose] public section


/-! Packet exchange storage includes the generated move/zero streams and
fixed copy, reclaim, ABI and return recipes. The original data words are
moved by fetched execution rather than supplied as construction answers. -/
namespace Controller.Cost.PacketTransferStorage

open Controller.Cost Controller.Extensions Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestClauseProgramConstruction (environment)

inductive MaskTrace (width : Nat) : Nat → List (Instruction width 8) → Nat → Prop
  | nil : MaskTrace width 0 [] 32
  | cons {count head tail first later}
      (formed : WordConstructionStorage.Trace (environment [0])
        (ExtensionConstructionRecipes.literalOperand.constructionRecipe width) head
        (work (ExtensionConstructionRecipes.literalOperand.constructionRecipe width)) first)
      (remaining : MaskTrace width count tail later)
      (copied : CompilerAppendTrace.AppendTrace head tail (head ++ tail) head.length) :
      MaskTrace width (count + 1) (head ++ tail) (max first (later + 128))

theorem mask (width count : Nat) :
    ∃ peak, MaskTrace width count (SupportTraversalConstruction.mask width count).1 peak ∧
      peak ≤ 1280 * count + 1000 := by
  induction count with
  | zero => exact ⟨32, .nil, by omega⟩
  | succ count ih =>
      obtain ⟨first, formed, firstBound⟩ := WordConstructionStorage.construction
        (environment [0]) (ExtensionConstructionRecipes.literalOperand.constructionRecipe width)
      obtain ⟨later, remaining, laterBound⟩ := ih
      rw [ExtensionConstructionRecipes.literalOperand.constructionRecipe_work] at firstBound
      refine ⟨_, .cons formed remaining (CompilerAppendTrace.append_exists _ _), ?_⟩
      exact Nat.max_le.mpr ⟨by omega, by omega⟩

theorem park (width start count : Nat) :
    ∃ peak, TemplateStreamConstruction.Trace (StackPacketConstruction.parkRecipes width)
      (fun _ index => Fin.elim0 index) start count (StackPacketConstruction.park width start
          count).1
      (StackPacketConstruction.park width start count).2 peak ∧ peak ≤ 640 * (count + 1) := by
  obtain ⟨peak, trace, bound⟩ := TemplateStreamConstruction.storage
    (StackPacketConstruction.parkRecipes width) (fun _ index => Fin.elim0 index) start count
  have limit : 32 * (count + 1) *
      (work (StackPacketConstruction.parkRecipes width) +
        (StackPacketConstruction.parkRecipes width).length + 2) = 640 * (count + 1) := by
    simp [StackPacketConstruction.parkRecipes, work, InstructionRecipe.work]
    omega
  exact ⟨peak, trace, by omega⟩

structure Fixed (width : Nat) where
  copy : NativeQueryStorage.Uniform (SharedWitnessCopy.code.constructionRecipe width)
  reclaim : NativeQueryStorage.Uniform (SharedEvaluationReclaim.code.constructionRecipe width)
  abi : NativeQueryStorage.Uniform (ResolvedPacketHandoff.abi.constructionRecipe width)
  read : NativeQueryStorage.Uniform (ResolvedSourceRead.pushCode.constructionRecipe width)
  parkSource : NativeQueryStorage.Uniform (ResolvedSourcePark.code.constructionRecipe width)
  route : NativeQueryStorage.Uniform (ResolvedSourceReturn.routeCode.constructionRecipe width)

theorem fixed (width : Nat) : Fixed width :=
  ⟨NativeQueryStorage.uniform _, NativeQueryStorage.uniform _, NativeQueryStorage.uniform _,
    NativeQueryStorage.uniform _, NativeQueryStorage.uniform _, NativeQueryStorage.uniform _⟩

structure HandoffCertificate (width entry oldCount sourceEnd ambient : Nat) where
  parkPeak : Nat
  zeroPeak : Nat
  parked : TemplateStreamConstruction.Trace (StackPacketConstruction.parkRecipes width)
    (fun _ index => Fin.elim0 index) 0 sourceEnd
    (StackPacketConstruction.park width 0 sourceEnd).1
    (StackPacketConstruction.park width 0 sourceEnd).2 parkPeak
  zeroed : MaskTrace width (2 * ambient)
    (SupportTraversalConstruction.mask width (2 * ambient)).1 zeroPeak
  fixed : Fixed width

def handoffBuffers (width entry oldCount sourceEnd ambient : Nat)
    (certificate : HandoffCertificate width entry oldCount sourceEnd ambient) : Nat :=
  certificate.parkPeak + certificate.zeroPeak +
    64 * (StackPacketConstruction.handoff width entry oldCount sourceEnd ambient).1.length +
    100000

theorem handoff (width entry oldCount sourceEnd ambient : Nat) :
    ∃ certificate : HandoffCertificate width entry oldCount sourceEnd ambient,
      handoffBuffers width entry oldCount sourceEnd ambient certificate ≤
        1000000 * (sourceEnd + ambient + 1) := by
  obtain ⟨parkPeak, parked, parkBound⟩ := park width 0 sourceEnd
  obtain ⟨zeroPeak, zeroed, zeroBound⟩ := mask width (2 * ambient)
  have length : (StackPacketConstruction.handoff width entry oldCount sourceEnd ambient).1.length =
      10 + 2 * sourceEnd + 4 * ambient := by
    rw [StackPacketConstruction.handoff_image, ResolvedPacketHandoff.code_length]
  refine ⟨⟨parkPeak, zeroPeak, parked, zeroed, fixed width⟩, ?_⟩
  simp only [handoffBuffers, length]
  omega

structure ReturnCertificate (width entry oldCount retainedCount found rejected : Nat) where
  parkPeak : Nat
  parked : TemplateStreamConstruction.Trace (StackPacketConstruction.parkRecipes width)
    (fun _ index => Fin.elim0 index) 0 retainedCount
    (StackPacketConstruction.park width 0 retainedCount).1
    (StackPacketConstruction.park width 0 retainedCount).2 parkPeak
  fixed : Fixed width

def returnBuffers (width entry oldCount retainedCount found rejected : Nat)
    (certificate : ReturnCertificate width entry oldCount retainedCount found rejected) : Nat :=
  certificate.parkPeak +
    64 * (StackPacketConstruction.returning width entry oldCount retainedCount found
        rejected).1.length +
    100000

theorem returning (width entry oldCount retainedCount found rejected : Nat) :
    ∃ certificate : ReturnCertificate width entry oldCount retainedCount found rejected,
      returnBuffers width entry oldCount retainedCount found rejected certificate ≤
        1000000 * (retainedCount + 1) := by
  obtain ⟨parkPeak, parked, parkBound⟩ := park width 0 retainedCount
  have length : (StackPacketConstruction.returning width entry oldCount retainedCount
      found rejected).1.length = 12 + 2 * retainedCount := by
    rw [StackPacketConstruction.returning_image, ResolvedSourceReturn.code_length]
  refine ⟨⟨parkPeak, parked, fixed width⟩, ?_⟩
  simp only [returnBuffers, length]
  omega

end Controller.Cost.PacketTransferStorage
