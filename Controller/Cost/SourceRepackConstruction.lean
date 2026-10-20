module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.StackPacketConstruction

@[expose] public section


/-! Charged instruction construction for exchanging the retained source heap. -/
namespace Controller.Cost.SourceRepackConstruction

open Controller.Cost Controller.Extensions Controller.Extensions.ResolvedSourceEmit

def build (width entry oldCount : Nat) (operands : List (Operand width)) : List (Instruction width
  8) × Nat :=
  let emitted := SourceOperandConstruction.build width entry operands
  let copied := StackPacketConstruction.copy width (entry + emitted.1.length) (entry +
    emitted.1.length + 10) oldCount operands.length
  let release := StackPacketConstruction.reclaim width (entry + emitted.1.length + 10) (entry +
    emitted.1.length + 17) (oldCount + operands.length)
  let parked := StackPacketConstruction.park width 0 operands.length
  let image := emitted.1 ++ copied ++ release ++ parked.1
  (image, emitted.2 + parked.2 + 16 * image.length + 2000)

theorem image (width entry oldCount : Nat) (operands : List (Operand width)) :
    (build width entry oldCount operands).1 = SupportSourceRepack.code width entry oldCount operands
      := by
  simp only [build, SourceOperandConstruction.build_image, StackPacketConstruction.copy_image,
    StackPacketConstruction.reclaim_image, StackPacketConstruction.park_image,
      SupportSourceRepack.code,
    Nat.add_assoc, List.append_assoc]

theorem clock (width entry oldCount : Nat) (operands : List (Operand width)) :
    (build width entry oldCount operands).2 ≤ 3000 + 1000 * operands.length := by
  have emitted := SourceOperandConstruction.build_clock width entry operands
  have parked := StackPacketConstruction.park_clock width 0 operands.length
  have length : (build width entry oldCount operands).1.length ≤ 14 * operands.length + 17 := by
    rw [image]
    exact SupportSourceRepack.code_bound operands
  change _ + _ + 16 * (build width entry oldCount operands).1.length + 2000 ≤ _
  omega

end Controller.Cost.SourceRepackConstruction
