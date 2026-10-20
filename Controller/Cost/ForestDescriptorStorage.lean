module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ForestDescriptorConstruction

@[expose] public section


/-! Retained construction storage of the executed descriptor writer. The
measure charges descriptor-list records and generated instruction backing at
every control transition, including reversal and pending field writes. -/
namespace Controller.Cost.ForestDescriptorStorage

open Controller.Cost Controller.Cost.ForestDescriptorConstruction
open Controller.Cost.ForestCursorDescriptors

/-- Six words per retained descriptor/list entry is conservative for its three
fields and links; an instruction uses four backing words. -/
def phaseWords : Phase → Nat
  | .reverse pending saved => 6 * (pending.length + saved.length) + 8
  | .records pending => 6 * pending.length + 8
  | .parentAllocate _ rest | .positionConstant _ rest => 6 * rest.length + 14
  | .positionAllocate rest => 6 * rest.length + 8
  | _ => 8

def liveWords (state : Configuration width) : Nat := 4 * state.image.size + phaseWords state.phase

theorem step_bound {first last : Configuration width}
    (transition : ForestDescriptorConstruction.step width channels root pointer first = some last) :
    liveWords last ≤ liveWords first + 8 := by
  cases first with
  | mk phase image =>
      cases phase with
      | reverse pending saved =>
          cases pending <;> simp only [ForestDescriptorConstruction.step, Option.some.injEq] at transition <;>
            cases transition <;> simp [liveWords, phaseWords] <;> omega
      | records pending =>
          cases pending <;> simp only [ForestDescriptorConstruction.step, Option.some.injEq] at transition <;>
            cases transition <;> simp [liveWords, phaseWords] <;> omega
      | parentAllocate entry rest =>
          simp only [ForestDescriptorConstruction.step, Option.some.injEq] at transition
          cases transition
          simp [liveWords, phaseWords] <;> omega
      | positionConstant entry rest =>
          simp only [ForestDescriptorConstruction.step, Option.some.injEq] at transition
          cases transition
          simp [liveWords, phaseWords] <;> omega
      | positionAllocate rest =>
          simp only [ForestDescriptorConstruction.step, Option.some.injEq] at transition
          cases transition
          simp [liveWords, phaseWords] <;> omega
      | zeroAllocate remaining =>
          simp only [ForestDescriptorConstruction.step, Option.some.injEq] at transition
          cases transition
          simp [liveWords, phaseWords] <;> omega
      | root =>
          simp only [ForestDescriptorConstruction.step, Option.some.injEq] at transition
          cases transition
          simp [liveWords, phaseWords] <;> omega
      | pointer =>
          simp only [ForestDescriptorConstruction.step, Option.some.injEq] at transition
          cases transition
          simp [liveWords, phaseWords] <;> omega
      | zeroes remaining =>
          cases remaining <;> simp only [ForestDescriptorConstruction.step, Option.some.injEq] at transition <;>
            cases transition <;> simp [liveWords, phaseWords] <;> omega
      | done => simp [ForestDescriptorConstruction.step] at transition

inductive SpaceTrace (width channels root pointer : Nat) :
    Configuration width → Configuration width → Nat → Nat → Prop
  | refl (state) : SpaceTrace width channels root pointer state state 0 (liveWords state)
  | next {first middle last ticks peak}
      (transition : ForestDescriptorConstruction.step width channels root pointer first = some middle)
      (tail : SpaceTrace width channels root pointer middle last ticks peak) :
      SpaceTrace width channels root pointer first last (ticks + 1) (max (liveWords first) peak)

theorem space {first last : Configuration width} {ticks : Nat}
    (trace : Trace width channels root pointer first last ticks) :
    ∃ peak, SpaceTrace width channels root pointer first last ticks peak ∧
      peak ≤ liveWords first + 8 * ticks := by
  induction trace with
  | refl state => exact ⟨liveWords state, .refl state, by omega⟩
  | @next first middle last ticks transition tail ih =>
      obtain ⟨peak, stored, bound⟩ := ih
      have one := step_bound transition
      refine ⟨max (liveWords first) peak, .next transition stored, ?_⟩
      exact Nat.max_le.mpr ⟨by omega, by omega⟩

/-- Complete descriptor formation, including its transient reversal/field
state, has linear retained construction storage. -/
theorem complete (channels : Nat) (entries : List ParentEntry) (root pointer : Nat)
    (image : Program width 4) :
    ∃ final peak,
      SpaceTrace width channels root pointer ⟨.reverse entries [], image⟩ final
        (5 * entries.length + 2 * channels + 11) peak ∧
      peak ≤ 4 * image.size + 46 * entries.length + 16 * channels + 96 ∧
      final.phase = .done := by
  have execution := ForestDescriptorConstruction.complete (width := width) channels entries root pointer image
  obtain ⟨peak, trace, bound⟩ := space execution
  refine ⟨_, peak, trace, ?_, rfl⟩
  simp only [liveWords, phaseWords, List.length_nil, Nat.add_zero] at bound
  omega

end Controller.Cost.ForestDescriptorStorage
