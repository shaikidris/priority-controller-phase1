module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.Model

@[expose] public section


/-! A fuel-bounded interpreter for the concrete fetched machine. A proved
halting execution identifies its actual returned state at every sufficient
fuel bound. No output, answer or semantic evaluator is supplied to the driver. -/
namespace Controller.Cost.BoundedRun

open Controller.Cost

def run (program : Program width registers) : Nat → State width registers → State width registers
  | 0, state => state
  | fuel + 1, state =>
      match programStep program state with
      | none => state
      | some next => run program fuel next

theorem halted (program : Program width registers) (state : State width registers)
    (stopped : state.halted = true) (fuel : Nat) : run program fuel state = state := by
  have noNext : programStep program state = none := by
    unfold programStep
    cases fetched : program[state.pc.val]? <;> simp [fetched, step, stopped]
  cases fuel <;> simp only [run, noNext]

theorem of_execution (trace : Execution program initial final ticks peak)
    (stopped : final.halted = true) (fuel : Nat) (enough : ticks ≤ fuel) :
    run program fuel initial = final := by
  induction trace generalizing fuel with
  | refl state => exact halted program state stopped fuel
  | @cons initial middle final ticks peak transition rest ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [run, transition]
          exact ih stopped fuel (by omega)

end Controller.Cost.BoundedRun
