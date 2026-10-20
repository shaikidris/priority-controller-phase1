module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.CriticalSourceScan
public import Controller.Cost.EnumerationSteps

@[expose] public section


/-! Cold execution of the fixed critical-source scanner. -/
namespace Controller.Cost.CriticalSourceScan

open Controller Controller.Cost Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.GateProgram Controller.Cost.ForestIndexedOperands
open Controller.Cost.ForestZeroCallerWiden

variable {width : Nat}

/-- Seven fetched setup instructions read the channel count and compute the
descending scan interval. All other source words and caller frames are retained. -/
theorem setup_execution (resident : Program width 8) (state : State width 8)
    (entry channels : Nat) (position : state.pc = word width entry)
    (running : state.halted = false) (fits : entry + 7 < 2 ^ width)
    (capacity : 4 * channels + 3 < 2 ^ width) (nonempty : 0 < state.heap.size)
    (header : state.heap[0] = word width channels)
    (present : WidenedBlockAt resident entry (setupCode width)) :
    ∃ final, Execution resident state final 7 state.liveWords ∧
      final.pc = word width (entry + 7) ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 0 = word width (4 * channels + 3) ∧ final.reg 1 = word width 3 ∧
      final.reg 2 = word width (2 * channels + 3) ∧ final.reg 3 = word width 0 := by
  obtain ⟨s0, t0, pc0, r30, h0, st0, o0, run0, keep0⟩ :=
    SharedEvaluationReclaim.constant_execution resident entry 0 3 state position running (by omega)
      (by simpa [setupCode, RegisterWiden.widenInstruction, RegisterWiden.widenRegister] using present 0 (by simp))
  have zero : (s0.reg 3).val = 0 := by rw [r30]; rfl
  obtain ⟨s1, t1, pc1, r21, h1, st1, o1, run1, keep1⟩ :=
    EnumerationSteps.load_execution resident s0 (entry + 1) 2 3 pc0 run0 (by omega)
      (by rw [zero, h0]; exact nonempty)
      (by simpa [setupCode, RegisterWiden.widenInstruction, RegisterWiden.widenRegister] using present 1 (by simp))
  have countRead : s1.reg 2 = word width channels := by
    simpa only [zero, h0, header] using r21
  obtain ⟨s2, t2, pc2, r22, h2, st2, o2, run2, keep2⟩ :=
    EnumerationSteps.add_execution resident s1 (entry + 2) 2 2 2
      (by simpa only [Nat.add_assoc] using pc1) run1 (by omega)
      (by simpa [setupCode, RegisterWiden.widenInstruction, RegisterWiden.widenRegister] using present 2 (by simp))
  have doubled : s2.reg 2 = word width (2 * channels) := by
    rw [r22, countRead, show (word width channels).val = channels from Nat.mod_eq_of_lt (by omega)]
    congr 1
    omega
  obtain ⟨s3, t3, pc3, r03, h3, st3, o3, run3, keep3⟩ :=
    EnumerationSteps.add_execution resident s2 (entry + 3) 0 2 2
      (by simpa only [Nat.add_assoc] using pc2) run2 (by omega)
      (by simpa [setupCode, RegisterWiden.widenInstruction, RegisterWiden.widenRegister] using present 3 (by simp))
  have quadrupled : s3.reg 0 = word width (4 * channels) := by
    rw [r03, doubled, show (word width (2 * channels)).val = 2 * channels from Nat.mod_eq_of_lt (by omega)]
    congr 1
    omega
  obtain ⟨s4, t4, pc4, r14, h4, st4, o4, run4, keep4⟩ :=
    SharedEvaluationReclaim.constant_execution resident (entry + 4) 3 1 s3
      (by simpa only [Nat.add_assoc] using pc3) run3 (by omega)
      (by simpa [setupCode, RegisterWiden.widenInstruction, RegisterWiden.widenRegister] using present 4 (by simp))
  obtain ⟨s5, t5, pc5, r05, h5, st5, o5, run5, keep5⟩ :=
    EnumerationSteps.add_execution resident s4 (entry + 5) 0 0 1
      (by simpa only [Nat.add_assoc] using pc4) run4 (by omega)
      (by simpa [setupCode, RegisterWiden.widenInstruction, RegisterWiden.widenRegister] using present 5 (by simp))
  have start : s5.reg 0 = word width (4 * channels + 3) := by
    rw [r05, keep4 0 (by decide), quadrupled, r14,
      show (word width (4 * channels)).val = 4 * channels from Nat.mod_eq_of_lt (by omega),
      show (word width 3).val = 3 from Nat.mod_eq_of_lt (by omega)]
  obtain ⟨s6, t6, pc6, r26, h6, st6, o6, run6, keep6⟩ :=
    EnumerationSteps.add_execution resident s5 (entry + 6) 2 2 1
      (by simpa only [Nat.add_assoc] using pc5) run5 (by omega)
      (by simpa [setupCode, RegisterWiden.widenInstruction, RegisterWiden.widenRegister] using present 6 (by simp))
  have stop : s6.reg 2 = word width (2 * channels + 3) := by
    rw [r26, keep5 2 (by decide), keep4 2 (by decide), keep3 2 (by decide), doubled,
      keep5 1 (by decide), r14,
      show (word width (2 * channels)).val = 2 * channels from Nat.mod_eq_of_lt (by omega),
      show (word width 3).val = 3 from Nat.mod_eq_of_lt (by omega)]
  have finalZero : s6.reg 3 = word width 0 := by
    rw [keep6 3 (by decide), keep5 3 (by decide), keep4 3 (by decide),
      keep3 3 (by decide), keep2 3 (by decide), keep1 3 (by decide), r30]
  have live0 : s0.liveWords = state.liveWords := by simp only [State.liveWords, h0, st0, o0]
  have live1 : s1.liveWords = state.liveWords := by simp only [State.liveWords, h1, st1, o1, h0, st0, o0]
  have live2 : s2.liveWords = state.liveWords := by
    simp only [State.liveWords, h2, st2, o2, h1, st1, o1, h0, st0, o0]
  have live3 : s3.liveWords = state.liveWords := by
    simp only [State.liveWords, h3, st3, o3, h2, st2, o2, h1, st1, o1, h0, st0, o0]
  have live4 : s4.liveWords = state.liveWords := by
    simp only [State.liveWords, h4, st4, o4, h3, st3, o3, h2, st2, o2, h1, st1, o1, h0, st0, o0]
  have live5 : s5.liveWords = state.liveWords := by
    simp only [State.liveWords, h5, st5, o5, h4, st4, o4, h3, st3, o3, h2, st2, o2, h1, st1, o1, h0, st0, o0]
  have trace := (((((t0.append t1).append t2).append t3).append t4).append t5).append t6
  refine ⟨s6, ?_, by simpa only [Nat.add_assoc] using pc6, run6,
    h6.trans (h5.trans (h4.trans (h3.trans (h2.trans (h1.trans h0))))),
    st6.trans (st5.trans (st4.trans (st3.trans (st2.trans (st1.trans st0))))),
    o6.trans (o5.trans (o4.trans (o3.trans (o2.trans (o1.trans o0))))),
    (keep6 0 (by decide)).trans start,
    (keep6 1 (by decide)).trans ((keep5 1 (by decide)).trans r14), stop, finalZero⟩
  simpa only [live0, live1, live2, live3, live4, live5, Nat.max_self, Nat.reduceAdd] using trace

private theorem widened_prefix (resident : Program width 8) (base : Nat)
    (first second : GateProgram.Code width)
    (whole : WidenedBlockAt resident base (first ++ second)) :
    WidenedBlockAt resident base first := by
  intro offset bounded
  have cell := whole offset (by simp only [List.length_append]; omega)
  simpa only [List.getElem?_append_left bounded] using cell

private theorem widened_suffix (resident : Program width 8) (base : Nat)
    (first second : GateProgram.Code width)
    (whole : WidenedBlockAt resident base (first ++ second)) :
    WidenedBlockAt resident (base + first.length) second := by
  intro offset bounded
  have cell := whole (first.length + offset) (by simp only [List.length_append]; omega)
  simpa only [List.getElem?_append_right (by omega : first.length ≤ first.length + offset),
    Nat.add_sub_cancel_left, Nat.add_assoc] using cell

theorem program_block (width : Nat) : WidenedBlockAt (program width) 0 (code width) := by
  intro offset bounded
  have mapped : offset < ((code width).map RegisterWiden.widenInstruction).length := by
    simpa only [List.length_map] using bounded
  simp [program, List.getElem?_append_left mapped]

theorem program_blocks (width : Nat) :
    WidenedBlockAt (program width) 0 (ForestInputMetadata.fullCode width 0) ∧
    WidenedBlockAt (program width) 33 (setupCode width) ∧
    WidenedBlockAt (program width) 40 (loopCode width 40) := by
  have whole := program_block width
  change WidenedBlockAt (program width) 0
    (ForestInputMetadata.fullCode width 0 ++ (setupCode width ++ loopCode width 40)) at whole
  have loader := widened_prefix _ _ _ _ whole
  have afterLoader := widened_suffix _ _ _ _ whole
  simp only [ForestInputMetadata.fullCode_length, Nat.zero_add] at afterLoader
  have setup := widened_prefix _ _ _ _ afterLoader
  have loop := widened_suffix _ _ _ _ afterLoader
  simp only [setupCode_length, Nat.reduceAdd] at loop
  exact ⟨loader, setup, loop⟩

theorem program_accept (width : Nat) :
    (program width)[55]? = some (.constant 4 (word width 1)) ∧
    (program width)[56]? = some .halt := by
  simp [program]

/-- Concrete register observations identify a low-register kernel boundary;
this equality performs no transition or reset. -/
theorem kernel_state (state : State width 8) (entry address loaded last : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (r0 : state.reg 0 = word width address) (r1 : state.reg 1 = word width loaded)
    (r2 : state.reg 2 = word width last) (r3 : state.reg 3 = word width 0) :
    RegisterWiden.widenState
      ((ForestCounter.counterState state.heap entry (word width address)
        (word width loaded) (word width last)).frame state.stack state.output) state.reg = state := by
  change State.mk _ state.heap state.stack state.output (word width entry) false =
    State.mk state.reg state.heap state.stack state.output state.pc state.halted
  rw [State.mk.injEq]
  refine ⟨?_, rfl, rfl, rfl, position.symm, running.symm⟩
  funext register
  fin_cases register <;> simp [ForestCounter.counterState, State.frame,
    r0, r1, r2, r3]

/-- The fixed program's post-loader suffix reads source tags, emits the
canonical channel vector, sets its acceptance register and halts. -/
theorem loaded_execution (state : State width 8) (channels : Nat) (bits : Nat → Bool)
    (position : state.pc = word width 33) (running : state.halted = false)
    (fits : 57 < 2 ^ width) (capacity : 4 * channels + 3 < 2 ^ width)
    (nonempty : 0 < state.heap.size) (header : state.heap[0] = word width channels)
    (inside : ∀ index, index < channels → 5 + 2 * (channels + index) < state.heap.size)
    (stored : ∀ index (below : index < channels),
      state.heap[5 + 2 * (channels + index)]'(inside index below) =
        word width (if bits index then 3 else 1)) :
    ∃ final ticks, Execution (program width) state final ticks (state.liveWords + channels) ∧
      ticks ≤ 13 * channels + 12 ∧ final.halted = true ∧ final.reg 4 = word width 1 ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = (List.range channels).map (fun index => boolWord width (bits index)) ++ state.output := by
  obtain ⟨prepared, setup, pc, active, heap, stack, output, r0, r1, r2, r3⟩ :=
    setup_execution (program width) state 33 channels position running (by omega) capacity nonempty header
      (program_blocks width).2.1
  have inner (index : Nat) : 2 * channels + 3 + 2 * (index + 1) = 5 + 2 * (channels + index) := by omega
  have preparedInside : ∀ index, index < channels →
      2 * channels + 3 + 2 * (index + 1) < prepared.heap.size := by
    intro index below
    rw [heap, inner]
    exact inside index below
  have preparedStored : ∀ index (below : index < channels),
      prepared.heap[2 * channels + 3 + 2 * (index + 1)]'(preparedInside index below) =
        word width (if bits index then 3 else 1) := by
    intro index below
    simpa only [heap, inner] using stored index below
  obtain ⟨loopTicks, low, loopTime⟩ := loop_execution (lowerProgram (program width)) prepared.heap 40
    (2 * channels + 3) bits channels (word width 3) (by omega)
    (by have equality : 2 * channels + 3 + 2 * channels = 4 * channels + 3 := by omega
        simpa only [equality] using capacity)
    preparedInside preparedStored (lower_block _ _ _ (program_blocks width).2.2)
  have address : 2 * channels + 3 + 2 * channels = 4 * channels + 3 := by omega
  rw [address] at low
  let vector := (List.range channels).map (fun index => boolWord width (bits index))
  let loopFinal := RegisterWiden.widenState
    ((ForestCounter.counterState prepared.heap 55 (word width (2 * channels + 3))
      (word width 0) (word width (2 * channels + 3))).frame prepared.stack (vector ++ prepared.output)) prepared.reg
  have framed := low.frame prepared.stack prepared.output
  have lifted := ForestZeroCallerWiden.execution (program width) _ _ _ _ framed rfl prepared.reg
  have initial := kernel_state prepared 40 (4 * channels + 3) 3 (2 * channels + 3)
    (by simpa using pc) active r0 r1 r2 r3
  have loopTrace : Execution (program width) prepared loopFinal loopTicks
      (5 + prepared.heap.size + channels + (prepared.stack.length + prepared.output.length) + 4) := by
    rw [initial] at lifted
    exact lifted
  have preparedLive : prepared.liveWords = state.liveWords := by
    simp only [State.liveWords, heap, stack, output]
  have loopPeak : 5 + prepared.heap.size + channels +
      (prepared.stack.length + prepared.output.length) + 4 = state.liveWords + channels := by
    simp only [State.liveWords] at preparedLive ⊢
    omega
  rw [loopPeak] at loopTrace
  have vectorLength : vector.length = channels := by simp [vector]
  have finalLive : loopFinal.liveWords = state.liveWords + channels := by
    simp only [loopFinal, RegisterWiden.widenState_liveWords, State.frame_liveWords,
      ForestCounter.counterState_liveWords, List.length_append, vectorLength]
    simp only [State.liveWords] at preparedLive ⊢
    omega
  obtain ⟨accepted, accept, acceptPC, acceptedTag, acceptHeap, acceptStack, acceptOutput, acceptRunning, _⟩ :=
    SharedEvaluationReclaim.constant_execution (program width) 55 1 4 loopFinal rfl rfl (by omega)
      (program_accept width).1
  let final : State width 8 := { accepted.advance with halted := true }
  have lastStep : programStep (program width) accepted = some final := by
    rw [RawTransferLoops.fetched (program width) accepted 56 .halt acceptPC (by omega) (program_accept width).2]
    simp [step, acceptRunning, final]
  have haltTrace := Execution.cons lastStep (Execution.refl final)
  have acceptedLive : accepted.liveWords = state.liveWords + channels := by
    simp only [State.liveWords, acceptHeap, acceptStack, acceptOutput]
    exact finalLive
  have haltedLive : final.liveWords = accepted.liveWords := rfl
  rw [haltedLive, Nat.max_self, acceptedLive] at haltTrace
  have trace := ((setup.append loopTrace).append accept).append haltTrace
  refine ⟨final, 7 + loopTicks + 1 + 1, ?_, by omega, rfl, acceptedTag, ?_, ?_, ?_⟩
  · simpa only [finalLive, Nat.max_self,
      Nat.max_eq_right (by omega : state.liveWords ≤ state.liveWords + channels)] using trace
  · change accepted.heap = state.heap
    rw [acceptHeap]
    exact heap
  · change accepted.stack = state.stack
    rw [acceptStack]
    exact stack
  · change accepted.output = _
    rw [acceptOutput]
    change vector ++ prepared.output = _
    rw [output]

/-- A single fixed resident loads the complete original source packet, scans
the tag interval, emits its canonical vector, accepts and halts. The input
packet, retained output and caller suffix all contribute to the live bound. -/
theorem cold_execution (state : State width 8)
    (channels nodes children guards roots : Nat) (bits : Nat → Bool)
    (payload suffix : List (Word width))
    (position : state.pc = word width 0) (running : state.halted = false)
    (empty : state.heap = #[]) (zero : state.reg 3 = word width 0)
    (input : state.stack = ForestInputMetadata.headerWords width channels nodes children guards roots ++ payload ++ suffix)
    (lengthEq : payload.length = 6 * nodes + children + guards + roots)
    (fits : 57 < 2 ^ width) (capacity : 4 * channels + 3 < 2 ^ width)
    (room : 5 + payload.length ≤ 2 ^ width)
    (inside : ∀ index, index < channels →
      5 + 2 * (channels + index) <
        ((ForestInputMetadata.headerWords width channels nodes children guards roots).toArray ++ payload.toArray).size)
    (stored : ∀ index (below : index < channels),
      ((ForestInputMetadata.headerWords width channels nodes children guards roots).toArray ++ payload.toArray)[
        5 + 2 * (channels + index)]'(inside index below) = word width (if bits index then 3 else 1)) :
    ∃ final ticks, Execution (program width) state final ticks (state.liveWords + channels) ∧
      ticks ≤ 39 + 7 * payload.length + 13 * channels ∧
      final.halted = true ∧ final.reg 4 = word width 1 ∧
      final.heap = (ForestInputMetadata.headerWords width channels nodes children guards roots).toArray ++ payload.toArray ∧
      final.stack = suffix ∧
      final.output = (List.range channels).map (fun index => boolWord width (bits index)) ++ state.output := by
  obtain ⟨loaded, load, heap, stack, output, pc, active, _⟩ :=
    ForestRootProjection.cold_packet_eight_execution (program width) 0 channels nodes children guards roots
      payload suffix state position running empty zero input lengthEq (by omega) room (program_blocks width).1
  have nonempty : 0 < loaded.heap.size := by
    simp only [heap, Array.size_append, List.size_toArray, ForestInputMetadata.headerWords,
      List.length_cons, List.length_nil]
    omega
  have header : loaded.heap[0] = word width channels := by
    simp [heap, ForestInputMetadata.headerWords]
  obtain ⟨final, ticks, body, time, halted, accepted, finalHeap, finalStack, finalOutput⟩ :=
    loaded_execution loaded channels bits (by simpa using pc) active fits capacity nonempty header
      (by intro index below; simpa only [heap] using inside index below)
      (by intro index below; simpa only [heap] using stored index below)
  have loadedLive : loaded.liveWords = state.liveWords := by
    simp only [State.liveWords, heap, stack, output, empty, input,
      Array.size_append, List.size_toArray, List.length_append, ForestInputMetadata.headerWords,
      List.length_cons, List.length_nil]
    omega
  rw [loadedLive] at body
  have trace := load.append body
  refine ⟨final, 27 + 7 * payload.length + ticks, ?_, by omega, halted, accepted,
    finalHeap.trans heap, finalStack.trans stack, ?_⟩
  · simpa only [Nat.max_eq_right (by omega : state.liveWords ≤ state.liveWords + channels)] using trace
  · rw [finalOutput, output]

end Controller.Cost.CriticalSourceScan
