module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.CriticalSets
public import Controller.Cost.ForestMarkerMachine
public import Mathlib.Data.Nat.Bitwise

@[expose] public section


/-! A fixed source-tag scanner for the critical-set and modulo-cycle layouts.
The program reads the channel count and the original node headers. Neither
the hidden set nor a selected witness occurs in its instruction image. -/
namespace Controller.Cost.CriticalSourceScan

open Controller Controller.Decoder Controller.Decoder.DAG Controller.Boundaries
open Controller.Cost.GateProgram Controller.Cost.ForestCounter
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored

variable {n width : Nat}

/-- Registers hold source address, scratch, end address, and constant zero. -/
def loopCode (width base : Nat) : GateProgram.Code width :=
  [.xor 1 0 2, .branchZero 1 (word width (base + 14)), .load 1 0,
    .constant 3 (word width 3), .xor 1 1 3, .constant 3 (word width 0),
    .branchZero 1 (word width (base + 9)), .constant 1 (word width 0),
    .branchZero 3 (word width (base + 10)), .constant 1 (word width 1),
    .emit 1, .constant 1 (word width (2 ^ width - 2)), .add 0 0 1,
    .branchZero 3 (word width base), .branchZero 3 (word width (base + 15))]

def setupCode (width : Nat) : GateProgram.Code width :=
  [.constant 3 (word width 0), .load 2 3, .add 2 2 2, .add 0 2 2,
    .constant 1 (word width 3), .add 0 0 1, .add 2 2 1]

/-- The same 55 instructions serve every valid source instance at this width. -/
def code (width : Nat) : GateProgram.Code width :=
  ForestInputMetadata.fullCode width 0 ++ setupCode width ++ loopCode width 40

def program (width : Nat) : Program width 8 :=
  ((code width).map RegisterWiden.widenInstruction).toArray ++
    #[.constant 4 (word width 1), .halt]

@[simp] theorem loopCode_length (width base : Nat) : (loopCode width base).length = 15 := rfl
@[simp] theorem setupCode_length (width : Nat) : (setupCode width).length = 7 := rfl
@[simp] theorem code_length (width : Nat) : (code width).length = 55 := by
  simp [code]

@[simp] theorem program_size (width : Nat) : (program width).size = 57 := by
  simp [program]

def termNode (n : Nat) (channel : Channel n) : Fin (2 * n + 1) :=
  ⟨n + channel.val, by omega⟩

theorem critical_tag (K : Finset (Channel n)) (channel : Channel n) :
    tagValue (criticalDAG K) (termNode n channel) = if channel ∈ K then 3 else 1 := by
  have first : ¬n + channel.val < n := by omega
  have second : n + channel.val < 2 * n := by have := channel.isLt; omega
  by_cases member : channel ∈ K <;>
    simp [tagValue, criticalDAG, termNode, first, second, member]

theorem cycle_tag (channel : Channel n) :
    tagValue (CriticalSets.cycleDAG n) (termNode n channel) = 3 := by
  have first : ¬n + channel.val < n := by omega
  have second : n + channel.val < 2 * n := by have := channel.isLt; omega
  simp [tagValue, CriticalSets.cycleDAG, termNode, first, second]

/-- This is a cell of the original complete source packet, not a precomputed
eligible-set vector. The graph is only the representation specification. -/
theorem critical_source_cell (K : Finset (Channel n)) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch (criticalDAG K) rows) (initialHeap : Array (Word width)) (channel : Channel n) :
    (cacheHeap width initialHeap rows roots)[initialHeap.size + 2 * (n + channel.val)]'(
      by
        have bound : n + channel.val < rows.length := by
          rw [matched.length_eq]
          change n + channel.val < 2 * n + 1
          omega
        simp only [cacheHeap_size]
        omega) = word width (if channel ∈ K then 3 else 1) := by
  have cell := cache_tag_word initialHeap (criticalDAG K) rows roots matched (termNode n channel)
  rw [critical_tag] at cell
  simpa only [termNode] using cell

private theorem advance_state (heap : Array (Word width)) (cursor : Nat)
    (address loaded last : Word width) (fits : cursor < 2 ^ width) :
    (counterState heap cursor address loaded last).advance =
      counterState heap (cursor + 1) address loaded last := by
  unfold State.advance counterState
  rw [show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits]

private theorem put_loaded (heap : Array (Word width)) (cursor : Nat)
    (address loaded last value : Word width) :
    (counterState heap cursor address loaded last).put 1 value =
      counterState heap cursor address value last := by
  unfold State.put counterState
  congr 1
  funext register
  fin_cases register <;> rfl

theorem xor_transition (machine : Program width 4) (heap : Array (Word width))
    (cursor : Nat) (address loaded last : Word width) (fits : cursor < 2 ^ width)
    (fetched : machine[cursor]? = some (.xor 1 0 2)) :
    programStep machine (counterState heap cursor address loaded last) =
      some (counterState heap (cursor + 1) address
        (word width (Nat.xor address.val last.val)) last) := by
  unfold programStep
  rw [show (counterState heap cursor address loaded last).pc.val = cursor from
    Nat.mod_eq_of_lt fits, fetched]
  change step (.xor (1 : Fin 4) 0 2) (counterState heap cursor address loaded last) = _
  simp only [step, counterState, Bool.false_eq_true, if_false]
  change some ((counterState heap cursor address loaded last).advance.put 1
    (word width (Nat.xor address.val last.val))) = _
  rw [advance_state heap cursor address loaded last fits, put_loaded]
  rfl

theorem emit_transition (machine : Program width 4) (heap : Array (Word width))
    (cursor : Nat) (address loaded last : Word width) (fits : cursor < 2 ^ width)
    (fetched : machine[cursor]? = some (.emit 1)) :
    programStep machine (counterState heap cursor address loaded last) =
      some ((counterState heap (cursor + 1) address loaded last).frame [] [loaded]) := by
  unfold programStep
  rw [show (counterState heap cursor address loaded last).pc.val = cursor from
    Nat.mod_eq_of_lt fits, fetched]
  change step (.emit (1 : Fin 4)) (counterState heap cursor address loaded last) = _
  simp only [step, counterState, Bool.false_eq_true, if_false]
  change some { (counterState heap cursor address loaded last).advance with output := [loaded] } = _
  rw [advance_state heap cursor address loaded last fits]
  rfl

private theorem fetch (machine : Program width 4) (state : State width 4)
    (cursor : Nat) (instruction : Instruction width 4)
    (position : state.pc = word width cursor) (fits : cursor < 2 ^ width)
    (entry : machine[cursor]? = some instruction) :
    programStep machine state = step instruction state := by
  unfold programStep
  rw [position, show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits, entry]
  rfl

/-- Three fetched instructions compare a stored tag with the guard tag and
restore the fixed zero register. Nonmembers have input tag one, not zero. -/
theorem normalize_tag (machine : Program width 4) (heap : Array (Word width))
    (base : Nat) (address loaded last : Word width) (fits : base + 3 < 2 ^ width)
    (block : BlockAt machine base
      [.constant 3 (word width 3), .xor 1 1 3, .constant 3 (word width 0)]) :
    Execution machine (counterState heap base address loaded last)
      (counterState heap (base + 3) address (word width (Nat.xor loaded.val 3)) last)
      3 (5 + heap.size) := by
  let initial := counterState heap base address loaded last
  let first := initial.advance.put 3 (word width 3)
  let second := first.advance.put 1 (word width (Nat.xor loaded.val 3))
  let final := second.advance.put 3 (word width 0)
  have position0 : initial.pc = word width base := rfl
  have position1 : first.pc = word width (base + 1) := by
    simp [first, initial, counterState, State.advance, State.put,
      show (word width base).val = base from Nat.mod_eq_of_lt (by omega)]
  have position2 : second.pc = word width (base + 2) := by
    simp only [second, State.put, State.advance, position1]
    rw [show (word width (base + 1)).val = base + 1 from Nat.mod_eq_of_lt (by omega)]
  have position3 : final.pc = word width (base + 3) := by
    simp only [final, State.put, State.advance, position2]
    rw [show (word width (base + 2)).val = base + 2 from Nat.mod_eq_of_lt (by omega)]
  have firstStep : programStep machine initial = some first := by
    rw [fetch machine initial base (.constant 3 (word width 3)) position0 (by omega)
      (by simpa using block 0 (by simp))]
    simp [step, initial, first, counterState]
  have secondStep : programStep machine first = some second := by
    rw [fetch machine first (base + 1) (.xor 1 1 3) position1 (by omega)
      (by simpa using block 1 (by simp))]
    simp [step, first, second, initial, State.put, State.advance, counterState,
      show (word width 3).val = 3 from Nat.mod_eq_of_lt (by omega)]
  have thirdStep : programStep machine second = some final := by
    rw [fetch machine second (base + 2) (.constant 3 (word width 0)) position2 (by omega)
      (by simpa using block 2 (by simp))]
    simp [step, second, first, initial, final, State.put, State.advance, counterState]
  have registers : final.reg =
      (counterState heap (base + 3) address (word width (Nat.xor loaded.val 3)) last).reg := by
    funext register
    fin_cases register <;> simp [final, second, first, initial, State.put, State.advance, counterState]
  have endpoint : final =
      counterState heap (base + 3) address (word width (Nat.xor loaded.val 3)) last := by
    change State.mk final.reg final.heap final.stack final.output final.pc final.halted = _
    rw [counterState, State.mk.injEq]
    exact ⟨registers, rfl, rfl, rfl, position3, rfl⟩
  have trace := Execution.cons firstStep (Execution.cons secondStep
    (Execution.cons thirdStep (Execution.refl final)))
  rw [endpoint] at trace
  convert trace using 1
  simp only [first, second, initial, State.put, State.advance,
    State.liveWords, counterState, List.length_nil, Nat.add_zero, Nat.max_self]
  omega

/-- The first three fetched instructions test the source cursor against its
end and load the next real tag. The endpoint is an address, not an answer. -/
theorem read_tag (machine : Program width 4) (heap : Array (Word width))
    (base address stop : Nat) (loaded : Word width) (fits : base + 15 < 2 ^ width)
    (addressFits : address < 2 ^ width) (stopFits : stop < 2 ^ width)
    (earlier : stop < address) (inside : address < heap.size) (tag : Word width)
    (stored : heap[address] = tag) (block : BlockAt machine base (loopCode width base)) :
    Execution machine (counterState heap base (word width address) loaded (word width stop))
      (counterState heap (base + 3) (word width address) tag (word width stop))
      3 (5 + heap.size) := by
  have addressValue : (word width address).val = address := Nat.mod_eq_of_lt addressFits
  have stopValue : (word width stop).val = stop := Nat.mod_eq_of_lt stopFits
  have xorFits : Nat.xor address stop < 2 ^ width := Nat.xor_lt_two_pow addressFits stopFits
  have different : Nat.xor address stop ≠ 0 := by
    intro equal
    have same : stop = address := by
      calc
        stop = Nat.xor (Nat.xor address address) stop := by
          simp only [Nat.xor_eq, Nat.xor_self, Nat.zero_xor]
        _ = Nat.xor address (Nat.xor address stop) := Nat.xor_assoc _ _ _
        _ = address := by rw [equal]; simp only [Nat.xor_eq, Nat.xor_zero]
    omega
  have first := xor_transition machine heap base (word width address) loaded (word width stop)
    (by omega) (by simpa [loopCode] using block 0 (by simp))
  rw [addressValue, stopValue] at first
  have second := ForestMarkerMachine.branch_transition machine heap (base + 1) (base + 14) 1
    (word width address) (word width (Nat.xor address stop)) (word width stop)
    (by omega) (by simpa [loopCode] using block 1 (by simp))
  have second' : programStep machine
      (counterState heap (base + 1) (word width address) (word width (Nat.xor address stop)) (word width stop)) =
      some (counterState heap (base + 2) (word width address) (word width (Nat.xor address stop)) (word width stop)) := by
    have selector : ((counterState heap (base + 1) (word width address)
        (word width (Nat.xor address stop)) (word width stop)).reg 1).val = Nat.xor address stop := by
      change (word width (Nat.xor address stop)).val = Nat.xor address stop
      exact Nat.mod_eq_of_lt xorFits
    rw [selector, if_neg different] at second
    simpa only [Nat.add_assoc] using second
  have third := ForestCounter.read_transition machine heap (base + 2) address
    (word width (Nat.xor address stop)) (word width stop) tag (by omega) addressFits inside stored
    (by simpa [loopCode] using block 2 (by simp))
  have trace := Execution.cons first (Execution.cons second'
    (Execution.cons third (Execution.refl
      (counterState heap (base + 2 + 1) (word width address) tag (word width stop)))))
  simpa only [counterState_liveWords, Nat.max_self, Nat.reduceAdd, Nat.add_assoc] using trace

theorem emit_advance (machine : Program width 4) (heap : Array (Word width))
    (base address stop : Nat) (bit : Bool) (fits : base + 15 < 2 ^ width)
    (addressFits : address < 2 ^ width) (positive : 2 ≤ address)
    (block : BlockAt machine base (loopCode width base)) :
    Execution machine
      (counterState heap (base + 10) (word width address) (boolWord width bit) (word width stop))
      ((counterState heap base (word width (address - 2)) (word width (2 ^ width - 2)) (word width stop)).frame
        [] [boolWord width bit]) 4 (6 + heap.size) := by
  have first := emit_transition machine heap (base + 10) (word width address)
    (boolWord width bit) (word width stop) (by omega)
    (by simpa [loopCode] using block 10 (by simp))
  have second := ForestMarkerMachine.constant_loaded_transition machine heap (base + 11)
    (word width address) (boolWord width bit) (word width stop) (word width (2 ^ width - 2)) (by omega)
    (by simpa [loopCode] using block 11 (by simp))
  have third := ForestMarkerMachine.add_address_transition machine heap (base + 12)
    (word width address) (word width (2 ^ width - 2)) (word width stop) (by omega)
    (by simpa [loopCode] using block 12 (by simp))
  rw [show (word width address).val = address from Nat.mod_eq_of_lt addressFits,
    show (word width (2 ^ width - 2)).val = 2 ^ width - 2 from Nat.mod_eq_of_lt (by omega)] at third
  have decrement : word width (address + (2 ^ width - 2)) = word width (address - 2) := by
    apply Fin.ext
    change (address + (2 ^ width - 2)) % (2 ^ width) = (address - 2) % (2 ^ width)
    rw [show address + (2 ^ width - 2) = (address - 2) + 2 ^ width by omega, Nat.add_mod_right]
  rw [decrement] at third
  have fourth := ForestMarkerMachine.branch_transition machine heap (base + 13) base 3
    (word width (address - 2)) (word width (2 ^ width - 2)) (word width stop) (by omega)
    (by simpa [loopCode] using block 13 (by simp))
  have fourth' : programStep machine
      (counterState heap (base + 13) (word width (address - 2)) (word width (2 ^ width - 2)) (word width stop)) =
      some (counterState heap base (word width (address - 2)) (word width (2 ^ width - 2)) (word width stop)) := by
    simpa [counterState, word] using fourth
  simp only [Nat.add_assoc] at first second third
  have trace := Execution.cons first (Execution.cons
    (programStep_frame machine _ _ [] [boolWord width bit] second)
    (Execution.cons (programStep_frame machine _ _ [] [boolWord width bit] third)
      (Execution.cons (programStep_frame machine _ _ [] [boolWord width bit] fourth')
        (Execution.refl ((counterState heap base (word width (address - 2))
          (word width (2 ^ width - 2)) (word width stop)).frame [] [boolWord width bit])))))
  convert trace using 1
  simp only [State.frame_liveWords, counterState_liveWords, List.length_cons, List.length_nil]
  omega

theorem select_bit (machine : Program width 4) (heap : Array (Word width))
    (base : Nat) (address last : Word width) (bit : Bool) (fits : base + 15 < 2 ^ width)
    (block : BlockAt machine base (loopCode width base)) :
    ∃ ticks, Execution machine
      (counterState heap (base + 6) address (word width (Nat.xor (if bit then 3 else 1) 3)) last)
      (counterState heap (base + 10) address (boolWord width bit) last)
      ticks (5 + heap.size) ∧ ticks ≤ 3 := by
  cases bit with
  | false =>
      have first := ForestMarkerMachine.branch_transition machine heap (base + 6) (base + 9) 1
        address (word width 2) last (by omega) (by simpa [loopCode] using block 6 (by simp))
      have first' : programStep machine (counterState heap (base + 6) address (word width 2) last) =
          some (counterState heap (base + 7) address (word width 2) last) := by
        simpa [counterState, word, Nat.mod_eq_of_lt (by omega : 2 < 2 ^ width), Nat.add_assoc] using first
      have second := ForestMarkerMachine.constant_loaded_transition machine heap (base + 7)
        address (word width 2) last (word width 0) (by omega)
        (by simpa [loopCode] using block 7 (by simp))
      have third := ForestMarkerMachine.branch_transition machine heap (base + 8) (base + 10) 3
        address (word width 0) last (by omega) (by simpa [loopCode] using block 8 (by simp))
      have third' : programStep machine (counterState heap (base + 8) address (word width 0) last) =
          some (counterState heap (base + 10) address (word width 0) last) := by
        simpa [counterState, word] using third
      simp only [Nat.add_assoc] at second
      have trace := Execution.cons first' (Execution.cons second
        (Execution.cons third' (Execution.refl (counterState heap (base + 10) address (word width 0) last))))
      exact ⟨3, by simpa [counterState_liveWords, boolWord] using trace, by decide⟩
  | true =>
      have first := ForestMarkerMachine.branch_transition machine heap (base + 6) (base + 9) 1
        address (word width 0) last (by omega) (by simpa [loopCode] using block 6 (by simp))
      have first' : programStep machine (counterState heap (base + 6) address (word width 0) last) =
          some (counterState heap (base + 9) address (word width 0) last) := by
        simpa [counterState, word] using first
      have second := ForestMarkerMachine.constant_loaded_transition machine heap (base + 9)
        address (word width 0) last (word width 1) (by omega)
        (by simpa [loopCode] using block 9 (by simp))
      simp only [Nat.add_assoc] at second
      have trace := Execution.cons first' (Execution.cons second
        (Execution.refl (counterState heap (base + 10) address (word width 1) last)))
      exact ⟨2, by simpa [counterState_liveWords, boolWord] using trace, by decide⟩

/-- An entire scan iteration reads the source tag and emits its membership
bit in at most thirteen fetched instructions. All branch targets are fixed. -/
theorem iteration (machine : Program width 4) (heap : Array (Word width))
    (base address stop : Nat) (loaded : Word width) (bit : Bool)
    (fits : base + 15 < 2 ^ width) (addressFits : address < 2 ^ width)
    (positive : 2 ≤ address) (stopFits : stop < 2 ^ width)
    (earlier : stop < address) (inside : address < heap.size)
    (stored : heap[address] = word width (if bit then 3 else 1))
    (block : BlockAt machine base (loopCode width base)) :
    ∃ ticks, Execution machine (counterState heap base (word width address) loaded (word width stop))
      ((counterState heap base (word width (address - 2)) (word width (2 ^ width - 2)) (word width stop)).frame
        [] [boolWord width bit]) ticks (6 + heap.size) ∧ ticks ≤ 13 := by
  have reading := read_tag machine heap base address stop loaded fits addressFits stopFits earlier inside _ stored block
  have normalBlock : BlockAt machine (base + 3)
      [.constant 3 (word width 3), .xor 1 1 3, .constant 3 (word width 0)] := by
    intro offset bounded
    have small : offset < 3 := by simpa using bounded
    interval_cases offset
    · simpa [loopCode, Nat.add_assoc] using block 3 (by simp)
    · simpa [loopCode, Nat.add_assoc] using block 4 (by simp)
    · simpa [loopCode, Nat.add_assoc] using block 5 (by simp)
  have normal := normalize_tag machine heap (base + 3) (word width address)
    (word width (if bit then 3 else 1)) (word width stop) (by omega) normalBlock
  have tagFits : (if bit then 3 else 1) < 2 ^ width := by
    cases bit
    · change 1 < 2 ^ width
      omega
    · change 3 < 2 ^ width
      omega
  rw [show (word width (if bit then 3 else 1)).val = (if bit then 3 else 1) from
    Nat.mod_eq_of_lt tagFits] at normal
  simp only [Nat.add_assoc] at normal
  obtain ⟨selectTicks, selection, selectionTime⟩ :=
    select_bit machine heap base (word width address) (word width stop) bit fits block
  have emission := emit_advance machine heap base address stop bit fits addressFits positive block
  refine ⟨3 + 3 + selectTicks + 4, ?_, by omega⟩
  have trace := ((reading.append normal).append selection).append emission
  simpa only [Nat.max_self, Nat.max_eq_right (by omega : 5 + heap.size ≤ 6 + heap.size)] using trace

theorem exit (machine : Program width 4) (heap : Array (Word width))
    (base stop : Nat) (loaded : Word width) (fits : base + 15 < 2 ^ width)
    (stopFits : stop < 2 ^ width) (block : BlockAt machine base (loopCode width base)) :
    Execution machine (counterState heap base (word width stop) loaded (word width stop))
      (counterState heap (base + 15) (word width stop) (word width 0) (word width stop))
      3 (5 + heap.size) := by
  have first := xor_transition machine heap base (word width stop) loaded (word width stop)
    (by omega) (by simpa [loopCode] using block 0 (by simp))
  rw [show (word width stop).val = stop from Nat.mod_eq_of_lt stopFits] at first
  have same : Nat.xor stop stop = 0 := by simp only [Nat.xor_eq, Nat.xor_self]
  rw [same] at first
  have second := ForestMarkerMachine.branch_transition machine heap (base + 1) (base + 14) 1
    (word width stop) (word width 0) (word width stop) (by omega)
    (by simpa [loopCode] using block 1 (by simp))
  have second' : programStep machine
      (counterState heap (base + 1) (word width stop) (word width 0) (word width stop)) =
      some (counterState heap (base + 14) (word width stop) (word width 0) (word width stop)) := by
    simpa [counterState, word] using second
  have third := ForestMarkerMachine.branch_transition machine heap (base + 14) (base + 15) 3
    (word width stop) (word width 0) (word width stop) (by omega)
    (by simpa [loopCode] using block 14 (by simp))
  have third' : programStep machine
      (counterState heap (base + 14) (word width stop) (word width 0) (word width stop)) =
      some (counterState heap (base + 15) (word width stop) (word width 0) (word width stop)) := by
    simpa [counterState, word] using third
  have trace := Execution.cons first (Execution.cons second'
    (Execution.cons third' (Execution.refl
      (counterState heap (base + 15) (word width stop) (word width 0) (word width stop)))))
  simpa only [counterState_liveWords, Nat.max_self, Nat.reduceAdd] using trace

/-- Descending physical reads produce the canonical ascending channel vector.
The clock includes every guard comparison, output and the actual exit jumps. -/
theorem loop_execution (machine : Program width 4) (heap : Array (Word width))
    (base stop : Nat) (bits : Nat → Bool) (count : Nat) (loaded : Word width)
    (fits : base + 15 < 2 ^ width) (capacity : stop + 2 * count < 2 ^ width)
    (inside : ∀ index, index < count → stop + 2 * (index + 1) < heap.size)
    (stored : ∀ index (below : index < count),
      heap[stop + 2 * (index + 1)]'(inside index below) = word width (if bits index then 3 else 1))
    (block : BlockAt machine base (loopCode width base)) :
    ∃ ticks, Execution machine
      (counterState heap base (word width (stop + 2 * count)) loaded (word width stop))
      ((counterState heap (base + 15) (word width stop) (word width 0) (word width stop)).frame
        [] ((List.range count).map (fun index => boolWord width (bits index))))
      ticks (5 + heap.size + count) ∧ ticks ≤ 13 * count + 3 := by
  induction count generalizing loaded with
  | zero =>
      have stopped := exit machine heap base stop loaded fits (by simpa using capacity) block
      exact ⟨3, by simpa [State.frame, counterState] using stopped, by decide⟩
  | succ count ih =>
      obtain ⟨headTicks, head, headTime⟩ := iteration machine heap base (stop + 2 * (count + 1)) stop
        loaded (bits count) fits capacity (by omega) (by omega) (by omega)
        (inside count (by omega)) (stored count (by omega)) block
      have next : stop + 2 * (count + 1) - 2 = stop + 2 * count := by omega
      rw [next] at head
      obtain ⟨tailTicks, tail, tailTime⟩ := ih (word width (2 ^ width - 2)) (by omega)
        (fun index below => inside index (by omega)) (fun index below => stored index (by omega))
      have trace := head.append (tail.frame [] [boolWord width (bits count)])
      have peak : max (6 + heap.size) (5 + heap.size + count + (0 + 1)) =
          5 + heap.size + (count + 1) := by omega
      simp only [List.length_nil, List.length_cons] at trace
      rw [peak] at trace
      refine ⟨headTicks + tailTicks, ?_, by omega⟩
      simpa [State.frame, List.range_succ, List.map_append, List.append_assoc] using trace

end Controller.Cost.CriticalSourceScan
