module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ResolvedQueryStorage

@[expose] public section


/-! Compositional instruction-list storage in the source word model. Append
copies its left spine and shares its right input. Widening, redirection and
relocation retain their input while forming a new image. Leaves are checked
instruction recipes, operand emitters and the source/native query certificates. -/
namespace Controller.Cost.AssemblyStorage

open Controller Controller.Decoder Controller.Cost Controller.Extensions
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.WordConstructionRecipe Controller.Cost.ForestIndexedOperands

inductive Trace (width : Nat) : {registers : Nat} → List (Instruction width registers) → Nat → Prop
  | empty : Trace width [] 0
  | recipes {environment : Fin parameters → Nat} {recipes : List
      (InstructionRecipe parameters width registers)} {output ticks peak}
      (formed : WordConstructionStorage.Trace environment recipes output ticks peak) :
      Trace width output peak
  | stream {recipes : List (InstructionRecipe parameters width registers)}
      {records start count output ticks peak}
      (formed : TemplateStreamConstruction.Trace recipes records start count output ticks peak) :
      Trace width output peak
  | append {left right : List (Instruction width registers)} {p q}
      (first : Trace width left p) (second : Trace width right q)
      (copied : CompilerAppendTrace.AppendTrace left right (left ++ right) left.length) :
      Trace width (left ++ right) (p + q + 32 * left.length + 32)
  | preparation {discarded output : List (Instruction width registers)} {first later}
      (prepared : Trace width discarded first) (formed : Trace width output later) :
      Trace width output (first + later + 32 * discarded.length + 32)
  | widen {source : List (Instruction width 4)} {peak}
      (formed : Trace width source peak) :
      Trace width (source.map RegisterWiden.widenInstruction) (peak + 32 * source.length)
  | redirect {source : List (Instruction width 8)} {peak}
      (formed : Trace width source peak) :
      Trace width (source.map WitnessStack.redirect) (peak + 32 * source.length)
  | relocated {source : List (Instruction width 8)} {output ticks peak extra delta}
      (formed : Trace width source peak)
      (moved : ProgramRelocationConstruction.Trace delta source output ticks extra) :
      Trace width output (peak + extra + 32 * source.length)
  | operands {entry : Nat} {values : List (ResolvedSourceEmit.Operand width)}
      {output ticks peak} (formed : SourceOperandConstruction.Trace width entry values output
        ticks peak) : Trace width output (peak + 32 * values.length)
  | native (parameters : Parameters) (base entry : Nat)
      (certificate : NativeFinishStorage.Certificate parameters width base entry) :
      Trace width (NativeContinuationConstruction.finish parameters width base entry).1
        (NativeFinishStorage.buffers parameters width base entry certificate)
  | callback (graph : DAG n) (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
      (b : Nat) (target : Channel n) (reference : Fin graph.nodeCount)
      (rootSlot entry sourceCount found rejected : Nat)
      (certificate : ResolvedQueryStorage.Callback width graph packet rows roots b target reference
        rootSlot entry sourceCount found rejected) :
      Trace width (ResolvedCallbackConstruction.build width graph packet rows roots b target
        reference rootSlot entry sourceCount found rejected).1
        (ResolvedQueryStorage.callbackBuffers width graph packet rows roots b target reference
          rootSlot entry sourceCount found rejected certificate)
  | nativeQuery (parameters : Parameters) (entry next : Nat)
      (reference : Fin parameters.decoder.nodeCount)
      (certificate : ResolvedQueryStorage.Native parameters width entry next reference) :
      Trace width (ResolvedNativeQueryConstruction.build parameters width entry next reference).1
        (ResolvedQueryStorage.nativeBuffers parameters width entry next reference certificate)
  | front (graph : DAG n) (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
      (b : Nat) (target : Channel n) (rootSlot entry sourceCount : Nat)
      (certificate : ResolvedFrontStorage.Certificate width graph packet rows roots b target
          rootSlot
        entry sourceCount) :
      Trace width (ResolvedFrontConstruction.prepare width graph packet rows roots b target rootSlot
        entry sourceCount).1
        (ResolvedFrontStorage.buffers width graph packet rows roots b target rootSlot entry
          sourceCount certificate)
  | enlarge {output : List (Instruction width registers)} {peak bound}
      (formed : Trace width output peak) (bounded : peak ≤ bound) : Trace width output bound

abbrev Bounded (output : List (Instruction width registers)) (bound : Nat) : Prop :=
  Trace width output bound

theorem wordCode (environment : Fin parameters → Nat)
    (recipes : List (InstructionRecipe parameters width registers)) :
    Bounded (evaluate environment recipes) (32 * work recipes) := by
  obtain ⟨peak, formed, bound⟩ := WordConstructionStorage.construction environment recipes
  exact .enlarge (.recipes formed) bound

theorem constant (destination : Fin registers) (value : Nat) :
    Bounded [Instruction.constant destination (word width value)] 320 := by
  exact wordCode (fun _ : Fin 0 => 0) [.constant destination (.literal value)]

theorem branch (source : Fin registers) (target : Nat) :
    Bounded [Instruction.branchZero source (word width target)] 320 := by
  exact wordCode (fun _ : Fin 0 => 0) [.branchZero source (.literal target)]

theorem fixed (instruction : Instruction width registers)
    (_plain : match instruction with | .constant .. | .branchZero .. => False | _ => True) :
    Bounded [instruction] 256 :=
  wordCode (fun _ : Fin 0 => 0) [.plain instruction]

theorem join (first : Bounded (width := width) left p) (second : Bounded right q) :
    Bounded (left ++ right) (p + q + 32 * left.length + 32) :=
  .append first second (CompilerAppendTrace.append_exists left right)

theorem relocate (formed : Bounded (width := width) source peak) (delta : Nat) :
    Bounded (ProgramRelocationConstruction.build delta source).1
      (peak + 288 * source.length + 16) := by
  obtain ⟨extra, moved, bound⟩ := ProgramRelocationConstruction.construction delta source
  exact .enlarge (.relocated formed moved) (by omega)

theorem operand (width entry : Nat) (values : List (ResolvedSourceEmit.Operand width)) :
    Bounded (SourceOperandConstruction.build width entry values).1
      (5032 * values.length + 32) := by
  obtain ⟨peak, formed, bound⟩ := SourceOperandConstruction.storage width entry values
  exact .enlarge (.operands formed) (by omega)

theorem native (parameters : Parameters) (width base entry : Nat) :
    Bounded (NativeContinuationConstruction.finish parameters width base entry).1
      (2000000 * ((selectedSize parameters).total + 1)) := by
  obtain ⟨certificate, bound⟩ := NativeFinishStorage.complete parameters width base entry
  exact .enlarge (.native parameters base entry certificate) bound

end Controller.Cost.AssemblyStorage
