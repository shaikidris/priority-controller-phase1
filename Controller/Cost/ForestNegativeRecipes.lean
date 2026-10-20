/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.ForestConstructionRecipes
import Controller.Cost.ForestCachedNegativeProgram

/-! Fixed negative-query kernels with explicit scalar operands. The variable
clause constructor is assembled separately between these two fixed streams. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Controller.Cost.ForestNegativeRecipes

open Controller.Cost Controller.Cost.ForestZeroResident
open Controller.Cost.ForestZeroAdmissibleCaller

private def widen (code : GateProgram.Code width) : Program width 8 :=
  (code.map RegisterWiden.widenInstruction).toArray

def entryCode (width sourceBase : Nat) : List (Instruction width 8) :=
  [reuseEntryCode width, widen (keepCode width), #[.constant 0 (word width sourceBase)]].flatMap Array.toList

def suffix (width protectedEnd base count query next : Nat) : List (Instruction width 8) :=
  let recordStart := base + 5 * count + 4
  [scratchCountCode width,
   Controller.Horn.TrackedAllocate.code width (query + 11),
   scratchHeaderCode width, scratchEndpointCode, saveProjectionCode,
   Controller.Horn.NormalizeCNF.code width (query + 42) count base
     protectedEnd (protectedEnd + 1) (protectedEnd + 2) (protectedEnd + 3) (protectedEnd + 4),
   ForestZeroHeaderBridge.saveCode width protectedEnd,
   Controller.Horn.IndexScan.code (n := count) width base recordStart (query + 210),
   ForestZeroHeaderBridge.restoreCode width, ForestZeroReclaim.captureCode width,
   ForestZeroSeedSetup.code (n := count) width base protectedEnd recordStart (query + 261),
   Controller.Horn.WorklistSeed.code (n := count) width base (query + 261) (query + 308) (query + 382),
   Controller.Horn.WorklistAccept.headSetupCode (n := count) width base (query + 312),
   Controller.Horn.WorklistFIFO.fetchCode (n := count) width base (query + 312) (query + 369) (query + 331),
   Controller.Horn.WorklistFIFO.advanceCode (n := count) width base (query + 312),
   Controller.Horn.WorklistBucketLoop.code width (query + 331) (query + 326) (query + 343),
   Controller.Horn.WorklistBucketReady.code (n := count) width base (query + 343) (query + 326) (query + 382) (query + 331),
   ForestZeroAnswer.savedCode width 1 (query + 395),
   ForestZeroAnswer.savedCode width 0 (query + 430),
   projectionConstantsCode width, channelPrepareCode width,
   ForestZeroChannelEmit.code width (query + 416) (query + 430),
   ForestZeroReclaim.setupCode width,
   ForestZeroReclaim.code width (query + 433) (query + 437),
   widen ((resetPrepareCode width).toList),
   widen (ForestZeroReset.code width (query + 452)),
   #[.pop 4], ForestZeroRootLoop.dispatchCode width next].flatMap Array.toList

derive_word_recipe entryCode



open Controller.Cost.WordConstructionRecipe

open Controller.Horn.RowScan in
def rowStream (width entry n base cursorHeader startHeader exit : Nat) : List (Instruction width 8) :=
  (testCode width cursorHeader startHeader exit).toList ++
  (Controller.Horn.SourceScan.pairCode width (entry + 6) cursorHeader (entry + 46)).toList ++
  (readMarksCode width base true).toList ++
  (dispatchCode width (entry + 17) (Controller.Horn.LiteralDispatch.rowLayout n base) true).toList ++
  (writeMarkCode width base true).toList ++
  (#[.branchZero 2 (word width entry)]).toList ++
  (readMarksCode width base false).toList ++
  (dispatchCode width (entry + 47) (Controller.Horn.LiteralDispatch.rowLayout n base) false).toList ++
  (writeMarkCode width base false).toList ++
  (#[.branchZero 2 (word width entry)]).toList

theorem rowStream_eq (width entry n base cursorHeader startHeader exit : Nat) :
    rowStream width entry n base cursorHeader startHeader exit = (Controller.Horn.RowScan.rowCode width entry n base cursorHeader startHeader exit).toList := by
  simp only [rowStream, Controller.Horn.RowScan.rowCode, Array.toList_append]

open Controller.Horn.JoinedRuleCopy in
def copyStream (width n entry base cursorHeader : Nat) : List (Instruction width 8) :=
  (Controller.Horn.RuleDispatch.code width n entry base (entry + 17)).toList ++
  (Controller.Horn.RuleCopy.recordAddressCode width cursorHeader).toList ++
  (Controller.Horn.RuleCopy.headerCode width).toList ++
  (Controller.Horn.RuleDispatch.skipCode width (entry + 37)).toList ++
  (Controller.Horn.RuleCopy.setupCode width (base + 2 * n)).toList ++
  (Controller.Horn.RuleCopy.bodyCode width (entry + 29) (base + 3 * n + 4) (entry + 37)).toList ++
  (Controller.Horn.RuleCopy.finishCode width).toList ++
  (Controller.Horn.RuleCopy.cursorUpdateCode width cursorHeader).toList

theorem copyStream_eq (width n entry base cursorHeader : Nat) :
    copyStream width n entry base cursorHeader = (Controller.Horn.JoinedRuleCopy.code width n entry base cursorHeader).toList := by
  simp only [copyStream, Controller.Horn.JoinedRuleCopy.code, Array.toList_append]

open Controller.Horn.NormalizeCNF in
def normalizeStream (width entry n base recordHeader inputHeader firstHeader directoryHeader endHeader : Nat) : List (Instruction width 8) :=
  (Controller.Horn.ClauseEntry.code width directoryHeader endHeader inputHeader firstHeader (entry + 161)).toList ++
  rowStream width (entry + 16) n base inputHeader firstHeader (entry + 93) ++
  copyStream width n (entry + 93) base recordHeader ++
  (Controller.Horn.ResetPointer.setupCode width (base + 2 * n + 2) base).toList ++
  (Controller.Horn.ResetPointer.code width (entry + 138) (base + 5 * n + 4)).toList ++
  (Controller.Horn.ResetReuse.headerCode width n base).toList ++
  (#[.branchZero 2 (word width entry)]).toList

theorem normalizeStream_eq (width entry n base recordHeader inputHeader firstHeader directoryHeader endHeader : Nat) :
    normalizeStream width entry n base recordHeader inputHeader firstHeader directoryHeader endHeader = (Controller.Horn.NormalizeCNF.code width entry n base recordHeader inputHeader firstHeader directoryHeader endHeader).toList := by
  simp only [normalizeStream, Controller.Horn.NormalizeCNF.code, Array.toList_append, rowStream_eq, copyStream_eq]

open Controller.Horn.WorklistSeed in
def seedStream (n : Nat) (width base entry done conflict : Nat) : List (Instruction width 8) :=
  (#[.constant 3 (word width (Controller.Horn.WorklistFIFO.headSlot (n := n) base)),
    .load 4 3, .xor 3 1 4, .branchZero 3 (word width done),
    .add 3 1 5, .add 3 3 5, .load 7 3, .branchZero 7 (word width (entry + 13)),
    .add 1 1 7, .add 1 1 5, .add 1 1 5, .add 1 1 5,
    .branchZero 2 (word width entry),
    .copy 4 1, .add 4 4 5, .add 4 4 5, .add 4 4 5]).toList ++
  (Controller.Horn.WorklistBucketReady.code (n := n) width base (entry + 17) (entry + 45) conflict (entry + 43)).toList ++
  (#[.copy 1 0, .branchZero 2 (word width entry),
    .copy 1 4, .branchZero 2 (word width entry)]).toList

theorem seedStream_eq (n : Nat) (width base entry done conflict : Nat) :
    seedStream n width base entry done conflict = (Controller.Horn.WorklistSeed.code (n := n) width base entry done conflict).toList := by
  simp only [seedStream, Controller.Horn.WorklistSeed.code, Array.toList_append]

def part00 (width _protectedEnd _base _count _query _next : Nat) : List (Instruction width 8) :=
  (scratchCountCode width).toList
derive_word_recipe part00

def part01 (width _protectedEnd _base _count query _next : Nat) : List (Instruction width 8) :=
  (Controller.Horn.TrackedAllocate.code width (query + 11)).toList
derive_word_recipe part01

def part02 (width _protectedEnd _base _count _query _next : Nat) : List (Instruction width 8) :=
  (scratchHeaderCode width).toList
derive_word_recipe part02

def part03 (width _protectedEnd _base _count _query _next : Nat) : List (Instruction width 8) :=
  (scratchEndpointCode).toList
derive_word_recipe part03

def part04 (width _protectedEnd _base _count _query _next : Nat) : List (Instruction width 8) :=
  (saveProjectionCode).toList
derive_word_recipe part04

def part05 (width protectedEnd base count query _next : Nat) : List (Instruction width 8) :=
  normalizeStream width (query + 42) count base
     protectedEnd (protectedEnd + 1) (protectedEnd + 2) (protectedEnd + 3) (protectedEnd + 4)
derive_word_recipe part05

def part06 (width protectedEnd _base _count _query _next : Nat) : List (Instruction width 8) :=
  (ForestZeroHeaderBridge.saveCode width protectedEnd).toList
derive_word_recipe part06

def part07 (width _protectedEnd base count query _next : Nat) : List (Instruction width 8) :=
  (Controller.Horn.IndexScan.code (n := count) width base (base + 5 * count + 4) (query + 210)).toList
derive_word_recipe part07

def part08 (width _protectedEnd _base _count _query _next : Nat) : List (Instruction width 8) :=
  (ForestZeroHeaderBridge.restoreCode width).toList
derive_word_recipe part08

def part09 (width _protectedEnd _base _count _query _next : Nat) : List (Instruction width 8) :=
  (ForestZeroReclaim.captureCode width).toList
derive_word_recipe part09

def part10 (width protectedEnd base count query _next : Nat) : List (Instruction width 8) :=
  (ForestZeroSeedSetup.code (n := count) width base protectedEnd (base + 5 * count + 4) (query + 261)).toList
derive_word_recipe part10

def part11 (width _protectedEnd base count query _next : Nat) : List (Instruction width 8) :=
  seedStream count width base (query + 261) (query + 308) (query + 382)
derive_word_recipe part11

def part12 (width _protectedEnd base count query _next : Nat) : List (Instruction width 8) :=
  (Controller.Horn.WorklistAccept.headSetupCode (n := count) width base (query + 312)).toList
derive_word_recipe part12

def part13 (width _protectedEnd base count query _next : Nat) : List (Instruction width 8) :=
  (Controller.Horn.WorklistFIFO.fetchCode (n := count) width base (query + 312) (query + 369) (query + 331)).toList
derive_word_recipe part13

def part14 (width _protectedEnd base count query _next : Nat) : List (Instruction width 8) :=
  (Controller.Horn.WorklistFIFO.advanceCode (n := count) width base (query + 312)).toList
derive_word_recipe part14

def part15 (width _protectedEnd _base _count query _next : Nat) : List (Instruction width 8) :=
  (Controller.Horn.WorklistBucketLoop.code width (query + 331) (query + 326) (query + 343)).toList
derive_word_recipe part15

def part16 (width _protectedEnd base count query _next : Nat) : List (Instruction width 8) :=
  (Controller.Horn.WorklistBucketReady.code (n := count) width base (query + 343) (query + 326) (query + 382) (query + 331)).toList
derive_word_recipe part16

def part17 (width _protectedEnd _base _count query _next : Nat) : List (Instruction width 8) :=
  (ForestZeroAnswer.savedCode width 1 (query + 395)).toList
derive_word_recipe part17

def part18 (width _protectedEnd _base _count query _next : Nat) : List (Instruction width 8) :=
  (ForestZeroAnswer.savedCode width 0 (query + 430)).toList
derive_word_recipe part18

def part19 (width _protectedEnd _base _count _query _next : Nat) : List (Instruction width 8) :=
  (projectionConstantsCode width).toList
derive_word_recipe part19

def part20 (width _protectedEnd _base _count _query _next : Nat) : List (Instruction width 8) :=
  (channelPrepareCode width).toList
derive_word_recipe part20

def part21 (width _protectedEnd _base _count query _next : Nat) : List (Instruction width 8) :=
  (ForestZeroChannelEmit.code width (query + 416) (query + 430)).toList
derive_word_recipe part21

def part22 (width _protectedEnd _base _count _query _next : Nat) : List (Instruction width 8) :=
  (ForestZeroReclaim.setupCode width).toList
derive_word_recipe part22

def part23 (width _protectedEnd _base _count query _next : Nat) : List (Instruction width 8) :=
  (ForestZeroReclaim.code width (query + 433) (query + 437)).toList
derive_word_recipe part23

def part24 (width _protectedEnd _base _count _query _next : Nat) : List (Instruction width 8) :=
  (widen ((resetPrepareCode width).toList)).toList
derive_word_recipe part24

def part25 (width _protectedEnd _base _count query _next : Nat) : List (Instruction width 8) :=
  (widen (ForestZeroReset.code width (query + 452))).toList
derive_word_recipe part25

def part26 (width _protectedEnd _base _count _query _next : Nat) : List (Instruction width 8) :=
  (#[.pop 4]).toList
derive_word_recipe part26

def part27 (width _protectedEnd _base _count _query next : Nat) : List (Instruction width 8) :=
  (ForestZeroRootLoop.dispatchCode width next).toList
derive_word_recipe part27

def suffixRecipes (width : Nat) : List (InstructionRecipe 5 width 8) :=
  [part00.constructionRecipe width,
   part01.constructionRecipe width,
   part02.constructionRecipe width,
   part03.constructionRecipe width,
   part04.constructionRecipe width,
   part05.constructionRecipe width,
   part06.constructionRecipe width,
   part07.constructionRecipe width,
   part08.constructionRecipe width,
   part09.constructionRecipe width,
   part10.constructionRecipe width,
   part11.constructionRecipe width,
   part12.constructionRecipe width,
   part13.constructionRecipe width,
   part14.constructionRecipe width,
   part15.constructionRecipe width,
   part16.constructionRecipe width,
   part17.constructionRecipe width,
   part18.constructionRecipe width,
   part19.constructionRecipe width,
   part20.constructionRecipe width,
   part21.constructionRecipe width,
   part22.constructionRecipe width,
   part23.constructionRecipe width,
   part24.constructionRecipe width,
   part25.constructionRecipe width,
   part26.constructionRecipe width,
   part27.constructionRecipe width].flatten

theorem suffix_recipe_image (width protectedEnd base count query next : Nat) :
    evaluate (fun index => [protectedEnd, base, count, query, next].getD index.val 0) (suffixRecipes width) =
      suffix width protectedEnd base count query next := by
  conv_lhs =>
    rw [suffixRecipes, evaluate_flatten]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [part00.constructionRecipe_eq width protectedEnd base count query next,
    part01.constructionRecipe_eq width protectedEnd base count query next,
    part02.constructionRecipe_eq width protectedEnd base count query next,
    part03.constructionRecipe_eq width protectedEnd base count query next,
    part04.constructionRecipe_eq width protectedEnd base count query next,
    part05.constructionRecipe_eq width protectedEnd base count query next,
    part06.constructionRecipe_eq width protectedEnd base count query next,
    part07.constructionRecipe_eq width protectedEnd base count query next,
    part08.constructionRecipe_eq width protectedEnd base count query next,
    part09.constructionRecipe_eq width protectedEnd base count query next,
    part10.constructionRecipe_eq width protectedEnd base count query next,
    part11.constructionRecipe_eq width protectedEnd base count query next,
    part12.constructionRecipe_eq width protectedEnd base count query next,
    part13.constructionRecipe_eq width protectedEnd base count query next,
    part14.constructionRecipe_eq width protectedEnd base count query next,
    part15.constructionRecipe_eq width protectedEnd base count query next,
    part16.constructionRecipe_eq width protectedEnd base count query next,
    part17.constructionRecipe_eq width protectedEnd base count query next,
    part18.constructionRecipe_eq width protectedEnd base count query next,
    part19.constructionRecipe_eq width protectedEnd base count query next,
    part20.constructionRecipe_eq width protectedEnd base count query next,
    part21.constructionRecipe_eq width protectedEnd base count query next,
    part22.constructionRecipe_eq width protectedEnd base count query next,
    part23.constructionRecipe_eq width protectedEnd base count query next,
    part24.constructionRecipe_eq width protectedEnd base count query next,
    part25.constructionRecipe_eq width protectedEnd base count query next,
    part26.constructionRecipe_eq width protectedEnd base count query next,
    part27.constructionRecipe_eq width protectedEnd base count query next]
  simp only [suffix, part00, part01, part02, part03, part04, part05, part06, part07, part08, part09, part10, part11, part12, part13, part14, part15, part16, part17, part18, part19, part20, part21, part22, part23, part24, part25, part26, part27, List.flatMap_cons, List.flatMap_nil, List.append_nil, normalizeStream_eq, seedStream_eq]

/-- The fixed recipes cover the complete entryCode and solver suffix. The exact
variable constructor remains in the middle, with its original branch entry. -/
theorem image_eq (width protectedEnd channels entry next : Nat)
    (refs : List (List (ForestZeroEmit.Reference ambient))) (summary : ForestCompilerQueries.Summary ambient) :
    ForestCachedNegativeProgram.instructions width protectedEnd channels entry next refs summary =
      entryCode width (protectedEnd + 5 + 2 * (refs.length + 1)) ++
      ((ForestZeroAdmissibleCaller.constructorCode width (entry + 15) protectedEnd protectedEnd (protectedEnd + 4)
        (ForestZeroResident.placement width protectedEnd entry next refs).query refs).map
          RegisterWiden.widenInstruction) ++
      suffix width protectedEnd (ForestCachedNegativeProgram.heapEnd protectedEnd channels refs summary)
        summary.coordinates.size (ForestZeroResident.placement width protectedEnd entry next refs).query next := by
  simp only [ForestCachedNegativeProgram.instructions, ForestCachedNegativeProgram.chunks,
    entryCode, suffix, List.flatMap_cons, List.flatMap_nil, List.append_nil, widen,
    List.append_assoc]
  rfl

end Controller.Cost.ForestNegativeRecipes
