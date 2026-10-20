module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ForestDirectoryConstruction

@[expose] public section


/-! Complete variable constructor image for one source-addressed query. The
profile, directory and literal streams are computed from the supplied rows.
Fixed header/caller instructions use the checked scalar recipes. -/
namespace Controller.Cost.ForestClauseProgramConstruction

open Controller.Cost Controller.Cost.WordConstructionRecipe
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroAssembly
open Controller.Cost.ForestZeroQueryCaller Controller.Cost.ForestZeroAdmissibleCaller
open Controller.Cost.CompilerAppendTrace

variable {ambient : Nat}

def environment (values : List Nat) (index : Fin values.length) : Nat := values.getD index.val 0

def join (blocks : List (List α)) : List α := blocks.flatten

def joinWork (blocks : List (List α)) : Nat := blocks.flatten.length + blocks.length

inductive JoinTrace : List (List α) → List α → Nat → Prop
  | nil : JoinTrace [] [] 0
  | cons (block rest tail later)
      (remaining : JoinTrace rest tail later)
      (copied : AppendTrace block tail (block ++ tail) block.length) :
      JoinTrace (block :: rest) (block ++ tail) (block.length + later + 1)

theorem join_trace (blocks : List (List α)) : JoinTrace blocks (join blocks) (joinWork blocks) := by
  induction blocks with
  | nil => exact .nil
  | cons block rest ih =>
      have result := JoinTrace.cons block rest _ _ ih (append_exists _ _)
      simpa [join, joinWork, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result

def query (width base protectedEnd : Nat) (refs : List (List (Reference ambient))) :
    GateProgram.Code width × Nat :=
  let counts := ForestDirectoryConstruction.profile refs
  let headerRecipes := preservingHeaderCode.constructionRecipe width
  let header := evaluate (environment [protectedEnd, counts.1, counts.2.1]) headerRecipes
  let directory := ForestDirectoryConstruction.directory width refs
  let literals := ForestQueryConstruction.emit width (base + 14 + directory.1.length) refs.flatten
  let finalRecipes := countCode.constructionRecipe width
  let final := evaluate (environment [protectedEnd + 1]) finalRecipes
  let blocks := [header, [.push 2], directory.1, [.pop 2], literals.1, final]
  (join blocks, counts.2.2 + work headerRecipes + directory.2 + literals.2 + work finalRecipes +
    joinWork blocks + refs.flatten.length + refs.length + directory.1.length + 30)

theorem directory_coordinates (width : Nat) (refs : List (List (Reference ambient))) :
    refs.flatMap (fun row => ForestDirectoryConstruction.rowCode width row.length) =
      ForestZeroDirectory.code width (originalRows refs) := by
  induction refs with
  | nil => rfl
  | cons row rest ih =>
      calc
        _ = ForestDirectoryConstruction.rowCode width row.length ++
            ForestZeroDirectory.code width (originalRows rest) :=
          congrArg (List.append (ForestDirectoryConstruction.rowCode width row.length)) ih
        _ = _ := by
          simp only [ForestDirectoryConstruction.rowCode, ForestZeroDirectory.code, originalRows,
            List.map_cons, ForestZeroQuery.countClause_exact, List.length_map]

theorem header_image (width protectedEnd rows literals : Nat) :
    evaluate (environment [protectedEnd, rows, literals]) (preservingHeaderCode.constructionRecipe width) =
      preservingHeaderCode width protectedEnd rows literals := by
  change evaluate (fun index => [protectedEnd, rows, literals].getD index.val 0) _ = _
  exact preservingHeaderCode.constructionRecipe_eq width protectedEnd rows literals

theorem final_image (width header : Nat) :
    evaluate (environment [header]) (countCode.constructionRecipe width) = countCode width header := by
  change evaluate (fun index => [header].getD index.val 0) _ = _
  exact countCode.constructionRecipe_eq width header

theorem query_image (width base protectedEnd : Nat) (refs : List (List (Reference ambient))) :
    (query width base protectedEnd refs).1 = queryCode width base protectedEnd refs := by
  have counts := ForestDirectoryConstruction.profile_exact refs
  simp only [query, header_image, final_image, counts.1, counts.2.1,
    ForestDirectoryConstruction.directory_image, ForestQueryConstruction.emit_image,
    directory_coordinates width refs, join, List.flatten_cons, List.flatten_nil, List.append_nil,
    queryCode, assemblyCode, List.append_assoc]

theorem query_work (width base protectedEnd : Nat) (refs : List (List (Reference ambient))) :
    (query width base protectedEnd refs).2 ≤ 300 + 70 * refs.length + 350 * refs.flatten.length := by
  have profile := (ForestDirectoryConstruction.profile_exact refs).2.2
  have directory := ForestDirectoryConstruction.directory_work width refs
  have literals := ForestQueryConstruction.emit_work width
    (base + 14 + (ForestDirectoryConstruction.directory width refs).1.length) refs.flatten
  have header : (evaluate (environment [protectedEnd, (ForestDirectoryConstruction.profile refs).1,
      (ForestDirectoryConstruction.profile refs).2.1]) (preservingHeaderCode.constructionRecipe width)).length = 12 := by
    rw [header_image, preservingHeaderCode_length]
  have final : (evaluate (environment [protectedEnd + 1]) (countCode.constructionRecipe width)).length = 2 := by
    rw [final_image, countCode_length]
  have rows : (ForestDirectoryConstruction.directory width refs).1.length = 5 * refs.length := by
    rw [ForestDirectoryConstruction.directory_image, directory_coordinates,
      ForestZeroDirectory.code_length]
    simp [originalRows]
  have emitted := ForestZeroEmit.emitCode_length width
    (base + 14 + (ForestDirectoryConstruction.directory width refs).1.length) refs.flatten
  rw [← ForestQueryConstruction.emit_image] at emitted
  simp only [query, preservingHeaderCode.constructionRecipe_work, countCode.constructionRecipe_work,
    joinWork, List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append,
    List.length_cons, List.length_nil, header, final]
  omega

end Controller.Cost.ForestClauseProgramConstruction
