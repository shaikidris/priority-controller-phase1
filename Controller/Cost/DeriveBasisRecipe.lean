/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
import Controller.Cost.WordConstructionRecipe
import Lean.Elab.Command
import Lean.Util.Sorry

/-! Checked derivation of recipes for fixed numeric instruction templates.
The generator rejects instance-dependent plain instructions and unsupported
arithmetic. Every generated identity is submitted to Lean's kernel; derivation
does not add an axiom or admit an unsupported case. -/
namespace Controller.Cost.DeriveBasisRecipe

open Lean Meta Elab Command
open Controller.Cost.WordConstructionRecipe

private def dependsOn (expression : Expr) (inputs : Array Expr) : Bool :=
  inputs.any fun input =>
    let source := match input with
      | .proj _ _ source => source
      | _ => if input.isFVar then input else input.getAppArgs.back!
    expression.containsFVar source.fvarId!

private def finLiteral (index size : Nat) : MetaM Expr := do
  let value := mkNatLit index
  let bound := mkNatLit size
  mkAppM ``Fin.mk #[value, ← mkDecideProof (← mkLt value bound)]

private partial def natural (inputs : Array Expr) (expression : Expr) : MetaM Expr := do
  let count := mkNatLit inputs.size
  if let some index := inputs.findIdx? (· == expression) then
    return ← mkAppM ``Expression.parameter #[← finLiteral index inputs.size]
  if expression.isAppOf ``Fin.val || (match expression with | .proj ``Fin 0 _ => true | _ => false)
    then
    for index in [:inputs.size] do
      if ← isDefEq inputs[index]! expression then
        return ← mkAppM ``Expression.parameter #[← finLiteral index inputs.size]
  if !dependsOn expression inputs then
    return mkApp2 (mkConst ``Expression.literal) count expression
  let function := expression.getAppFn.constName?
  let arguments := expression.getAppArgs
  if (function == some ``HAdd.hAdd || function == some ``HSub.hSub || function == some ``HMul.hMul)
    && arguments.size >= 2 then
    let left ← natural inputs arguments[arguments.size - 2]!
    let right ← natural inputs arguments.back!
    let operation := if function == some ``HAdd.hAdd then ``Expression.add
      else if function == some ``HSub.hSub then ``Expression.sub else ``Expression.mul
    return mkApp3 (mkConst operation) count left right
  if (function == some ``Nat.add || function == some ``Nat.sub || function == some ``Nat.mul) &&
    arguments.size == 2 then
    let left ← natural inputs arguments[0]!
    let right ← natural inputs arguments[1]!
    let operation := if function == some ``Nat.add then ``Expression.add
      else if function == some ``Nat.sub then ``Expression.sub else ``Expression.mul
    return mkApp3 (mkConst operation) count left right
  if function == some ``Nat.succ && arguments.size == 1 then
    let value ← natural inputs arguments[0]!
    let one := mkApp2 (mkConst ``Expression.literal) count (mkNatLit 1)
    return mkApp3 (mkConst ``Expression.add) count value one
  if function == some ``Nat.div || function == some ``Nat.mod || function == some ``Nat.pow then
    throwError "unsupported numeric template expression: {expression}"
  let simplified ← whnf expression
  if simplified != expression then natural inputs simplified
  else throwError "unsupported numeric template expression: {expression}"

private partial def immediate (inputs : Array Expr) (expression : Expr) : MetaM Expr := do
  if expression.isAppOfArity ``Controller.Cost.word 2 then
    return ← natural inputs expression.getAppArgs[1]!
  let simplified ← whnf expression
  if simplified.isAppOf ``Fin.mk then
    let packed := simplified.getAppArgs[1]!
    let head := packed.getAppFn.constName?
    if head == some ``Nat.mod || head == some ``HMod.hMod then
      let arguments := packed.getAppArgs
      return ← natural inputs arguments[arguments.size - 2]!
  if simplified != expression then immediate inputs simplified
  else throwError "template immediate is not an explicit packed word: {expression}"

private partial def instruction (inputs : Array Expr) (width registers : Expr) (expression : Expr) :
  MetaM Expr := do
  let expanded ← whnf expression
  let name := expanded.getAppFn.constName?
  let arguments := expanded.getAppArgs
  if name == some ``Instruction.constant then
    let destination := arguments[arguments.size - 2]!
    if dependsOn destination inputs then throwError "instance-dependent register identifier"
    return mkAppN (mkConst ``InstructionRecipe.constant) #[mkNatLit inputs.size, width, registers,
      destination, ← immediate inputs arguments.back!]
  if name == some ``Instruction.branchZero then
    let source := arguments[arguments.size - 2]!
    if dependsOn source inputs then throwError "instance-dependent register identifier"
    return mkAppN (mkConst ``InstructionRecipe.branchZero) #[mkNatLit inputs.size, width, registers,
      source, ← immediate inputs arguments.back!]
  if dependsOn expanded inputs then
    throwError "instance-dependent plain instruction: {expanded}"
  return mkApp4 (mkConst ``InstructionRecipe.plain) (mkNatLit inputs.size) width registers expanded

private partial def instructions (inputs : Array Expr) (width registers : Expr) (expression : Expr)
  : MetaM (List Expr) := do
  let expanded ← whnf expression
  if expanded.isAppOf ``List.nil then return []
  if expanded.isAppOf ``List.cons then
    let arguments := expanded.getAppArgs
    let first ← instruction inputs width registers arguments[1]!
    let rest ← instructions inputs width registers arguments[2]!
    return first :: rest
  throwError "template is not a fixed instruction list: {expanded}"

private partial def expressionWork (expression : Expr) : MetaM Nat := do
  let name := expression.getAppFn.constName?
  if name == some ``Expression.literal || name == some ``Expression.parameter then return 1
  if name == some ``Expression.add || name == some ``Expression.sub || name == some ``Expression.mul
    then
    let arguments := expression.getAppArgs
    return (← expressionWork arguments[arguments.size - 2]!) +
      (← expressionWork arguments.back!) + 1
  throwError "unrecognized generated expression recipe"

private def instructionWork (expression : Expr) : MetaM Nat := do
  if expression.isAppOf ``InstructionRecipe.plain then return 8
  if expression.isAppOf ``InstructionRecipe.constant || expression.isAppOf
    ``InstructionRecipe.branchZero then
    return (← expressionWork expression.getAppArgs.back!) + 9
  throwError "unrecognized generated instruction recipe"

/-- Derive a width-indexed fixed recipe and a kernel-checked image identity.
All natural parameters other than `width` become explicit environment slots. -/
elab "derive_basis_recipe " source:ident : command => do
  liftTermElabM do
    let name ← realizeGlobalConstNoOverloadWithInfo source
    let information ← getConstInfo name
    if information.isUnsafe then throwError "unsafe template is unsupported"
    unless information.levelParams.isEmpty do throwError "polymorphic template is unsupported"
    forallTelescopeReducing information.type fun arguments resultType => do
      let mut widthOption : Option Expr := none
      let mut inputs : Array Expr := #[]
      for argument in arguments do
        let declaration ← argument.fvarId!.getDecl
        if ← isDefEq declaration.type (mkConst ``Nat) then
          if declaration.userName == `width then widthOption := some argument
          else inputs := inputs.push argument
        else if (← whnf declaration.type).isAppOf ``Fin then
          inputs := inputs.push (← mkAppM ``Fin.val #[argument])
        else
          throwError "template argument must be a natural or finite index: {declaration.userName}"
      let some width := widthOption | throwError "missing width parameter"
      let call := mkAppN (mkConst name) arguments
      let resultType ← whnf resultType
      let (list, itemType) ← if resultType.isAppOf ``List then
          pure (call, resultType.getAppArgs[0]!)
        else if resultType.isAppOf ``Array then
          pure (← mkAppM ``Array.toList #[call], resultType.getAppArgs[0]!)
        else throwError "template must produce a list or array"
      unless itemType.isAppOf ``Instruction do throwError "not an instruction template: {itemType}"
      let registers := itemType.getAppArgs[1]!
      let items ← instructions inputs width registers list
      let recipeType := mkApp3 (mkConst ``InstructionRecipe) (mkNatLit inputs.size) width registers
      let recipe ← mkListLit recipeType items
      if dependsOn recipe inputs then throwError "recipe retained an instance-dependent constant"
      let recipeName := name.str "constructionRecipe"
      let definitionType ← mkForallFVars #[width] (← inferType recipe)
      let definitionValue ← mkLambdaFVars #[width] recipe
      addAndCompile (.defnDecl {
        name := recipeName
        levelParams := []
        type := definitionType
        value := definitionValue
        hints := .regular 0
        safety := .safe })
      enableRealizationsForConst recipeName
      let inputList ← mkListLit (mkConst ``Nat) inputs.toList
      let environment ← withLocalDeclD `index (mkApp (mkConst ``Fin) (mkNatLit inputs.size)) fun
        index => do
        let value ← mkAppM ``List.getD #[inputList, ← mkAppM ``Fin.val #[index], mkNatLit 0]
        mkLambdaFVars #[index] value
      let result ← mkAppM ``evaluate #[environment, mkApp (mkConst recipeName) width]
      let identity ← mkEq result list
      unless (← isDefEq result list) do
        throwError "generated recipe does not match the original template"
      addDecl (.thmDecl {
        name := name.str "constructionRecipe_eq"
        levelParams := []
        type := ← mkForallFVars arguments identity
        value := ← mkLambdaFVars arguments (← mkEqRefl result) })
      let cost ← mkAppM ``work #[mkApp (mkConst recipeName) width]
      let mut costValue := 0
      for item in items do costValue := costValue + (← instructionWork item)
      let count := mkNatLit costValue
      let proofSyntax ← `(by
        simp only [$(mkIdent recipeName):term, WordConstructionRecipe.work,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          InstructionRecipe.work, Expression.work] <;> decide )
      let equation ← mkEq cost count
      let value ← Term.elabTerm proofSyntax (some equation)
      Term.synthesizeSyntheticMVarsNoPostponing
      let value ← instantiateMVars value
      let cost ← instantiateMVars cost
      if value.hasSorry then throwError "recipe cost proof contains an admission"
      if value.hasMVar || cost.hasMVar then throwError "unresolved recipe cost proof: {value}"
      addDecl (.thmDecl {
        name := name.str "constructionRecipe_work"
        levelParams := []
        type := ← mkForallFVars #[width] (← mkEq cost count)
        value := ← mkLambdaFVars #[width] value })
      logInfo m!"{recipeName}: {items.length} instructions; {inputs.size} slots; work={costValue}"

end Controller.Cost.DeriveBasisRecipe
