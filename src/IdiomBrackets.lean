import Lean 
import init.Data.Array
open Lean Lean.Meta Lean.Core Lean.Elab Lean.Elab.Term 
open Lean.Elab.Command

syntax (name := applicative) "{| " term* " |}" : term

private def saveContext : TermElabM SavedContext :=
  return {
    macroStack := (← read).macroStack
    declName?  := (← read).declName?
    options    := (← getOptions)
    openDecls  := (← getOpenDecls)
    errToSorry := (← read).errToSorry
  }

private def postponeElabTerm (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
  trace[Elab.postpone] "{stx} : {expectedType?}"
  let mvar ← mkFreshExprMVar expectedType? MetavarKind.syntheticOpaque
  let ctx ← read
  registerSyntheticMVar stx mvar.mvarId! (SyntheticMVarKind.postponed (← saveContext))
  pure mvar

private def exceptionToSorry (ex : Exception) (expectedType? : Option Expr) : TermElabM Expr := do
  let expectedType ← match expectedType? with
    | none              => mkFreshTypeMVar
    | some expectedType => pure expectedType
  let syntheticSorry ← mkSyntheticSorry expectedType
  logException ex
  pure syntheticSorry

private def elabUsingElabFnsAux (s : SavedState) (stx : Syntax) (expectedType? : Option Expr) (catchExPostpone : Bool)
    : List TermElab → TermElabM Expr
  | []                => do throwError "unexpected syntax{indentD stx}"
  | (elabFn::elabFns) => do
    try
      let expr ← elabFn stx expectedType?
      return expr
    catch ex => match ex with
      | Exception.error _ _ =>
        if (← read).errToSorry then
          exceptionToSorry ex expectedType?
        else
          throw ex
      | Exception.internal id _ =>
        if (← read).errToSorry && id == abortTermExceptionId then
          exceptionToSorry ex expectedType?
        else if id == unsupportedSyntaxExceptionId then
          s.restore
          elabUsingElabFnsAux s stx expectedType? catchExPostpone elabFns
        else if catchExPostpone && id == postponeExceptionId then
            s.restore
            postponeElabTerm stx expectedType?
          else
            throw ex

private def elabUsingElabFns (stx : Syntax) (expectedType? : Option Expr) (catchExPostpone : Bool) : TermElabM Expr := do
  let s ← saveAllState
  let table := termElabAttribute.ext.getState (← getEnv) |>.table
  let k := stx.getKind
  match table.find? k with
  | some elabFns => do
      elabUsingElabFnsAux s stx expectedType? catchExPostpone elabFns
  | none         => throwError "elaboration function for '{k}' has not been implemented{indentD stx}"

def isApplicative? (m : Expr) : MetaM (Option Expr) :=
  try
    let applicativeType ← mkAppM `Applicative #[m]
    let result    ← trySynthInstance applicativeType
    match result with
    | LOption.some inst => pure inst
    | _                 => pure none
  catch _ =>
    pure none

def isApplicativeApp (type : Expr) : TermElabM Bool := do
  let some (m, _) ← isTypeApp? type | pure false
  return (← isApplicative? m) |>.isSome

def isApplicativeType (type : Expr) : TermElabM (Option (Expr × Expr)) := do
  match ← isTypeApp? type with
  | some (m, α) => 
    match ← isApplicative? m with
    | some inst => return some (m, α)
    | none => return none
  | none => return none

def elabApplicativeExpr (e : Expr) : TermElabM (Expr × Expr) := do
  match ← isApplicativeType e with
  | some (m, α) => return (m, α)
  | none => throwError "{e} is not an applicative functor."

def ensureHasTypeApplicative (expectedApplicative : Expr) (e : Expr) : TermElabM (Expr × Expr) := do
  let (meType, αeType) ← elabApplicativeExpr (← inferType e)
  let _ ← ensureHasTypeAux (some expectedApplicative) meType e
  return (meType, αeType)

def mkFType (t : Expr) (b : Expr) : Expr :=
  mkForall Name.anonymous BinderInfo.default t b

def insertApplicative (f : Syntax) (args : Array Syntax) : TermElabM Syntax := do
  let mut g ← `(pure $f)
  for arg in args do
    g ← `(Seq.seq $g $arg) 
  return g

partial def testAppAux (expectedType? : Option Expr) (catchExPostpone : Bool) (implicitLambda : Bool): Syntax → TermElabM Expr
  | `({| $stx |}) => withFreshMacroScope $ withIncRecDepth do
    trace[Elab.step] "expected type: {expectedType?}, term\n\{|{stx}|}"
    checkMaxHeartbeats "elaborator"
    -- expand macro
    withNestedTraces do
      let env ← getEnv
      let stxNew? ← catchInternalId unsupportedSyntaxExceptionId
        (do let newStx ← adaptMacro (getMacros env) stx; pure (some newStx))
        (fun _ => pure none)
      match stxNew? with
      | some stxNew => 
        withMacroExpansion stx stxNew $ testAppAux expectedType? catchExPostpone implicitLambda (← `({| $stxNew |}))
      -- No macro
      | none => 
        match stx with
        | `($f $args*) => do
          match expectedType? with
          | some expectedType => do
            let (expectedApplicative, expectedArg) ← elabApplicativeExpr expectedType
            let argArgs ← Array.mapM (λ arg => do 
                let arg ← elabUsingElabFns arg none catchExPostpone
                let (_, argArg) ← ensureHasTypeApplicative expectedApplicative arg
                return argArg
              ) args
            let fTypeExpectedType := Array.foldr mkFType expectedArg argArgs
            let _ ← ensureHasType (some fTypeExpectedType) (← elabUsingElabFns f none catchExPostpone)
            elabTerm (← insertApplicative f args) expectedType?
          | none => throwError "missing expectedType"
        | _ => throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax

@[termElab applicative] def testApp : TermElab := λ stx expectedType? =>
  withInfoContext' (withRef stx <| testAppAux expectedType? true true stx) (mkTermInfo stx)

def add (a b : Int) : Int := a + b
def hello : IO String := return "Hello"
def world : IO String := return "World"
def testMain₁ : IO String := {| hello ++ world |}

#check testMain₁

