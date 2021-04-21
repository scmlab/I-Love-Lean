import Lean 
import init.Data.Array
open Lean Lean.Meta Lean.Core Lean.Elab Lean.Elab.Term 
open Lean.Elab.Command

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

def ensureHasTypeApplicative (expectedApplicative : Expr) (e : Syntax) : TermElabM (Expr × Expr) := do
  let e ← elabTerm e none 
  let eType ← inferType e
  let eType ← ensureHasTypeAux (some (mkApp expectedApplicative (← mkFreshTypeMVar))) eType eType
  elabApplicativeExpr eType

def insertApplicative (f : Syntax) (args : Array Syntax) : TermElabM Syntax := do
  let mut g ← `(pure $f)
  for arg in args do
    g ← `(Seq.seq $g $arg) 
  return g

syntax (name := applicative) "{| " term* " |}" : term

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
      -- If no macro
      | none => 
        match stx with
        | `($f $args*) => do
          match expectedType? with
          | some expectedType => do
            let (expectedApplicative, expectedArg) ← elabApplicativeExpr expectedType
            let argArgs ← Array.mapM (λ arg => 
                  Prod.snd <$> ensureHasTypeApplicative expectedApplicative arg
              ) args
            let fExpectedType ← Array.foldrM (λ e1 e2 => liftMetaM $ mkArrow e1 e2) expectedArg argArgs
            let _ ← ensureHasType (some fExpectedType) (← elabTerm f none)
            elabTermEnsuringType (← insertApplicative f args) expectedType?
          | none => throwError "missing expectedType"
        | `($f) => do
          match expectedType? with
          | some expectedType => do
            let (expectedApplicative, expectedF) ← elabApplicativeExpr expectedType
            let fApp ← elabTerm (← insertApplicative f Array.empty) none
            let f ← elabTerm f none 
            let fType ← inferType f
            let _ ← ensureHasTypeAux expectedF fType f
            ensureHasType (some (mkApp expectedApplicative fType)) fApp
          | none => throwError "missing expectedType"
        | _ => throwUnsupportedSyntax
       
  | _ => throwUnsupportedSyntax

@[termElab applicative] partial def testApp : TermElab := λ stx expectedType? =>
  withInfoContext' (withRef stx <| testAppAux expectedType? true true stx) (mkTermInfo stx)

def add (a b : Int) : Int := a + b
def hello : IO String := return "Hello"
def world : IO String := return "World"
def testMain₁ : IO Int := {| (add 1 2)  |}

#check testMain₁
#eval testMain₁
#check Prod.snd
