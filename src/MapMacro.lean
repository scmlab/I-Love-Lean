import Lean 

open Lean Lean.Meta Lean.Elab Lean.Elab.Term 
open Lean.Elab.Command hiding withMacroExpansion

syntax "{| " term* " |}" : term
partial def go₁ (f : Syntax) (args : Array Syntax) : MacroM Syntax := do
  match args.data with
  | [] => `($f)
  | (a :: as) => go₁ (←`($f <*> $a)) {data := as}

def go₂ (f : Syntax) (args : Array Syntax) : MacroM Syntax := do
  let mut g := f
  for a in args do
    g ← `($g <*> $a) 
  return g

macro_rules
| `({| $f $args* |}) => go₂ f args

def stringID : String → String → String := λ s1 s2 => s1 ++ s2

def testString : IO String := return "Hello World!"

def testMain : IO String := 
  {| stringID testString testString |}

#eval testMain