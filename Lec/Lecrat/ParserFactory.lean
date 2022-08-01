import Lec.Lecrat.CoreParser
import Lec.Lecrat.Utils
import Std.Data.HashMap

open Lean Std HashMap
open RatValue

def Grammar.isWellFormed {α : Type _} (gram : Grammar α) : Bool :=
  let rec isPure : RatValue α → Bool
    | a ⊹ b      => isPure a && isPure b
    | *a         => isPure a
    | +a         => isPure a
    | COMPTO a _ => isPure a
    | _ ← a      => isPure a
    | OPTION a   => isPure a
    | _ ∣ _      => False
    | _          => True
  gram.fold (λ acc _ value => value.all isPure && acc) True

def PartialGrammar.toExplicitGrammar {α : Type _} (toDesugar : PartialGrammar α) : Grammar α :=
  
  toDesugar.fold go empty where

  go (acc : Grammar α) (key : Lean.Name) (value : RatValue α) :=
    let isFound? := acc.find? key
    match isFound? with
    | none   => acc.insert key (explicit value)
    | some r => acc.insert key (r.append $ explicit value)

  explicit : RatValue α → List (RatValue α)
    | OR a b => (explicit a).append $ explicit b
    | other  => [other]