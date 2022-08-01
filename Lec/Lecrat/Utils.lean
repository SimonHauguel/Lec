import Lec.Lecrat.CoreParser
import Std.Data.HashMap

open Lean Std HashMap
open RatValue

class PrettyShow (α : Type _) where
  pretty : α → String

open PrettyShow

instance : PrettyShow (RatValue α) where
  pretty :=
  let rec val
  | a ∣ b      => s!"{val a} | {val b}"
  | a ⊹ b      => s!"{val a} {val b}"
  | REF n      => s!"{n}"
  | ε          => "ε"
  | COMPTO a _ => s!"{val a}"
  | _ ← a      => s!"{val a}"
  | *a         => s!"({val a})*"
  | +a         => s!"({val a})+"
  | OPTION a   => s!"({val a})?"
  | STRING a   => s!"{a}"
  val

instance : PrettyShow Int where
  pretty := toString

instance [PrettyShow α] : PrettyShow (PartialGrammar α) where
  pretty pg := 
    pg.fold (λ acc key value => s!"{key} → {pretty value}\n{acc}") default

instance : PrettyShow (Grammar α) where
  pretty g := 
  g.fold (
    λ acc key value =>
      let temp := value.foldr (
        λ new acc => s!"{key} → {pretty new}\n{acc}"
      ) default
      s!"{temp}\n{acc}"
  ) default

instance : Membership (Lean.Name) (Grammar α) where
  mem n g := g.contains n

instance : ToString (RatValue α) where
  toString := 
  let rec go
  | a ∣ b      => s!"O{go a}{go b}"
  | a ⊹ b      => s!"P{go a}{go b}"
  | _ ← b      => s!"N{go b}"
  | COMPTO a _ => s!"COMP{go a}"
  | ε          => s!"EPS"
  | +a         => s!"S{go a}"
  | *a         => s!"M{go a}"
  | OPTION a   => s!"OPT{go a}"
  | STRING a   => s!"STR{a}"
  | REF a      => s!"REF{a}"
  go