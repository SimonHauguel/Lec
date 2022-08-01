import Lec.Lecrat.CoreParser
import Lec.Lecrat.ParserFactory
import Std.Data.HashMap

open RatValue
open Lean Std HashMap

@[inline] abbrev getUnique [Inhabited α] (bi : HashMap Lean.Name α) := bi.find! `unique
@[inline] abbrev oneOf (s : String) : RatValue α :=
  match s.data with
  | x::xs => xs.foldl (λ acc n => $s!"{n}" ∣ acc) (STRING s!"{x}")
  | _     => ε
@[inline] abbrev unique : RatValue α → RatValue α := NAMED `unique 
@[inline] abbrev between [Inhabited α] (l : RatValue α) (r : RatValue α) (e : RatValue α) : RatValue α := 
  l ⊹ (unique e) ⊹ r ~> getUnique;
@[inline] abbrev parens [Inhabited α] : RatValue α → RatValue α := between ($"(") ($")")
@[inline] abbrev num : RatValue α :=
  unique $ oneOf "0123456789"
@[inline] abbrev alpha : RatValue α :=
  unique $ oneOf "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
@[inline] abbrev lowerAlpha : RatValue α :=
  unique $ oneOf "abcdefghijklmnopqrstuvwxyz"
@[inline] abbrev upperAlpha : RatValue α :=
  unique $ oneOf "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
@[inline] abbrev sepBy1 [Inhabited α] (sep : RatValue α) (toParse : RatValue α) : RatValue α :=
  toParse ⊹ *(sep ⊹ unique toParse ~> getUnique;)