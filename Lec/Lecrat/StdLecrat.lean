import Lec.Lecrat.CoreParser
import Lec.Lecrat.ParserFactory

open RatValue

@[inline] abbrev unique : RatValue α → RatValue α := NAMED `unique 
@[inline] abbrev between (l : RatValue α) (r : RatValue α) (e : RatValue α) : RatValue α := 
  l ⊹ unique e ⊹ r
@[inline] abbrev parens : RatValue α → RatValue α := between ($"(") ($")")
@[inline] abbrev num : RatValue α :=
  $"0" ∣ $"1" ∣
  $"2" ∣ $"3" ∣
  $"4" ∣ $"5" ∣
  $"6" ∣ $"7" ∣
  $"8" ∣ $"9"