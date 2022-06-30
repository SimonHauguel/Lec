import Lec.Lecrat.CoreParser
import Lec.Lecrat.ParserFactory
import Lec.Lecrat.StdLecrat

partial def Parser.print [ToString α] (p : Parser α Error) : IO Unit :=
  match p.error with
  | some _       => println! p.entry ++ " /!\\ Fail"
  | none         =>
    println! s!"NewInput : {p.entry}\nParsed : {p.result}"



Expr IsAGrammarThatProducesA Int Where

  `Add ::= (`first ← num) ⊹ $" + " ⊹ (`second ← num) {> 
    λ binders => binders.find! `first + binders.find! `second
  <};;

EndGrammar

Foo IsAGrammarThatProducesA Int With [Expr] Where

  `Times ::= (`first ← parens (↑`Add)) ⊹ $" * " ⊹ (`second ← num) {> 
    λ binders => binders.find! `first * binders.find! `second
  <};;

EndGrammar


#eval (("(1 + 2) * 8".mkParserFromString Int Error).parse Foo `Times).print