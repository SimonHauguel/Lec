import Lec.Lecrat.CoreParser
import Lec.Lecrat.ParserFactory
import Lec.Lecrat.StdLecrat


inductive Lambda where
  | Var : Int → Lambda
  | Abs : Lambda → Lambda
  | App : Lambda → Lambda → Lambda

  | Nil        : Lambda
  | MetaString : String → Lambda
  | Cons       : Lambda → Lambda → Lambda
  deriving Inhabited

protected partial def Lambda.toString : Lambda → String
| Var n => s!"Var {n}"
| Abs l => "λ." ++ Lambda.toString l
| App a b => "(" ++ Lambda.toString a ++ ")(" ++ Lambda.toString b  ++ ")"
| Nil => "ERRORNIL"
| MetaString a => "ERRORMETASTRING"
| Cons a b => "ERRORCONS"

instance : ToString Lambda where
  toString := Lambda.toString

open Lambda

instance : CanProduceParsingResult Lambda where
  resultMetaNil     := Nil
  resultMetaString  := MetaString
  resultMultiParser a b := 
    match [a, b] with
    | [MetaString x, MetaString y] => MetaString $ x ++ y
    | _ => Cons a b


@[inline] def joinWith (l : List String) (inside : String) : String :=
  l.foldl (fun r s => r ++ (if r.length > 0 then inside else default) ++ s) default 

partial def Parser.print [ToString α] (p : Parser α Error) : IO Unit :=
  match p.error with
  | some _       => println! p.entry ++ " /!\\ Fail"
  | none         =>
    println! s!"NewInput : {p.entry}\nParsed : {p.result}"


Lam IsAGrammarThatProducesA Lambda Where

  `Expr ::= ↑`Var ∣ parens (↑`Expr);;

  `Var ::= unique num {> λ bi => 
    match (bi.find! `unique) with
    | MetaString a => Var $ stringToNat a
    | _ => panic "noway" 
  <};;

  `SubApp ::= parens (↑`Expr);;
  `App ::= (`fst ← ↑`SubApp) ⊹ (`snd ← ↑`SubApp) {>
    λ bi => App (bi.find! `fst) (bi.find! `snd)
  <};;

  `Abs ::= $"λ." ⊹ (`val ← parens (↑`Expr)) {> λ bi => Abs (bi.find! `val)<};;

EndGrammar

#eval (("(3)".mkParserFromString Lambda Error).parse Lam `Expr).print
