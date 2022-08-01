import Std.Data.HashMap

open Lean Std HashMap

universe u

-- Lecrat is a DSL that claims to describe a pep-like and generates a packrat parser

-- RatValue is the AST that is generated by the lecrat parser 
inductive RatValue (α : Type u) where
  -- a | b
  | OR         : RatValue α   → RatValue α                 → RatValue α
  -- a b 
  | COMP       : RatValue α   → RatValue α                 → RatValue α 
  -- a where a is not terminal
  | REF        : Lean.Name                                 → RatValue α
  -- a where a is terminal
  | STRING     : String                                    → RatValue α
  -- a*
  | MANY       : RatValue α                                → RatValue α
  -- a+
  | SOME       : RatValue α                                → RatValue α
  -- a?
  | OPTION     : RatValue α                                → RatValue α
  -- bind ← a
  | NAMED      : Lean.Name    → RatValue α                 → RatValue α
  -- a => fun
  | COMPTO     : RatValue α   → (HashMap Lean.Name α → α)  → RatValue α
  -- ε do nothing
  | NIL        : RatValue α
  
  deriving Inhabited

open RatValue


@[inline] abbrev PartialGrammar : Type u → Type u :=
  λ α => HashMap Lean.Name (RatValue α)
@[inline] abbrev Grammar : Type u → Type u       := 
  λ α => HashMap Lean.Name (List (RatValue  α))

partial def isSame : RatValue α → RatValue α → Bool
  | OR     a b , OR     c d => isSame a c && isSame b d
  | COMP   a b , COMP   c d => isSame a c && isSame b d 
  | NAMED  a b , NAMED  c d => a == c && isSame b d
  | OPTION a   , OPTION b   => isSame a b
  | SOME   a   , SOME   b   => isSame a b
  | MANY   a   , MANY   b   => isSame a b
  | COMPTO a _ , COMPTO c _ => isSame a c
  | STRING a   , STRING b   => a == b
  | REF    a   , REF    b   => a == b
  | NIL        , NIL        => true
  | _          , _          => false

instance : BEq (RatValue α) where
  beq := isSame

notation:10 lrv "∣" rrv:10      => OR lrv rrv
notation:54 lrv "⊹" rrv:55      => COMP lrv rrv
notation        "*" rrv:80      => MANY rrv
notation        "+" rrv:80      => SOME rrv
notation        "?" rrv:70      => OPTION rrv
notation        "$" name:90     => STRING name
notation        "↑" name:90     => REF name
notation:45 lrv "←" rrv:45      => NAMED lrv rrv     
notation        "ε"             => NIL
notation:30 lrv "~>" val:30 ";" => COMPTO lrv val

macro n:ident "IsAGrammarThatProducesA" typ:term "Where" terms:many(term) "EndGrammar" :command => 
  `(def $n : PartialGrammar $typ :=
      HashMap.ofList [$terms,*])

macro n:ident "IsAGrammarThatProducesA" typ:term "With" depends:term
      "Where" terms:many(term) "EndGrammar" :command =>
    `(def $n : PartialGrammar $typ :=
      HashMap.ofList (
        List.foldr ((.++.) ∘ HashMap.toList) [$terms,*] $depends
      ))

macro X:term "::=" V:term ";;" :term => `(⟨$X, $V⟩)


-- To be a valid AST, you need to satisfy 3 things :
-- 1 . You need to give a way to capture *meta terminal symbol*
-- 2 . You need to give a way to concatenate the result of a many/some
-- 3 . You need to give a way to parse *nothing*
-- Note : (α, resultMultiParser, resultMetaNil) is a Monoid
class CanProduceParsingResult (α : Type u) where
  resultMetaString  : String → α
  resultMultiParser : α → α → α 
  resultMetaNil     : α