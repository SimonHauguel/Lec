import Lec.Lecrat.CoreParser
import Std.Data.HashMap

open RatValue
open CanProduceParsingResult
open CanProduceErrorFromContext
open Lean Std HashMap

-- # TODO : Implement Option and Ref
-- # TODO : Fix Many & Some Parsers
-- # TODO : Fix Comp Parser
-- # TODO : Make Something efficient
-- # TODO : Error handling

mutual

partial def metaNameParser [CanProduceErrorFromContext β] [CanProduceParsingResult α] 
  : String → Parser α β → Parser α β := 
  λ s p =>
      let entry := p.entry
      if  entry.startsWith s
      then {
        p with
          entry      := entry.drop (s.length)
          result     := resultMetaString s
      }
      else { p with error := some $ fromParserContext p }

partial def orSequenceParser [CanProduceErrorFromContext β] [Inhabited α] [CanProduceParsingResult α] 
  : RatValue α → RatValue α → Parser α β → Parser α β :=
  λ fst snd p =>
    let newParser := p.parseUniqueRatValue fst
    if newParser.error.isNone 
    then newParser
    else p.parseUniqueRatValue snd

partial def plusSequenceParser [CanProduceErrorFromContext β] [Inhabited α] [CanProduceParsingResult α] 
  : RatValue α → RatValue α → Parser α β → Parser α β :=
  λ fst snd p =>
    let newParser := p.parseUniqueRatValue fst
    if newParser.error.isNone
    then
      let lastParser := newParser.parseUniqueRatValue snd
      {
        lastParser with
          result := resultMultiParser newParser.result lastParser.result
      }
    else newParser

partial def manyParser [CanProduceErrorFromContext β] [Inhabited α] [CanProduceParsingResult α]
  : RatValue α → Parser α β → Parser α β :=
  λ r p =>
    let newParser := p.parseUniqueRatValue r
    if newParser.error.isNone
    then 
      let lastParser := manyParser r newParser
      {
        lastParser with
          result := resultMultiParser newParser.result lastParser.result
      }
    else p

partial def someParser [CanProduceErrorFromContext β] [Inhabited α] [CanProduceParsingResult α]
  : RatValue α → Parser α β → Parser α β :=
  λ r p =>
    let newParser := p.parseUniqueRatValue r
    if newParser.error.isNone
    then 
      let lastParser := manyParser r newParser
      {
        lastParser with
          result := resultMultiParser newParser.result lastParser.result
      }
    else {
      p with error := some $ fromParserContext p
    }

partial def namedParser [CanProduceErrorFromContext β] [Inhabited α] [CanProduceParsingResult α]
  : Lean.Name → RatValue α → Parser α β → Parser α β :=
  λ n r p => 
    let newParser := p.parseUniqueRatValue r
    if newParser.error.isNone
    then {
      newParser with
        context := newParser.context.insert n (newParser.result)
    }
    else {
      p with error := some $ fromParserContext p
    }

partial def compToParser [CanProduceErrorFromContext β] [Inhabited α] [CanProduceParsingResult α]
  : RatValue α → (HashMap Lean.Name α → α) → Parser α β → Parser α β :=
  λ r f p =>
    let newParser := p.parseUniqueRatValue r
    if newParser.error.isNone
    then {
      newParser with
        result := f newParser.context
    }
    else {
      p with error := some $ fromParserContext p
    }

partial def Parser.parse [CanProduceErrorFromContext β] [Inhabited α] [CanProduceParsingResult α] : HashMap Lean.Name (RatValue α) → Lean.Name → Parser α β → Parser α β :=
  λ r n p => match r.find! n with
  | STRING a   => metaNameParser a p
  | OR ⟨a, b⟩   => orSequenceParser a b p
  | COMP ⟨a, b⟩ => plusSequenceParser a b p
  | MANY a     => manyParser a p
  | SOME a     => someParser a p
  | NAMED a b  => namedParser a b p
  | COMPTO a f => compToParser a f p
  | NIL        => p
  | _          => panic! "Not Yet Implemented"

partial abbrev Parser.parseUniqueRatValue [CanProduceErrorFromContext β] [Inhabited α] [CanProduceParsingResult α] : RatValue α → Parser α β → Parser α β :=
  λ r p => p.parse (HashMap.ofList [⟨`default, r⟩]) `default

partial def Parser.print (p : Parser String Error) : IO Unit :=
  match p.error with
  | some _       => println! p.entry ++ " /!\\ Fail"
  | none         => 
    println! s!"Rest : {p.entry}\nParsed : {p.result}"

end