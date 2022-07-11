import Lec.Lecrat.CoreParser
import Std.Data.HashMap

open RatValue
open CanProduceParsingResult
open CanProduceErrorFromContext
open Lean Std HashMap

-- # TODO : Make Something efficient
-- # TODO : Error handling

def String.startsWithAnyOfChar (s : String) (l : List Char) : Bool :=
  l.foldl (λ acc ns => acc || s.startsWith s!"{ns}") false

mutual

partial def metaNameParser [CanProduceErrorFromContext β] [CanProduceParsingResult α] 
  : String → Parser α β → Parser α β := 
  λ s p =>
      let entry := p.entry
      if  entry.startsWith s
      then {
        p with
          entry  := entry.drop (s.length)
          result := resultMetaString s
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
    else {
      p with error := some $ fromParserContext p
    }

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
    else { p with result := resultMetaNil }

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
      else { p with error := some $ fromParserContext p }

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

partial def optionParser [CanProduceErrorFromContext β] [Inhabited α] [CanProduceParsingResult α]
  : RatValue α → Parser α β → Parser α β :=
  λ r p =>
    let newParser := p.parseUniqueRatValue r
    if newParser.error.isNone
      then newParser
      else p

partial def refParser [CanProduceErrorFromContext β] [Inhabited α] [CanProduceParsingResult α]
  : Lean.Name →  Parser α β → Parser α β := 
  λ n p =>
  if p.extensions.contains n
    then p.parseUniqueRatValue (p.extensions.find! n) 
    else panic s!"Could not find {n} in this context"


partial def Parser.skip [CanProduceErrorFromContext β] [Inhabited α] [CanProduceParsingResult α] 
  : Parser α β → Parser α β :=
  λ p => 
        if p.entry.startsWith (p.oneLineComment) 
        then 
          { p with entry := p.entry.dropWhile (.!='\n')}.skip
        else
        if p.entry.startsWithAnyOfChar (p.toSkip)
        then
          { p with entry := p.entry.dropWhile p.toSkip.contains}.skip
        else
        if p.entry.startsWith (p.multiLineComment.fst)
        then
          Id.run do
            let mut newEntry := p.entry.drop (p.multiLineComment.fst.length)
            while not $ newEntry.startsWith (p.multiLineComment.snd) do
              newEntry := newEntry.drop 1
            { p with entry := newEntry.drop (p.multiLineComment.snd.length)}.skip
        else p
        
partial def Parser.parse [CanProduceErrorFromContext β] [Inhabited α] [CanProduceParsingResult α] 
  : HashMap Lean.Name (RatValue α) → Lean.Name → Parser α β → Parser α β :=
  λ r n p =>
  if p.error.isNone then
    let contextFullParser := {p.skip with extensions := r}
    if r.contains n then
      match r.find! n with
      | STRING a   => metaNameParser a contextFullParser
      | OR ⟨a, b⟩   => orSequenceParser a b contextFullParser
      | COMP ⟨a, b⟩ => plusSequenceParser a b contextFullParser
      | MANY a     => manyParser a contextFullParser
      | SOME a     => someParser a contextFullParser
      | NAMED a b  => namedParser a b contextFullParser
      | COMPTO a f => compToParser a f contextFullParser
      | OPTION a   => optionParser a contextFullParser
      | NIL        => contextFullParser
      | REF a      => refParser a contextFullParser
    else panic s!"Unknow binders {n} !"
  else panic s!"Error Not Empty, can't parse"

partial abbrev Parser.parseUniqueRatValue [CanProduceErrorFromContext β] [Inhabited α] [CanProduceParsingResult α] 
  : RatValue α → Parser α β → Parser α β :=
  λ r p => p.parse (p.extensions.insert `default r) `default

end
