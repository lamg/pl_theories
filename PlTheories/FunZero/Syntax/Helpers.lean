import PlTheories.FunZero.Syntax.Parsing
open Syntax.Parsing

namespace Syntax

def lparen_token : String := "("
def rparen_token : String := ")"
def comma_token : String := ","
def equals_token : String := "="
def arrow_token : String := "→"
def lambda_token : String := "ꟛ"
def let_token : String := "let"
def in_token : String := "in"
def true_token := "true"
def false_token := "false"
def double_quotes := '"'
def underscore := '_'

def reserved_tokens := [
  lambda_token, let_token, in_token, equals_token,
  arrow_token, lparen_token, rparen_token, comma_token,
  true_token, false_token]

@[reducible]
def is_reserved (t: String) := reserved_tokens.contains t

@[reducible]
def is_identifier (t: String) : Bool :=
  let is_underscore c := c = underscore
  t.startsWith (fun x => is_underscore x ∨ Char.isAlpha x)
  ∧ t.all (fun x => is_underscore x ∨ Char.isAlphanum x)

example: ¬is_identifier "α" := by decide
example: is_identifier "user" := by simp[is_identifier]; rfl
example: ¬is_identifier "1oe" := by simp[is_identifier]; rfl

@[reducible]
def identifier : Parser String := guardp is_identifier any

example: identifier ["user", "bla"] "user" ["bla"] := by
  simp [identifier, guardp]
  decide

def is_number (xs: String): Bool := xs.all Char.isDigit
def is_bool (xs: String): Bool := xs = true_token ∨ xs = false_token
def is_string (xs: String): Bool :=
  let is_double_quotes c := c = double_quotes
  xs.startsWith is_double_quotes ∧ xs.endsWith is_double_quotes

def unquote (s: String): String :=
  ((s.drop 1).dropEnd 1).toString

inductive Literal where
| number_lit (s: Nat)
| bool_lit (b: Bool)
| string_lit (s: String)

@[reducible]
def make_number (s: String): Literal := .number_lit s.toNat!

@[reducible]
def make_bool (s: String): Literal := .bool_lit (s == true_token)

@[reducible]
def make_string (s: String): Literal := .string_lit (unquote s)

@[reducible]
def literal : Parser Literal :=
  make_number <$> guardp is_number any
  <|> make_bool <$> guardp is_bool any
  <|> make_string <$> guardp is_string any

example: literal ["42", "bla"] (.number_lit 42) ["bla"] := by
  simp [literal, HOrElse.hOrElse, OrElse.orElse, choice, map, guardp]
  exists "42"
  native_decide

example: literal ["true", "bla"] (.bool_lit true) ["bla"] := by
  simp [literal, HOrElse.hOrElse, OrElse.orElse, choice, map, guardp]
  decide

example: literal ["\"hi\"", "bla"] (.string_lit "hi") ["bla"] := by
  simp only [literal, HOrElse.hOrElse, OrElse.orElse, choice, map, guardp]
  right
  right
  exists "\"hi\""
  simp [unquote]
  native_decide

def lparen : Parser String := tk lparen_token
def rparen : Parser String := tk rparen_token
def comma : Parser String := tk comma_token
def equals : Parser String := tk equals_token
def arrow : Parser String := tk arrow_token
def lambda_tok : Parser String := tk lambda_token
def let_tok : Parser String := tk let_token
def in_tok : Parser String := tk in_token

end Syntax
