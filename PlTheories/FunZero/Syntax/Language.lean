import PlTheories.FunZero.Syntax.Parsing
import PlTheories.FunZero.Syntax.Helpers
open Syntax.Parsing

namespace Syntax

/--
_Literal_ defines the literals we support in our language:
-/
inductive Literal where
| number_lit (s: Nat)
| bool_lit (b: Bool)
| string_lit (s: String)

set_option pp.all false in
@[reducible]
def make_number (s: String): Literal := .number_lit s.toNat!

set_option pp.all false in
@[reducible]
def make_bool (s: String): Literal := .bool_lit (s == true_token)

set_option pp.all false in
@[reducible]
def make_string (s: String): Literal := .string_lit (unquote s)

set_option pp.all false in
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

/--
_Expr_ defines the basic expressions of our language:

- variable
- literal
- tuple
- lambda abstraction
- function application
- let binding
-/

inductive Expr where
| var (s: String)
| literal (l: Literal)
| tuple (fst: Expr) (snd: Expr)
| abs (x: String) (body: Expr)
| app (f: Expr) (arg: Expr)
| let_ (v: String) (binding: Expr) (inExpr: Expr)

/--
Basically _Expr_ is a tree and for each constructor above we have a parser
specification. The ones for _var_ and _literal_ are the following:
-/

def var_parser : Parser Expr := .var <$> identifier
def literal_parser: Parser Expr := .literal <$> literal

mutual
/--
The following are a little more complicated, but basically they all follow
the pattern of declaring the intermediate rest values in the existential
quantifier, and use each one as input to the next.
-/
def tuple_parser : Parser Expr
  | input, .tuple e1 e2, rest =>
    ∃ left_rest e1_rest comma_rest e2_rest,
      lparen input lparen_token left_rest
      ∧ expression left_rest e1 e1_rest
      ∧ comma e1_rest comma_token comma_rest
      ∧ expression comma_rest e2 e2_rest
      ∧ rparen e2_rest rparen_token rest
  | _, _, _ => False

def lambda_parser : Parser Expr
  | input, .abs x body, rest =>
    ∃ lambda_rest ident_rest arrow_rest,
      lambda_tok input lambda_token lambda_rest
      ∧ identifier lambda_rest x ident_rest
      ∧ arrow ident_rest arrow_token arrow_rest
      ∧ expression arrow_rest body rest
  | _, _, _ => False

def app_parser : Parser Expr
  | input, .app f arg, rest =>
    ∃ f_rest,
      expression input f f_rest
      ∧ expression f_rest arg rest
  | _, _, _ => False

def let_parser : Parser Expr
  | input, .let_ v binding inExpr, rest =>
    ∃ let_rest id_rest eq_rest ex_rest in_rest,
      let_tok input let_token let_rest
      ∧ identifier let_rest v id_rest
      ∧ equals id_rest equals_token eq_rest
      ∧ expression eq_rest binding ex_rest
      ∧ in_tok ex_rest in_token in_rest
      ∧ expression in_rest inExpr rest
  | _, _, _ => False

/--
Now _expression_ includes them all:
-/
def expression : Parser Expr
  | input, .var s, rest => var_parser input (.var s) rest
  | input, .literal l, rest => literal_parser input (.literal l) rest
  | input, .tuple e1 e2, rest => tuple_parser input (.tuple e1 e2) rest
  | input, .abs x body, rest => lambda_parser input (.abs x body) rest
  | input, .app f arg, rest => app_parser input (.app f arg) rest
  | input, .let_ v binding inExpr, rest =>
      let_parser input (.let_ v binding inExpr) rest

end

example: tuple_parser ["(", "x", ",", "y", ")"]
    (.tuple (.var "x") (.var "y")) [] := by
  simp [tuple_parser, expression, var_parser, map, identifier, guardp, lparen, comma, rparen, lparen_token, comma_token, rparen_token, tk]
  exists [",", "y", ")"]

example: lambda_parser ["ꟛ", "x", "→", "x"] (.abs "x" (.var "x")) [] := by
  simp [lambda_parser, expression, var_parser, map, identifier, guardp, lambda_tok, arrow, lambda_token, arrow_token, tk]
  exists ["→", "x"]

example: app_parser ["f", "x"] (.app (.var "f") (.var "x")) [] := by
  simp [app_parser, expression, var_parser, map, identifier, guardp]
  decide

example: let_parser ["let", "x", "=", "1", "in", "x"]
    (.let_ "x" (.literal (.number_lit 1)) (.var "x")) [] := by
  simp [
    let_parser, expression, literal_parser, var_parser, map, identifier,
    let_tok, equals, in_tok, let_token, equals_token, in_token, tk,
    literal, HOrElse.hOrElse, OrElse.orElse, choice, guardp, is_number]
  exists ["=", "1", "in", "x"]
  simp
  constructor
  · decide
  · exists ["in", "x"]
    simp
    constructor
    · exists "1"
      native_decide
    · native_decide

example: expression ["(", "x", ",", "y", ")"]
    (.tuple (.var "x") (.var "y")) [] := by
  simp [
    expression, tuple_parser, var_parser, map, identifier, guardp,
    lparen, comma, rparen, lparen_token, comma_token, rparen_token, tk]
  exists [",", "y", ")"]

end Syntax
