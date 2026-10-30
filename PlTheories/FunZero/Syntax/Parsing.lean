namespace Syntax.Parsing

/-!
## Parser

_Parser_ defines the signature of a relation between an input tokens,
a result value, and the remaining tokens after parsing that value. Those
relations are not meant to implement parsing, just to declare the behavior
of parsers to then prove the correctness of any implementation.

-/
abbrev Parser (α: Type) := List String → α → List String → Prop

/--
_tk_ illustrates the above introduction: given a token, specifies the behavior
of a parser that recognizes that token at the head of input, or fails.
-/
@[reducible]
def tk (s: String): Parser String :=
  fun input result rest =>
    input = s :: rest ∧ result = s

set_option pp.all false in
example: (tk "let") ["let", "find_user"] "let" ["find_user"] := by decide

set_option pp.all false in
example: ¬ (tk "module") ["bla"] "bla" ["bla"] := by decide

/--
_any_ specifies the behavior of a parser that always succeeds on non-empty
sequences of tokens, consuming the head token.
-/
@[reducible]
def any : Parser String :=
  fun input result rest => input = result :: rest

example: any ["a", "b"] "a" ["b"] := by decide

/--
_pure_ consumes no input and returns its parameter as successfully parsed
result
-/
@[reducible]
def pure (x: α) : Parser α :=
  fun input result rest => result = x ∧ rest = input

example: pure 1 ["a", "b"] 1 ["a", "b"] := by decide

/--
_fail_ always fails to parse.
-/
@[reducible]
def fail : Parser α := fun _input _result _rest => False

example: ¬ fail ["a"] ["a"] [] := by decide

/--
_choice_ succeeds if any of the parsers passed as argument succeeds, in no
particular order, i.e. non-deterministically.
-/
@[reducible]
def choice (x y : Parser α) : Parser α :=
  fun input result rest =>
    x input result rest ∨ y input result rest

/--
_first_choice_ is a more convenient specification for the choice like behavior
described above, since implementations tend to deterministically try the
first parser, and if it fails then they try the second. To rely on the above
_choice_ definition would make proofs to cumbersome for some typical
implementations.
-/
@[reducible]
def first_choice (x y : Parser α) : Parser α :=
  fun input result rest =>
    x input result rest ∨
      ((¬ ∃ r s, x input r s) ∧ y input result rest)

set_option pp.all false in
example: (first_choice (tk "bla") (tk "ok")) ["ok"] "ok" [] := by
  simp [first_choice, tk]

set_option pp.all false in
example: (first_choice (pure 1) (pure 2)) [] 1 [] := by
  simp [first_choice, pure]

set_option pp.all false in
example: ¬ (first_choice (pure 1) (pure 2)) [] 2 [] := by
  simp [first_choice, pure]

set_option pp.all false in
instance : OrElse (Parser α) where
  orElse p q := choice p (q ())

set_option pp.all false in
example: ((tk "ok") <|> (tk "bla")) ["ok"] "ok" [] := by
  show choice (tk "ok") (tk "bla") ["ok"] "ok" []
  decide

set_option pp.all false in
example: ((tk "bla") <|> (tk "bla")) ["bla"] "bla" [] := by
  show choice (tk "bla") (tk "bla") ["bla"] "bla" []
  decide

/--
_seq_ applies two parsers sequentially. The first on the original input,
the second on the remaining tokens after the first succeeds. Both results are
compound the resulting tuple value.
-/
@[reducible]
def seq (p: Parser α) (q: Parser β): Parser (α × β) :=
  fun input result rest =>
    ∃ a b mid, result = (a, b) ∧ p input a mid ∧ q mid b rest

infixl:60 " <*> " => seq

set_option pp.all false in
example: ((tk "a") <*> (tk "b")) ["a", "b"] ("a", "b") [] := by
  simp [seq]
  exists "a"
  exists "b"
  constructor
  · simp
  · exists ["b"]

set_option pp.all false in
example: (tk "a" <*> tk "b") ["a", "b"] ("a", "b") [] :=
  ⟨"a", "b", ["b"], rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/--
_many_ applies a parser zero or more times, resulting on a list of values.
-/
@[reducible]
def many (p: Parser α): Parser (List α)
  | input, [], rest => input = rest
  | input, a :: results, rest =>
    ∃ mid, p input a mid ∧ many p mid results rest

set_option pp.all false in
example: many (tk "a") ["b"] [] ["b"] := rfl

set_option pp.all false in
example: many (tk "a") ["a", "a", "b"] ["a", "a"] ["b"] := by
  simp [many]
  exists ["a", "b"]

/--
_map_ applies a function to the result value of a successful Parser
-/
@[reducible]
def map (f: α → β) (p: Parser α): Parser β :=
  fun input result rest =>
    ∃ a, p input a rest ∧ f a = result

infixr:100 " <$> " => map

set_option pp.all false in
example: (String.length <$> tk "abcd") ["abcd"] 4 [] :=
  ⟨"abcd", ⟨rfl, rfl⟩, rfl⟩

set_option pp.all false in
example: map (String.toInt?) (tk "1") ["1"] (.some 1) [] := by
  simp [map]
  exists "1"
  native_decide

/--
_guardp_ constraints the success of a parser using a predicate f on its
result value
-/
@[reducible]
def guardp(f: α → Bool) (p: Parser α): Parser α :=
  fun input result rest =>
    (f result) ∧ p input result rest

set_option pp.all false in
def all_digits (xs: String) := xs.all Char.isDigit

set_option pp.all false in
def all_alpha (xs: String) := xs.all Char.isAlpha

set_option pp.all false in
example: guardp all_digits any ["33", "bla"] "33" ["bla"] := by
  simp [guardp, all_digits]

set_option pp.all false in
example: ¬guardp all_digits any ["bla"] "" ["bla"] := by
  simp [guardp]

/--
_digits_ and _alpha_ are convenient specifications for parsers that succeed
only on digit tokens and alphabetic characters respectively.
-/
def digits := guardp all_digits any
def alpha := guardp all_alpha any

/--
_left_ applies two parsers but only returns the result of the first one
-/
@[reducible]
def left (p: Parser α) (q: Parser β): Parser α :=
  fun input result rest =>
    ∃ mid ignored, p input result mid ∧ q mid ignored rest

infixl:60 " <* " => left

set_option pp.all false in
example: (digits <* alpha) ["12", "bla"] "12" [] := by
  simp [left, digits, guardp, all_digits, alpha, all_alpha]

/--
_right_ applies two parsers but only returns the result of the second one
-/
@[reducible]
def right (p: Parser α) (q: Parser β): Parser β :=
  fun input result rest =>
    ∃ mid ignored, p input ignored mid ∧ q mid result rest

infixl:60 " *> " => right

set_option pp.all false in
example: (digits *> alpha) ["12", "bla"] "bla" [] := by
  simp [right, digits, guardp, alpha, all_digits, all_alpha]

end Syntax.Parsing
