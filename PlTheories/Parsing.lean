namespace Parsing

abbrev Parser (α: Type) := List String → α → List String → Prop

@[reducible]
def tk (s: String): Parser String :=
  fun input result rest =>
    input = s :: rest ∧ result = s

example: (tk "let") ["let", "find_user"] "let" ["find_user"] := by decide
example: ¬ (tk "module") ["bla"] "bla" ["bla"] := by decide

@[reducible]
def any : Parser String :=
  fun input result rest => input = result :: rest

example: any ["a", "b"] "a" ["b"]  := by decide

@[reducible]
def pure (x: α) : Parser α :=
  fun input result rest => result = x ∧ rest = input

example: pure 1 ["a", "b"] 1 ["a", "b"] := by decide

@[reducible]
def fail : Parser α := fun _input _result _rest => False

example: ¬ fail ["a"] ["a"] [] := by decide

@[reducible]
def choice (x y : Parser α) : Parser α :=
  fun input result rest =>
    x input result rest ∨ y input result rest

instance : OrElse (Parser α) where
  orElse p q := choice p (q ())

example: ((tk "ok") <|> (tk "bla")) ["ok"] "ok" [] := by
  show choice (tk "ok") (tk "bla") ["ok"] "ok" []
  decide
example: ((tk "bla") <|> (tk "bla")) ["bla"] "bla" [] := by
  show choice (tk "bla") (tk "bla") ["bla"] "bla" []
  decide

@[reducible]
def seq (p: Parser α) (q: Parser β): Parser (α × β) :=
  fun input result rest =>
    ∃ a b mid, result = (a, b) ∧ p input a mid ∧ q mid b rest

infixl:60 " <*> " => seq

example: ((tk "a") <*> (tk "b")) ["a", "b"] ("a", "b") [] := by
  simp [seq]
  exists "a"
  exists "b"
  constructor
  · simp
  · exists ["b"]

example: (tk "a" <*> tk "b") ["a", "b"] ("a", "b") [] :=
  ⟨"a", "b", ["b"], rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

@[reducible]
def many (p: Parser α): Parser (List α)
  | input, [], rest => input = rest
  | input, a :: results, rest =>
    ∃ mid, p input a mid ∧ many p mid results rest

example: many (tk "a") ["b"] [] ["b"] := rfl
example: many (tk "a") ["a", "a", "b"] ["a", "a"] ["b"] := by
  simp [many]
  exists ["a", "b"]

@[reducible]
def map (f: α → β) (p: Parser α): Parser β :=
  fun input result rest =>
    ∃ a, p input a rest ∧ f a = result

infixr:100 " <$> " => map

example: (String.length <$> tk "abcd") ["abcd"] 4 [] :=
  ⟨"abcd", ⟨rfl, rfl⟩, rfl⟩

example: map (String.toInt?) (tk "1") ["1"] (.some 1) [] := by
  simp [map]
  exists "1"
  native_decide

@[reducible]
def guardp(f: α → Bool) (p: Parser α): Parser α :=
  fun input result rest =>
    (f result) ∧ p input result rest

def all_digits (xs: String) := xs.all Char.isDigit
def all_alpha (xs: String) := xs.all Char.isAlpha

example: guardp all_digits any ["33", "bla"] "33" ["bla"] := by
  simp [guardp, all_digits]

example: ¬guardp all_digits any ["bla"] "" ["bla"] := by
  simp [guardp]

def digits := guardp all_digits any
def alpha := guardp all_alpha any

@[reducible]
def left (p: Parser α) (q: Parser β): Parser α :=
  fun input result rest =>
    ∃ mid ignored, p input result mid ∧ q mid ignored rest

infixl:60 " <* " => left

example: (digits <* alpha) ["12", "bla"] "12" [] := by
  simp [left, digits, guardp, all_digits, alpha, all_alpha]

@[reducible]
def right (p: Parser α) (q: Parser β): Parser β :=
  fun input result rest =>
    ∃ mid ignored, p input ignored mid ∧ q mid result rest

infixl:60 " *> " => right

example: (digits *> alpha) ["12", "bla"] "bla" [] := by
  simp [right, digits, guardp, alpha, all_digits, all_alpha]

end Parsing
