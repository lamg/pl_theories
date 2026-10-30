import PlTheories.FunZero.Syntax.Parsing

namespace RecursiveDescent
/--
Our _Parser_ relation works as highlevel specification, it is just a relation
that evaluates to True or False according their inputs, but once we move into
the area of implementation we need to return more complex types, and take
error handling into account. That's the purpose of _ParseError_
-/
inductive ParseError where
  | unexpectedToken (expected : String) (found : String)
  | unexpectedEnd (expected : String)
  | expectingOneOf (choice₀ choice₁ : ParseError)
  | alwaysFails
  | guardFailed
  | noProgress
deriving DecidableEq, Repr

/--
_RdParser_ stands for _Recursive Descent Parser_ and for each one of it there
is a corresponding _Parser_ specification.
-/
abbrev RdParser α := List String → Except ParseError (α × List String)

/--
_tk_ corresponds to [`Parsing.tk`](PlTheories/FunZero/Syntax/Parsing/#Syntax___Parsing___tk)
-/
def tk (s: String) : RdParser String :=
  fun xs =>
  match xs with
  | [] => .error (.unexpectedEnd s)
  | y :: ys =>
    if y = s
    then .ok (y, ys)
    else .error (.unexpectedToken s y)

example: tk "let" ["let", "x"] = .ok ("let", ["x"]) := rfl
example: tk "let" ["bla", "x"] = .error (.unexpectedToken "let" "bla") := rfl
example: tk "let" [] = .error (.unexpectedEnd "let") := rfl

/--
_any_ corresponds to [`Parsing.any`](PlTheories/FunZero/Syntax/Parsing/#Syntax___Parsing___any)
-/
def any : RdParser String :=
  fun input =>
  match input with
  | [] => .error (.unexpectedEnd "")
  | x :: xs => .ok (x, xs)

/--
_pure_ corresponds to [`Parsing.pure`](PlTheories/FunZero/Syntax/Parsing/#Syntax___Parsing___pure)
-/
def pure (x: α): RdParser α :=
  fun input => .ok (x, input)

/--
_fail_ corresponds to [`Parsing.fail`](PlTheories/FunZero/Syntax/Parsing/#Syntax___Parsing___fail)
-/
def fail : RdParser α :=
  fun _input => .error .alwaysFails

/--
_choice_ corresponds to [`Parsing.first_choice`](PlTheories/FunZero/Syntax/Parsing/#Syntax___Parsing___first_choice): it tries the first parser,
and if it fails then it tries the second one.
-/
def choice (p q: RdParser α): RdParser α :=
  fun input =>
    match p input with
    | .ok (r, rest) => .ok (r,rest)
    | .error e =>
      match q input with
      | .ok (r, rest) => .ok (r, rest)
      | .error f =>
        .error (.expectingOneOf e f)

/--
_FollowsSpec_ defines the correspondence between parser implementation
and specification: an implementation follows a specification when it
succeeds exactly on the inputs, results, and remaining tokens that the
specification relates.
-/
def FollowsSpec (impl: RdParser α) (spec: Syntax.Parsing.Parser α) : Prop :=
  ∀ input result rest,
    impl input = .ok (result, rest) ↔ spec input result rest

/--
_seq_ corresponds to [`Parsing.seq`](PlTheories/FunZero/Syntax/Parsing/#Syntax___Parsing___seq)
-/
def seq (p: RdParser α) (q: RdParser β): RdParser (α × β) :=
  fun input =>
    match p input with
    | .ok (rp, rest_p) =>
      match q rest_p with
      | .ok (rq, rest_q) => .ok ((rp, rq), rest_q)
      | .error eq => .error eq
    | .error eq => .error eq

/--
_many_ corresponds to [`Parsing.many`](PlTheories/FunZero/Syntax/Parsing/#Syntax___Parsing___many): it keeps applying its parser until
it fails, and fails itself when an application succeeds without
consuming any input.
-/
def many (p: RdParser α): RdParser (List α) :=
  fun input =>
    match p input with
    | .ok (x, first_rest) =>
      if first_rest.length < input.length then
        match many p first_rest with
        | .ok (xs, rem_rest) => .ok (x :: xs, rem_rest)
        | .error e => .error e
      else
        .error .noProgress
    | .error _ => .ok ([], input)

termination_by input => input.length

example: many (tk "a") ["a", "a", "b"] = .ok (["a", "a"], ["b"])
:= by simp [many, tk]

example: many (tk "a") ["b"] = .ok ([], ["b"])
:= by simp [many, tk]

example: many (tk "a") [] = .ok ([], [])
:= by simp [many, tk]

example: many (pure 1) [] = .error .noProgress
:= by simp [many, pure]

example: many (choice (tk "a") (pure "fallback")) ["a"] = .error .noProgress
:= by simp [many, choice, tk, pure]

/--
_map_ corresponds to [`Parsing.map`](PlTheories/FunZero/Syntax/Parsing/#Syntax___Parsing___map)
-/
def map (f: α → β) (p: RdParser α): RdParser β :=
  fun input =>
    match p input with
    | .ok (x, rest) => .ok (f x, rest)
    | .error e => .error e

/--
_guardp_ corresponds to [`Parsing.guardp`](PlTheories/FunZero/Syntax/Parsing/#Syntax___Parsing___guardp)
-/
def guardp (f: α → Bool) (p: RdParser α): RdParser α :=
  fun input =>
    match p input with
    | .ok (x, rest) =>
      if f x then .ok (x, rest) else .error .guardFailed
    | .error e => .error e

/--
_all_digits_ and _all_alpha_ reuse [`Parsing.all_digits`](PlTheories/FunZero/Syntax/Parsing/#Syntax___Parsing___all_digits) and
[`Parsing.all_alpha`](PlTheories/FunZero/Syntax/Parsing/#Syntax___Parsing___all_alpha) as predicates on tokens.
-/
def all_digits := Syntax.Parsing.all_digits
def all_alpha := Syntax.Parsing.all_alpha

/--
_digits_ and _alpha_ correspond to [`Parsing.digits`](PlTheories/FunZero/Syntax/Parsing/#Syntax___Parsing___digits) and [`Parsing.alpha`](PlTheories/FunZero/Syntax/Parsing/#Syntax___Parsing___alpha)
-/
def digits := guardp all_digits any
def alpha := guardp all_alpha any

/--
_left_ corresponds to [`Parsing.left`](PlTheories/FunZero/Syntax/Parsing/#Syntax___Parsing___left)
-/
def left (p: RdParser α) (q: RdParser β): RdParser α :=
  map Prod.fst (seq p q)

/--
_right_ corresponds to [`Parsing.right`](PlTheories/FunZero/Syntax/Parsing/#Syntax___Parsing___right)
-/
def right (p: RdParser α) (q: RdParser β): RdParser β :=
  map Prod.snd (seq p q)

example: map String.length (tk "abcd") ["abcd", "rest"] = .ok (4, ["rest"]) := rfl

example: digits ["33", "bla"] = .ok ("33", ["bla"]) := by
  simp [digits, guardp, any, all_digits, Syntax.Parsing.all_digits]

example: digits ["bla"] = .error .guardFailed := by
  simp [digits, guardp, any, all_digits, Syntax.Parsing.all_digits]

example: alpha ["abc", "12"] = .ok ("abc", ["12"]) := by
  simp [alpha, guardp, any, all_alpha, Syntax.Parsing.all_alpha]

example: left digits alpha ["12", "bla"] = .ok ("12", []) := by
  simp [left, map, seq, digits, alpha, guardp, any, all_digits, all_alpha,
    Syntax.Parsing.all_digits, Syntax.Parsing.all_alpha]

example: right digits alpha ["12", "bla"] = .ok ("bla", []) := by
  simp [right, map, seq, digits, alpha, guardp, any, all_digits, all_alpha,
    Syntax.Parsing.all_digits, Syntax.Parsing.all_alpha]

example: left digits alpha ["12", "34"] = .error .guardFailed := by
  simp [left, map, seq, digits, alpha, guardp, any, all_digits, all_alpha,
    Syntax.Parsing.all_digits, Syntax.Parsing.all_alpha]

example: right digits alpha ["bad", "abc"] = .error .guardFailed := by
  simp [right, map, seq, digits, guardp, any, all_digits, Syntax.Parsing.all_digits]

end RecursiveDescent
