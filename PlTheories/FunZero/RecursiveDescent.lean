import PlTheories.Parsing

namespace RecursiveDescent

inductive ParseError where
  | unexpectedToken (expected : String) (found : String)
  | unexpectedEnd (expected : String)
  | alwaysFails
deriving DecidableEq, Repr

abbrev RdParser α := List String → Except ParseError (α × List String)

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

theorem tk_spec_ok (input rest : List String) (s : String) :
  tk s input = .ok (s, rest) ↔ Parsing.tk s input s rest
:= by
  constructor
  · intro h
    cases input with
    | nil => simp [tk] at h
    | cons y ys =>
      by_cases hy : y = s
      · simp [tk, hy] at h
        cases h
        subst hy
        simp [Parsing.tk]
      · simp [tk, hy] at h
  · intro h
    cases input with
    | nil => cases h.left
    | cons y ys =>
      cases h.left
      simp [tk]

def any : RdParser String :=
  fun input =>
  match input with
  | [] => .error (.unexpectedEnd "")
  | x :: xs => .ok (x, xs)

theorem any_spec_ok (rest: List String) (hd: String):
  any (hd :: rest) = .ok (hd, rest) ↔ Parsing.any (hd :: rest) hd rest
:= by simp [any]

def pure (x: α): RdParser α :=
  fun input => .ok (x, input)

theorem pure_spec_ok (x: α) (input: List String) (r: α) (rest: List String):
  pure x input = .ok (r, rest) ↔ Parsing.pure x input r rest
:= by
  constructor
  · intro h
    simp [Parsing.pure]
    simp [pure] at h
    exact (And.intro h.1.symm h.2.symm)
  · intro h
    simp [pure]
    simp [Parsing.pure] at h
    exact ⟨h.1.symm, h.2.symm⟩

def fail : RdParser α :=
  fun _input => .error .alwaysFails

theorem fail_spec_ok (input rest: List String) (result: α):
  fail input = .ok (result, rest) ↔ Parsing.fail input result rest
:= by
  simp [fail, Parsing.fail]

end RecursiveDescent
