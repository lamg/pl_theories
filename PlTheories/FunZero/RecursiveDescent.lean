import PlTheories.Parsing

namespace RecursiveDescent

inductive ParseError where
  | unexpectedToken (expected : String) (found : String)
  | unexpectedEnd (expected : String)
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

end RecursiveDescent
