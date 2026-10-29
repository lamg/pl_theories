import PlTheories.Parsing

namespace RecursiveDescent

inductive ParseError where
  | unexpectedToken (expected : String) (found : String)
  | unexpectedEnd (expected : String)
  | expectingOneOf (choice₀ choice₁ : ParseError)
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
  simp [fail]

def choice (p q: RdParser α): RdParser α :=
  fun input =>
    match p input with
    | .ok (r, rest) => .ok (r,rest)
    | .error e =>
      match q input with
      | .ok (r, rest) => .ok (r, rest)
      | .error f =>
        .error (.expectingOneOf e f)

-- FollowsSpec defines the correspondence between parser
-- implementation and specification
def FollowsSpec (impl: RdParser α) (spec: Parsing.Parser α) : Prop :=
  ∀ input result rest,
    impl input = .ok (result, rest) ↔ spec input result rest

example (x : α) : FollowsSpec (pure x) (Parsing.pure x) :=
  pure_spec_ok x

theorem first_choice_spec_ok (hp: FollowsSpec p P) (hq: FollowsSpec q Q):
  FollowsSpec (choice p q) (Parsing.first_choice P Q)
:= by
  intro input result rest
  constructor
  · simp [choice]
    cases hip: p input with
    | ok res =>
      simp
      intro res_fst res_snd
      simp [Parsing.first_choice]
      left
      rw [<-hp, hip, <-res_fst, <-res_snd]
    | error e =>
      simp
      cases hiq: q input with
      | ok res =>
        simp
        intro res_fst res_snd
        simp [Parsing.first_choice]
        right
        constructor
        · intro x x_1
          rw [<-hp, hip]
          simp
        · rw [<-hq, hiq, <-res_fst, <-res_snd]
      | error e => simp
  · intro h_fst_choice
    simp [choice]
    cases hip: p input with
    | ok res =>
      simp
      simpa [Parsing.first_choice, ← hp input, hip, Prod.ext_iff] using h_fst_choice
    | error e =>
      simp
      cases hiq : q input with
      | ok res => simp; simpa [Parsing.first_choice, ← hp input, ← hq input, hip, hiq, Prod.ext_iff] using h_fst_choice
      | error e => simp [Parsing.first_choice, ← hp input, ← hq input, hip, hiq] at h_fst_choice








end RecursiveDescent
