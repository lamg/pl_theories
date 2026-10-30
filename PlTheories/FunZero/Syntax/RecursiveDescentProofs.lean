import PlTheories.FunZero.Syntax.Parsing
import PlTheories.FunZero.Syntax.RecursiveDescent

namespace RecursiveDescent

theorem tk_spec_ok (input rest : List String) (s : String) :
  tk s input = .ok (s, rest) ↔ Syntax.Parsing.tk s input s rest
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
        simp [Syntax.Parsing.tk]
      · simp [tk, hy] at h
  · intro h
    cases input with
    | nil => cases h.left
    | cons y ys =>
      cases h.left
      simp [tk]

theorem any_spec_ok (rest: List String) (hd: String):
  any (hd :: rest) = .ok (hd, rest) ↔ Syntax.Parsing.any (hd :: rest) hd rest
:= by simp [any]

theorem pure_spec_ok (x: α) (input: List String) (r: α) (rest: List String):
  pure x input = .ok (r, rest) ↔ Syntax.Parsing.pure x input r rest
:= by
  constructor
  · intro h
    simp [Syntax.Parsing.pure]
    simp [pure] at h
    exact (And.intro h.1.symm h.2.symm)
  · intro h
    simp [pure]
    simp [Syntax.Parsing.pure] at h
    exact ⟨h.1.symm, h.2.symm⟩

theorem fail_spec_ok (input rest: List String) (result: α):
  fail input = .ok (result, rest) ↔ Syntax.Parsing.fail input result rest
:= by
  simp [fail]

example (x : α) : FollowsSpec (pure x) (Syntax.Parsing.pure x) :=
  pure_spec_ok x

theorem first_choice_spec_ok (hp: FollowsSpec p P) (hq: FollowsSpec q Q):
  FollowsSpec (choice p q) (Syntax.Parsing.first_choice P Q)
:= by
  intro input result rest
  constructor
  · simp [choice]
    cases hip: p input with
    | ok res =>
      simp
      intro res_fst res_snd
      simp [Syntax.Parsing.first_choice]
      left
      rw [<-hp, hip, <-res_fst, <-res_snd]
    | error e =>
      simp
      cases hiq: q input with
      | ok res =>
        simp
        intro res_fst res_snd
        simp [Syntax.Parsing.first_choice]
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
      simpa [Syntax.Parsing.first_choice, ← hp input, hip, Prod.ext_iff] using h_fst_choice
    | error e =>
      simp
      cases hiq : q input with
      | ok res => simp; simpa [Syntax.Parsing.first_choice, ← hp input, ← hq input, hip, hiq, Prod.ext_iff] using h_fst_choice
      | error e => simp [Syntax.Parsing.first_choice, ← hp input, ← hq input, hip, hiq] at h_fst_choice

theorem seq_spec_ok (hp: FollowsSpec p P) (hq: FollowsSpec q Q):
  ∀ input r rest,
    seq p q input = .ok (r, rest) ↔ Syntax.Parsing.seq P Q input r rest
:= by
  intro input (pr, pq) rest
  constructor
  · intro h
    cases hip: p input with
    | ok r =>
      cases hiq: q r.snd with
      | ok s =>
        simp [seq, hip, hiq] at h
        exact ⟨r.fst, s.fst, r.snd,
          Prod.ext h.1.1.symm h.1.2.symm,
          (hp input r.fst r.snd).mp hip,
          by simpa only [h.2] using (hq r.snd s.fst s.snd).mp hiq⟩
      | error e => simp [seq, hip, hiq] at h
    | error e => simp [seq, hip] at h
  · intro ⟨a, b, mid, hr, hP, hQ⟩
    rw [← hp] at hP
    rw [← hq] at hQ
    simp [seq, hP, hQ, hr]

-- The implementation is greedy; Syntax.Parsing.many also allows stopping early.
theorem many_spec_ok (hp: FollowsSpec p P):
  ∀ input xs rest,
    many p input = .ok (xs, rest) → Syntax.Parsing.many P input xs rest
:= by
  intro input xs rest
  induction xs generalizing input with
  | nil =>
    intro h
    rw [many] at h
    cases hip: p input with
    | error e =>
      simp [hip] at h
      exact h
    | ok r =>
      simp only [hip] at h
      split at h
      · cases hm: many p r.snd with
        | error e => simp [hm] at h
        | ok s => simp [hm] at h
      · simp at h
  | cons x xs ih =>
    intro h
    rw [many] at h
    cases hip: p input with
    | error e => simp [hip] at h
    | ok r =>
      simp only [hip] at h
      split at h
      · cases hm: many p r.snd with
        | error e => simp [hm] at h
        | ok s =>
          simp only [hm, Except.ok.injEq, Prod.mk.injEq, List.cons.injEq] at h
          exact ⟨r.snd,
            (hp input x r.snd).mp (by rw [← h.1.1]; exact hip),
            ih r.snd (by rw [← h.1.2, ← h.2]; exact hm)⟩
      · simp at h

-- General forms for use as premises of the combinator correctness theorems.
theorem tk_follows_spec (s: String): FollowsSpec (tk s) (Syntax.Parsing.tk s) := by
  intro input result rest
  cases input with
  | nil => simp [tk, Syntax.Parsing.tk]
  | cons x xs =>
    by_cases h : x = s
    · subst x
      simp [tk, Syntax.Parsing.tk, eq_comm, and_comm]
    · simp [tk, Syntax.Parsing.tk, h]

theorem any_follows_spec: FollowsSpec any Syntax.Parsing.any := by
  intro input result rest
  cases input with
  | nil => simp [any, Syntax.Parsing.any]
  | cons x xs => simp [any, Syntax.Parsing.any]

-- Deterministic choice is sound for the nondeterministic specification.
theorem choice_spec_ok (hp: FollowsSpec p P) (hq: FollowsSpec q Q):
  ∀ input result rest,
    choice p q input = .ok (result, rest) → Syntax.Parsing.choice P Q input result rest
:= by
  intro input result rest h
  rcases (first_choice_spec_ok hp hq input result rest).mp h with hP | ⟨_, hQ⟩
  · exact Or.inl hP
  · exact Or.inr hQ

theorem map_spec_ok (f: α → β) (hp: FollowsSpec p P):
  FollowsSpec (map f p) (Syntax.Parsing.map f P)
:= by
  intro input result rest
  cases h: p input with
  | error e => simp [map, Syntax.Parsing.map, ← hp input, h]
  | ok r =>
    rcases r with ⟨x, remaining⟩
    simp only [map, h, Except.ok.injEq, Prod.mk.injEq, Syntax.Parsing.map, ← hp input]
    constructor
    · intro ⟨hf, hr⟩
      exact ⟨x, ⟨rfl, hr⟩, hf⟩
    · intro ⟨a, ⟨ha, hr⟩, hf⟩
      exact ⟨ha ▸ hf, hr⟩

theorem guardp_spec_ok (f: α → Bool) (hp: FollowsSpec p P):
  FollowsSpec (guardp f p) (Syntax.Parsing.guardp f P)
:= by
  intro input result rest
  cases h: p input with
  | error e => simp [guardp, Syntax.Parsing.guardp, ← hp input, h]
  | ok r =>
    rcases r with ⟨x, remaining⟩
    by_cases hf : f x = true
    · simp [guardp, Syntax.Parsing.guardp, ← hp input, h, hf]
      intro hx _
      simpa [← hx] using hf
    · simp [guardp, Syntax.Parsing.guardp, ← hp input, h, hf]
      intro _ hx _
      subst result
      contradiction

theorem digits_spec_ok: FollowsSpec digits Syntax.Parsing.digits :=
  guardp_spec_ok all_digits any_follows_spec

theorem alpha_spec_ok: FollowsSpec alpha Syntax.Parsing.alpha :=
  guardp_spec_ok all_alpha any_follows_spec

theorem left_spec_ok (hp: FollowsSpec p P) (hq: FollowsSpec q Q):
  FollowsSpec (left p q) (Syntax.Parsing.left P Q)
:= by
  intro input result rest
  rw [left, map_spec_ok Prod.fst (seq_spec_ok hp hq)]
  constructor
  · intro ⟨⟨a, b⟩, ⟨x, y, mid, hr, hP, hQ⟩, ha⟩
    cases hr
    subst result
    exact ⟨mid, b, hP, hQ⟩
  · intro ⟨mid, ignored, hP, hQ⟩
    exact ⟨(result, ignored), ⟨result, ignored, mid, rfl, hP, hQ⟩, rfl⟩

theorem right_spec_ok (hp: FollowsSpec p P) (hq: FollowsSpec q Q):
  FollowsSpec (right p q) (Syntax.Parsing.right P Q)
:= by
  intro input result rest
  rw [right, map_spec_ok Prod.snd (seq_spec_ok hp hq)]
  constructor
  · intro ⟨⟨a, b⟩, ⟨x, y, mid, hr, hP, hQ⟩, hb⟩
    cases hr
    subst result
    exact ⟨mid, a, hP, hQ⟩
  · intro ⟨mid, ignored, hP, hQ⟩
    exact ⟨(ignored, result), ⟨ignored, result, mid, rfl, hP, hQ⟩, rfl⟩

end RecursiveDescent
