import PlTheories.FunZero.Typechecking.Unification

/-!
# Typing rules and the contract for Algorithm W

The first layer introduced the objects; the second explained how types
can be made to agree. This third layer uses both to state which types an
expression may have, then states the soundness obligation for inference.
The declarative relation comes first so the eventual executable algorithm
has an independent standard against which it can be proved correct.
-/

namespace Typechecking

/--
Using a variable means taking an instance of its stored scheme. Only
quantified names may be replaced; free names retain their shared meaning.
This completes the notion of schemes from the first layer using the
substitutions of the second layer.
-/
def Instantiates (sc: Scheme) (t: FzType): Prop :=
  ∃ s: Substitution,
    (∀ x u, (x, u) ∈ s → x ∈ sc.quantified) ∧ applyType s sc.body = t

/--
At a let binding, collect the type variables that can be reused independently:
those free in the inferred type but not free in the surrounding context.
For `let id = λx. x`, this turns `a → a` into `∀ a, a → a` when `a` is not
already shared with the context. Lambda parameters are not generalized.
-/
def generalize (Γ: Context) (t: FzType): Scheme :=
  ⟨(freeTypeVars t).filter (fun x => !(contextFreeTypeVars Γ).contains x), t⟩

/--
`HasType Γ e t` means that expression `e` has type `t` under the assumptions
in `Γ`. Each constructor is a typing rule, and a proof records a derivation.
The rules describe valid answers independently of how Algorithm W finds
them: instantiate at variable use, share a monotype inside a lambda, and
generalize at let. Application requires an arrow with the argument's type;
a tuple combines the types of its two components.
-/
inductive HasType : Context → Syntax.Expr → FzType → Prop where
  | literal : HasType Γ (.literal l) (literalType l)
  | var :
      lookup Γ x = some sc →
      Instantiates sc t →
      HasType Γ (.var x) t
  | tuple :
      HasType Γ a ta →
      HasType Γ b tb →
      HasType Γ (.tuple a b) (.prod ta tb)
  | app :
      HasType Γ f (.arrow a b) →
      HasType Γ arg a →
      HasType Γ (.app f arg) b
  | lambda :
      HasType (extend Γ x (Scheme.mono a)) body b →
      HasType Γ (.abs x body) (.arrow a b)
  | let_ :
      HasType Γ binding a →
      HasType (extend Γ x (generalize Γ a)) body b →
      HasType Γ (.let_ x binding body) b

/--
The declarative interface relates a context, an expression, and a type.
Its result is a proposition whose evidence is a typing derivation.
-/
abbrev TypingRelation := Context → Syntax.Expr → FzType → Prop

/--
Inference will return either an error or a substitution and a type. Its
first obligation is soundness: the returned type must be justified in the
context rewritten by that substitution. This states an obligation on a
future implementation; it does not implement Algorithm W.

Completeness and principality additionally require every valid typing to
be obtainable from the inferred answer by further substitution. They do
not require every valid type to equal the particular type inference returns.
-/
def InferenceSound (infer: Context → Syntax.Expr → Except ε (Substitution × FzType)):
    Prop :=
  ∀ Γ e s t, infer Γ e = .ok (s, t) → HasType (applyContext s Γ) e t

/--
A monomorphic scheme has exactly its stored type as an instance. This is
why different uses of one lambda parameter cannot choose different types.
-/
theorem instantiates_mono (a b: FzType): Instantiates (Scheme.mono a) b ↔ a = b := by
  constructor
  · intro ⟨s, hs, h⟩
    have hempty : s = [] := by
      cases s with
      | nil => rfl
      | cons binding tail =>
        have := hs binding.1 binding.2 (by simp)
        simp [Scheme.mono] at this
    simpa [hempty, Scheme.mono, applyType_identity] using h
  · intro h
    exact ⟨[], by simp, by simpa [Scheme.mono, applyType_identity] using h⟩

example: HasType [] (.literal (.number_lit 42)) (.tcon "Nat") := .literal

example (t: FzType): HasType [] (.abs "x" (.var "x")) (.arrow t t) := by
  apply HasType.lambda
  exact HasType.var (lookup_extend_same _ _ _) ((instantiates_mono t t).mpr rfl)

-- A lambda parameter's free type variables must not be generalized at let.
example: generalize [("x", Scheme.mono (.tvar "a"))]
    (.arrow (.tvar "a") (.tvar "b")) =
    ⟨["b"], .arrow (.tvar "a") (.tvar "b")⟩ := by decide

-- A let-bound identity can be instantiated at two types in the same body.
example: HasType []
    (.let_ "id" (.abs "x" (.var "x"))
      (.tuple (.app (.var "id") (.literal (.number_lit 1)))
        (.app (.var "id") (.literal (.bool_lit true)))))
    (.prod (.tcon "Nat") (.tcon "Bool")) := by
  apply HasType.let_ (a := .arrow (.tvar "a") (.tvar "a"))
  · apply HasType.lambda
    exact HasType.var (lookup_extend_same _ _ _)
      ((instantiates_mono _ _).mpr rfl)
  · apply HasType.tuple
    · apply HasType.app (a := .tcon "Nat")
      · apply HasType.var (lookup_extend_same _ _ _)
        exact ⟨[("a", .tcon "Nat")], by simp [generalize, freeTypeVars,
          contextFreeTypeVars, contextFreeTypeVars.go], rfl⟩
      · exact HasType.literal
    · apply HasType.app (a := .tcon "Bool")
      · apply HasType.var (lookup_extend_same _ _ _)
        exact ⟨[("a", .tcon "Bool")], by simp [generalize, freeTypeVars,
          contextFreeTypeVars, contextFreeTypeVars.go], rfl⟩
      · exact HasType.literal

example: ¬HasType []
    (.app (.literal (.number_lit 1)) (.literal (.bool_lit true))) t := by
  intro h
  cases h with
  | app hf _ => cases hf

end Typechecking
