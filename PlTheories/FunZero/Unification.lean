import PlTheories.FunZero.BasicConcepts

/-!
# Making types agree

Suppose a lambda body uses its parameter as a function, as in `x 42`.
Its previously unknown type must now agree with an arrow. Substitutions
record such discoveries; unification asks which discoveries make two types
agree while leaving as much as possible open. This second layer describes
those operations without examining an expression.
-/

namespace Typechecking

/--
A substitution records discoveries such as “a stands for Nat”. We use a
finite list of replacements, with the first binding for a name taking
precedence. The empty list is the identity substitution; a singleton makes
one replacement. Replacements are simultaneous, not recursively expanded.
-/
abbrev Substitution := List (String × FzType)

/--
A name with no recorded replacement remains a type variable. This lookup
returns the replacement as stored; it does not apply the substitution again
to that replacement.
-/
def substitutionLookup : Substitution → String → FzType
  | [], x => .tvar x
  | (y, t) :: s, x => if x = y then t else substitutionLookup s x

/--
Applying a substitution writes its replacements into a type. Concrete types
stay unchanged, while arrows and products are rebuilt from their parts.
This operation describes the effect of a discovery before we discuss how
a unification algorithm makes that discovery.
-/
def applyType (s: Substitution): FzType → FzType
  | .tcon c => .tcon c
  | .tvar x => substitutionLookup s x
  | .arrow a b => .arrow (applyType s a) (applyType s b)
  | .prod a b => .prod (applyType s a) (applyType s b)

/--
Composition carries discoveries forward: `compose s₂ s₁` applies `s₁`
first and then `s₂`. Replacements already present in `s₁` are rewritten by
`s₂`; names absent from `s₁` can still receive a replacement from `s₂`.
-/
def compose (s₂ s₁: Substitution): Substitution :=
  s₁.map (fun (x, t) => (x, applyType s₂ t)) ++ s₂

/--
The free variables of a type tell us which unknowns it mentions. This is
also the information needed for an occurs check: solving `a = a → b` by
replacing `a` with `a → b` cannot produce a finite type. Lists represent
finite sets here; membership, rather than order, matters.
-/
def freeTypeVars : FzType → List String
  | .tcon _ => []
  | .tvar x => [x]
  | .arrow a b | .prod a b => (freeTypeVars a ++ freeTypeVars b).eraseDups

/--
Quantified names belong to the scheme itself. Only the other variables in
its body remain free, and therefore shared with the surrounding context.
-/
def Scheme.freeTypeVars (sc: Scheme): List String :=
  Typechecking.freeTypeVars sc.body |>.filter (fun x => !sc.quantified.contains x)

/--
A context mentions the free variables of its visible schemes. Shadowed
entries must not contribute, even if a caller constructed the context
list directly rather than using `extend`. The helper remembers names
already visited so that only their first bindings count.
-/
def contextFreeTypeVars (Γ: Context): List String :=
  go [] Γ
where
  go (seen: List String): Context → List String
    | [] => []
    | (x, sc) :: rest =>
      if seen.contains x then go seen rest
      else (sc.freeTypeVars ++ go (x :: seen) rest).eraseDups

/--
A fresh name is chosen longer than every name in the avoidance list.
-/
private def freshName (avoid: List String): String :=
  String.ofList (List.replicate (1 + (avoid.map String.length).foldl max 0) 'a')

/--
Choose one distinct fresh name per quantified variable. Adding each choice
to the avoidance list prevents later choices from reusing it.
-/
private def freshNames : List String → List String → List String
  | [], _ => []
  | _ :: xs, avoid =>
    let x := freshName avoid
    x :: freshNames xs (x :: avoid)

/--
Substitution in a scheme must preserve binding. Before substitution, rename
its quantified variables away from the body, the substitution domain, and
all variables in replacement types. Thus substituting `a ↦ b` in
`∀ b, a → b` keeps the introduced `b` free. Bound names may change even for
an identity substitution; schemes should be compared up to renaming when
their meaning, rather than their concrete spelling, is what matters.
-/
def applyScheme (s: Substitution) (sc: Scheme): Scheme :=
  let bound := sc.quantified.eraseDups
  let avoid := freeTypeVars sc.body ++ bound ++
    s.flatMap (fun (x, t) => x :: freeTypeVars t)
  let renamed := freshNames bound avoid
  let renames :=  bound.zip (renamed.map FzType.tvar)
  ⟨renamed, applyType s (applyType renames sc.body)⟩

/--
Apply the same discoveries to every scheme in a context. Expression
variable names are unchanged: the substitution concerns type variables.
-/
def applyContext (s: Substitution) (Γ: Context): Context :=
  Γ.map (fun (x, sc) => (x, applyScheme s sc))

/--
Two types unify under a substitution when their rewritten forms agree.
This proposition specifies a successful solution without choosing a search
procedure, a substitution representation normal form, or fresh names.
-/
def Unifies (a b: FzType) (s: Substitution): Prop :=
  applyType s a = applyType s b

/--
A most general unifier makes no unnecessary commitments: every other
unifier is obtained by applying a further substitution after it. Compare
substitutions by their effect on types, rather than equality of lists.
This is the declarative contract for the unification procedure to come.
-/
def MostGeneralUnifier (a b: FzType) (s: Substitution): Prop :=
  Unifies a b s ∧
    ∀ other, Unifies a b other →
      ∃ further, ∀ t, applyType other t = applyType further (applyType s t)

/--
With no discoveries recorded, substitution leaves every type unchanged.
-/
theorem applyType_identity (t: FzType): applyType [] t = t := by
  induction t with
  | tcon c => rfl
  | tvar x => rfl
  | arrow a b ha hb => simp [applyType, ha, hb]
  | prod a b ha hb => simp [applyType, ha, hb]

/--
Identical types need no discoveries; the identity is already most general.
-/
theorem identity_mgu (t: FzType): MostGeneralUnifier t t [] := by
  constructor
  · rfl
  · intro other _
    exact ⟨other, fun u => by rw [applyType_identity]⟩

-- A concrete discovery can make an unknown agree with a number type.
example: Unifies (.tvar "a") (.tcon "Nat") [("a", .tcon "Nat")] := by
  simp [Unifies, applyType, substitutionLookup]

example: contextFreeTypeVars
    [("x", Scheme.mono (.tcon "Nat")), ("x", Scheme.mono (.tvar "a"))] = [] := by
  simp [contextFreeTypeVars, contextFreeTypeVars.go, Scheme.freeTypeVars, Scheme.mono, freeTypeVars]

-- Substituting a ↦ b in ∀ b, a → b must leave the new b free.
example: (applyScheme [("a", .tvar "b")]
    ⟨["b"], .arrow (.tvar "a") (.tvar "b")⟩).freeTypeVars = ["b"] := by decide

end Typechecking
