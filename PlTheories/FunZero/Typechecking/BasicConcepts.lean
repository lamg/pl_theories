import PlTheories.FunZero.Syntax.Language

/-!
# Basic concepts

This is the first layer of the typechecking development: expressions, types, schemes,
and contexts. `Syntax` supplies the expressions; this module supplies the
vocabulary for discussing their types. It does not yet solve type equations
or decide which expressions have which types.
-/

/--
The expressions in `Syntax.Expr` form a small language in the ML family.
Their types describe concrete values, unknown types, functions, and pairs.
A type variable names something inference may later discover; an arrow
records both the argument type and the result type of a function.
-/
inductive FzType where
| tcon (s: String)
| tvar (s: String)
| arrow (x y : FzType)
| prod (x y : FzType)
deriving DecidableEq, Repr

namespace Typechecking

/--
A literal already tells us what kind of value it represents.
[`Syntax.Literal`](PlTheories/FunZero/Syntax/Language/#Syntax___Literal) distinguishes numbers,
booleans, and strings. Number literals contain a `Nat`, so their type is `Nat`.
-/
def literalType : Syntax.Literal → FzType
  | .number_lit _ => .tcon "Nat"
  | .bool_lit _ => .tcon "Bool"
  | .string_lit _ => .tcon "String"

/--
A context stores schemes, so that a let-bound identity can be used at both
`Nat → Nat` and `Bool → Bool`. A scheme separates its quantified names from
its type body: `⟨["a"], .arrow (.tvar "a") (.tvar "a")⟩` represents `∀ a, a → a`.
Names in the body that are not quantified remain shared with the context.
The list of quantified names represents a sequence of universal quantifiers.
-/
structure Scheme where
  quantified : List String
  body : FzType
  deriving DecidableEq, Repr

/--
A monomorphic scheme quantifies no names. Lambda parameters use this form:
all uses of a parameter must agree on one type, even if that type still
contains unknowns. Quantifying those unknowns would break that agreement.
-/
def Scheme.mono (t: FzType): Scheme := ⟨[], t⟩

/--
A context associates expression variables with schemes. The first binding
for a name is the visible one; `[]` is the empty context. Keeping this
representation concrete lets us compute lookup without adding axioms.
-/
abbrev Context := List (String × Scheme)

/--
Looking up an unbound name returns `none`. A successful lookup retrieves
a scheme; deciding how that scheme can be instantiated belongs to the
later typing layer, once substitution has been introduced.
-/
def lookup : Context → String → Option Scheme
  | [], _ => none
  | (y, sc) :: Γ, x => if x = y then some sc else lookup Γ x

/--
Extending a context introduces a binding that shadows earlier bindings of
the same expression variable. Removing the old entries also keeps their
free type variables out of later generalization.
-/
def extend (Γ: Context) (x: String) (sc: Scheme): Context :=
  (x, sc) :: Γ.filter (fun binding => binding.1 != x)

/--
The most recently introduced binding is the one lookup observes.
-/
theorem lookup_extend_same (Γ: Context) (x: String) (sc: Scheme):
    lookup (extend Γ x sc) x = some sc := by
  simp [extend, lookup]

end Typechecking
