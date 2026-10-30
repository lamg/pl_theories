import PlTheories.FunZero.Syntax.Parsing
import PlTheories.FunZero

/-!
# Programming Language Theories

How do we describe a programming language, build an implementation, and
prove that the implementation follows the description? This series explores
those questions by developing a small language in Lean.

The language has literals, variables, pairs, functions, application, and
let bindings. We begin with specifications that explain which answers are
valid, then develop programs and proofs that connect them to those specifications.

## Parsing

Start with **Parser specifications**, which describes parsers as relations
between an input, a result, and the remaining tokens. **Language syntax**
uses those relations to describe expressions. **Recursive descent** gives
executable parser combinators and their correctness proofs.

## Typechecking

Read **Basic concepts** for types, schemes, and contexts. Continue with
**Unification** to see how substitutions express discoveries about unknown
types. Finally, **Algorithm W** introduces the declarative typing rules and
the soundness contract for a future inference implementation.

This is an ongoing development. The parser combinators are implemented;
executable type inference and evaluation semantics are still to come.
The examples and proofs on these pages are checked by Lean when the site builds.
-/
