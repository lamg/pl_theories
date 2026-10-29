import PlTheories.FunZero.Syntax
import PlTheories.FunZero.Typechecking

/-!
# A small functional language

Our language combines literals, variables, pairs, functions, application,
and let bindings. Its chapters are organized in two sections, which follow
its development from syntax to declarative typing rules.

The **Syntax** section describes the language and how its programs are read:

1. **Language syntax** describes expressions and the token sequences that represent them.
2. **Recursive descent** implements the parser combinators and proves their correctness.

The **Typechecking** section explains which types expressions may have:

1. **Basic concepts** introduces types, schemes, and typing contexts.
2. **Unification** explains substitutions and what it means to make two types agree.
3. **Algorithm W** states the typing rules and the contract for inference.

The series is a work in progress. The inference contract is a specification;
the executable inference procedure remains to be developed.
-/
