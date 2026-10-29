import PlTheories.FunZero.Syntax
import PlTheories.FunZero.RecursiveDescent
import PlTheories.FunZero.AlgorithmW

/-!
# A small functional language

Our language combines literals, variables, pairs, functions, application,
and let bindings. The chapters below follow its development from syntax
to executable parsing and declarative typing rules.

1. **Language syntax** describes expressions and the token sequences that represent them.
2. **Recursive descent** implements the parser combinators and proves their correctness.
3. **Basic concepts** introduces types, schemes, and typing contexts.
4. **Unification** explains substitutions and what it means to make two types agree.
5. **Algorithm W** states the typing rules and the contract for inference.

The series is a work in progress. The inference contract is a specification;
the executable inference procedure remains to be developed.
-/
