import PlTheories.FunZero.AlgorithmW

/-!
# Typechecking

The development proceeds through three layers:

1. `BasicConcepts`: types, literals, schemes, and contexts.
2. `Unification`: substitution, free variables, and most general unifiers.
3. `AlgorithmW`: instantiation, generalization, typing rules, and inference soundness.

This module re-exports all three layers for existing imports. The executable
unification and inference procedures are still to be implemented.
-/
