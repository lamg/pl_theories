import PlTheories.FunZero.Syntax.Parsing
import PlTheories.FunZero.Syntax.Language
import PlTheories.FunZero.Syntax.RecursiveDescent

/-!
# Syntax

This section describes what the language is and how its programs are read:

1. **Parsing** encodes the behavior of parsers as relations, which are then
used to prove parser implementation's correctness.
2. **Language syntax** describes expressions and the token sequences that represent them.
3. **Recursive descent** implements the parser combinators and proves their correctness.

Read **Parsing** first, then **Language syntax**; **Recursive descent** builds
on the parser specifications introduced there.
-/
