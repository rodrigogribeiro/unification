Require Import Unify.

Extraction Language Haskell.

Cd "dist".

Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sumor   => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].


Recursive Extraction Library Unify.
