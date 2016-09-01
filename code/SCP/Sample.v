Section PRED.

  Inductive nat : Set :=
   | O : nat
   | S : nat -> nat.

  Definition pred (n : nat) : {m | n = S m} + {n = O}.
    exact (match n as n' return {m | n' = S m} + {n' = O} with
            | O => inright eq_refl
            | S m => inleft _ (exist _ m eq_refl)
            end).
  Defined.
End PRED.
Extraction Language Haskell.
Extract Inductive sumor => "Maybe" ["Just" "Nothing"].
Recursive Extraction pred.
Print sig.