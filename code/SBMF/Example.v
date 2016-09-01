(* A tiny example of Coq code *)

Section EXAMPLE.
   Variables A B C : Prop.
   Theorem example : (A -> B) -> (B -> C) -> A -> C.
   Proof.
       intros H H' HA. apply H'. apply H. assumption. 
   Qed.

   Definition example' : (A -> B) -> (B -> C) -> A -> C :=
       fun (H : A -> B) (H' : B -> C) (HA : A) => H' (H HA).
   Print example.
End EXAMPLE.
