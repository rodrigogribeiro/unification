Set Implicit Arguments.

Require Import LibTactics.
Require Import Unify.
Require Import Arith.Arith_base.
Require Import List.

Inductive term : Set :=
| var_t   : id -> term
| app_t   : term -> term -> term
| lam_t   : id -> term -> term
| const_t : term.

Definition tyctx : Set := list (id * ty)%type.

Inductive has_type : tyctx -> term -> ty -> Prop :=
| const_ht : forall G, has_type G const_t con
| var_ht : forall v G t, In (v,t) G -> has_type G (var_t v) t
| lam_ht : forall v G tau tau' t, has_type ((v,tau) :: G) t tau' ->
                                  has_type G (lam_t v t) (arr tau tau')
| app_ht : forall G tau tau' l r, has_type G l (arr tau tau') ->
                                  has_type G r tau ->
                                  has_type G (app_t l r) tau'.
Record tc_state := mkState {
                       next_tvar   : id ;
                       used_vars   : list id ;
                       constraints : list (ty * ty)%type
                   }.

Definition TcM (A : Type) := tc_state -> option (tc_state * A)%type.

Definition ret (A : Type)(x : A) : TcM A := fun s => Some (s,x).

Definition bind (A B : Type)(c : TcM A) (c' : A -> TcM B) : TcM B :=
  fun s =>
    match c s with
    | None => None
    | Some (s',v) => c' v s'            
    end.

Notation "x <- c1 ; c2" := (bind c1 (fun x => c2)) 
                           (right associativity, at level 84, c1 at next level).

Definition failT (A : Type) : TcM A := fun s => None.

Definition fresh : TcM ty :=
  fun s => match s with
             mkState n ts cs => Some (mkState (1 + n) (ts ++ (n :: nil)) cs, var n)
           end.

Definition add_constr (t t' : ty) : TcM unit :=
  fun s => match s with
             | mkState n ts cs => Some (mkState n ts ((t,t') :: cs) , tt)
           end.

Fixpoint look (x : id)(G : tyctx) : TcM ty :=
  match G with
  | nil => failT _
  | (y,t) :: G' => if eq_id_dec x y then ret t else look x G'              
  end.

Fixpoint wf_tyctx (D : varctxt)(G : tyctx) : Prop :=
  match G with
  | nil => True
  | (x,t) :: G' => wf_ty D t /\ wf_tyctx D G'
  end.

Lemma wf_tyctx_weaken (D D1 : varctxt)(G : tyctx) : wf_tyctx D G -> wf_tyctx (D ++ D1) G.
Proof.
  induction G ; auto ; mysimp ; intros ; mysimp.
Qed.

Hint Resolve wf_tyctx_weaken.

Lemma wf_constr_weaken D1 cs : wf_constr_list D1 cs -> forall D2, wf_constr_list (D1 ++ D2) cs.
Proof.
  induction cs ; auto ; mysimp ; destruct a ; intros ; mysimp.
Qed.

Hint Resolve wf_constr_weaken.


Lemma member_end : forall D x, member (D ++ x::nil) x.
Proof.  
  induction D ; intros ; mysimp.
Qed.

Hint Resolve member_end.

Lemma member_id : forall x D1 D2, member ((D1 ++ x::nil)++D2) x.
Proof.  
  induction D1 ; intros ; mysimp.
Qed.

Hint Resolve member_id.

Fixpoint gen_constr (G : tyctx)(t : term) : TcM ty :=
  match t with
  | const_t => ret con
  | var_t v => look v G
  | app_t l r =>
    t1 <- gen_constr G l ;
    t2 <- gen_constr G r ;
    t <- fresh ;
    _ <- add_constr t1 (arr t2 t) ;
    ret t
  | lam_t v t =>
    t1 <- fresh ;
    t2 <- gen_constr ((v,t1) :: G) t ;
    ret (arr t1 t2)  
  end.


Ltac gen_constr_tac :=
  repeat subst ; unfold bind, fresh, ret, failT in * ; 
    match goal with 
      | [ IH : forall _ _ _ _, gen_constr _ ?e _ = _ -> _, 
           H : context[gen_constr ?G ?e ?s] |- _ ] => 
           generalize (IH G s) ; clear IH ; 
             destruct (gen_constr G e s) ; intros ; try congruence 
      | [ p : (_ * _)%type |- _ ] => destruct p
      | [ H : forall _ _, Some _ = Some _ -> _ |- _ ] => 
        generalize (H _ _ (refl_equal _)) ; clear H ; intro H 
      | [ s : tc_state |- _ ] => destruct s ; simpl in * 
      | [ H : exists _, _ |- _ ] => destruct H ; simpl in * 
      | [ H : Some _ = Some _ |- _] => inversion H ; clear H ; subst
      | [ H1 : wf_tyctx ?D1 ?G,
          H2 : wf_constr_list (?D1 ++ ?D2) ?cs,
          H3 : wf_tyctx (?D1 ++ ?D2) ?G -> wf_constr_list (?D1 ++ ?D2) ?cs -> _ |- _] =>
          generalize (H3 (wf_constr_list _ _ _ H1) H2) ; clear H3 ; intros ; mysimp ; subst ;
            simpl ; repeat rewrite app_ass ; eauto
      | [ H1 : wf_tyctx ?D ?G, 
          H2 : wf_constr_list ?D ?cs,
          H3 : wf_tyctx ?D ?G -> wf_constr_list ?D ?cs -> _ |- _ ] => 
          generalize (H3 H1 H2) ; clear H3 ; intros ; mysimp ; subst ; eauto
      | [ H : _ -> _ -> ?P |- _ ] => 
        assert P; [ eapply H | idtac ] ; mysimp ; subst ; eauto ;
          [ eapply wf_constr_weaken ; auto | rewrite app_ass ; eauto ] ; fail
      | [ |- exists _, ?p :: ?x1 ++ ?x ++ ?s = _ ++ ?s ] => 
        exists (p :: x1 ++ x) ; simpl ; rewrite app_ass ; eauto
      | [ H : context[eq_id_dec ?v1 ?v2] |- _ ] => destruct* (eq_id_dec v1 v2) 
      | [ H : None = Some _ |- _ ] => congruence
      | [ H : _ /\ _ |- _ ] => destruct H
    end.

Lemma gen_constr_wf : forall e G s1 s2 t,
    gen_constr G e s1 = Some (s2, t) ->
    wf_tyctx (used_vars s1) G ->
    wf_constr_list (used_vars s1) (constraints s1) ->
    (exists D2, (used_vars s2) = (used_vars s1) ++ D2) /\
    (exists c2, (constraints s2) = c2 ++ (constraints s1)) /\
    wf_constr_list (used_vars s2) (constraints s2) /\
    wf_ty (used_vars s2) t.
Proof.
  induction e ; simpl ; intros ; gen_constr_tac ;
    match goal with 
    | [ H : look _ ?G _ = _ |- _ ] => 
       induction G ; simpl in * ; unfold failT in * ; try congruence ;
         repeat gen_constr_tac ; [ repeat split ; auto ; try (exists nil ; auto ; 
           rewrite <- app_nil_end ; auto) ; auto
           | apply IHG ; tauto]
    | _ => idtac
  end ; repeat gen_constr_tac ; mysimp ;
      try solve [ try exists (@nil id) ;
                  try exists (@nil (ty * ty)%type) ;
                             auto ; try rewrite <- app_nil_end ; auto ].
  eapply wf_tyctx_weaken in H0.
  eapply H3 in H0 ; gen_constr_tac.
  destruct H0. destruct H2. destruct H. rewrite H.
  do 2 rewrite <- app_assoc. eexists ; eauto.
  eapply wf_tyctx_weaken in H0.
  eapply H3 in H0 ; gen_constr_tac.
  destruct H0. destruct H2. destruct H0. rewrite H0.
  exists (((t1, arr t3 (var next_tvar0)) :: x1) ++ x). rewrite <- app_assoc. auto.
  eapply wf_tyctx_weaken in H0.
  eapply H3 in H0 ; gen_constr_tac.
  destruct H0. destruct H2. destruct H0. destruct H. rewrite H.
  do 2 eapply wf_ty_weaken ; auto.
  eapply wf_tyctx_weaken in H0. eapply (H3 H0) in H4.
  destruct H4. destruct H2. destruct H4. eapply wf_ty_weaken ; eauto.
  eapply wf_tyctx_weaken in H0. eapply (H3 H0) in H4.
  destruct H4. destruct H2. destruct H4. eapply wf_constr_weaken ; eauto.
  destruct H2. splits*. eapply wf_constr_weaken ; eauto.
  destruct H. rewrite H. rewrite <- app_assoc. eexists ; eauto.
  destruct H2. splits*. eapply wf_constr_weaken ; eauto.
  destruct H2. destruct H2. rewrite H2. eexists ; eauto.
  destruct H2. splits*. eapply wf_constr_weaken ; eauto.
  destruct H2. destruct H3. eauto.
  destruct H2. splits*. eapply wf_constr_weaken ; eauto.
  destruct H2. destruct H. rewrite H. apply member_id.
  destruct H2. splits*. eapply wf_constr_weaken ; eauto.
  destruct H2. destruct H3. auto.
Qed.


Ltac tc_simp := 
  match goal with 
    | [ s : tc_state |- _ ] => destruct s ; simpl in *
    | [ H : (_ * _)%type |- _ ] => destruct H
    | [ IH : forall _ _ _ _, gen_constr _ ?e _ = _ -> _,
      H: context[gen_constr ?G ?e ?s] |- _] => 
    generalize (IH G s) ; clear IH ; destruct (gen_constr G e s) ; try 
      congruence
    | [ H : forall _ _, Some _ = Some _ -> _ |- _ ] => generalize (H _ _ (refl_equal _)) ;
      clear H ; intro H
  end.

Lemma gen_constr_extends : forall e G s1 s2 t,
    gen_constr G e s1 = Some (s2, t) ->
    exists cs2, (constraints s2) = cs2 ++ (constraints s1).
Proof.
  induction e ; simpl ; intros ; unfold ret, bind, failT in * ;
    mysimp ; substs* ;
      match goal with
      | [H : look _ ?G _ = _ |- _] =>
        exists (@nil (ty * ty)%type) ; simpl ; induction G ;
          simpl in * ; unfold failT, ret in *; try congruence ;
            mysimp
      | _ => idtac
      end ; repeat tc_simp ; mysimp ; intros ; repeat tc_simp ;
        mysimp ; simpl in * ; substs ; eauto ;
          try solve [ exists (@nil (ty * ty)) ; auto ] ;
          try solve [ exists ((t1, arr t2 (var next_tvar3)) :: x ++ x0) ;
                     rewrite app_assoc ; auto ]. 
Qed.

Definition type_infer (e:term) : option ty :=
      let x := gen_constr nil e (mkState 0 nil nil) in 
      match x as x' return (x = x') -> option ty with 
         | None => fun _ => None
         | Some (mkState _ D cs, t) => 
            fun H => 
              match unify (existT _ D cs)
                          (proj1 (proj2 (proj2 (gen_constr_wf _ _ _ H I I))))  with 
                | inleft _ (exist _ s _) => Some (apply_subst s t)
                | inright _ => None
              end
      end (refl_equal x).

Lemma gen_only_add : forall s c1 c2,
                  (forall t1 t2, In (t1,t2) (c2 ++ c1) -> apply_subst s t1 = apply_subst s t2) -> 
                  (forall t1 t2, In (t1,t2) c1 -> apply_subst s t1 = apply_subst s t2).
Proof.
  induction c2 ; auto ; mysimp.
Qed.


Fixpoint apply_ctx (s : substitution) (G : tyctx) : tyctx := 
  match G with 
    | nil => nil
    | (x,t)::rest => (x, apply_subst s t)::(apply_ctx s rest)
  end.

Lemma has_type_subst : forall s G e t, has_type G e t ->
                                       has_type (apply_ctx s G) e (apply_subst s t).
Proof.
  induction 1 ; intros ; try rewrite apply_subst_con in * ;
    try rewrite apply_subst_app ; econstructor ;
      try (rewrite <- apply_subst_app) ; eauto.
  induction G ; simpl in * ; mysimp.
Qed.

Hint Resolve has_type_subst.

Lemma apply_ctx_compose G s2 s1 : apply_ctx (s1++s2) G = apply_ctx s2 (apply_ctx s1 G).
Proof.  
  induction G ; mysimp ; intros ; rewrite apply_subst_append ; rewrite IHG ; auto.
Qed.

Lemma has_type_apply_ctx G e t s1 s2 :
         has_type (apply_ctx s1 G) e (apply_subst s1 t) ->
         has_type (apply_ctx (s1 ++ s2) G) e (apply_subst (s1 ++ s2) t).
Proof.
  intros ; try rewrite apply_ctx_compose ; try rewrite apply_subst_append ;
    eapply has_type_subst ; eauto.
Qed.

Lemma member_remove : forall C i, ~ Unify.member (Unify.remove i C) i.
Proof.
  intros C i H ;
  induction C ; simpl in * ; try contradiction ; mysimp ; simpl in * ; mysimp.
Qed.

Hint Resolve member_remove.

Lemma member_remove_var : forall x y D, x <> y ->
                                        Unify.member (Unify.remove x D) y = Unify.member D y.
Proof.  
  induction D ; mysimp.
Qed.

Lemma apply_subst_idem t D s : wf_ty (minus D (dom s)) t -> apply_subst s t = t.
Proof.
  induction t ; simpl in * ; intros. induction s ; try destruct a ; simpl in * ; auto.
  destruct (eq_id_dec i0 i) ; substs*. apply member_remove in H ; try contradiction.
  apply IHs. rewrite member_remove_var in * ; auto.
  rewrite apply_subst_app ; mysimp. rewrite (IHt1 H) ; rewrite (IHt2 H0) ; auto.
  rewrite apply_subst_con ; auto.
Qed.

Lemma ti_correct : forall e G s1 s2 t,
   gen_constr G e s1 = Some (s2,t) ->
   forall s, (forall t1 t2, In (t1,t2) (constraints s2) -> apply_subst s t1 = apply_subst s t2) ->
             has_type (apply_ctx s G) e (apply_subst s t).
Proof.
  induction e ; simpl ; intros ; unfold bind, fresh, add_constr, ret, failT in * ; 
    mysimp ; subst ;
  repeat match goal with 
    | [ |- has_type _  (var_t _) _ ] => 
      constructor ; induction G ; simpl in * ; unfold ret, failT in * ; mysimp
    | [ |- has_type _ const_t _ ] => rewrite apply_subst_con ; constructor
    | [ |- has_type _ (lam_t _ _) _ ] => 
      repeat (repeat tc_simp ; intros ; mysimp ; subst) ; 
            rewrite apply_subst_app ; econstructor ; eauto
    | [ H : context[gen_constr ?G ?e1 ?s1] |- _] => 
      generalize (gen_constr_extends e1 G s1) ; tc_simp ; tc_simp ; tc_simp ; tc_simp
    | _ => intros ; repeat (repeat tc_simp ; intros ; mysimp ; simpl in * ; subst)
         end ;
  match goal with 
    | [ H1 : forall _, _ -> has_type _ ?e1 (apply_subst _ ?t0), 
        H2 : forall _, _ -> has_type _ ?e2 (apply_subst _ ?t1),
        H0 : forall _ _, _ -> apply_subst _ _ = apply_subst _ _ |- 
          has_type _ (app_t ?e1 ?e2) (apply_subst ?s ?t) ] => 
    econstructor ; [ idtac | eauto ] ; 
      rewrite <- apply_subst_app
  end. assert (H : apply_subst s t1 = apply_subst s (Unify.arr t2 (var next_tvar3))).
  apply H0. tauto. rewrite <- H. eapply H3. eapply gen_only_add. intros. eapply H0.
  right ; eauto.
Qed.

Lemma unify_eq : forall cs s t t', unifier cs s ->
                                   In (t,t') cs -> apply_subst s t = apply_subst s t'.
Proof.
  induction cs ; intros ; try contradiction ; simpl in * ; mysimp.
  destruct* a. inverts* H0. destruct* a.
Qed.

Hint Resolve unify_eq.
  
Theorem type_infer_sound : forall e t, type_infer e = Some t -> has_type nil e t.
Proof.
  unfold type_infer.
  intros e t.
  generalize (gen_constr_wf e nil (mkState 0 nil nil)).
  generalize (ti_correct e nil (mkState 0 nil nil)).
  destruct (gen_constr nil e (mkState 0 nil nil)) ; intros ; mysimp.
  repeat tc_simp.
  generalize (a _ _ (refl_equal _) I I). intros. mysimp. simpl in *. subst.
  match goal with
  | [H : context[match ?E with _ => _ end] |- _] => destruct E ; try congruence
  end. destruct s ; mysimp.
Qed.

Extraction Language Haskell.
Extract Inductive sumbool => "Prelude.Bool" ["Prelude.False"  "Prelude.True"].
Extract Inductive option => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].
Extract Inductive sumor => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].
Extract Inductive prod => "(,)"  [ "(,)" ].
Extract Inductive unit => "()" [ "()" ].
Extract Inductive sigT => "(,)" ["(,)"].
Extraction "./infer/src/TypeInfer.hs" type_infer.