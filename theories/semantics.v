(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List.
Import ListNotations.

From SystemF Require Import utils syntax beta typing.

Set Implicit Arguments.

Section semantics.

  Implicit Types (P Q : term -> Prop).

  Definition sem_arrow P Q t := forall u, P u -> Q (t @ u). 

  Notation " P ~> Q " := (@sem_arrow P Q) (at level 68).

  Fact sem_arrow_mono P P' Q Q' : P' ⊆₁ P -> Q ⊆₁ Q' -> P~>Q ⊆₁ P'~>Q'.
  Proof. intros HP HQ ? Hu ? Ht; apply HQ, Hu, HP, Ht. Qed.

  Notation "P ≡ Q" := (forall u, P u <-> Q u) (at level 70).

  Fact sem_arrow_congr P P' Q Q' : P ≡ P' -> Q ≡ Q' -> P~>Q ≡ P'~>Q'.
  Proof. intros H1 H2 u; split; apply sem_arrow_mono; apply H1 || apply H2. Qed.

  Local Definition N := term_beta_sn.
  
  Local Definition Nsaturated P := forall u a l, N a -> P (u⌈a⌉@*l) -> P ((λ u)@*(a::l)).

  Local Fact Nsaturated_N : Nsaturated N.
  Proof. intros ? ? ?; apply term_beta_sn_app. Qed.

  Local Fact Nsaturated_right P Q : Nsaturated Q -> Nsaturated (P~>Q).
  Proof.
    intros HQ u a l Ha H q Hq.
    change (Q ((λ u)@*(a::l)@*(q::nil))).
    rewrite <- term_app_comp.
    simpl app.
    apply HQ; auto.
    rewrite term_app_comp; simpl.
    apply H, Hq.
  Qed.

  (* Nsaturated is stable under intersections *)
  Local Fact Nsaturated_cap X (Q : X -> Prop) (f : X -> term -> Prop) :
         (forall x, Q x -> Nsaturated (f x))
      -> Nsaturated (fun u => forall x, Q x -> f x u).
  Proof. intros H u a l H1 H2 ? ?; apply H; eauto. Qed. 

  Local Definition N0 u := exists x l, u = £x @* l /\ Forall N l.

  Local Fact N0_N_app u v : N0 u -> N v -> N0 (u@v).
  Proof.
    intros (x & l & -> & H1) H2.
    exists x, (l++[v]); rewrite term_app_snoc; split; eauto.
    apply Forall_app; auto.
  Qed.

  Local Fact N0_inc_N : N0 ⊆₁ N.
  Proof.
    intros v (x & m & -> & H1%prod_list_Acc).
    induction H1 as [ m _ IH ].
    constructor.
    intros u Hu%term_beta_var_app_inv.
    destruct Hu.
    apply IH; now constructor.
  Qed.

  Hint Resolve N0_inc_N Nsaturated_N : core.

  Local Definition Nadapted P :=
            Nsaturated N
         /\ P ⊆₁ N~>P /\ N~>P ⊆₁ P~>N /\ P~>N ⊆₁ N.

  Local Fact Nsaturated_N0 : ~ Nsaturated N0.
  Proof.
    intros C.
    destruct (C (£0) (£0) []) as (x & l & H1 & _); simpl.
    + constructor; intros _ []%term_beta_inv.
    + exists 0, []; auto.
    + simpl in H1.
      destruct l as [ | l a _ ] using list_snoc_rect; try easy.
      rewrite term_app_snoc in H1.
      injection H1; clear H1; intros _ H1.
      destruct l as [ | l ? _ ] using list_snoc_rect; try easy.
      now rewrite term_app_snoc in H1.
  Qed.

  Fact N0_Nadapted : Nadapted N0.
  Proof.
    split; [ | split; [ | split ] ]; auto.
    + intros u (x & l & -> & Hl) p Hp.
      exists x, (l++[p]); rewrite term_app_snoc; split; auto.
      apply Forall_app; auto.
    + apply sem_arrow_mono; auto.
    + intros u Hu.
      cut (N (u@£0)).
      2: apply Hu; now exists 0, [].
      now intros []%term_beta_sn_app_inv.
  Qed.

  Local Definition Nmodel P := Nsaturated P /\ N0 ⊆₁ P /\ P ⊆₁ N.

  Local Fact Nmodel_N : Nmodel N.
  Proof. split; [ | split ]; auto. Qed.

  Hint Resolve Nmodel_N : core.

  Fixpoint type_sem (A : type) (I : nat -> term -> Prop) : term -> Prop :=
    match A with
    | £ x => I x
    | A⇨B => type_sem A I ~> type_sem B I
    | ∀ A => fun u => forall P, Nmodel P -> type_sem A (P∷I) u
    end.

  Hint Resolve in_or_app : core.

  Fact type_sem_ext A I J : 
           (forall x, x ∈ syn_vars A -> I x ≡ J x) 
        -> type_sem A I ≡ type_sem A J. 
  Proof.
    induction A as [ x | A IHA B IHB | A IHA ] in I, J |- *; simpl; intros H u.
    + apply H; simpl; eauto.
    + apply sem_arrow_congr; eauto.
    + split.
      * intros ? P ?; apply IHA with (I := P∷I); eauto.
        intros []; simpl; try tauto.
        intros; now apply H, In_list_pred.
      * intros ? P ?; apply IHA with (J := P∷J); eauto.
        intros []; simpl; try tauto.
        intros; now apply H, In_list_pred.
  Qed.

  Fact type_sem_Nmodel A I : 
         (forall x, x ∈ syn_vars A -> Nmodel (I x)) -> Nmodel (type_sem A I).
  Proof.
    induction A as [ x | A IHA B IHB | A IHA ] in I |- *; simpl; intros H; eauto.
    + split; [ | split ].
      * apply Nsaturated_right, IHB; eauto.
      * intros u Hu v Hv.
        apply IHB; eauto.
        apply N0_N_app; auto.
        revert Hv; apply IHA; eauto.
      * intros u Hu.
        apply N0_Nadapted.
        revert Hu; apply sem_arrow_mono.
        - apply IHA; eauto.
        - apply IHB; eauto.
    + split; [ | split ].
      * apply Nsaturated_cap.
        intros P HP; apply IHA.
        intros [] ?; simpl; auto; now apply H, In_list_pred.
      * intros u Hu P HP.
        apply IHA; auto.
        intros [] ?; simpl; auto; now apply H, In_list_pred.
      * intros u Hu.
        destruct (IHA (N∷I)) as (G1 & G2 & G3); eauto.
        intros [] ?; simpl; auto; now apply H, In_list_pred.
  Qed.

  Fact type_sem_ren A I f : 
         type_sem (syn_ren A f) I ≡ type_sem A (fun x => I (f x)).
  Proof.
    induction A as [ x | A IHA B IHB | A IHA ] in I, f |- *; simpl; intros u; try easy.
    + apply sem_arrow_congr; auto.
    + split.
      * intros H P HP.
        specialize (H P HP).
        rewrite IHA in H.
        revert H; apply type_sem_ext; now intros [].
      * intros H P HP.
        apply IHA.
        specialize (H P HP).
        revert H; apply type_sem_ext; now intros [].
  Qed.

  Fact type_sem_subst A I f : 
         type_sem (syn_subst A f) I ≡ type_sem A (fun x => type_sem (f x) I).
  Proof.
    induction A as [ x | A IHA B IHB | A IHA ] in I, f |- *; simpl; intros u; try easy.
    + apply sem_arrow_congr; auto.
    + split.
      * intros H P HP.
        specialize (H P HP).
        rewrite IHA in H.
        revert H; apply type_sem_ext.
        intros [|x] v Hx; simpl; try tauto.
        unfold syn_lift; rewrite type_sem_ren.
        apply type_sem_ext; now simpl.
      * intros H P HP.
        apply IHA.
        specialize (H P HP).
        revert H; apply type_sem_ext.
        intros [|x] v Hx; simpl; try tauto.
        unfold syn_lift; rewrite type_sem_ren.
        apply type_sem_ext; now simpl.
  Qed.

  Fact type_sem_replace A B I : type_sem (A⌈B⌉) I ≡ type_sem A (type_sem B I∷I).
  Proof.
    intro; rewrite type_sem_subst.
    apply type_sem_ext.
    now intros [].
  Qed.
 
  Theorem FTJ_adequacy Γ u A :
        Γ ⊢ u ∶ A
     -> forall I f,
            (forall x, (* x ∈ syn_vars A \/ x ∈ syn_vars (Γ n) -> *) Nmodel (I x))
         -> (forall n, n ∈ syn_vars u -> type_sem (Γ n) I (f n))
         -> type_sem A I (syn_subst u f).
  Proof.
    induction 1 as [ G x | G u A B H1 IH1 | G u v A B H1 IH1 H2 IH2 | G u A H1 IH1 | G u A B H1 IH1 ];
      simpl; intros I f HI Hf; eauto.
    + intros w Hw.
      refine (proj1 (type_sem_Nmodel B I _) _ _ [] _ _); eauto.
      * revert Hw; apply type_sem_Nmodel; eauto.
      * simpl.
        rewrite syn_subst_comp.
        apply IH1; eauto.
        intros [|n] Hn; simpl; auto.
        rewrite syn_lift_replace; eauto.
    + apply IH1; auto.
      apply IH2; auto.
    + intros P HP.
      apply IH1.
      * intros []; simpl; auto.
      * intros x Hx.
        unfold syn_lift.
        apply type_sem_ren; simpl; auto.
    + apply type_sem_replace, IH1; auto.
      apply type_sem_Nmodel; auto.
  Qed.

  (* Given a statement Γ ⊢ u ∶ A,
      * if all type variables are interpreted by a model
      * if any term n variable (occuring free in u) belongs
        to the model of the type given by (Γ n)
     then u belongs to the model of type A *)

  Theorem FTJ_adequacy' Γ u A I :
           (forall x, Nmodel (I x))
        -> (forall n, n ∈ syn_vars u -> type_sem (Γ n) I (£ n))
        -> Γ ⊢ u ∶ A -> type_sem A I u.
  Proof.
    intros H1 H2 H.
    rewrite <- syn_subst_id.
    now apply (FTJ_adequacy H).
  Qed.

  (* Strong Normalization for Curry-style system F *)
  Theorem FTJ_beta_sn Γ u A : Γ ⊢ u ∶ A -> term_beta_sn u.
  Proof.
    intros H.
    apply FTJ_adequacy' with (I := fun _ => N) in H; auto.
    + revert H; apply type_sem_Nmodel; auto.
    + intros x _.
      cut (N0 (£ x)).
      * apply type_sem_Nmodel; auto.
      * now exists x, [].
  Qed.

  Definition N1 u := N u /\ syn_vars u <> [].

  Fact Nmodel_N1 : Nmodel N1.
  Proof.
    split; [ | split ].
    + intros u a l H1 (H2 & H3); split; eauto.
      contradict H3.
      rewrite term_app_vars in H3 |- *; simpl in H3 |- *.
      generalize (syn_replace_vars u a).
      apply app_eq_nil in H3 as (-> & (-> & ->)%app_eq_nil).
      rewrite <- !app_nil_end.
      destruct (syn_vars (u⌈a⌉)) as [ | n ]; auto.
      intros C; destruct (C n); simpl; auto.
    + intros u Hu; split; auto.
      destruct Hu as (x & l & -> & ?).
      rewrite term_app_vars; now simpl.
    + now intros ? [].
  Qed.

  (* Building the smallest Nmodel, ie type_sem (∀£0) I *)

  (* The smallest model does not contain any closed term *)
  Fact type_sem_bot I : type_sem (∀£0) I ⊆₁ N1.
  Proof.
    intros u; simpl.
    intros H; apply H, Nmodel_N1.
  Qed.

  (* A term of type ∀£0 (bottom) cannot be closed *)
  Theorem FTJ_bot Γ u : Γ ⊢ u ∶ ∀£0 -> syn_vars u <> [].
  Proof.
    intros H.
    apply (@type_sem_bot (fun _ => N)), FTJ_adequacy' with (3 := H); auto.
    intros n _.
    refine (proj1 (proj2 (type_sem_Nmodel _ (fun _ => N) _)) _ _); auto.
    exists n, []; auto.
  Qed.

End semantics.

Check FTJ_beta_sn.
Check FTJ_bot.
