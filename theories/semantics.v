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
    intros u Hu%term_var_app_beta_inv.
    induction Hu.
    apply IH; now constructor.
  Qed.

  Hint Resolve N0_inc_N Nsaturated_N : core.

  Local Definition Nadapted P :=
            Nsaturated N
         /\ P ⊆₁ N~>P /\ N~>P ⊆₁ P~>N /\ P~>N ⊆₁ N.

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
      * intros u a l Ha Hl P HP.
        specialize (Hl P HP).
        specialize (IHA (P∷I)).
        destruct IHA as (G1 & G2 & G3); auto.
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
            (forall x, (* x ∈ syn_vars A -> *) Nmodel (I x))
         -> (forall x, type_sem (Γ x) I (f x))
         -> type_sem A I (syn_subst u f).
  Proof.
    induction 1 as [ G x | G u A B H1 IH1 | G u v A B H1 IH1 H2 IH2 | G u A H1 IH1 | G u A B H1 IH1 ];
      simpl; intros I f HI Hf; eauto.
    + intros w Hw.
      refine (proj1 (type_sem_Nmodel B I (fun x Hx => HI x)) _ _ [] _ _); auto.
      * revert Hw; apply type_sem_Nmodel; eauto.
      * simpl.
        rewrite syn_subst_comp.
        apply IH1; eauto.
        intros []; simpl; auto.
        now rewrite syn_lift_replace.
    + apply IH1; auto. 
      apply IH2; auto.
    + intros P HP.
      apply IH1.
      * intros []; simpl; auto.
      * intros x.
        unfold syn_lift.
        apply type_sem_ren; simpl; auto.
    + apply type_sem_replace, IH1; auto.
      apply type_sem_Nmodel; auto.
  Qed.

  (* Strong Normalization for Curry-style system F *)
  Theorem FTJ_beta_sn Γ u A : Γ ⊢ u ∶ A -> term_beta_sn u.
  Proof.
    intros H.
    apply FTJ_adequacy with (I := fun _ => N) (f := £) in H; auto.
    + revert H.
      rewrite syn_subst_id.
      apply type_sem_Nmodel; auto.
    + intros x.
      cut (N0 (£ x)).
      * apply type_sem_Nmodel; auto.
      * now exists x, [].
  Qed.

End semantics.

About FTJ_beta_sn.
Print Assumptions FTJ_beta_sn.
