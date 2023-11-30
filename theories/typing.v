(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Wellfounded Utf8.
Import ListNotations.

From SystemF Require Import utils syntax.

Set Implicit Arguments.

(* Beware the ∶ CHAR below is NOT THE SAME as the semicolumn : CHAR 
   even if they look identical *)
#[global] Reserved Notation "Γ ⊢ u ∶ A" (at level 70).

Inductive F_Typing_Judgement : (nat -> type) -> term -> type -> Prop :=
  | fty_var Γ x :              Γ ⊢ £x ∶ Γ x
  | fty_arr_intro Γ u A B :  A∷Γ ⊢ u ∶ B 
                         ->    Γ ⊢ Ⲗ u ∶ A⇨B
  | fty_arr_elim Γ u v A B :   Γ ⊢ u ∶ A⇨B
                         ->    Γ ⊢ v ∶ A
                         ->    Γ ⊢ u@v ∶ B
  | fty_abs_intro Γ u A :     ⇑Γ ⊢ u ∶ A
                         ->    Γ ⊢ u ∶ ∇A
  | fty_abs_elim Γ u A B :     Γ ⊢ u ∶ ∇A
                         ->    Γ ⊢ u ∶ A⌈B⌉
where "Γ ⊢ u ∶ A" := (F_Typing_Judgement Γ u A).

#[global] Hint Constructors F_Typing_Judgement : core.

Fact FTJ_var Γ n A : Γ n = A -> Γ ⊢ £n ∶ A.
Proof. intros <-; constructor. Qed.

#[global] Hint Resolve FTJ_var : core.

Definition term_id : term := Ⲗ(£0).
Definition type_id : type := ∇(£0⇨£0).

Fact FTJ_id Γ : Γ ⊢ term_id ∶ type_id.
Proof. do 2 constructor; eauto. Qed.

#[local] Hint Resolve in_or_app in_eq in_cons : core.

Fact FTJ_ext Γ Δ u A :
       (forall x, x ∈ syn_vars u -> Γ x = Δ x)
     -> Γ ⊢ u ∶ A
     -> Δ ⊢ u ∶ A.
Proof.
  intros H.
  induction 1 as [ G x | G u A B H1 IH1 | G u v A B H1 IH1 H2 IH2 | G u A H1 IH1 | G u A B H1 IH1 ]
    in Δ, H |- *; simpl in H.
  + apply FTJ_var; symmetry; eauto.
  + constructor.
    apply IH1.
    intros [] ?; simpl; eauto.
  + constructor 3 with A; [ apply IH1 | apply IH2 ];
      intros ? ?; apply H; simpl; eauto.
  + constructor; apply IH1.
    intros x ?; f_equal; auto.
  + constructor; eauto.
Qed.

(* F typing judgements are closed under substituion of types *)
Fact FTJ_type_subst Γ u A f :
          Γ ⊢ u ∶ A
       -> (fun x => syn_subst (Γ x) f) ⊢ u ∶ syn_subst A f.
Proof.
  induction 1 as [ G x | G u A B H1 IH1 | G u v A B H1 IH1 H2 IH2 | G u A H1 IH1 | G u A B H1 IH1 ]
    in f |- *; simpl; eauto.
  + constructor 2; apply FTJ_ext with (2 := IH1 f); now intros [].
  + constructor.
    match goal with 
      |- _ ⊢ _ ∶ syn_subst _ ?f => generalize (IH1 f)
    end.
    apply FTJ_ext.
    intros; unfold syn_lift.
    rewrite syn_subst_ren_comp,
            syn_ren_subst_comp.
    now apply syn_subst_ext.
  + rewrite syn_subst_replace.
    constructor; apply IH1.
Qed.

(* F typing judgements are closed under renaming of types *)
Fact FTJ_type_ren Γ u A f :
          Γ ⊢ u ∶ A
       -> (fun x => syn_ren (Γ x) f) ⊢ u ∶ syn_ren A f.
Proof.
  intros H.
  rewrite syn_ren_eq_subst.
  generalize (FTJ_type_subst (fun x => £ (f x)) H).
  apply FTJ_ext.
  intros; now rewrite syn_ren_eq_subst.
Qed.

(* F typing judgements are closed under renaming of terms *)
Fact FTJ_term_ren Γ Δ A u f :
            Γ ⊢ u ∶ A
         -> (forall x, x ∈ syn_vars u -> Δ (f x) = Γ x)
         -> Δ ⊢ syn_ren u f ∶ A.
Proof.
  intros H; revert H Δ f.
  induction 1 as [ G x | G u A B H1 IH1 | G u v A B H1 IH1 H2 IH2 | G u A H1 IH1 | G u A B H1 IH1 ];
    simpl; intros Δ f H; eauto.
  + constructor.
    apply IH1.
    intros []; simpl; eauto.
  + constructor 3 with A; eauto.
  + constructor; apply IH1.
    intros; f_equal; eauto.
Qed.

(* F typing judgements are closed under substitution of terms *)
Fact FTJ_term_subst Γ Δ C u f :
            Γ ⊢ u ∶ C
         -> (forall x, x ∈ syn_vars u -> Δ ⊢ f x ∶ Γ x)
         -> Δ ⊢ syn_subst u f ∶ C.
Proof.
   intros H; revert H Δ f.
   induction 1 as [ G x | G u A B H1 IH1 | G u v A B H1 IH1 H2 IH2 | G u A H1 IH1 | G u A B H1 IH1 ];
     simpl; intros Δ f H; eauto.
   + constructor 2.
     apply IH1.
     intros [|x] Hx; simpl; eauto.
     apply In_list_pred, H in Hx.
     apply FTJ_term_ren with (1 := Hx); auto.
   + constructor 3 with A; eauto.
   + constructor; apply IH1.
     intros; apply FTJ_type_ren; auto.
Qed.

(* This one does not hold, see below
   Fact FTJ_vars_conclusion Γ C u : Γ ⊢ u ∶ C -> forall x, x ∈ syn_vars C -> exists n, n ∈ syn_vars u /\ x ∈ syn_vars (Γ n).
*)

Fact FTJ_cex_1 : (fun _ => Ⲗ(£0)) ⊢ Ⲗ(£0) ∶ £0⇨£0.
Proof. constructor; constructor 1 with (Γ := £0∷_). Qed.
