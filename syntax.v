(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

Require Import List.

Import ListNotations.

Require Import utils.

Set Implicit Arguments.

Definition scons {X} x (f : nat -> X) n :=
  match n with
  | 0 => x
  | S n => f n
  end.

#[global] Notation "x ∷ f" := (scons x f) (at level 45, right associativity).

Fixpoint list_pred l :=
  match l with
  | [] => []
  | 0::l => list_pred l
  | S n::l => n::list_pred l
  end.

Fact In_list_pred l n : S n ∈ l -> n ∈ list_pred l.
Proof. induction l as [ | [] ]; simpl; intros []; now eauto. Qed.

Fact list_pred_In l n : n ∈ list_pred l -> S n ∈ l.
Proof. induction l as [ | [] ]; simpl; eauto; intros []; eauto. Qed.

#[global] Hint Resolve In_list_pred list_pred_In : core.

Fact In_list_pred_iff l n : n ∈ list_pred l <-> S n ∈ l.
Proof. split; auto. Qed.

#[local] Hint Resolve in_or_app : core.

#[global] Reserved Notation "u ⌈ v ⌉" (at level 50, format "u ⌈ v ⌉").

Section syntax.

  Implicit Type (b : bool).

  Inductive syntax b :=
    | syn_var : nat -> syntax b
    | syn_bin : syntax b -> syntax b -> syntax b
    | syn_abs : syntax b -> syntax b.

  Arguments syn_var {_}.

  Context {b : bool}.

  Implicit Type (A : syntax b).

  Fixpoint syn_vars A :=
    match A with
    | syn_var x => [x]
    | syn_bin u v => syn_vars u ++ syn_vars v
    | syn_abs u => list_pred (syn_vars u)
    end.

  Fixpoint syn_ren A f : syntax b :=
    match A with 
    | syn_var n => syn_var (f n)
    | syn_bin A B => syn_bin (syn_ren A f) (syn_ren B f)
    | syn_abs A => syn_abs (syn_ren A (0∷fun n => S (f n)))
    end.

  Definition syn_lift A := syn_ren A S.

  Fact syn_ren_ext A f g :
        (forall x, x ∈ syn_vars A -> f x = g x)
      -> syn_ren A f = syn_ren A g.
  Proof.
    induction A as [ | | A IHA ] in f, g |- *; 
      simpl; intros Hfg; simpl; f_equal; eauto.
    apply IHA; intros [] ?; simpl; auto.
  Qed.

  Fact syn_ren_id A : syn_ren A (fun x => x) = A.
  Proof. 
    induction A as [ | | A IHA ]; simpl; f_equal; eauto.
    rewrite <- IHA at 2.
    apply syn_ren_ext; now intros [].
  Qed.

  Fact syn_ren_comp A f g : syn_ren (syn_ren A f) g = syn_ren A (fun n => g (f n)).
  Proof.
    induction A as [ | | A IHA ] in f, g |- *;
      simpl; f_equal; auto.
    rewrite IHA.
    apply syn_ren_ext; now intros [].
  Qed.

  Fixpoint syn_subst A f :=
    match A with 
    | syn_var n => f n
    | syn_bin A B => syn_bin (syn_subst A f) (syn_subst B f)
    | syn_abs A => syn_abs (syn_subst A (syn_var 0∷fun n => syn_lift (f n)))
    end.

  Fact syn_subst_ext A f g :
        (forall x, x ∈ syn_vars A -> f x = g x)
      -> syn_subst A f = syn_subst A g.
  Proof.
    induction A as [ | | A IHA ] in f, g |- *;
      simpl; intros Hfg; simpl; f_equal; eauto.
    apply IHA.
    intros [] ?; simpl; f_equal; eauto.
  Qed.

  Fact syn_subst_id A : syn_subst A syn_var = A.
  Proof.
    induction A as [ | | A IHA ]; simpl; f_equal; eauto.
    rewrite <- IHA at 2.
    apply syn_subst_ext; now intros [].
  Qed.

  Fact syn_subst_ren_comp A f g : syn_subst (syn_ren A f) g = syn_subst A (fun n => g (f n)).
  Proof.
    induction A as [ | | A IHA ] in f, g |- *; simpl; f_equal; auto.
    rewrite IHA.
    apply syn_subst_ext; now intros [].
  Qed.

  Fact syn_ren_subst_comp A f g : syn_ren (syn_subst A f) g = syn_subst A (fun n => syn_ren (f n) g).
  Proof.
    induction A as [ | | A IHA ] in f, g |- *; simpl; f_equal; auto.
    rewrite IHA.
    apply syn_subst_ext.
    intros [] _; simpl; auto.
    unfold syn_lift.
    rewrite !syn_ren_comp.
    apply syn_ren_ext; auto.
  Qed.

  Fact syn_subst_comp A f g : syn_subst (syn_subst A f) g = syn_subst A (fun n => syn_subst (f n) g).
  Proof.
    induction A as [ | | A IHA ] in f, g |- *; simpl; f_equal; auto.
    rewrite IHA.
    apply syn_subst_ext.
    intros [] _; simpl; auto.
    unfold syn_lift.
    rewrite syn_subst_ren_comp, syn_ren_subst_comp.
    apply syn_subst_ext; now intros [].
  Qed.

  Fact syn_ren_eq_subst A f : syn_ren A f = syn_subst A (fun x => syn_var (f x)).
  Proof.
    induction A as [ | | A IHA ] in f |- *; simpl; f_equal; eauto.
    rewrite IHA.
    apply syn_subst_ext; now intros [].
  Qed.

  Notation "£" := syn_var.
  Notation "↑" := syn_lift.
  Notation "u ⌈ v ⌉" := (syn_subst u (v∷£)).

  Fact syn_ren_replace A B f : 
       syn_ren (A⌈B⌉) f = (syn_ren A (0∷fun n => S (f n)))⌈syn_ren B f⌉.
  Proof.
    rewrite syn_ren_subst_comp, syn_subst_ren_comp.
    apply syn_subst_ext; now intros [].
  Qed.

  Fact syn_lift_replace A B : ↑A⌈B⌉ = A.
  Proof.
    unfold syn_lift.
    rewrite syn_subst_ren_comp; simpl.
    apply syn_subst_id.
  Qed.

  Fact syn_subst_replace A B f : 
       syn_subst (A⌈B⌉) f = (syn_subst A (£0∷fun n => ↑(f n)))⌈syn_subst B f⌉.
  Proof.
    rewrite !syn_subst_comp.
    apply syn_subst_ext.
    intros [] _; simpl; auto.
    now rewrite syn_lift_replace.
  Qed.

End syntax.

Notation type := (syntax false).
Notation term := (syntax true).

Notation "£" := (@syn_var _).
Notation "↑" := (@syn_lift _).
Notation "u ⌈ v ⌉" := (@syn_subst _ u (v∷£)).
Notation "⇑ Γ" := (fun x => ↑(Γ x)) (at level 1, format "⇑ Γ").

Notation "A ⇨ B" := (@syn_bin _ A B) (at level 60, format "A ⇨ B").
Notation "∀" := (@syn_abs _).

Notation "u @ v" := (@syn_bin _ u v) (at level 50,format "u @ v").
Notation λ := (@syn_abs _).

