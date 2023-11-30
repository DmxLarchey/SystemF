(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Utf8.
Import ListNotations.

From SystemF Require Import utils.

Set Implicit Arguments.

Definition scons {X} x (f : nat → X) n :=
  match n with
  | 0 => x
  | S n => f n
  end.

#[global] Notation "x ∷ f" := (scons x f) (at level 45, right associativity).
#[global] Notation "f ⋄ g" := (λ x,f (g x)) (at level 44, left associativity).

#[global] Reserved Notation "u ⟪ f ⟫" (at level 1, left associativity, format "u ⟪ f ⟫").
#[global] Reserved Notation "u ⟬ f ⟭" (at level 1, left associativity, format "u ⟬ f ⟭").
(*#[global] Reserved Notation "'𝓥' u" (at level 2, format "𝓥 u"). *)
#[global] Reserved Notation "u ⌈ v ⌉" (at level 50, format "u ⌈ v ⌉").

Fixpoint list_pred l :=
  match l with
  | []     => []
  | 0::l   => list_pred l
  | S n::l => n::list_pred l
  end.

Fact In_list_pred l n : S n ∈ l → n ∈ list_pred l.
Proof. induction l as [ | [] ]; simpl; intros []; now eauto. Qed.

Fact list_pred_In l n : n ∈ list_pred l → S n ∈ l.
Proof. induction l as [ | [] ]; simpl; eauto; intros []; eauto. Qed.

#[global] Hint Resolve In_list_pred list_pred_In : core.

Fact In_list_pred_iff l n : n ∈ list_pred l ↔ S n ∈ l.
Proof. split; auto. Qed.

Fact list_pred_map_S l : list_pred (map S l) = l.
Proof. induction l; simpl; f_equal; auto. Qed.

Fact list_pred_app l m : list_pred (l++m) = list_pred l ++ list_pred m.
Proof. induction l as [ | [] ]; simpl; f_equal; auto. Qed.

#[local] Hint Resolve in_or_app in_eq in_cons : core.

Fact list_pred_mono l m : incl l m → incl (list_pred l) (list_pred m).
Proof. revert m; induction l as [ | [] ]; intros [ | [] ] ? ?; easy || eauto. Qed.

Section syntax.

  Implicit Type (c : bool).

  Inductive syntax c :=
    | syn_var : nat → syntax c                 (* Variables, binded or not *)
    | syn_bop : syntax c → syntax c → syntax c (* Binary composition operator *)
    | syn_bnd : syntax c → syntax c            (* Nameless de Bruijn binder *)
    .

  Notation "£" := syn_var.
  Infix "⊘" := syn_bop (at level 45).
  Notation Λ := syn_bnd.

  Arguments syn_var {_}.

  Context {c : bool}.

  Implicit Type (u v : syntax c).

  Fixpoint syn_vars u :=
    match u with
    | £ x   => [x]
    | u ⊘ v => syn_vars u ++ syn_vars v
    | Λ u   => list_pred (syn_vars u)
    end.

  Notation 𝓥 := (syn_vars).

  Fixpoint syn_ren u f : syntax c :=
    match u with 
    | £ n   => £ (f n)
    | u ⊘ v => u⟬f⟭ ⊘ v⟬f⟭
    | Λ u   => Λ u⟬0∷S⋄f⟭
    end
  where "u ⟬ f ⟭" := (syn_ren u f).

  Definition syn_lift u := syn_ren u S.

  Notation "↑" := syn_lift. (* x) (at level 1, format "↑ x"). *)

  Fact syn_ren_ext u f g : (∀x, x ∈ 𝓥 u → f x = g x) → u⟬f⟭ = u⟬g⟭.
  Proof.
    induction u as [ | | u IHu ] in f, g |- *; 
      simpl; intros Hfg; simpl; f_equal; eauto.
    apply IHu; intros [] ?; simpl; auto.
  Qed.

  Fact syn_ren_vars u f : 𝓥 u⟬f⟭ = map f (𝓥 u).
  Proof.
    induction u as [ | | u IHu ] in f |- *; simpl; eauto.
    + rewrite map_app; f_equal; auto.
    + rewrite IHu; simpl; clear IHu.
      induction (syn_vars u) as [ | [] ]; simpl; f_equal; eauto.
  Qed.

  Fact syn_lift_vars u : 𝓥 (↑u) = map S (𝓥 u).
  Proof. apply syn_ren_vars. Qed.

  Fact syn_ren_id u : u⟬λ x, x⟭ = u.
  Proof. 
    induction u as [ | | u IHu ]; simpl; f_equal; eauto.
    rewrite <- IHu at 2.
    apply syn_ren_ext; now intros [].
  Qed.

  Fact syn_ren_comp u f g : u⟬f⟭⟬g⟭ = u⟬g⋄f⟭.
  Proof.
    induction u as [ | | u IHu ] in f, g |- *;
      simpl; f_equal; auto.
    rewrite IHu.
    apply syn_ren_ext; now intros [].
  Qed.

  Fixpoint syn_subst u f :=
    match u with 
    | £ n   => f n
    | u ⊘ v => u⟪f⟫ ⊘ v⟪f⟫
    | Λ u   => Λ u⟪£0∷↑⋄f⟫
    end
  where "u ⟪ f ⟫" := (syn_subst u f).

  Fact syn_subst_ext u f g : (∀x, x ∈ 𝓥 u → f x = g x) → u⟪f⟫ = u⟪g⟫.
  Proof.
    induction u as [ | | u IHu ] in f, g |- *;
      simpl; intros Hfg; simpl; f_equal; eauto.
    apply IHu.
    intros [] ?; simpl; f_equal; eauto.
  Qed.

  Fact syn_subst_vars u f : 𝓥 u⟪f⟫ = flat_map (𝓥⋄f) (𝓥 u).
  Proof.
    induction u as [ | | u IHu ] in f |- *; eauto.
    + simpl; now rewrite <- app_nil_end.
    + simpl; rewrite flat_map_app; f_equal; auto.
    + simpl syn_subst; simpl.
      rewrite IHu; simpl; clear IHu.
      induction (syn_vars u) as [ | [] l IH ]; simpl; eauto.
      now rewrite <- IH, syn_lift_vars, list_pred_app, list_pred_map_S.
  Qed.

  Fact syn_subst_id u : u⟪£⟫ = u.
  Proof.
    induction u as [ | | u IHu ]; simpl; f_equal; eauto.
    rewrite <- IHu at 2.
    apply syn_subst_ext; now intros [].
  Qed.

  Fact syn_subst_ren_comp u f g : u⟬f⟭⟪g⟫ = u⟪g⋄f⟫.
  Proof.
    induction u as [ | | u IHu ] in f, g |- *; simpl; f_equal; auto.
    rewrite IHu.
    apply syn_subst_ext; now intros [].
  Qed.

  Fact syn_ren_subst_comp u f g : u⟪f⟫⟬g⟭ = u⟪λ n, (f n)⟬g⟭⟫.
  Proof.
    induction u as [ | | u IHu ] in f, g |- *; simpl; f_equal; auto.
    rewrite IHu.
    apply syn_subst_ext.
    intros [] _; simpl; auto.
    unfold syn_lift.
    rewrite !syn_ren_comp.
    apply syn_ren_ext; auto.
  Qed.

  Fact syn_subst_comp u f g : u⟪f⟫⟪g⟫ = u⟪λ n, (f n)⟪g⟫⟫.
  Proof.
    induction u as [ | | u IHu ] in f, g |- *; simpl; f_equal; auto.
    rewrite IHu.
    apply syn_subst_ext.
    intros [] _; simpl; auto.
    unfold syn_lift.
    rewrite syn_subst_ren_comp, syn_ren_subst_comp.
    apply syn_subst_ext; now intros [].
  Qed.

  Fact syn_ren_eq_subst u f : u⟬f⟭ = u⟪£⋄f⟫.
  Proof.
    induction u as [ | | u IHu ] in f |- *; simpl; f_equal; eauto.
    rewrite IHu.
    apply syn_subst_ext; now intros [].
  Qed.

  Notation "u ⌈ v ⌉" := (u⟪v∷£⟫).

  Fact syn_replace_vars u v x : x ∈ 𝓥 (u⌈v⌉) → x ∈ list_pred (𝓥 u) ++ 𝓥 v.
  Proof.
    rewrite syn_subst_vars.
    intros ([|n] & H1 & H2)%in_flat_map; simpl in H2; eauto.
    destruct H2 as [ -> | [] ]; eauto.
  Qed.

  Fact syn_ren_replace u v f : (u⌈v⌉)⟬f⟭ = u⟬0∷S⋄f⟭⌈v⟬f⟭⌉.
  Proof.
    rewrite syn_ren_subst_comp, syn_subst_ren_comp.
    apply syn_subst_ext; now intros [].
  Qed.

  Fact syn_lift_replace u v : ↑u⌈v⌉ = u.
  Proof.
    unfold syn_lift.
    rewrite syn_subst_ren_comp; simpl.
    apply syn_subst_id.
  Qed.

  Fact syn_subst_replace u v f : (u⌈v⌉)⟪f⟫ = u⟪£0∷↑⋄f⟫⌈v⟪f⟫⌉.
  Proof.
    rewrite !syn_subst_comp.
    apply syn_subst_ext.
    intros [] _; simpl; auto.
    now rewrite syn_lift_replace.
  Qed.

  Fact syn_replace_notfree u v w : ¬ 0 ∈ 𝓥 u → u⌈v⌉ = u⌈w⌉.
  Proof. intro; apply syn_subst_ext; intros [] ?; simpl; tauto. Qed. 

  Fact syn_replace_lift u v : ~ 0 ∈ 𝓥 u → ↑(u⌈v⌉) = u.
  Proof.
    intros H.
    unfold syn_lift.
    rewrite syn_ren_subst_comp.
    rewrite <- syn_subst_id.
    apply syn_subst_ext.
    intros []; simpl; tauto.
  Qed.

  Fact syn_ren_var_eq_inv u f x : £x = u⟬f⟭ → ∃y, u = £y ∧ x = f y.
  Proof. destruct u; simpl; try easy; inversion 1; eauto. Qed.

  Fact syn_ren_bin_eq_inv u f p q : p ⊘ q = u⟬f⟭ → ∃p' q', u = p' ⊘ q' ∧ p = p'⟬f⟭ ∧ q = q'⟬f⟭.
  Proof. destruct u; try easy; simpl; inversion 1; eauto. Qed.

  Fact syn_ren_abs_eq_inv u f v : Λ v = u⟬f⟭ → ∃u', u = Λ u' ∧ v = u'⟬0∷S⋄f⟭.
  Proof. destruct u; try easy; simpl; inversion 1; eauto. Qed.

End syntax.

Notation type := (syntax false).
Notation term := (syntax true).

Notation 𝓥 := (@syn_vars _).

Notation "£" := (@syn_var _).
Notation "↑" := (@syn_lift _).

Notation "u ⟬ f ⟭" := (syn_ren u f).
Notation "u ⟪ f ⟫" := (syn_subst u f).
Notation "u ⌈ v ⌉" := (@syn_subst _ u (v∷£)).
Notation "⇑ Γ" := (fun x => ↑(Γ x)) (at level 1, format "⇑ Γ").

Notation "A ⇨ B" := (@syn_bop _ A B) (at level 60, only parsing).
Notation "∇ A" := (@syn_bnd _ A) (at level 60, only parsing).

Notation "A ⇨ B" := (@syn_bop false A B) (at level 60, format "A ⇨ B", only printing).
Notation "∇ A" := (@syn_bnd false A) (at level 60, format "∇ A", only printing).

Notation "u @ v" := (@syn_bop _ u v) (at level 50, only parsing).
Notation "'Ⲗ' u" := (@syn_bnd _ u) (at level 50, only parsing).

Notation "u @ v" := (@syn_bop true u v) (at level 50, format "u @ v", only printing).
Notation "'Ⲗ' u" := (@syn_bnd true u) (at level 50, format "Ⲗ u", only printing).

#[global] Reserved Notation "f '@*' l" (at level 61, left associativity).

Fixpoint term_app f l : term :=
  match l with
  | []   => f
  | x::l => (f@x) @* l
  end
where "f @* l" := (term_app f l).

Fact term_app_comp u l m : u @* (l++m) = u @* l @* m .
Proof. induction l in u |- *; simpl; auto. Qed.

Fact term_app_snoc u l v : u @* (l++[v]) = (u @* l) @ v.
Proof. now rewrite term_app_comp. Qed.

Fact term_app_vars u l : 𝓥 (u @* l) = flat_map 𝓥 (u::l).
Proof.
  induction l as [ | a l IHl ] in u |- *; simpl.
  + now rewrite <- app_nil_end.
  + rewrite IHl; simpl; now rewrite app_ass.
Qed.

Fact term_app_lift_replace t a l : (t @* map ↑ l)⌈a⌉ = t⌈a⌉ @* l.
Proof.
  induction l as [ | b l IHl ] in t |- *; simpl; auto.
  rewrite IHl; simpl; now rewrite syn_lift_replace.
Qed.
