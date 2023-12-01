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

Set Implicit Arguments.

#[global] Infix "∈" := In (at level 70, no associativity).

#[global] Notation rinv R := (λ x y, R y x).
#[global] Notation "P '⊆₁' Q" := (∀x, P x → Q x) (at level 70, format "P  ⊆₁  Q").

Arguments clos_trans {_}.
Arguments clos_refl_trans {_}.

Theorem list_snoc_rect X (P : list X → Type) :
          P []
       → (∀ l x, P l → P (l++[x]))
       → ∀l, P l.
Proof.
  intros H1 H2 l; revert P H1 H2.
  induction l as [ | x l IHl ]; eauto.
  intros P H1 H2.
  apply IHl with (P := fun l => P (x::l)).
  + apply (H2 []), H1.
  + intros ? ?; apply (H2 (_::_)).
Qed. 

Section closure_t_rt.

  Variables (X : Type).

  Implicit Type (R : X → X → Prop).

  Hint Constructors clos_trans clos_refl_trans : core.

  Local Fact clos_trans_rev' R x y : clos_trans R x y → clos_trans (rinv R) y x.
  Proof. induction 1; eauto. Qed.

  Fact clos_trans_rinv R x y : clos_trans R x y ↔ clos_trans (rinv R) y x.
  Proof. split; now intros ?%clos_trans_rev'. Qed.

  Local Fact clos_refl_trans_rev' R x y : clos_refl_trans R x y → clos_refl_trans (rinv R) y x.
  Proof. induction 1; eauto. Qed.

  Fact clos_refl_trans_rinv R x y : clos_refl_trans R x y ↔ clos_refl_trans (rinv R) y x.
  Proof. split; now intros ?%clos_refl_trans_rev'. Qed.

(*
  Fact clos_refl_trans_clos_trans R x y :
      clos_refl_trans R x y → x = y ∨ clos_trans R x y.
  Proof. induction 1 as [ | | x y z _ [] _ [] ]; subst; eauto. Qed.
*)

  Fact clos_trans_fun R f :
         (∀ x y, R x y → R (f x) (f y))
       → (∀ x y, clos_trans R x y → clos_trans R (f x) (f y)).
  Proof. induction 2; eauto. Qed.

  Fact clos_refl_trans_fun R f :
         (∀ x y, R x y → R (f x) (f y))
       → (∀ x y, clos_refl_trans R x y → clos_refl_trans R (f x) (f y)).
  Proof. induction 2; eauto. Qed.

End closure_t_rt.

#[local] Hint Resolve Acc_intro Acc_inv : core.

Fact Acc_inv_clos_refl_trans X (R : X → X → Prop) x y :
     clos_refl_trans R y x → Acc R x → Acc R y.
Proof. induction 1; eauto. Qed.

Fact Acc_inv_clos_refl_trans_rinv X (R : X → X → Prop) x y :
       clos_refl_trans R x y → Acc (rinv R) x → Acc (rinv R) y.
Proof.
  intros H1%clos_refl_trans_rinv.
  now apply Acc_inv_clos_refl_trans.
Qed.

Section Acc_lex_product_rect.

  Variables (X Y : Type) 
            (R : X → X → Prop) 
            (T : Y → Y → Prop)
            (P : X → Y → Type).

  Hint Resolve Acc_inv Acc_intro : core.

  Section Acc_lex_rect.

    Hypothesis (HP : ∀ x y, 
                     Acc R x 
                   → Acc T y 
                   → (∀ x' y', R x' x → Acc T y' → P x' y')
                   → (∀ y', T y' y → P x y')
                   → P x y).

    Theorem Acc_lex_rect x y : Acc R x → Acc T y → P x y.
    Proof. induction 1 in y |- *; induction 1; eauto. Qed.

  End Acc_lex_rect.

  Section Acc_product_rect.

    Hypothesis (HP : ∀ x y, 
                     Acc R x 
                   → Acc T y 
                   → (∀x', R x' x → P x' y)
                   → (∀y', T y' y → P x y')
                   → P x y).

    Theorem Acc_product_rect x y : Acc R x → Acc T y → P x y.
    Proof. intros Hx; revert Hx y; do 2 induction 1; apply HP; eauto. Qed.

  End Acc_product_rect.

End Acc_lex_product_rect.

Section Acc_rinv_fun_rect.

  Variables (X Y : Type) (R : Y → Y → Prop) (f g : X → Y)
            (P : Y → Type)
            (HP : ∀x, Acc (rinv R) (f x)
                    → (∀x', R (f x) (f x') → P (g x'))
                    → P (g x)).

  Local Lemma Acc_rinv_fun_rect_eq y : Acc (rinv R) y → ∀x, y = f x → P (g x).
  Proof. induction 1; intros ? ->; eauto. Qed.

  Theorem Acc_rinv_fun_rect x : Acc (rinv R) (f x) → P (g x).
  Proof. intros; eapply Acc_rinv_fun_rect_eq; eauto. Qed.

End Acc_rinv_fun_rect.

Section Acc_rinv_lex_fun_rect.

  (** This tailored induction principle is specifically
      designed to establish the following result called
      term_beta_sn_app in beta.v:

           SN a → SN (u⌈a⌉ @ *m) → SN (λ u @* a::m)

      where f and g are instantiated as 
            f a u m := u⌈a⌉ @ *m 
        and g a u m := λ u @* a::m
      and P is just SN := Acc (rinv term_beta) *)

  Variables (X Y Z K : Type) (R : X → X → Prop) (T : K → K → Prop)
            (f g : X → Y → Z → K)
            (P : K → Type)
            (HP : ∀ x y z,
                    Acc (rinv R) x
                  → Acc (rinv T) (f x y z)
                  → (∀ x' y' z', R x x' → Acc (rinv T) (f x' y' z') → P (g x' y' z'))
                  → (∀ y' z', T (f x y z) (f x y' z') → P (g x y' z'))
                  → P (g x y z)).

  Local Lemma Acc_lex_fun_rect_eq x k :
      Acc (rinv R) x → Acc (rinv T) k → ∀ y z, k = f x y z → P (g x y z).
  Proof.
    intros H1 H2; pattern x, k; revert x k H1 H2; apply Acc_lex_rect.
    intros; subst; eauto.
  Qed.

  Theorem Acc_rinv_lex_fun_rect x y z : Acc (rinv R) x → Acc (rinv T) (f x y z) → P (g x y z).
  Proof. intros; eapply Acc_lex_fun_rect_eq; eauto. Qed.

End Acc_rinv_lex_fun_rect.

Section prod_list.

  (** The Acc(essibility) characterization proof mimics the
      one used to show that the M(ulti) S(et) O(rdering) is
      well-founded. By Nipkow and Buchholz *)

  Variables (X : Type).

  Implicit Type (R : X → X → Prop).

  Inductive prod_list R : list X → list X → Prop :=
    | in_prod_list l x y r : R x y → prod_list R (l++x::r) (l++y::r).

  Hint Constructors prod_list : core.

  (* We implement a right inversion lemma for prod_list
     using a custom inversion predicate (called telescope ?) *)

  Inductive prod_list_cons_right R y m : list X → Prop :=
    | in_prod_list_cons_right_0 x : R x y → prod_list_cons_right R y m (x::m)
    | in_prod_list_cons_right_1 l : prod_list R l m → prod_list_cons_right R y m (y::l).

  Hint Constructors prod_list_cons_right : core.

  Local Fact prod_list_right_inv R l m :
          prod_list R l m 
        → match m with
          | []   => False
          | y::m => prod_list_cons_right R y m l
          end.
  Proof. intros [[]]; simpl; eauto. Qed. 

  Lemma prod_list_Acc R l : Forall (Acc R) l → Acc (prod_list R) l.
  Proof. 
    induction 1 as [ | y m Hy _ IHm ].
    + constructor; now intros ? ?%prod_list_right_inv.
    + revert y m Hy IHm; apply Acc_product_rect; intros y m _ _ IHx IHm.
      constructor; intros ? []%prod_list_right_inv; eauto.
  Qed.

End prod_list.
