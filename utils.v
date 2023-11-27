(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

Require Import List Relations Wellfounded.

Import ListNotations.

Set Implicit Arguments.

#[global] Infix "∈" := In (at level 70, no associativity).

#[global] Notation rinv R := (fun x y => R y x).
#[global] Notation "P '⊆₁' Q" := (forall x, P x -> Q x) (at level 70).

Arguments clos_trans {_}.
Arguments clos_refl_trans {_}.

Section closure_t_rt.

  Variables (X : Type).

  Implicit Type (R : X -> X -> Prop).

  Hint Constructors clos_trans clos_refl_trans : core.

  Local Fact clos_trans_rev' R x y : clos_trans R x y -> clos_trans (rinv R) y x.
  Proof. induction 1; eauto. Qed.

  Fact clos_trans_rinv R x y : clos_trans R x y <-> clos_trans (rinv R) y x.
  Proof. split; now intros ?%clos_trans_rev'. Qed. 

  Fact clos_refl_trans_clos_trans R x y :
      clos_refl_trans R x y -> x = y \/ clos_trans R x y.
  Proof. induction 1 as [ | | x y z _ [] _ [] ]; subst; eauto. Qed.

  Fact clos_trans_fun R f :
         (forall x y, R x y -> R (f x) (f y))
      -> (forall x y, clos_trans R x y -> clos_trans R (f x) (f y)).
  Proof. induction 2; eauto. Qed.

  Fact clos_refl_trans_fun R f :
         (forall x y, R x y -> R (f x) (f y))
      -> (forall x y, clos_refl_trans R x y -> clos_refl_trans R (f x) (f y)).
  Proof. induction 2; eauto. Qed.

End closure_t_rt.

Section Acc_lex_product_rect.

  Variables (X Y : Type) 
            (R : X -> X -> Prop) 
            (T : Y -> Y -> Prop)
            (P : X -> Y -> Type).

  Hint Resolve Acc_inv Acc_intro : core.

  Section Acc_lex_rect.

    Hypothesis (HP : forall x y, 
                      Acc R x 
                   -> Acc T y 
                   -> (forall x' y', R x' x -> Acc T y' -> P x' y')
                   -> (forall y', T y' y -> P x y')
                   -> P x y).

    Theorem Acc_lex_rect x y : Acc R x -> Acc T y -> P x y.
    Proof. induction 1 in y |- *; induction 1; eauto. Qed.

  End Acc_lex_rect.

  Section Acc_product_rect.

    Hypothesis (HP : forall x y, 
                      Acc R x 
                   -> Acc T y 
                   -> (forall x', R x' x -> P x' y)
                   -> (forall y', T y' y -> P x y')
                   -> P x y).

    Theorem Acc_product_rect x y : Acc R x -> Acc T y -> P x y.
    Proof. intros Hx; revert Hx y; do 2 induction 1; apply HP; eauto. Qed.

  End Acc_product_rect.

End Acc_lex_product_rect.

Section prod_list.

  (** The Acc(essibility) characterization proof mimics the
      one used to show that the M(ulti) S(et) O(rdering) is
      well-founded. By Nipkow and Buchholz *)

  Variables (X : Type).

  Implicit Type (R : X -> X -> Prop).

  Inductive prod_list R : list X -> list X -> Prop :=
    | in_prod_list l x y r : R x y -> prod_list R (l++x::r) (l++y::r).

  Notation Π := prod_list.

  Hint Constructors prod_list : core.

  (* We implement a right inversion lemma for prod_list
     using a custom inversion predicate (called telescope ?) *)

  Inductive prod_list_cons_right R y m : list X -> Prop :=
    | in_prod_list_cons_right_0 x : R x y -> prod_list_cons_right R y m (x::m)
    | in_prod_list_cons_right_1 l : Π R l m -> prod_list_cons_right R y m (y::l).

  Hint Constructors prod_list_cons_right : core.

  Local Fact prod_list_right_inv R l m :
          Π R l m 
       -> match m with
          | []   => False
          | y::m => prod_list_cons_right R y m l
          end.
  Proof. intros [[]]; simpl; eauto. Qed. 

  Lemma prod_list_Acc R l : Forall (Acc R) l -> Acc (Π R) l.
  Proof. 
    induction 1 as [ | y m Hy _ IHm ].
    + constructor; now intros ? ?%prod_list_right_inv.
    + revert y m Hy IHm; apply Acc_product_rect; intros y m _ _ IHx IHm.
      constructor; intros ? []%prod_list_right_inv; eauto.
  Qed.

End prod_list.
