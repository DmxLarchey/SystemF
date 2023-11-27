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

Require Import utils syntax.

Reserved Notation "x '-β->' y" (at level 70).

Inductive term_beta : term -> term -> Prop :=
  | in_beta_redex u v :         (λ u)@v -β-> u⌈v⌉  
  | in_beta_lft u v w : u -β-> v -> u@w -β-> v@w
  | in_beta_rt  u v w : u -β-> v -> w@u -β-> w@v
  | in_beta_abs u v   : u -β-> v -> λ u -β-> λ v
where  " x '-β->' y " := (@term_beta x y).

#[global] Hint Constructors term_beta : core.

(*
Inductive term_beta_inv_abs u : term -> Prop :=
  | in_term_beta_inv_abs_0 v : u -β-> v -> term_beta_inv_abs u (λ v).

Inductive term_beta_inv_app v : term -> term -> Prop :=
  | in_term_beta_inv_app_0 u u' : u -β-> u' -> term_beta_inv_app v u (u'@v)
  | in_term_beta_inv_app_1 v
*)

Notation "x '-β+>' y" := (clos_trans term_beta x y) (at level 70).
Notation "x '-β*>' y" := (clos_refl_trans term_beta x y) (at level 70).

Fact term_betaplus_abs u v : u -β+> v -> λ u -β+> λ v.
Proof. apply clos_trans_fun; eauto. Qed.

Fact term_betastar_abs u v : u -β*> v -> λ u -β*> λ v.
Proof. apply clos_refl_trans_fun; eauto. Qed.

Fact term_betaplus_lft u v w : u -β+> v -> u@w -β+> v@w.
Proof. apply clos_trans_fun with (f := fun u => u@w); eauto. Qed.

Fact term_betastar_lft u v w : u -β*> v -> u@w -β*> v@w.
Proof. apply clos_refl_trans_fun with (f := fun u => u@w); eauto. Qed.

Fact term_betaplus_rt u v w : v -β+> w -> u@v -β+> u@w.
Proof. apply clos_trans_fun with (f := fun w => u@w); eauto. Qed.

Fact term_betastar_rt u v w : v -β*> w -> u@v -β*> u@w.
Proof. apply clos_refl_trans_fun with (f := fun w => u@w); eauto. Qed.

Fact term_beta_ren u v f : u -β-> v -> syn_ren u f -β-> syn_ren v f.
Proof.
  induction 1 in f |- *; simpl; eauto.
  rewrite syn_ren_replace; constructor.
Qed.

#[local] Hint Resolve term_beta_ren : core.

Fact term_betastar_ren u v f : u -β*> v -> syn_ren u f -β*> syn_ren v f. 
Proof. apply clos_refl_trans_fun with (f := fun u => syn_ren u f); auto. Qed.

Fact term_beta_subst u v f : u -β-> v -> syn_subst u f -β-> syn_subst v f.
Proof.
  induction 1 in f |- *; simpl; eauto.
  rewrite syn_subst_replace; eauto.
Qed.

Fact term_beta_replace u v a : u -β-> v -> u⌈a⌉ -β-> v⌈a⌉.
Proof. apply term_beta_subst. Qed.

#[local] Hint Resolve in_or_app in_eq in_cons : core.

Fact term_subst_betastar u f g :
        (forall x, x ∈ syn_vars u -> f x -β*> g x)
     -> syn_subst u f -β*> syn_subst u g.
Proof.
  induction u as [ x | u IHu v IHv | u IHu ] in f, g |- *; simpl; intros H; eauto.
  + constructor 3 with (syn_subst u f@syn_subst v g).
    * apply term_betastar_rt, IHv; eauto.
    * apply term_betastar_lft, IHu; eauto.
  + apply term_betastar_abs, IHu.
    intros [] ?; simpl.
    * now constructor 2.
    * apply term_betastar_ren; eauto.
Qed.

Fact term_subst_betaplus u f g : 
        (forall x, x ∈ syn_vars u -> f x = g x \/ f x -β-> g x)
     -> syn_subst u f = syn_subst u g \/ syn_subst u f -β+> syn_subst u g.
Proof.
  intros H.
  apply clos_refl_trans_clos_trans, term_subst_betastar.
  intros ? [-> | ]%H.
  + constructor 2.
  + now constructor 1.
Qed.

Fact term_replace_betaplus u a b : a -β-> b -> u⌈a⌉ = u⌈b⌉ \/ u⌈a⌉ -β+> u⌈b⌉.
Proof.
  intros H; apply term_subst_betaplus.
  intros []; simpl; auto.
Qed.

Fact term_beta_inv u w :
    u -β-> w 
 -> match u with
    | £ _  => False
    | λ u  => exists v, w = λ v /\ u -β-> v
    | u@v  => (exists u', w = u'@v /\ u -β-> u')
           \/ (exists v', w = u@v' /\ v -β-> v')
           \/ (exists u', u = λ u' /\ w = u'⌈v⌉) 
    end. 
Proof. intros []; simpl; eauto. Qed.

Fact term_beta_redex_inv f a v :
       λ f @ a -β-> v
    -> v = f⌈a⌉
    \/ (exists g, v = λ g @ a /\ f -β-> g)
    \/ (exists b, v = λ f @ b /\ a -β-> b).
Proof.
  intros [ (? & -> & (g & -> & ?)%term_beta_inv) 
       | [ | (f' & E & ->)] ]%term_beta_inv; eauto.
  inversion E; subst; eauto.
Qed.

#[global] Reserved Notation "f '@*' l" (at level 61, left associativity).
#[global] Reserved Notation "f '*@' l" (at level 61, left associativity).

Fixpoint term_app f l : term :=
  match l with
  | nil  => f
  | x::l => (f@x) @* l
  end
where "f @* l" := (term_app f l).

Fixpoint term_rapp f l : term :=
  match l with
  | nil  => f
  | x::l => (f *@l) @ x
  end
where "f *@ l" := (term_rapp f l).

Fact term_app_comp u l m : u @* (l++m) = u @* l @* m .
Proof. induction l in u |- *; simpl; auto. Qed.

Fact term_rapp_comp u l m : u *@ (l++m) = u *@ m *@ l.
Proof. induction l; simpl; f_equal; auto. Qed.

Fact term_app_rapp u l : u @* l = u *@ (rev l).
Proof.
  induction l as [ | ? l IHl ] in u |- *; simpl; auto.
  now rewrite IHl, term_rapp_comp.
Qed.

Fact term_beta_rapp u v l : u -β-> v -> u *@ l -β-> v *@ l.
Proof. intros; induction l; simpl; eauto. Qed.

Fact term_beta_app u v l : u -β-> v -> u @* l -β-> v @* l.
Proof. rewrite !term_app_rapp; apply term_beta_rapp. Qed.

#[local] Hint Resolve term_beta_app term_beta_rapp : core.

Fact term_betaplus_app u v l : u -β+> v -> u @* l -β+> v @* l.
Proof. apply clos_trans_fun with (f := fun u => u @* l); eauto. Qed.

#[local] Hint Resolve term_beta_app : core.

Fact term_beta_app_middle a l u v r : 
        u -β-> v -> a @* l++u::r -β-> a @* l++v::r.
Proof. intro; rewrite !term_app_comp; simpl; auto. Qed.

Fact term_var_rapp_beta_inv x m u : 
        £x *@ m -β-> u
     -> exists l v w r, m = l++v::r /\ u = £x *@ l++w::r /\ v -β-> w.
Proof.
  induction m as [ | v m IHm ] in u |- *; simpl.
  + intros []%term_beta_inv.
  + intros [ (a & -> & H1) 
         | [ (a & -> & H1)
           | (a & H1 & H2) ]]%term_beta_inv.
    * apply IHm in H1 as (l & u & w & r & -> & -> & H2).
      exists (v::l), u, w, r; auto.
    * exists [], v, a, m; auto.
    * now destruct m.
Qed.

Fact term_var_app_beta_inv x m u : 
        £x @* m -β-> u
     -> exists l v w r, m = l++v::r /\ u = £x @* l++w::r /\ v -β-> w.
Proof.
  rewrite term_app_rapp. 
  intros (l & v & w & r & H1 & H2 & H3)%term_var_rapp_beta_inv.
  apply f_equal with (f := @rev _) in H1.
  rewrite rev_involutive, rev_app_distr in H1.
  simpl in H1; rewrite app_ass in H1; simpl in H1.
  subst; exists (rev r), v, w, (rev l).
  repeat split; auto.
  rewrite term_app_rapp, rev_app_distr.
  now simpl rev; rewrite !rev_involutive, app_ass.
Qed.

Definition term_beta_normal u := forall v, ~ u -β-> v.

Fact term_var_beta_normal x : term_beta_normal (£x).
Proof. now intros v ?%term_beta_inv. Qed.

Definition term_neutral (u : term) :=
  match u with 
  | λ _ => False
  | _   => True
  end.

Fact term_beta_neutral_rapp_inv a u m : 
        term_neutral a
      -> a *@ m -β-> u
      -> (exists a', u = a' *@ m /\ a -β-> a')
      \/ (exists l v w r, m = l++v::r /\ u = a *@ (l++w::r) /\ v -β-> w).
Proof.
  induction m as [ | b m IHm ] in a, u |- *; simpl; intros H1 H2.
  + left; now exists u.
  + apply term_beta_inv in H2
      as [ (u' & -> & H2) 
       | [ (b' & -> & H2)
         | (k  & E & _) ] ].
    * apply IHm in H2
        as [ (a' & -> & ?) | (l & v & w & r & -> & -> & ?)]; auto.
      - left; now exists a'.
      - right; exists (b::l), v, w, r; auto.
    * right; exists [], b, b', m; auto.
    * destruct m; simpl in E; now subst.
Qed.

Fact term_beta_app_inv a b u m : 
          a @* b::m -β-> u
      -> (exists c, u = c @* m /\ a@b -β-> c)
      \/ (exists l v w r, m = l++v::r /\ u = a @* (b::l++w::r) /\ v -β-> w).
Proof.
  intros H; simpl in H.
  rewrite term_app_rapp in H.
  apply term_beta_neutral_rapp_inv in H
    as [ (c & -> & H)
       | (l & v & w & r & E1 & -> & H) ]; simpl; auto.
  + left; exists c; split; auto; now rewrite term_app_rapp.
  + right; exists (rev r), v, w, (rev l); split; [ | split ]; auto.
    * rewrite <- (rev_involutive m), E1, rev_app_distr; simpl; now rewrite app_ass.
    * rewrite term_app_rapp; f_equal.
      rewrite rev_app_distr; simpl; now rewrite app_ass, !rev_involutive.
Qed.

Definition term_beta_sn := Acc (fun u v => term_beta v u).

#[local] Notation SN := term_beta_sn.

Fact term_beta_sn_app_inv u :
       SN u
    -> match u with
       | £ _ => True
       | u@v => SN u /\ SN v
       | λ u => SN u
       end.
Proof.
  induction 1 as [ [ x | u v | u ]  _ IH ]; auto.
  + split.
    * constructor; intros k Hk.
      refine (proj1 (IH (k@v) _)); auto.
    * constructor; intros k Hk.
      refine (proj2 (IH (u@k) _)); auto.
  + constructor; intros k Hk.
    apply (IH (λ k)); eauto.
Qed.

(** This proof DOES NOT require computing the SN height of a and u⌈a⌉@*l 
     which gives a major improvement over the previous version in the 
     coq-terms project, and also depart from the proof in Krivines book *)
#[local] Lemma term_beta_sn_app_rec a b : 
          SN a -> SN b -> forall u l, b = u⌈a⌉@*l -> SN (λ u @* a::l).
Proof.
  intros Ha Hb%Acc_clos_trans; pattern a, b; revert a b Ha Hb.
  apply Acc_lex_rect.
  intros a ? Ha Hm IHa IHb u m ->.

  constructor; intros ? 
        [ (c & -> & [ -> | [ (v & -> & ?) | (b & -> & ?) ] ]%term_beta_redex_inv) 
        | (l & p & q & r & -> & -> & ?) ]%term_beta_app_inv.
  + revert Hm; apply Acc_incl; now constructor 1.
  + (* v⌈a⌉ @* m is smaller than u⌈a⌉ @* m *)
    apply IHb with (2 := eq_refl).
    apply clos_trans_rinv, term_betaplus_app.
    constructor 1.
    now apply term_beta_replace.
  + (* b is smaller than a *) 
    apply IHa with (1 := H) (3 := eq_refl).
    (* either u⌈a⌉ = u⌈b⌉ or
       u⌈b⌉ @* m is smaller than u⌈a⌉ @* m *)
    destruct term_replace_betaplus with (u := u) (1 := H)
      as [ <- | ? ]; auto.
    apply Acc_inv with (1 := Hm).
    apply clos_trans_rinv.
    now apply term_betaplus_app.
  + (* u⌈a⌉ @* l++q::r is smaller than u⌈a⌉ @* l++p::r *)
    apply IHb with (2 := eq_refl).
    constructor 1.
    now apply term_beta_app_middle.
Qed.

Theorem term_beta_sn_app u a l : SN a -> SN (u⌈a⌉@*l) -> SN (λ u @* a::l).
Proof. intros ? H; now apply term_beta_sn_app_rec with (2 := H). Qed.
