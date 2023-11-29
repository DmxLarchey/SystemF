(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import List Relations Wellfounded.
Import ListNotations.

From SystemF Require Import utils syntax.

Set Implicit Arguments.

#[local] Hint Constructors clos_trans clos_refl_trans : core.

#[global] Reserved Notation "x '-β->' y" (at level 70).
#[global] Reserved Notation "x '-β+>' y" (at level 70).
#[global] Reserved Notation "x '-β*>' y" (at level 70).

Inductive term_beta : term -> term -> Prop :=
  | in_beta_redex u v :         (λ u)@v -β-> u⌈v⌉
  | in_beta_lft u v w : u -β-> v -> u@w -β-> v@w
  | in_beta_rt  u v w : u -β-> v -> w@u -β-> w@v
  | in_beta_abs u v   : u -β-> v -> λ u -β-> λ v
where  "x -β-> y" := (@term_beta x y).

#[global] Hint Constructors term_beta : core.

(*
Inductive term_beta_inv_abs u : term -> Prop :=
  | in_term_beta_inv_abs_0 v : u -β-> v -> term_beta_inv_abs u (λ v).

Inductive term_beta_inv_app v : term -> term -> Prop :=
  | in_term_beta_inv_app_0 u u' : u -β-> u' -> term_beta_inv_app v u (u'@v)
  | in_term_beta_inv_app_1 v
*)

Fact term_beta_app u v l : u -β-> v -> u @* l -β-> v @* l.
Proof.
  intros.
  induction l using list_snoc_rect; auto.
  rewrite !term_app_snoc; auto.
Qed.

#[local] Hint Resolve term_beta_app : core.

Fact term_beta_app_middle a l u v r : u -β-> v -> a @* l++u::r -β-> a @* l++v::r.
Proof. intro; rewrite !term_app_comp; simpl; auto. Qed.

Notation "x -β+> y" := (clos_trans term_beta x y).
Notation "x -β*> y" := (clos_refl_trans term_beta x y).

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

Fact term_betastar_app u v l : u -β*> v -> u @* l -β*> v @* l.
Proof. apply clos_refl_trans_fun with (f := fun u => u @* l); eauto. Qed.

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

Lemma term_betastar_subst u f g :
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

(** Notice that a -β-> b -> u⌈a⌉ -β-> u⌈b⌉
            and a -β+> b -> u⌈a⌉ -β+> u⌈b⌉
    DO NOT HOLD because u might no contain
    any occurence of the variable 0 and hence,
    there would be no reduction because u⌈a⌉ = u⌈b⌉ = u⌈_⌉ *)
Lemma term_betastar_replace u a b : a -β*> b -> u⌈a⌉ -β*> u⌈b⌉.
Proof.
  intro; apply term_betastar_subst.
  intros []; simpl; eauto.
Qed.

(** We study inversions shapes for t -β-> _ *)

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

(*

Inductive term_beta_lam_invt : term -> term -> Prop :=
  | term_beta_lam_invt0 u v : u -β-> v -> term_beta_lam_invt (λ u) (λ v).

Inductive term_beta_app_invt : term -> term -> Prop :=
  | term_beta_app_invt0 u u' v : u -β-> u' -> term_beta_app_invt (u@v) (u'@v)
  | term_beta_app_invt1 u v v' : v -β-> v' -> term_beta_app_invt (u@v) (u@v')
  | term_beta_app_invt2 u v : term_beta_app_invt (λ u@v) (u⌈v⌉)
  .

Fact term_beta_inv' u v :
    u -β-> v 
 -> match u with
    | £ _  => False
    | λ _  => term_beta_lam_invt u v
    | _@_  => term_beta_app_invt u v
    end. 
Proof. intros []; simpl; constructor; auto. Qed.

*)

Inductive term_beta_redex_shape f a : term -> Prop :=
  | term_beta_redex_shape0 : term_beta_redex_shape f a (f⌈a⌉)
  | term_beta_redex_shape1 g : f -β-> g -> term_beta_redex_shape f a (λ g @ a)
  | term_beta_redex_shape2 b : a -β-> b -> term_beta_redex_shape f a (λ f @ b)
  .

Fact term_beta_redex_inv f a v : λ f @ a -β-> v -> term_beta_redex_shape f a v.
Proof.
  intros [ (? & -> & (g & -> & ?)%term_beta_inv) 
       | [ (? & -> & ?) | (f' & E & ->)] ]%term_beta_inv; try constructor; auto.
  inversion E; constructor.
Qed.

(*
Fact term_beta_redex_inv' f a v :
       λ f @ a -β-> v
    -> v = f⌈a⌉
    \/ (exists g, v = λ g @ a /\ f -β-> g)
    \/ (exists b, v = λ f @ b /\ a -β-> b).
Proof.
  intros H%term_beta_redex_inv.
  destruct H; eauto.
Qed.
*)

(** We study the successors of _ @* _ for the following forms
     - £_ @* _
     - _@_ @* _
     - λ_ @* []
     - λ_ @* _::_ *)

Definition term_neutral (u : term) :=
  match u with 
  | λ _ => False
  | _   => True
  end.

Inductive term_beta_neutral_app_invt a : list term -> term -> Prop :=
  | term_beta_neutral_app_invt0 b m : a -β-> b -> term_beta_neutral_app_invt a m (b @* m)
  | term_beta_neutral_app_invt1 l v w r : v -β-> w -> term_beta_neutral_app_invt a (l++v::r) (a @* l++w::r).

(** This is a key lemma for the results below, by snoc induction on m *)
Lemma term_beta_neutral_app_inv a u m : 
        term_neutral a -> a @* m -β-> u -> term_beta_neutral_app_invt a m u.
Proof.
  induction m as [ | m b IHm ] in a, u |- * using list_snoc_rect; intros H1 H2.
  + simpl in H2; constructor 1 with (1:= H2).
  + rewrite term_app_snoc in H2.
    apply term_beta_inv in H2
      as [ (u' & -> & H2%IHm) 
       | [ (b' & -> & H2)
         | (k  & E & _) ] ]; auto.
    * destruct H2 as [ b' m H2 | l v w r H2 ]; rewrite <- term_app_snoc.
      - now constructor 1.
      - rewrite !app_ass; now constructor 2.
    * rewrite <- term_app_snoc.
      now constructor 2 with (r := []). 
    * destruct m using list_snoc_rect; 
        [ simpl in E | rewrite term_app_snoc in E ];
        now subst.
Qed.

Inductive term_beta_var_app_shape x : list term -> term -> Prop :=
  | term_beta_var_app_shape0 l v w r : v -β-> w -> term_beta_var_app_shape x (l++v::r) (£x @* l++w::r).

Fact term_beta_var_app_inv x m u : £x @* m -β-> u -> term_beta_var_app_shape x m u.
Proof.
  intros H%term_beta_neutral_app_inv; simpl; auto.
  destruct H as [ _ _ []%term_beta_inv | ].
  now constructor.
Qed.

Inductive term_beta_ap_app_shape a b : list term -> term -> Prop :=
  | term_beta_ap_app_shape0 m t : a@b -β-> t -> term_beta_ap_app_shape a b m (t @* m)
  | term_beta_ap_app_shape1 l v w r : v -β-> w -> term_beta_ap_app_shape a b (l++v::r) ((a@b) @* l++w::r).

Fact term_beta_ap_app_inv a b m u : (a@b) @* m -β-> u -> term_beta_ap_app_shape a b m u.
Proof.
  intros H%term_beta_neutral_app_inv; simpl; auto.
  destruct H; constructor; auto.
Qed.

Fact term_beta_lam_app0_inv a u : λ a @* [] -β-> u -> exists b, u = λ b @* [] /\ a -β-> b.
Proof. now intros H%term_beta_inv. Qed.

Inductive term_beta_redex_app_shape u a : list term -> term -> Prop :=
  | term_beta_redex_app_shape0 m : term_beta_redex_app_shape u a m (u⌈a⌉ @* m)
  | term_beta_redex_app_shape1 m v : u -β-> v -> term_beta_redex_app_shape u a m (λ v @* a::m)
  | term_beta_redex_app_shape2 m b : a -β-> b -> term_beta_redex_app_shape u a m (λ u @* b::m)
  | term_beta_redex_app_shape3 l v w r : v -β-> w -> term_beta_redex_app_shape u a (l++v::r) (λ u @* a::l++w::r).

Fact term_beta_redex_app_inv u a m t : λ u @* a::m -β-> t -> term_beta_redex_app_shape u a m t.
Proof.
  intros H%term_beta_ap_app_inv.
  destruct H as [ m t H%term_beta_redex_inv | ].
  + destruct H; now constructor.
  + now constructor.
Qed.

(** We study strong normalization *)

Definition term_beta_normal u := forall v, ~ u -β-> v.

Fact term_var_beta_normal x : term_beta_normal (£x).
Proof. now intros ? ?%term_beta_inv. Qed.

Definition term_beta_sn := Acc (fun u v => term_beta v u).

#[local] Notation SN := term_beta_sn.

Fact term_betastar_sn u v : u -β*> v -> SN u -> SN v.
Proof. apply Acc_inv_clos_refl_trans_rinv. Qed.

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

#[local] Hint Resolve
     term_beta_app term_beta_replace 
     term_betastar_sn
       term_betastar_app term_betastar_replace
     term_beta_app_middle : core.

(** This proof DOES NOT require computing the SN height of a and u⌈a⌉@*l 
     which gives a MAJOR SIMPLIFICATION over the previous version in the 
     coq-terms project, and also departs from the proof in Krivine's book *)
Lemma term_beta_sn_app a u m : SN a -> SN (u⌈a⌉ @* m) -> SN (λ u @* a::m).
Proof.
  (** We use the tailored Acc_rinv_lex_fun_rect induction principle *) 
  unfold SN; revert a u m;
  apply Acc_rinv_lex_fun_rect
    with (f := fun a u m => u⌈a⌉ @* m)
         (g := fun a u m => λ u @* a::m);
  fold SN;
  intros a u m H1 H2 IH1 IH2.

  (** Now we can proceed with the proof.
      First the Acc constructor and 
      then case analysis on the
      possible successors of λu @* a::m 
      given by term_beta_redex_app_inv:
        + u⌈a⌉ @* m                  (Hm works)
        + λv @* a::m with u -β-> v   (IH2 works)
        + λu @* b::m with a -β-> b   (IH1 works)
        + λu @* a::m' with m -β-> m'
             at one position in m    (IH2 works)
    *)
  constructor; fold SN; intros ? H%term_beta_redex_app_inv.
  destruct H as [ m | m v Hv | m b Hb | l v w r Hv ].
  + (** SN (u⌈a⌉ @* m) *)
    trivial.
  + (** SN ((λv)@a @* m) *)
    apply IH2.
    (** u -β-> v entails u⌈a⌉ @* m  -β+>  v⌈a⌉ @* m *)
    auto.
  + (** SN ((λu)@b @* m) *)
    apply IH1. 
    * trivial.
    * (** a -β-> b entails u⌈a⌉ @* m  -β*>  u⌈b⌉ @* m *)
      eauto.
  + (** SN (λu @* a::l++w::r) *)
    apply IH2.
    (** v -β-> w entails u⌈a⌉ @* l++v::r  -β->  u⌈a⌉ @* l++w::r *)
    eauto.
Qed.
