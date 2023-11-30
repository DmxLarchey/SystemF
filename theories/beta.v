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

#[local] Hint Resolve in_or_app in_app_or list_pred_mono syn_replace_vars : core.

Fact term_beta_vars u v : u -β-> v -> incl (syn_vars v) (syn_vars u).
Proof. unfold incl; induction 1; simpl; eauto; intros ? []%in_app_or; auto. Qed.

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

Fact term_betastar_vars u v : u -β*> v -> incl (syn_vars v) (syn_vars u).
Proof. unfold incl; induction 1; eauto; now apply term_beta_vars. Qed. 

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

#[local] Hint Resolve term_betastar_lft term_betastar_rt : core.

Fact term_beta_ren u v f : u -β-> v -> syn_ren u f -β-> syn_ren v f.
Proof.
  induction 1 in f |- *; simpl; eauto.
  rewrite syn_ren_replace; constructor.
Qed.

Fact term_beta_lift u v : u -β-> v -> ↑u -β-> ↑v.
Proof. apply term_beta_ren. Qed.

#[local] Hint Resolve term_beta_ren term_beta_lift : core.

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

Local Fact term_beta_ren_inv_rec u v :
        u -β-> v
     -> forall f u', u = syn_ren u' f 
     -> exists v', v = syn_ren v' f /\ u' -β-> v'.
Proof.
  induction 1 as [ u v | u v w _ IH | u v w _ IH | u v _ IH ]; intros f u' E.
  + apply syn_ren_bin_eq_inv in E as (u'' & v' & -> & 
       (u' & -> & ->)%syn_ren_abs_eq_inv & ->).
    exists (u'⌈v'⌉); split; auto.
    rewrite syn_ren_subst_comp, syn_subst_ren_comp.
    apply syn_subst_ext.
    intros []; simpl; auto.
  + apply syn_ren_bin_eq_inv in E as (u'' & w' & -> & -> & ->).
    destruct (IH _ _ eq_refl) as (v' & -> & ?).
    exists (v'@w'); eauto.
  + apply syn_ren_bin_eq_inv in E as (w' & u'' & -> & -> & ->).
    destruct (IH _ _ eq_refl) as (v' & -> & ?).
    exists (w'@v'); eauto.
  + apply syn_ren_abs_eq_inv in E as (u'' & -> & ->).
    destruct (IH _ _ eq_refl) as (v' & -> & ?).
    exists (λ v'); eauto.
Qed.

Fact term_beta_ren_inv u f w :
        syn_ren u f -β-> w
     -> exists v, w = syn_ren v f /\ u -β-> v.
Proof. intros H; apply term_beta_ren_inv_rec with (2 := eq_refl) in H; auto. Qed.

Fact term_beta_lift_inv u w : ↑u -β-> w -> exists v, w = ↑v  /\ u -β-> v.
Proof. apply term_beta_ren_inv. Qed.

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
  | term_beta_redex_shape2 b : a -β-> b -> term_beta_redex_shape f a (λ f @ b).

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

Inductive term_beta_neutral_app_shape a : list term -> term -> Prop :=
  | term_beta_neutral_app_shape0 b m : a -β-> b -> term_beta_neutral_app_shape a m (b @* m)
  | term_beta_neutral_app_shape1 l v w r : v -β-> w -> term_beta_neutral_app_shape a (l++v::r) (a @* l++w::r).

(** This is a key lemma for the results below, by snoc induction on m *)
Lemma term_beta_neutral_app_inv a u m : term_neutral a -> a @* m -β-> u -> term_beta_neutral_app_shape a m u.
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

Fact term_beta_var_app_inv' x m u :
         £x @* m -β-> u
      -> exists l v w r, m = l++v::r /\ u = £x @* l++w::r /\ v -β-> w.
Proof. intros [ l v w r ]%term_beta_var_app_inv; exists l, v, w, r; auto. Qed.

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

Fact term_beta_sn_inv u :
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

Fact term_beta_sn_app_inv a m : SN (a @* m) -> SN a /\ Forall SN m.
Proof.
  induction m as [ | ? ? IHm ] in a |- *; simpl; auto.
  intros [[]%term_beta_sn_inv ]%IHm; eauto.
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

Fact term_beta_sn_subst u f : SN (syn_subst u f) -> SN u.
Proof.
  revert u; apply Acc_rinv_fun_rect; fold SN.
  intros u Hu IHu.
  constructor; intros v Hv.
  now apply IHu, term_beta_subst.
Qed.

Fact term_beta_sn_replace u a : SN (u⌈a⌉) -> SN u.
Proof. apply term_beta_sn_subst. Qed.

Inductive ctx C : Prop :=
  | ctx_intro :(forall a b, a -β-> b -> C⌈a⌉ -β-> C⌈b⌉)
            -> (forall a u, term_neutral a 
                       -> C⌈a⌉ -β-> u 
                       -> (exists b, u = C⌈b⌉ /\ a -β-> b) 
                       \/ (exists D, u = D⌈a⌉ /\ C -β-> D))
            -> (forall D, C -β-> D -> ctx D)
            -> ctx C.

Fact ctx_SN : ctx ⊆₁ SN.
Proof. induction 1; constructor; eauto. Qed.

Theorem term_app_ctx m : Forall SN m -> ctx (£0 @* map ↑ m).
Proof.
  intros H%prod_list_Acc.
  induction H as [ m _ IHm ].
  split.
  + intros a b Hab.
    rewrite !term_app_lift_replace; eauto.
  + intros a u Ha H.
    rewrite term_app_lift_replace in H; simpl in H.
    apply term_beta_neutral_app_inv in H; auto.
    destruct H.
    * left; exists b; split; auto.
      now rewrite term_app_lift_replace.
    * right; exists (£ 0 @* map ↑ (l++w::r)).
      rewrite term_app_lift_replace; split; auto.
      rewrite !map_app; simpl; eauto.
  + intros q (l & v & w & r & (l' & r'' & -> & <- & 
              (a & r' & ? & ? & ?)%map_eq_cons)%map_eq_app & -> & H2)%term_beta_var_app_inv'; subst.
    apply term_beta_lift_inv in H2 as (b & -> & H2).
    specialize (IHm (l'++b::r')).
    rewrite map_app in IHm.
    apply IHm; now constructor.
Qed.

Lemma term_beta_sn_ctx_sig a u (C : sig ctx) :
           SN a
        -> SN ((proj1_sig C)⌈u⌈a⌉⌉) 
        -> SN ((proj1_sig C)⌈λ u@a⌉).
Proof.
  unfold SN; revert a u C.
  apply Acc_rinv_lex_fun_rect
    with (f := fun a u C => (proj1_sig C)⌈u⌈a⌉⌉)
         (g := fun a u C => (proj1_sig C)⌈λ u @ a⌉);
  fold SN;
  intros a u (C & HC) H1 H2 IH1 IH2; simpl in *.
  constructor.
  intros k Hk.
  case HC; intros HC1 HC2 HC3.
  apply HC2 in Hk as [ (b & -> & Hb%term_beta_redex_inv) | (D & -> & HD) ]; simpl; auto.
  + destruct Hb as [ | g Hg | b Hb ]; auto.
    * apply (IH2 _ (exist _ C HC)); simpl.
      apply HC; eauto.
    * apply (IH1 _ _ (exist _ C HC)); simpl; eauto.
  + apply (IH2 _ (exist _ D (HC3 _ HD))); simpl; eauto.
Qed.

Theorem term_beta_sn_ctx a u C : ctx C -> SN a -> SN (C⌈u⌈a⌉⌉) -> SN (C⌈λ u@a⌉).
Proof. intros HC; apply term_beta_sn_ctx_sig with (C := exist _ C HC). Qed.

(* An alternate, more modular proof *)
Lemma term_beta_sn_app' a u m : SN a -> SN (u⌈a⌉ @* m) -> SN (λ u @* a::m).
Proof.
  intros H1 H2.
  replace (λ u @* a::m) with ((£0 @* map ↑ m)⌈λ u @ a⌉).
  + apply term_beta_sn_ctx; auto.
    * apply term_app_ctx.
      now apply term_beta_sn_app_inv in H2.
    * now rewrite term_app_lift_replace.
  + now rewrite term_app_lift_replace.
Qed.
  

