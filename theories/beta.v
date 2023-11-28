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

Fact term_betastar_subst u f g :
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

Fact term_betastar_replace u a b : a -β*> b -> u⌈a⌉ -β*> u⌈b⌉.
Proof.
  intro; apply term_betastar_subst.
  intros []; simpl; eauto.
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

Fixpoint term_app f l : term :=
  match l with
  | nil  => f
  | x::l => (f@x) @* l
  end
where "f @* l" := (term_app f l).

Fact term_app_comp u l m : u @* (l++m) = u @* l @* m .
Proof. induction l in u |- *; simpl; auto. Qed.

Fact term_app_snoc u l v : u @* (l++[v]) = (u @* l) @ v.
Proof. now rewrite term_app_comp. Qed.

Fact term_beta_app u v l : u -β-> v -> u @* l -β-> v @* l.
Proof.
  intros.
  induction l using list_snoc_rect; auto.
  rewrite !term_app_snoc; auto.
Qed.

#[local] Hint Resolve term_beta_app : core.

Fact term_betastar_app u v l : u -β*> v -> u @* l -β*> v @* l.
Proof. apply clos_refl_trans_fun with (f := fun u => u @* l); eauto. Qed.

Fact term_beta_app_middle a l u v r : 
        u -β-> v -> a @* l++u::r -β-> a @* l++v::r.
Proof. intro; rewrite !term_app_comp; simpl; auto. Qed.

Fact term_var_app_beta_inv x m u : 
        £x @* m -β-> u
     -> exists l v w r, m = l++v::r /\ u = £x @* l++w::r /\ v -β-> w.
Proof.
  induction m as [ | m v IHm ] in u |- * using list_snoc_rect.
  + intros []%term_beta_inv.
  + rewrite term_app_snoc.
    intros [ (a & -> & H1) 
         | [ (a & -> & H1)
           | (a & H1 & H2) ]]%term_beta_inv.
    * apply IHm in H1 as (l & u & w & r & -> & -> & H2).
      exists l, u, w, (r++[v]); split; [ | split ]; auto.
      - now rewrite app_ass.
      - now rewrite <- term_app_snoc, app_ass.
    * exists m, v, a, []; repeat split; auto.
      now rewrite term_app_snoc.
    * now destruct m using list_snoc_rect; 
        [ | rewrite term_app_snoc in H1 ].
Qed.

Definition term_beta_normal u := forall v, ~ u -β-> v.

Fact term_var_beta_normal x : term_beta_normal (£x).
Proof. now intros v ?%term_beta_inv. Qed.

Definition term_neutral (u : term) :=
  match u with 
  | λ _ => False
  | _   => True
  end.

Fact term_beta_neutral_app_inv a u m : 
        term_neutral a
      -> a @* m -β-> u
      -> (exists a', u = a' @* m /\ a -β-> a')
      \/ (exists l v w r, m = l++v::r /\ u = a @* (l++w::r) /\ v -β-> w).
Proof.
  induction m as [ | m b IHm ] in a, u |- * using list_snoc_rect; intros H1 H2.
  + left; now exists u.
  + rewrite term_app_snoc in H2.
    apply term_beta_inv in H2
      as [ (u' & -> & H2) 
       | [ (b' & -> & H2)
         | (k  & E & _) ] ].
    * apply IHm in H2
        as [ (a' & -> & ?) | (l & v & w & r & -> & -> & ?)]; auto.
      - left; exists a'; now rewrite term_app_snoc.
      - right; exists l, v, w, (r++[b]); repeat split; auto.
        ++ now rewrite app_ass.
        ++ now rewrite <- term_app_snoc, app_ass.
    * right; exists m, b, b', []; repeat split; auto.
      now rewrite term_app_snoc.
    * destruct m using list_snoc_rect; 
        [ simpl in E | rewrite term_app_snoc in E ]; 
        now subst.
Qed.

Fact term_beta_app_inv a b u m : 
          a @* b::m -β-> u
      -> (exists c, u = c @* m /\ a@b -β-> c)
      \/ (exists l v w r, m = l++v::r /\ u = a @* b::l++w::r /\ v -β-> w).
Proof.
  intros H; simpl in H.
  apply term_beta_neutral_app_inv in H
    as [ (? & -> & ?)
       | (? & ? & ? & ? & ? & -> & ?) ]; simpl; eauto.
  right; do 4 eexists; eauto.
Qed.

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

  (** Now we can proceed with the proof with the proper IH
      First the Acc constructor and then case analysis on the
      possible successors of λu @* a::m which are
        + u⌈a⌉ @* m                  (Hm works)
        + λv @* a::m with u -β-> v   (IH2 works)
        + λu @* b::m with a -β-> b   (IH1 works)
        + λu @* a::m' with m -β-> m'
             at one position in m    (IH2 works)
    *)
  constructor; fold SN.
  intros ? 
        [ (c & -> & [ -> | [ (v & -> & ?) | (b & -> & ?) ] ]%term_beta_redex_inv) 
        | (l & p & q & r & -> & -> & ?) ]%term_beta_app_inv.
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
  + (** SN (λu @* a :: l ++ q :: r) *)
    apply IH2.
    (** p -β-> q entails u⌈a⌉ @* l++p::r  -β->  u⌈a⌉ @* l++q::r *)
    eauto.
Qed.
