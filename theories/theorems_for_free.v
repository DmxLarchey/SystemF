Definition and' (A B : Prop) := 
  forall P : Prop, (A -> B -> P) -> P.

Fact and_iff_and' A B : A /\ B <-> and' A B.
Proof.
  split.
  + intros [] P; auto.
  + intros H; apply H; now constructor.
Qed.

Definition or' (A B : Prop) := 
  forall P : Prop, (A -> P) -> (B -> P) -> P.

Fact or_iff_or' A B : A \/ B <-> or' A B.
Proof.
  split.
  + intros [] P; auto.
  + intros H; apply H; now constructor.
Qed.

Definition ex' {X} (P : X -> Prop) := 
  forall Q : Prop, (forall x, P x -> Q) -> Q.

Fact ex_iff_ex' X P : @ex X P <-> ex' P.
Proof.
  split.
  + intros [] ? ?; eauto.
  + intros H; apply H; eauto.
Qed.

Definition sig' {X} (P : X -> Prop) := 
  forall Q, (forall x, P x -> Q) -> Q.

Fact sig_iff_sig' X P : (@sig X P -> sig' P) * (sig' P -> sig P).
Proof.
  split.
  + intros [] ? ?; eauto.
  + intros H; apply H; eauto.
Qed.

Definition sigT' {X} (P : X -> Type) := 
  forall Q, (forall x, P x -> Q) -> Q.

Fact sigT_iff_sigT' X P : (@sigT X P -> sigT' P) * (sigT' P -> sigT P).
Proof.
  split.
  + intros [] ? ?; eauto.
  + intros H; apply H; eauto.
Qed.

Check nat_ind.





Section unary.

  Implicit Type (P : nat -> term -> Prop).

  Fixpoint interp_1 P A { struct A } : term -> Prop :=
    match A with 
    | ty_var n => P n
    | ty_arr A B => fun u => forall v, interp_1 P A v -> interp_1 P B (trm_app u v)
    | ty_abs A => fun u => forall K, interp_1 (K∷P) A u 
    end.

  Theorem soundness Γ t A :
          f_typing Γ t A
       -> forall P, (forall n, interp_1 P (Γ n) (trm_var n)) -> interp_1 P A t.
  Proof.
    induction 1 as [ Γ n | Γ u A B H IH | Γ u v A B H1 IH1 H2 IH2 | Γ u A H IH  | Γ u A B H IH ]; intros P HP; simpl.
    + apply HP.
    + intros v Hv.
      apply IH.

Fixpoint interp2 {X} (r : nat -> X -> X -> Prop) t x y { struct t } :=
  match t with
  | ty_var n => r n x y
  | ty_arr A B => interp2 r A x y -> interp2 r B x y
  | ty_abs A => forall K : X -> X -> Prop, interp2 (K∷r) A x y 
  end.


Section indexed.

  Variable (I : Type) (X : I -> Type).

  Implicit Types (f : nat -> I).

  Fixpoint interp f t : Type :=
    match t with
    | ty_var n => X (f n)
    | ty_arr A B => interp f A -> interp f B
    | ty_abs A => forall i, interp (i∷f) A
    end.

  Theorem soundness Γ u t f :
          f_typing Γ u t
       -> forall n, interp f (Γ n) -> interp u

End indexed.

 

Check interp (fun i => i) (fun _ => Empty_set) id_type.
