# SystemF
A clean and short proof of strong normalization for Curry-style System F

```
Inductive term_beta : term → term → Prop :=
  | in_beta_redex u v :             (Ⲗu)@v -β-> u⌈v⌉
  | in_beta_lft u v w : u -β-> v   →   u@w -β-> v@w
  | in_beta_rt  u v w : u -β-> v   →   w@u -β-> w@v
  | in_beta_abs u v   : u -β-> v   →    Ⲗu -β-> Ⲗv
where  "x -β-> y" := (term_beta x y).
```

```
Inductive F_Typing_Judgement : (nat → type) → term → type → Prop :=
  | fty_var Γ x :                Γ ⊢ £x ∶ Γ x
  | fty_arr_intro Γ u A B  :   A∷Γ ⊢ u ∶ B 
                           →     Γ ⊢ Ⲗu ∶ A⇨B
  | fty_arr_elim Γ u v A B :     Γ ⊢ u ∶ A⇨B
                           →     Γ ⊢ v ∶ A
                           →     Γ ⊢ u@v ∶ B
  | fty_abs_intro Γ u A    :    ⇑Γ ⊢ u ∶ A
                           →     Γ ⊢ u ∶ ∇A
  | fty_abs_elim Γ u A B   :     Γ ⊢ u ∶ ∇A
                           →     Γ ⊢ u ∶ A⌈B⌉
where "Γ ⊢ u ∶ A" := (F_Typing_Judgement Γ u A).
```

```
Theorem FTJ_beta_sn Γ u A : Γ ⊢ u ∶ A -> SN u.
```

To be able to implement such definitions, some infrastructure
is necessary.
