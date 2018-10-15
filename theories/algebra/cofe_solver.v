From iris.algebra Require Export ofe.
Set Default Proof Using "Type".

Record solution (F : cFunctor) := Solution {
  solution_car :> ofeT;
  solution_cofe : Cofe solution_car;
  solution_unfold : solution_car -n> F solution_car;
  solution_fold : F solution_car -n> solution_car;
  solution_fold_unfold X : solution_fold (solution_unfold X) ≡ X;
  solution_unfold_fold X : solution_unfold (solution_fold X) ≡ X
}.
Arguments solution_unfold {_} _.
Arguments solution_fold {_} _.
Existing Instance solution_cofe.

Module solver. Section solver.
Context (F : cFunctor) `{Fcontr : cFunctorContractive F}
        `{Fcofe : ∀ T : ofeT, Cofe T → Cofe (F T)} `{Finh : Inhabited (F unitC)}.
Notation map := (cFunctor_map F).

Fixpoint A (k : nat) : ofeT :=
  match k with 0 => unitC | S k => F (A k) end.
Local Instance: ∀ k, Cofe (A k).
Proof using Fcofe. induction 0; apply _. Defined.
Fixpoint f (k : nat) : A k -n> A (S k) :=
  match k with 0 => CofeMor (λ _, inhabitant) | S k => map (g k,f k) end
with g (k : nat) : A (S k) -n> A k :=
  match k with 0 => CofeMor (λ _, ()) | S k => map (f k,g k) end.
Definition f_S k (x : A (S k)) : f (S k) x = map (g k,f k) x := eq_refl.
Definition g_S k (x : A (S (S k))) : g (S k) x = map (f k,g k) x := eq_refl.
Arguments A : simpl never.
Arguments f : simpl never.
Arguments g : simpl never.

Lemma gf {k} (x : A k) : g k (f k x) ≡ x.
Proof using Fcontr.
  induction k as [|k IH]; simpl in *; [by destruct x|].
  rewrite -cFunctor_compose -{2}[x]cFunctor_id. by apply (contractive_proper map).
Qed.
Lemma fg {k} (x : A (S (S k))) : f (S k) (g (S k) x) ≡{k}≡ x.
Proof using Fcontr.
  induction k as [|k IH]; simpl.
  - rewrite f_S g_S -{2}[x]cFunctor_id -cFunctor_compose.
    apply (contractive_0 map).
  - rewrite f_S g_S -{2}[x]cFunctor_id -cFunctor_compose.
    by apply (contractive_S map).
Qed.

Record tower := {
  tower_car k :> A k;
  g_tower k : g k (tower_car (S k)) ≡ tower_car k
}.
Instance tower_equiv : Equiv tower := λ X Y, ∀ k, X k ≡ Y k.
Instance tower_dist : Dist tower := λ n X Y, ∀ k, X k ≡{n}≡ Y k.
Definition tower_ofe_mixin : OfeMixin tower.
Proof.
  split.
  - intros X Y; split; [by intros HXY n k; apply equiv_dist|].
    intros HXY k; apply equiv_dist; intros n; apply HXY.
  - intros k; split.
    + by intros X n.
    + by intros X Y ? n.
    + by intros X Y Z ?? n; trans (Y n).
  - intros k X Y HXY n; apply dist_S.
    by rewrite -(g_tower X) (HXY (S n)) g_tower.
Qed.
Definition T : ofeT := OfeT tower tower_ofe_mixin.

Program Definition tower_chain (c : chain T) (k : nat) : chain (A k) :=
  {| chain_car i := c i k |}.
Next Obligation. intros c k n i ?; apply (chain_cauchy c n); lia. Qed.
Program Definition tower_compl : Compl T := λ c,
  {| tower_car n := compl (tower_chain c n) |}.
Next Obligation.
  intros c k; apply equiv_dist=> n.
  by rewrite (conv_compl n (tower_chain c k))
    (conv_compl n (tower_chain c (S k))) /= (g_tower (c _) k).
Qed.
Global Program Instance tower_cofe : Cofe T := { compl := tower_compl }.
Next Obligation.
  intros n c k; rewrite /= (conv_compl n (tower_chain c k)).
  apply (chain_cauchy c); lia.
Qed.

Fixpoint ff {k} (i : nat) : A k -n> A (i + k) :=
  match i with 0 => cid | S i => f (i + k) ◎ ff i end.
Fixpoint gg {k} (i : nat) : A (i + k) -n> A k :=
  match i with 0 => cid | S i => gg i ◎ g (i + k) end.
Lemma ggff {k i} (x : A k) : gg i (ff i x) ≡ x.
Proof using Fcontr. induction i as [|i IH]; simpl; [done|by rewrite (gf (ff i x)) IH]. Qed.
Lemma f_tower k (X : tower) : f (S k) (X (S k)) ≡{k}≡ X (S (S k)).
Proof using Fcontr. intros. by rewrite -(fg (X (S (S k)))) -(g_tower X). Qed.
Lemma ff_tower k i (X : tower) : ff i (X (S k)) ≡{k}≡ X (i + S k).
Proof using Fcontr.
  intros; induction i as [|i IH]; simpl; [done|].
  by rewrite IH Nat.add_succ_r (dist_le _ _ _ _ (f_tower _ X)); last omega.
Qed.
Lemma gg_tower k i (X : tower) : gg i (X (i + k)) ≡ X k.
Proof. by induction i as [|i IH]; simpl; [done|rewrite g_tower IH]. Qed.

Instance tower_car_ne k : NonExpansive (λ X, tower_car X k).
Proof. by intros X Y HX. Qed.
Definition project (k : nat) : T -n> A k := CofeMor (λ X : T, tower_car X k).

Definition coerce {i j} (H : i = j) : A i -n> A j :=
  eq_rect _ (λ i', A i -n> A i') cid _ H.
Lemma coerce_id {i} (H : i = i) (x : A i) : coerce H x = x.
Proof. unfold coerce. by rewrite (proof_irrel H (eq_refl i)). Qed.
Lemma coerce_proper {i j} (x y : A i) (H1 H2 : i = j) :
  x = y → coerce H1 x = coerce H2 y.
Proof. by destruct H1; rewrite !coerce_id. Qed.
Lemma g_coerce {k j} (H : S k = S j) (x : A (S k)) :
  g j (coerce H x) = coerce (Nat.succ_inj _ _ H) (g k x).
Proof. by assert (k = j) by lia; subst; rewrite !coerce_id. Qed.
Lemma coerce_f {k j} (H : S k = S j) (x : A k) :
  coerce H (f k x) = f j (coerce (Nat.succ_inj _ _ H) x).
Proof. by assert (k = j) by lia; subst; rewrite !coerce_id. Qed.
Lemma gg_gg {k i i1 i2 j} : ∀ (H1: k = i + j) (H2: k = i2 + (i1 + j)) (x: A k),
  gg i (coerce H1 x) = gg i1 (gg i2 (coerce H2 x)).
Proof.
  intros ? -> x. assert (i = i2 + i1) as -> by lia. revert j x H1.
  induction i2 as [|i2 IH]; intros j X H1; simplify_eq/=;
    [by rewrite coerce_id|by rewrite g_coerce IH].
Qed.
Lemma ff_ff {k i i1 i2 j} : ∀ (H1: i + k = j) (H2: i1 + (i2 + k) = j) (x: A k),
  coerce H1 (ff i x) = coerce H2 (ff i1 (ff i2 x)).
Proof.
  intros ? <- x. assert (i = i1 + i2) as -> by lia.
  induction i1 as [|i1 IH]; simplify_eq/=;
    [by rewrite coerce_id|by rewrite coerce_f IH].
Qed.

Definition embed_coerce {k} (i : nat) : A k -n> A i :=
  match le_lt_dec i k with
  | left H => gg (k-i) ◎ coerce (eq_sym (Nat.sub_add _ _ H))
  | right H => coerce (Nat.sub_add k i (Nat.lt_le_incl _ _ H)) ◎ ff (i-k)
  end.
Lemma g_embed_coerce {k i} (x : A k) :
  g i (embed_coerce (S i) x) ≡ embed_coerce i x.
Proof using Fcontr.
  unfold embed_coerce; destruct (le_lt_dec (S i) k), (le_lt_dec i k); simpl.
  - symmetry; by erewrite (@gg_gg _ _ 1 (k - S i)); simpl.
  - exfalso; lia.
  - assert (i = k) by lia; subst.
    rewrite (ff_ff _ (eq_refl (1 + (0 + k)))) /= gf.
    by rewrite (gg_gg _ (eq_refl (0 + (0 + k)))).
  - assert (H : 1 + ((i - k) + k) = S i) by lia.
    rewrite (ff_ff _ H) /= -{2}(gf (ff (i - k) x)) g_coerce.
    by erewrite coerce_proper by done.
Qed.
Program Definition embed (k : nat) (x : A k) : T :=
  {| tower_car n := embed_coerce n x |}.
Next Obligation. intros k x i. apply g_embed_coerce. Qed.
Instance: Params (@embed) 1.
Instance embed_ne k : NonExpansive (embed k).
Proof. by intros n x y Hxy i; rewrite /= Hxy. Qed.
Definition embed' (k : nat) : A k -n> T := CofeMor (embed k).
Lemma embed_f k (x : A k) : embed (S k) (f k x) ≡ embed k x.
Proof.
  rewrite equiv_dist=> n i; rewrite /embed /= /embed_coerce.
  destruct (le_lt_dec i (S k)), (le_lt_dec i k); simpl.
  - assert (H : S k = S (k - i) + (0 + i)) by lia; rewrite (gg_gg _ H) /=.
    by erewrite g_coerce, gf, coerce_proper by done.
  - assert (S k = 0 + (0 + i)) as H by lia.
    rewrite (gg_gg _ H); simplify_eq/=.
    by rewrite (ff_ff _ (eq_refl (1 + (0 + k)))).
  - exfalso; lia.
  - assert (H : (i - S k) + (1 + k) = i) by lia; rewrite (ff_ff _ H) /=.
    by erewrite coerce_proper by done.
Qed.
Lemma embed_tower k (X : T) : embed (S k) (X (S k)) ≡{k}≡ X.
Proof.
  intros i; rewrite /= /embed_coerce.
  destruct (le_lt_dec i (S k)) as [H|H]; simpl.
  - rewrite -(gg_tower i (S k - i) X).
    apply (_ : Proper (_ ==> _) (gg _)); by destruct (eq_sym _).
  - rewrite (ff_tower k (i - S k) X). by destruct (Nat.sub_add _ _ _).
Qed.

Program Definition unfold_chain (X : T) : chain (F T) :=
  {| chain_car n := map (project n,embed' n) (X (S n)) |}.
Next Obligation.
  intros X n i Hi.
  assert (∃ k, i = k + n) as [k ?] by (exists (i - n); lia); subst; clear Hi.
  induction k as [|k IH]; simpl; first done.
  rewrite -IH -(dist_le _ _ _ _ (f_tower (k + n) _)); last lia.
  rewrite f_S -cFunctor_compose.
  by apply (contractive_ne map); split=> Y /=; rewrite ?g_tower ?embed_f.
Qed.
Definition unfold (X : T) : F T := compl (unfold_chain X).
Instance unfold_ne : NonExpansive unfold.
Proof.
  intros n X Y HXY. by rewrite /unfold (conv_compl n (unfold_chain X))
    (conv_compl n (unfold_chain Y)) /= (HXY (S n)).
Qed.

Program Definition fold (X : F T) : T :=
  {| tower_car n := g n (map (embed' n,project n) X) |}.
Next Obligation.
  intros X k. apply (_ : Proper ((≡) ==> (≡)) (g k)).
  rewrite g_S -cFunctor_compose.
  apply (contractive_proper map); split=> Y; [apply embed_f|apply g_tower].
Qed.
Instance fold_ne : NonExpansive fold.
Proof. by intros n X Y HXY k; rewrite /fold /= HXY. Qed.

Theorem result : solution F.
Proof using Type*.
  apply (Solution F T _ (CofeMor unfold) (CofeMor fold)).
  - move=> X /=. rewrite equiv_dist=> n k; rewrite /unfold /fold /=.
    rewrite -g_tower -(gg_tower _ n); apply (_ : Proper (_ ==> _) (g _)).
    trans (map (ff n, gg n) (X (S (n + k)))).
    { rewrite /unfold (conv_compl n (unfold_chain X)).
      rewrite -(chain_cauchy (unfold_chain X) n (S (n + k))) /=; last lia.
      rewrite -(dist_le _ _ _ _ (f_tower (n + k) _)); last lia.
      rewrite f_S -!cFunctor_compose; apply (contractive_ne map); split=> Y.
      + rewrite /embed' /= /embed_coerce.
        destruct (le_lt_dec _ _); simpl; [exfalso; lia|].
        by rewrite (ff_ff _ (eq_refl (S n + (0 + k)))) /= gf.
      + rewrite /embed' /= /embed_coerce.
        destruct (le_lt_dec _ _); simpl; [|exfalso; lia].
        by rewrite (gg_gg _ (eq_refl (0 + (S n + k)))) /= gf. }
    assert (∀ i k (x : A (S i + k)) (H : S i + k = i + S k),
      map (ff i, gg i) x ≡ gg i (coerce H x)) as map_ff_gg.
    { intros i; induction i as [|i IH]; intros k' x H; simpl.
      { by rewrite coerce_id cFunctor_id. }
      rewrite cFunctor_compose g_coerce; apply IH. }
    assert (H: S n + k = n + S k) by lia.
    rewrite (map_ff_gg _ _ _ H).
    apply (_ : Proper (_ ==> _) (gg _)); by destruct H.
  - intros X; rewrite equiv_dist=> n /=.
    rewrite /unfold /= (conv_compl' n (unfold_chain (fold X))) /=.
    rewrite g_S -!cFunctor_compose -{2}[X]cFunctor_id.
    apply (contractive_ne map); split => Y /=.
    + rewrite f_tower. apply dist_S. by rewrite embed_tower.
    + etrans; [apply embed_ne, equiv_dist, g_tower|apply embed_tower].
Qed.
End solver. End solver.
