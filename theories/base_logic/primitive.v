From iris.base_logic Require Export upred.
From stdpp Require Import finite.
From iris.algebra Require Export updates.
Set Default Proof Using "Type".
Local Hint Extern 1 (_ ≼ _) => etrans; [eassumption|].
Local Hint Extern 1 (_ ≼ _) => etrans; [|eassumption].
Local Hint Extern 10 (_ ≤ _) => omega.

(** logical connectives *)
Program Definition uPred_pure_def {M} (φ : Prop) : uPred M :=
  {| uPred_holds n x := φ |}.
Solve Obligations with done.
Definition uPred_pure_aux : seal (@uPred_pure_def). by eexists. Qed.
Definition uPred_pure {M} := unseal uPred_pure_aux M.
Definition uPred_pure_eq :
  @uPred_pure = @uPred_pure_def := seal_eq uPred_pure_aux.

Instance uPred_inhabited M : Inhabited (uPred M) := populate (uPred_pure True).

Program Definition uPred_and_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := P n x ∧ Q n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Definition uPred_and_aux : seal (@uPred_and_def). by eexists. Qed.
Definition uPred_and {M} := unseal uPred_and_aux M.
Definition uPred_and_eq: @uPred_and = @uPred_and_def := seal_eq uPred_and_aux.

Program Definition uPred_or_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := P n x ∨ Q n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Definition uPred_or_aux : seal (@uPred_or_def). by eexists. Qed.
Definition uPred_or {M} := unseal uPred_or_aux M.
Definition uPred_or_eq: @uPred_or = @uPred_or_def := seal_eq uPred_or_aux.

Program Definition uPred_impl_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ n' x',
       x ≼ x' → n' ≤ n → ✓{n'} x' → P n' x' → Q n' x' |}.
Next Obligation.
  intros M P Q n1 n1' x1 x1' HPQ [x2 Hx1'] Hn1 n2 x3 [x4 Hx3] ?; simpl in *.
  rewrite Hx3 (dist_le _ _ _ _ Hx1'); auto. intros ??.
  eapply HPQ; auto. exists (x2 ⋅ x4); by rewrite assoc.
Qed.
Definition uPred_impl_aux : seal (@uPred_impl_def). by eexists. Qed.
Definition uPred_impl {M} := unseal uPred_impl_aux M.
Definition uPred_impl_eq :
  @uPred_impl = @uPred_impl_def := seal_eq uPred_impl_aux.

Program Definition uPred_forall_def {M A} (Ψ : A → uPred M) : uPred M :=
  {| uPred_holds n x := ∀ a, Ψ a n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Definition uPred_forall_aux : seal (@uPred_forall_def). by eexists. Qed.
Definition uPred_forall {M A} := unseal uPred_forall_aux M A.
Definition uPred_forall_eq :
  @uPred_forall = @uPred_forall_def := seal_eq uPred_forall_aux.

Program Definition uPred_exist_def {M A} (Ψ : A → uPred M) : uPred M :=
  {| uPred_holds n x := ∃ a, Ψ a n x |}.
Solve Obligations with naive_solver eauto 2 with uPred_def.
Definition uPred_exist_aux : seal (@uPred_exist_def). by eexists. Qed.
Definition uPred_exist {M A} := unseal uPred_exist_aux M A.
Definition uPred_exist_eq: @uPred_exist = @uPred_exist_def := seal_eq uPred_exist_aux.

Program Definition uPred_internal_eq_def {M} {A : ofeT} (a1 a2 : A) : uPred M :=
  {| uPred_holds n x := a1 ≡{n}≡ a2 |}.
Solve Obligations with naive_solver eauto 2 using (dist_le (A:=A)).
Definition uPred_internal_eq_aux : seal (@uPred_internal_eq_def). by eexists. Qed.
Definition uPred_internal_eq {M A} := unseal uPred_internal_eq_aux M A.
Definition uPred_internal_eq_eq:
  @uPred_internal_eq = @uPred_internal_eq_def := seal_eq uPred_internal_eq_aux.

Program Definition uPred_sep_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∃ x1 x2, x ≡{n}≡ x1 ⋅ x2 ∧ P n x1 ∧ Q n x2 |}.
Next Obligation.
  intros M P Q n1 n2 x y (x1&x2&Hx&?&?) [z Hy] Hn.
  exists x1, (x2 ⋅ z); split_and?; eauto using uPred_mono, cmra_includedN_l.
  eapply dist_le, Hn. by rewrite Hy Hx assoc.
Qed.
Definition uPred_sep_aux : seal (@uPred_sep_def). by eexists. Qed.
Definition uPred_sep {M} := unseal uPred_sep_aux M.
Definition uPred_sep_eq: @uPred_sep = @uPred_sep_def := seal_eq uPred_sep_aux.

Program Definition uPred_wand_def {M} (P Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ n' x',
       n' ≤ n → ✓{n'} (x ⋅ x') → P n' x' → Q n' (x ⋅ x') |}.
Next Obligation.
  intros M P Q n1 n1' x1 x1' HPQ ? Hn n3 x3 ???; simpl in *.
  eapply uPred_mono with n3 (x1 ⋅ x3);
    eauto using cmra_validN_includedN, cmra_monoN_r, cmra_includedN_le.
Qed.
Definition uPred_wand_aux : seal (@uPred_wand_def). by eexists. Qed.
Definition uPred_wand {M} := unseal uPred_wand_aux M.
Definition uPred_wand_eq :
  @uPred_wand = @uPred_wand_def := seal_eq uPred_wand_aux.

(* Equivalently, this could be `∀ y, P n y`.  That's closer to the intuition
   of "embedding the step-indexed logic in Iris", but the two are equivalent
   because Iris is afine.  The following is easier to work with. *)
Program Definition uPred_plainly_def {M} (P : uPred M) : uPred M :=
  {| uPred_holds n x := P n ε |}.
Solve Obligations with naive_solver eauto using uPred_mono, ucmra_unit_validN.
Definition uPred_plainly_aux : seal (@uPred_plainly_def). by eexists. Qed.
Definition uPred_plainly {M} := unseal uPred_plainly_aux M.
Definition uPred_plainly_eq :
  @uPred_plainly = @uPred_plainly_def := seal_eq uPred_plainly_aux.

Program Definition uPred_persistently_def {M} (P : uPred M) : uPred M :=
  {| uPred_holds n x := P n (core x) |}.
Next Obligation.
  intros M; naive_solver eauto using uPred_mono, @cmra_core_monoN.
Qed.
Definition uPred_persistently_aux : seal (@uPred_persistently_def). by eexists. Qed.
Definition uPred_persistently {M} := unseal uPred_persistently_aux M.
Definition uPred_persistently_eq :
  @uPred_persistently = @uPred_persistently_def := seal_eq uPred_persistently_aux.

Program Definition uPred_later_def {M} (P : uPred M) : uPred M :=
  {| uPred_holds n x := match n return _ with 0 => True | S n' => P n' x end |}.
Next Obligation.
  intros M P [|n1] [|n2] x1 x2; eauto using uPred_mono, cmra_includedN_S with lia.
Qed.
Definition uPred_later_aux : seal (@uPred_later_def). by eexists. Qed.
Definition uPred_later {M} := unseal uPred_later_aux M.
Definition uPred_later_eq :
  @uPred_later = @uPred_later_def := seal_eq uPred_later_aux.

Program Definition uPred_ownM_def {M : ucmraT} (a : M) : uPred M :=
  {| uPred_holds n x := a ≼{n} x |}.
Next Obligation.
  intros M a n1 n2 x1 x [a' Hx1] [x2 Hx] Hn. eapply cmra_includedN_le=>//.
  exists (a' ⋅ x2). by rewrite Hx(assoc op) Hx1.
Qed.
Definition uPred_ownM_aux : seal (@uPred_ownM_def). by eexists. Qed.
Definition uPred_ownM {M} := unseal uPred_ownM_aux M.
Definition uPred_ownM_eq :
  @uPred_ownM = @uPred_ownM_def := seal_eq uPred_ownM_aux.

Program Definition uPred_cmra_valid_def {M} {A : cmraT} (a : A) : uPred M :=
  {| uPred_holds n x := ✓{n} a |}.
Solve Obligations with naive_solver eauto 2 using cmra_validN_le.
Definition uPred_cmra_valid_aux : seal (@uPred_cmra_valid_def). by eexists. Qed.
Definition uPred_cmra_valid {M A} := unseal uPred_cmra_valid_aux M A.
Definition uPred_cmra_valid_eq :
  @uPred_cmra_valid = @uPred_cmra_valid_def := seal_eq uPred_cmra_valid_aux.

Program Definition uPred_bupd_def {M} (Q : uPred M) : uPred M :=
  {| uPred_holds n x := ∀ k yf,
      k ≤ n → ✓{k} (x ⋅ yf) → ∃ x', ✓{k} (x' ⋅ yf) ∧ Q k x' |}.
Next Obligation.
  intros M Q n1 n2 x1 x2 HQ [x3 Hx] Hn k yf Hk.
  rewrite (dist_le _ _ _ _ Hx); last lia. intros Hxy.
  destruct (HQ k (x3 ⋅ yf)) as (x'&?&?); [auto|by rewrite assoc|].
  exists (x' ⋅ x3); split; first by rewrite -assoc.
  eauto using uPred_mono, cmra_includedN_l.
Qed.
Definition uPred_bupd_aux : seal (@uPred_bupd_def). by eexists. Qed.
Definition uPred_bupd {M} := unseal uPred_bupd_aux M.
Definition uPred_bupd_eq : @uPred_bupd = @uPred_bupd_def := seal_eq uPred_bupd_aux.

(* Latest notation *)
Notation "'⌜' φ '⌝'" := (uPred_pure φ%stdpp%type)
  (at level 1, φ at level 200, format "⌜ φ ⌝") : uPred_scope.
Notation "'False'" := (uPred_pure False) : uPred_scope.
Notation "'True'" := (uPred_pure True) : uPred_scope.
Infix "∧" := uPred_and : uPred_scope.
Notation "(∧)" := uPred_and (only parsing) : uPred_scope.
Infix "∨" := uPred_or : uPred_scope.
Notation "(∨)" := uPred_or (only parsing) : uPred_scope.
Infix "→" := uPred_impl : uPred_scope.
Infix "∗" := uPred_sep (at level 80, right associativity) : uPred_scope.
Notation "(∗)" := uPred_sep (only parsing) : uPred_scope.
Notation "P -∗ Q" := (uPred_wand P Q)
  (at level 99, Q at level 200, right associativity) : uPred_scope.
Notation "∀ x .. y , P" :=
  (uPred_forall (λ x, .. (uPred_forall (λ y, P)) ..)%I)
  (at level 200, x binder, y binder, right associativity) : uPred_scope.
Notation "∃ x .. y , P" :=
  (uPred_exist (λ x, .. (uPred_exist (λ y, P)) ..)%I)
  (at level 200, x binder, y binder, right associativity) : uPred_scope.
Notation "■ P" := (uPred_plainly P)
  (at level 20, right associativity) : uPred_scope.
Notation "□ P" := (uPred_persistently P)
  (at level 20, right associativity) : uPred_scope.
Notation "▷ P" := (uPred_later P)
  (at level 20, right associativity) : uPred_scope.
Infix "≡" := uPred_internal_eq : uPred_scope.
Notation "✓ x" := (uPred_cmra_valid x) (at level 20) : uPred_scope.
Notation "|==> Q" := (uPred_bupd Q)
  (at level 99, Q at level 200, format "|==>  Q") : uPred_scope.
Notation "P ==∗ Q" := (P ⊢ |==> Q)
  (at level 99, Q at level 200, only parsing) : stdpp_scope.
Notation "P ==∗ Q" := (P -∗ |==> Q)%I
  (at level 99, Q at level 200, format "P  ==∗  Q") : uPred_scope.

Coercion uPred_valid {M} (P : uPred M) : Prop := True%I ⊢ P.
Typeclasses Opaque uPred_valid.

Notation "P -∗ Q" := (P ⊢ Q)
  (at level 99, Q at level 200, right associativity) : stdpp_scope.

Module uPred.
Definition unseal_eqs :=
  (uPred_pure_eq, uPred_and_eq, uPred_or_eq, uPred_impl_eq, uPred_forall_eq,
  uPred_exist_eq, uPred_internal_eq_eq, uPred_sep_eq, uPred_wand_eq,
  uPred_persistently_eq, uPred_plainly_eq, uPred_persistently_eq,
  uPred_later_eq, uPred_ownM_eq, uPred_cmra_valid_eq, uPred_bupd_eq).
Ltac unseal := rewrite !unseal_eqs /=.

Section primitive.
Context {M : ucmraT}.
Implicit Types φ : Prop.
Implicit Types P Q : uPred M.
Implicit Types A : Type.
Notation "P ⊢ Q" := (@uPred_entails M P%I Q%I). (* Force implicit argument M *)
Notation "P ⊣⊢ Q" := (equiv (A:=uPred M) P%I Q%I). (* Force implicit argument M *)
Arguments uPred_holds {_} !_ _ _ /.
Hint Immediate uPred_in_entails.

(** Non-expansiveness and setoid morphisms *)
Global Instance pure_proper : Proper (iff ==> (⊣⊢)) (@uPred_pure M) | 0.
Proof. intros φ1 φ2 Hφ. by unseal; split=> -[|n] ?; try apply Hφ. Qed.
Global Instance pure_ne n : Proper (iff ==> dist n) (@uPred_pure M) | 1.
Proof. by intros φ1 φ2 ->. Qed.

Global Instance and_ne : NonExpansive2 (@uPred_and M).
Proof.
  intros n P P' HP Q Q' HQ; unseal; split=> x n' ??.
  split; (intros [??]; split; [by apply HP|by apply HQ]).
Qed.
Global Instance and_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@uPred_and M) := ne_proper_2 _.
Global Instance or_ne : NonExpansive2 (@uPred_or M).
Proof.
  intros n P P' HP Q Q' HQ; split=> x n' ??.
  unseal; split; (intros [?|?]; [left; by apply HP|right; by apply HQ]).
Qed.
Global Instance or_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@uPred_or M) := ne_proper_2 _.
Global Instance impl_ne :
  NonExpansive2 (@uPred_impl M).
Proof.
  intros n P P' HP Q Q' HQ; split=> x n' ??.
  unseal; split; intros HPQ x' n'' ????; apply HQ, HPQ, HP; auto.
Qed.
Global Instance impl_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@uPred_impl M) := ne_proper_2 _.
Global Instance sep_ne : NonExpansive2 (@uPred_sep M).
Proof.
  intros n P P' HP Q Q' HQ; split=> n' x ??.
  unseal; split; intros (x1&x2&?&?&?); ofe_subst x;
    exists x1, x2; split_and!; try (apply HP || apply HQ);
    eauto using cmra_validN_op_l, cmra_validN_op_r.
Qed.
Global Instance sep_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@uPred_sep M) := ne_proper_2 _.
Global Instance wand_ne :
  NonExpansive2 (@uPred_wand M).
Proof.
  intros n P P' HP Q Q' HQ; split=> n' x ??; unseal; split; intros HPQ x' n'' ???;
    apply HQ, HPQ, HP; eauto using cmra_validN_op_r.
Qed.
Global Instance wand_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@uPred_wand M) := ne_proper_2 _.
Global Instance internal_eq_ne (A : ofeT) :
  NonExpansive2 (@uPred_internal_eq M A).
Proof.
  intros n x x' Hx y y' Hy; split=> n' z; unseal; split; intros; simpl in *.
  - by rewrite -(dist_le _ _ _ _ Hx) -?(dist_le _ _ _ _ Hy); auto.
  - by rewrite (dist_le _ _ _ _ Hx) ?(dist_le _ _ _ _ Hy); auto.
Qed.
Global Instance internal_eq_proper (A : ofeT) :
  Proper ((≡) ==> (≡) ==> (⊣⊢)) (@uPred_internal_eq M A) := ne_proper_2 _.
Global Instance forall_ne A n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (@uPred_forall M A).
Proof.
  by intros Ψ1 Ψ2 HΨ; unseal; split=> n' x; split; intros HP a; apply HΨ.
Qed.
Global Instance forall_proper A :
  Proper (pointwise_relation _ (⊣⊢) ==> (⊣⊢)) (@uPred_forall M A).
Proof.
  by intros Ψ1 Ψ2 HΨ; unseal; split=> n' x; split; intros HP a; apply HΨ.
Qed.
Global Instance exist_ne A n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (@uPred_exist M A).
Proof.
  intros Ψ1 Ψ2 HΨ.
  unseal; split=> n' x ??; split; intros [a ?]; exists a; by apply HΨ.
Qed.
Global Instance exist_proper A :
  Proper (pointwise_relation _ (⊣⊢) ==> (⊣⊢)) (@uPred_exist M A).
Proof.
  intros Ψ1 Ψ2 HΨ.
  unseal; split=> n' x ?; split; intros [a ?]; exists a; by apply HΨ.
Qed.
Global Instance later_contractive : Contractive (@uPred_later M).
Proof.
  unseal; intros [|n] P Q HPQ; split=> -[|n'] x ?? //=; try omega.
  apply HPQ; eauto using cmra_validN_S.
Qed.
Definition later_ne : NonExpansive (@uPred_later M) := _.
Global Instance later_proper :
  Proper ((⊣⊢) ==> (⊣⊢)) (@uPred_later M) := ne_proper _.
Global Instance plainly_ne : NonExpansive (@uPred_plainly M).
Proof.
  intros n P1 P2 HP.
  unseal; split=> n' x; split; apply HP; eauto using @ucmra_unit_validN.
Qed.
Global Instance plainly_proper :
  Proper ((⊣⊢) ==> (⊣⊢)) (@uPred_plainly M) := ne_proper _.
Global Instance persistently_ne : NonExpansive (@uPred_persistently M).
Proof.
  intros n P1 P2 HP.
  unseal; split=> n' x; split; apply HP; eauto using @cmra_core_validN.
Qed.
Global Instance persistently_proper :
  Proper ((⊣⊢) ==> (⊣⊢)) (@uPred_persistently M) := ne_proper _.
Global Instance ownM_ne : NonExpansive (@uPred_ownM M).
Proof.
  intros n a b Ha.
  unseal; split=> n' x ? /=. by rewrite (dist_le _ _ _ _ Ha); last lia.
Qed.
Global Instance ownM_proper: Proper ((≡) ==> (⊣⊢)) (@uPred_ownM M) := ne_proper _.
Global Instance cmra_valid_ne {A : cmraT} :
  NonExpansive (@uPred_cmra_valid M A).
Proof.
  intros n a b Ha; unseal; split=> n' x ? /=.
  by rewrite (dist_le _ _ _ _ Ha); last lia.
Qed.
Global Instance cmra_valid_proper {A : cmraT} :
  Proper ((≡) ==> (⊣⊢)) (@uPred_cmra_valid M A) := ne_proper _.
Global Instance bupd_ne : NonExpansive (@uPred_bupd M).
Proof.
  intros n P Q HPQ.
  unseal; split=> n' x; split; intros HP k yf ??;
    destruct (HP k yf) as (x'&?&?); auto;
    exists x'; split; auto; apply HPQ; eauto using cmra_validN_op_l.
Qed.
Global Instance bupd_proper : Proper ((≡) ==> (≡)) (@uPred_bupd M) := ne_proper _.
Global Instance uPred_valid_proper : Proper ((⊣⊢) ==> iff) (@uPred_valid M).
Proof. solve_proper. Qed.
Global Instance uPred_valid_mono : Proper ((⊢) ==> impl) (@uPred_valid M).
Proof. solve_proper. Qed.
Global Instance uPred_valid_flip_mono :
  Proper (flip (⊢) ==> flip impl) (@uPred_valid M).
Proof. solve_proper. Qed.

(** Introduction and elimination rules *)
Lemma pure_intro φ P : φ → P ⊢ ⌜φ⌝.
Proof. by intros ?; unseal; split. Qed.
Lemma pure_elim' φ P : (φ → True ⊢ P) → ⌜φ⌝ ⊢ P.
Proof. unseal; intros HP; split=> n x ??. by apply HP. Qed.
Lemma pure_forall_2 {A} (φ : A → Prop) : (∀ x : A, ⌜φ x⌝) ⊢ ⌜∀ x : A, φ x⌝.
Proof. by unseal. Qed.

Lemma and_elim_l P Q : P ∧ Q ⊢ P.
Proof. by unseal; split=> n x ? [??]. Qed.
Lemma and_elim_r P Q : P ∧ Q ⊢ Q.
Proof. by unseal; split=> n x ? [??]. Qed.
Lemma and_intro P Q R : (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R.
Proof. intros HQ HR; unseal; split=> n x ??; by split; [apply HQ|apply HR]. Qed.

Lemma or_intro_l P Q : P ⊢ P ∨ Q.
Proof. unseal; split=> n x ??; left; auto. Qed.
Lemma or_intro_r P Q : Q ⊢ P ∨ Q.
Proof. unseal; split=> n x ??; right; auto. Qed.
Lemma or_elim P Q R : (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R.
Proof. intros HP HQ; unseal; split=> n x ? [?|?]. by apply HP. by apply HQ. Qed.

Lemma impl_intro_r P Q R : (P ∧ Q ⊢ R) → P ⊢ Q → R.
Proof.
  unseal; intros HQ; split=> n x ?? n' x' ????. apply HQ;
    naive_solver eauto using uPred_mono, cmra_included_includedN.
Qed.
Lemma impl_elim P Q R : (P ⊢ Q → R) → (P ⊢ Q) → P ⊢ R.
Proof. by unseal; intros HP HP'; split=> n x ??; apply HP with n x, HP'. Qed.

Lemma forall_intro {A} P (Ψ : A → uPred M): (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a.
Proof. unseal; intros HPΨ; split=> n x ?? a; by apply HPΨ. Qed.
Lemma forall_elim {A} {Ψ : A → uPred M} a : (∀ a, Ψ a) ⊢ Ψ a.
Proof. unseal; split=> n x ? HP; apply HP. Qed.

Lemma exist_intro {A} {Ψ : A → uPred M} a : Ψ a ⊢ ∃ a, Ψ a.
Proof. unseal; split=> n x ??; by exists a. Qed.
Lemma exist_elim {A} (Φ : A → uPred M) Q : (∀ a, Φ a ⊢ Q) → (∃ a, Φ a) ⊢ Q.
Proof. unseal; intros HΦΨ; split=> n x ? [a ?]; by apply HΦΨ with a. Qed.

Lemma internal_eq_refl {A : ofeT} (a : A) : uPred_valid (M:=M) (a ≡ a).
Proof. unseal; by split=> n x ??; simpl. Qed.
Lemma internal_eq_rewrite {A : ofeT} a b (Ψ : A → uPred M) :
  NonExpansive Ψ → a ≡ b ⊢ Ψ a → Ψ b.
Proof. intros HΨ. unseal; split=> n x ?? n' x' ??? Ha. by apply HΨ with n a. Qed.

(* BI connectives *)
Lemma sep_mono P P' Q Q' : (P ⊢ Q) → (P' ⊢ Q') → P ∗ P' ⊢ Q ∗ Q'.
Proof.
  intros HQ HQ'; unseal.
  split; intros n' x ? (x1&x2&?&?&?); exists x1,x2; ofe_subst x;
    eauto 7 using cmra_validN_op_l, cmra_validN_op_r, uPred_in_entails.
Qed.
Lemma True_sep_1 P : P ⊢ True ∗ P.
Proof.
  unseal; split; intros n x ??. exists (core x), x. by rewrite cmra_core_l.
Qed.
Lemma True_sep_2 P : True ∗ P ⊢ P.
Proof.
  unseal; split; intros n x ? (x1&x2&?&_&?); ofe_subst;
    eauto using uPred_mono, cmra_includedN_r.
Qed.
Lemma sep_comm' P Q : P ∗ Q ⊢ Q ∗ P.
Proof.
  unseal; split; intros n x ? (x1&x2&?&?&?); exists x2, x1; by rewrite (comm op).
Qed.
Lemma sep_assoc' P Q R : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R).
Proof.
  unseal; split; intros n x ? (x1&x2&Hx&(y1&y2&Hy&?&?)&?).
  exists y1, (y2 ⋅ x2); split_and?; auto.
  + by rewrite (assoc op) -Hy -Hx.
  + by exists y2, x2.
Qed.
Lemma wand_intro_r P Q R : (P ∗ Q ⊢ R) → P ⊢ Q -∗ R.
Proof.
  unseal=> HPQR; split=> n x ?? n' x' ???; apply HPQR; auto.
  exists x, x'; split_and?; auto.
  eapply uPred_mono with n x; eauto using cmra_validN_op_l.
Qed.
Lemma wand_elim_l' P Q R : (P ⊢ Q -∗ R) → P ∗ Q ⊢ R.
Proof.
  unseal =>HPQR. split; intros n x ? (?&?&?&?&?). ofe_subst.
  eapply HPQR; eauto using cmra_validN_op_l.
Qed.

(* The plainness modality *)
Lemma plainly_mono P Q : (P ⊢ Q) → ■ P ⊢ ■ Q.
Proof. intros HP; unseal; split=> n x ? /=. apply HP, ucmra_unit_validN. Qed.
Lemma plainly_elim' P : ■ P ⊢ □ P.
Proof. unseal; split; simpl; eauto using uPred_mono, @ucmra_unit_leastN. Qed.
Lemma plainly_idemp P : ■ P ⊢ ■ ■ P.
Proof. unseal; split=> n x ?? //. Qed.

Lemma plainly_forall_2 {A} (Ψ : A → uPred M) : (∀ a, ■ Ψ a) ⊢ (■ ∀ a, Ψ a).
Proof. by unseal. Qed.
Lemma plainly_exist_1 {A} (Ψ : A → uPred M) : (■ ∃ a, Ψ a) ⊢ (∃ a, ■ Ψ a).
Proof. by unseal. Qed.

Lemma prop_ext P Q : ■ ((P → Q) ∧ (Q → P)) ⊢ P ≡ Q.
Proof.
  unseal; split=> n x ? /= HPQ; split=> n' x' ? HP;
    split; eapply HPQ; eauto using @ucmra_unit_least.
Qed.

(* Always *)
Lemma persistently_mono P Q : (P ⊢ Q) → □ P ⊢ □ Q.
Proof. intros HP; unseal; split=> n x ? /=. by apply HP, cmra_core_validN. Qed.
Lemma persistently_elim P : □ P ⊢ P.
Proof.
  unseal; split=> n x ? /=.
  eauto using uPred_mono, @cmra_included_core, cmra_included_includedN.
Qed.
Lemma persistently_idemp_2 P : □ P ⊢ □ □ P.
Proof. unseal; split=> n x ?? /=. by rewrite cmra_core_idemp. Qed.

Lemma persistently_forall_2 {A} (Ψ : A → uPred M) : (∀ a, □ Ψ a) ⊢ (□ ∀ a, Ψ a).
Proof. by unseal. Qed.
Lemma persistently_exist_1 {A} (Ψ : A → uPred M) : (□ ∃ a, Ψ a) ⊢ (∃ a, □ Ψ a).
Proof. by unseal. Qed.

Lemma persistently_and_sep_l_1 P Q : □ P ∧ Q ⊢ □ P ∗ Q.
Proof.
  unseal; split=> n x ? [??]; exists (core x), x; simpl in *.
  by rewrite cmra_core_l cmra_core_idemp.
Qed.

(* The following two laws are very similar, and indeed they hold not just for □
   and ■, but for any modality defined as `M P n x := ∀ y, R x y → P n y`. *)
Lemma persistently_impl_plainly P Q : (■ P → □ Q) ⊢ □ (■ P → Q).
Proof.
  unseal; split=> /= n x ? HPQ n' x' ????.
  eapply uPred_mono with n' (core x)=>//; [|by apply cmra_included_includedN].
  apply (HPQ n' x); eauto using cmra_validN_le.
Qed.

Lemma plainly_impl_plainly P Q : (■ P → ■ Q) ⊢ ■ (■ P → Q).
Proof.
  unseal; split=> /= n x ? HPQ n' x' ????.
  eapply uPred_mono with n' ε=>//; [|by apply cmra_included_includedN].
  apply (HPQ n' x); eauto using cmra_validN_le.
Qed.

(* Later *)
Lemma later_mono P Q : (P ⊢ Q) → ▷ P ⊢ ▷ Q.
Proof.
  unseal=> HP; split=>-[|n] x ??; [done|apply HP; eauto using cmra_validN_S].
Qed.
Lemma löb P : (▷ P → P) ⊢ P.
Proof.
  unseal; split=> n x ? HP; induction n as [|n IH]; [by apply HP|].
  apply HP, IH, uPred_mono with (S n) x; eauto using cmra_validN_S.
Qed.
Lemma later_forall_2 {A} (Φ : A → uPred M) : (∀ a, ▷ Φ a) ⊢ ▷ ∀ a, Φ a.
Proof. unseal; by split=> -[|n] x. Qed.
Lemma later_exist_false {A} (Φ : A → uPred M) :
  (▷ ∃ a, Φ a) ⊢ ▷ False ∨ (∃ a, ▷ Φ a).
Proof. unseal; split=> -[|[|n]] x /=; eauto. Qed.
Lemma later_sep P Q : ▷ (P ∗ Q) ⊣⊢ ▷ P ∗ ▷ Q.
Proof.
  unseal; split=> n x ?; split.
  - destruct n as [|n]; simpl.
    { by exists x, (core x); rewrite cmra_core_r. }
    intros (x1&x2&Hx&?&?); destruct (cmra_extend n x x1 x2)
      as (y1&y2&Hx'&Hy1&Hy2); eauto using cmra_validN_S; simpl in *.
    exists y1, y2; split; [by rewrite Hx'|by rewrite Hy1 Hy2].
  - destruct n as [|n]; simpl; [done|intros (x1&x2&Hx&?&?)].
    exists x1, x2; eauto using dist_S.
Qed.
Lemma later_false_excluded_middle P : ▷ P ⊢ ▷ False ∨ (▷ False → P).
Proof.
  unseal; split=> -[|n] x ? /= HP; [by left|right].
  intros [|n'] x' ????; eauto using uPred_mono, cmra_included_includedN.
Qed.
Lemma persistently_later P : □ ▷ P ⊣⊢ ▷ □ P.
Proof. by unseal. Qed.
Lemma plainly_later P : ■ ▷ P ⊣⊢ ▷ ■ P.
Proof. by unseal. Qed.

(* Own *)
Lemma ownM_op (a1 a2 : M) :
  uPred_ownM (a1 ⋅ a2) ⊣⊢ uPred_ownM a1 ∗ uPred_ownM a2.
Proof.
  unseal; split=> n x ?; split.
  - intros [z ?]; exists a1, (a2 ⋅ z); split; [by rewrite (assoc op)|].
    split. by exists (core a1); rewrite cmra_core_r. by exists z.
  - intros (y1&y2&Hx&[z1 Hy1]&[z2 Hy2]); exists (z1 ⋅ z2).
    by rewrite (assoc op _ z1) -(comm op z1) (assoc op z1)
      -(assoc op _ a2) (comm op z1) -Hy1 -Hy2.
Qed.
Lemma persistently_ownM_core (a : M) : uPred_ownM a ⊢ □ uPred_ownM (core a).
Proof.
  split=> n x /=; unseal; intros Hx. simpl. by apply cmra_core_monoN.
Qed.
Lemma ownM_unit : uPred_valid (M:=M) (uPred_ownM ε).
Proof. unseal; split=> n x ??; by  exists x; rewrite left_id. Qed.
Lemma later_ownM a : ▷ uPred_ownM a ⊢ ∃ b, uPred_ownM b ∧ ▷ (a ≡ b).
Proof.
  unseal; split=> -[|n] x /= ? Hax; first by eauto using ucmra_unit_leastN.
  destruct Hax as [y ?].
  destruct (cmra_extend n x a y) as (a'&y'&Hx&?&?); auto using cmra_validN_S.
  exists a'. rewrite Hx. eauto using cmra_includedN_l.
Qed.

(* Valid *)
Lemma ownM_valid (a : M) : uPred_ownM a ⊢ ✓ a.
Proof.
  unseal; split=> n x Hv [a' ?]; ofe_subst; eauto using cmra_validN_op_l.
Qed.
Lemma cmra_valid_intro {A : cmraT} (a : A) : ✓ a → uPred_valid (M:=M) (✓ a).
Proof. unseal=> ?; split=> n x ? _ /=; by apply cmra_valid_validN. Qed.
Lemma cmra_valid_elim {A : cmraT} (a : A) : ¬ ✓{0} a → ✓ a ⊢ False.
Proof. unseal=> Ha; split=> n x ??; apply Ha, cmra_validN_le with n; auto. Qed.
Lemma plainly_cmra_valid_1 {A : cmraT} (a : A) : ✓ a ⊢ ■ ✓ a.
Proof. by unseal. Qed.
Lemma cmra_valid_weaken {A : cmraT} (a b : A) : ✓ (a ⋅ b) ⊢ ✓ a.
Proof. unseal; split=> n x _; apply cmra_validN_op_l. Qed.

(* Basic update modality *)
Lemma bupd_intro P : P ==∗ P.
Proof.
  unseal. split=> n x ? HP k yf ?; exists x; split; first done.
  apply uPred_mono with n x; eauto using cmra_validN_op_l.
Qed.
Lemma bupd_mono P Q : (P ⊢ Q) → (|==> P) ==∗ Q.
Proof.
  unseal. intros HPQ; split=> n x ? HP k yf ??.
  destruct (HP k yf) as (x'&?&?); eauto.
  exists x'; split; eauto using uPred_in_entails, cmra_validN_op_l.
Qed.
Lemma bupd_trans P : (|==> |==> P) ==∗ P.
Proof. unseal; split; naive_solver. Qed.
Lemma bupd_frame_r P R : (|==> P) ∗ R ==∗ P ∗ R.
Proof.
  unseal; split; intros n x ? (x1&x2&Hx&HP&?) k yf ??.
  destruct (HP k (x2 ⋅ yf)) as (x'&?&?); eauto.
  { by rewrite assoc -(dist_le _ _ _ _ Hx); last lia. }
  exists (x' ⋅ x2); split; first by rewrite -assoc.
  exists x', x2. eauto using uPred_mono, cmra_validN_op_l, cmra_validN_op_r.
Qed.
Lemma bupd_ownM_updateP x (Φ : M → Prop) :
  x ~~>: Φ → uPred_ownM x ==∗ ∃ y, ⌜Φ y⌝ ∧ uPred_ownM y.
Proof.
  unseal=> Hup; split=> n x2 ? [x3 Hx] k yf ??.
  destruct (Hup k (Some (x3 ⋅ yf))) as (y&?&?); simpl in *.
  { rewrite /= assoc -(dist_le _ _ _ _ Hx); auto. }
  exists (y ⋅ x3); split; first by rewrite -assoc.
  exists y; eauto using cmra_includedN_l.
Qed.
Lemma bupd_plainly P : (|==> ■ P) ⊢ P.
Proof.
  unseal; split => n x Hnx /= Hng.
  destruct (Hng n ε) as [? [_ Hng']]; try rewrite right_id; auto.
  eapply uPred_mono; eauto using ucmra_unit_leastN.
Qed.

(* Products *)
Lemma prod_equivI {A B : ofeT} (x y : A * B) : x ≡ y ⊣⊢ x.1 ≡ y.1 ∧ x.2 ≡ y.2.
Proof. by unseal. Qed.
Lemma prod_validI {A B : cmraT} (x : A * B) : ✓ x ⊣⊢ ✓ x.1 ∧ ✓ x.2.
Proof. by unseal. Qed.

(* Type-level Later *)
Lemma later_equivI {A : ofeT} (x y : A) : Next x ≡ Next y ⊣⊢ ▷ (x ≡ y).
Proof. by unseal. Qed.

(* Discrete *)
Lemma discrete_valid {A : cmraT} `{!CmraDiscrete A} (a : A) : ✓ a ⊣⊢ ⌜✓ a⌝.
Proof. unseal; split=> n x _. by rewrite /= -cmra_discrete_valid_iff. Qed.
Lemma discrete_eq {A : ofeT} (a b : A) : Discrete a → a ≡ b ⊣⊢ ⌜a ≡ b⌝.
Proof.
  unseal=> ?. apply (anti_symm (⊢)); split=> n x ?; by apply (discrete_iff n).
Qed.

(* Option *)
Lemma option_equivI {A : ofeT} (mx my : option A) :
  mx ≡ my ⊣⊢ match mx, my with
             | Some x, Some y => x ≡ y | None, None => True | _, _ => False
             end.
Proof.
  unseal. do 2 split. by destruct 1. by destruct mx, my; try constructor.
Qed.
Lemma option_validI {A : cmraT} (mx : option A) :
  ✓ mx ⊣⊢ match mx with Some x => ✓ x | None => True end.
Proof. unseal. by destruct mx. Qed.

(* Contractive functions *)
Lemma contractiveI {A B : ofeT} (f : A → B) :
  Contractive f ↔ (∀ a b, ▷ (a ≡ b) ⊢ f a ≡ f b).
Proof.
  split; unseal; intros Hf.
  - intros a b; split=> n x _; apply Hf.
  - intros i a b; eapply Hf, ucmra_unit_validN.
Qed.

(* Function extensionality *)
Lemma ofe_morC_equivI {A B : ofeT} (f g : A -n> B) : f ≡ g ⊣⊢ ∀ x, f x ≡ g x.
Proof. by unseal. Qed.
Lemma ofe_fun_equivI `{B : A → ofeT} (g1 g2 : ofe_fun B) :
  g1 ≡ g2 ⊣⊢ ∀ i, g1 i ≡ g2 i.
Proof. by uPred.unseal. Qed.

Lemma ofe_fun_validI `{B : A → ucmraT} (g : ofe_fun B) : ✓ g ⊣⊢ ∀ i, ✓ g i.
Proof. by uPred.unseal. Qed.

(* Sigma OFE *)
Lemma sig_equivI {A : ofeT} (P : A → Prop) (x y : sigC P) :
  x ≡ y ⊣⊢ proj1_sig x ≡ proj1_sig y.
Proof. by unseal. Qed.
End primitive.
End uPred.
