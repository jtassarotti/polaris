From iris.base_logic Require Export primitive.
Set Default Proof Using "Type".
Import upred.uPred primitive.uPred.

Definition uPred_iff {M} (P Q : uPred M) : uPred M := ((P → Q) ∧ (Q → P))%I.
Instance: Params (@uPred_iff) 1.
Infix "↔" := uPred_iff : uPred_scope.

Definition uPred_laterN {M} (n : nat) (P : uPred M) : uPred M :=
  Nat.iter n uPred_later P.
Instance: Params (@uPred_laterN) 2.
Notation "▷^ n P" := (uPred_laterN n P)
  (at level 20, n at level 9, P at level 20,
   format "▷^ n  P") : uPred_scope.
Notation "▷? p P" := (uPred_laterN (Nat.b2n p) P)
  (at level 20, p at level 9, P at level 20,
   format "▷? p  P") : uPred_scope.

Definition uPred_persistently_if {M} (p : bool) (P : uPred M) : uPred M :=
  (if p then □ P else P)%I.
Instance: Params (@uPred_persistently_if) 2.
Arguments uPred_persistently_if _ !_ _/.
Notation "□? p P" := (uPred_persistently_if p P)
  (at level 20, p at level 9, P at level 20, format "□? p  P").

Definition uPred_except_0 {M} (P : uPred M) : uPred M := ▷ False ∨ P.
Notation "◇ P" := (uPred_except_0 P)
  (at level 20, right associativity) : uPred_scope.
Instance: Params (@uPred_except_0) 1.
Typeclasses Opaque uPred_except_0.

Class Timeless {M} (P : uPred M) := timelessP : ▷ P ⊢ ◇ P.
Arguments timelessP {_} _ {_}.
Hint Mode Timeless + ! : typeclass_instances.
Instance: Params (@Timeless) 1.

Class Persistent {M} (P : uPred M) := persistent : P ⊢ □ P.
Arguments persistent {_} _ {_}.
Hint Mode Persistent + ! : typeclass_instances.
Instance: Params (@Persistent) 1.

Class Plain {M} (P : uPred M) := plain : P ⊢ ■ P.
Arguments plain {_} _ {_}.
Hint Mode Plain + ! : typeclass_instances.
Instance: Params (@Plain) 1.

Module uPred.
Section derived.
Context {M : ucmraT}.
Implicit Types φ : Prop.
Implicit Types P Q : uPred M.
Implicit Types A : Type.
Notation "P ⊢ Q" := (@uPred_entails M P%I Q%I). (* Force implicit argument M *)
Notation "P ⊣⊢ Q" := (equiv (A:=uPred M) P%I Q%I). (* Force implicit argument M *)

(* Derived logical stuff *)
Lemma False_elim P : False ⊢ P.
Proof. by apply (pure_elim' False). Qed.
Lemma True_intro P : P ⊢ True.
Proof. by apply pure_intro. Qed.

Lemma and_elim_l' P Q R : (P ⊢ R) → P ∧ Q ⊢ R.
Proof. by rewrite and_elim_l. Qed.
Lemma and_elim_r' P Q R : (Q ⊢ R) → P ∧ Q ⊢ R.
Proof. by rewrite and_elim_r. Qed.
Lemma or_intro_l' P Q R : (P ⊢ Q) → P ⊢ Q ∨ R.
Proof. intros ->; apply or_intro_l. Qed.
Lemma or_intro_r' P Q R : (P ⊢ R) → P ⊢ Q ∨ R.
Proof. intros ->; apply or_intro_r. Qed.
Lemma exist_intro' {A} P (Ψ : A → uPred M) a : (P ⊢ Ψ a) → P ⊢ ∃ a, Ψ a.
Proof. intros ->; apply exist_intro. Qed.
Lemma forall_elim' {A} P (Ψ : A → uPred M) : (P ⊢ ∀ a, Ψ a) → ∀ a, P ⊢ Ψ a.
Proof. move=> HP a. by rewrite HP forall_elim. Qed.

Hint Resolve pure_intro.
Hint Resolve or_elim or_intro_l' or_intro_r'.
Hint Resolve and_intro and_elim_l' and_elim_r'.
Hint Immediate True_intro False_elim.

Lemma impl_intro_l P Q R : (Q ∧ P ⊢ R) → P ⊢ Q → R.
Proof. intros HR; apply impl_intro_r; rewrite -HR; auto. Qed.
Lemma impl_elim_l P Q : (P → Q) ∧ P ⊢ Q.
Proof. apply impl_elim with P; auto. Qed.
Lemma impl_elim_r P Q : P ∧ (P → Q) ⊢ Q.
Proof. apply impl_elim with P; auto. Qed.
Lemma impl_elim_l' P Q R : (P ⊢ Q → R) → P ∧ Q ⊢ R.
Proof. intros; apply impl_elim with Q; auto. Qed.
Lemma impl_elim_r' P Q R : (Q ⊢ P → R) → P ∧ Q ⊢ R.
Proof. intros; apply impl_elim with P; auto. Qed.
Lemma impl_entails P Q : (P → Q)%I → P ⊢ Q.
Proof. intros HPQ; apply impl_elim with P; rewrite -?HPQ; auto. Qed.
Lemma entails_impl P Q : (P ⊢ Q) → (P → Q)%I.
Proof. intro. apply impl_intro_l. auto. Qed.

Lemma and_mono P P' Q Q' : (P ⊢ Q) → (P' ⊢ Q') → P ∧ P' ⊢ Q ∧ Q'.
Proof. auto. Qed.
Lemma and_mono_l P P' Q : (P ⊢ Q) → P ∧ P' ⊢ Q ∧ P'.
Proof. by intros; apply and_mono. Qed.
Lemma and_mono_r P P' Q' : (P' ⊢ Q') → P ∧ P' ⊢ P ∧ Q'.
Proof. by apply and_mono. Qed.

Lemma or_mono P P' Q Q' : (P ⊢ Q) → (P' ⊢ Q') → P ∨ P' ⊢ Q ∨ Q'.
Proof. auto. Qed.
Lemma or_mono_l P P' Q : (P ⊢ Q) → P ∨ P' ⊢ Q ∨ P'.
Proof. by intros; apply or_mono. Qed.
Lemma or_mono_r P P' Q' : (P' ⊢ Q') → P ∨ P' ⊢ P ∨ Q'.
Proof. by apply or_mono. Qed.

Lemma impl_mono P P' Q Q' : (Q ⊢ P) → (P' ⊢ Q') → (P → P') ⊢ Q → Q'.
Proof.
  intros HP HQ'; apply impl_intro_l; rewrite -HQ'.
  apply impl_elim with P; eauto.
Qed.
Lemma forall_mono {A} (Φ Ψ : A → uPred M) :
  (∀ a, Φ a ⊢ Ψ a) → (∀ a, Φ a) ⊢ ∀ a, Ψ a.
Proof.
  intros HP. apply forall_intro=> a; rewrite -(HP a); apply forall_elim.
Qed.
Lemma exist_mono {A} (Φ Ψ : A → uPred M) :
  (∀ a, Φ a ⊢ Ψ a) → (∃ a, Φ a) ⊢ ∃ a, Ψ a.
Proof. intros HΦ. apply exist_elim=> a; rewrite (HΦ a); apply exist_intro. Qed.

Global Instance and_mono' : Proper ((⊢) ==> (⊢) ==> (⊢)) (@uPred_and M).
Proof. by intros P P' HP Q Q' HQ; apply and_mono. Qed.
Global Instance and_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢) ==> flip (⊢)) (@uPred_and M).
Proof. by intros P P' HP Q Q' HQ; apply and_mono. Qed.
Global Instance or_mono' : Proper ((⊢) ==> (⊢) ==> (⊢)) (@uPred_or M).
Proof. by intros P P' HP Q Q' HQ; apply or_mono. Qed.
Global Instance or_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢) ==> flip (⊢)) (@uPred_or M).
Proof. by intros P P' HP Q Q' HQ; apply or_mono. Qed.
Global Instance impl_mono' :
  Proper (flip (⊢) ==> (⊢) ==> (⊢)) (@uPred_impl M).
Proof. by intros P P' HP Q Q' HQ; apply impl_mono. Qed.
Global Instance impl_flip_mono' :
  Proper ((⊢) ==> flip (⊢) ==> flip (⊢)) (@uPred_impl M).
Proof. by intros P P' HP Q Q' HQ; apply impl_mono. Qed.
Global Instance forall_mono' A :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (@uPred_forall M A).
Proof. intros P1 P2; apply forall_mono. Qed.
Global Instance forall_flip_mono' A :
  Proper (pointwise_relation _ (flip (⊢)) ==> flip (⊢)) (@uPred_forall M A).
Proof. intros P1 P2; apply forall_mono. Qed.
Global Instance exist_mono' A :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (@uPred_exist M A).
Proof. intros P1 P2; apply exist_mono. Qed.
Global Instance exist_flip_mono' A :
  Proper (pointwise_relation _ (flip (⊢)) ==> flip (⊢)) (@uPred_exist M A).
Proof. intros P1 P2; apply exist_mono. Qed.

Global Instance and_idem : IdemP (⊣⊢) (@uPred_and M).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance or_idem : IdemP (⊣⊢) (@uPred_or M).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance and_comm : Comm (⊣⊢) (@uPred_and M).
Proof. intros P Q; apply (anti_symm (⊢)); auto. Qed.
Global Instance True_and : LeftId (⊣⊢) True%I (@uPred_and M).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance and_True : RightId (⊣⊢) True%I (@uPred_and M).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance False_and : LeftAbsorb (⊣⊢) False%I (@uPred_and M).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance and_False : RightAbsorb (⊣⊢) False%I (@uPred_and M).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance True_or : LeftAbsorb (⊣⊢) True%I (@uPred_or M).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance or_True : RightAbsorb (⊣⊢) True%I (@uPred_or M).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance False_or : LeftId (⊣⊢) False%I (@uPred_or M).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance or_False : RightId (⊣⊢) False%I (@uPred_or M).
Proof. intros P; apply (anti_symm (⊢)); auto. Qed.
Global Instance and_assoc : Assoc (⊣⊢) (@uPred_and M).
Proof. intros P Q R; apply (anti_symm (⊢)); auto. Qed.
Global Instance or_comm : Comm (⊣⊢) (@uPred_or M).
Proof. intros P Q; apply (anti_symm (⊢)); auto. Qed.
Global Instance or_assoc : Assoc (⊣⊢) (@uPred_or M).
Proof. intros P Q R; apply (anti_symm (⊢)); auto. Qed.
Global Instance True_impl : LeftId (⊣⊢) True%I (@uPred_impl M).
Proof.
  intros P; apply (anti_symm (⊢)).
  - by rewrite -(left_id True%I uPred_and (_ → _)%I) impl_elim_r.
  - by apply impl_intro_l; rewrite left_id.
Qed.
Lemma False_impl P : (False → P) ⊣⊢ True.
Proof.
  apply (anti_symm (⊢)); [by auto|].
  apply impl_intro_l. rewrite left_absorb. auto.
Qed.

Lemma exists_impl_forall {A} P (Ψ : A → uPred M) :
  ((∃ x : A, Ψ x) → P) ⊣⊢ ∀ x : A, Ψ x → P.
Proof.
  apply equiv_spec; split.
  - apply forall_intro=>x. by rewrite -exist_intro.
  - apply impl_intro_r, impl_elim_r', exist_elim=>x.
    apply impl_intro_r. by rewrite (forall_elim x) impl_elim_r.
Qed.

Lemma or_and_l P Q R : P ∨ Q ∧ R ⊣⊢ (P ∨ Q) ∧ (P ∨ R).
Proof.
  apply (anti_symm (⊢)); first auto.
  do 2 (apply impl_elim_l', or_elim; apply impl_intro_l); auto.
Qed.
Lemma or_and_r P Q R : P ∧ Q ∨ R ⊣⊢ (P ∨ R) ∧ (Q ∨ R).
Proof. by rewrite -!(comm _ R) or_and_l. Qed.
Lemma and_or_l P Q R : P ∧ (Q ∨ R) ⊣⊢ P ∧ Q ∨ P ∧ R.
Proof.
  apply (anti_symm (⊢)); last auto.
  apply impl_elim_r', or_elim; apply impl_intro_l; auto.
Qed.
Lemma and_or_r P Q R : (P ∨ Q) ∧ R ⊣⊢ P ∧ R ∨ Q ∧ R.
Proof. by rewrite -!(comm _ R) and_or_l. Qed.
Lemma and_exist_l {A} P (Ψ : A → uPred M) : P ∧ (∃ a, Ψ a) ⊣⊢ ∃ a, P ∧ Ψ a.
Proof.
  apply (anti_symm (⊢)).
  - apply impl_elim_r'. apply exist_elim=>a. apply impl_intro_l.
    by rewrite -(exist_intro a).
  - apply exist_elim=>a. apply and_intro; first by rewrite and_elim_l.
    by rewrite -(exist_intro a) and_elim_r.
Qed.
Lemma and_exist_r {A} P (Φ: A → uPred M) : (∃ a, Φ a) ∧ P ⊣⊢ ∃ a, Φ a ∧ P.
Proof.
  rewrite -(comm _ P) and_exist_l. apply exist_proper=>a. by rewrite comm.
Qed.
Lemma or_exist {A} (Φ Ψ : A → uPred M) :
  (∃ a, Φ a ∨ Ψ a) ⊣⊢ (∃ a, Φ a) ∨ (∃ a, Ψ a).
Proof.
  apply (anti_symm (⊢)).
  - apply exist_elim=> a. by rewrite -!(exist_intro a).
  - apply or_elim; apply exist_elim=> a; rewrite -(exist_intro a); auto.
Qed.

Lemma pure_elim φ Q R : (Q ⊢ ⌜φ⌝) → (φ → Q ⊢ R) → Q ⊢ R.
Proof.
  intros HQ HQR. rewrite -(idemp uPred_and Q) {1}HQ.
  apply impl_elim_l', pure_elim'=> ?. by apply entails_impl, HQR.
Qed.
Lemma pure_mono φ1 φ2 : (φ1 → φ2) → ⌜φ1⌝ ⊢ ⌜φ2⌝.
Proof. intros; apply pure_elim with φ1; eauto. Qed.
Global Instance pure_mono' : Proper (impl ==> (⊢)) (@uPred_pure M).
Proof. intros φ1 φ2; apply pure_mono. Qed.
Global Instance pure_flip_mono : Proper (flip impl ==> flip (⊢)) (@uPred_pure M).
Proof. intros φ1 φ2; apply pure_mono. Qed.
Lemma pure_iff φ1 φ2 : (φ1 ↔ φ2) → ⌜φ1⌝ ⊣⊢ ⌜φ2⌝.
Proof. intros [??]; apply (anti_symm _); auto using pure_mono. Qed.
Lemma pure_intro_l φ Q R : φ → (⌜φ⌝ ∧ Q ⊢ R) → Q ⊢ R.
Proof. intros ? <-; auto using pure_intro. Qed.
Lemma pure_intro_r φ Q R : φ → (Q ∧ ⌜φ⌝ ⊢ R) → Q ⊢ R.
Proof. intros ? <-; auto. Qed.
Lemma pure_intro_impl φ Q R : φ → (Q ⊢ ⌜φ⌝ → R) → Q ⊢ R.
Proof. intros ? ->. eauto using pure_intro_l, impl_elim_r. Qed.
Lemma pure_elim_l φ Q R : (φ → Q ⊢ R) → ⌜φ⌝ ∧ Q ⊢ R.
Proof. intros; apply pure_elim with φ; eauto. Qed.
Lemma pure_elim_r φ Q R : (φ → Q ⊢ R) → Q ∧ ⌜φ⌝ ⊢ R.
Proof. intros; apply pure_elim with φ; eauto. Qed.

Lemma pure_True (φ : Prop) : φ → ⌜φ⌝ ⊣⊢ True.
Proof. intros; apply (anti_symm _); auto. Qed.
Lemma pure_False (φ : Prop) : ¬φ → ⌜φ⌝ ⊣⊢ False.
Proof. intros; apply (anti_symm _); eauto using pure_elim. Qed.

Lemma pure_and φ1 φ2 : ⌜φ1 ∧ φ2⌝ ⊣⊢ ⌜φ1⌝ ∧ ⌜φ2⌝.
Proof.
  apply (anti_symm _).
  - eapply pure_elim=> // -[??]; auto.
  - eapply (pure_elim φ1); [auto|]=> ?. eapply (pure_elim φ2); auto.
Qed.
Lemma pure_or φ1 φ2 : ⌜φ1 ∨ φ2⌝ ⊣⊢ ⌜φ1⌝ ∨ ⌜φ2⌝.
Proof.
  apply (anti_symm _).
  - eapply pure_elim=> // -[?|?]; auto.
  - apply or_elim; eapply pure_elim; eauto.
Qed.
Lemma pure_impl φ1 φ2 : ⌜φ1 → φ2⌝ ⊣⊢ (⌜φ1⌝ → ⌜φ2⌝).
Proof.
  apply (anti_symm _).
  - apply impl_intro_l. rewrite -pure_and. apply pure_mono. naive_solver.
  - rewrite -pure_forall_2. apply forall_intro=> ?.
    by rewrite -(left_id True uPred_and (_→_))%I (pure_True φ1) // impl_elim_r.
Qed.
Lemma pure_forall {A} (φ : A → Prop) : ⌜∀ x, φ x⌝ ⊣⊢ ∀ x, ⌜φ x⌝.
Proof.
  apply (anti_symm _); auto using pure_forall_2.
  apply forall_intro=> x. eauto using pure_mono.
Qed.
Lemma pure_exist {A} (φ : A → Prop) : ⌜∃ x, φ x⌝ ⊣⊢ ∃ x, ⌜φ x⌝.
Proof.
  apply (anti_symm _).
  - eapply pure_elim=> // -[x ?]. rewrite -(exist_intro x); auto.
  - apply exist_elim=> x. eauto using pure_mono.
Qed.

Lemma internal_eq_refl' {A : ofeT} (a : A) P : P ⊢ a ≡ a.
Proof. rewrite (True_intro P). apply internal_eq_refl. Qed.
Hint Resolve internal_eq_refl'.
Lemma equiv_internal_eq {A : ofeT} P (a b : A) : a ≡ b → P ⊢ a ≡ b.
Proof. by intros ->. Qed.
Lemma internal_eq_sym {A : ofeT} (a b : A) : a ≡ b ⊢ b ≡ a.
Proof.
  rewrite (internal_eq_rewrite a b (λ b, b ≡ a)%I ltac:(solve_proper)).
  by rewrite -internal_eq_refl True_impl.
Qed.
Lemma f_equiv {A B : ofeT} (f : A → B) `{!NonExpansive f} x y :
  x ≡ y ⊢ f x ≡ f y.
Proof.
  rewrite (internal_eq_rewrite x y (λ y, f x ≡ f y)%I ltac:(solve_proper)).
  by rewrite -internal_eq_refl True_impl.
Qed.
Lemma internal_eq_rewrite_contractive {A : ofeT} a b (Ψ : A → uPred M)
  {HΨ : Contractive Ψ} : ▷ (a ≡ b) ⊢ Ψ a → Ψ b.
Proof. move: HΨ=> /contractiveI ->. by rewrite (internal_eq_rewrite _ _ id). Qed.

Lemma pure_impl_forall φ P : (⌜φ⌝ → P) ⊣⊢ (∀ _ : φ, P).
Proof.
  apply (anti_symm _).
  - apply forall_intro=> ?. by rewrite pure_True // left_id.
  - apply impl_intro_l, pure_elim_l=> Hφ. by rewrite (forall_elim Hφ).
Qed.
Lemma pure_alt φ : ⌜φ⌝ ⊣⊢ ∃ _ : φ, True.
Proof.
  apply (anti_symm _).
  - eapply pure_elim; eauto=> H. rewrite -(exist_intro H); auto.
  - by apply exist_elim, pure_intro.
Qed.
Lemma and_alt P Q : P ∧ Q ⊣⊢ ∀ b : bool, if b then P else Q.
Proof.
  apply (anti_symm _); first apply forall_intro=> -[]; auto.
  apply and_intro. by rewrite (forall_elim true). by rewrite (forall_elim false).
Qed.
Lemma or_alt P Q : P ∨ Q ⊣⊢ ∃ b : bool, if b then P else Q.
Proof.
  apply (anti_symm _); last apply exist_elim=> -[]; auto.
  apply or_elim. by rewrite -(exist_intro true). by rewrite -(exist_intro false).
Qed.

Global Instance iff_ne : NonExpansive2 (@uPred_iff M).
Proof. unfold uPred_iff; solve_proper. Qed.
Global Instance iff_proper :
  Proper ((⊣⊢) ==> (⊣⊢) ==> (⊣⊢)) (@uPred_iff M) := ne_proper_2 _.

Lemma iff_refl Q P : Q ⊢ P ↔ P.
Proof. rewrite /uPred_iff; apply and_intro; apply impl_intro_l; auto. Qed.
Lemma iff_equiv P Q : (P ↔ Q)%I → (P ⊣⊢ Q).
Proof.
  intros HPQ; apply (anti_symm (⊢));
    apply impl_entails; rewrite /uPred_valid HPQ /uPred_iff; auto.
Qed.
Lemma equiv_iff P Q : (P ⊣⊢ Q) → (P ↔ Q)%I.
Proof. intros ->; apply iff_refl. Qed.
Lemma internal_eq_iff P Q : P ≡ Q ⊢ P ↔ Q.
Proof.
  rewrite (internal_eq_rewrite P Q (λ Q, P ↔ Q)%I ltac:(solve_proper)).
  by rewrite -(iff_refl True) True_impl.
Qed.

(* Derived BI Stuff *)
Hint Resolve sep_mono.
Lemma sep_mono_l P P' Q : (P ⊢ Q) → P ∗ P' ⊢ Q ∗ P'.
Proof. by intros; apply sep_mono. Qed.
Lemma sep_mono_r P P' Q' : (P' ⊢ Q') → P ∗ P' ⊢ P ∗ Q'.
Proof. by apply sep_mono. Qed.
Global Instance sep_mono' : Proper ((⊢) ==> (⊢) ==> (⊢)) (@uPred_sep M).
Proof. by intros P P' HP Q Q' HQ; apply sep_mono. Qed.
Global Instance sep_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢) ==> flip (⊢)) (@uPred_sep M).
Proof. by intros P P' HP Q Q' HQ; apply sep_mono. Qed.
Lemma wand_mono P P' Q Q' : (Q ⊢ P) → (P' ⊢ Q') → (P -∗ P') ⊢ Q -∗ Q'.
Proof.
  intros HP HQ; apply wand_intro_r. rewrite HP -HQ. by apply wand_elim_l'.
Qed.
Global Instance wand_mono' : Proper (flip (⊢) ==> (⊢) ==> (⊢)) (@uPred_wand M).
Proof. by intros P P' HP Q Q' HQ; apply wand_mono. Qed.
Global Instance wand_flip_mono' :
  Proper ((⊢) ==> flip (⊢) ==> flip (⊢)) (@uPred_wand M).
Proof. by intros P P' HP Q Q' HQ; apply wand_mono. Qed.

Global Instance sep_comm : Comm (⊣⊢) (@uPred_sep M).
Proof. intros P Q; apply (anti_symm _); auto using sep_comm'. Qed.
Global Instance sep_assoc : Assoc (⊣⊢) (@uPred_sep M).
Proof.
  intros P Q R; apply (anti_symm _); auto using sep_assoc'.
  by rewrite !(comm _ P) !(comm _ _ R) sep_assoc'.
Qed.
Global Instance True_sep : LeftId (⊣⊢) True%I (@uPred_sep M).
Proof. intros P; apply (anti_symm _); auto using True_sep_1, True_sep_2. Qed.
Global Instance sep_True : RightId (⊣⊢) True%I (@uPred_sep M).
Proof. by intros P; rewrite comm left_id. Qed.
Lemma sep_elim_l P Q : P ∗ Q ⊢ P.
Proof. by rewrite (True_intro Q) right_id. Qed.
Lemma sep_elim_r P Q : P ∗ Q ⊢ Q.
Proof. by rewrite (comm (∗))%I; apply sep_elim_l. Qed.
Lemma sep_elim_l' P Q R : (P ⊢ R) → P ∗ Q ⊢ R.
Proof. intros ->; apply sep_elim_l. Qed.
Lemma sep_elim_r' P Q R : (Q ⊢ R) → P ∗ Q ⊢ R.
Proof. intros ->; apply sep_elim_r. Qed.
Hint Resolve sep_elim_l' sep_elim_r'.
Lemma sep_intro_True_l P Q R : P%I → (R ⊢ Q) → R ⊢ P ∗ Q.
Proof. by intros; rewrite -(left_id True%I uPred_sep R); apply sep_mono. Qed.
Lemma sep_intro_True_r P Q R : (R ⊢ P) → Q%I → R ⊢ P ∗ Q.
Proof. by intros; rewrite -(right_id True%I uPred_sep R); apply sep_mono. Qed.
Lemma sep_elim_True_l P Q R : P → (P ∗ R ⊢ Q) → R ⊢ Q.
Proof. by intros HP; rewrite -HP left_id. Qed.
Lemma sep_elim_True_r P Q R : P → (R ∗ P ⊢ Q) → R ⊢ Q.
Proof. by intros HP; rewrite -HP right_id. Qed.
Lemma wand_intro_l P Q R : (Q ∗ P ⊢ R) → P ⊢ Q -∗ R.
Proof. rewrite comm; apply wand_intro_r. Qed.
Lemma wand_elim_l P Q : (P -∗ Q) ∗ P ⊢ Q.
Proof. by apply wand_elim_l'. Qed.
Lemma wand_elim_r P Q : P ∗ (P -∗ Q) ⊢ Q.
Proof. rewrite (comm _ P); apply wand_elim_l. Qed.
Lemma wand_elim_r' P Q R : (Q ⊢ P -∗ R) → P ∗ Q ⊢ R.
Proof. intros ->; apply wand_elim_r. Qed.
Lemma wand_apply P Q R S : (P ⊢ Q -∗ R) → (S ⊢ P ∗ Q) → S ⊢ R.
Proof. intros HR%wand_elim_l' HQ. by rewrite HQ. Qed.
Lemma wand_frame_l P Q R : (Q -∗ R) ⊢ P ∗ Q -∗ P ∗ R.
Proof. apply wand_intro_l. rewrite -assoc. apply sep_mono_r, wand_elim_r. Qed.
Lemma wand_frame_r P Q R : (Q -∗ R) ⊢ Q ∗ P -∗ R ∗ P.
Proof.
  apply wand_intro_l. rewrite ![(_ ∗ P)%I]comm -assoc.
  apply sep_mono_r, wand_elim_r.
Qed.
Lemma wand_diag P : (P -∗ P) ⊣⊢ True.
Proof. apply (anti_symm _); auto. apply wand_intro_l; by rewrite right_id. Qed.
Lemma wand_True P : (True -∗ P) ⊣⊢ P.
Proof.
  apply (anti_symm _); last by auto using wand_intro_l.
  eapply sep_elim_True_l; last by apply wand_elim_r. done.
Qed.
Lemma wand_entails P Q : (P -∗ Q)%I → P ⊢ Q.
Proof.
  intros HPQ. eapply sep_elim_True_r; first exact: HPQ. by rewrite wand_elim_r.
Qed.
Lemma entails_wand P Q : (P ⊢ Q) → (P -∗ Q)%I.
Proof. intro. apply wand_intro_l. auto. Qed.
Lemma wand_curry P Q R : (P -∗ Q -∗ R) ⊣⊢ (P ∗ Q -∗ R).
Proof.
  apply (anti_symm _).
  - apply wand_intro_l. by rewrite (comm _ P) -assoc !wand_elim_r.
  - do 2 apply wand_intro_l. by rewrite assoc (comm _ Q) wand_elim_r.
Qed.

Lemma sep_and P Q : (P ∗ Q) ⊢ (P ∧ Q).
Proof. auto. Qed.
Lemma impl_wand_1 P Q : (P → Q) ⊢ P -∗ Q.
Proof. apply wand_intro_r, impl_elim with P; auto. Qed.
Lemma pure_elim_sep_l φ Q R : (φ → Q ⊢ R) → ⌜φ⌝ ∗ Q ⊢ R.
Proof. intros; apply pure_elim with φ; eauto. Qed.
Lemma pure_elim_sep_r φ Q R : (φ → Q ⊢ R) → Q ∗ ⌜φ⌝ ⊢ R.
Proof. intros; apply pure_elim with φ; eauto. Qed.

Global Instance sep_False : LeftAbsorb (⊣⊢) False%I (@uPred_sep M).
Proof. intros P; apply (anti_symm _); auto. Qed.
Global Instance False_sep : RightAbsorb (⊣⊢) False%I (@uPred_sep M).
Proof. intros P; apply (anti_symm _); auto. Qed.

Lemma entails_equiv_and P Q : (P ⊣⊢ Q ∧ P) ↔ (P ⊢ Q).
Proof. split. by intros ->; auto. intros; apply (anti_symm _); auto. Qed.
Lemma sep_and_l P Q R : P ∗ (Q ∧ R) ⊢ (P ∗ Q) ∧ (P ∗ R).
Proof. auto. Qed.
Lemma sep_and_r P Q R : (P ∧ Q) ∗ R ⊢ (P ∗ R) ∧ (Q ∗ R).
Proof. auto. Qed.
Lemma sep_or_l P Q R : P ∗ (Q ∨ R) ⊣⊢ (P ∗ Q) ∨ (P ∗ R).
Proof.
  apply (anti_symm (⊢)); last by eauto 8.
  apply wand_elim_r', or_elim; apply wand_intro_l; auto.
Qed.
Lemma sep_or_r P Q R : (P ∨ Q) ∗ R ⊣⊢ (P ∗ R) ∨ (Q ∗ R).
Proof. by rewrite -!(comm _ R) sep_or_l. Qed.
Lemma sep_exist_l {A} P (Ψ : A → uPred M) : P ∗ (∃ a, Ψ a) ⊣⊢ ∃ a, P ∗ Ψ a.
Proof.
  intros; apply (anti_symm (⊢)).
  - apply wand_elim_r', exist_elim=>a. apply wand_intro_l.
    by rewrite -(exist_intro a).
  - apply exist_elim=> a; apply sep_mono; auto using exist_intro.
Qed.
Lemma sep_exist_r {A} (Φ: A → uPred M) Q: (∃ a, Φ a) ∗ Q ⊣⊢ ∃ a, Φ a ∗ Q.
Proof. setoid_rewrite (comm _ _ Q); apply sep_exist_l. Qed.
Lemma sep_forall_l {A} P (Ψ : A → uPred M) : P ∗ (∀ a, Ψ a) ⊢ ∀ a, P ∗ Ψ a.
Proof. by apply forall_intro=> a; rewrite forall_elim. Qed.
Lemma sep_forall_r {A} (Φ : A → uPred M) Q : (∀ a, Φ a) ∗ Q ⊢ ∀ a, Φ a ∗ Q.
Proof. by apply forall_intro=> a; rewrite forall_elim. Qed.

(* Plainness modality *)
Global Instance plainly_mono' : Proper ((⊢) ==> (⊢)) (@uPred_plainly M).
Proof. intros P Q; apply plainly_mono. Qed.
Global Instance naugth_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢)) (@uPred_plainly M).
Proof. intros P Q; apply plainly_mono. Qed.

Lemma plainly_elim P : ■ P ⊢ P.
Proof. by rewrite plainly_elim' persistently_elim. Qed.
Hint Resolve plainly_mono plainly_elim.
Lemma plainly_intro' P Q : (■ P ⊢ Q) → ■ P ⊢ ■ Q.
Proof. intros <-. apply plainly_idemp. Qed.
Lemma plainly_idemp P : ■ ■ P ⊣⊢ ■ P.
Proof. apply (anti_symm _); auto using plainly_idemp. Qed.

Lemma persistently_plainly P : □ ■ P ⊣⊢ ■ P.
Proof.
  apply (anti_symm _); auto using persistently_elim.
  by rewrite -plainly_elim' plainly_idemp.
Qed.
Lemma plainly_persistently P : ■ □ P ⊣⊢ ■ P.
Proof.
  apply (anti_symm _); auto using plainly_mono, persistently_elim.
  by rewrite -plainly_elim' plainly_idemp.
Qed.

Lemma plainly_pure φ : ■ ⌜φ⌝ ⊣⊢ ⌜φ⌝.
Proof.
  apply (anti_symm _); auto.
  apply pure_elim'=> Hφ.
  trans (∀ x : False, ■ True : uPred M)%I; [by apply forall_intro|].
  rewrite plainly_forall_2. auto using plainly_mono, pure_intro.
Qed.
Lemma plainly_forall {A} (Ψ : A → uPred M) : (■ ∀ a, Ψ a) ⊣⊢ (∀ a, ■ Ψ a).
Proof.
  apply (anti_symm _); auto using plainly_forall_2.
  apply forall_intro=> x. by rewrite (forall_elim x).
Qed.
Lemma plainly_exist {A} (Ψ : A → uPred M) : (■ ∃ a, Ψ a) ⊣⊢ (∃ a, ■ Ψ a).
Proof.
  apply (anti_symm _); auto using plainly_exist_1.
  apply exist_elim=> x. by rewrite (exist_intro x).
Qed.
Lemma plainly_and P Q : ■ (P ∧ Q) ⊣⊢ ■ P ∧ ■ Q.
Proof. rewrite !and_alt plainly_forall. by apply forall_proper=> -[]. Qed.
Lemma plainly_or P Q : ■ (P ∨ Q) ⊣⊢ ■ P ∨ ■ Q.
Proof. rewrite !or_alt plainly_exist. by apply exist_proper=> -[]. Qed.
Lemma plainly_impl P Q : ■ (P → Q) ⊢ ■ P → ■ Q.
Proof.
  apply impl_intro_l; rewrite -plainly_and.
  apply plainly_mono, impl_elim with P; auto.
Qed.
Lemma plainly_internal_eq {A:ofeT} (a b : A) : ■ (a ≡ b) ⊣⊢ a ≡ b.
Proof.
  apply (anti_symm (⊢)); auto using persistently_elim.
  rewrite {1}(internal_eq_rewrite a b (λ b, ■ (a ≡ b))%I ltac:(solve_proper)).
  by rewrite -internal_eq_refl plainly_pure True_impl.
Qed.

Lemma plainly_and_sep_l_1 P Q : ■ P ∧ Q ⊢ ■ P ∗ Q.
Proof. by rewrite -persistently_plainly persistently_and_sep_l_1. Qed.
Lemma plainly_and_sep_l' P Q : ■ P ∧ Q ⊣⊢ ■ P ∗ Q.
Proof. apply (anti_symm (⊢)); auto using plainly_and_sep_l_1. Qed.
Lemma plainly_and_sep_r' P Q : P ∧ ■ Q ⊣⊢ P ∗ ■ Q.
Proof. by rewrite !(comm _ P) plainly_and_sep_l'. Qed.
Lemma plainly_sep_dup' P : ■ P ⊣⊢ ■ P ∗ ■ P.
Proof. by rewrite -plainly_and_sep_l' idemp. Qed.

Lemma plainly_and_sep P Q : ■ (P ∧ Q) ⊣⊢ ■ (P ∗ Q).
Proof.
  apply (anti_symm (⊢)); auto.
  rewrite -{1}plainly_idemp plainly_and plainly_and_sep_l'; auto.
Qed.
Lemma plainly_sep P Q : ■ (P ∗ Q) ⊣⊢ ■ P ∗ ■ Q.
Proof. by rewrite -plainly_and_sep -plainly_and_sep_l' plainly_and. Qed.

Lemma plainly_wand P Q : ■ (P -∗ Q) ⊢ ■ P -∗ ■ Q.
Proof. by apply wand_intro_r; rewrite -plainly_sep wand_elim_l. Qed.
Lemma plainly_impl_wand P Q : ■ (P → Q) ⊣⊢ ■ (P -∗ Q).
Proof.
  apply (anti_symm (⊢)); [by rewrite -impl_wand_1|].
  apply plainly_intro', impl_intro_r.
  by rewrite plainly_and_sep_l' plainly_elim wand_elim_l.
Qed.
Lemma impl_wand_plainly P Q : (■ P → Q) ⊣⊢ (■ P -∗ Q).
Proof.
  apply (anti_symm (⊢)); [by rewrite -impl_wand_1|].
  apply impl_intro_l. by rewrite plainly_and_sep_l' wand_elim_r.
Qed.
Lemma plainly_entails_l' P Q : (P ⊢ ■ Q) → P ⊢ ■ Q ∗ P.
Proof. intros; rewrite -plainly_and_sep_l'; auto. Qed.
Lemma plainly_entails_r' P Q : (P ⊢ ■ Q) → P ⊢ P ∗ ■ Q.
Proof. intros; rewrite -plainly_and_sep_r'; auto. Qed.

Lemma plainly_laterN n P : ■ ▷^n P ⊣⊢ ▷^n ■ P.
Proof. induction n as [|n IH]; simpl; auto. by rewrite plainly_later IH. Qed.

(* Always derived *)
Hint Resolve persistently_mono persistently_elim.
Global Instance persistently_mono' : Proper ((⊢) ==> (⊢)) (@uPred_persistently M).
Proof. intros P Q; apply persistently_mono. Qed.
Global Instance persistently_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢)) (@uPred_persistently M).
Proof. intros P Q; apply persistently_mono. Qed.

Lemma persistently_intro' P Q : (□ P ⊢ Q) → □ P ⊢ □ Q.
Proof. intros <-. apply persistently_idemp_2. Qed.
Lemma persistently_idemp P : □ □ P ⊣⊢ □ P.
Proof. apply (anti_symm _); auto using persistently_idemp_2. Qed.

Lemma persistently_pure φ : □ ⌜φ⌝ ⊣⊢ ⌜φ⌝.
Proof. by rewrite -plainly_pure persistently_plainly. Qed.
Lemma persistently_forall {A} (Ψ : A → uPred M) : (□ ∀ a, Ψ a) ⊣⊢ (∀ a, □ Ψ a).
Proof.
  apply (anti_symm _); auto using persistently_forall_2.
  apply forall_intro=> x. by rewrite (forall_elim x).
Qed.
Lemma persistently_exist {A} (Ψ : A → uPred M) : (□ ∃ a, Ψ a) ⊣⊢ (∃ a, □ Ψ a).
Proof.
  apply (anti_symm _); auto using persistently_exist_1.
  apply exist_elim=> x. by rewrite (exist_intro x).
Qed.
Lemma persistently_and P Q : □ (P ∧ Q) ⊣⊢ □ P ∧ □ Q.
Proof. rewrite !and_alt persistently_forall. by apply forall_proper=> -[]. Qed.
Lemma persistently_or P Q : □ (P ∨ Q) ⊣⊢ □ P ∨ □ Q.
Proof. rewrite !or_alt persistently_exist. by apply exist_proper=> -[]. Qed.
Lemma persistently_impl P Q : □ (P → Q) ⊢ □ P → □ Q.
Proof.
  apply impl_intro_l; rewrite -persistently_and.
  apply persistently_mono, impl_elim with P; auto.
Qed.
Lemma persistently_internal_eq {A:ofeT} (a b : A) : □ (a ≡ b) ⊣⊢ a ≡ b.
Proof. by rewrite -plainly_internal_eq persistently_plainly. Qed.

Lemma persistently_and_sep_l P Q : □ P ∧ Q ⊣⊢ □ P ∗ Q.
Proof. apply (anti_symm (⊢)); auto using persistently_and_sep_l_1. Qed.
Lemma persistently_and_sep_r P Q : P ∧ □ Q ⊣⊢ P ∗ □ Q.
Proof. by rewrite !(comm _ P) persistently_and_sep_l. Qed.
Lemma persistently_sep_dup P : □ P ⊣⊢ □ P ∗ □ P.
Proof. by rewrite -persistently_and_sep_l idemp. Qed.

Lemma persistently_and_sep P Q : □ (P ∧ Q) ⊣⊢ □ (P ∗ Q).
Proof.
  apply (anti_symm (⊢)); auto.
  rewrite -{1}persistently_idemp persistently_and persistently_and_sep_l; auto.
Qed.
Lemma persistently_sep P Q : □ (P ∗ Q) ⊣⊢ □ P ∗ □ Q.
Proof. by rewrite -persistently_and_sep -persistently_and_sep_l persistently_and. Qed.

Lemma persistently_wand P Q : □ (P -∗ Q) ⊢ □ P -∗ □ Q.
Proof. by apply wand_intro_r; rewrite -persistently_sep wand_elim_l. Qed.
Lemma persistently_impl_wand P Q : □ (P → Q) ⊣⊢ □ (P -∗ Q).
Proof.
  apply (anti_symm (⊢)); [by rewrite -impl_wand_1|].
  apply persistently_intro', impl_intro_r.
  by rewrite persistently_and_sep_l persistently_elim wand_elim_l.
Qed.
Lemma impl_wand_persistently P Q : (□ P → Q) ⊣⊢ (□ P -∗ Q).
Proof.
  apply (anti_symm (⊢)); [by rewrite -impl_wand_1|].
  apply impl_intro_l. by rewrite persistently_and_sep_l wand_elim_r.
Qed.
Lemma persistently_entails_l P Q : (P ⊢ □ Q) → P ⊢ □ Q ∗ P.
Proof. intros; rewrite -persistently_and_sep_l; auto. Qed.
Lemma persistently_entails_r P Q : (P ⊢ □ Q) → P ⊢ P ∗ □ Q.
Proof. intros; rewrite -persistently_and_sep_r; auto. Qed.

Lemma persistently_laterN n P : □ ▷^n P ⊣⊢ ▷^n □ P.
Proof. induction n as [|n IH]; simpl; auto. by rewrite persistently_later IH. Qed.

Lemma wand_alt P Q : (P -∗ Q) ⊣⊢ ∃ R, R ∗ □ (P ∗ R → Q).
Proof.
  apply (anti_symm (⊢)).
  - rewrite -(right_id True%I uPred_sep (P -∗ Q)%I) -(exist_intro (P -∗ Q)%I).
    apply sep_mono_r. rewrite -persistently_pure. apply persistently_mono, impl_intro_l.
    by rewrite wand_elim_r right_id.
  - apply exist_elim=> R. apply wand_intro_l. rewrite assoc -persistently_and_sep_r.
    by rewrite persistently_elim impl_elim_r.
Qed.
Lemma impl_alt P Q : (P → Q) ⊣⊢ ∃ R, R ∧ □ (P ∧ R -∗ Q).
Proof.
  apply (anti_symm (⊢)).
  - rewrite -(right_id True%I uPred_and (P → Q)%I) -(exist_intro (P → Q)%I).
    apply and_mono_r. rewrite -persistently_pure. apply persistently_mono, wand_intro_l.
    by rewrite impl_elim_r right_id.
  - apply exist_elim=> R. apply impl_intro_l. rewrite assoc persistently_and_sep_r.
    by rewrite persistently_elim wand_elim_r.
Qed.

(* Later derived *)
Hint Resolve later_mono.
Global Instance later_mono' : Proper ((⊢) ==> (⊢)) (@uPred_later M).
Proof. intros P Q; apply later_mono. Qed.
Global Instance later_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢)) (@uPred_later M).
Proof. intros P Q; apply later_mono. Qed.

Lemma later_intro P : P ⊢ ▷ P.
Proof.
  rewrite -(and_elim_l (▷ P) P) -(löb (▷ P ∧ P)).
  apply impl_intro_l. by rewrite {1}(and_elim_r (▷ P)).
Qed.

Lemma later_True : ▷ True ⊣⊢ True.
Proof. apply (anti_symm (⊢)); auto using later_intro. Qed.
Lemma later_forall {A} (Φ : A → uPred M) : (▷ ∀ a, Φ a) ⊣⊢ (∀ a, ▷ Φ a).
Proof.
  apply (anti_symm _); auto using later_forall_2.
  apply forall_intro=> x. by rewrite (forall_elim x).
Qed.
Lemma later_exist_2 {A} (Φ : A → uPred M) : (∃ a, ▷ Φ a) ⊢ ▷ (∃ a, Φ a).
Proof. apply exist_elim; eauto using exist_intro. Qed.
Lemma later_exist `{Inhabited A} (Φ : A → uPred M) :
  ▷ (∃ a, Φ a) ⊣⊢ (∃ a, ▷ Φ a).
Proof.
  apply: anti_symm; [|apply later_exist_2].
  rewrite later_exist_false. apply or_elim; last done.
  rewrite -(exist_intro inhabitant); auto.
Qed.
Lemma later_and P Q : ▷ (P ∧ Q) ⊣⊢ ▷ P ∧ ▷ Q.
Proof. rewrite !and_alt later_forall. by apply forall_proper=> -[]. Qed.
Lemma later_or P Q : ▷ (P ∨ Q) ⊣⊢ ▷ P ∨ ▷ Q.
Proof. rewrite !or_alt later_exist. by apply exist_proper=> -[]. Qed.
Lemma later_impl P Q : ▷ (P → Q) ⊢ ▷ P → ▷ Q.
Proof. apply impl_intro_l; rewrite -later_and; eauto using impl_elim. Qed.
Lemma later_wand P Q : ▷ (P -∗ Q) ⊢ ▷ P -∗ ▷ Q.
Proof. apply wand_intro_r; rewrite -later_sep; eauto using wand_elim_l. Qed.
Lemma later_iff P Q : ▷ (P ↔ Q) ⊢ ▷ P ↔ ▷ Q.
Proof. by rewrite /uPred_iff later_and !later_impl. Qed.

(* Iterated later modality *)
Global Instance laterN_ne m : NonExpansive (@uPred_laterN M m).
Proof. induction m; simpl. by intros ???. solve_proper. Qed.
Global Instance laterN_proper m :
  Proper ((⊣⊢) ==> (⊣⊢)) (@uPred_laterN M m) := ne_proper _.

Lemma laterN_0 P : ▷^0 P ⊣⊢ P.
Proof. done. Qed.
Lemma later_laterN n P : ▷^(S n) P ⊣⊢ ▷ ▷^n P.
Proof. done. Qed.
Lemma laterN_later n P : ▷^(S n) P ⊣⊢ ▷^n ▷ P.
Proof. induction n; f_equiv/=; auto. Qed.
Lemma laterN_plus n1 n2 P : ▷^(n1 + n2) P ⊣⊢ ▷^n1 ▷^n2 P.
Proof. induction n1; f_equiv/=; auto. Qed.
Lemma laterN_le n1 n2 P : n1 ≤ n2 → ▷^n1 P ⊢ ▷^n2 P.
Proof. induction 1; simpl; by rewrite -?later_intro. Qed.

Lemma laterN_mono n P Q : (P ⊢ Q) → ▷^n P ⊢ ▷^n Q.
Proof. induction n; simpl; auto. Qed.
Global Instance laterN_mono' n : Proper ((⊢) ==> (⊢)) (@uPred_laterN M n).
Proof. intros P Q; apply laterN_mono. Qed.
Global Instance laterN_flip_mono' n :
  Proper (flip (⊢) ==> flip (⊢)) (@uPred_laterN M n).
Proof. intros P Q; apply laterN_mono. Qed.

Lemma laterN_intro n P : P ⊢ ▷^n P.
Proof. induction n as [|n IH]; simpl; by rewrite -?later_intro. Qed.

Lemma laterN_True n : ▷^n True ⊣⊢ True.
Proof. apply (anti_symm (⊢)); auto using laterN_intro. Qed.
Lemma laterN_forall {A} n (Φ : A → uPred M) : (▷^n ∀ a, Φ a) ⊣⊢ (∀ a, ▷^n Φ a).
Proof. induction n as [|n IH]; simpl; rewrite -?later_forall ?IH; auto. Qed.
Lemma laterN_exist_2 {A} n (Φ : A → uPred M) : (∃ a, ▷^n Φ a) ⊢ ▷^n (∃ a, Φ a).
Proof. apply exist_elim; eauto using exist_intro, laterN_mono. Qed.
Lemma laterN_exist `{Inhabited A} n (Φ : A → uPred M) :
  (▷^n ∃ a, Φ a) ⊣⊢ ∃ a, ▷^n Φ a.
Proof. induction n as [|n IH]; simpl; rewrite -?later_exist ?IH; auto. Qed.
Lemma laterN_and n P Q : ▷^n (P ∧ Q) ⊣⊢ ▷^n P ∧ ▷^n Q.
Proof. induction n as [|n IH]; simpl; rewrite -?later_and ?IH; auto. Qed.
Lemma laterN_or n P Q : ▷^n (P ∨ Q) ⊣⊢ ▷^n P ∨ ▷^n Q.
Proof. induction n as [|n IH]; simpl; rewrite -?later_or ?IH; auto. Qed.
Lemma laterN_impl n P Q : ▷^n (P → Q) ⊢ ▷^n P → ▷^n Q.
Proof.
  apply impl_intro_l; rewrite -laterN_and; eauto using impl_elim, laterN_mono.
Qed.
Lemma laterN_sep n P Q : ▷^n (P ∗ Q) ⊣⊢ ▷^n P ∗ ▷^n Q.
Proof. induction n as [|n IH]; simpl; rewrite -?later_sep ?IH; auto. Qed.
Lemma laterN_wand n P Q : ▷^n (P -∗ Q) ⊢ ▷^n P -∗ ▷^n Q.
Proof.
  apply wand_intro_r; rewrite -laterN_sep; eauto using wand_elim_l,laterN_mono.
Qed.
Lemma laterN_iff n P Q : ▷^n (P ↔ Q) ⊢ ▷^n P ↔ ▷^n Q.
Proof. by rewrite /uPred_iff laterN_and !laterN_impl. Qed.

(* Conditional persistently *)
Global Instance persistently_if_ne p : NonExpansive (@uPred_persistently_if M p).
Proof. solve_proper. Qed.
Global Instance persistently_if_proper p : Proper ((⊣⊢) ==> (⊣⊢)) (@uPred_persistently_if M p).
Proof. solve_proper. Qed.
Global Instance persistently_if_mono p : Proper ((⊢) ==> (⊢)) (@uPred_persistently_if M p).
Proof. solve_proper. Qed.

Lemma persistently_if_elim p P : □?p P ⊢ P.
Proof. destruct p; simpl; auto using persistently_elim. Qed.
Lemma persistently_elim_if p P : □ P ⊢ □?p P.
Proof. destruct p; simpl; auto using persistently_elim. Qed.

Lemma persistently_if_pure p φ : □?p ⌜φ⌝ ⊣⊢ ⌜φ⌝.
Proof. destruct p; simpl; auto using persistently_pure. Qed.
Lemma persistently_if_and p P Q : □?p (P ∧ Q) ⊣⊢ □?p P ∧ □?p Q.
Proof. destruct p; simpl; auto using persistently_and. Qed.
Lemma persistently_if_or p P Q : □?p (P ∨ Q) ⊣⊢ □?p P ∨ □?p Q.
Proof. destruct p; simpl; auto using persistently_or. Qed.
Lemma persistently_if_exist {A} p (Ψ : A → uPred M) : (□?p ∃ a, Ψ a) ⊣⊢ ∃ a, □?p Ψ a.
Proof. destruct p; simpl; auto using persistently_exist. Qed.
Lemma persistently_if_sep p P Q : □?p (P ∗ Q) ⊣⊢ □?p P ∗ □?p Q.
Proof. destruct p; simpl; auto using persistently_sep. Qed.
Lemma persistently_if_later p P : □?p ▷ P ⊣⊢ ▷ □?p P.
Proof. destruct p; simpl; auto using persistently_later. Qed.
Lemma persistently_if_laterN p n P : □?p ▷^n P ⊣⊢ ▷^n □?p P.
Proof. destruct p; simpl; auto using persistently_laterN. Qed.

(* True now *)
Global Instance except_0_ne : NonExpansive (@uPred_except_0 M).
Proof. solve_proper. Qed.
Global Instance except_0_proper : Proper ((⊣⊢) ==> (⊣⊢)) (@uPred_except_0 M).
Proof. solve_proper. Qed.
Global Instance except_0_mono' : Proper ((⊢) ==> (⊢)) (@uPred_except_0 M).
Proof. solve_proper. Qed.
Global Instance except_0_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢)) (@uPred_except_0 M).
Proof. solve_proper. Qed.

Lemma except_0_intro P : P ⊢ ◇ P.
Proof. rewrite /uPred_except_0; auto. Qed.
Lemma except_0_mono P Q : (P ⊢ Q) → ◇ P ⊢ ◇ Q.
Proof. by intros ->. Qed.
Lemma except_0_idemp P : ◇ ◇ P ⊢ ◇ P.
Proof. rewrite /uPred_except_0; auto. Qed.

Lemma except_0_True : ◇ True ⊣⊢ True.
Proof. rewrite /uPred_except_0. apply (anti_symm _); auto. Qed.
Lemma except_0_or P Q : ◇ (P ∨ Q) ⊣⊢ ◇ P ∨ ◇ Q.
Proof. rewrite /uPred_except_0. apply (anti_symm _); auto. Qed.
Lemma except_0_and P Q : ◇ (P ∧ Q) ⊣⊢ ◇ P ∧ ◇ Q.
Proof. by rewrite /uPred_except_0 or_and_l. Qed.
Lemma except_0_sep P Q : ◇ (P ∗ Q) ⊣⊢ ◇ P ∗ ◇ Q.
Proof.
  rewrite /uPred_except_0. apply (anti_symm _).
  - apply or_elim; last by auto.
    by rewrite -!or_intro_l -persistently_pure -persistently_later -persistently_sep_dup.
  - rewrite sep_or_r sep_elim_l sep_or_l; auto.
Qed.
Lemma except_0_forall {A} (Φ : A → uPred M) : ◇ (∀ a, Φ a) ⊣⊢ ∀ a, ◇ Φ a.
Proof.
  apply (anti_symm _).
  { apply forall_intro=> a. by rewrite (forall_elim a). }
  trans (▷ (∀ a : A, Φ a) ∧ (∀ a : A, ◇ Φ a))%I.
  { apply and_intro, reflexivity. rewrite later_forall. apply forall_mono=> a.
    apply or_elim; auto using later_intro. }
  rewrite later_false_excluded_middle and_or_r. apply or_elim.
  { rewrite and_elim_l. apply or_intro_l. }
  apply or_intro_r', forall_intro=> a. rewrite !(forall_elim a).
  by rewrite /uPred_except_0 and_or_l impl_elim_l and_elim_r idemp.
Qed.
Lemma except_0_exist_2 {A} (Φ : A → uPred M) : (∃ a, ◇ Φ a) ⊢ ◇ ∃ a, Φ a.
Proof. apply exist_elim=> a. by rewrite (exist_intro a). Qed.
Lemma except_0_exist `{Inhabited A} (Φ : A → uPred M) :
  ◇ (∃ a, Φ a) ⊣⊢ (∃ a, ◇ Φ a).
Proof.
  apply (anti_symm _); [|by apply except_0_exist_2]. apply or_elim.
  - rewrite -(exist_intro inhabitant). by apply or_intro_l.
  - apply exist_mono=> a. apply except_0_intro.
Qed.
Lemma except_0_later P : ◇ ▷ P ⊢ ▷ P.
Proof. by rewrite /uPred_except_0 -later_or False_or. Qed.
Lemma except_0_persistently P : ◇ □ P ⊣⊢ □ ◇ P.
Proof. by rewrite /uPred_except_0 persistently_or persistently_later persistently_pure. Qed.
Lemma except_0_persistently_if p P : ◇ □?p P ⊣⊢ □?p ◇ P.
Proof. destruct p; simpl; auto using except_0_persistently. Qed.
Lemma except_0_plainly P : ◇ ■ P ⊣⊢ ■ ◇ P.
Proof. by rewrite /uPred_except_0 plainly_or plainly_later plainly_pure. Qed.
Lemma except_0_frame_l P Q : P ∗ ◇ Q ⊢ ◇ (P ∗ Q).
Proof. by rewrite {1}(except_0_intro P) except_0_sep. Qed.
Lemma except_0_frame_r P Q : ◇ P ∗ Q ⊢ ◇ (P ∗ Q).
Proof. by rewrite {1}(except_0_intro Q) except_0_sep. Qed.

(* Own and valid derived *)
Lemma persistently_ownM (a : M) : CoreId a → □ uPred_ownM a ⊣⊢ uPred_ownM a.
Proof.
  intros; apply (anti_symm _); first by apply:persistently_elim.
  by rewrite {1}persistently_ownM_core core_id_core.
Qed.
Lemma ownM_invalid (a : M) : ¬ ✓{0} a → uPred_ownM a ⊢ False.
Proof. by intros; rewrite ownM_valid cmra_valid_elim. Qed.
Global Instance ownM_mono : Proper (flip (≼) ==> (⊢)) (@uPred_ownM M).
Proof. intros a b [b' ->]. rewrite ownM_op. eauto. Qed.
Lemma ownM_unit' : uPred_ownM ε ⊣⊢ True.
Proof. apply (anti_symm _); first by auto. apply ownM_unit. Qed.
Lemma plainly_cmra_valid {A : cmraT} (a : A) : ■ ✓ a ⊣⊢ ✓ a.
Proof. apply (anti_symm _); auto using plainly_elim, plainly_cmra_valid_1. Qed.
Lemma persistently_cmra_valid {A : cmraT} (a : A) : □ ✓ a ⊣⊢ ✓ a.
Proof. by rewrite -plainly_cmra_valid persistently_plainly. Qed.

(** * Derived rules *)
Global Instance bupd_mono' : Proper ((⊢) ==> (⊢)) (@uPred_bupd M).
Proof. intros P Q; apply bupd_mono. Qed.
Global Instance bupd_flip_mono' : Proper (flip (⊢) ==> flip (⊢)) (@uPred_bupd M).
Proof. intros P Q; apply bupd_mono. Qed.
Lemma bupd_frame_l R Q : (R ∗ |==> Q) ==∗ R ∗ Q.
Proof. rewrite !(comm _ R); apply bupd_frame_r. Qed.
Lemma bupd_wand_l P Q : (P -∗ Q) ∗ (|==> P) ==∗ Q.
Proof. by rewrite bupd_frame_l wand_elim_l. Qed.
Lemma bupd_wand_r P Q : (|==> P) ∗ (P -∗ Q) ==∗ Q.
Proof. by rewrite bupd_frame_r wand_elim_r. Qed.
Lemma bupd_sep P Q : (|==> P) ∗ (|==> Q) ==∗ P ∗ Q.
Proof. by rewrite bupd_frame_r bupd_frame_l bupd_trans. Qed.
Lemma bupd_ownM_update x y : x ~~> y → uPred_ownM x ⊢ |==> uPred_ownM y.
Proof.
  intros; rewrite (bupd_ownM_updateP _ (y =)); last by apply cmra_update_updateP.
  by apply bupd_mono, exist_elim=> y'; apply pure_elim_l=> ->.
Qed.
Lemma except_0_bupd P : ◇ (|==> P) ⊢ (|==> ◇ P).
Proof.
  rewrite /uPred_except_0. apply or_elim; auto using bupd_mono.
  by rewrite -bupd_intro -or_intro_l.
Qed.

Global Instance Timeless_proper : Proper ((≡) ==> iff) (@Timeless M).
Proof. solve_proper. Qed.
Global Instance pure_timeless φ : Timeless (⌜φ⌝ : uPred M)%I.
Proof.
  rewrite /Timeless pure_alt later_exist_false. by setoid_rewrite later_True.
Qed.
Global Instance valid_timeless {A : cmraT} `{CmraDiscrete A} (a : A) :
  Timeless (✓ a : uPred M)%I.
Proof. rewrite /Timeless !discrete_valid. apply (timelessP _). Qed.
Global Instance and_timeless P Q: Timeless P → Timeless Q → Timeless (P ∧ Q).
Proof. intros; rewrite /Timeless except_0_and later_and; auto. Qed.
Global Instance or_timeless P Q : Timeless P → Timeless Q → Timeless (P ∨ Q).
Proof. intros; rewrite /Timeless except_0_or later_or; auto. Qed.
Global Instance impl_timeless P Q : Timeless Q → Timeless (P → Q).
Proof.
  rewrite /Timeless=> HQ. rewrite later_false_excluded_middle.
  apply or_mono, impl_intro_l; first done.
  rewrite -{2}(löb Q); apply impl_intro_l.
  rewrite HQ /uPred_except_0 !and_or_r. apply or_elim; last auto.
  by rewrite assoc (comm _ _ P) -assoc !impl_elim_r.
Qed.
Global Instance sep_timeless P Q: Timeless P → Timeless Q → Timeless (P ∗ Q).
Proof. intros; rewrite /Timeless except_0_sep later_sep; auto. Qed.
Global Instance wand_timeless P Q : Timeless Q → Timeless (P -∗ Q).
Proof.
  rewrite /Timeless=> HQ. rewrite later_false_excluded_middle.
  apply or_mono, wand_intro_l; first done.
  rewrite -{2}(löb Q); apply impl_intro_l.
  rewrite HQ /uPred_except_0 !and_or_r. apply or_elim; last auto.
  rewrite -(persistently_pure) -persistently_later persistently_and_sep_l.
  by rewrite assoc (comm _ _ P) -assoc -persistently_and_sep_l impl_elim_r wand_elim_r.
Qed.
Global Instance forall_timeless {A} (Ψ : A → uPred M) :
  (∀ x, Timeless (Ψ x)) → Timeless (∀ x, Ψ x).
Proof.
  rewrite /Timeless=> HQ. rewrite except_0_forall later_forall.
  apply forall_mono; auto.
Qed.
Global Instance exist_timeless {A} (Ψ : A → uPred M) :
  (∀ x, Timeless (Ψ x)) → Timeless (∃ x, Ψ x).
Proof.
  rewrite /Timeless=> ?. rewrite later_exist_false. apply or_elim.
  - rewrite /uPred_except_0; auto.
  - apply exist_elim=> x. rewrite -(exist_intro x); auto.
Qed.
Global Instance persistently_timeless P : Timeless P → Timeless (□ P).
Proof. intros; rewrite /Timeless except_0_persistently -persistently_later; auto. Qed.
Global Instance persistently_if_timeless p P : Timeless P → Timeless (□?p P).
Proof. destruct p; apply _. Qed.
Global Instance eq_timeless {A : ofeT} (a b : A) :
  Discrete a → Timeless (a ≡ b : uPred M)%I.
Proof. intros. rewrite /Timeless !discrete_eq. apply (timelessP _). Qed.
Global Instance ownM_timeless (a : M) : Discrete a → Timeless (uPred_ownM a).
Proof.
  intros ?. rewrite /Timeless later_ownM. apply exist_elim=> b.
  rewrite (timelessP (a≡b)) (except_0_intro (uPred_ownM b)) -except_0_and.
  apply except_0_mono. rewrite internal_eq_sym. apply impl_elim_r'.
  apply: internal_eq_rewrite.
Qed.
Global Instance from_option_timeless {A} P (Ψ : A → uPred M) (mx : option A) :
  (∀ x, Timeless (Ψ x)) → Timeless P → Timeless (from_option Ψ P mx).
Proof. destruct mx; apply _. Qed.

(* Derived lemmas for plainness *)
Global Instance Plain_proper : Proper ((≡) ==> iff) (@Plain M).
Proof. solve_proper. Qed.
Global Instance limit_preserving_Plain {A:ofeT} `{Cofe A} (Φ : A → uPred M) :
  NonExpansive Φ → LimitPreserving (λ x, Plain (Φ x)).
Proof. intros. apply limit_preserving_entails; solve_proper. Qed.

(* Not an instance, see the bottom of this file *)
Lemma plain_persistent P : Plain P → Persistent P.
Proof. rewrite /Plain /Persistent=> HP. by rewrite {1}HP plainly_elim'. Qed.

Lemma plainly_plainly P `{!Plain P} : ■ P ⊣⊢ P.
Proof. apply (anti_symm (⊢)); eauto. Qed.
Lemma plainly_intro P Q `{!Plain P} : (P ⊢ Q) → P ⊢ ■ Q.
Proof. rewrite -(plainly_plainly P); apply plainly_intro'. Qed.
Lemma plainly_alt P : ■ P ⊣⊢ P ≡ True.
Proof.
  apply (anti_symm (⊢)).
  - rewrite -prop_ext. apply plainly_mono, and_intro; apply impl_intro_r; auto.
  - rewrite internal_eq_sym (internal_eq_rewrite _ _ (λ P, ■ P)%I).
    by rewrite plainly_pure True_impl.
Qed.

Lemma bupd_plain P `{!Plain P} : (|==> P) ⊢ P.
Proof. by rewrite -{1}(plainly_plainly P) bupd_plainly. Qed.

(* Derived lemmas for persistence *)
Global Instance Persistent_proper : Proper ((≡) ==> iff) (@Persistent M).
Proof. solve_proper. Qed.
Global Instance limit_preserving_Persistent {A:ofeT} `{Cofe A} (Φ : A → uPred M) :
  NonExpansive Φ → LimitPreserving (λ x, Persistent (Φ x)).
Proof. intros. apply limit_preserving_entails; solve_proper. Qed.

Lemma persistent_persistently P `{!Persistent P} : □ P ⊣⊢ P.
Proof. apply (anti_symm (⊢)); auto using persistently_elim. Qed.
Lemma persistent_persistently_if p P `{!Persistent P} : □?p P ⊣⊢ P.
Proof. destruct p; simpl; auto using persistent_persistently. Qed.
Lemma persistently_intro P Q `{!Persistent P} : (P ⊢ Q) → P ⊢ □ Q.
Proof. rewrite -(persistent_persistently P); apply persistently_intro'. Qed.
Lemma and_sep_l P Q `{!Persistent P} : P ∧ Q ⊣⊢ P ∗ Q.
Proof. by rewrite -(persistent_persistently P) persistently_and_sep_l. Qed.
Lemma and_sep_r P Q `{!Persistent Q} : P ∧ Q ⊣⊢ P ∗ Q.
Proof. by rewrite -(persistent_persistently Q) persistently_and_sep_r. Qed.
Lemma sep_dup P `{!Persistent P} : P ⊣⊢ P ∗ P.
Proof. by rewrite -(persistent_persistently P) -persistently_sep_dup. Qed.
Lemma sep_entails_l P Q `{!Persistent Q} : (P ⊢ Q) → P ⊢ Q ∗ P.
Proof. by rewrite -(persistent_persistently Q); apply persistently_entails_l. Qed.
Lemma sep_entails_r P Q `{!Persistent Q} : (P ⊢ Q) → P ⊢ P ∗ Q.
Proof. by rewrite -(persistent_persistently Q); apply persistently_entails_r. Qed.
Lemma impl_wand P `{!Persistent P} Q : (P → Q) ⊣⊢ (P -∗ Q).
Proof.
  apply (anti_symm _); auto using impl_wand_1.
  apply impl_intro_l. by rewrite and_sep_l wand_elim_r.
Qed.

(* Plain *)
Global Instance pure_plain φ : Plain (⌜φ⌝ : uPred M)%I.
Proof. by rewrite /Plain plainly_pure. Qed.
Global Instance impl_plain P Q : Plain P → Plain Q → Plain (P → Q).
Proof.
  rewrite /Plain=> HP HQ.
  by rewrite {2}HP -plainly_impl_plainly -HQ plainly_elim.
Qed.
Global Instance wand_plain P Q : Plain P → Plain Q → Plain (P -∗ Q)%I.
Proof.
  rewrite /Plain=> HP HQ.
  by rewrite {2}HP -{1}(plainly_elim P) -!impl_wand_plainly -plainly_impl_plainly -HQ.
Qed.
Global Instance plainly_plain P : Plain (■ P).
Proof. by intros; apply plainly_intro'. Qed.
Global Instance persistently_plain P : Plain P → Plain (□ P).
Proof. rewrite /Plain=> HP. by rewrite {1}HP persistently_plainly plainly_persistently. Qed.
Global Instance and_plain P Q :
  Plain P → Plain Q → Plain (P ∧ Q).
Proof. by intros; rewrite /Plain plainly_and; apply and_mono. Qed.
Global Instance or_plain P Q :
  Plain P → Plain Q → Plain (P ∨ Q).
Proof. by intros; rewrite /Plain plainly_or; apply or_mono. Qed.
Global Instance sep_plain P Q :
  Plain P → Plain Q → Plain (P ∗ Q).
Proof. by intros; rewrite /Plain plainly_sep; apply sep_mono. Qed.
Global Instance forall_plain {A} (Ψ : A → uPred M) :
  (∀ x, Plain (Ψ x)) → Plain (∀ x, Ψ x).
Proof. by intros; rewrite /Plain plainly_forall; apply forall_mono. Qed.
Global Instance exist_palin {A} (Ψ : A → uPred M) :
  (∀ x, Plain (Ψ x)) → Plain (∃ x, Ψ x).
Proof. by intros; rewrite /Plain plainly_exist; apply exist_mono. Qed.
Global Instance internal_eq_plain {A : ofeT} (a b : A) :
  Plain (a ≡ b : uPred M)%I.
Proof. by intros; rewrite /Plain plainly_internal_eq. Qed.
Global Instance cmra_valid_plain {A : cmraT} (a : A) :
  Plain (✓ a : uPred M)%I.
Proof. by intros; rewrite /Plain; apply plainly_cmra_valid_1. Qed.
Global Instance later_plain P : Plain P → Plain (▷ P).
Proof. by intros; rewrite /Plain plainly_later; apply later_mono. Qed.
Global Instance except_0_plain P : Plain P → Plain (◇ P).
Proof. by intros; rewrite /Plain -except_0_plainly; apply except_0_mono. Qed.
Global Instance laterN_plain n P : Plain P → Plain (▷^n P).
Proof. induction n; apply _. Qed.
Global Instance from_option_palin {A} P (Ψ : A → uPred M) (mx : option A) :
  (∀ x, Plain (Ψ x)) → Plain P → Plain (from_option Ψ P mx).
Proof. destruct mx; apply _. Qed.

(* Persistence *)
Global Instance pure_persistent φ : Persistent (⌜φ⌝ : uPred M)%I.
Proof. by rewrite /Persistent persistently_pure. Qed.
Global Instance impl_persistent P Q :
  Plain P → Persistent Q → Persistent (P → Q).
Proof.
  rewrite /Plain /Persistent=> HP HQ.
  rewrite {2}HP -persistently_impl_plainly. by rewrite -HQ plainly_elim.
Qed.
Global Instance wand_persistent P Q :
  Plain P → Persistent Q → Persistent (P -∗ Q)%I.
Proof.
  rewrite /Plain /Persistent=> HP HQ.
  by rewrite {2}HP -{1}(plainly_elim P) -!impl_wand_plainly -persistently_impl_plainly -HQ.
Qed.
Global Instance plainly_persistent P : Persistent (■ P).
Proof. by rewrite /Persistent persistently_plainly. Qed.
Global Instance persistently_persistent P : Persistent (□ P).
Proof. by intros; apply persistently_intro'. Qed.
Global Instance and_persistent P Q :
  Persistent P → Persistent Q → Persistent (P ∧ Q).
Proof. by intros; rewrite /Persistent persistently_and; apply and_mono. Qed.
Global Instance or_persistent P Q :
  Persistent P → Persistent Q → Persistent (P ∨ Q).
Proof. by intros; rewrite /Persistent persistently_or; apply or_mono. Qed.
Global Instance sep_persistent P Q :
  Persistent P → Persistent Q → Persistent (P ∗ Q).
Proof. by intros; rewrite /Persistent persistently_sep; apply sep_mono. Qed.
Global Instance forall_persistent {A} (Ψ : A → uPred M) :
  (∀ x, Persistent (Ψ x)) → Persistent (∀ x, Ψ x).
Proof. by intros; rewrite /Persistent persistently_forall; apply forall_mono. Qed.
Global Instance exist_persistent {A} (Ψ : A → uPred M) :
  (∀ x, Persistent (Ψ x)) → Persistent (∃ x, Ψ x).
Proof. by intros; rewrite /Persistent persistently_exist; apply exist_mono. Qed.
Global Instance internal_eq_persistent {A : ofeT} (a b : A) :
  Persistent (a ≡ b : uPred M)%I.
Proof. by intros; rewrite /Persistent persistently_internal_eq. Qed.
Global Instance cmra_valid_persistent {A : cmraT} (a : A) :
  Persistent (✓ a : uPred M)%I.
Proof. by intros; rewrite /Persistent persistently_cmra_valid. Qed.
Global Instance later_persistent P : Persistent P → Persistent (▷ P).
Proof. by intros; rewrite /Persistent persistently_later; apply later_mono. Qed.
Global Instance laterN_persistent n P : Persistent P → Persistent (▷^n P).
Proof. induction n; apply _. Qed.
Global Instance except_0_persistent P : Persistent P → Persistent (◇ P).
Proof. by intros; rewrite /Persistent -except_0_persistently; apply except_0_mono. Qed.
Global Instance ownM_persistent : CoreId a → Persistent (@uPred_ownM M a).
Proof. intros. by rewrite /Persistent persistently_ownM. Qed.
Global Instance from_option_persistent {A} P (Ψ : A → uPred M) (mx : option A) :
  (∀ x, Persistent (Ψ x)) → Persistent P → Persistent (from_option Ψ P mx).
Proof. destruct mx; apply _. Qed.

(* For big ops *)
Global Instance uPred_and_monoid : Monoid (@uPred_and M) :=
  {| monoid_unit := True%I |}.
Global Instance uPred_or_monoid : Monoid (@uPred_or M) :=
  {| monoid_unit := False%I |}.
Global Instance uPred_sep_monoid : Monoid (@uPred_sep M) :=
  {| monoid_unit := True%I |}.

Global Instance uPred_persistently_and_homomorphism :
  MonoidHomomorphism uPred_and uPred_and (≡) (@uPred_persistently M).
Proof. split; [split; try apply _|]. apply persistently_and. apply persistently_pure. Qed.
Global Instance uPred_plainly_and_homomorphism :
  MonoidHomomorphism uPred_and uPred_and (≡) (@uPred_plainly M).
Proof. split; [split; try apply _|]. apply plainly_and. apply plainly_pure. Qed.
Global Instance uPred_persistently_if_and_homomorphism b :
  MonoidHomomorphism uPred_and uPred_and (≡) (@uPred_persistently_if M b).
Proof. split; [split; try apply _|]. apply persistently_if_and. apply persistently_if_pure. Qed.
Global Instance uPred_later_monoid_and_homomorphism :
  MonoidHomomorphism uPred_and uPred_and (≡) (@uPred_later M).
Proof. split; [split; try apply _|]. apply later_and. apply later_True. Qed.
Global Instance uPred_laterN_and_homomorphism n :
  MonoidHomomorphism uPred_and uPred_and (≡) (@uPred_laterN M n).
Proof. split; [split; try apply _|]. apply laterN_and. apply laterN_True. Qed.
Global Instance uPred_except_0_and_homomorphism :
  MonoidHomomorphism uPred_and uPred_and (≡) (@uPred_except_0 M).
Proof. split; [split; try apply _|]. apply except_0_and. apply except_0_True. Qed.

Global Instance uPred_persistently_or_homomorphism :
  MonoidHomomorphism uPred_or uPred_or (≡) (@uPred_persistently M).
Proof. split; [split; try apply _|]. apply persistently_or. apply persistently_pure. Qed.
Global Instance uPred_plainly_or_homomorphism :
  MonoidHomomorphism uPred_or uPred_or (≡) (@uPred_plainly M).
Proof. split; [split; try apply _|]. apply plainly_or. apply plainly_pure. Qed.
Global Instance uPred_persistently_if_or_homomorphism b :
  MonoidHomomorphism uPred_or uPred_or (≡) (@uPred_persistently_if M b).
Proof. split; [split; try apply _|]. apply persistently_if_or. apply persistently_if_pure. Qed.
Global Instance uPred_later_monoid_or_homomorphism :
  WeakMonoidHomomorphism uPred_or uPred_or (≡) (@uPred_later M).
Proof. split; try apply _. apply later_or. Qed.
Global Instance uPred_laterN_or_homomorphism n :
  WeakMonoidHomomorphism uPred_or uPred_or (≡) (@uPred_laterN M n).
Proof. split; try apply _. apply laterN_or. Qed.
Global Instance uPred_except_0_or_homomorphism :
  WeakMonoidHomomorphism uPred_or uPred_or (≡) (@uPred_except_0 M).
Proof. split; try apply _. apply except_0_or. Qed.

Global Instance uPred_persistently_sep_homomorphism :
  MonoidHomomorphism uPred_sep uPred_sep (≡) (@uPred_persistently M).
Proof. split; [split; try apply _|]. apply persistently_sep. apply persistently_pure. Qed.
Global Instance uPred_plainly_sep_homomorphism :
  MonoidHomomorphism uPred_sep uPred_sep (≡) (@uPred_plainly M).
Proof. split; [split; try apply _|]. apply plainly_sep. apply plainly_pure. Qed.
Global Instance uPred_persistently_if_sep_homomorphism b :
  MonoidHomomorphism uPred_sep uPred_sep (≡) (@uPred_persistently_if M b).
Proof. split; [split; try apply _|]. apply persistently_if_sep. apply persistently_if_pure. Qed.
Global Instance uPred_later_monoid_sep_homomorphism :
  MonoidHomomorphism uPred_sep uPred_sep (≡) (@uPred_later M).
Proof. split; [split; try apply _|]. apply later_sep. apply later_True. Qed.
Global Instance uPred_laterN_sep_homomorphism n :
  MonoidHomomorphism uPred_sep uPred_sep (≡) (@uPred_laterN M n).
Proof. split; [split; try apply _|]. apply laterN_sep. apply laterN_True. Qed.
Global Instance uPred_except_0_sep_homomorphism :
  MonoidHomomorphism uPred_sep uPred_sep (≡) (@uPred_except_0 M).
Proof. split; [split; try apply _|]. apply except_0_sep. apply except_0_True. Qed.
Global Instance uPred_ownM_sep_homomorphism :
  MonoidHomomorphism op uPred_sep (≡) (@uPred_ownM M).
Proof. split; [split; try apply _|]. apply ownM_op. apply ownM_unit'. Qed.
End derived.
End uPred.

(* When declared as an actual instance, [plain_persistent] will give cause
failing proof searches to take exponential time, as Coq will try to apply it
the instance at any node in the proof search tree.

To avoid that, we declare it using a [Hint Immediate], so that it will only be
used at the leaves of the proof search tree, i.e. when the premise of the hint
can be derived from just the current context. *)
Hint Immediate uPred.plain_persistent : typeclass_instances.
