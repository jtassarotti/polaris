From iris.base_logic.lib Require Export own.
From stdpp Require Export coPset.
From iris.base_logic.lib Require Import wsat.
From iris.algebra Require Import gmap.
From iris.base_logic Require Import big_op.
From iris.proofmode Require Import tactics classes.
Set Default Proof Using "Type".
Export invG.
Import uPred.

Program Definition fupd_def `{invG Σ}
    (E1 E2 : coPset) (P : iProp Σ) : iProp Σ :=
  (wsat ∗ ownE E1 ==∗ ◇ (wsat ∗ ownE E2 ∗ P))%I.
Definition fupd_aux : seal (@fupd_def). by eexists. Qed.
Definition fupd := unseal fupd_aux.
Definition fupd_eq : @fupd = @fupd_def := seal_eq fupd_aux.
Arguments fupd {_ _} _ _ _%I.
Instance: Params (@fupd) 4.

Notation "|={ E1 , E2 }=> Q" := (fupd E1 E2 Q)
  (at level 99, E1, E2 at level 50, Q at level 200,
   format "|={ E1 , E2 }=>  Q") : uPred_scope.
Notation "P ={ E1 , E2 }=∗ Q" := (P -∗ |={E1,E2}=> Q)%I
  (at level 99, E1,E2 at level 50, Q at level 200,
   format "P  ={ E1 , E2 }=∗  Q") : uPred_scope.
Notation "P ={ E1 , E2 }=∗ Q" := (P -∗ |={E1,E2}=> Q)
  (at level 99, E1, E2 at level 50, Q at level 200, only parsing) : stdpp_scope.

Notation "|={ E }=> Q" := (fupd E E Q)
  (at level 99, E at level 50, Q at level 200,
   format "|={ E }=>  Q") : uPred_scope.
Notation "P ={ E }=∗ Q" := (P -∗ |={E}=> Q)%I
  (at level 99, E at level 50, Q at level 200,
   format "P  ={ E }=∗  Q") : uPred_scope.
Notation "P ={ E }=∗ Q" := (P -∗ |={E}=> Q)
  (at level 99, E at level 50, Q at level 200, only parsing) : stdpp_scope.

Section fupd.
Context `{invG Σ}.
Implicit Types P Q : iProp Σ.

Global Instance fupd_ne E1 E2 : NonExpansive (@fupd Σ _ E1 E2).
Proof. rewrite fupd_eq. solve_proper. Qed.
Global Instance fupd_proper E1 E2 : Proper ((≡) ==> (≡)) (@fupd Σ _ E1 E2).
Proof. apply ne_proper, _. Qed.

Lemma fupd_intro_mask E1 E2 P : E2 ⊆ E1 → P ⊢ |={E1,E2}=> |={E2,E1}=> P.
Proof.
  intros (E1''&->&?)%subseteq_disjoint_union_L.
  rewrite fupd_eq /fupd_def ownE_op //.
  by iIntros "$ ($ & $ & HE) !> !> [$ $] !> !>" .
Qed.

Lemma except_0_fupd E1 E2 P : ◇ (|={E1,E2}=> P) ={E1,E2}=∗ P.
Proof. rewrite fupd_eq. iIntros ">H [Hw HE]". iApply "H"; by iFrame. Qed.

Lemma bupd_fupd E P : (|==> P) ={E}=∗ P.
Proof. rewrite fupd_eq /fupd_def. by iIntros ">? [$ $] !> !>". Qed.

Lemma fupd_mono E1 E2 P Q : (P ⊢ Q) → (|={E1,E2}=> P) ⊢ |={E1,E2}=> Q.
Proof.
  rewrite fupd_eq /fupd_def. iIntros (HPQ) "HP HwE".
  rewrite -HPQ. by iApply "HP".
Qed.

Lemma fupd_trans E1 E2 E3 P : (|={E1,E2}=> |={E2,E3}=> P) ⊢ |={E1,E3}=> P.
Proof.
  rewrite fupd_eq /fupd_def. iIntros "HP HwE".
  iMod ("HP" with "HwE") as ">(Hw & HE & HP)". iApply "HP"; by iFrame.
Qed.

Lemma fupd_mask_frame_r' E1 E2 Ef P :
  E1 ## Ef → (|={E1,E2}=> ⌜E2 ## Ef⌝ → P) ={E1 ∪ Ef,E2 ∪ Ef}=∗ P.
Proof.
  intros. rewrite fupd_eq /fupd_def ownE_op //. iIntros "Hvs (Hw & HE1 &HEf)".
  iMod ("Hvs" with "[Hw HE1]") as ">($ & HE2 & HP)"; first by iFrame.
  iDestruct (ownE_op' with "[HE2 HEf]") as "[? $]"; first by iFrame.
  iIntros "!> !>". by iApply "HP".
Qed.

Lemma fupd_frame_r E1 E2 P Q : (|={E1,E2}=> P) ∗ Q ={E1,E2}=∗ P ∗ Q.
Proof. rewrite fupd_eq /fupd_def. by iIntros "[HwP $]". Qed.

Lemma fupd_plain' E1 E2 E2' P Q `{!Plain P} :
  E1 ⊆ E2 →
  (Q ={E1, E2'}=∗ P) -∗ (|={E1, E2}=> Q) ={E1}=∗ (|={E1, E2}=> Q) ∗ P.
Proof.
  iIntros ((E3&->&HE)%subseteq_disjoint_union_L) "HQP HQ".
  rewrite fupd_eq /fupd_def ownE_op //. iIntros "H".
  iMod ("HQ" with "H") as ">(Hws & [HE1 HE3] & HQ)"; iModIntro.
  iAssert (◇ P)%I as "#HP".
  { by iMod ("HQP" with "HQ [$]") as "(_ & _ & HP)". }
  iMod "HP". iFrame. auto.
Qed.

Lemma later_fupd_plain E P `{!Plain P} : (▷ |={E}=> P) ={E}=∗ ▷ ◇ P.
Proof.
  rewrite fupd_eq /fupd_def. iIntros "HP [Hw HE]".
  iAssert (▷ ◇ P)%I with "[-]" as "#$"; last by iFrame.
  iNext. by iMod ("HP" with "[$]") as "(_ & _ & HP)".
Qed.

Lemma bupd_forall_pure {M : ucmraT} {A : Type} (φ: A → Prop):
  (|==> ∀ a, ⌜φ a⌝ : uPred M)%I ≡ (∀ a : A, |==> ⌜ φ a ⌝)%I.
Proof.
  intros. apply (anti_symm (⊢)).
  - iIntros "H". iIntros (a). iMod "H" as %H'. iModIntro; auto.
  - iIntros "H". iModIntro. iIntros (a). iSpecialize ("H" $! a).
    iMod "H". auto.
Qed.

Lemma and_helper P Q R:
  (P ⊢ Q) → (P ∧ Q ⊢ R) → (P ⊢ Q ∧ R).  
Proof.
  intros HPQ HPQR. iIntros "H"; iSplit.
  - by iApply HPQ.
  - rewrite -(and_idem P) {2}HPQ.
      by iApply HPQR. 
Qed.

Lemma forall_and_l {A: Type} `{INH: Inhabited A} P Φ:
  (∀ a : A, P ∧ Φ a)%I ≡ (P ∧ (∀ a, Φ a))%I.
Proof.
  apply (anti_symm (⊢)).
  - iIntros "H". iSplit.
    * destruct INH as [a]. iSpecialize ("H" $! a); auto. by rewrite and_elim_l.
    * iIntros (a). iSpecialize ("H" $! a); auto. by rewrite and_elim_r.
  - iIntros "H". iIntros (a). iSplit.
    * by rewrite and_elim_l. 
    * rewrite and_elim_r. iApply "H".
Qed.

Lemma fupd_forall_pure {A: Type} {INH: Inhabited A} E1 E2 (φ: A → Prop):
  (|={E1, E2}=> ∀ a, ⌜ φ a⌝)%I ≡
  ( ∀ a, |={E1, E2}=> ⌜ φ a⌝)%I.
Proof.
  intros. apply (anti_symm (⊢)).
  - iIntros "H". iIntros (a). iApply fupd_mono; last iApply "H". auto.
  - iIntros "H". rewrite fupd_eq /fupd_def.
    iIntros "[Hw HE]". 
    rewrite sep_assoc.
    rewrite except_0_sep.
    rewrite -bupd_sep.
    rewrite except_0_forall.
    rewrite -(bupd_intro (∀ a, _)).
    rewrite -except_0_forall.
    rewrite -pure_forall -persistently_pure.
    rewrite except_0_persistently.
    rewrite -persistently_and_sep_r.
    rewrite pure_forall.
    rewrite except_0_forall.
    rewrite persistently_forall.
    rewrite -forall_and_l. iIntros (a).
    iSplit.
    * iMod ("H" $! a with "[$Hw $HE]") as ">($&$&?)" => //.
    * iApply bupd_plain. iMod ("H" $! a with "[$Hw $HE]") as "H".
      iModIntro. rewrite -except_0_persistently. iMod "H" as "(?&?&%)". iModIntro.
      iAlways. done.
Qed.

(** * Derived rules *)
Global Instance fupd_mono' E1 E2 : Proper ((⊢) ==> (⊢)) (@fupd Σ _ E1 E2).
Proof. intros P Q; apply fupd_mono. Qed.
Global Instance fupd_flip_mono' E1 E2 :
  Proper (flip (⊢) ==> flip (⊢)) (@fupd Σ _ E1 E2).
Proof. intros P Q; apply fupd_mono. Qed.

Lemma fupd_intro E P : P ={E}=∗ P.
Proof. iIntros "HP". by iApply bupd_fupd. Qed.
Lemma fupd_intro_mask' E1 E2 : E2 ⊆ E1 → (|={E1,E2}=> |={E2,E1}=> True)%I.
Proof. exact: fupd_intro_mask. Qed.
Lemma fupd_except_0 E1 E2 P : (|={E1,E2}=> ◇ P) ={E1,E2}=∗ P.
Proof. by rewrite {1}(fupd_intro E2 P) except_0_fupd fupd_trans. Qed.

Lemma fupd_frame_l E1 E2 P Q : (P ∗ |={E1,E2}=> Q) ={E1,E2}=∗ P ∗ Q.
Proof. rewrite !(comm _ P); apply fupd_frame_r. Qed.
Lemma fupd_wand_l E1 E2 P Q : (P -∗ Q) ∗ (|={E1,E2}=> P) ={E1,E2}=∗ Q.
Proof. by rewrite fupd_frame_l wand_elim_l. Qed.
Lemma fupd_wand_r E1 E2 P Q : (|={E1,E2}=> P) ∗ (P -∗ Q) ={E1,E2}=∗ Q.
Proof. by rewrite fupd_frame_r wand_elim_r. Qed.

Lemma fupd_trans_frame E1 E2 E3 P Q :
  ((Q ={E2,E3}=∗ True) ∗ |={E1,E2}=> (Q ∗ P)) ={E1,E3}=∗ P.
Proof.
  rewrite fupd_frame_l assoc -(comm _ Q) wand_elim_r.
  by rewrite fupd_frame_r left_id fupd_trans.
Qed.

Lemma fupd_mask_frame_r E1 E2 Ef P :
  E1 ## Ef → (|={E1,E2}=> P) ={E1 ∪ Ef,E2 ∪ Ef}=∗ P.
Proof.
  iIntros (?) "H". iApply fupd_mask_frame_r'; auto.
  iApply fupd_wand_r; iFrame "H"; eauto.
Qed.
Lemma fupd_mask_mono E1 E2 P : E1 ⊆ E2 → (|={E1}=> P) ={E2}=∗ P.
Proof.
  intros (Ef&->&?)%subseteq_disjoint_union_L. by apply fupd_mask_frame_r.
Qed.

Lemma fupd_sep E P Q : (|={E}=> P) ∗ (|={E}=> Q) ={E}=∗ P ∗ Q.
Proof. by rewrite fupd_frame_r fupd_frame_l fupd_trans. Qed.
Lemma fupd_big_sepL {A} E (Φ : nat → A → iProp Σ) (l : list A) :
  ([∗ list] k↦x ∈ l, |={E}=> Φ k x) ={E}=∗ [∗ list] k↦x ∈ l, Φ k x.
Proof.
  apply (big_opL_forall (λ P Q, P ={E}=∗ Q)); auto using fupd_intro.
  intros P1 P2 HP Q1 Q2 HQ. by rewrite HP HQ -fupd_sep.
Qed.
Lemma fupd_big_sepM `{Countable K} {A} E (Φ : K → A → iProp Σ) (m : gmap K A) :
  ([∗ map] k↦x ∈ m, |={E}=> Φ k x) ={E}=∗ [∗ map] k↦x ∈ m, Φ k x.
Proof.
  apply (big_opM_forall (λ P Q, P ={E}=∗ Q)); auto using fupd_intro.
  intros P1 P2 HP Q1 Q2 HQ. by rewrite HP HQ -fupd_sep.
Qed.
Lemma fupd_big_sepS `{Countable A} E (Φ : A → iProp Σ) X :
  ([∗ set] x ∈ X, |={E}=> Φ x) ={E}=∗ [∗ set] x ∈ X, Φ x.
Proof.
  apply (big_opS_forall (λ P Q, P ={E}=∗ Q)); auto using fupd_intro.
  intros P1 P2 HP Q1 Q2 HQ. by rewrite HP HQ -fupd_sep.
Qed.

Lemma fupd_plain E1 E2 P Q `{!Plain P} :
  E1 ⊆ E2 → (Q -∗ P) -∗ (|={E1, E2}=> Q) ={E1}=∗ (|={E1, E2}=> Q) ∗ P.
Proof.
  iIntros (HE) "HQP HQ". iApply (fupd_plain' _ _ E1 with "[HQP] HQ"); first done.
  iIntros "?". iApply fupd_intro. by iApply "HQP".
Qed.
End fupd.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{invG Σ}.
  Implicit Types P Q : iProp Σ.

  Global Instance from_pure_fupd E P φ : FromPure P φ → FromPure (|={E}=> P) φ.
  Proof. rewrite /FromPure. intros <-. apply fupd_intro. Qed.

  Global Instance from_assumption_fupd E p P Q :
    FromAssumption p P (|==> Q) → FromAssumption p P (|={E}=> Q)%I.
  Proof. rewrite /FromAssumption=>->. apply bupd_fupd. Qed.

  Global Instance wand_weaken_fupd E1 E2 P Q P' Q' :
    WandWeaken false P Q P' Q' →
    WandWeaken' false P Q (|={E1,E2}=> P') (|={E1,E2}=> Q').
  Proof.
    rewrite /WandWeaken' /WandWeaken=>->. apply wand_intro_l. by rewrite fupd_wand_r.
  Qed.

  Global Instance from_and_fupd E P Q1 Q2 :
    FromAnd false P Q1 Q2 → FromAnd false (|={E}=> P) (|={E}=> Q1) (|={E}=> Q2).
  Proof. rewrite /FromAnd=><-. apply fupd_sep. Qed.

  Global Instance or_split_fupd E1 E2 P Q1 Q2 :
    FromOr P Q1 Q2 → FromOr (|={E1,E2}=> P) (|={E1,E2}=> Q1) (|={E1,E2}=> Q2).
  Proof. rewrite /FromOr=><-. apply or_elim; apply fupd_mono; auto with I. Qed.

  Global Instance exists_split_fupd {A} E1 E2 P (Φ : A → iProp Σ) :
    FromExist P Φ → FromExist (|={E1,E2}=> P) (λ a, |={E1,E2}=> Φ a)%I.
  Proof.
    rewrite /FromExist=><-. apply exist_elim=> a. by rewrite -(exist_intro a).
  Qed.

  Global Instance frame_fupd p E1 E2 R P Q :
    Frame p R P Q → Frame p R (|={E1,E2}=> P) (|={E1,E2}=> Q).
  Proof. rewrite /Frame=><-. by rewrite fupd_frame_l. Qed.

  Global Instance is_except_0_fupd E1 E2 P : IsExcept0 (|={E1,E2}=> P).
  Proof. by rewrite /IsExcept0 except_0_fupd. Qed.

  Global Instance from_modal_fupd E P : FromModal (|={E}=> P) P.
  Proof. rewrite /FromModal. apply fupd_intro. Qed.

  (* Put a lower priority compared to [elim_modal_fupd_fupd], so that
     it is not taken when the first parameter is not specified (in
     spec. patterns). *)
  Global Instance elim_modal_bupd_fupd E1 E2 P Q :
    ElimModal (|==> P) P (|={E1,E2}=> Q) (|={E1,E2}=> Q) | 10.
  Proof.
    by rewrite /ElimModal (bupd_fupd E1) fupd_frame_r wand_elim_r fupd_trans.
  Qed.
  Global Instance elim_modal_fupd_fupd E1 E2 E3 P Q :
    ElimModal (|={E1,E2}=> P) P (|={E1,E3}=> Q) (|={E2,E3}=> Q).
  Proof. by rewrite /ElimModal fupd_frame_r wand_elim_r fupd_trans. Qed.
End proofmode_classes.

Hint Extern 2 (coq_tactics.envs_entails _ (|={_}=> _)) => iModIntro.

(** Fancy updates that take a step. *)

Notation "|={ E1 , E2 }▷=> Q" := (|={E1,E2}=> (▷ |={E2,E1}=> Q))%I
  (at level 99, E1, E2 at level 50, Q at level 200,
   format "|={ E1 , E2 }▷=>  Q") : uPred_scope.
Notation "P ={ E1 , E2 }▷=∗ Q" := (P -∗ |={ E1 , E2 }▷=> Q)%I
  (at level 99, E1, E2 at level 50, Q at level 200,
   format "P  ={ E1 , E2 }▷=∗  Q") : uPred_scope.
Notation "|={ E }▷=> Q" := (|={E,E}▷=> Q)%I
  (at level 99, E at level 50, Q at level 200,
   format "|={ E }▷=>  Q") : uPred_scope.
Notation "P ={ E }▷=∗ Q" := (P ={E,E}▷=∗ Q)%I
  (at level 99, E at level 50, Q at level 200,
   format "P  ={ E }▷=∗  Q") : uPred_scope.

Section step_fupd.
Context `{invG Σ}.

Lemma step_fupd_wand E1 E2 P Q : (|={E1,E2}▷=> P) -∗ (P -∗ Q) -∗ |={E1,E2}▷=> Q.
Proof. iIntros "HP HPQ". by iApply "HPQ". Qed.

Lemma step_fupd_mask_frame_r E1 E2 Ef P :
  E1 ## Ef → E2 ## Ef → (|={E1,E2}▷=> P) ⊢ |={E1 ∪ Ef,E2 ∪ Ef}▷=> P.
Proof.
  iIntros (??) "HP". iApply fupd_mask_frame_r. done. iMod "HP". iModIntro.
  iNext. by iApply fupd_mask_frame_r.
Qed.

Lemma step_fupd_mask_mono E1 E2 F1 F2 P :
  F1 ⊆ F2 → E1 ⊆ E2 → (|={E1,F2}▷=> P) ⊢ |={E2,F1}▷=> P.
Proof.
  iIntros (??) "HP".
  iMod (fupd_intro_mask') as "HM1"; first done. iMod "HP".
  iMod (fupd_intro_mask') as "HM2"; first done. iModIntro.
  iNext. iMod "HM2". iMod "HP". iMod "HM1". done.
Qed.

Lemma step_fupd_intro E1 E2 P : E2 ⊆ E1 → ▷ P -∗ |={E1,E2}▷=> P.
Proof. iIntros (?) "HP". iApply (step_fupd_mask_mono E2 _ _ E2); auto. Qed.

Lemma step_fupd_ex_intro {A} E1 E2 P :
  E2 ⊆ E1 → ▷ (∃ c : A, (P c)) -∗ |={E1,E2}=> ▷ ∃ c, |={E2,E1}=> P c.
Proof.
  iIntros (?) "HP".
  iMod (fupd_intro_mask') as "HM1"; first done.
  iMod (fupd_intro_mask') as "HM2"; first done. iModIntro.
  iNext. iDestruct "HP" as (c) "HP".
  iExists c. iMod "HM1".
  iModIntro. done.
Qed.

Lemma step_fupd_forall_pure {A: Type} E (φ: A → Prop):
  (|={E, ∅}▷=> ∀ a, ⌜ φ a⌝)%I ≡
  ( ∀ a, |={E, ∅}▷=> ⌜ φ a⌝)%I.
Proof.
  intros. apply (anti_symm (⊢)).
  - iIntros "H". iIntros (a). iMod "H".
    iModIntro. iNext. iMod "H". iModIntro. auto.
  - iIntros "H".
    rewrite fupd_eq /fupd_def. iIntros "(Hw&HE)".
    rewrite -except_0_intro.
    iMod (ownE_empty) as "Hemp".
    iModIntro. 
    iAssert (▷ ◇ ⌜∀ a, φ a⌝)%I with "[Hw HE H]" as "#Hpure".
    { 
      iIntros (a). iMod ("H" $! a with "[$Hw $HE]") as "H".
      iMod "H" as "(Hw&HE&H)".
      iNext. iMod ("H" with "[$Hw $HE]") as ">(?&?&$)".
    }
    iAssert (wsat ∗ ownE ∅ ∗ ▷ (wsat ∗ ownE ∅ ==∗ ◇ (wsat ∗ ownE E)))%I
      with "[H Hw HE Hemp]" as "Hfinish"; last first.
    { iDestruct "Hfinish" as "($&$&H)". iIntros.  
      iNext. iIntros "Hw". iMod ("H" with "Hw") as "Hw".
      iModIntro. iMod "Hpure" as %Hp. iMod "Hw" as "($&$)".
      iModIntro. eauto. 
    }
    iFrame. iNext. iIntros "(?&?)". iModIntro. auto.
Qed.

Lemma step_fupd_iter_mono n P Q E :
  (P ⊢ Q) → Nat.iter n (λ P, |={E, ∅}▷=> P)%I P ⊢ Nat.iter n (λ P, |={E, ∅}▷=> P)%I Q.
Proof.
  intros HPQ. induction n as [|n IH]=> //=. rewrite IH //.
Qed.

Global Instance step_fupd_iter_mono' n E:
  Proper ((⊢)%I ==> (⊢)%I) (Nat.iter n (λ P, |={E, ∅}▷=> P)%I).
Proof. intros P Q; apply step_fupd_iter_mono. Qed.

Global Instance step_fupd_iter_flip_mono' n E :
  Proper (flip (⊢) ==> flip (⊢)) (Nat.iter n (λ P, |={E, ∅}▷=> P)%I).
Proof. intros P Q; apply step_fupd_iter_mono. Qed.

Global Instance step_fupd_iter_proper n E:
  Proper ((≡)%I ==> (≡)%I) (Nat.iter n (λ P, |={E, ∅}▷=> P)%I).
Proof.
  intros P Q Hequiv.
  iSplit; (iIntros; iApply step_fupd_iter_mono; last eauto; rewrite Hequiv; auto).
Qed.

Lemma fupd_to_step_fupd E P:
  (|={E, ∅}=> |={∅, E}=> P) ⊢ |={E, ∅}▷=> P.
Proof.
  iIntros "H". iMod "H". iModIntro. iNext. auto.
Qed.

Lemma step_fupd_iter_frame_l n R Q :
  R ∗ Nat.iter n (λ P, |={⊤, ∅}▷=> P) Q ⊢ Nat.iter n (λ P, |={⊤, ∅}▷=> P) (R ∗ Q).
Proof.
  induction n as [|n IH]; simpl; [done|].
  iIntros "(HR&H)". iMod "H". iModIntro. iNext. iMod "H"; iModIntro.
  iApply IH; iFrame.
Qed.

(*
Lemma step_fupd_iter_pure (φ: Prop) n E:
  (Nat.iter (S n) (λ P, |={E, ∅}▷=> P) (⌜φ⌝))%I ≡
  (|={E, ∅}▷=> ▷^n ⌜ φ ⌝)%I.
Proof.
  induction n as [|n IH]; [simpl; done|].
  apply (anti_symm (⊢)).
  - rewrite Nat_iter_S IH.
    rewrite fupd_eq /fupd_def. iIntros "H (Hw&HE)".
    iMod (ownE_empty) as "Hemp".
    iModIntro. 
    iAssert (▷ ◇ ▷ ◇ ▷^n ⌜ φ ⌝)%I with "[Hw HE H]" as "#Hpure".
    { 
      iMod ("H" with "[$Hw $HE]") as "H".
      iMod "H" as "(Hw&HE&H)".
      iNext. iMod ("H" with "[$Hw $HE]") as ">(Hw&HE&H)".
      iMod ("H" with "[$Hw $HE]") as ">(Hw&HE&H)".
      iModIntro. iNext.
      iMod ("H" with "[$Hw $HE]") as "(Hw&HE&H)".
      auto.
    }
    iAssert (wsat ∗ ownE ∅ ∗ ▷ (wsat ∗ ownE ∅ ==∗ ◇ (wsat ∗ ownE E)))%I
      with "[H Hw HE Hemp]" as "Hfinish"; last first.
    { iDestruct "Hfinish" as "($&$&H)". iIntros.  
      iModIntro.
      rewrite later_laterN.
      rewrite except_0_later.
      SearchAbout "except_0". 
      iNext. iIntros "Hw". iMod ("H" with "Hw") as "Hw".
      iModIntro. iMod "Hw" as "($&$)".
      iModIntro. iMod "Hpure". SearchAbout uPred_except_0. rewrite  auto.
    }
    iFrame. iNext. iIntros "(?&?)". iModIntro. auto.
  - iIntros "H".
    rewrite Nat_iter_S IH.
    iMod "H". iModIntro.
    iNext. iMod "H".
    iModIntro.
    iApply (step_fupd_mask_mono ∅ _ _ ∅); auto with set_solver.
Qed.
*)

Lemma step_fupd_iter_plain' (P: iProp Σ) `{!Plain P} n E:
  (Nat.iter (S n) (λ P, |={E, ∅}▷=> P) (◇ P))%I ≡
  (|={E, ∅}▷=> ▷^n ◇ P)%I.
Proof.
  induction n as [|n IH]; [simpl; done|].
  apply (anti_symm (⊢)).
  - rewrite Nat_iter_S IH.
    rewrite fupd_eq /fupd_def. iIntros "H (Hw&HE)".
    iMod (ownE_empty) as "Hemp".
    iModIntro. 
    iAssert (▷^(S (S n)) ◇ P)%I with "[Hw HE H]" as "#Hpure".
    { 
      iMod ("H" with "[$Hw $HE]") as "H".
      iMod "H" as "(Hw&HE&H)". rewrite later_laterN.
      iNext. iMod ("H" with "[$Hw $HE]") as ">(Hw&HE&H)".
      iMod ("H" with "[$Hw $HE]") as ">(Hw&HE&H)".
      rewrite later_laterN.
      iNext.
      iMod ("H" with "[$Hw $HE]") as "(Hw&HE&H)".
      destruct n; (iMod "H"; auto).
    }
    iAssert (wsat ∗ ownE ∅ ∗ ▷ (wsat ∗ ownE ∅ ==∗ ◇ (wsat ∗ ownE E)))%I
      with "[H Hw HE Hemp]" as "Hfinish"; last first.
    { iDestruct "Hfinish" as "($&$&H)". iIntros.  
      iModIntro.
      rewrite later_laterN.
      iNext. iIntros "Hw". iMod ("H" with "Hw") as "Hw".
      iModIntro. iMod "Hw" as "($&$)".
      iModIntro. auto.
    }
    iFrame. iNext. iIntros "(?&?)". iModIntro. auto.
  - iIntros "H".
    rewrite Nat_iter_S IH.
    iMod "H". iModIntro.
    iNext. iMod "H".
    iModIntro.
    iApply (step_fupd_mask_mono ∅ _ _ ∅); auto with set_solver.
Qed.

Lemma step_fupd_iter_except_0 n E P:
  (Nat.iter (S n) (λ P, |={E, ∅}▷=> P) (◇ P))%I ≡
  (Nat.iter (S n) (λ P, |={E, ∅}▷=> P) P)%I.
Proof.
  induction n.
  - iSplit.
    * iIntros "H". rewrite //=.
      iMod "H". iModIntro. iNext. iApply fupd_except_0. auto.
    * iIntros. iApply step_fupd_iter_mono; last eauto. auto.
  - rewrite Nat_iter_S IHn //=.
Qed.

Lemma step_fupd_iter_plain P `{!Plain P} n E:
  (Nat.iter (S n) (λ P, |={E, ∅}▷=> P) P)%I ≡
  (|={E, ∅}▷=> ▷^n ◇ P)%I.
Proof. rewrite -step_fupd_iter_plain' step_fupd_iter_except_0 //. Qed.
  
Lemma step_fupd_iter_forall_pure {A: Type} (φ: A → Prop) n:
  (Nat.iter n (λ P, |={⊤, ∅}▷=> P) (∀ a, ⌜ φ a ⌝))%I ≡
  (∀ a, Nat.iter n (λ P, |={⊤, ∅}▷=> P)%I (⌜ φ a ⌝))%I.
Proof.
  induction n as [|n IH]; [simpl; done|].
  apply (anti_symm (⊢)).
  - iIntros "H". iIntros (a). iApply (step_fupd_iter_mono with "H"); auto.
  - iIntros "H". 
    rewrite -pure_forall.
    rewrite step_fupd_iter_plain.
    rewrite pure_forall.
    rewrite except_0_forall. 
    rewrite laterN_forall.
    iAssert (∀ a, |={⊤,∅}▷=> ▷^n ◇ ⌜φ a⌝)%I with "[H]" as "Hcut".
    { iIntros (a). rewrite -step_fupd_iter_plain. iApply "H". }
    clear IH. rewrite fupd_eq /fupd_def.
    iIntros "(Hw&HE)".
    iAssert (▷ ◇ ▷^n ◇ ⌜ ∀ a, φ a⌝)%I with "[Hw HE Hcut]" as "#Hpure".
    { 
      rewrite pure_forall except_0_forall laterN_forall except_0_forall.
      iIntros (a). iMod ("Hcut" $! a with "[$Hw $HE]") as "H".
      iMod "H" as "(Hw&HE&H)".
      iNext. iMod ("H" with "[$Hw $HE]") as ">(?&?&HP)".
      iModIntro; auto.
    }
    iMod (ownE_empty) as "Hemp".
    iAssert (wsat ∗ ownE ∅ ∗ ▷ (wsat ∗ ownE ∅ ==∗ ◇ (wsat ∗ ownE ⊤)))%I
      with "[Hcut Hw HE Hemp]" as "Hfinish"; last first.
    { iDestruct "Hfinish" as "($&$&H)". iIntros.  
      iModIntro. iModIntro.
      iNext. iIntros "Hw". iMod ("H" with "Hw") as "Hw".
      iModIntro. iMod "Hpure".  iMod "Hw" as "(?&?)".
      iModIntro. iFrame. iIntros. iNext. iMod "Hpure" as %Hp. iModIntro; eauto.
    }
    iFrame. iNext. iIntros "(?&?)". iModIntro. auto.
Qed.

Lemma step_fupd_iter_forall_pure_mid {A: Type} {INH: Inhabited A} (φ: A → Prop) n:
  (|={∅, ⊤}=> Nat.iter n (λ P, |={⊤, ∅}▷=> P) (∀ a, ⌜ φ a ⌝))%I ≡
  (∀ a, |={∅, ⊤}=> (Nat.iter n (λ P, |={⊤, ∅}▷=> P)%I (⌜ φ a ⌝)))%I.
Proof.
  induction n as [|n IH].
  { simpl. apply fupd_forall_pure. }
  apply (anti_symm (⊢)).
  - iIntros "H". iIntros (a). iApply (step_fupd_iter_mono with "H"); auto.
  - iIntros "H". 
    rewrite -pure_forall.
    rewrite step_fupd_iter_plain.
    rewrite pure_forall.
    rewrite except_0_forall. 
    rewrite laterN_forall.
    iAssert (∀ a, |={∅, ⊤}=> |={⊤,∅}▷=> ▷^n ◇ ⌜φ a⌝)%I with "[H]" as "Hcut".
    { iIntros (a). rewrite -step_fupd_iter_plain. iApply "H". }
    clear IH. rewrite fupd_eq /fupd_def.
    iIntros "(Hw&HE)".
    iAssert (◇ ▷ ◇ ▷^n ◇ ⌜ ∀ a, φ a⌝)%I with "[Hw HE Hcut]" as "#Hpure".
    { 
      rewrite pure_forall except_0_forall laterN_forall except_0_forall later_forall except_0_forall.
      iIntros (a). iMod ("Hcut" $! a with "[$Hw $HE]") as "H".
      iMod "H" as "(Hw&HE&H)".
      iMod ("H" with "[$Hw $HE]") as ">(Hw&HE&H)".
      iModIntro.  iNext.
      iMod ("H" with "[$Hw $HE]") as ">(?&?&HP)".
      iModIntro; auto.
    }
    iMod (ownE_empty) as "Hemp".
    iAssert (|==> ◇ (wsat ∗ ownE ⊤ ∗ (wsat ∗ ownE ⊤ ==∗ ◇ (wsat ∗ ownE ∅ ∗ ▷ (wsat ∗ ownE ∅ ==∗ ◇ (wsat ∗ ownE ⊤))))))%I
      with "[Hcut Hw HE Hemp]" as "Hfinish"; last first.
    { iMod "Hfinish". iMod "Hfinish". iDestruct "Hfinish" as "($&$&H)". iIntros.  
      iModIntro. iModIntro.
      iIntros "Hw". iMod ("H" with "Hw") as "Hw".
      iModIntro. iMod "Hw" as "($&$&Hw)". iMod "Hpure". iModIntro. iNext. iIntros "H".
      iMod ("Hw" with "H") as ">($&$)". iMod "Hpure".
      iModIntro. iModIntro. iIntros (a). iNext. iMod "Hpure" as %Hp; iModIntro; eauto.
    }
    destruct INH as [a].
    iMod ("Hcut" $! a with "[$Hw $HE]") as ">(?&?&H)".
    iFrame. iModIntro. iModIntro. iIntros "Hw". iMod ("H" with "Hw") as ">(Hw&HE&H)".
    do 2 iModIntro. iFrame.
    iNext.
    iIntros "Hw". iMod ("H" with "Hw") as ">(?&?&?)"; do 2 iModIntro; iFrame.
Qed.

Lemma step_fupd_iter_forall_pure_mid_alt {A: Type} (R φ: A → Prop) n:
  (∃ a, R a) →
  (|={∅, ⊤}=> Nat.iter n (λ P, |={⊤, ∅}▷=> P) (∀ a,  ⌜ R a ⌝ → ⌜ φ a ⌝))%I ≡
  (∀ a, ⌜ R a ⌝ → |={∅, ⊤}=> (Nat.iter n (λ P, |={⊤, ∅}▷=> P)%I (⌜ φ a ⌝)))%I.
Proof.
  intros Hex. iSplit. 
  - iIntros "Hequiv". 
    iIntros. iMod "Hequiv". iModIntro.
    iApply step_fupd_iter_mono; last eauto.
    iIntros. eauto.
  - iIntros "Hall".
    iAssert ((|={∅, ⊤}=> Nat.iter n (λ P, |={⊤, ∅}▷=> P) (∀ (a : {a : A | R a}), ⌜ φ (proj1_sig a) ⌝))%I) with "[Hall]" as "H".
    { destruct Hex as (a&HR).
      erewrite @step_fupd_iter_forall_pure_mid; last first.
      { eexists; eauto. }
      iIntros ((a'&HR')).
      iSpecialize ("Hall" $! a' with "[%]"); first auto.
      iMod "Hall". iModIntro.
      iApply step_fupd_iter_mono; eauto.
    }
    iMod "H". iModIntro. iApply step_fupd_iter_mono; last iApply "H".
    iIntros (Hp a Hr). iPureIntro.
    specialize (Hp (exist _ a Hr)); eauto.
Qed.

End step_fupd.
