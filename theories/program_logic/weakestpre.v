From iris.base_logic.lib Require Export fancy_updates.
From iris.program_logic Require Export language.
From iris.base_logic Require Import big_op.
From iris.proofmode Require Import tactics classes.
Set Default Proof Using "Type".
Import uPred.

(*
Record step_interpT Λ cTy Σ := {
  interp_fun :> expr Λ → state Λ → expr Λ → state Λ → list (expr Λ) → cTy → iProp Σ;
}.
                                
*)

Class irisG' (Λ : language) (Σ : gFunctors) := IrisG {
  iris_invG :> invG Σ;
  state_interp : state Λ → iProp Σ;
  aux_state : Type;
  aux_interp : aux_state → iProp Σ;
  choice_type : expr Λ → state Λ → aux_state → Type;
  response_type : ∀ e1 σ1 c1 (c2 : choice_type e1 σ1 c1), expr Λ → state Λ → list (expr Λ) → Type;
  step_interpR : ∀ (e1: expr Λ) (σ1: state Λ) (c1: aux_state) (c2: choice_type e1 σ1 c1)
                   (e2: expr Λ) (σ2: state Λ) efs (r: response_type e1 σ1 c1 c2 e2 σ2 efs), iProp Σ;
  step_to_aux : (∀ e1 σ1 c1 c2 e2 σ2 efs r,
                    step_interpR e1 σ1 c1 c2 e2 σ2 efs r ==∗ ∃ c', aux_interp c')%I;
  response_inhabited :
    ∀ e1 σ1 c1 c2 e2 σ2 efs, prim_step e1 σ1 e2 σ2 efs → response_type e1 σ1 c1 c2 e2 σ2 efs
}.
Notation irisG Λ Σ := (irisG' Λ Σ).

Inductive stuckness := NotStuck | MaybeStuck.

Definition stuckness_le (s1 s2 : stuckness) : bool :=
  match s1, s2 with
  | MaybeStuck, NotStuck => false
  | _, _ => true
  end.
Instance: PreOrder stuckness_le.
Proof.
  split; first by case. move=>s1 s2 s3. by case: s1; case: s2; case: s3.
Qed.
Instance: SqSubsetEq stuckness := stuckness_le.

Definition stuckness_to_atomicity (s : stuckness) : atomicity :=
  if s is MaybeStuck then StronglyAtomic else WeaklyAtomic.

Definition wp_pre `{irisG Λ Σ} (s : stuckness)
    (wp : coPset -c> expr Λ -c> (val Λ -c> iProp Σ) -c> iProp Σ) :
    coPset -c> expr Λ -c> (val Λ -c> iProp Σ) -c> iProp Σ := λ E e1 Φ,
  match to_val e1 with
  | Some v => |={E}=> Φ v
  | None => ∀ σ1 c1,
     state_interp σ1 ∗ aux_interp c1 ={E,∅}=∗ ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
       ▷ ∃ (c2 : choice_type e1 σ1 c1), ∀ e2 σ2 efs c3, 
       ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={∅,E}=∗
       state_interp σ2 ∗ wp E e2 Φ ∗
       step_interpR e1 σ1 c1 c2 e2 σ2 efs c3 ∗
       [∗ list] ef ∈ efs, wp ⊤ ef (λ _, True)
  end%I.

Local Instance wp_pre_contractive `{irisG Λ Σ} s : Contractive (wp_pre s).
Proof.
  rewrite /wp_pre=> n wp wp' Hwp E e1 Φ.
  repeat (f_contractive || f_equiv); apply Hwp.
Qed.

Definition wp_def `{irisG Λ Σ} s :
  coPset → expr Λ → (val Λ → iProp Σ) → iProp Σ := fixpoint (wp_pre s).
Definition wp_aux : seal (@wp_def). by eexists. Qed.
Definition wp := unseal wp_aux.
Definition wp_eq : @wp = @wp_def := seal_eq wp_aux.

Arguments wp {_ _ _} _ _ _%E _.
Instance: Params (@wp) 6.

Notation "'WP' e @ s ; E {{ Φ } }" := (wp s E e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'[' 'WP'  e  '/' @  s ;  E  {{  Φ  } } ']'") : uPred_scope.
Notation "'WP' e @ E {{ Φ } }" := (wp NotStuck E e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'[' 'WP'  e  '/' @  E  {{  Φ  } } ']'") : uPred_scope.
Notation "'WP' e @ E ? {{ Φ } }" := (wp MaybeStuck E e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'[' 'WP'  e  '/' @  E  ? {{  Φ  } } ']'") : uPred_scope.
Notation "'WP' e {{ Φ } }" := (wp NotStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'[' 'WP'  e  '/' {{  Φ  } } ']'") : uPred_scope.
Notation "'WP' e ? {{ Φ } }" := (wp MaybeStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'[' 'WP'  e  '/' ? {{  Φ  } } ']'") : uPred_scope.

Notation "'WP' e @ s ; E {{ v , Q } }" := (wp s E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' @  s ;  E  {{  v ,  Q  } } ']'") : uPred_scope.
Notation "'WP' e @ E {{ v , Q } }" := (wp NotStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' @  E  {{  v ,  Q  } } ']'") : uPred_scope.
Notation "'WP' e @ E ? {{ v , Q } }" := (wp MaybeStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' @  E  ? {{  v ,  Q  } } ']'") : uPred_scope.
Notation "'WP' e {{ v , Q } }" := (wp NotStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' {{  v ,  Q  } } ']'") : uPred_scope.
Notation "'WP' e ? {{ v , Q } }" := (wp MaybeStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' ? {{  v ,  Q  } } ']'") : uPred_scope.

(* Texan triples *)
Notation "'{{{' P } } } e @ s ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ s; E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  @  s ;  E  {{{  x .. y ,  RET  pat ;  Q } } }") : uPred_scope.
Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  @  E  {{{  x .. y ,  RET  pat ;  Q } } }") : uPred_scope.
Notation "'{{{' P } } } e @ E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E ?{{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  @  E  ? {{{  x .. y ,  RET  pat ;  Q } } }") : uPred_scope.
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  {{{  x .. y ,   RET  pat ;  Q } } }") : uPred_scope.
Notation "'{{{' P } } } e ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e ?{{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  ? {{{  x .. y ,   RET  pat ;  Q } } }") : uPred_scope.
Notation "'{{{' P } } } e @ s ; E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ s; E {{ Φ }})%I
    (at level 20,
     format "{{{  P  } } }  e  @  s ;  E  {{{  RET  pat ;  Q } } }") : uPred_scope.
Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ E {{ Φ }})%I
    (at level 20,
     format "{{{  P  } } }  e  @  E  {{{  RET  pat ;  Q } } }") : uPred_scope.
Notation "'{{{' P } } } e @ E ? {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ E ?{{ Φ }})%I
    (at level 20,
     format "{{{  P  } } }  e  @  E  ? {{{  RET  pat ;  Q } } }") : uPred_scope.
Notation "'{{{' P } } } e {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e {{ Φ }})%I
    (at level 20,
     format "{{{  P  } } }  e  {{{  RET  pat ;  Q } } }") : uPred_scope.
Notation "'{{{' P } } } e ? {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e ?{{ Φ }})%I
    (at level 20,
     format "{{{  P  } } }  e  ? {{{  RET  pat ;  Q } } }") : uPred_scope.

Notation "'{{{' P } } } e @ s ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ s; E {{ Φ }})
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  @  s ;  E  {{{  x .. y ,  RET  pat ;  Q } } }") : stdpp_scope.
Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E {{ Φ }})
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  @  E  {{{  x .. y ,  RET  pat ;  Q } } }") : stdpp_scope.
Notation "'{{{' P } } } e @ E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E ?{{ Φ }})
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  @  E  ? {{{  x .. y ,  RET  pat ;  Q } } }") : stdpp_scope.
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e {{ Φ }})
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  {{{  x .. y ,  RET  pat ;  Q } } }") : stdpp_scope.
Notation "'{{{' P } } } e ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e ?{{ Φ }})
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  ? {{{  x .. y ,  RET  pat ;  Q } } }") : stdpp_scope.
Notation "'{{{' P } } } e @ s ; E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ s; E {{ Φ }})
    (at level 20,
     format "{{{  P  } } }  e  @  s ;  E  {{{  RET  pat ;  Q } } }") : stdpp_scope.
Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ E {{ Φ }})
    (at level 20,
     format "{{{  P  } } }  e  @  E  {{{  RET  pat ;  Q } } }") : stdpp_scope.
Notation "'{{{' P } } } e @ E ? {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ E ?{{ Φ }})
    (at level 20,
     format "{{{  P  } } }  e  @  E  ? {{{  RET  pat ;  Q } } }") : stdpp_scope.
Notation "'{{{' P } } } e {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e {{ Φ }})
    (at level 20,
     format "{{{  P  } } }  e  {{{  RET  pat ;  Q } } }") : stdpp_scope.
Notation "'{{{' P } } } e ? {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e ?{{ Φ }})
    (at level 20,
     format "{{{  P  } } }  e  ? {{{  RET  pat ;  Q } } }") : stdpp_scope.

Section wp.
Context `{irisG Λ Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

(* Weakest pre *)
Lemma wp_unfold s E e Φ : WP e @ s; E {{ Φ }} ⊣⊢ wp_pre s (wp s) E e Φ.
Proof. rewrite wp_eq. apply (fixpoint_unfold (wp_pre s)). Qed.

Global Instance wp_ne s E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (@wp Λ Σ _ s E e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !wp_unfold /wp_pre.
  (* FIXME: figure out a way to properly automate this proof *)
  (* FIXME: reflexivity, as being called many times by f_equiv and f_contractive
  is very slow here *)
  do 23 (f_contractive || f_equiv). apply IH; first lia.
  intros v. eapply dist_le; eauto with omega.
Qed.
Global Instance wp_proper s E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (@wp Λ Σ _ s E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.

Lemma wp_value' s E Φ v : Φ v ⊢ WP of_val v @ s; E {{ Φ }}.
Proof. iIntros "HΦ". rewrite wp_unfold /wp_pre to_of_val. auto. Qed.
Lemma wp_value_inv s E Φ v : WP of_val v @ s; E {{ Φ }} ={E}=∗ Φ v.
Proof. by rewrite wp_unfold /wp_pre to_of_val. Qed.

Lemma wp_strong_mono s E1 E2 e Φ Ψ :
  E1 ⊆ E2 → (∀ v, Φ v ={E2}=∗ Ψ v) ∗ WP e @ s; E1 {{ Φ }} ⊢ WP e @ s; E2 {{ Ψ }}.
Proof.
  iIntros (?) "[HΦ H]". iLöb as "IH" forall (e). rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:?.
  { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  iIntros (σ1 c1) "Hσ". iMod (fupd_intro_mask' E2 E1) as "Hclose"; first done.
  iMod ("H" $! σ1 c1 with "[$]") as "[$ H]".
  iModIntro. iNext.
  iDestruct "H" as (c2) "H".
  iExists c2. iIntros (e2 σ2 efs c3). iIntros "Hstep".
  iMod ("H" with "Hstep") as "($ & H & $)"; auto.
  iMod "Hclose" as "_". by iApply ("IH" with "HΦ").
Qed.

Lemma wp_stuck_weaken s E e Φ :
  WP e @ s; E {{ Φ }} ⊢ WP e @ E ?{{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|]; first iExact "H".
  iIntros (σ1 c1) "Hσ". iMod ("H" with "Hσ") as "[#Hred H]". iModIntro.
  iSplit; first done. iNext. iDestruct "H" as (c2) "H".
  iExists c2.
  iIntros (e2 σ2 efs c3) "#Hstep".
  iMod ("H" with "Hstep") as "($ & He2 & Hr & Hefs)". iModIntro.
  iSplitL "He2"; first by iApply ("IH" with "He2"). iClear "Hred Hstep".
  iSplitL "Hr"; first done.
  clear c3.
  induction efs as [|ef efs IH]; first by iApply big_sepL_nil.
  rewrite !big_sepL_cons. iDestruct "Hefs" as "(Hef & Hefs)".
  iSplitL "Hef". by iApply ("IH" with "Hef").
  exact: IH. 
Qed.

Lemma fupd_wp s E e Φ : (|={E}=> WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  iIntros (σ1 c1) "Hσ1". iMod "H". by iApply "H".
Qed.
Lemma wp_fupd s E e Φ : WP e @ s; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }}.
Proof. iIntros "H". iApply (wp_strong_mono s E); try iFrame; auto. Qed.

Lemma wp_atomic s E1 E2 e Φ `{!Atomic (stuckness_to_atomicity s) e} :
  (|={E1,E2}=> WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros "H". rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { by iDestruct "H" as ">>> $". }
  iIntros (σ1 c1) "Hσ". iMod "H".
  iMod ("H" $! σ1 c1 with "Hσ") as "[$ H]".
  iModIntro. iNext.
  iDestruct "H" as (c2) "H"; iExists c2.
  iIntros (e2 σ2 efs c3) "Hstep". iDestruct "Hstep" as %Hstep.
  iMod ("H" $! e2 σ2 efs c3 with "[#]") as "(Hphy & H & Hs & $)"; first by auto.
  destruct s.
  - rewrite !wp_unfold /wp_pre. destruct (to_val e2) as [v2|] eqn:He2.
    + iDestruct "H" as ">> $"; eauto with iFrame.
    + iMod (step_to_aux with "Hs") as (c') "Ha".
    iMod ("H" $! σ2 c' with "[$]") as "[H _]".
    iDestruct "H" as %(? & ? & ? & Hstep').
    by edestruct (atomic _ _ _ _ Hstep).
  - iFrame. destruct (atomic _ _ _ _ Hstep) as [v <-%of_to_val].
    iMod (wp_value_inv with "H") as ">H". by iApply wp_value'.
Qed.

Lemma wp_step_fupd s E1 E2 e P Φ :
  to_val e = None → E2 ⊆ E1 →
  (|={E1,E2}▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre. iIntros (-> ?) "HR H".
  iIntros (σ1 c1) "Hσ". iMod "HR". iMod ("H" with "[$]") as "[$ H]".
  iModIntro; iNext;
  iDestruct "H" as (c) "H"; iExists c.
  iIntros (e2 σ2 efs c3) "Hstep". 
  iMod ("H" $! e2 σ2 efs with "Hstep") as "($ & H & $)".
  iMod "HR". iModIntro. iApply (wp_strong_mono s E2); first done.
  iSplitR "H"; last iExact "H". iIntros (v) "H". by iApply "H".
Qed.

Lemma wp_bind K `{!LanguageCtx K} s E e Φ 
      (HfillR: ∀ e1 σ1 c1 c2, (if s then reducible e1 σ1 else to_val e1 = None) →
                              ∃ c2', ∀ e2 σ2 efs r', ∃ r,
                                    (step_interpR e1 σ1 c1 c2 e2 σ2 efs r
                                                  ⊢ step_interpR (K e1) σ1 c1 c2' (K e2) σ2 efs r')):
  WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ WP K e @ s; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by iApply fupd_wp. }
  rewrite wp_unfold /wp_pre fill_not_val //.
  iIntros (σ1 c1) "Hσ". iMod ("H" $! σ1 c1 with "[$]") as "[% H]". iModIntro; iSplit.
  { iPureIntro. destruct s; last done.
    unfold reducible in *. naive_solver eauto using fill_step. }
  iNext; iDestruct "H" as (c2) "H".
  edestruct (HfillR _ σ1 c1 c2) as (c2'&Hfill); eauto.
  { destruct s; auto. }
  iExists c2'.
  iIntros (e2 σ2 efs c3') "%". 
  destruct (fill_step_inv e σ1 e2 σ2 efs) as (e2'&->&?); auto.
  edestruct (Hfill _ _ _ c3') as (c3&Hfill').
  iMod ("H" $! e2' σ2 efs c3 with "[#]") as "($ & H & Hs & $)"; first auto.
  iDestruct (Hfill' with "Hs") as "$".
  by iApply "IH".
Qed.

(*
Lemma wp_bind K `{!LanguageCtx K} s E e Φ 
      (HfillR: ∀ e1 σ1 c1 c2, (if s then reducible e1 σ1 else True) → ∃ c2', ∀ e2 σ2 efs r', ∃ r,
          (step_interpR e1 σ1 c1 c2 e2 σ2 efs r ⊢ step_interpR (K e1) σ1 c1 c2' (K e2) σ2 efs r')):
  WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ WP K e @ s; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by iApply fupd_wp. }
  rewrite wp_unfold /wp_pre fill_not_val //.
  iIntros (σ1 c1) "Hσ". iMod ("H" $! σ1 c1 with "[$]") as "[% H]". iModIntro; iSplit.
  { iPureIntro. destruct s; last done.
    unfold reducible in *. naive_solver eauto using fill_step. }
  iNext; iDestruct "H" as (c2) "H".
  edestruct (HfillR _ σ1 c1 c2) as (c2'&Hfill); eauto; (* first done. *)
  iExists c2'.
  iIntros (e2 σ2 efs c3') "%". 
  destruct (fill_step_inv e σ1 e2 σ2 efs) as (e2'&->&?); auto.
  edestruct (Hfill _ _ _ c3') as (c3&Hfill').
  iMod ("H" $! e2' σ2 efs c3 with "[#]") as "($ & H & Hs & $)"; first auto.
  iDestruct (Hfill' with "Hs") as "$".
  by iApply "IH".
Qed.
*)

Lemma wp_bind_inv K `{!LanguageCtx K} s E e Φ 
      (HfillR: ∀ e1 σ1 c1 c2, (if s then reducible e1 σ1 else to_val e1 = None)
                              → ∃ c2', ∀ e2 σ2 efs r', ∃ r,
                (step_interpR (K e1) σ1 c1 c2 (K e2) σ2 efs r ⊢
                              step_interpR e1 σ1 c1 c2' e2 σ2 efs r')):
  WP K e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by rewrite !wp_unfold /wp_pre. }
  rewrite fill_not_val //.
  iIntros (σ1 c1) "Hσ". iMod ("H" with "[$]") as "[% H]". iModIntro; iSplit.
  { destruct s; eauto using reducible_fill. }
  iNext.
  iDestruct "H" as (c2) "H".
  edestruct (HfillR _ σ1 c1 c2) as (c2'&Hfill); first (destruct s; eauto using reducible_fill).
  iExists c2'.
  iIntros (e2 σ2 efs c3 Hstep).
  edestruct (Hfill _ _ _ c3) as (c3'&Hfill').
  iMod ("H" $! (K e2) σ2 efs c3' with "[%]") as "($ & H & Hs & $)"; eauto using fill_step.
  iDestruct (Hfill' with "Hs") as "$".
  by iApply "IH".
Qed.

(** * Derived rules *)
Lemma wp_mono s E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_strong_mono s E E); auto.
  iIntros "{$H}" (v) "?". by iApply HΦ.
Qed.
Lemma wp_stuck_mono s1 s2 E e Φ :
  s1 ⊑ s2 → WP e @ s1; E {{ Φ }} ⊢ WP e @ s2; E {{ Φ }}.
Proof. case: s1; case: s2 => // _. exact: wp_stuck_weaken. Qed.
Lemma wp_mask_mono s E1 E2 e Φ : E1 ⊆ E2 → WP e @ s; E1 {{ Φ }} ⊢ WP e @ s; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (wp_strong_mono s E1 E2); auto. iFrame; eauto. Qed.
Global Instance wp_mono' s E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (@wp Λ Σ _ s E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

Lemma wp_value s E Φ e v `{!IntoVal e v} : Φ v ⊢ WP e @ s; E {{ Φ }}.
Proof. intros; rewrite -(of_to_val e v) //; by apply wp_value'. Qed.
Lemma wp_value_fupd' s E Φ v : (|={E}=> Φ v) ⊢ WP of_val v @ s; E {{ Φ }}.
Proof. intros. by rewrite -wp_fupd -wp_value'. Qed.
Lemma wp_value_fupd s E Φ e v `{!IntoVal e v} :
  (|={E}=> Φ v) ⊢ WP e @ s; E {{ Φ }}.
Proof. intros. rewrite -wp_fupd -wp_value //. Qed.

Lemma wp_frame_l s E e Φ R : R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[??]". iApply (wp_strong_mono s E E _ Φ); try iFrame; eauto. Qed.
Lemma wp_frame_r s E e Φ R : WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[??]". iApply (wp_strong_mono s E E _ Φ); try iFrame; eauto. Qed.

Lemma wp_frame_step_l s E1 E2 e Φ R :
  to_val e = None → E2 ⊆ E1 →
  (|={E1,E2}▷=> R) ∗ WP e @ s; E2 {{ Φ }} ⊢ WP e @ s; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (wp_step_fupd with "Hu"); try done.
  iApply (wp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma wp_frame_step_r s E1 E2 e Φ R :
  to_val e = None → E2 ⊆ E1 →
  WP e @ s; E2 {{ Φ }} ∗ (|={E1,E2}▷=> R) ⊢ WP e @ s; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply wp_frame_step_l.
Qed.
Lemma wp_frame_step_l' s E e Φ R :
  to_val e = None → ▷ R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_l s E E); try iFrame; eauto. Qed.
Lemma wp_frame_step_r' s E e Φ R :
  to_val e = None → WP e @ s; E {{ Φ }} ∗ ▷ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_r s E E); try iFrame; eauto. Qed.

Lemma wp_wand s E e Φ Ψ :
  WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (wp_strong_mono s E); auto.
  iIntros "{$Hwp}" (?) "?". by iApply "H".
Qed.
Lemma wp_wand_l s E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r s E e Φ Ψ :
  WP e @ s; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (wp_wand with "Hwp H"). Qed.
End wp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{irisG Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.

  Global Instance frame_wp p s E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) → Frame p R (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Ψ }}).
  Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed.

  Global Instance is_except_0_wp s E e Φ : IsExcept0 (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wp s E e P Φ :
    ElimModal (|==> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /ElimModal (bupd_fupd E) fupd_frame_r wand_elim_r fupd_wp. Qed.

  Global Instance elim_modal_fupd_wp s E e P Φ :
    ElimModal (|={E}=> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /ElimModal fupd_frame_r wand_elim_r fupd_wp. Qed.

  (* lower precedence, if possible, it should persistently pick elim_upd_fupd_wp *)
  Global Instance elim_modal_fupd_wp_atomic s E1 E2 e P Φ :
    Atomic (stuckness_to_atomicity s) e →
    ElimModal (|={E1,E2}=> P) P
            (WP e @ s; E1 {{ Φ }}) (WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
  Proof. intros. by rewrite /ElimModal fupd_frame_r wand_elim_r wp_atomic. Qed.
End proofmode_classes.

