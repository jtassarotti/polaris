From iris.base_logic Require Import base_logic.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export hoare.
From iris.heap_lang Require Import proofmode notation.
Set Default Proof Using "Type".

(** The proofs from Section 3.1 *)
Section demo.
  Context {M : ucmraT}.
  Notation iProp := (uPred M).

  (* The version in Coq *)
  Lemma and_exist A (P R: Prop) (Ψ: A → Prop) :
    P ∧ (∃ a, Ψ a) ∧ R → ∃ a, P ∧ Ψ a.
  Proof.
    intros [HP [HΨ HR]].
    destruct HΨ as [x HΨ].
    exists x.
    split. assumption. assumption.
  Qed.

  (* The version in IPM *)
  Lemma sep_exist A (P R: iProp) (Ψ: A → iProp) :
    P ∗ (∃ a, Ψ a) ∗ R ⊢ ∃ a, Ψ a ∗ P.
  Proof.
    iIntros "[HP [HΨ HR]]".
    iDestruct "HΨ" as (x) "HΨ".
    iExists x.
    iSplitL "HΨ". iAssumption. iAssumption.
  Qed.

  (* The short version in IPM, as in the paper *)
  Lemma sep_exist_short A (P R: iProp) (Ψ: A → iProp) :
    P ∗ (∃ a, Ψ a) ∗ R ⊢ ∃ a, Ψ a ∗ P.
  Proof. iIntros "[HP [HΨ HR]]". iFrame "HP". iAssumption. Qed.

  (* An even shorter version in IPM, using the frame introduction pattern `$` *)
  Lemma sep_exist_shorter A (P R: iProp) (Ψ: A → iProp) :
    P ∗ (∃ a, Ψ a) ∗ R ⊢ ∃ a, Ψ a ∗ P.
  Proof. by iIntros "[$ [??]]". Qed.
End demo.

(** The proofs from Section 3.2 *)
(** In the Iris development we often write specifications directly using weakest
preconditions, in sort of `CPS` style, so that they can be applied easier when
proving client code. A version of [list_reverse] in that style can be found in
the file [theories/tests/list_reverse.v]. *)
Section list_reverse.
  Context `{!heapG Σ, !probG Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types l : loc.

  Fixpoint is_list (hd : val) (xs : list val) : iProp :=
    match xs with
    | [] => ⌜hd = NONEV⌝
    | x :: xs => ∃ l hd', ⌜hd = SOMEV #l⌝ ∗ l ↦ (x,hd') ∗ is_list hd' xs
    end%I.

  Definition rev : val :=
    rec: "rev" "hd" "acc" :=
      match: "hd" with
        NONE => "acc"
      | SOME "l" =>
         let: "tmp1" := Fst !"l" in
         let: "tmp2" := Snd !"l" in
         "l" <- ("tmp1", "acc");;
         "rev" "tmp2" "hd"
      end.

  Lemma rev_acc_ht hd acc xs ys :
    {{ is_list hd xs ∗ is_list acc ys }} rev hd acc {{ w, is_list w (reverse xs ++ ys) }}.
  Proof.
    iIntros "!# [Hxs Hys]".
    iLöb as "IH" forall (hd acc xs ys). wp_rec; wp_let.
    destruct xs as [|x xs]; iSimplifyEq.
    - (* nil *) by wp_match.
    - (* cons *) iDestruct "Hxs" as (l hd') "(% & Hx & Hxs)"; iSimplifyEq.
      wp_match. wp_load. wp_proj. wp_let. wp_load. wp_proj. wp_let. wp_store.
      rewrite reverse_cons -assoc.
      iApply ("IH" $! hd' (InjRV #l) xs (x :: ys) with "Hxs [Hx Hys]").
      iExists l, acc; by iFrame.
  Qed.

  Lemma rev_ht hd xs :
    {{ is_list hd xs }} rev hd NONE {{ w, is_list w (reverse xs) }}.
  Proof.
    iIntros "!# Hxs". rewrite -(right_id_L [] (++) (reverse xs)).
    iApply (rev_acc_ht hd NONEV with "[Hxs]"); simpl; by iFrame.
  Qed.
End list_reverse.

(** The proofs from Section 5 *)
(** This part contains a formalization of the monotone counter, but with an
explicit contruction of the monoid, as we have also done in the proof mode
paper. This should simplify explaining and understanding what is happening.
A version that uses the authoritative monoid and natural number monoid
under max can be found in [theories/heap_lang/lib/counter.v]. *)

(** The invariant rule in the paper is in fact derived from mask changing
update modalities (which we did not cover in the paper). Normally we use these
mask changing update modalities directly in our proofs, but in this file we use
the first prove the rule as a lemma, and then use that. *)
Lemma wp_inv_open `{irisG Λ Σ} N E P e Φ :
  nclose N ⊆ E → Atomic WeaklyAtomic e →
  inv N P ∗ (▷ P -∗ WP e @ E ∖ ↑N {{ v, ▷ P ∗ Φ v }}) ⊢ WP e @ E {{ Φ }}.
Proof.
  iIntros (??) "[#Hinv Hwp]".
  iMod (inv_open E N P with "Hinv") as "[HP Hclose]"=>//.
  iApply wp_wand_r; iSplitL "HP Hwp"; [by iApply "Hwp"|].
  iIntros (v) "[HP $]". by iApply "Hclose".
Qed.

Definition newcounter : val := λ: <>, ref #0.
Definition incr : val :=
  rec: "incr" "l" :=
    let: "n" := !"l" in
    if: CAS "l" "n" (#1 + "n") then #() else "incr" "l".
Definition read : val := λ: "l", !"l".

(** The CMRA we need. *)
Inductive M := Auth : nat → M | Frag : nat → M | Bot.

Section M.
  Arguments cmra_op _ !_ !_/.
  Arguments op _ _ !_ !_/.
  Arguments core _ _ !_/.

  Canonical Structure M_C : ofeT := leibnizC M.

  Instance M_valid : Valid M := λ x, x ≠ Bot.
  Instance M_op : Op M := λ x y,
    match x, y with
    | Auth n, Frag j | Frag j, Auth n => if decide (j ≤ n)%nat then Auth n else Bot
    | Frag i, Frag j => Frag (max i j)
    | _, _ => Bot
    end.
  Instance M_pcore : PCore M := λ x,
    Some match x with Auth j | Frag j => Frag j | _ => Bot end.
  Instance M_unit : Unit M := Frag 0.

  Definition M_ra_mixin : RAMixin M.
  Proof.
    apply ra_total_mixin; try solve_proper || eauto.
    - intros [n1|i1|] [n2|i2|] [n3|i3|];
        repeat (simpl; case_decide); f_equal/=; lia.
    - intros [n1|i1|] [n2|i2|]; repeat (simpl; case_decide); f_equal/=; lia.
    - intros [n|i|]; repeat (simpl; case_decide); f_equal/=; lia.
    - by intros [n|i|].
    - intros [n1|i1|] y [[n2|i2|] ?]; exists (core y); simplify_eq/=;
        repeat (simpl; case_decide); f_equal/=; lia.
    - intros [n1|i1|] [n2|i2|]; simpl; by try case_decide.
  Qed.
  Canonical Structure M_R : cmraT := discreteR M M_ra_mixin.

  Global Instance M_discrete : CmraDiscrete M_R.
  Proof. apply discrete_cmra_discrete. Qed.

  Definition M_ucmra_mixin : UcmraMixin M.
  Proof.
    split; try (done || apply _).
    intros [?|?|]; simpl; try case_decide; f_equal/=; lia.
  Qed.
  Canonical Structure M_UR : ucmraT := UcmraT M M_ucmra_mixin.

  Global Instance frag_core_id n : CoreId (Frag n).
  Proof. by constructor. Qed.
  Lemma auth_frag_valid j n : ✓ (Auth n ⋅ Frag j) → (j ≤ n)%nat.
  Proof. simpl. case_decide. done. by intros []. Qed.
  Lemma auth_frag_op (j n : nat) : (j ≤ n)%nat → Auth n = Auth n ⋅ Frag j.
  Proof. intros. by rewrite /= decide_True. Qed.

  Lemma M_update n : Auth n ~~> Auth (S n).
  Proof.
    apply cmra_discrete_update=>-[m|j|] /= ?; repeat case_decide; done || lia.
  Qed.
End M.

Class counterG Σ := CounterG { counter_tokG :> inG Σ M_UR }.
Definition counterΣ : gFunctors := #[GFunctor (constRF M_UR)].
Instance subG_counterΣ {Σ} : subG counterΣ Σ → counterG Σ.
Proof. intros [?%subG_inG _]%subG_inv. split; apply _. Qed.

Section counter_proof.
  Context `{!heapG Σ, !probG Σ, !counterG Σ}.
  Implicit Types l : loc.

  Definition I (γ : gname) (l : loc) : iProp Σ :=
    (∃ c : nat, l ↦ #c ∗ own γ (Auth c))%I.

  Definition C (l : loc) (n : nat) : iProp Σ :=
    (∃ N γ, inv N (I γ l) ∧ own γ (Frag n))%I.

  (** The main proofs. *)
  Global Instance C_persistent l n : Persistent (C l n).
  Proof. apply _. Qed.

  Lemma newcounter_spec :
    {{ True }} newcounter #() {{ v, ∃ l, ⌜v = #l⌝ ∧ C l 0 }}.
  Proof.
    iIntros "!# _ /=". rewrite -wp_fupd /newcounter /=. wp_seq. wp_alloc l as "Hl".
    iMod (own_alloc (Auth 0)) as (γ) "Hγ"; first done.
    rewrite (auth_frag_op 0 0) //; iDestruct "Hγ" as "[Hγ Hγf]".
    set (N:= nroot .@ "counter").
    iMod (inv_alloc N _ (I γ l) with "[Hl Hγ]") as "#?".
    { iIntros "!>". iExists 0%nat. by iFrame. }
    iModIntro. rewrite /C; eauto 10.
  Qed.

  Lemma incr_spec l n :
    {{ C l n }} incr #l {{ v, ⌜v = #()⌝ ∧ C l (S n) }}.
  Proof.
    iIntros "!# Hl /=". iLöb as "IH". wp_rec.
    iDestruct "Hl" as (N γ) "[#Hinv Hγf]".
    wp_bind (! _)%E. iApply wp_inv_open; last iFrame "Hinv"; auto.
    iDestruct 1 as (c) "[Hl Hγ]".
    wp_load. iSplitL "Hl Hγ"; [iNext; iExists c; by iFrame|].
    wp_let. wp_op.
    wp_bind (CAS _ _ _). iApply wp_inv_open; last iFrame "Hinv"; auto.
    iDestruct 1 as (c') ">[Hl Hγ]".
    destruct (decide (c' = c)) as [->|].
    - iCombine "Hγ" "Hγf" as "Hγ".
      iDestruct (own_valid with "Hγ") as %?%auth_frag_valid; rewrite -auth_frag_op //.
      iMod (own_update with "Hγ") as "Hγ"; first apply M_update.
      rewrite (auth_frag_op (S n) (S c)); last lia; iDestruct "Hγ" as "[Hγ Hγf]".
      wp_cas_suc. iSplitL "Hl Hγ".
      { iNext. iExists (S c). rewrite Nat2Z.inj_succ Z.add_1_l. by iFrame. }
      wp_if. rewrite {3}/C; eauto 10.
    - wp_cas_fail; first (intros [=]; abstract omega).
      iSplitL "Hl Hγ"; [iNext; iExists c'; by iFrame|].
      wp_if. iApply ("IH" with "[Hγf]"). rewrite {3}/C; eauto 10.
  Qed.

  Lemma read_spec l n :
    {{ C l n }} read #l {{ v, ∃ m : nat, ⌜v = #m ∧ n ≤ m⌝ ∧ C l m }}.
  Proof.
    iIntros "!# Hl /=". iDestruct "Hl" as (N γ) "[#Hinv Hγf]".
    rewrite /read /=. wp_let. iApply wp_inv_open; last iFrame "Hinv"; auto.
    iDestruct 1 as (c) "[Hl Hγ]". wp_load.
    iDestruct (own_valid γ (Frag n ⋅ Auth c) with "[-]") as % ?%auth_frag_valid.
    { iApply own_op. by iFrame. }
    rewrite (auth_frag_op c c); last lia; iDestruct "Hγ" as "[Hγ Hγf']".
    iSplitL "Hl Hγ"; [iNext; iExists c; by iFrame|].
    rewrite /C; eauto 10 with omega.
  Qed.
End counter_proof.
