From iris.program_logic Require Export weakestpre adequacy.
From iris.heap_lang Require Export lifting.
From iris.algebra Require Import auth.
From iris.heap_lang Require Import proofmode notation.
From iris.proofmode Require Import tactics.
From discprob.idxval Require Import pival pival_dist irrel_equiv.
Set Default Proof Using "Type".
From iris.program_logic Require prob_adequacy.

Class heapPreG Σ := HeapPreG {
  heap_preG_iris :> invPreG Σ;
  heap_preG_heap :> gen_heapPreG loc val Σ;
  heap_probG_inG : prob_adequacy.probPreG heap_ectxi_lang Σ
}.

Definition heapΣ : gFunctors := #[invΣ; gen_heapΣ loc val;
                                  GFunctor (authUR (optionUR (exclR (discreteC prob_state))))].
Instance subG_heapPreG {Σ} : subG heapΣ Σ → heapPreG Σ.
Proof. split; solve_inG. Qed.

Instance heap_proj_heapPreG {Σ} : heapPreG Σ → prob_adequacy.probPreG heap_ectxi_lang Σ.
Proof. intros [? ? ?]. eauto.  Qed.

Definition heap_adequacy Σ `{heapPreG Σ} {X} (Is: pidist X) s e σ φ :
  (∀ `{heapG Σ} `{H: probG Σ},
      @ownProb _ H X Is ⊢ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}%I) →
  adequate s e σ φ.
Proof.
  intros Hwp; eapply prob_adequacy.wp_prob_safety_adequacy.
  { eapply heap_preG_iris. }
  iIntros (?) "".
  iMod (own_alloc (● to_gen_heap σ)) as (γ) "Hh".
  { apply: auth_auth_valid. exact: to_gen_heap_valid. }
  iModIntro. iExists (λ σ, own γ (● to_gen_heap σ)); iFrame; iIntros.
  set (Hheap := GenHeapG loc val Σ _ _ _ γ).
  iApply (Hwp (HeapG _ _ _) with "[$]").  
Qed.

Definition heap_adequacy' Σ `{heapPreG Σ} s e σ φ :
  (∀ `{heapG Σ} `{probG Σ}, WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}%I) →
  adequate s e σ φ.
Proof.
  intros Hwp. apply (heap_adequacy _  (mret tt)) => Hh Hp.
  iIntros; iApply Hwp.
Qed.

Definition heap_prob_adequacy Σ `{heapPreG Σ} {X} Is e σ φ sch n:
  terminates sch [([e], σ)] n →
  (∀ `{heapG Σ} `{H: probG Σ},
      ownProb Is ⊢ WP e {{ v, ∃ v' : X, ownProb (mret v') ∗ ⌜φ v v'⌝ }}%I) →
  irrel_couplingP (ivdist_tpool_stepN sch [e] σ n)
                  Is
                  (prob_adequacy.coupling_post φ).
Proof.
  intros Hsch Hwp. 
  eapply prob_adequacy.wp_prob_adequacy'; eauto.
  iIntros (?) "".
  iMod (own_alloc (● to_gen_heap σ)) as (γ) "Hh".
  { apply: auth_auth_valid. exact: to_gen_heap_valid. }
  iModIntro. iExists (λ σ, own γ (● to_gen_heap σ)); iFrame; iIntros.
  set (Hheap := GenHeapG loc val Σ _ _ _ γ).
  iApply (Hwp (HeapG _ _ _) with "[$]").  
Qed.

Require Import Reals.
Import Rbar.
From discprob.idxval Require Import extrema ival_dist.

Definition coerce_cfg (f: val → R) (r: R) (ρ: cfg heap_lang) : R :=
  match fst ρ with
  | [] => r
  | e :: _ => match prob_language.to_val e with
              | Some v => f v 
              | _ => r
              end
  end.

(*
Definition coerce_cfg P (f: { v : val | P v} → R) (r: R) (ρ: cfg heap_lang) : R :=
  match fst ρ with
  | [] => r
  | e :: _ => match prob_language.to_val e with
              | Some v =>
                match (ClassicalEpsilon.excluded_middle_informative (P v)) with
                | left Hpf => f (exist _ v Hpf)
                | _ => r
                end
              | _ => r
              end
  end.
*)

Definition heap_prob_adequacy_Ex_max Σ `{heapPreG Σ} {X} (Is: pidist X) e σ sch n f g d:
  terminates sch [([e], σ)] n →
  (∀ `{heapG Σ} `{H: probG Σ},
      ownProb Is ⊢ WP e {{ v, ∃ (v' : X), ownProb (mret v') ∗ ⌜f v = g v'⌝ }}%I) →
  bounded_fun_on g (λ x, In_psupport x Is) →
  Rbar_le (extrema.Ex_ival (coerce_cfg f d) (ivdist_tpool_stepN sch [e] σ n))
          (extrema.Ex_max g Is).
Proof.
  rewrite /coerce_cfg.
  intros. apply irrel_coupling_eq_Ex_max_supp; eauto.
  eapply irrel_coupling_conseq; last eapply heap_prob_adequacy with (φ := λ x y, f x = g y); eauto.
  intros x y. rewrite /prob_adequacy.coupling_post.
  destruct x as (l&?). destruct l => //=.
  destruct to_val => //=.
Qed.

Definition heap_prob_adequacy_Ex_min Σ `{heapPreG Σ} {X} Is e σ sch n f g d:
  terminates sch [([e], σ)] n →
  (∀ `{heapG Σ} `{H: probG Σ},
      ownProb Is ⊢ WP e {{ v, ∃ (v' : X), ownProb (mret v') ∗ ⌜f v = g v'⌝ }}%I) →
  bounded_fun_on g (λ x, In_psupport x Is) →
  Rbar_le (extrema.Ex_min g Is)
          (extrema.Ex_ival (coerce_cfg f d) (ivdist_tpool_stepN sch [e] σ n))%R.
Proof.
  rewrite /coerce_cfg.
  intros. apply irrel_coupling_eq_Ex_min_supp; eauto.
  eapply irrel_coupling_conseq; last eapply heap_prob_adequacy with (φ := λ x y, f x = g y); eauto.
  intros x y. rewrite /prob_adequacy.coupling_post.
  destruct x as (l&?). destruct l => //=.
  destruct to_val => //=.
Qed.