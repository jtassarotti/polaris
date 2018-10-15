From iris.base_logic.lib Require Export fancy_updates namespaces.
From iris.base_logic.lib Require Import wsat.
From iris.algebra Require Import gmap.
From iris.proofmode Require Import tactics coq_tactics intro_patterns.
Set Default Proof Using "Type".
Import uPred.

(** Derived forms and lemmas about them. *)
Definition inv_def `{invG Σ} (N : namespace) (P : iProp Σ) : iProp Σ :=
  (∃ i, ⌜i ∈ (↑N:coPset)⌝ ∧ ownI i P)%I.
Definition inv_aux : seal (@inv_def). by eexists. Qed.
Definition inv {Σ i} := unseal inv_aux Σ i.
Definition inv_eq : @inv = @inv_def := seal_eq inv_aux.
Instance: Params (@inv) 3.
Typeclasses Opaque inv.

Section inv.
Context `{invG Σ}.
Implicit Types i : positive.
Implicit Types N : namespace.
Implicit Types P Q R : iProp Σ.

Global Instance inv_contractive N : Contractive (inv N).
Proof.
  rewrite inv_eq=> n ???. apply exist_ne=>i. by apply and_ne, ownI_contractive.
Qed.

Global Instance inv_ne N : NonExpansive (inv N).
Proof. apply contractive_ne, _. Qed.

Global Instance inv_Proper N : Proper ((⊣⊢) ==> (⊣⊢)) (inv N).
Proof. apply ne_proper, _. Qed.

Global Instance inv_persistent N P : Persistent (inv N P).
Proof. rewrite inv_eq /inv; apply _. Qed.

Lemma fresh_inv_name (E : gset positive) N : ∃ i, i ∉ E ∧ i ∈ (↑N:coPset).
Proof.
  exists (coPpick (↑ N ∖ coPset.of_gset E)).
  rewrite -coPset.elem_of_of_gset (comm and) -elem_of_difference.
  apply coPpick_elem_of=> Hfin.
  eapply nclose_infinite, (difference_finite_inv _ _), Hfin.
  apply of_gset_finite.
Qed.

Lemma inv_alloc N E P : ▷ P ={E}=∗ inv N P.
Proof.
  rewrite inv_eq /inv_def fupd_eq /fupd_def. iIntros "HP [Hw $]".
  iMod (ownI_alloc (∈ (↑N : coPset)) P with "[$HP $Hw]")
    as (i ?) "[$ ?]"; auto using fresh_inv_name.
Qed.

Lemma inv_alloc_open N E P :
  ↑N ⊆ E → (|={E, E∖↑N}=> inv N P ∗ (▷P ={E∖↑N, E}=∗ True))%I.
Proof.
  rewrite inv_eq /inv_def fupd_eq /fupd_def. iIntros (Sub) "[Hw HE]".
  iMod (ownI_alloc_open (∈ (↑N : coPset)) P with "Hw")
    as (i ?) "(Hw & #Hi & HD)"; auto using fresh_inv_name.
  iAssert (ownE {[i]} ∗ ownE (↑ N ∖ {[i]}) ∗ ownE (E ∖ ↑ N))%I
    with "[HE]" as "(HEi & HEN\i & HE\N)".
  { rewrite -?ownE_op; [|set_solver..].
    rewrite assoc_L -!union_difference_L //. set_solver. }
  do 2 iModIntro. iFrame "HE\N". iSplitL "Hw HEi"; first by iApply "Hw".
  iSplitL "Hi"; first by eauto. iIntros "HP [Hw HE\N]".
  iDestruct (ownI_close with "[$Hw $Hi $HP $HD]") as "[$ HEi]".
  do 2 iModIntro. iSplitL; [|done].
  iCombine "HEi" "HEN\i" as "HEN"; iCombine "HEN" "HE\N" as "HE".
  rewrite -?ownE_op; [|set_solver..].
  rewrite -!union_difference_L //; set_solver.
Qed.

Lemma inv_open E N P :
  ↑N ⊆ E → inv N P ={E,E∖↑N}=∗ ▷ P ∗ (▷ P ={E∖↑N,E}=∗ True).
Proof.
  rewrite inv_eq /inv_def fupd_eq /fupd_def; iDestruct 1 as (i) "[Hi #HiP]".
  iDestruct "Hi" as % ?%elem_of_subseteq_singleton.
  rewrite {1 4}(union_difference_L (↑ N) E) // ownE_op; last set_solver.
  rewrite {1 5}(union_difference_L {[ i ]} (↑ N)) // ownE_op; last set_solver.
  iIntros "(Hw & [HE $] & $) !> !>".
  iDestruct (ownI_open i P with "[$Hw $HE $HiP]") as "($ & $ & HD)".
  iIntros "HP [Hw $] !> !>". iApply ownI_close; by iFrame.
Qed.

Lemma inv_open_timeless E N P `{!Timeless P} :
  ↑N ⊆ E → inv N P ={E,E∖↑N}=∗ P ∗ (P ={E∖↑N,E}=∗ True).
Proof.
  iIntros (?) "Hinv". iMod (inv_open with "Hinv") as "[>HP Hclose]"; auto.
  iIntros "!> {$HP} HP". iApply "Hclose"; auto.
Qed.
End inv.

Tactic Notation "iInvCore" constr(N) "as" tactic(tac) constr(Hclose) :=
  let Htmp := iFresh in
  let patback := intro_pat.parse_one Hclose in
  let pat := constr:(IList [[IIdent Htmp; patback]]) in
  iMod (inv_open _ N with "[#]") as pat;
    [idtac|iAssumption || fail "iInv: invariant" N "not found"|idtac];
    [solve_ndisj || match goal with |- ?P => fail "iInv: cannot solve" P end
    |tac Htmp].

Tactic Notation "iInv" constr(N) "as" constr(pat) constr(Hclose) :=
   iInvCore N as (fun H => iDestruct H as pat) Hclose.
Tactic Notation "iInv" constr(N) "as" "(" simple_intropattern(x1) ")"
    constr(pat) constr(Hclose) :=
   iInvCore N as (fun H => iDestruct H as (x1) pat) Hclose.
Tactic Notation "iInv" constr(N) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) constr(Hclose) :=
   iInvCore N as (fun H => iDestruct H as (x1 x2) pat) Hclose.
Tactic Notation "iInv" constr(N) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")"
    constr(pat) constr(Hclose) :=
   iInvCore N as (fun H => iDestruct H as (x1 x2 x3) pat) Hclose.
Tactic Notation "iInv" constr(N) "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) constr(Hclose) :=
   iInvCore N as (fun H => iDestruct H as (x1 x2 x3 x4) pat) Hclose.
