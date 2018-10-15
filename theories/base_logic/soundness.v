From iris.base_logic Require Export base_logic.
Set Default Proof Using "Type".
Import uPred.

Section adequacy.
Context {M : ucmraT}.

(** Consistency and adequancy statements *)
Lemma soundness φ n : (▷^n ⌜ φ ⌝ : uPred M)%I → φ.
Proof.
  cut ((▷^n ⌜ φ ⌝ : uPred M)%I n ε → φ).
  { intros help H. eapply help, H; eauto using ucmra_unit_validN. by unseal. }
  rewrite /uPred_laterN; unseal. induction n as [|n IH]=> H; auto.
Qed.

Corollary consistency_modal n : ¬ (▷^n False : uPred M)%I.
Proof. exact (soundness False n). Qed.

Corollary consistency : ¬ (False : uPred M)%I.
Proof. exact (consistency_modal 0). Qed.
End adequacy.
