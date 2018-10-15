From iris.base_logic Require Export derived.
Set Default Proof Using "Type".

Module Import uPred.
  Export upred.uPred.
  Export primitive.uPred.
  Export derived.uPred.
End uPred.

(* Hint DB for the logic *)
Hint Resolve pure_intro : I.
Hint Resolve or_elim or_intro_l' or_intro_r' : I.
Hint Resolve and_intro and_elim_l' and_elim_r' : I.
Hint Resolve persistently_mono : I.
Hint Resolve sep_elim_l' sep_elim_r' sep_mono : I.
Hint Immediate True_intro False_elim : I.
Hint Immediate iff_refl internal_eq_refl' : I.
