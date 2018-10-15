From stdpp Require Export strings.
From iris.proofmode Require Import base tokens.
Set Default Proof Using "Type".

Inductive sel_pat :=
  | SelPure
  | SelPersistent
  | SelSpatial
  | SelIdent : ident → sel_pat.

Fixpoint sel_pat_pure (ps : list sel_pat) : bool :=
  match ps with
  | [] => false
  | SelPure :: ps => true
  | _ :: ps => sel_pat_pure ps
  end.

Module sel_pat.
Fixpoint parse_go (ts : list token) (k : list sel_pat) : option (list sel_pat) :=
  match ts with
  | [] => Some (reverse k)
  | TName s :: ts => parse_go ts (SelIdent s :: k)
  | TPure :: ts => parse_go ts (SelPure :: k)
  | TAlways :: ts => parse_go ts (SelPersistent :: k)
  | TSep :: ts => parse_go ts (SelSpatial :: k)
  | _ => None
  end.
Definition parse (s : string) : option (list sel_pat) :=
  parse_go (tokenize s) [].

Ltac parse s :=
  lazymatch type of s with
  | sel_pat => constr:([s])
  | list sel_pat => s
  | ident => constr:([SelIdent s])
  | list ident => eval vm_compute in (SelIdent <$> s)
  | list string => eval vm_compute in (SelIdent ∘ INamed <$> s)
  | string =>
     lazymatch eval vm_compute in (parse s) with
     | Some ?pats => pats | _ => fail "invalid sel_pat" s
     end
  end.
End sel_pat.
