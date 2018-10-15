From stdpp Require Export strings.
From iris.proofmode Require Import base tokens sel_patterns.
Set Default Proof Using "Type".

Inductive intro_pat :=
  | IIdent : ident → intro_pat
  | IAnom : intro_pat
  | IDrop : intro_pat
  | IFrame : intro_pat
  | IList : list (list intro_pat) → intro_pat
  | IPureElim : intro_pat
  | IAlwaysElim : intro_pat → intro_pat
  | IModalElim : intro_pat → intro_pat
  | IRewrite : direction → intro_pat
  | IPureIntro : intro_pat
  | IAlwaysIntro : intro_pat
  | IModalIntro : intro_pat
  | ISimpl : intro_pat
  | IDone : intro_pat
  | IForall : intro_pat
  | IAll : intro_pat
  | IClear : sel_pat → intro_pat
  | IClearFrame : sel_pat → intro_pat.

Module intro_pat.
Inductive stack_item :=
  | SPat : intro_pat → stack_item
  | SList : stack_item
  | SConjList : stack_item
  | SBar : stack_item
  | SAmp : stack_item
  | SAlwaysElim : stack_item
  | SModalElim : stack_item.
Notation stack := (list stack_item).

Fixpoint close_list (k : stack)
    (ps : list intro_pat) (pss : list (list intro_pat)) : option stack :=
  match k with
  | SList :: k => Some (SPat (IList (ps :: pss)) :: k)
  | SPat pat :: k => close_list k (pat :: ps) pss
  | SAlwaysElim :: k =>
     ''(p,ps) ← maybe2 (::) ps; close_list k (IAlwaysElim p :: ps) pss
  | SModalElim :: k =>
     ''(p,ps) ← maybe2 (::) ps; close_list k (IModalElim p :: ps) pss
  | SBar :: k => close_list k [] (ps :: pss)
  | _ => None
  end.

Fixpoint big_conj (ps : list intro_pat) : intro_pat :=
  match ps with
  | [] => IList [[]]
  | [p] => IList [[ p ]]
  | [p1;p2] => IList [[ p1 ; p2 ]]
  | p :: ps => IList [[ p ; big_conj ps ]]
  end.

Fixpoint close_conj_list (k : stack)
    (cur : option intro_pat) (ps : list intro_pat) : option stack :=
  match k with
  | SConjList :: k =>
     ps ← match cur with
          | None => guard (ps = []); Some [] | Some p => Some (p :: ps)
          end;
     Some (SPat (big_conj ps) :: k)
  | SPat pat :: k => guard (cur = None); close_conj_list k (Some pat) ps
  | SAlwaysElim :: k => p ← cur; close_conj_list k (Some (IAlwaysElim p)) ps
  | SModalElim :: k => p ← cur; close_conj_list k (Some (IModalElim p)) ps
  | SAmp :: k => p ← cur; close_conj_list k None (p :: ps)
  | _ => None
  end.

Fixpoint parse_go (ts : list token) (k : stack) : option stack :=
  match ts with
  | [] => Some k
  | TName "_" :: ts => parse_go ts (SPat IDrop :: k)
  | TName s :: ts => parse_go ts (SPat (IIdent s) :: k)
  | TAnom :: ts => parse_go ts (SPat IAnom :: k)
  | TFrame :: ts => parse_go ts (SPat IFrame :: k)
  | TBracketL :: ts => parse_go ts (SList :: k)
  | TBar :: ts => parse_go ts (SBar :: k)
  | TBracketR :: ts => close_list k [] [] ≫= parse_go ts
  | TParenL :: ts => parse_go ts (SConjList :: k)
  | TAmp :: ts => parse_go ts (SAmp :: k)
  | TParenR :: ts => close_conj_list k None [] ≫= parse_go ts
  | TPure :: ts => parse_go ts (SPat IPureElim :: k)
  | TAlways :: ts => parse_go ts (SAlwaysElim :: k)
  | TModal :: ts => parse_go ts (SModalElim :: k)
  | TArrow d :: ts => parse_go ts (SPat (IRewrite d) :: k)
  | TPureIntro :: ts => parse_go ts (SPat IPureIntro :: k)
  | TAlwaysIntro :: ts => parse_go ts (SPat IAlwaysIntro :: k)
  | TModalIntro :: ts => parse_go ts (SPat IModalIntro :: k)
  | TSimpl :: ts => parse_go ts (SPat ISimpl :: k)
  | TDone :: ts => parse_go ts (SPat IDone :: k)
  | TAll :: ts => parse_go ts (SPat IAll :: k)
  | TForall :: ts => parse_go ts (SPat IForall :: k)
  | TBraceL :: ts => parse_clear ts k
  | _ => None
  end
with parse_clear (ts : list token) (k : stack) : option stack :=
  match ts with
  | TFrame :: TName s :: ts => parse_clear ts (SPat (IClearFrame (SelIdent s)) :: k)
  | TFrame :: TPure :: ts => parse_clear ts (SPat (IClearFrame SelPure) :: k)
  | TFrame :: TAlways :: ts => parse_clear ts (SPat (IClearFrame SelPersistent) :: k)
  | TFrame :: TSep :: ts => parse_clear ts (SPat (IClearFrame SelSpatial) :: k)
  | TName s :: ts => parse_clear ts (SPat (IClear (SelIdent s)) :: k)
  | TPure :: ts => parse_clear ts (SPat (IClear SelPure) :: k)
  | TAlways :: ts => parse_clear ts (SPat (IClear SelPersistent) :: k)
  | TSep :: ts => parse_clear ts (SPat (IClear SelSpatial) :: k)
  | TBraceR :: ts => parse_go ts k
  | _ => None
  end.

Fixpoint close (k : stack) (ps : list intro_pat) : option (list intro_pat) :=
  match k with
  | [] => Some ps
  | SPat pat :: k => close k (pat :: ps)
  | SAlwaysElim :: k => ''(p,ps) ← maybe2 (::) ps; close k (IAlwaysElim p :: ps)
  | SModalElim :: k => ''(p,ps) ← maybe2 (::) ps; close k (IModalElim p :: ps)
  | _ => None
  end.

Definition parse (s : string) : option (list intro_pat) :=
  k ← parse_go (tokenize s) []; close k [].

Ltac parse s :=
  lazymatch type of s with
  | list intro_pat => s
  | intro_pat => constr:([s])
  | list string =>
     lazymatch eval vm_compute in (mjoin <$> mapM parse s) with
     | Some ?pats => pats | _ => fail "invalid list intro_pat" s
     end
  | string =>
     lazymatch eval vm_compute in (parse s) with
     | Some ?pats => pats | _ => fail "invalid list intro_pat" s
     end
  | ident => constr:([IIdent s])
  | ?X => fail "intro_pat.parse:" s "has unexpected type" X
  end.
Ltac parse_one s :=
  lazymatch type of s with
  | intro_pat => s
  | string =>
     lazymatch eval vm_compute in (parse s) with
     | Some [?pat] => pat | _ => fail "invalid intro_pat" s
     end
  | ?X => fail "intro_pat.parse_one:" s "has unexpected type" X
  end.
End intro_pat.

Fixpoint intro_pat_persistent (p : intro_pat) :=
  match p with
  | IPureElim => true
  | IAlwaysElim _ => true
  | IList pps => forallb (forallb intro_pat_persistent) pps
  | ISimpl => true
  | IClear _ => true
  | IClearFrame _ => true
  | _ => false
  end.

Ltac intro_pat_persistent p :=
  lazymatch type of p with
  | intro_pat => eval cbv in (intro_pat_persistent p)
  | list intro_pat => eval cbv in (forallb intro_pat_persistent p)
  | string =>
     let pat := intro_pat.parse p in
     eval cbv in (forallb intro_pat_persistent pat)
  | ident => false
  | bool => p
  | ?X => fail "intro_pat_persistent:" p "has unexpected type" X
  end.
