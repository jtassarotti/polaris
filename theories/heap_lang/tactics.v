From iris.heap_lang Require Export lang.
Set Default Proof Using "Type".
Import heap_lang.

(** We define an alternative representation of expressions in which the
embedding of values and closed expressions is explicit. By reification of
expressions into this type we can implementation substitution, closedness
checking, atomic checking, and conversion into values, by computation. *)
Module W.
Inductive expr :=
  (* Value together with the original expression *)
  | Val (v : val) (e : heap_lang.expr) (H : to_val e = Some v)
  | ClosedExpr (e : heap_lang.expr) `{!Closed [] e}
  (* Base lambda calculus *)
  | Var (x : string)
  | Rec (f x : binder) (e : expr)
  | App (e1 e2 : expr)
  (* Base types and their operations *)
  | Lit (l : base_lit)
  | UnOp (op : un_op) (e : expr)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | ProbBinOp (op : prob_bin_op) (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  (* Sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (e1 : expr) (e2 : expr)
  (* Concurrency *)
  | Fork (e : expr)
  (* Heap *)
  | Alloc (e : expr) (ez: expr)
  | Load (e : expr)
  | Store (e1 : expr) (e2 : expr)
  | CAS (e0 : expr) (e1 : expr) (e2 : expr)
  | FAA (e1 : expr) (e2 : expr).

Fixpoint to_expr (e : expr) : heap_lang.expr :=
  match e with
  | Val v e' _ => e'
  | ClosedExpr e => e
  | Var x => heap_lang.Var x
  | Rec f x e => heap_lang.Rec f x (to_expr e)
  | App e1 e2 => heap_lang.App (to_expr e1) (to_expr e2)
  | Lit l => heap_lang.Lit l
  | UnOp op e => heap_lang.UnOp op (to_expr e)
  | BinOp op e1 e2 => heap_lang.BinOp op (to_expr e1) (to_expr e2)
  | ProbBinOp op e1 e2 => heap_lang.ProbBinOp op (to_expr e1) (to_expr e2)
  | If e0 e1 e2 => heap_lang.If (to_expr e0) (to_expr e1) (to_expr e2)
  | Pair e1 e2 => heap_lang.Pair (to_expr e1) (to_expr e2)
  | Fst e => heap_lang.Fst (to_expr e)
  | Snd e => heap_lang.Snd (to_expr e)
  | InjL e => heap_lang.InjL (to_expr e)
  | InjR e => heap_lang.InjR (to_expr e)
  | Case e0 e1 e2 => heap_lang.Case (to_expr e0) (to_expr e1) (to_expr e2)
  | Fork e => heap_lang.Fork (to_expr e)
  | Alloc e ez => heap_lang.Alloc (to_expr e) (to_expr ez)
  | Load e => heap_lang.Load (to_expr e)
  | Store e1 e2 => heap_lang.Store (to_expr e1) (to_expr e2)
  | CAS e0 e1 e2 => heap_lang.CAS (to_expr e0) (to_expr e1) (to_expr e2)
  | FAA e1 e2 => heap_lang.FAA (to_expr e1) (to_expr e2)
  end.

Ltac of_expr e :=
  lazymatch e with
  | heap_lang.Var ?x => constr:(Var x)
  | heap_lang.Rec ?f ?x ?e => let e := of_expr e in constr:(Rec f x e)
  | heap_lang.App ?e1 ?e2 =>
     let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(App e1 e2)
  | heap_lang.Lit ?l => constr:(Lit l)
  | heap_lang.UnOp ?op ?e => let e := of_expr e in constr:(UnOp op e)
  | heap_lang.BinOp ?op ?e1 ?e2 =>
     let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(BinOp op e1 e2)
  | heap_lang.ProbBinOp ?op ?e1 ?e2 =>
     let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(ProbBinOp op e1 e2)
  | heap_lang.If ?e0 ?e1 ?e2 =>
     let e0 := of_expr e0 in let e1 := of_expr e1 in let e2 := of_expr e2 in
     constr:(If e0 e1 e2)
  | heap_lang.Pair ?e1 ?e2 =>
     let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(Pair e1 e2)
  | heap_lang.Fst ?e => let e := of_expr e in constr:(Fst e)
  | heap_lang.Snd ?e => let e := of_expr e in constr:(Snd e)
  | heap_lang.InjL ?e => let e := of_expr e in constr:(InjL e)
  | heap_lang.InjR ?e => let e := of_expr e in constr:(InjR e)
  | heap_lang.Case ?e0 ?e1 ?e2 =>
     let e0 := of_expr e0 in let e1 := of_expr e1 in let e2 := of_expr e2 in
     constr:(Case e0 e1 e2)
  | heap_lang.Fork ?e => let e := of_expr e in constr:(Fork e)
  | heap_lang.Alloc ?e ?ez =>
    let e := of_expr e in let ez := of_expr ez in constr:(Alloc e ez)
  | heap_lang.Load ?e => let e := of_expr e in constr:(Load e)
  | heap_lang.Store ?e1 ?e2 =>
     let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(Store e1 e2)
  | heap_lang.CAS ?e0 ?e1 ?e2 =>
     let e0 := of_expr e0 in let e1 := of_expr e1 in let e2 := of_expr e2 in
     constr:(CAS e0 e1 e2)
  | heap_lang.FAA ?e1 ?e2 =>
     let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(FAA e1 e2)
  | to_expr ?e => e
  | of_val ?v => constr:(Val v (of_val v) (to_of_val v))
  | _ => match goal with
         | H : to_val e = Some ?v |- _ => constr:(Val v e H)
         | H : Closed [] e |- _ => constr:(@ClosedExpr e H)
         end
  end.

Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Val _ _ _ | ClosedExpr _ => true
  | Var x => bool_decide (x ∈ X)
  | Rec f x e => is_closed (f :b: x :b: X) e
  | Lit _ => true
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Fork e | Load e =>
     is_closed X e
  | Alloc e1 e2 | App e1 e2 | BinOp _ e1 e2 | ProbBinOp _ e1 e2 | Pair e1 e2
  | Store e1 e2 | FAA e1 e2 =>
     is_closed X e1 && is_closed X e2
  | If e0 e1 e2 | Case e0 e1 e2 | CAS e0 e1 e2 =>
     is_closed X e0 && is_closed X e1 && is_closed X e2
  end.
Lemma is_closed_correct X e : is_closed X e → heap_lang.is_closed X (to_expr e).
Proof.
  revert X.
  induction e; naive_solver eauto using is_closed_to_val, is_closed_weaken_nil.
Qed.

(* We define [to_val (ClosedExpr _)] to be [None] since [ClosedExpr]
constructors are only generated for closed expressions of which we know nothing
about apart from being closed. Notice that the reverse implication of
[to_val_Some] thus does not hold. *)
Fixpoint to_val (e : expr) : option val :=
  match e with
  | Val v _ _ => Some v
  | Rec f x e =>
     if decide (is_closed (f :b: x :b: []) e) is left H
     then Some (@RecV f x (to_expr e) (is_closed_correct _ _ H)) else None
  | Lit l => Some (LitV l)
  | Pair e1 e2 => v1 ← to_val e1; v2 ← to_val e2; Some (PairV v1 v2)
  | InjL e => InjLV <$> to_val e
  | InjR e => InjRV <$> to_val e
  | _ => None
  end.
Lemma to_val_Some e v :
  to_val e = Some v → heap_lang.to_val (to_expr e) = Some v.
Proof.
  revert v. induction e; intros; simplify_option_eq; rewrite ?to_of_val; auto.
  - do 2 f_equal. apply proof_irrel.
  - exfalso. unfold Closed in *; eauto using is_closed_correct.
Qed.
Lemma to_val_is_Some e :
  is_Some (to_val e) → is_Some (heap_lang.to_val (to_expr e)).
Proof. intros [v ?]; exists v; eauto using to_val_Some. Qed.

Fixpoint subst (x : string) (es : expr) (e : expr)  : expr :=
  match e with
  | Val v e H => Val v e H
  | ClosedExpr e => ClosedExpr e
  | Var y => if decide (x = y) then es else Var y
  | Rec f y e =>
     Rec f y $ if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then subst x es e else e
  | App e1 e2 => App (subst x es e1) (subst x es e2)
  | Lit l => Lit l
  | UnOp op e => UnOp op (subst x es e)
  | BinOp op e1 e2 => BinOp op (subst x es e1) (subst x es e2)
  | ProbBinOp op e1 e2 => ProbBinOp op (subst x es e1) (subst x es e2)
  | If e0 e1 e2 => If (subst x es e0) (subst x es e1) (subst x es e2)
  | Pair e1 e2 => Pair (subst x es e1) (subst x es e2)
  | Fst e => Fst (subst x es e)
  | Snd e => Snd (subst x es e)
  | InjL e => InjL (subst x es e)
  | InjR e => InjR (subst x es e)
  | Case e0 e1 e2 => Case (subst x es e0) (subst x es e1) (subst x es e2)
  | Fork e => Fork (subst x es e)
  | Alloc e ez => Alloc (subst x es e) (subst x es ez)
  | Load e => Load (subst x es e)
  | Store e1 e2 => Store (subst x es e1) (subst x es e2)
  | CAS e0 e1 e2 => CAS (subst x es e0) (subst x es e1) (subst x es e2)
  | FAA e1 e2 => FAA (subst x es e1) (subst x es e2)
  end.
Lemma to_expr_subst x er e :
  to_expr (subst x er e) = heap_lang.subst x (to_expr er) (to_expr e).
Proof.
  induction e; simpl; repeat case_decide;
    f_equal; eauto using subst_is_closed_nil, is_closed_to_val, eq_sym.
Qed.

Definition is_atomic (e : expr) :=
  match e with
  | Alloc e ez => bool_decide (is_Some (to_val e) ∧ is_Some (to_val ez))
  | Load e => bool_decide (is_Some (to_val e))
  | Store e1 e2 => bool_decide (is_Some (to_val e1) ∧ is_Some (to_val e2))
  | UnOp op e1 => bool_decide (is_Some (to_val e1))
  | BinOp op e1 e2 => bool_decide (is_Some (to_val e1) ∧ is_Some (to_val e2))
  | ProbBinOp op e1 e2 => bool_decide (is_Some (to_val e1) ∧ is_Some (to_val e2))
  | CAS e0 e1 e2 =>
     bool_decide (is_Some (to_val e0) ∧ is_Some (to_val e1) ∧ is_Some (to_val e2))
  | FAA e1 e2 => bool_decide (is_Some (to_val e1) ∧ is_Some (to_val e2))
  | Fork _ => true
  (* Make "skip" atomic *)
  | App (Rec _ _ (Lit _)) (Lit _) => true
  | _ => false
  end.
Lemma is_atomic_correct s e : is_atomic e → Atomic s (to_expr e).
Proof.
  intros He. apply strongly_atomic_atomic, ectx_language_atomic.
  - intros σ e' σ' ef Hstep; simpl in *. revert Hstep.
    destruct e=> //=; repeat (simplify_eq/=; case_match=>//);
      inversion 1; simplify_eq/=; rewrite ?to_of_val; eauto.
    unfold subst'; repeat (simplify_eq/=; case_match=>//); eauto.
  - apply ectxi_language_sub_redexes_are_values=> /= Ki e' Hfill.
    destruct e=> //; destruct Ki; repeat (simplify_eq/=; case_match=>//);
      naive_solver eauto using to_val_is_Some.
Qed.
End W.

Ltac solve_closed :=
  match goal with
  | |- Closed ?X ?e =>
     let e' := W.of_expr e in change (Closed X (W.to_expr e'));
     apply W.is_closed_correct; vm_compute; exact I
  end.
Hint Extern 0 (Closed _ _) => solve_closed : typeclass_instances.

Ltac solve_into_val :=
  match goal with
  | |- IntoVal ?e ?v =>
     let e' := W.of_expr e in change (to_val (W.to_expr e') = Some v);
     apply W.to_val_Some; simpl; unfold W.to_expr; reflexivity
  end.
Hint Extern 10 (IntoVal _ _) => solve_into_val : typeclass_instances.

Ltac solve_as_val :=
  match goal with
  | |- AsVal ?e =>
     let e' := W.of_expr e in change (is_Some (to_val (W.to_expr e')));
     apply W.to_val_is_Some, (bool_decide_unpack _); vm_compute; exact I
  end.
Hint Extern 10 (AsVal _) => solve_as_val : typeclass_instances.

Ltac solve_atomic :=
  match goal with
  | |- Atomic ?s ?e =>
     let e' := W.of_expr e in change (Atomic s (W.to_expr e'));
     apply W.is_atomic_correct; vm_compute; exact I
  end.
Hint Extern 10 (Atomic _ _) => solve_atomic : typeclass_instances.

(** Substitution *)
Ltac simpl_subst :=
  simpl;
  repeat match goal with
  | |- context [subst ?x ?er ?e] =>
      let er' := W.of_expr er in let e' := W.of_expr e in
      change (subst x er e) with (subst x (W.to_expr er') (W.to_expr e'));
      rewrite <-(W.to_expr_subst x); simpl (* ssr rewrite is slower *)
  end;
  unfold W.to_expr.
Arguments W.to_expr : simpl never.
Arguments subst : simpl never.

(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
Ltac reshape_val e tac :=
  let rec go e :=
  lazymatch e with
  | of_val ?v => v
  | Rec ?f ?x ?e => constr:(RecV f x e)
  | Lit ?l => constr:(LitV l)
  | Pair ?e1 ?e2 =>
    let v1 := go e1 in let v2 := go e2 in constr:(PairV v1 v2)
  | InjL ?e => let v := go e in constr:(InjLV v)
  | InjR ?e => let v := go e in constr:(InjRV v)
  end in let v := go e in tac v.

Ltac reshape_expr e tac :=
  let rec go K e :=
  match e with
  | _ => tac K e
  | App ?e1 ?e2 => reshape_val e1 ltac:(fun v1 => go (AppRCtx v1 :: K) e2)
  | App ?e1 ?e2 => go (AppLCtx e2 :: K) e1
  | UnOp ?op ?e => go (UnOpCtx op :: K) e
  | BinOp ?op ?e1 ?e2 =>
     reshape_val e1 ltac:(fun v1 => go (BinOpRCtx op v1 :: K) e2)
  | BinOp ?op ?e1 ?e2 => go (BinOpLCtx op e2 :: K) e1
  | ProbBinOp ?op ?e1 ?e2 =>
     reshape_val e1 ltac:(fun v1 => go (ProbBinOpRCtx op v1 :: K) e2)
  | ProbBinOp ?op ?e1 ?e2 => go (ProbBinOpLCtx op e2 :: K) e1
  | If ?e0 ?e1 ?e2 => go (IfCtx e1 e2 :: K) e0
  | Pair ?e1 ?e2 => reshape_val e1 ltac:(fun v1 => go (PairRCtx v1 :: K) e2)
  | Pair ?e1 ?e2 => go (PairLCtx e2 :: K) e1
  | Fst ?e => go (FstCtx :: K) e
  | Snd ?e => go (SndCtx :: K) e
  | InjL ?e => go (InjLCtx :: K) e
  | InjR ?e => go (InjRCtx :: K) e
  | Case ?e0 ?e1 ?e2 => go (CaseCtx e1 e2 :: K) e0
  | Alloc ?e1 ?e2 => reshape_val e1 ltac:(fun v1 => go (AllocRCtx v1 :: K) e2)
  | Alloc ?e1 ?e2 => go (AllocLCtx e2 :: K) e1
  | Load ?e => go (LoadCtx :: K) e
  | Store ?e1 ?e2 => reshape_val e1 ltac:(fun v1 => go (StoreRCtx v1 :: K) e2)
  | Store ?e1 ?e2 => go (StoreLCtx e2 :: K) e1
  | CAS ?e0 ?e1 ?e2 => reshape_val e0 ltac:(fun v0 => first
     [ reshape_val e1 ltac:(fun v1 => go (CasRCtx v0 v1 :: K) e2)
     | go (CasMCtx v0 e2 :: K) e1 ])
  | CAS ?e0 ?e1 ?e2 => go (CasLCtx e1 e2 :: K) e0
  | FAA ?e1 ?e2 => reshape_val e1 ltac:(fun v1 => go (FaaRCtx v1 :: K) e2)
  | FAA ?e1 ?e2 => go (FaaLCtx e2 :: K) e1
  end in go (@nil ectx_item) e.
