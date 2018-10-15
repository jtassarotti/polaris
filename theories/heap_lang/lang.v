Require Reals.
Require Import Psatz.
Require ClassicalEpsilon.
From iris.program_logic Require Export language prob_language ectx_language ectxi_language.
From discprob.monad Require Import monad.
From discprob.idxval Require Import ival_dist uniform.
From discprob.basic Require Import classic_proof_irrel.
From iris.algebra Require Export ofe.
From stdpp Require Export strings.
From stdpp Require Import gmap pmap.
From mathcomp Require Import bigop fintype choice.
From mathcomp Require eqtype.
From discprob.basic Require stdpp_ext seq_ext.
Set Default Proof Using "Type".

Module heap_lang.
Open Scope Z_scope.

(** Expressions and vals. *)
Definition loc := positive. (* Really, any countable type. *)

Inductive base_lit : Set :=
  | LitInt (n : Z) | LitBool (b : bool) | LitUnit | LitLoc (l : loc).
Inductive un_op : Set :=
  | NegOp | MinusUnOp.
Inductive bin_op : Set :=
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp | ExpOp (* Arithmetic *)
  | AndOp | OrOp | XorOp (* Bitwise *)
  | ShiftLOp | ShiftROp (* Shifts *)
  | LeOp | LtOp | EqOp (* Relations *).
Inductive prob_un_op : Set := UnifOp.
Inductive prob_bin_op : Set :=
  | BernOp.

Inductive binder := BAnon | BNamed : string → binder.
Delimit Scope binder_scope with bind.
Bind Scope binder_scope with binder.
Definition cons_binder (mx : binder) (X : list string) : list string :=
  match mx with BAnon => X | BNamed x => x :: X end.
Infix ":b:" := cons_binder (at level 60, right associativity).
Instance binder_eq_dec_eq : EqDecision binder.
Proof. solve_decision. Defined.

Instance set_unfold_cons_binder x mx X P :
  SetUnfold (x ∈ X) P → SetUnfold (x ∈ mx :b: X) (BNamed x = mx ∨ P).
Proof.
  constructor. rewrite -(set_unfold (x ∈ X) P).
  destruct mx; rewrite /= ?elem_of_cons; naive_solver.
Qed.

Inductive expr :=
  (* Base lambda calculus *)
  | Var (x : string)
  | Rec (f x : binder) (e : expr)
  | App (e1 e2 : expr)
  (* Base types and their operations *)
  | Lit (l : base_lit)
  | UnOp (op : un_op) (e : expr)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | ProbUnOp (op : prob_un_op) (e : expr) 
  | ProbBinOp (op : prob_bin_op) (e1 e2: expr)
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

Bind Scope expr_scope with expr.

Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Var x => bool_decide (x ∈ X)
  | Rec f x e => is_closed (f :b: x :b: X) e
  | Lit _ => true
  | UnOp _ e | ProbUnOp _ e | Fst e | Snd e | InjL e | InjR e | Fork e | Load e =>
     is_closed X e
  | App e1 e2 | BinOp _ e1 e2 | ProbBinOp _ e1 e2 | Pair e1 e2 | Store e1 e2 | FAA e1 e2
    | Alloc e1 e2 => is_closed X e1 && is_closed X e2
  | If e0 e1 e2 | Case e0 e1 e2 | CAS e0 e1 e2 =>
     is_closed X e0 && is_closed X e1 && is_closed X e2
  end.

Class Closed (X : list string) (e : expr) := closed : is_closed X e.
Instance closed_proof_irrel X e : ProofIrrel (Closed X e).
Proof. rewrite /Closed. apply _. Qed.
Instance closed_dec X e : Decision (Closed X e).
Proof. rewrite /Closed. apply _. Defined.

Inductive val :=
  | RecV (f x : binder) (e : expr) `{!Closed (f :b: x :b: []) e}
  | LitV (l : base_lit)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val).

Bind Scope val_scope with val.

Fixpoint of_val (v : val) : expr :=
  match v with
  | RecV f x e => Rec f x e
  | LitV l => Lit l
  | PairV v1 v2 => Pair (of_val v1) (of_val v2)
  | InjLV v => InjL (of_val v)
  | InjRV v => InjR (of_val v)
  end.

Fixpoint to_val (e : expr) : option val :=
  match e with
  | Rec f x e =>
     if decide (Closed (f :b: x :b: []) e) then Some (RecV f x e) else None
  | Lit l => Some (LitV l)
  | Pair e1 e2 => v1 ← to_val e1; v2 ← to_val e2; Some (PairV v1 v2)
  | InjL e => InjLV <$> to_val e
  | InjR e => InjRV <$> to_val e
  | _ => None
  end.

(** The state: heaps of val blocks. *)
Definition state := gmap loc val.

(** Equality and other typeclass stuff *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  by induction v; simplify_option_eq; repeat f_equal; try apply (proof_irrel _).
Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  revert v; induction e; intros v ?; simplify_option_eq; auto with f_equal.
Qed.

Instance of_val_inj : Inj (=) (=) of_val.
Proof. by intros ?? Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

Instance base_lit_eq_dec : EqDecision base_lit.
Proof. solve_decision. Defined.
Instance un_op_eq_dec : EqDecision un_op.
Proof. solve_decision. Defined.
Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.
Instance prob_un_op_eq_dec : EqDecision prob_un_op.
Proof. solve_decision. Defined.
Instance prob_bin_op_eq_dec : EqDecision prob_bin_op.
Proof. solve_decision. Defined.
Instance expr_eq_dec : EqDecision expr.
Proof. solve_decision. Defined.
Instance val_eq_dec : EqDecision val.
Proof.
 refine (λ v v', cast_if (decide (of_val v = of_val v'))); abstract naive_solver.
Defined.

Instance base_lit_countable : Countable base_lit.
Proof.
 refine (inj_countable' (λ l, match l with
  | LitInt n => inl (inl n) | LitBool b => inl (inr b)
  | LitUnit => inr (inl ()) | LitLoc l => inr (inr l)
  end) (λ l, match l with
  | inl (inl n) => LitInt n | inl (inr b) => LitBool b
  | inr (inl ()) => LitUnit | inr (inr l) => LitLoc l
  end) _); by intros [].
Qed.
Instance un_op_finite : Countable un_op.
Proof.
 refine (inj_countable' (λ op, match op with NegOp => 0 | MinusUnOp => 1 end)
  (λ n, match n with 0 => NegOp | _ => MinusUnOp end) _); by intros [].
Qed.
Instance bin_op_countable : Countable bin_op.
Proof.
 refine (inj_countable' (λ op, match op with
  | PlusOp => 0 | MinusOp => 1 | MultOp => 2 | QuotOp => 3 | RemOp => 4
  | AndOp => 5 | OrOp => 6 | XorOp => 7 | ShiftLOp => 8 | ShiftROp => 9
  | LeOp => 10 | LtOp => 11 | EqOp => 12 | ExpOp => 13
  end) (λ n, match n with
  | 0 => PlusOp | 1 => MinusOp | 2 => MultOp | 3 => QuotOp | 4 => RemOp
  | 5 => AndOp | 6 => OrOp | 7 => XorOp | 8 => ShiftLOp | 9 => ShiftROp
  | 10 => LeOp | 11 => LtOp | 12 => EqOp | _ => ExpOp
  end) _); by intros [].
Qed.
Instance prob_un_op_finite : Countable prob_un_op.
Proof.
 refine (inj_countable' (λ op, match op with _ => 0 end)
  (λ n, match n with | _ => UnifOp end) _); by intros [].
Qed.
Instance prob_bin_op_finite : Countable prob_bin_op.
Proof.
 refine (inj_countable' (λ op, match op with BernOp => 0 end)
  (λ n, match n with | _ => BernOp end) _); by intros [].
Qed.
Instance binder_countable : Countable binder.
Proof.
 refine (inj_countable' (λ b, match b with BNamed s => Some s | BAnon => None end)
  (λ b, match b with Some s => BNamed s | None => BAnon end) _); by intros [].
Qed.
Instance expr_countable : Countable expr.
Proof.
 set (enc := fix go e :=
  match e return
        gen_tree (string + binder +
                  (base_lit + (un_op + (bin_op + (prob_bin_op + prob_un_op))))) with
  | Var x => GenLeaf (inl (inl x))
  | Rec f x e => GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); go e]
  | App e1 e2 => GenNode 1 [go e1; go e2]
  | Lit l => GenLeaf (inr (inl l))
  | UnOp op e => GenNode 2 [GenLeaf (inr (inr (inl op))); go e]
  | ProbUnOp op e1 => GenNode 18 [GenLeaf (inr (inr (inr (inr (inr op))))); go e1]
  | ProbBinOp op e1 e2 => GenNode 16 [GenLeaf (inr (inr (inr (inr (inl op))))); go e1; go e2]
  | BinOp op e1 e2 => GenNode 3 [GenLeaf (inr (inr (inr (inl op)))); go e1; go e2]
  | If e0 e1 e2 => GenNode 4 [go e0; go e1; go e2]
  | Pair e1 e2 => GenNode 5 [go e1; go e2]
  | Fst e => GenNode 6 [go e]
  | Snd e => GenNode 7 [go e]
  | InjL e => GenNode 8 [go e]
  | InjR e => GenNode 9 [go e]
  | Case e0 e1 e2 => GenNode 10 [go e0; go e1; go e2]
  | Fork e => GenNode 11 [go e]
  | Alloc e1 e2 => GenNode 12 [go e1; go e2]
  | Load e => GenNode 13 [go e]
  | Store e1 e2 => GenNode 14 [go e1; go e2]
  | CAS e0 e1 e2 => GenNode 15 [go e0; go e1; go e2]
  | FAA e1 e2 => GenNode 17 [go e1; go e2]
  end ).
 set (dec := fix go e :=
  match e with
  | GenLeaf (inl (inl x)) => Var x
  | GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); e] => Rec f x (go e)
  | GenNode 1 [e1; e2] => App (go e1) (go e2)
  | GenLeaf (inr (inl l)) => Lit l
  | GenNode 2 [GenLeaf (inr (inr (inl op))); e] => UnOp op (go e)
  | GenNode 18 [GenLeaf (inr (inr (inr (inr (inr op))))); e1] => ProbUnOp op (go e1)
  | GenNode 16 [GenLeaf (inr (inr (inr (inr (inl op))))); e1; e2] => ProbBinOp op (go e1) (go e2)
  | GenNode 3 [GenLeaf (inr (inr (inr (inl op)))); e1; e2] => BinOp op (go e1) (go e2)
  | GenNode 4 [e0; e1; e2] => If (go e0) (go e1) (go e2)
  | GenNode 5 [e1; e2] => Pair (go e1) (go e2)
  | GenNode 6 [e] => Fst (go e)
  | GenNode 7 [e] => Snd (go e)
  | GenNode 8 [e] => InjL (go e)
  | GenNode 9 [e] => InjR (go e)
  | GenNode 10 [e0; e1; e2] => Case (go e0) (go e1) (go e2)
  | GenNode 11 [e] => Fork (go e)
  | GenNode 12 [e1; e2] => Alloc (go e1) (go e2)
  | GenNode 13 [e] => Load (go e)
  | GenNode 14 [e1; e2] => Store (go e1) (go e2)
  | GenNode 15 [e0; e1; e2] => CAS (go e0) (go e1) (go e2)
  | GenNode 17 [e0; e1] => FAA (go e0) (go e1)
  | _ => Lit LitUnit (* dummy *)
  end).
 refine (inj_countable' enc dec _). intros e. induction e; f_equal/=; auto.
Qed.
Instance val_countable : Countable val.
Proof. refine (inj_countable of_val to_val _); auto using to_of_val. Qed.

Instance expr_inhabited : Inhabited expr := populate (Lit LitUnit).
Instance val_inhabited : Inhabited val := populate (LitV LitUnit).

Canonical Structure stateC := leibnizC state.
Canonical Structure valC := leibnizC val.
Canonical Structure exprC := leibnizC expr.

(** Evaluation contexts *)
Inductive ectx_item :=
  | AppLCtx (e2 : expr)
  | AppRCtx (v1 : val)
  | UnOpCtx (op : un_op)
  | BinOpLCtx (op : bin_op) (e2 : expr)
  | BinOpRCtx (op : bin_op) (v1 : val)
  | ProbBinOpLCtx (op : prob_bin_op) (e2 : expr)
  | ProbBinOpRCtx (op : prob_bin_op) (v1 : val)
  | IfCtx (e1 e2 : expr)
  | PairLCtx (e2 : expr)
  | PairRCtx (v1 : val)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx (e1 : expr) (e2 : expr)
  | AllocLCtx (ez: expr)
  | AllocRCtx (v1: val)
  | LoadCtx
  | StoreLCtx (e2 : expr)
  | StoreRCtx (v1 : val)
  | CasLCtx (e1 : expr) (e2 : expr)
  | CasMCtx (v0 : val) (e2 : expr)
  | CasRCtx (v0 : val) (v1 : val)
  | FaaLCtx (e2 : expr)
  | FaaRCtx (v1 : val).

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | AppLCtx e2 => App e e2
  | AppRCtx v1 => App (of_val v1) e
  | UnOpCtx op => UnOp op e
  | BinOpLCtx op e2 => BinOp op e e2
  | BinOpRCtx op v1 => BinOp op (of_val v1) e
  | ProbBinOpLCtx op e2 => ProbBinOp op e e2
  | ProbBinOpRCtx op v1 => ProbBinOp op (of_val v1) e
  | IfCtx e1 e2 => If e e1 e2
  | PairLCtx e2 => Pair e e2
  | PairRCtx v1 => Pair (of_val v1) e
  | FstCtx => Fst e
  | SndCtx => Snd e
  | InjLCtx => InjL e
  | InjRCtx => InjR e
  | CaseCtx e1 e2 => Case e e1 e2
  | AllocLCtx ez => Alloc e ez
  | AllocRCtx v => Alloc (of_val v) e
  | LoadCtx => Load e
  | StoreLCtx e2 => Store e e2 
  | StoreRCtx v1 => Store (of_val v1) e
  | CasLCtx e1 e2 => CAS e e1 e2
  | CasMCtx v0 e2 => CAS (of_val v0) e e2
  | CasRCtx v0 v1 => CAS (of_val v0) (of_val v1) e
  | FaaLCtx e2 => FAA e e2
  | FaaRCtx v1 => FAA (of_val v1) e
  end.

(** Substitution *)
Fixpoint subst (x : string) (es : expr) (e : expr)  : expr :=
  match e with
  | Var y => if decide (x = y) then es else Var y
  | Rec f y e =>
     Rec f y $ if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then subst x es e else e
  | App e1 e2 => App (subst x es e1) (subst x es e2)
  | Lit l => Lit l
  | UnOp op e => UnOp op (subst x es e)
  | BinOp op e1 e2 => BinOp op (subst x es e1) (subst x es e2)
  | ProbBinOp op e1 e2 => ProbBinOp op (subst x es e1) (subst x es e2)
  | ProbUnOp op e1=> ProbUnOp op (subst x es e1)
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

Definition subst' (mx : binder) (es : expr) : expr → expr :=
  match mx with BNamed x => subst x es | BAnon => id end.

(** The stepping relation *)
Definition un_op_eval (op : un_op) (v : val) : option val :=
  match op, v with
  | NegOp, LitV (LitBool b) => Some $ LitV $ LitBool (negb b)
  | NegOp, LitV (LitInt n) => Some $ LitV $ LitInt (Z.lnot n)
  | MinusUnOp, LitV (LitInt n) => Some $ LitV $ LitInt (- n)
  | _, _ => None
  end.

Definition bin_op_eval_int (op : bin_op) (n1 n2 : Z) : base_lit :=
  match op with
  | PlusOp => LitInt (n1 + n2)
  | MinusOp => LitInt (n1 - n2)
  | MultOp => LitInt (n1 * n2)
  | QuotOp => LitInt (n1 `quot` n2)
  | RemOp => LitInt (n1 `rem` n2)
  | AndOp => LitInt (Z.land n1 n2)
  | OrOp => LitInt (Z.lor n1 n2)
  | XorOp => LitInt (Z.lxor n1 n2)
  | ShiftLOp => LitInt (n1 ≪ n2)
  | ShiftROp => LitInt (n1 ≫ n2)
  | LeOp => LitBool (bool_decide (n1 ≤ n2))
  | LtOp => LitBool (bool_decide (n1 < n2))
  | EqOp => LitBool (bool_decide (n1 = n2))
  | ExpOp => LitInt (BinIntDef.Z.pow n1 n2)
  end.

Definition bin_op_eval_bool (op : bin_op) (b1 b2 : bool) : option base_lit :=
  match op with
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp | ExpOp => None (* Arithmetic *)
  | AndOp => Some (LitBool (b1 && b2))
  | OrOp => Some (LitBool (b1 || b2))
  | XorOp => Some (LitBool (xorb b1 b2))
  | ShiftLOp | ShiftROp => None (* Shifts *)
  | LeOp | LtOp => None (* InEquality *)
  | EqOp => Some (LitBool (bool_decide (b1 = b2)))
  end.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  match v1, v2, op with
  | LitV (LitInt n1), LitV (LitInt n2), _ => Some $ LitV $ bin_op_eval_int op n1 n2
  | LitV (LitBool b1), LitV (LitBool b2), _ => LitV <$> bin_op_eval_bool op b1 b2
  | LitV (LitLoc l), LitV (LitInt n2), PlusOp => 
    Some $ LitV $ LitLoc (Z.to_pos (Zpos l + n2))
  | v1, v2, _ =>
    guard (op = EqOp); Some $ LitV $ LitBool $ bool_decide (v1 = v2)
  end.

(* The bin ops must evaluate to primitive distributions; this cleans up things a bit *)
Definition prob_bin_op_eval (op : prob_bin_op) (v1 v2 : val) :
  option ({I : ivdist val | ival.ival_primitive I}).
unshelve (refine
  (match op, v1, v2 with
  | BernOp, LitV (LitInt n1), LitV (LitInt n2)=>
    let p := Rbasic_fun.Rmin (Rbasic_fun.Rabs
                                (Rdefinitions.Rdiv (Rdefinitions.IZR n1) (Rdefinitions.IZR n2))) 1 in
    Some (exist _ (ivdplus p _ (mret (LitV $ LitBool true)) (mret (LitV $ LitBool false))) _)
  | _, _, _ => None
  end)).
- rewrite /p; split.
  * apply Rpower.P_Rmin; last by auto with *. apply Rbasic_fun.Rabs_pos.
  * apply Rbasic_fun.Rmin_r.
- apply primitive_ivdplus_mret => //=.
Defined.

Definition prob_un_op_eval (op : prob_un_op) (v : val) :
  option ({I : ivdist val | ival.ival_primitive I}).
unshelve (refine
  (match op, v with
   | UnifOp, LitV (LitInt n1) =>
     Some (exist _ (mbind (λ n, mret (LitV $ LitInt (Z.of_nat n))) (ival_unif (Z.to_nat n1))) _)
  | _, _ => None
  end)).
- apply ival.primitive_mbind_inj.
  * abstract (intros ??; inversion 1; zify; omega).
  * apply ival_unif_primitive.
Defined.

Fixpoint set_block (v: val) (l: loc) (sz: nat) (init: gmap loc val) : gmap loc val :=
  match sz with
    | O => <[l := v]>init
    | S n' =>  <[(l + Pos.of_succ_nat n')%positive:= v]>(set_block v l n' init)
  end.

Inductive head_step : expr → state → expr → state → list (expr) → Prop :=
  | BetaS f x e1 e2 v2 e' σ :
     to_val e2 = Some v2 →
     Closed (f :b: x :b: []) e1 →
     e' = subst' x (of_val v2) (subst' f (Rec f x e1) e1) →
     head_step (App (Rec f x e1) e2) σ e' σ []
  | UnOpS op e v v' σ :
     to_val e = Some v →
     un_op_eval op v = Some v' → 
     head_step (UnOp op e) σ (of_val v') σ []
  | BinOpS op e1 e2 v1 v2 v' σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     bin_op_eval op v1 v2 = Some v' → 
     head_step (BinOp op e1 e2) σ (of_val v') σ []
  | ProbUnOpS op e1 v1 Idist (v' : ival.isupport (ivd_ival (proj1_sig Idist))) σ :
     to_val e1 = Some v1 →
     prob_un_op_eval op v1 = Some Idist → 
     head_step (ProbUnOp op e1) σ (of_val (proj1_sig v')) σ []
  | ProbBinOpS op e1 e2 v1 v2 Idist (v' : ival.isupport (ivd_ival (proj1_sig Idist))) σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     prob_bin_op_eval op v1 v2 = Some Idist → 
     head_step (ProbBinOp op e1 e2) σ (of_val (proj1_sig v')) σ []
  | IfTrueS e1 e2 σ :
     head_step (If (Lit $ LitBool true) e1 e2) σ e1 σ []
  | IfFalseS e1 e2 σ :
     head_step (If (Lit $ LitBool false) e1 e2) σ e2 σ []
  | FstS e1 v1 e2 v2 σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     head_step (Fst (Pair e1 e2)) σ e1 σ []
  | SndS e1 v1 e2 v2 σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     head_step (Snd (Pair e1 e2)) σ e2 σ []
  | CaseLS e0 v0 e1 e2 σ :
     to_val e0 = Some v0 →
     head_step (Case (InjL e0) e1 e2) σ (App e1 e0) σ []
  | CaseRS e0 v0 e1 e2 σ :
     to_val e0 = Some v0 →
     head_step (Case (InjR e0) e1 e2) σ (App e2 e0) σ []
  | ForkS e σ:
     head_step (Fork e) σ (Lit LitUnit) σ [e]
  | AllocS e v ez size σ l
     (Hrange: ∀ l', (l <= l' < l + Z.to_pos (Zsucc size))%positive → σ !! l' = None) :
     to_val e = Some v →
     to_val ez = Some (LitV $ (LitInt size)) →
     l = Pos.succ (fold_left Pos.max (elements (dom (gset loc) σ)) 1)%positive →
     head_step (Alloc e ez) σ (Lit $ LitLoc l) (set_block v l (Z.to_nat size) σ) []
  | LoadS l v σ :
     σ !! l = Some v →
     head_step (Load (Lit $ LitLoc l)) σ (of_val v) σ []
  | StoreS l e v σ :
     to_val e = Some v → is_Some (σ !! l) →
     head_step (Store (Lit $ LitLoc l) e) σ (Lit LitUnit) (<[l:=v]>σ) []
  | CasFailS l e1 v1 e2 v2 vl σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     σ !! l = Some vl → vl ≠ v1 →
     head_step (CAS (Lit $ LitLoc l) e1 e2) σ (Lit $ LitBool false) σ []
  | CasSucS l e1 v1 e2 v2 σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     σ !! l = Some v1 →
     head_step (CAS (Lit $ LitLoc l) e1 e2) σ (Lit $ LitBool true) (<[l:=v2]>σ) []
  | FaaS l i1 e2 i2 σ :
     to_val e2 = Some (LitV (LitInt i2)) →
     σ !! l = Some (LitV (LitInt i1)) →
     head_step (FAA (Lit $ LitLoc l) e2) σ (Lit $ LitInt i1) (<[l:=LitV (LitInt (i1 + i2))]>σ) [].

(** Basic properties about the language *)
Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

Lemma val_head_stuck e1 σ1 e2 σ2 efs : head_step e1 σ1 e2 σ2 efs → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma head_ctx_step_val Ki e σ1 e2 σ2 efs :
  head_step (fill_item Ki e) σ1 e2 σ2 efs → is_Some (to_val e).
Proof. destruct Ki; inversion_clear 1; simplify_option_eq; by eauto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  destruct Ki1, Ki2; intros; try discriminate; simplify_eq/=;
    repeat match goal with
    | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
    end; auto.
Qed.

Lemma alloc_fresh e ez v sz σ :
  let l := Pos.succ (fold_left Pos.max (elements (dom (gset loc) σ)) 1)%positive in
  to_val e = Some v → 
  to_val ez = Some (LitV $ LitInt sz) → 
  head_step (Alloc e ez) σ (Lit (LitLoc l)) (set_block v l (Z.to_nat sz) σ) [].
Proof.
  intros; apply AllocS; eauto.
  intros l' Hle.
  eapply @not_elem_of_dom with (D := gset loc); first apply _.
  rewrite -elem_of_elements.
  intros Hin.
  cut (l' <= (fold_left Pos.max (elements (dom (gset loc) σ)) 1%positive))%positive.
  { rewrite /l in Hle. zify. omega. }
  apply seq_ext.fold_left_Pmax_ub, elem_of_list_In; auto.
Qed.

(* Misc *)
Lemma to_val_rec f x e `{!Closed (f :b: x :b: []) e} :
  to_val (Rec f x e) = Some (RecV f x e).
Proof. rewrite /to_val. case_decide=> //. do 2 f_equal; apply proof_irrel. Qed.

(** Closed expressions *)
Lemma is_closed_weaken X Y e : is_closed X e → X ⊆ Y → is_closed Y e.
Proof. revert X Y; induction e; naive_solver (eauto; set_solver). Qed.

Lemma is_closed_weaken_nil X e : is_closed [] e → is_closed X e.
Proof. intros. by apply is_closed_weaken with [], list_subseteq_nil. Qed.

Lemma is_closed_of_val X v : is_closed X (of_val v).
Proof. apply is_closed_weaken_nil. induction v; simpl; auto. Qed.

Lemma is_closed_to_val X e v : to_val e = Some v → is_closed X e.
Proof. intros <-%of_to_val. apply is_closed_of_val. Qed.

Lemma is_closed_subst X e x es :
  is_closed [] es → is_closed (x :: X) e → is_closed X (subst x es e).
Proof.
  intros ?. revert X.
  induction e=> X /= ?; destruct_and?; split_and?; simplify_option_eq;
    try match goal with
    | H : ¬(_ ∧ _) |- _ => apply not_and_l in H as [?%dec_stable|?%dec_stable]
    end; eauto using is_closed_weaken with set_solver.
Qed.
Lemma is_closed_do_subst' X e x es :
  is_closed [] es → is_closed (x :b: X) e → is_closed X (subst' x es e).
Proof. destruct x; eauto using is_closed_subst. Qed.

(* Substitution *)
Lemma subst_is_closed X e x es : is_closed X e → x ∉ X → subst x es e = e.
Proof.
  revert X. induction e=> X /=; rewrite ?bool_decide_spec ?andb_True=> ??;
    repeat case_decide; simplify_eq/=; f_equal; intuition eauto with set_solver.
Qed.

Lemma subst_is_closed_nil e x es : is_closed [] e → subst x es e = e.
Proof. intros. apply subst_is_closed with []; set_solver. Qed.

Lemma subst_subst e x es es' :
  Closed [] es' → subst x es (subst x es' e) = subst x es' e.
Proof.
  intros. induction e; simpl; try (f_equal; by auto);
    simplify_option_eq; auto using subst_is_closed_nil with f_equal.
Qed.
Lemma subst_subst' e x es es' :
  Closed [] es' → subst' x es (subst' x es' e) = subst' x es' e.
Proof. destruct x; simpl; auto using subst_subst. Qed.

Lemma subst_subst_ne e x y es es' :
  Closed [] es → Closed [] es' → x ≠ y →
  subst x es (subst y es' e) = subst y es' (subst x es e).
Proof.
  intros. induction e; simpl; try (f_equal; by auto);
    simplify_option_eq; auto using eq_sym, subst_is_closed_nil with f_equal.
Qed.
Lemma subst_subst_ne' e x y es es' :
  Closed [] es → Closed [] es' → x ≠ y →
  subst' x es (subst' y es' e) = subst' y es' (subst' x es e).
Proof. destruct x, y; simpl; auto using subst_subst_ne with congruence. Qed.

Lemma subst_rec' f y e x es :
  x = f ∨ x = y ∨ x = BAnon →
  subst' x es (Rec f y e) = Rec f y e.
Proof. intros. destruct x; simplify_option_eq; naive_solver. Qed.
Lemma subst_rec_ne' f y e x es :
  (x ≠ f ∨ f = BAnon) → (x ≠ y ∨ y = BAnon) →
  subst' x es (Rec f y e) = Rec f y (subst' x es e).
Proof. intros. destruct x; simplify_option_eq; naive_solver. Qed.

Import Rdefinitions.

Inductive head_step_prob_rel : expr → state → expr → state → list (expr) → R → Prop :=
  | ProbUnOpSP op e1 v1 Idist (i: ival.idx (ivd_ival (proj1_sig Idist))) σ :
     to_val e1 = Some v1 →
     prob_un_op_eval op v1 = Some Idist → 
     (ival.val (ivd_ival (proj1_sig Idist)) i > 0)%R →
     head_step_prob_rel (ProbUnOp op e1) σ (of_val (ival.ind (ivd_ival (proj1_sig Idist)) i)) σ
                        []
                        (ival.val (ivd_ival (proj1_sig Idist)) i)
  | ProbBinOpSP op e1 e2 v1 v2 Idist (i: ival.idx (ivd_ival (proj1_sig Idist))) σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     prob_bin_op_eval op v1 v2 = Some Idist → 
     (ival.val (ivd_ival (proj1_sig Idist)) i > 0)%R →
     head_step_prob_rel (ProbBinOp op e1 e2) σ (of_val (ival.ind (ivd_ival (proj1_sig Idist)) i)) σ
                        []
                        (ival.val (ivd_ival (proj1_sig Idist)) i)
  | NonPropS e1 σ1 e2 σ2 efs:
      head_step e1 σ1 e2 σ2 efs →
      (∀ op eop, e1 ≠ ProbUnOp op eop) →
      (∀ op eop1 eop2, e1 ≠ ProbBinOp op eop1 eop2) →
      head_step_prob_rel e1 σ1 e2 σ2 efs 1.

Global Program Instance Rgt_dec_instance x y : Decision ((x > y)%R) := RIneq.Rgt_dec x y.
Definition head_step_prob (e1 : expr) (σ1 : state) (e2 : expr) (σ2 : state) (efs : list expr) :
  R.
  destruct (ClassicalEpsilon.excluded_middle_informative
              (head_step e1 σ1 e2 σ2 efs)) as [Hhead|Hnostep].
  - refine (match e1 as e return (e1 = e → R) with
            | ProbUnOp op eop1 => _
            | ProbBinOp op eop1 eop2 => _
            | _ => λ _,  R1
            end eq_refl); intros ->.
    *  assert (∃ Idist i v1,
                 to_val eop1 = Some v1  ∧
                 prob_un_op_eval op v1 = Some Idist ∧
                 to_val e2 = Some (ival.ind (proj1_sig Idist) i) ∧
                 ival.val (proj1_sig Idist) i > 0)%R as Hex.
      { inversion Hhead. destruct v' as (?&i&?&?).
        exists Idist, i. do 1 eexists; split_and!; eauto;
                           abstract(rewrite //=; rewrite to_of_val; congruence).
      }
      apply ClassicalEpsilon.constructive_indefinite_description in Hex.
      destruct Hex as (Idist&Hex).
      apply ClassicalEpsilon.constructive_indefinite_description in Hex.
      destruct Hex as (i&Hex).
      exact (ival.val (ivd_ival (proj1_sig Idist)) i).
    * assert (∃ Idist i v1 v2,
                 to_val eop1 = Some v1 ∧ to_val eop2 = Some v2  ∧
                 prob_bin_op_eval op v1 v2 = Some Idist ∧
                 to_val e2 = Some (ival.ind (proj1_sig Idist) i) ∧
                 ival.val (proj1_sig Idist) i > 0)%R as Hex.
      { inversion Hhead. destruct v' as (?&i&?&?).
        exists Idist, i. do 2 eexists; split_and!; eauto;
                           abstract(rewrite //=; rewrite to_of_val; congruence).
      }
      apply ClassicalEpsilon.constructive_indefinite_description in Hex.
      destruct Hex as (Idist&Hex).
      apply ClassicalEpsilon.constructive_indefinite_description in Hex.
      destruct Hex as (i&Hex).
      exact (ival.val (ivd_ival (proj1_sig Idist)) i).
  - exact R0.
Defined.

Import eqtype.

Lemma remove_dups_map `{EqDecision A} `{EqDecision B} (l: list A) (f: A → B)
      (Hinj: Inj eq eq f):
  remove_dups (map f l) = map f (remove_dups l).
Proof.
  induction l => //=.
  destruct decide_rel as [Helem_map|Hnot_map];
    destruct decide_rel as [Helem|Hnot]; auto.
  - rewrite elem_of_list_In in Hnot *. 
    rewrite elem_of_list_In in Helem_map *.
    intros (?&Heq&?)%in_map_iff.
    apply Hinj in Heq. congruence.
  - rewrite elem_of_list_In in Hnot_map * => Hnot.
    rewrite elem_of_list_In in Helem * => Helem.
    exfalso; apply Hnot. apply in_map_iff; exists a; auto.
  - rewrite //=. by f_equal. 
Qed.
             

Lemma head_step_nonneg : ∀ e1 σ1 e2 σ2 efs, (head_step_prob e1 σ1 e2 σ2 efs >= 0)%R.
Proof.
  intros. rewrite /head_step_prob.
  destruct ClassicalEpsilon.excluded_middle_informative => //=; eauto; last try nra.
  destruct e1; try nra.
  * rewrite /eq_rec_r //=.
    destruct ClassicalEpsilon.constructive_indefinite_description as (Idist&?).
    destruct ClassicalEpsilon.constructive_indefinite_description as (v'&?).
    apply ival.val_nonneg.
  * rewrite /eq_rec_r //=.
    destruct ClassicalEpsilon.constructive_indefinite_description as (Idist&?).
    destruct ClassicalEpsilon.constructive_indefinite_description as (v'&?).
    apply ival.val_nonneg.
Qed.

Lemma head_step_strict_gt :
    ∀ e1 σ1 e2 σ2 efs, head_step e1 σ1 e2 σ2 efs ↔ (head_step_prob e1 σ1 e2 σ2 efs > 0)%R.
Proof.
  intros; split.
  - intros Hstep.
    rewrite /head_step_prob.
    destruct ClassicalEpsilon.excluded_middle_informative => //=; eauto; [].
    destruct e1; try nra; [|].
    * rewrite /eq_rec_r //=;
      destruct ClassicalEpsilon.constructive_indefinite_description as (Idist&?).
      destruct ClassicalEpsilon.constructive_indefinite_description as (v'0&?&?&?&?&?).
      auto.
    * rewrite /eq_rec_r //=;
      destruct ClassicalEpsilon.constructive_indefinite_description as (Idist&?).
      destruct ClassicalEpsilon.constructive_indefinite_description as (v'0&?&?&?&?&?&?&?).
      auto.
  - rewrite /head_step_prob.
    destruct ClassicalEpsilon.excluded_middle_informative => //=; eauto; [].
    intros; nra.
Qed.

Lemma Countable_to_pcancel {T: Type} `{EqDecision T} (HC: Countable T):
    ssrfun.pcancel (λ x : T, Pos.to_nat (@encode _ _ HC x))
                   (λ x, @decode _ _ HC (Pos.of_nat x)).
Proof.
  rewrite /ssrfun.pcancel.
  intros x.
  destruct HC => //=.
  rewrite /countable.decode/countable.encode.
  rewrite Pos2Nat.id decode_encode //=.
Qed.

Definition StdppCountEqMixin {T : Type} `{EqDecision T}:
  Countable T → Equality.mixin_of T.
Proof.
  intros HC.
  eapply (@PcanEqMixin T [countType of nat] (λ x, Pos.to_nat (@encode _ _ HC x))
                       (λ x, @decode _ _ HC (Pos.of_nat x))).
  apply Countable_to_pcancel.
Qed.

Definition StdppCountChoiceMixin {T : Type} `{EqDecision T}:
  Countable T → Choice.mixin_of T.
Proof.
  intros HC.
  eapply (@PcanChoiceMixin [countType of nat] _ (λ x, Pos.to_nat (@encode _ _ HC x))
                       (λ x, @decode _ _ HC (Pos.of_nat x))).
  apply Countable_to_pcancel.
Qed.

Definition StdppCountCountMixin {T : Type} `{EqDecision T}:
  Countable T → Countable.mixin_of T.
Proof.
  intros HC.
  eapply (@PcanCountMixin [countType of nat] _ (λ x, Pos.to_nat (@encode _ _ HC x))
                       (λ x, @decode _ _ HC (Pos.of_nat x))).
  apply Countable_to_pcancel.
Qed.

Instance sig_eqdecision {T : Type} `{EqDecision T} (P: T → Prop):
  EqDecision T → EqDecision {x : T | P x}.
Proof.
  intros Heq (x&Hpf1) (y&Hpf2).
  - destruct (Heq x y).
    * rewrite /Decision. left. apply sval.sval_inj_pi => //=.
    * right. inversion 1; subst; eauto.
Qed.

Definition sig_countable {T : Type} `{EqDecision T} (P: T → Prop):
  Countable T → Countable {x : T | P x}.
Proof.
  intros [enc dec Hed].
  unshelve (eexists).
  * intros (x&Hp). exact (enc x).
  * intros n. apply dec in n.
    destruct n as [t|].
    ** destruct (ClassicalEpsilon.excluded_middle_informative (P t)).
       *** apply Some; exists t; eauto. 
       *** apply None.
    ** apply None.
  * intros (x&Hp) => //=.
    rewrite Hed. destruct ClassicalEpsilon.excluded_middle_informative; eauto.
    ** f_equal. apply sval.sval_inj_pi => //=.
    ** exfalso; eauto.
Qed.

Lemma head_step_count e σ:
      Countable.class_of { esf: expr * state * list expr |
                           head_step e σ (esf.1.1) (esf.1.2) (esf.2) }.
Proof.
  split.
  - split.
    * apply StdppCountEqMixin. apply sig_countable. apply _.
    * apply StdppCountChoiceMixin. apply sig_countable. apply _.
  - apply StdppCountCountMixin. apply sig_countable. apply _.
Qed.
  
Import Series.

Lemma head_step_non_prob_det e1 σ1 e2 σ2 efs e2' σ2' efs'
      (Hnprobb : ∀ (op : prob_bin_op) (eop1 eop2 : expr), e1 ≠ ProbBinOp op eop1 eop2)
      (Hnprobu : ∀ (op : prob_un_op) (eop1 : expr), e1 ≠ ProbUnOp op eop1):
  head_step e1 σ1 e2 σ2 efs  →
  head_step e1 σ1 e2' σ2' efs'  →
  e2 = e2' ∧ σ2 = σ2' ∧ efs = efs'.
Proof.
  intros Hstep1 Hstep2.
  destruct e1;
    try (exfalso; eapply Hnprobu; eauto; fail);
    try (exfalso; eapply Hnprobb; eauto; fail);
    try (inversion Hstep1; inversion Hstep2; subst; split_and!; try congruence; eauto).
Qed.

Lemma head_step_non_prob_det_prob1 e1 σ1 e2 σ2 efs
      (Hnprobb : ∀ (op : prob_bin_op) (eop1 eop2 : expr), e1 ≠ ProbBinOp op eop1 eop2)
      (Hnprobu : ∀ (op : prob_un_op) (eop1 : expr), e1 ≠ ProbUnOp op eop1):
  head_step e1 σ1 e2 σ2 efs  →
  head_step_prob e1 σ1 e2 σ2 efs = 1%R.
Proof.
  intros Hstep1.
  destruct e1;
    try (exfalso; eapply Hnprobb; eauto; fail);
    try (exfalso; eapply Hnprobu; eauto; fail);
  rewrite /head_step_prob;
  destruct ClassicalEpsilon.excluded_middle_informative as [?|Hn]; eauto;
                             exfalso; eapply Hn; eauto.
Qed.

Lemma head_step_prob_idx op eop1 eop2 v1 v2 σ1 e2 σ2 efs Idist: 
  to_val eop1 = Some v1 →
  to_val eop2 = Some v2 →
  prob_bin_op_eval op v1 v2 = Some Idist →
  head_step (ProbBinOp op eop1 eop2) σ1 e2 σ2 efs →
           {i : ival.idx (sval Idist) | of_val (ival.ind (sval Idist) i) = e2}.
Proof.
  intros ?? Hop Hstep.
  apply ClassicalEpsilon.constructive_indefinite_description.
  inversion Hstep. subst.
  repeat match goal with
           [ H1 : to_val ?e = Some ?v1, H2 : to_val ?e = Some ?v2 |- _ ] =>
           assert (v1 = v2) by abstract(congruence); subst; clear H2
         end.
  match goal with
    [ H1 : prob_bin_op_eval ?op ?v1 ?v2 = Some ?Idist1,
           H2 : prob_bin_op_eval ?op ?v1 ?v2 = Some ?Idist2 |- _] =>
    assert (Idist1 = Idist2) by abstract(congruence); subst; clear H2
  end.
  match goal with
    [ H : ival.isupport _ |- _ ] => destruct H as (?&ix&?)
  end.
  exists ix => //=. rewrite //= in Hstep. intuition. congruence.
Qed.

Lemma head_step_probu_idx op eop1 v1 σ1 e2 σ2 efs Idist: 
  to_val eop1 = Some v1 →
  prob_un_op_eval op v1 = Some Idist →
  head_step (ProbUnOp op eop1) σ1 e2 σ2 efs →
           {i : ival.idx (sval Idist) | of_val (ival.ind (sval Idist) i) = e2}.
Proof.
  intros ? Hop Hstep.
  apply ClassicalEpsilon.constructive_indefinite_description.
  inversion Hstep. subst.
  repeat match goal with
           [ H1 : to_val ?e = Some ?v1, H2 : to_val ?e = Some ?v2 |- _ ] =>
           assert (v1 = v2) by abstract(congruence); subst; clear H2
         end.
  match goal with
    [ H1 : prob_un_op_eval ?op ?v1 = Some ?Idist1,
           H2 : prob_un_op_eval ?op ?v1 = Some ?Idist2 |- _] =>
    assert (Idist1 = Idist2) by abstract(congruence); subst; clear H2
  end.
  match goal with
    [ H : ival.isupport _ |- _ ] => destruct H as (?&ix&?)
  end.
  exists ix => //=. rewrite //= in Hstep. intuition. congruence.
Qed.

Lemma head_step_prob_idx_val op eop1 eop2 v1 v2 σ1 e2 σ2 efs Idist ix:
  to_val eop1 = Some v1 →
  to_val eop2 = Some v2 →
  prob_bin_op_eval op v1 v2 = Some Idist →
  head_step (ProbBinOp op eop1 eop2) σ1 e2 σ2 efs →
  of_val (ival.ind (sval Idist) ix) = e2 →
  head_step_prob (ProbBinOp op eop1 eop2) σ1 e2 σ2 efs = ival.val (sval Idist) ix.
Proof.
  intros Hval1 Hval2 Hop Hstep Hidx.
  rewrite /head_step_prob.
  destruct ClassicalEpsilon.excluded_middle_informative => //=.
  rewrite /eq_rec_r //=.
  rewrite //=.
  destruct ClassicalEpsilon.constructive_indefinite_description as
      (Idist'&ix'&v1'&v2'&Hdist'&Hval1'&Hval2'&Hix'&Hsupp') => //=.
  destruct Idist' as (Idist'&Hprim) => //=. 
  destruct ClassicalEpsilon.constructive_indefinite_description as
      (ix''&v1''&v2''&Hdist''&Hval1''&Hval2''&Hix''&Hsupp'') => //=.
  rewrite //= in Hix'.
  repeat match goal with
           [ H1 : to_val ?e = Some ?v1, H2 : to_val ?e = Some ?v2 |- _ ] =>
           assert (v1 = v2) by abstract(congruence); subst; clear H2
         end.
  repeat match goal with
    [ H1 : prob_bin_op_eval ?op ?v1 ?v2 = Some ?Idist1,
           H2 : prob_bin_op_eval ?op ?v1 ?v2 = Some ?Idist2 |- _] =>
    assert (Idist1 = Idist2) by abstract(congruence); subst; clear H2
  end.
  f_equal.
  apply Hprim; eauto.
  rewrite to_of_val //= in Hix''. congruence.
Qed.

Lemma head_step_probu_idx_val op eop1 v1 σ1 e2 σ2 efs Idist ix:
  to_val eop1 = Some v1 →
  prob_un_op_eval op v1 = Some Idist →
  head_step (ProbUnOp op eop1) σ1 e2 σ2 efs →
  of_val (ival.ind (sval Idist) ix) = e2 →
  head_step_prob (ProbUnOp op eop1) σ1 e2 σ2 efs = ival.val (sval Idist) ix.
Proof.
  intros Hval1 Hop Hstep Hidx.
  rewrite /head_step_prob.
  destruct ClassicalEpsilon.excluded_middle_informative => //=.
  rewrite /eq_rec_r //=.
  rewrite //=.
  destruct ClassicalEpsilon.constructive_indefinite_description as
      (Idist'&ix'&v1'&Hdist'&Hval1'&Hix'&Hsupp') => //=.
  destruct Idist' as (Idist'&Hprim) => //=. 
  destruct ClassicalEpsilon.constructive_indefinite_description as
      (ix''&v1''&Hdist''&Hval1''&Hix''&Hsupp'') => //=.
  rewrite //= in Hix'.
  repeat match goal with
           [ H1 : to_val ?e = Some ?v1, H2 : to_val ?e = Some ?v2 |- _ ] =>
           assert (v1 = v2) by abstract(congruence); subst; clear H2
         end.
  repeat match goal with
    [ H1 : prob_un_op_eval ?op ?v1 = Some ?Idist1,
           H2 : prob_un_op_eval ?op ?v1 = Some ?Idist2 |- _] =>
    assert (Idist1 = Idist2) by abstract(congruence); subst; clear H2
  end.
  f_equal.
  apply Hprim; eauto.
  rewrite to_of_val //= in Hix''. congruence.
Qed.

Lemma head_step_prob_to_rel e1 σ1 e2 σ2 efs:
  head_step e1 σ1 e2 σ2 efs →
  head_step_prob_rel e1 σ1 e2 σ2 efs (head_step_prob e1 σ1 e2 σ2 efs).
Proof.
  intros Hstep.
  destruct e1; try (rewrite head_step_non_prob_det_prob1; eauto; econstructor; eauto).
  - inversion Hstep; subst.
    destruct v' as (v&i&Heqiv&Hgt0).
    rewrite //= in Hstep.
    erewrite head_step_probu_idx_val; eauto.
    * rewrite //=. rewrite -Heqiv. econstructor; eauto.
    * rewrite //=. f_equal; eauto.
  - inversion Hstep; subst.
    destruct v' as (v&i&Heqiv&Hgt0).
    rewrite //= in Hstep.
    erewrite head_step_prob_idx_val; eauto.
    * rewrite //=. rewrite -Heqiv. econstructor; eauto.
    * rewrite //=. f_equal; eauto.
Qed.

Lemma head_step_prob_rel_to_fun e1 σ1 e2 σ2 efs r:
  head_step_prob_rel e1 σ1 e2 σ2 efs r →
  head_step e1 σ1 e2 σ2 efs ∧ head_step_prob e1 σ1 e2 σ2 efs = r.
Proof.
  intros Hstep.
  inversion Hstep; subst.
  - assert (∃ (v' : ival.isupport (ivd_ival (proj1_sig Idist))),
              (sval v' = (ival.ind (sval Idist) i))) as (v'&Heq).
    { unshelve eexists.
      { exists ((ival.ind (sval Idist) i)).
        exists i; split; auto. }
      rewrite //=.
    }
    rewrite -?Heq.
    split; first by econstructor; eauto.
    eapply head_step_probu_idx_val; eauto.
    { econstructor; eauto. }
    { congruence. }
  - assert (∃ (v' : ival.isupport (ivd_ival (proj1_sig Idist))),
              (sval v' = (ival.ind (sval Idist) i))) as (v'&Heq).
    { unshelve eexists.
      { exists ((ival.ind (sval Idist) i)).
        exists i; split; auto. }
      rewrite //=.
    }
    rewrite -?Heq.
    split; first by econstructor; eauto.
    eapply head_step_prob_idx_val; eauto.
    { econstructor; eauto. }
    { congruence. }
  - split; eauto.
    eapply head_step_non_prob_det_prob1; eauto.
Qed.

Lemma heap_lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step head_step_prob.
Proof.
  unshelve (econstructor; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
    fill_item_val, fill_item_no_val_inj, head_ctx_step_val,
    head_ctx_step_val, head_step_nonneg, 
    head_step_strict_gt).
  * intros. apply head_step_count.
  * intros e1 σ1 Hstep.
    destruct Hstep as (e2&σ2&efs&Hstep).
    assert ((∃ op eop1 eop2, e1 = ProbBinOp op eop1 eop2) ∨ 
            (∃ op eop1, e1 = ProbUnOp op eop1) ∨
            ((∀ op eop1 eop2, e1 ≠ ProbBinOp op eop1 eop2) ∧
             (∀ op eop1, e1 ≠ ProbUnOp op eop1))) as [Hprobb | [Hprobu |[Hnprobb Hnoprobu]]].
    { destruct e1; eauto.  }
    ** destruct Hprobb as (op&eop1&eop2&Heq).
       subst. inversion Hstep; subst.
       rewrite -(is_series_unique _ _ (ival_dist.val_sum1 (sval Idist))).
       unshelve (edestruct (@rearrange.countable_series_rearrange_covering
                              (Countable.Pack (head_step_count (ProbBinOp op eop1 eop2) σ2)
                                              {esf : expr * state * list expr |
                                               head_step (ProbBinOp op eop1 eop2) σ2 esf.1.1
                                                         esf.1.2 esf.2})
                              (ival.idx (sval Idist)))
                  as (His1&His2)); last (eapply is_seriesC_ext; last eapply His2).
       { intros (esf&Hstep'). 
         assert {i : ival.idx (sval Idist) | of_val (ival.ind (sval Idist) i) = esf.1.1}
                as (i&Heq).
         { eapply head_step_prob_idx; last try eassumption; eauto. }
         exact i.
       }
       { exact 1%R. }
       { intros (esf1&Hstep1) (esf2&Hstep2) Hneq0.
         destruct esf1 as [[? ?] ?].
         destruct esf2 as [[? ?] ?].
         rewrite //= in Hstep1 Hstep2 Hneq0 *.
         rewrite //=.
         destruct head_step_prob_idx as (i1&Heqi1).
         destruct head_step_prob_idx as (i2&Heqi2).
         rewrite //=. intros; subst.
         inversion Hstep1; subst.
         inversion Hstep2; subst.
         apply sval.sval_inj_pi => //=.
       }
       { intros ix Hneq0.
         unshelve (eexists).
         { unshelve (eexists (of_val _, σ2, []));
             last unshelve (econstructor; eauto).
           eexists. exists ix. split_and!; eauto.
           { abstract (destruct (ival.val_nonneg _ ix); eauto; exfalso; nra). }
         }
         rewrite //=. destruct head_step_prob_idx as (ix'&Heq).
         apply of_val_inj in Heq.
         destruct Idist as (?&Hprim). apply Hprim in Heq. auto.
       }
       { eapply is_seriesC_ext; last eapply ival_dist.val_sum1.
         intros n. rewrite Rbasic_fun.Rabs_right //=.
         apply ival.val_nonneg.
       }
       { intros (efs1&Hstep1) => //=.
         destruct head_step_prob_idx => //=.
         symmetry; eapply head_step_prob_idx_val; eauto.
       }
    ** destruct Hprobu as (op&eop1&Heq).
       subst. inversion Hstep; subst.
       rewrite -(is_series_unique _ _ (ival_dist.val_sum1 (sval Idist))).
       unshelve (edestruct (@rearrange.countable_series_rearrange_covering
                              (Countable.Pack (head_step_count (ProbUnOp op eop1) σ2)
                                              {esf : expr * state * list expr |
                                               head_step (ProbUnOp op eop1) σ2 esf.1.1
                                                         esf.1.2 esf.2})
                              (ival.idx (sval Idist)))
                  as (His1&His2)); last (eapply is_seriesC_ext; last eapply His2).
       { intros (esf&Hstep'). 
         assert {i : ival.idx (sval Idist) | of_val (ival.ind (sval Idist) i) = esf.1.1}
                as (i&Heq).
         { eapply head_step_probu_idx; last try eassumption; eauto. }
         exact i.
       }
       { exact 1%R. }
       { intros (esf1&Hstep1) (esf2&Hstep2) Hneq0.
         destruct esf1 as [[? ?] ?].
         destruct esf2 as [[? ?] ?].
         rewrite //= in Hstep1 Hstep2 Hneq0 *.
         rewrite //=.
         destruct head_step_probu_idx as (i1&Heqi1).
         destruct head_step_probu_idx as (i2&Heqi2).
         rewrite //=. intros; subst.
         inversion Hstep1; subst.
         inversion Hstep2; subst.
         apply sval.sval_inj_pi => //=.
       }
       { intros ix Hneq0.
         unshelve (eexists).
         { unshelve (eexists (of_val _, σ2, []));
             last unshelve (econstructor; eauto).
           eexists. exists ix. split_and!; eauto.
           { abstract (destruct (ival.val_nonneg _ ix); eauto; exfalso; nra). }
         }
         rewrite //=. destruct head_step_probu_idx as (ix'&Heq).
         apply of_val_inj in Heq.
         destruct Idist as (?&Hprim). apply Hprim in Heq. auto.
       }
       { eapply is_seriesC_ext; last eapply ival_dist.val_sum1.
         intros n. rewrite Rbasic_fun.Rabs_right //=.
         apply ival.val_nonneg.
       }
       { intros (efs1&Hstep1) => //=.
         destruct head_step_probu_idx => //=.
         symmetry; eapply head_step_probu_idx_val; eauto.
       }
    ** eapply (is_seriesC_ext  _
                              (λ x, if x == (exist _ (e2, σ2, efs) Hstep :
                                               Countable.Pack (head_step_count e1 σ1)
                                                              {esf : expr * state * list expr |
                                                               head_step e1 σ1 esf.1.1 esf.1.2 esf.2}
                                            ) then 1%R else 0%R)).
      { intros (esf&Hstep').
        destruct esf as [[e2' σ2'] efs'].
        rewrite //= in Hstep' *.
        edestruct (head_step_non_prob_det _ _ _ _ _ _ _ _ Hnprobb Hnoprobu Hstep Hstep')
          as (Heq1&Heq2&Heq3); subst.
        assert (Hstep = Hstep').
        { apply classical_proof_irrelevance. }
        subst. rewrite eq_refl.
        symmetry. eapply head_step_non_prob_det_prob1; eauto.
      }
      eapply is_seriesC_bump.
Qed.
End heap_lang.


(** Language *)
Canonical Structure heap_ectxi_lang := EctxiLanguage heap_lang.heap_lang_mixin.
Canonical Structure heap_ectx_lang := EctxLanguageOfEctxi heap_ectxi_lang.
Canonical Structure heap_prob_lang := ProbLanguageOfEctx heap_ectx_lang.
Canonical Structure heap_lang := LanguageOfProb heap_prob_lang.

(* Prefer heap_lang names over ectx_language names. *)
Export heap_lang.

(** Define some derived forms *)
Notation Lam x e := (Rec BAnon x e).
Notation Let x e1 e2 := (App (Lam x e2) e1).
Notation Seq e1 e2 := (Let BAnon e1 e2).
Notation LamV x e := (RecV BAnon x e).
Notation LetCtx x e2 := (AppRCtx (LamV x e2)).
Notation SeqCtx e2 := (LetCtx BAnon e2).
Notation Skip := (Seq (Lit LitUnit) (Lit LitUnit)).
Notation Match e0 x1 e1 x2 e2 := (Case e0 (Lam x1 e1) (Lam x2 e2)).
