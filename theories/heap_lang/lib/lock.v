From iris.heap_lang Require Export lifting notation.
From iris.base_logic.lib Require Export invariants.
Set Default Proof Using "Type".

Structure lock Σ `{!heapG Σ, !probG Σ} := Lock {
  (* -- operations -- *)
  newlock : val;
  acquire : val;
  release : val;
  (* -- predicates -- *)
  (* name is used to associate locked with is_lock *)
  name : Type;
  is_lock (N: namespace) (γ: name) (lock: val) (R: iProp Σ) : iProp Σ;
  locked (γ: name) : iProp Σ;
  (* -- general properties -- *)
  is_lock_ne N γ lk : NonExpansive (is_lock N γ lk);
  is_lock_persistent N γ lk R : Persistent (is_lock N γ lk R);
  locked_timeless γ : Timeless (locked γ);
  locked_exclusive γ : locked γ -∗ locked γ -∗ False;
  (* -- operation specs -- *)
  newlock_spec N (R : iProp Σ) :
    {{{ R }}} newlock #() {{{ lk γ, RET lk; is_lock N γ lk R }}};
  acquire_spec N γ lk R :
    {{{ is_lock N γ lk R }}} acquire lk {{{ RET #(); locked γ ∗ R }}};
  release_spec N γ lk R :
    {{{ is_lock N γ lk R ∗ locked γ ∗ R }}} release lk {{{ RET #(); True }}}
}.

Arguments newlock {_ _ _} _.
Arguments acquire {_ _ _} _.
Arguments release {_ _ _} _.
Arguments is_lock {_ _ _} _ _ _ _ _.
Arguments locked {_ _ _} _ _.

Existing Instances is_lock_ne is_lock_persistent locked_timeless.

Instance is_lock_proper Σ `{!heapG Σ, !probG Σ} (L: lock Σ) N γ lk:
  Proper ((≡) ==> (≡)) (is_lock L N γ lk) := ne_proper _.

