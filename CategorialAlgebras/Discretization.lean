import Stemma
import Mathlib.CategoryTheory.Adjunction.Basic
import CategorialAlgebras.Graduation

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "Discretization and truncation" =>

Discretization regards an $`m`-categorial algebra as an $`n`-categorial algebra whose cells of
dimension at least $`m` are identities, and truncation forgets the cells of dimension greater than
$`m` (Section `STruncation` of the draft). As graduation and unification, both are induced by
generalized ep-derivors, in the compact and in the extended presentations.

The draft takes $`m \leq n`. The compact discretization derivor below is defined, and sends models
to models, for all $`m` and $`n`; for $`m \geq n` it keeps every dimension of $`n`.

```lean
universe u v w

namespace CategorialAlgebras

open Signature Term CategoryTheory

variable {S : Type u} (Sig : Signature.{u, v} S) (n m : ℕ)
```

# Compact discretization

:::definition (label := "discretization-derivor") (central := false) (title := "The compact discretization derivor")
The *compact discretization derivor* $`\boldsymbol{\delta}^{(n,m)} = (\mathrm{id}_S, D, d)` is the
generalized ep-derivor from $`\mathbf{\Sigma}^{(n)}` to $`\mathbf{\Sigma}^{(m)}` with $`D_s = \varnothing`,
$`d(\sigma) = \sigma((v_p)_p)`, and, for $`k \in n`: if $`k < m`,
$`d(\mathrm{sc}^{k}_{s}) = \mathrm{sc}^{k}_{s}(v_0)`, $`d(\mathrm{tg}^{k}_{s}) = \mathrm{tg}^{k}_{s}(v_0)` and
$`d(\circ^{k}_{s}) = v_0 \circ^{k}_{s} v_1`; if $`k \geq m`,
$`d(\mathrm{sc}^{k}_{s}) = d(\mathrm{tg}^{k}_{s}) = d(\circ^{k}_{s}) = v_0`.

For $`k \geq m` the derived $`\circ^{k}_{s}` is total, but its domain condition
$`\mathrm{sc}^{k}_{s}(v_0) \overset{\mathrm{e}}{=} \mathrm{tg}^{k}_{s}(v_1)` becomes $`v_0 \overset{\mathrm{e}}{=} v_1`:
two cells are $`k`-composable exactly when they are equal.

```lean
/-- The terms of the compact discretization derivor. -/
def discOp : ∀ {ws : List S} {s : S}, Compact.CompactSignature Sig (Fin n) ws s →
    Term (Compact.CompactSignature Sig (Fin m)) (Vars (id ∘ ws.get)) s
  | _, _, .op σ => .app (.op σ) fun j => .var (Vars.mk j)
  | _, _, .sc k s => if hk : k.val < m then app₁ (.sc ⟨k.val, hk⟩ s) (.var ⟨⟨0, by simp⟩, rfl⟩)
      else .var ⟨⟨0, by simp⟩, rfl⟩
  | _, _, .tg k s => if hk : k.val < m then app₁ (.tg ⟨k.val, hk⟩ s) (.var ⟨⟨0, by simp⟩, rfl⟩)
      else .var ⟨⟨0, by simp⟩, rfl⟩
  | _, _, .comp k s => if hk : k.val < m then
      app₂ (.comp ⟨k.val, hk⟩ s) (.var ⟨⟨0, by simp⟩, rfl⟩) (.var ⟨⟨1, by simp⟩, rfl⟩)
      else .var ⟨⟨0, by simp⟩, rfl⟩

/-- The compact discretization derivor `𝛅^{(n,m)}`. -/
def disc : GenEpDerivor (compactEpSig Sig (Fin n)) (compactEpSig Sig (Fin m)) where
  sortMap := id
  sortDom _ := ∅
  op := discOp Sig n m
```
:::

The discretized algebra $`(\boldsymbol{\delta}^{(n,m)})^{\ast}_{\mathfrak{gd}}(\mathbf{B})` of a model
$`\mathbf{B}` has the cells of $`\mathbf{B}`; its operations of dimension $`k < m` are those of
$`\mathbf{B}`, and for $`k \geq m` its $`k`-sources and $`k`-targets are identities and $`x \circ^{k} y`
is defined exactly when $`x = y`, and then it is $`x`.

```lean
namespace Disc

open Compact.CategoryStruct

variable {Sig n m}

/-- The discretized algebra. -/
noncomputable abbrev D (n : ℕ) (M : Compact.CompactPAlg.{u, v, w} Sig (Fin m)) :=
  (disc Sig n m).derived M.1

variable {M : Compact.CompactPAlg.{u, v, w} Sig (Fin m)}

variable (M) in
/-- The `k`-source of the discretized algebra: the identity for `k ≥ m`. -/
noncomputable def dsc (k : Fin n) {s : S} (x : D n M s) : D n M s :=
  ⟨if hk : k.val < m then Compact.msc M ⟨k.val, hk⟩ x.1 else x.1, EEq.holdsAll_empty⟩

variable (M) in
noncomputable def dtg (k : Fin n) {s : S} (x : D n M s) : D n M s :=
  ⟨if hk : k.val < m then Compact.mtg M ⟨k.val, hk⟩ x.1 else x.1, EEq.holdsAll_empty⟩

lemma dsc_lt {k : Fin n} (hk : k.val < m) {s : S} (x : D n M s) :
    (dsc M k x).1 = Compact.msc M ⟨k.val, hk⟩ x.1 := dif_pos hk

lemma dtg_lt {k : Fin n} (hk : k.val < m) {s : S} (x : D n M s) :
    (dtg M k x).1 = Compact.mtg M ⟨k.val, hk⟩ x.1 := dif_pos hk

lemma dsc_ge {k : Fin n} (hk : ¬ k.val < m) {s : S} (x : D n M s) : dsc M k x = x :=
  Subtype.ext (dif_neg hk)

lemma dtg_ge {k : Fin n} (hk : ¬ k.val < m) {s : S} (x : D n M s) : dtg M k x = x :=
  Subtype.ext (dif_neg hk)

variable (M) in
/-- The `k`-composite of the discretized algebra: `x` itself for `k ≥ m`. -/
noncomputable def dcomp (k : Fin n) {s : S} (x y : D n M s) (hxy : dsc M k x = dtg M k y) : D n M s :=
  ⟨if hk : k.val < m then comp (C := M.1 s) (⟨k.val, hk⟩ : Fin m) x.1 y.1
      ((dsc_lt hk x).symm.trans ((congrArg Subtype.val hxy).trans (dtg_lt hk y))) else x.1,
    EEq.holdsAll_empty⟩

lemma op_sc (k : Fin n) {s : S} (x : D n M s) :
    (D n M).op (.sc k s) (arityOne x) = Part.some (dsc M k x) := by
  refine (disc Sig n m).derived_op_eq_some EEq.holdsAll_empty ?_ _
  by_cases hk : k.val < m
  · have e : (disc Sig n m).op (.sc k s) =
        app₁ (.sc ⟨k.val, hk⟩ s) (.var ⟨⟨0, by simp⟩, rfl⟩) := dif_pos hk
    rw [e]
    exact (Compact.eval_sc rfl).trans (congrArg Part.some (dsc_lt hk x).symm)
  · have e : (disc Sig n m).op (.sc k s) = .var ⟨⟨0, by simp⟩, rfl⟩ := dif_neg hk
    rw [e]
    exact congrArg Part.some (congrArg Subtype.val (dsc_ge hk x)).symm

lemma op_tg (k : Fin n) {s : S} (x : D n M s) :
    (D n M).op (.tg k s) (arityOne x) = Part.some (dtg M k x) := by
  refine (disc Sig n m).derived_op_eq_some EEq.holdsAll_empty ?_ _
  by_cases hk : k.val < m
  · have e : (disc Sig n m).op (.tg k s) =
        app₁ (.tg ⟨k.val, hk⟩ s) (.var ⟨⟨0, by simp⟩, rfl⟩) := dif_pos hk
    rw [e]
    exact (Compact.eval_tg rfl).trans (congrArg Part.some (dtg_lt hk x).symm)
  · have e : (disc Sig n m).op (.tg k s) = .var ⟨⟨0, by simp⟩, rfl⟩ := dif_neg hk
    rw [e]
    exact congrArg Part.some (congrArg Subtype.val (dtg_ge hk x)).symm

variable (M) in
/-- The operations of `Σ` in the discretized algebra. -/
noncomputable def dop {ws : List S} {s : S} (σ : Sig ws s) (a : Arity (D n M) ws) : D n M s :=
  ⟨Compact.mop M σ fun j => (a j).1, EEq.holdsAll_empty⟩

lemma op_op {ws : List S} {s : S} (σ : Sig ws s) (a : Arity (D n M) ws) :
    (D n M).op (.op σ) a = Part.some (dop M σ a) :=
  (disc Sig n m).derived_op_eq_some EEq.holdsAll_empty (Compact.eval_op σ fun _ => rfl) _

lemma cond_lt {k : Fin n} (hk : k.val < m) {s : S} {x y : D n M s} :
    dsc M k x = dtg M k y ↔ Compact.msc M ⟨k.val, hk⟩ x.1 = Compact.mtg M ⟨k.val, hk⟩ y.1 :=
  ⟨fun h => (dsc_lt hk x).symm.trans ((congrArg Subtype.val h).trans (dtg_lt hk y)),
    fun h => Subtype.ext ((dsc_lt hk x).trans (h.trans (dtg_lt hk y).symm))⟩

lemma eq_of_cond_ge {k : Fin n} (hk : ¬ k.val < m) {s : S} {x y : D n M s}
    (h : dsc M k x = dtg M k y) : x = y := by
  rwa [dsc_ge hk, dtg_ge hk] at h

lemma dcomp_lt {k : Fin n} (hk : k.val < m) {s : S} (x y : D n M s) (h : dsc M k x = dtg M k y) :
    (dcomp M k x y h).1 = comp (C := M.1 s) (⟨k.val, hk⟩ : Fin m) x.1 y.1 ((cond_lt hk).mp h) :=
  dif_pos hk

lemma dcomp_ge {k : Fin n} (hk : ¬ k.val < m) {s : S} (x y : D n M s) (h : dsc M k x = dtg M k y) :
    dcomp M k x y h = x :=
  Subtype.ext (dif_neg hk)

lemma eval_sc_var (k : Fin n) {s : S} (x y : D n M s) :
    (app₁ (.sc k s) (.var ⟨⟨0, by simp⟩, rfl⟩) :
        Term (Compact.CompactSignature Sig (Fin n)) (Vars [s, s].get) s).eval
      (D n M) (famVal (arityTwo x y)) = Part.some (dsc M k x) :=
  (eval_app₁_arity _ rfl).trans (op_sc k x)

lemma eval_tg_var (k : Fin n) {s : S} (x y : D n M s) :
    (app₁ (.tg k s) (.var ⟨⟨1, by simp⟩, rfl⟩) :
        Term (Compact.CompactSignature Sig (Fin n)) (Vars [s, s].get) s).eval
      (D n M) (famVal (arityTwo x y)) = Part.some (dtg M k y) :=
  (eval_app₁_arity _ rfl).trans (op_tg k y)

lemma comp_defn_iff (k : Fin n) {s : S} (x y : D n M s) :
    EEq.HoldsAll (D n M) (famVal (arityTwo x y)) ((compactEpSig Sig (Fin n)).defn (.comp k s)) ↔
      dsc M k x = dtg M k y :=
  EEq.holdsAll_singleton.trans (EEq.holds_mk'_iff (eval_sc_var k x y) (eval_tg_var k x y))

lemma op_comp (k : Fin n) {s : S} (x y : D n M s) (hxy : dsc M k x = dtg M k y) :
    (D n M).op (.comp k s) (arityTwo x y) = Part.some (dcomp M k x y hxy) := by
  refine (disc Sig n m).derived_op_eq_some ((comp_defn_iff k x y).mpr hxy) ?_ _
  by_cases hk : k.val < m
  · have e : (disc Sig n m).op (.comp k s) = app₂ (.comp ⟨k.val, hk⟩ s)
        (.var ⟨⟨0, by simp⟩, rfl⟩) (.var ⟨⟨1, by simp⟩, rfl⟩) := dif_pos hk
    rw [e]
    exact (Compact.eval_comp rfl rfl ((cond_lt hk).mp hxy)).trans
      (congrArg Part.some (dcomp_lt hk x y hxy).symm)
  · have e : (disc Sig n m).op (.comp k s) = .var ⟨⟨0, by simp⟩, rfl⟩ := dif_neg hk
    rw [e]
    exact congrArg Part.some (congrArg Subtype.val (dcomp_ge hk x y hxy)).symm

lemma op_comp_dom (k : Fin n) {s : S} (x y : D n M s) :
    ((D n M).op (.comp k s) (arityTwo x y)).Dom ↔ dsc M k x = dtg M k y :=
  ⟨fun hd => (comp_defn_iff k x y).mp (((disc Sig n m).op_derived_dom_iff _ _).mp hd).1,
    fun hxy => (Part.eq_some_iff.mp (op_comp k x y hxy)).1⟩

theorem isAlgebra : (compactEpSig Sig (Fin n)).IsAlgebra (D n M) := by
  intro ws s σ a
  cases σ with
  | op σ => exact ⟨fun _ => EEq.holdsAll_empty, fun _ => (Part.eq_some_iff.mp (op_op σ a)).1⟩
  | sc k s =>
    have ha : arityOne (a ⟨0, by simp⟩) = a := by funext i; match i with | ⟨0, _⟩ => rfl
    exact ⟨fun _ => EEq.holdsAll_empty, fun _ => ha ▸ (Part.eq_some_iff.mp (op_sc k _)).1⟩
  | tg k s =>
    have ha : arityOne (a ⟨0, by simp⟩) = a := by funext i; match i with | ⟨0, _⟩ => rfl
    exact ⟨fun _ => EEq.holdsAll_empty, fun _ => ha ▸ (Part.eq_some_iff.mp (op_tg k _)).1⟩
  | comp k s =>
    have ha : arityTwo (a ⟨0, by simp⟩) (a ⟨1, by simp⟩) = a := by
      funext i; match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl
    exact ha ▸ (op_comp_dom k _ _).trans (comp_defn_iff k _ _).symm

/-! ### The laws of the discretized algebra -/

section Laws

variable {k : Fin n} {s : S}

lemma dsc_dsc (x : D n M s) : dsc M k (dsc M k x) = dsc M k x := by
  by_cases hk : k.val < m
  · apply Subtype.ext; rw [dsc_lt hk, dsc_lt hk]; exact Compact.model_sc_sc _
  · rw [dsc_ge hk, dsc_ge hk]

lemma dsc_dtg (x : D n M s) : dsc M k (dtg M k x) = dtg M k x := by
  by_cases hk : k.val < m
  · apply Subtype.ext; rw [dsc_lt hk, dtg_lt hk]; exact Compact.model_sc_tg _
  · rw [dsc_ge hk, dtg_ge hk]

lemma dtg_dsc (x : D n M s) : dtg M k (dsc M k x) = dsc M k x := by
  by_cases hk : k.val < m
  · apply Subtype.ext; rw [dtg_lt hk, dsc_lt hk]; exact Compact.model_tg_sc _
  · rw [dsc_ge hk, dtg_ge hk]

lemma dtg_dtg (x : D n M s) : dtg M k (dtg M k x) = dtg M k x := by
  by_cases hk : k.val < m
  · apply Subtype.ext; rw [dtg_lt hk, dtg_lt hk]; exact Compact.model_tg_tg _
  · rw [dtg_ge hk, dtg_ge hk]

lemma dsc_dcomp {x y : D n M s} (h : dsc M k x = dtg M k y) :
    dsc M k (dcomp M k x y h) = dsc M k y := by
  by_cases hk : k.val < m
  · apply Subtype.ext; rw [dsc_lt hk, dcomp_lt hk, dsc_lt hk]; exact Compact.model_sc_comp _
  · rw [dcomp_ge hk]; obtain rfl := eq_of_cond_ge hk h; rfl

lemma dtg_dcomp {x y : D n M s} (h : dsc M k x = dtg M k y) :
    dtg M k (dcomp M k x y h) = dtg M k x := by
  by_cases hk : k.val < m
  · apply Subtype.ext; rw [dtg_lt hk, dcomp_lt hk, dtg_lt hk]; exact Compact.model_tg_comp _
  · rw [dcomp_ge hk]

lemma dcomp_dsc (x : D n M s) : dcomp M k x (dsc M k x) (dtg_dsc x).symm = x := by
  by_cases hk : k.val < m
  · exact Subtype.ext ((dcomp_lt hk _ _ _).trans ((Compact.congr_comp₁ (dsc_lt hk x) rfl _).trans
      (Compact.model_comp_sc x.1)))
  · exact dcomp_ge hk _ _ _

lemma dcomp_dtg (x : D n M s) : dcomp M k (dtg M k x) x (dsc_dtg x) = x := by
  by_cases hk : k.val < m
  · exact Subtype.ext ((dcomp_lt hk _ _ _).trans ((Compact.congr_comp₁ rfl (dtg_lt hk x) _).trans
      (Compact.model_tg_comp_self x.1)))
  · exact (dcomp_ge hk _ _ _).trans (dtg_ge hk x)

lemma dcomp_assoc {a b c : D n M s} (hab : dsc M k a = dtg M k b) (hbc : dsc M k b = dtg M k c) :
    dcomp M k (dcomp M k a b hab) c ((dsc_dcomp hab).trans hbc) =
      dcomp M k a (dcomp M k b c hbc) (hab.trans (dtg_dcomp hbc).symm) := by
  by_cases hk : k.val < m
  · refine Subtype.ext ((dcomp_lt hk _ _ _).trans ?_)
    refine ((Compact.congr_comp₁ rfl (dcomp_lt hk a b hab) _).trans ?_).trans
      (dcomp_lt hk _ _ _).symm
    exact (Compact.model_assoc _ _).trans (Compact.congr_comp₁ (dcomp_lt hk b c hbc).symm rfl _)
  · simp only [dcomp_ge hk]

lemma dsc_dop {ws : List S} (σ : Sig ws s) (a : Arity (D n M) ws) :
    dsc M k (dop M σ a) = dop M σ (fun j => dsc M k (a j)) := by
  by_cases hk : k.val < m
  · apply Subtype.ext
    rw [dsc_lt hk]
    refine ((Compact.modelOp M σ).map_sc_eq_sc_map ⟨k.val, hk⟩ _).symm.trans ?_
    exact congrArg (Compact.mop M σ) (funext fun j => (dsc_lt hk (a j)).symm)
  · simp only [dsc_ge hk]

lemma dtg_dop {ws : List S} (σ : Sig ws s) (a : Arity (D n M) ws) :
    dtg M k (dop M σ a) = dop M σ (fun j => dtg M k (a j)) := by
  by_cases hk : k.val < m
  · apply Subtype.ext
    rw [dtg_lt hk]
    refine ((Compact.modelOp M σ).map_tg_eq_tg_map ⟨k.val, hk⟩ _).symm.trans ?_
    exact congrArg (Compact.mop M σ) (funext fun j => (dtg_lt hk (a j)).symm)
  · simp only [dtg_ge hk]

lemma dop_dcomp {ws : List S} (σ : Sig ws s) (a b : Arity (D n M) ws)
    (hab : ∀ j, dsc M k (a j) = dtg M k (b j)) :
    dop M σ (fun j => dcomp M k (a j) (b j) (hab j)) =
      dcomp M k (dop M σ a) (dop M σ b)
        ((dsc_dop σ a).trans ((congrArg (dop M σ) (funext hab)).trans (dtg_dop σ b).symm)) := by
  by_cases hk : k.val < m
  · refine Subtype.ext (Eq.trans ?_ (dcomp_lt hk _ _ _).symm)
    have h' : ∀ j, Compact.CategoryStruct.sc_is_tg (C := M.1 (ws.get j)) (⟨k.val, hk⟩ : Fin m)
        (a j).1 (b j).1 := fun j => (cond_lt hk).mp (hab j)
    refine (congrArg (Compact.mop M σ) (funext fun j => dcomp_lt hk (a j) (b j) (hab j))).trans ?_
    exact (Compact.modelOp M σ).map_comp_eq_comp_map (Compact.pi_sc_is_tg.mpr h')
  · have e : ∀ j, a j = b j := fun j => eq_of_cond_ge hk (hab j)
    simp only [dcomp_ge hk]

lemma dcomp_congr {x x' y y' : D n M s} (hx : x = x') (hy : y = y') (h : dsc M k x = dtg M k y)
    (h' : dsc M k x' = dtg M k y') : dcomp M k x y h = dcomp M k x' y' h' := by
  subst hx hy; rfl

end Laws

section Laws₂

variable {l k : Fin n} (hlk : l < k) {s : S}

include hlk

lemma lt_of_lt {hk : k.val < m} : l.val < m := lt_trans (Fin.lt_def.mp hlk) hk

lemma low_lt (hk : k.val < m) : (⟨l.val, lt_of_lt hlk (hk := hk)⟩ : Fin m) < ⟨k.val, hk⟩ :=
  Fin.lt_def.mpr (Fin.lt_def.mp hlk)

lemma dsc_k_dsc_l (x : D n M s) : dsc M k (dsc M l x) = dsc M l x := by
  by_cases hk : k.val < m
  · have hl := lt_of_lt hlk (hk := hk)
    apply Subtype.ext; rw [dsc_lt hk, dsc_lt hl]; exact Compact.model_sc_k_sc_l _ (low_lt hlk hk)
  · rw [dsc_ge hk]

lemma dtg_k_dtg_l (x : D n M s) : dtg M k (dtg M l x) = dtg M l x := by
  by_cases hk : k.val < m
  · have hl := lt_of_lt hlk (hk := hk)
    apply Subtype.ext; rw [dtg_lt hk, dtg_lt hl]; exact Compact.model_tg_k_tg_l _ (low_lt hlk hk)
  · rw [dtg_ge hk]

lemma dsc_l_dsc_k (x : D n M s) : dsc M l (dsc M k x) = dsc M l x := by
  by_cases hk : k.val < m
  · have hl := lt_of_lt hlk (hk := hk)
    apply Subtype.ext; rw [dsc_lt hl, dsc_lt hk, dsc_lt hl]
    exact Compact.model_sc_l_sc_k _ (low_lt hlk hk)
  · rw [dsc_ge hk]

lemma dtg_l_dtg_k (x : D n M s) : dtg M l (dtg M k x) = dtg M l x := by
  by_cases hk : k.val < m
  · have hl := lt_of_lt hlk (hk := hk)
    apply Subtype.ext; rw [dtg_lt hl, dtg_lt hk, dtg_lt hl]
    exact Compact.model_tg_l_tg_k _ (low_lt hlk hk)
  · rw [dtg_ge hk]

lemma dsc_l_dtg_k (x : D n M s) : dsc M l (dtg M k x) = dsc M l x := by
  by_cases hk : k.val < m
  · have hl := lt_of_lt hlk (hk := hk)
    apply Subtype.ext; rw [dsc_lt hl, dtg_lt hk, dsc_lt hl]
    exact Compact.model_sc_l_tg_k _ (low_lt hlk hk)
  · rw [dtg_ge hk]

lemma dtg_l_dsc_k (x : D n M s) : dtg M l (dsc M k x) = dtg M l x := by
  by_cases hk : k.val < m
  · have hl := lt_of_lt hlk (hk := hk)
    apply Subtype.ext; rw [dtg_lt hl, dsc_lt hk, dtg_lt hl]
    exact Compact.model_tg_l_sc_k _ (low_lt hlk hk)
  · rw [dsc_ge hk]

lemma dsc_k_dcomp_l {x y : D n M s} (h : dsc M l x = dtg M l y) :
    dsc M k (dcomp M l x y h) = dcomp M l (dsc M k x) (dsc M k y)
      ((dsc_l_dsc_k hlk x).trans (h.trans (dtg_l_dsc_k hlk y).symm)) := by
  by_cases hk : k.val < m
  · have hl := lt_of_lt hlk (hk := hk)
    refine Subtype.ext ((dsc_lt hk _).trans (Eq.trans ?_ (dcomp_lt hl _ _ _).symm))
    rw [dcomp_lt hl]
    refine (Compact.model_sc_comp_l (low_lt hlk hk) _ ?_).trans ?_
    · exact Compact.CategoryStruct.dom_of_sc_is_tg
        (Compact.Category.sc_tg_j_sc (low_lt hlk hk) ((cond_lt hl).mp h))
    · exact Part.get_eq_get_of_eq _ _ (congrArg₂ _ (dsc_lt hk x).symm (dsc_lt hk y).symm)
  · simp only [dsc_ge hk]

lemma dtg_k_dcomp_l {x y : D n M s} (h : dsc M l x = dtg M l y) :
    dtg M k (dcomp M l x y h) = dcomp M l (dtg M k x) (dtg M k y)
      ((dsc_l_dtg_k hlk x).trans (h.trans (dtg_l_dtg_k hlk y).symm)) := by
  by_cases hk : k.val < m
  · have hl := lt_of_lt hlk (hk := hk)
    refine Subtype.ext ((dtg_lt hk _).trans (Eq.trans ?_ (dcomp_lt hl _ _ _).symm))
    rw [dcomp_lt hl]
    refine (Compact.model_tg_comp_l (low_lt hlk hk) _ ?_).trans ?_
    · exact Compact.CategoryStruct.dom_of_sc_is_tg
        (Compact.Category.sc_tg_j_tg (low_lt hlk hk) ((cond_lt hl).mp h))
    · exact Part.get_eq_get_of_eq _ _ (congrArg₂ _ (dtg_lt hk x).symm (dtg_lt hk y).symm)
  · simp only [dtg_ge hk]

lemma dsc_l_dcomp_k {x y : D n M s} (h : dsc M k x = dtg M k y) :
    dsc M l (dcomp M k x y h) = dsc M l x :=
  (dsc_l_dtg_k hlk _).symm.trans ((congrArg _ (dtg_dcomp h)).trans (dsc_l_dtg_k hlk x))

lemma dtg_l_dcomp_k {x y : D n M s} (h : dsc M k x = dtg M k y) :
    dtg M l (dcomp M k x y h) = dtg M l x :=
  (dtg_l_dtg_k hlk _).symm.trans ((congrArg _ (dtg_dcomp h)).trans (dtg_l_dtg_k hlk x))

lemma dinterchange {x y z t : D n M s} (hxy : dsc M l x = dtg M l y) (hzt : dsc M l z = dtg M l t)
    (hxz : dsc M k x = dtg M k z) (hyt : dsc M k y = dtg M k t) :
    dcomp M k (dcomp M l x y hxy) (dcomp M l z t hzt)
        ((dsc_k_dcomp_l hlk hxy).trans ((dcomp_congr hxz hyt _ _).trans
          (dtg_k_dcomp_l hlk hzt).symm)) =
      dcomp M l (dcomp M k x z hxz) (dcomp M k y t hyt)
        ((dsc_l_dcomp_k hlk hxz).trans (hxy.trans (dtg_l_dcomp_k hlk hyt).symm)) := by
  by_cases hk : k.val < m
  · have hl := lt_of_lt hlk (hk := hk)
    refine Subtype.ext ((dcomp_lt hk _ _ _).trans (Eq.trans ?_ (dcomp_lt hl _ _ _).symm))
    refine (Compact.congr_comp₁ (dcomp_lt hl z t hzt) (dcomp_lt hl x y hxy) _).trans ?_
    refine (Compact.Category.interchange (low_lt hlk hk) ((cond_lt hk).mp hxz)
      ((cond_lt hk).mp hyt) ((cond_lt hl).mp hxy) ((cond_lt hl).mp hzt)).trans ?_
    exact Compact.congr_comp₁ (dcomp_lt hk y t hyt).symm (dcomp_lt hk x z hxz).symm _
  · obtain rfl := eq_of_cond_ge hk hxz
    obtain rfl := eq_of_cond_ge hk hyt
    simp only [dcomp_ge hk]

end Laws₂

section Eval

variable {val : ∀ s, Compact.Var S s → Part ((D n M) s)}

lemma ev_scT (k : Fin n) {s : S} {t : Compact.CTerm Sig (Fin n) s} {x : D n M s}
    (ht : t.eval (D n M) val = Part.some x) :
    (Compact.CTerm.scT k t).eval (D n M) val = Part.some (dsc M k x) :=
  (eval_app₁_arity _ ht).trans (op_sc k x)

lemma ev_tgT (k : Fin n) {s : S} {t : Compact.CTerm Sig (Fin n) s} {x : D n M s}
    (ht : t.eval (D n M) val = Part.some x) :
    (Compact.CTerm.tgT k t).eval (D n M) val = Part.some (dtg M k x) :=
  (eval_app₁_arity _ ht).trans (op_tg k x)

lemma ev_compT (k : Fin n) {s : S} {t t' : Compact.CTerm Sig (Fin n) s} {x y : D n M s}
    (ht : t.eval (D n M) val = Part.some x) (ht' : t'.eval (D n M) val = Part.some y)
    (hxy : dsc M k x = dtg M k y) :
    (Compact.CTerm.compT k t t').eval (D n M) val = Part.some (dcomp M k x y hxy) :=
  (eval_app₂_arity _ ht ht').trans (op_comp k x y hxy)

lemma ev_compT_dom (k : Fin n) {s : S} {t t' : Compact.CTerm Sig (Fin n) s} {x y : D n M s}
    (ht : t.eval (D n M) val = Part.some x) (ht' : t'.eval (D n M) val = Part.some y)
    (hd : ((Compact.CTerm.compT k t t').eval (D n M) val).Dom) : dsc M k x = dtg M k y :=
  (op_comp_dom k x y).mp ((eval_app₂_arity _ ht ht') ▸ hd)

lemma ev_opT {ws : List S} {s : S} (σ : Sig ws s)
    {ts : (j : Fin ws.length) → Compact.CTerm Sig (Fin n) (ws.get j)} {a : Arity (D n M) ws}
    (h : ∀ j, (ts j).eval (D n M) val = Part.some (a j)) :
    (Compact.CTerm.opT σ ts).eval (D n M) val = Part.some (dop M σ a) :=
  (eval_app_of_eq_some _ _ _ h).trans (op_op σ a)

end Eval

/-- The variables of an axiom. -/
local macro "vm" : tactic => `(tactic| (
  simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, Compact.CTerm.scT, Compact.CTerm.tgT,
    Compact.CTerm.compT, Compact.CTerm.opT, Compact.CTerm.x]))

/-- A premise of an axiom. -/
local macro "pm" : tactic => `(tactic| (
  first
    | exact List.Mem.head _
    | exact List.Mem.tail _ (List.Mem.head _)
    | exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    | exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

open Compact.CTerm in
theorem holds : ∀ q ∈ Compact.compactSpec Sig (Fin n), q.Holds (D n M) := by
  intro q hq val hvars hprem
  have var : ∀ {s : S} (i : ℕ), (⟨s, i⟩ : Σ t, Compact.Var S t) ∈ q.vars →
      ∃ x, (Compact.CTerm.x (Sig := Sig) (Index := Fin n) (s := s) i).eval (D n M) val =
        Part.some x :=
    fun i hi => ⟨_, (Part.some_get (hvars _ hi)).symm⟩
  have prem : ∀ e ∈ q.premises, e.Holds (D n M) val := hprem
  cases hq with
  | @A0 ws s σ xs =>
    choose a ha using fun j => var (s := ws.get j) (xs j) (by vm; try exact ⟨j, rfl, rfl⟩)
    exact EEq.holds_defined_iff.mpr (Part.eq_some_iff.mp (ev_opT σ ha)).1
  | A1_sc k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact EEq.holds_defined_iff.mpr (Part.eq_some_iff.mp (ev_scT k ha)).1
  | A1_tg k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact EEq.holds_defined_iff.mpr (Part.eq_some_iff.mp (ev_tgT k ha)).1
  | A2_sc_sc k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_scT k (ev_scT k ha)) (ev_scT k ha)).mpr (dsc_dsc a)
  | A2_sc_tg k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_scT k (ev_tgT k ha)) (ev_tgT k ha)).mpr (dsc_dtg a)
  | A2_tg_sc k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_tgT k (ev_scT k ha)) (ev_scT k ha)).mpr (dtg_dsc a)
  | A2_tg_tg k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_tgT k (ev_tgT k ha)) (ev_tgT k ha)).mpr (dtg_dtg a)
  | A3_dom k s i j =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    obtain ⟨b, hb⟩ := var (s := s) j (by vm)
    exact (EEq.holds_mk'_iff (ev_scT k ha) (ev_tgT k hb)).mpr
      (ev_compT_dom k ha hb (EEq.holds_defined_iff.mp (prem _ (by pm))))
  | A3_def k s i j =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    obtain ⟨b, hb⟩ := var (s := s) j (by vm)
    have hab := (EEq.holds_mk'_iff (ev_scT k ha) (ev_tgT k hb)).mp (prem _ (by pm))
    exact EEq.holds_defined_iff.mpr (Part.eq_some_iff.mp (ev_compT k ha hb hab)).1
  | A4_sc k s i j =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    obtain ⟨b, hb⟩ := var (s := s) j (by vm)
    have hab := ev_compT_dom k ha hb (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_scT k (ev_compT k ha hb hab)) (ev_scT k hb)).mpr (dsc_dcomp hab)
  | A4_tg k s i j =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    obtain ⟨b, hb⟩ := var (s := s) j (by vm)
    have hab := ev_compT_dom k ha hb (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_tgT k (ev_compT k ha hb hab)) (ev_tgT k ha)).mpr (dtg_dcomp hab)
  | A5_sc k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_compT k ha (ev_scT k ha) (dtg_dsc a).symm) ha).mpr (dcomp_dsc a)
  | A5_tg k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_compT k (ev_tgT k ha) ha (dsc_dtg a)) ha).mpr (dcomp_dtg a)
  | A6 k s i j l =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    obtain ⟨b, hb⟩ := var (s := s) j (by vm)
    obtain ⟨c, hc⟩ := var (s := s) l (by vm)
    have hab := ev_compT_dom k ha hb (EEq.holds_defined_iff.mp (prem _ (by pm)))
    have hbc := ev_compT_dom k hb hc (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_compT k (ev_compT k ha hb hab) hc ((dsc_dcomp hab).trans hbc))
      (ev_compT k ha (ev_compT k hb hc hbc) (hab.trans (dtg_dcomp hbc).symm))).mpr
      (dcomp_assoc hab hbc)
  | @A7_sc k ws s σ xs =>
    choose a ha using fun j => var (s := ws.get j) (xs j) (by vm; try exact ⟨j, rfl, rfl⟩)
    exact (EEq.holds_mk'_iff (ev_scT k (ev_opT σ ha)) (ev_opT σ fun j => ev_scT k (ha j))).mpr
      (dsc_dop σ a)
  | @A7_tg k ws s σ xs =>
    choose a ha using fun j => var (s := ws.get j) (xs j) (by vm; try exact ⟨j, rfl, rfl⟩)
    exact (EEq.holds_mk'_iff (ev_tgT k (ev_opT σ ha)) (ev_opT σ fun j => ev_tgT k (ha j))).mpr
      (dtg_dop σ a)
  | @A8 k ws s σ xs ys =>
    choose a ha using fun j => var (s := ws.get j) (xs j)
      (by vm; exact Or.inl (Or.inr (Or.inl ⟨j, rfl, rfl⟩)))
    choose b hb using fun j => var (s := ws.get j) (ys j)
      (by vm; exact Or.inl (Or.inr (Or.inr ⟨j, rfl, rfl⟩)))
    have hab : ∀ j, dsc M k (a j) = dtg M k (b j) := fun j =>
      ev_compT_dom k (ha j) (hb j) (EEq.holds_defined_iff.mp (prem _ (List.mem_ofFn.mpr ⟨j, rfl⟩)))
    exact (EEq.holds_mk'_iff (ev_opT σ fun j => ev_compT k (ha j) (hb j) (hab j))
      (ev_compT k (ev_opT σ ha) (ev_opT σ hb)
        ((dsc_dop σ a).trans ((congrArg (dop M σ) (funext hab)).trans (dtg_dop σ b).symm)))).mpr
      (dop_dcomp σ a b hab)
  | AB1_sc_sc l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_scT k (ev_scT l ha)) (ev_scT l ha)).mpr (dsc_k_dsc_l h a)
  | AB1_tg_tg l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_tgT k (ev_tgT l ha)) (ev_tgT l ha)).mpr (dtg_k_dtg_l h a)
  | AB1_sc_sck l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_scT l (ev_scT k ha)) (ev_scT l ha)).mpr (dsc_l_dsc_k h a)
  | AB1_tg_tgk l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_tgT l (ev_tgT k ha)) (ev_tgT l ha)).mpr (dtg_l_dtg_k h a)
  | AB1_sc_tgk l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_scT l (ev_tgT k ha)) (ev_scT l ha)).mpr (dsc_l_dtg_k h a)
  | AB1_tg_sck l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_tgT l (ev_scT k ha)) (ev_tgT l ha)).mpr (dtg_l_dsc_k h a)
  | AB2_sc l k h s i j =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    obtain ⟨b, hb⟩ := var (s := s) j (by vm)
    have hab := ev_compT_dom l ha hb (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_scT k (ev_compT l ha hb hab))
      (ev_compT l (ev_scT k ha) (ev_scT k hb) _)).mpr (dsc_k_dcomp_l h hab)
  | AB2_tg l k h s i j =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    obtain ⟨b, hb⟩ := var (s := s) j (by vm)
    have hab := ev_compT_dom l ha hb (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_tgT k (ev_compT l ha hb hab))
      (ev_compT l (ev_tgT k ha) (ev_tgT k hb) _)).mpr (dtg_k_dcomp_l h hab)
  | AB3 l k h s i j p q =>
    obtain ⟨x, hx⟩ := var (s := s) i (by vm)
    obtain ⟨y, hy⟩ := var (s := s) j (by vm)
    obtain ⟨z, hz⟩ := var (s := s) p (by vm)
    obtain ⟨t, ht⟩ := var (s := s) q (by vm)
    have hxy := ev_compT_dom l hx hy (EEq.holds_defined_iff.mp (prem _ (by pm)))
    have hzt := ev_compT_dom l hz ht (EEq.holds_defined_iff.mp (prem _ (by pm)))
    have hxz := ev_compT_dom k hx hz (EEq.holds_defined_iff.mp (prem _ (by pm)))
    have hyt := ev_compT_dom k hy ht (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_compT k (ev_compT l hx hy hxy) (ev_compT l hz ht hzt) _)
      (ev_compT l (ev_compT k hx hz hxz) (ev_compT k hy ht hyt) _)).mpr
      (dinterchange h hxy hzt hxz hyt)

end Disc
```

:::proposition (label := "discretization-models") (central := true) (title := "Compact discretization sends models to models")
$`(\boldsymbol{\delta}^{(n,m)})^{\ast}_{\mathfrak{gd}}` sends the models of
$`(\mathbf{\Sigma}^{(m)}, \mathcal{C}^{\Sigma^{(m)}})` to models of
$`(\mathbf{\Sigma}^{(n)}, \mathcal{C}^{\Sigma^{(n)}})`. Moreover, if $`m < n`, every cell of the
discretized algebra is an $`m`-cell.

```lean
theorem disc_sendsModels :
    (disc Sig n m).SendsModels.{u, max u v, u, max u v, w}
      (Compact.compactSpec Sig (Fin n)) (Compact.compactSpec Sig (Fin m)) :=
  fun B hB => ⟨Disc.isAlgebra (M := ⟨B, hB.2⟩), Disc.holds (M := ⟨B, hB.2⟩)⟩

theorem disc_isCell (hm : m < n) {M : Compact.CompactPAlg.{u, v, w} Sig (Fin m)} {s : S}
    (x : Disc.D n M s) :
    Compact.msc (⟨Disc.D n M, Disc.holds⟩ : Compact.CompactPAlg.{u, v, w} Sig (Fin n)) ⟨m, hm⟩ x =
      x :=
  (Part.get_eq_of_mem (Part.eq_some_iff.mp (Disc.op_sc _ x)) _).trans
    (Disc.dsc_ge (lt_irrefl m) x)
```
:::

:::proof (of := "discretization-models")
In the discretized algebra the operations of $`\Sigma`, the sources and the targets are total, and
two cells satisfy the domain condition of $`\circ^{k}_{s}` if and only if
$`\mathrm{sc}^{k}_{s}(x) = \mathrm{tg}^{k}_{s}(y)`, for $`k < m`, in which case $`x \circ^{k}_{s} y` is
defined by (A$`^{k}`3), and if and only if $`x = y`, for $`k \geq m`. Under this description, the
axioms in which all the dimensions are smaller than $`m` are axioms of $`\mathcal{C}^{\Sigma^{(m)}}`;
for $`k \geq m`, (A$`^{k}`1)–(A$`^{k}`8) become trivial; for $`l < m \leq k`, (AB$`^{l,k}`1) and
(AB$`^{l,k}`2) become trivial and the premises $`x = z`, $`y = t` of (AB$`^{l,k}`3) make it trivial;
and for $`m \leq l < k` every premise is an equality of variables. Every cell $`x` is an
$`m`-cell, since $`\mathrm{sc}^{m}_{s}(x) = x`.
:::

:::definition (label := "discretization-functor") (central := false) (title := "The compact discretization functor")
The *discretization functor* $`\mathrm{D}^{(n,m)}` is the birestriction of
$`(\boldsymbol{\delta}^{(n,m)})^{\ast}_{\mathfrak{gd}}` to the categories of models.

```lean
/-- The discretization functor `D⁽ⁿ'ᵐ⁾`. -/
noncomputable def discFunctor :
    EpSpec.EpAlg.{u, max u v, w} (compactEpSpec Sig (Fin m)) ⥤
      EpSpec.EpAlg.{u, max u v, w} (compactEpSpec Sig (Fin n)) :=
  (disc Sig n m).restrict (disc_sendsModels Sig n m)
```
:::

# Compact truncation

:::definition (label := "truncation-derivor") (central := false) (title := "The compact truncation derivor")
Let $`m \leq n`. The *compact truncation derivor* $`\boldsymbol{\tau}^{(m,n)} = (\mathrm{id}_S, D, d)` is
the generalized ep-derivor from $`\mathbf{\Sigma}^{(m)}` to $`\mathbf{\Sigma}^{(n)}` in which $`d` sends
every operation symbol to itself, applied to variables, and
$`D_s = \{\mathrm{sc}^{m}_{s}(v) \overset{\mathrm{e}}{=} v\}` if $`m < n`, $`D_s = \varnothing` if $`m = n`.

```lean
section CompactTrunc

variable {n m} (hmn : m ≤ n)

/-- The domains of the compact truncation derivor. -/
def truncDom (m n : ℕ) (s : S) :
    Set (EEq (Compact.CompactSignature Sig (Fin n)) (Vars fun _ : Unit => s)) :=
  if hm : m < n then {EEq.mk' (app₁ (.sc ⟨m, hm⟩ s) (.var ⟨(), rfl⟩)) (.var ⟨(), rfl⟩)} else ∅

/-- The terms of the compact truncation derivor: every symbol is sent to itself. -/
def truncOp : ∀ {ws : List S} {s : S}, Compact.CompactSignature Sig (Fin m) ws s →
    Term (Compact.CompactSignature Sig (Fin n)) (Vars (id ∘ ws.get)) s
  | _, _, .op σ => .app (.op σ) fun j => .var (Vars.mk j)
  | _, _, .sc k s => app₁ (.sc (Fin.castLE hmn k) s) (.var ⟨⟨0, by simp⟩, rfl⟩)
  | _, _, .tg k s => app₁ (.tg (Fin.castLE hmn k) s) (.var ⟨⟨0, by simp⟩, rfl⟩)
  | _, _, .comp k s =>
      app₂ (.comp (Fin.castLE hmn k) s) (.var ⟨⟨0, by simp⟩, rfl⟩) (.var ⟨⟨1, by simp⟩, rfl⟩)

/-- The compact truncation derivor `𝛕^{(m,n)}`. -/
def trunc : GenEpDerivor (compactEpSig Sig (Fin m)) (compactEpSig Sig (Fin n)) where
  sortMap := id
  sortDom := truncDom Sig m n
  op := truncOp Sig hmn

end CompactTrunc
```
:::

The truncated algebra $`(\boldsymbol{\tau}^{(m,n)})^{\ast}_{\mathfrak{gd}}(\mathbf{B})` of a model
$`\mathbf{B}` is the relative subalgebra of $`\mathbf{B}` on its $`m`-cells.

```lean
section CompactTrunc

variable {n m} (hmn : m ≤ n)

namespace Trunc

open Compact.CategoryStruct

variable {Sig hmn}

/-- The truncated algebra. -/
noncomputable abbrev T (hmn : m ≤ n) (M : Compact.CompactPAlg.{u, v, w} Sig (Fin n)) :=
  (trunc Sig hmn).derived M.1

variable {M : Compact.CompactPAlg.{u, v, w} Sig (Fin n)}

lemma dom_iff (hm : m < n) {s : S} (b : M.1 s) :
    EEq.HoldsAll M.1 (val₁ b) (truncDom Sig m n s) ↔ Compact.msc M ⟨m, hm⟩ b = b := by
  simp only [truncDom, dif_pos hm]
  exact EEq.holdsAll_singleton.trans (EEq.holds_mk'_iff (Compact.eval_sc rfl) rfl)

lemma dom_top (hm : ¬ m < n) {s : S} (b : M.1 s) : EEq.HoldsAll M.1 (val₁ b) (truncDom Sig m n s) := by
  simp only [truncDom, dif_neg hm]; exact EEq.holdsAll_empty

/-- The cell condition: membership in the domain of a sort. -/
lemma mem_of {s : S} (b : M.1 s) (h : ∀ hm : m < n, Compact.msc M ⟨m, hm⟩ b = b) :
    EEq.HoldsAll M.1 (val₁ b) (truncDom Sig m n s) := by
  by_cases hm : m < n
  · exact (dom_iff hm b).mpr (h hm)
  · exact dom_top hm b

lemma isCell {s : S} (x : T hmn M s) (hm : m < n) : Compact.msc M ⟨m, hm⟩ x.1 = x.1 :=
  (dom_iff hm x.1).mp x.2

omit hmn in
lemma castLE_lt (hmn : m ≤ n) (k : Fin m) (hm : m < n) : Fin.castLE hmn k < (⟨m, hm⟩ : Fin n) :=
  Fin.lt_def.mpr k.isLt

variable (hmn M) in
noncomputable def tsc (k : Fin m) {s : S} (x : T hmn M s) : T hmn M s :=
  ⟨Compact.msc M (Fin.castLE hmn k) x.1, mem_of _ fun hm =>
    Compact.model_sc_k_sc_l _ (castLE_lt hmn k hm)⟩

variable (hmn M) in
noncomputable def ttg (k : Fin m) {s : S} (x : T hmn M s) : T hmn M s :=
  ⟨Compact.mtg M (Fin.castLE hmn k) x.1, mem_of _ fun hm => by
    calc Compact.msc M ⟨m, hm⟩ (Compact.mtg M (Fin.castLE hmn k) x.1)
        = Compact.msc M ⟨m, hm⟩ (Compact.msc M (Fin.castLE hmn k)
            (Compact.mtg M (Fin.castLE hmn k) x.1)) :=
          congrArg _ (Compact.model_sc_tg _).symm
      _ = Compact.msc M (Fin.castLE hmn k) (Compact.mtg M (Fin.castLE hmn k) x.1) :=
          Compact.model_sc_k_sc_l _ (castLE_lt hmn k hm)
      _ = _ := Compact.model_sc_tg _⟩

variable (hmn M) in
noncomputable def tcomp (k : Fin m) {s : S} (x y : T hmn M s)
    (hxy : sc_is_tg (Fin.castLE hmn k) x.1 y.1) : T hmn M s :=
  ⟨comp (Fin.castLE hmn k) x.1 y.1 hxy, mem_of _ fun hm => by
    have hd : (pcomp (Fin.castLE hmn k) (Compact.msc M ⟨m, hm⟩ x.1)
        (Compact.msc M ⟨m, hm⟩ y.1)).Dom :=
      dom_of_sc_is_tg (Compact.Category.sc_tg_j_sc (castLE_lt hmn k hm) hxy)
    refine (Compact.model_sc_comp_l (castLE_lt hmn k hm) hxy hd).trans ?_
    exact Part.get_eq_get_of_eq _ _ (congrArg₂ (pcomp _) (isCell x hm) (isCell y hm))⟩

variable (hmn M) in
noncomputable def top {ws : List S} {s : S} (σ : Sig ws s) (a : Arity (T hmn M) ws) : T hmn M s :=
  ⟨Compact.mop M σ fun j => (a j).1, mem_of _ fun hm =>
    ((Compact.modelOp M σ).map_sc_eq_sc_map ⟨m, hm⟩ _).symm.trans
      (congrArg (Compact.mop M σ) (funext fun j => isCell (a j) hm))⟩

lemma op_sc (k : Fin m) {s : S} (x : T hmn M s) :
    (T hmn M).op (.sc k s) (arityOne x) = Part.some (tsc hmn M k x) :=
  (trunc Sig hmn).derived_op_eq_some EEq.holdsAll_empty (Compact.eval_sc rfl) _

lemma op_tg (k : Fin m) {s : S} (x : T hmn M s) :
    (T hmn M).op (.tg k s) (arityOne x) = Part.some (ttg hmn M k x) :=
  (trunc Sig hmn).derived_op_eq_some EEq.holdsAll_empty (Compact.eval_tg rfl) _

lemma op_op {ws : List S} {s : S} (σ : Sig ws s) (a : Arity (T hmn M) ws) :
    (T hmn M).op (.op σ) a = Part.some (top hmn M σ a) :=
  (trunc Sig hmn).derived_op_eq_some EEq.holdsAll_empty (Compact.eval_op σ fun _ => rfl) _

lemma comp_defn_iff (k : Fin m) {s : S} (x y : T hmn M s) :
    EEq.HoldsAll (T hmn M) (famVal (arityTwo x y)) ((compactEpSig Sig (Fin m)).defn (.comp k s)) ↔
      sc_is_tg (Fin.castLE hmn k) x.1 y.1 := by
  refine EEq.holdsAll_singleton.trans ?_
  refine (EEq.holds_mk'_iff ((eval_app₁_arity _ rfl).trans (op_sc k x))
    ((eval_app₁_arity _ rfl).trans (op_tg k y))).trans ?_
  exact ⟨fun e => congrArg Subtype.val e, fun e => Subtype.ext e⟩

lemma op_comp (k : Fin m) {s : S} (x y : T hmn M s) (hxy : sc_is_tg (Fin.castLE hmn k) x.1 y.1) :
    (T hmn M).op (.comp k s) (arityTwo x y) = Part.some (tcomp hmn M k x y hxy) :=
  (trunc Sig hmn).derived_op_eq_some ((comp_defn_iff k x y).mpr hxy)
    (Compact.eval_comp rfl rfl hxy) _

lemma op_comp_dom (k : Fin m) {s : S} (x y : T hmn M s) :
    ((T hmn M).op (.comp k s) (arityTwo x y)).Dom ↔ sc_is_tg (Fin.castLE hmn k) x.1 y.1 :=
  ⟨fun hd => (comp_defn_iff k x y).mp (((trunc Sig hmn).op_derived_dom_iff _ _).mp hd).1,
    fun hxy => (Part.eq_some_iff.mp (op_comp k x y hxy)).1⟩

theorem isAlgebra : (compactEpSig Sig (Fin m)).IsAlgebra (T hmn M) := by
  intro ws s σ a
  cases σ with
  | op σ => exact ⟨fun _ => EEq.holdsAll_empty, fun _ => (Part.eq_some_iff.mp (op_op σ a)).1⟩
  | sc k s =>
    have ha : arityOne (a ⟨0, by simp⟩) = a := by funext i; match i with | ⟨0, _⟩ => rfl
    exact ⟨fun _ => EEq.holdsAll_empty, fun _ => ha ▸ (Part.eq_some_iff.mp (op_sc k _)).1⟩
  | tg k s =>
    have ha : arityOne (a ⟨0, by simp⟩) = a := by funext i; match i with | ⟨0, _⟩ => rfl
    exact ⟨fun _ => EEq.holdsAll_empty, fun _ => ha ▸ (Part.eq_some_iff.mp (op_tg k _)).1⟩
  | comp k s =>
    have ha : arityTwo (a ⟨0, by simp⟩) (a ⟨1, by simp⟩) = a := by
      funext i; match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl
    exact ha ▸ (op_comp_dom k _ _).trans (comp_defn_iff k _ _).symm

section Eval

variable {val : ∀ s, Compact.Var S s → Part ((T hmn M) s)}

lemma ev_scT (k : Fin m) {s : S} {t : Compact.CTerm Sig (Fin m) s} {x : T hmn M s}
    (ht : t.eval (T hmn M) val = Part.some x) :
    (Compact.CTerm.scT k t).eval (T hmn M) val = Part.some (tsc hmn M k x) :=
  (eval_app₁_arity _ ht).trans (op_sc k x)

lemma ev_tgT (k : Fin m) {s : S} {t : Compact.CTerm Sig (Fin m) s} {x : T hmn M s}
    (ht : t.eval (T hmn M) val = Part.some x) :
    (Compact.CTerm.tgT k t).eval (T hmn M) val = Part.some (ttg hmn M k x) :=
  (eval_app₁_arity _ ht).trans (op_tg k x)

lemma ev_compT (k : Fin m) {s : S} {t t' : Compact.CTerm Sig (Fin m) s} {x y : T hmn M s}
    (ht : t.eval (T hmn M) val = Part.some x) (ht' : t'.eval (T hmn M) val = Part.some y)
    (hxy : sc_is_tg (Fin.castLE hmn k) x.1 y.1) :
    (Compact.CTerm.compT k t t').eval (T hmn M) val = Part.some (tcomp hmn M k x y hxy) :=
  (eval_app₂_arity _ ht ht').trans (op_comp k x y hxy)

lemma ev_compT_dom (k : Fin m) {s : S} {t t' : Compact.CTerm Sig (Fin m) s} {x y : T hmn M s}
    (ht : t.eval (T hmn M) val = Part.some x) (ht' : t'.eval (T hmn M) val = Part.some y)
    (hd : ((Compact.CTerm.compT k t t').eval (T hmn M) val).Dom) :
    sc_is_tg (Fin.castLE hmn k) x.1 y.1 :=
  (op_comp_dom k x y).mp ((eval_app₂_arity _ ht ht') ▸ hd)

lemma ev_opT {ws : List S} {s : S} (σ : Sig ws s)
    {ts : (j : Fin ws.length) → Compact.CTerm Sig (Fin m) (ws.get j)} {a : Arity (T hmn M) ws}
    (h : ∀ j, (ts j).eval (T hmn M) val = Part.some (a j)) :
    (Compact.CTerm.opT σ ts).eval (T hmn M) val = Part.some (top hmn M σ a) :=
  (eval_app_of_eq_some _ _ _ h).trans (op_op σ a)

end Eval

/-- The variables of an axiom. -/
local macro "vm" : tactic => `(tactic| (
  simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, Compact.CTerm.scT, Compact.CTerm.tgT,
    Compact.CTerm.compT, Compact.CTerm.opT, Compact.CTerm.x]))

/-- A premise of an axiom. -/
local macro "pm" : tactic => `(tactic| (
  first
    | exact List.Mem.head _
    | exact List.Mem.tail _ (List.Mem.head _)
    | exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    | exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

open Compact.CTerm in
theorem holds : ∀ q ∈ Compact.compactSpec Sig (Fin m), q.Holds (T hmn M) := by
  intro q hq val hvars hprem
  have var : ∀ {s : S} (i : ℕ), (⟨s, i⟩ : Σ t, Compact.Var S t) ∈ q.vars →
      ∃ x, (Compact.CTerm.x (Sig := Sig) (Index := Fin m) (s := s) i).eval (T hmn M) val =
        Part.some x :=
    fun i hi => ⟨_, (Part.some_get (hvars _ hi)).symm⟩
  have prem : ∀ e ∈ q.premises, e.Holds (T hmn M) val := hprem
  have ll : ∀ {l k : Fin m}, l < k → Fin.castLE hmn l < Fin.castLE hmn k :=
    fun h => Fin.lt_def.mpr (Fin.lt_def.mp h)
  cases hq with
  | @A0 ws s σ xs =>
    choose a ha using fun j => var (s := ws.get j) (xs j) (by vm; try exact ⟨j, rfl, rfl⟩)
    exact EEq.holds_defined_iff.mpr (Part.eq_some_iff.mp (ev_opT σ ha)).1
  | A1_sc k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact EEq.holds_defined_iff.mpr (Part.eq_some_iff.mp (ev_scT k ha)).1
  | A1_tg k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact EEq.holds_defined_iff.mpr (Part.eq_some_iff.mp (ev_tgT k ha)).1
  | A2_sc_sc k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_scT k (ev_scT k ha)) (ev_scT k ha)).mpr
      (Subtype.ext (Compact.model_sc_sc _))
  | A2_sc_tg k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_scT k (ev_tgT k ha)) (ev_tgT k ha)).mpr
      (Subtype.ext (Compact.model_sc_tg _))
  | A2_tg_sc k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_tgT k (ev_scT k ha)) (ev_scT k ha)).mpr
      (Subtype.ext (Compact.model_tg_sc _))
  | A2_tg_tg k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_tgT k (ev_tgT k ha)) (ev_tgT k ha)).mpr
      (Subtype.ext (Compact.model_tg_tg _))
  | A3_dom k s i j =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    obtain ⟨b, hb⟩ := var (s := s) j (by vm)
    exact (EEq.holds_mk'_iff (ev_scT k ha) (ev_tgT k hb)).mpr
      (Subtype.ext (ev_compT_dom k ha hb (EEq.holds_defined_iff.mp (prem _ (by pm)))))
  | A3_def k s i j =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    obtain ⟨b, hb⟩ := var (s := s) j (by vm)
    have hab : sc_is_tg (Fin.castLE hmn k) a.1 b.1 := congrArg Subtype.val
      ((EEq.holds_mk'_iff (ev_scT k ha) (ev_tgT k hb)).mp (prem _ (by pm)))
    exact EEq.holds_defined_iff.mpr (Part.eq_some_iff.mp (ev_compT k ha hb hab)).1
  | A4_sc k s i j =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    obtain ⟨b, hb⟩ := var (s := s) j (by vm)
    have hab := ev_compT_dom k ha hb (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_scT k (ev_compT k ha hb hab)) (ev_scT k hb)).mpr
      (Subtype.ext (Compact.model_sc_comp hab))
  | A4_tg k s i j =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    obtain ⟨b, hb⟩ := var (s := s) j (by vm)
    have hab := ev_compT_dom k ha hb (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_tgT k (ev_compT k ha hb hab)) (ev_tgT k ha)).mpr
      (Subtype.ext (Compact.model_tg_comp hab))
  | A5_sc k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_compT k ha (ev_scT k ha) (Compact.model_tg_sc a.1).symm) ha).mpr
      (Subtype.ext (Compact.model_comp_sc a.1))
  | A5_tg k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_compT k (ev_tgT k ha) ha (Compact.model_sc_tg a.1)) ha).mpr
      (Subtype.ext (Compact.model_tg_comp_self a.1))
  | A6 k s i j l =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    obtain ⟨b, hb⟩ := var (s := s) j (by vm)
    obtain ⟨c, hc⟩ := var (s := s) l (by vm)
    have hab := ev_compT_dom k ha hb (EEq.holds_defined_iff.mp (prem _ (by pm)))
    have hbc := ev_compT_dom k hb hc (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff
      (ev_compT k (ev_compT k ha hb hab) hc ((Compact.model_sc_comp hab).trans hbc))
      (ev_compT k ha (ev_compT k hb hc hbc) (hab.trans (Compact.model_tg_comp hbc).symm))).mpr
      (Subtype.ext (Compact.model_assoc hbc hab))
  | @A7_sc k ws s σ xs =>
    choose a ha using fun j => var (s := ws.get j) (xs j) (by vm; try exact ⟨j, rfl, rfl⟩)
    exact (EEq.holds_mk'_iff (ev_scT k (ev_opT σ ha)) (ev_opT σ fun j => ev_scT k (ha j))).mpr
      (Subtype.ext ((Compact.modelOp M σ).map_sc_eq_sc_map _ _).symm)
  | @A7_tg k ws s σ xs =>
    choose a ha using fun j => var (s := ws.get j) (xs j) (by vm; try exact ⟨j, rfl, rfl⟩)
    exact (EEq.holds_mk'_iff (ev_tgT k (ev_opT σ ha)) (ev_opT σ fun j => ev_tgT k (ha j))).mpr
      (Subtype.ext ((Compact.modelOp M σ).map_tg_eq_tg_map _ _).symm)
  | @A8 k ws s σ xs ys =>
    choose a ha using fun j => var (s := ws.get j) (xs j)
      (by vm; exact Or.inl (Or.inr (Or.inl ⟨j, rfl, rfl⟩)))
    choose b hb using fun j => var (s := ws.get j) (ys j)
      (by vm; exact Or.inl (Or.inr (Or.inr ⟨j, rfl, rfl⟩)))
    have hab : ∀ j, sc_is_tg (Fin.castLE hmn k) (a j).1 (b j).1 := fun j =>
      ev_compT_dom k (ha j) (hb j) (EEq.holds_defined_iff.mp (prem _ (List.mem_ofFn.mpr ⟨j, rfl⟩)))
    exact (EEq.holds_mk'_iff (ev_opT σ fun j => ev_compT k (ha j) (hb j) (hab j))
      (ev_compT k (ev_opT σ ha) (ev_opT σ hb)
        ((Compact.modelOp M σ).comp_map (Compact.pi_sc_is_tg.mpr hab)))).mpr
      (Subtype.ext ((Compact.modelOp M σ).map_comp_eq_comp_map (Compact.pi_sc_is_tg.mpr hab)))
  | AB1_sc_sc l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_scT k (ev_scT l ha)) (ev_scT l ha)).mpr
      (Subtype.ext (Compact.model_sc_k_sc_l _ (ll h)))
  | AB1_tg_tg l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_tgT k (ev_tgT l ha)) (ev_tgT l ha)).mpr
      (Subtype.ext (Compact.model_tg_k_tg_l _ (ll h)))
  | AB1_sc_sck l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_scT l (ev_scT k ha)) (ev_scT l ha)).mpr
      (Subtype.ext (Compact.model_sc_l_sc_k _ (ll h)))
  | AB1_tg_tgk l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_tgT l (ev_tgT k ha)) (ev_tgT l ha)).mpr
      (Subtype.ext (Compact.model_tg_l_tg_k _ (ll h)))
  | AB1_sc_tgk l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_scT l (ev_tgT k ha)) (ev_scT l ha)).mpr
      (Subtype.ext (Compact.model_sc_l_tg_k _ (ll h)))
  | AB1_tg_sck l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_tgT l (ev_scT k ha)) (ev_tgT l ha)).mpr
      (Subtype.ext (Compact.model_tg_l_sc_k _ (ll h)))
  | AB2_sc l k h s i j =>
    obtain ⟨x, hx⟩ := var (s := s) i (by vm)
    obtain ⟨y, hy⟩ := var (s := s) j (by vm)
    have hxy := ev_compT_dom l hx hy (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_scT k (ev_compT l hx hy hxy))
      (ev_compT l (ev_scT k hx) (ev_scT k hy) (Compact.Category.sc_tg_j_sc (ll h) hxy))).mpr
      (Subtype.ext (Compact.Category.sck_compj_eq_compj_sck (ll h) hxy))
  | AB2_tg l k h s i j =>
    obtain ⟨x, hx⟩ := var (s := s) i (by vm)
    obtain ⟨y, hy⟩ := var (s := s) j (by vm)
    have hxy := ev_compT_dom l hx hy (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_tgT k (ev_compT l hx hy hxy))
      (ev_compT l (ev_tgT k hx) (ev_tgT k hy) (Compact.Category.sc_tg_j_tg (ll h) hxy))).mpr
      (Subtype.ext (Compact.Category.tgk_compj_eq_compj_tgk (ll h) hxy))
  | AB3 l k h s i j p q =>
    obtain ⟨x, hx⟩ := var (s := s) i (by vm)
    obtain ⟨y, hy⟩ := var (s := s) j (by vm)
    obtain ⟨z, hz⟩ := var (s := s) p (by vm)
    obtain ⟨t, ht⟩ := var (s := s) q (by vm)
    have hxy := ev_compT_dom l hx hy (EEq.holds_defined_iff.mp (prem _ (by pm)))
    have hzt := ev_compT_dom l hz ht (EEq.holds_defined_iff.mp (prem _ (by pm)))
    have hxz := ev_compT_dom k hx hz (EEq.holds_defined_iff.mp (prem _ (by pm)))
    have hyt := ev_compT_dom k hy ht (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff
      (ev_compT k (ev_compT l hx hy hxy) (ev_compT l hz ht hzt)
        (Compact.Category.sc_tg_k_interchange (ll h) hxz hyt hxy hzt))
      (ev_compT l (ev_compT k hx hz hxz) (ev_compT k hy ht hyt)
        (Compact.Category.sc_tg_j_interchange (ll h) hxz hyt hxy))).mpr
      (Subtype.ext (Compact.Category.interchange (ll h) hxz hyt hxy hzt))

end Trunc

end CompactTrunc
```

:::proposition (label := "truncation-models") (central := true) (title := "Compact truncation sends models to models")
Let $`m \leq n`. $`(\boldsymbol{\tau}^{(m,n)})^{\ast}_{\mathfrak{gd}}` sends the models of
$`(\mathbf{\Sigma}^{(n)}, \mathcal{C}^{\Sigma^{(n)}})` to models of
$`(\mathbf{\Sigma}^{(m)}, \mathcal{C}^{\Sigma^{(m)}})`.

```lean
theorem trunc_sendsModels {m n : ℕ} (hmn : m ≤ n) :
    (trunc Sig hmn).SendsModels.{u, max u v, u, max u v, w}
      (Compact.compactSpec Sig (Fin m)) (Compact.compactSpec Sig (Fin n)) :=
  fun B hB => ⟨Trunc.isAlgebra (M := ⟨B, hB.2⟩), Trunc.holds (M := ⟨B, hB.2⟩)⟩
```
:::

:::proof (of := "truncation-models")
The $`m`-cells are closed under the operations of $`\Sigma^{(m)}`: if every $`x_p` is an $`m`-cell,
so is $`\sigma((x_p)_p)`, by (A$`^{m}`7); for $`k < m`, $`\mathrm{sc}^{k}_{s}(x)` and
$`\mathrm{tg}^{k}_{s}(x)` are $`m`-cells, by (A$`^{k}`2) and (AB$`^{k,m}`1); and the $`k`-composite of two
$`m`-cells is an $`m`-cell, by (AB$`^{k,m}`2). Hence the truncated algebra is the relative subalgebra
on the $`m`-cells, an ep-algebra in which the values of terms are their values in $`\mathbf{B}`, and
every axiom of $`\mathcal{C}^{\Sigma^{(m)}}`, which is an axiom of $`\mathcal{C}^{\Sigma^{(n)}}`, holds
in it.
:::

:::definition (label := "truncation-functor") (central := false) (title := "The compact truncation functor")
Let $`m \leq n`. The *truncation functor* $`T^{(m,n)}` is the birestriction of
$`(\boldsymbol{\tau}^{(m,n)})^{\ast}_{\mathfrak{gd}}` to the categories of models.

```lean
/-- The truncation functor `T⁽ᵐ'ⁿ⁾`. -/
noncomputable def truncFunctor {m n : ℕ} (hmn : m ≤ n) :
    EpSpec.EpAlg.{u, max u v, w} (compactEpSpec Sig (Fin n)) ⥤
      EpSpec.EpAlg.{u, max u v, w} (compactEpSpec Sig (Fin m)) :=
  (trunc Sig hmn).restrict (trunc_sendsModels Sig hmn)
```
:::

# Extended truncation

:::definition (label := "truncation-ext-derivor") (central := false) (title := "The extended truncation derivor")
Let $`m \leq n`. The *extended truncation derivor* $`\boldsymbol{\tau}^{\mathrm{ext}(m,n)}` is the
generalized ep-derivor from $`\mathbf{\Sigma}^{\mathrm{ext}(m)}` to $`\mathbf{\Sigma}^{\mathrm{ext}(n)}`
determined by the embedding of $`\Sigma^{\mathrm{ext}(m)}` into $`\Sigma^{\mathrm{ext}(n)}`:
$`\varphi(k, s) = (k, s)`, $`D_{(k,s)} = \varnothing`, and every operation symbol is sent to itself,
applied to variables.

```lean
section ExtTrunc

variable {n m}

/-- A dimension of `m + 1`, as a dimension of `n + 1`. -/
def castDim (hmn : m ≤ n) (k : Fin (m + 1)) : Fin (n + 1) := Fin.castLE (by omega) k

lemma castDim_lt (hmn : m ≤ n) {j k : Fin (m + 1)} (h : j < k) : castDim hmn j < castDim hmn k :=
  Fin.lt_def.mpr (Fin.lt_def.mp h)

/-- The terms of the extended truncation derivor: every symbol is sent to itself. -/
def truncExtOp (hmn : m ≤ n) : ∀ {ws : List (Fin (m + 1) × S)} {t : Fin (m + 1) × S},
    Extended.ExtendedSignature Sig (Fin (m + 1)) ws t →
    Term (Extended.ExtendedSignature Sig (Fin (n + 1)))
      (Vars ((fun t => (castDim hmn t.1, t.2)) ∘ ws.get)) (castDim hmn t.1, t.2)
  | _, _, .op k σ => .app (.op (castDim hmn k) σ) fun q => .var ⟨Fin.cast (by simp) q, by simp⟩
  | _, _, .sc h s => app₁ (.sc (castDim_lt hmn h) s) (.var ⟨⟨0, by simp⟩, rfl⟩)
  | _, _, .tg h s => app₁ (.tg (castDim_lt hmn h) s) (.var ⟨⟨0, by simp⟩, rfl⟩)
  | _, _, .idm h s => app₁ (.idm (castDim_lt hmn h) s) (.var ⟨⟨0, by simp⟩, rfl⟩)
  | _, _, .comp h s =>
      app₂ (.comp (castDim_lt hmn h) s) (.var ⟨⟨0, by simp⟩, rfl⟩) (.var ⟨⟨1, by simp⟩, rfl⟩)

/-- The extended truncation derivor `𝛕^{ext(m,n)}`. -/
def truncExt (hmn : m ≤ n) : GenEpDerivor (extendedEpSig Sig (Fin (m + 1))) (extendedEpSig Sig (Fin (n + 1))) where
  sortMap t := (castDim hmn t.1, t.2)
  sortDom _ := ∅
  op := truncExtOp Sig hmn

end ExtTrunc
```
:::

```lean
section ExtTrunc

variable {n m}

namespace TruncExt

open Extended.Model

variable {Sig}

/-- The truncated algebra of an extended model. -/
noncomputable abbrev TE (hmn : m ≤ n) (M : Extended.ExtendedPAlg.{u, v, w} Sig (Fin (n + 1))) :=
  (truncExt Sig hmn).derived M.1

variable {hmn : m ≤ n} {M : Extended.ExtendedPAlg.{u, v, w} Sig (Fin (n + 1))}

variable (hmn M) in
noncomputable def tsc {j k : Fin (m + 1)} (h : j < k) {s : S} (x : TE hmn M (k, s)) :
    TE hmn M (j, s) :=
  ⟨sc M (castDim_lt hmn h) x.1, EEq.holdsAll_empty⟩

variable (hmn M) in
noncomputable def ttg {j k : Fin (m + 1)} (h : j < k) {s : S} (x : TE hmn M (k, s)) :
    TE hmn M (j, s) :=
  ⟨tg M (castDim_lt hmn h) x.1, EEq.holdsAll_empty⟩

variable (hmn M) in
noncomputable def tidm {j k : Fin (m + 1)} (h : j < k) {s : S} (u : TE hmn M (j, s)) :
    TE hmn M (k, s) :=
  ⟨idm M (castDim_lt hmn h) u.1, EEq.holdsAll_empty⟩

variable (hmn M) in
noncomputable def tcomp {j k : Fin (m + 1)} (h : j < k) {s : S} (x y : TE hmn M (k, s))
    (hxy : sc M (castDim_lt hmn h) x.1 = tg M (castDim_lt hmn h) y.1) : TE hmn M (k, s) :=
  ⟨comp M (castDim_lt hmn h) x.1 y.1 hxy, EEq.holdsAll_empty⟩

variable (hmn M) in
noncomputable def top (k : Fin (m + 1)) {ws : List S} {s : S} (σ : Sig ws s)
    (b : ∀ p, TE hmn M (k, ws.get p)) : TE hmn M (k, s) :=
  ⟨op M (castDim hmn k) σ fun p => (b p).1, EEq.holdsAll_empty⟩

lemma op_sc {j k : Fin (m + 1)} (h : j < k) {s : S} (x : TE hmn M (k, s)) :
    (TE hmn M).op (.sc h s) (Extended.arg₁ x) = Part.some (tsc hmn M h x) :=
  (truncExt Sig hmn).derived_op_eq_some EEq.holdsAll_empty (Unif.meval_sc _ rfl) _

lemma op_tg {j k : Fin (m + 1)} (h : j < k) {s : S} (x : TE hmn M (k, s)) :
    (TE hmn M).op (.tg h s) (Extended.arg₁ x) = Part.some (ttg hmn M h x) :=
  (truncExt Sig hmn).derived_op_eq_some EEq.holdsAll_empty (Unif.meval_tg _ rfl) _

lemma op_idm {j k : Fin (m + 1)} (h : j < k) {s : S} (u : TE hmn M (j, s)) :
    (TE hmn M).op (.idm h s) (Extended.arg₁ u) = Part.some (tidm hmn M h u) :=
  (truncExt Sig hmn).derived_op_eq_some EEq.holdsAll_empty (Unif.meval_idm _ rfl) _

lemma eval_var_lift (k : Fin (m + 1)) {ws : List S} (b : ∀ p, TE hmn M (k, ws.get p))
    (q : Fin (ws.map fun t => (castDim hmn k, t)).length) (hq) :
    (Term.var ⟨Fin.cast (by simp) q, hq⟩ :
        Term (Extended.ExtendedSignature Sig (Fin (n + 1)))
          (Vars ((fun t => (castDim hmn t.1, t.2)) ∘ (ws.map fun t => (k, t)).get))
          ((ws.map fun t => (castDim hmn k, t)).get q)).eval M.1
      (famVal fun i => (Extended.liftFam k b i).1) =
      Part.some (Extended.liftFam (castDim hmn k) (fun p => (b p).1) q) := by
  have key : ∀ {t' : Fin (m + 1) × S} (e : (k, ws.get (Fin.cast (by simp) q)) = t')
      {u' : Fin (n + 1) × S} (hq : (castDim hmn t'.1, t'.2) = u')
      (e' : (castDim hmn k, ws.get (Fin.cast (by simp) q)) = u'),
      hq ▸ (cast (congrArg (TE hmn M) e) (b (Fin.cast (by simp) q))).1 =
        cast (congrArg M.1 e') (b (Fin.cast (by simp) q)).1 := by
    intro t' e; subst e; intro u' hq; subst hq; intro e'; rfl
  exact congrArg Part.some (key (by simp) hq (by simp))

lemma op_op (k : Fin (m + 1)) {ws : List S} {s : S} (σ : Sig ws s)
    (b : ∀ p, TE hmn M (k, ws.get p)) :
    (TE hmn M).op (.op k σ) (Extended.liftFam k b) = Part.some (top hmn M k σ b) :=
  (truncExt Sig hmn).derived_op_eq_some EEq.holdsAll_empty
    ((eval_app_of_eq_some _ _ _ fun q => eval_var_lift k b q _).trans (Part.some_get _).symm) _

lemma comp_defn_iff {j k : Fin (m + 1)} (h : j < k) {s : S} (x y : TE hmn M (k, s)) :
    EEq.HoldsAll (TE hmn M) (famVal (Extended.arg₂ x y))
      ((extendedEpSig Sig (Fin (m + 1))).defn (.comp h s)) ↔
      sc M (castDim_lt hmn h) x.1 = tg M (castDim_lt hmn h) y.1 := by
  refine EEq.holdsAll_singleton.trans ?_
  refine (EEq.holds_mk'_iff ((Extended.eval_app₁ _ rfl).trans (op_sc h x))
    ((Extended.eval_app₁ _ rfl).trans (op_tg h y))).trans ?_
  exact ⟨fun e => congrArg Subtype.val e, fun e => Subtype.ext e⟩

lemma op_comp {j k : Fin (m + 1)} (h : j < k) {s : S} (x y : TE hmn M (k, s))
    (hxy : sc M (castDim_lt hmn h) x.1 = tg M (castDim_lt hmn h) y.1) :
    (TE hmn M).op (.comp h s) (Extended.arg₂ x y) = Part.some (tcomp hmn M h x y hxy) :=
  (truncExt Sig hmn).derived_op_eq_some ((comp_defn_iff h x y).mpr hxy)
    (Unif.meval_comp _ rfl rfl hxy) _

lemma op_comp_dom {j k : Fin (m + 1)} (h : j < k) {s : S} (x y : TE hmn M (k, s)) :
    ((TE hmn M).op (.comp h s) (Extended.arg₂ x y)).Dom ↔
      sc M (castDim_lt hmn h) x.1 = tg M (castDim_lt hmn h) y.1 :=
  ⟨fun hd => (comp_defn_iff h x y).mp (((truncExt Sig hmn).op_derived_dom_iff _ _).mp hd).1,
    fun hxy => (Part.eq_some_iff.mp (op_comp h x y hxy)).1⟩

theorem isAlgebra : (extendedEpSig Sig (Fin (m + 1))).IsAlgebra (TE hmn M) := by
  intro ws t σ a
  cases σ with
  | op k σ =>
    obtain ⟨b, rfl⟩ : ∃ b, Extended.liftFam k b = a := ⟨_, Extended.liftFam_unlift k a⟩
    exact ⟨fun _ => EEq.holdsAll_empty, fun _ => (Part.eq_some_iff.mp (op_op k σ b)).1⟩
  | sc h s =>
    have ha : Extended.arg₁ (a ⟨0, by simp⟩) = a := by funext i; match i with | ⟨0, _⟩ => rfl
    exact ⟨fun _ => EEq.holdsAll_empty, fun _ => ha ▸ (Part.eq_some_iff.mp (op_sc h _)).1⟩
  | tg h s =>
    have ha : Extended.arg₁ (a ⟨0, by simp⟩) = a := by funext i; match i with | ⟨0, _⟩ => rfl
    exact ⟨fun _ => EEq.holdsAll_empty, fun _ => ha ▸ (Part.eq_some_iff.mp (op_tg h _)).1⟩
  | idm h s =>
    have ha : Extended.arg₁ (a ⟨0, by simp⟩) = a := by funext i; match i with | ⟨0, _⟩ => rfl
    exact ⟨fun _ => EEq.holdsAll_empty, fun _ => ha ▸ (Part.eq_some_iff.mp (op_idm h _)).1⟩
  | comp h s =>
    have ha : Extended.arg₂ (a ⟨0, by simp⟩) (a ⟨1, by simp⟩) = a := by
      funext i; match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl
    exact ha ▸ (op_comp_dom h _ _).trans (comp_defn_iff h _ _).symm

section Eval

variable {val : ∀ t, Extended.EVar S (Fin (m + 1)) t → Part ((TE hmn M) t)}

lemma ev_scT {j k : Fin (m + 1)} (h : j < k) {s : S} {t : Extended.ETerm Sig (Fin (m + 1)) (k, s)}
    {x : TE hmn M (k, s)} (ht : t.eval (TE hmn M) val = Part.some x) :
    (Extended.ETerm.scT h t).eval (TE hmn M) val = Part.some (tsc hmn M h x) :=
  (Extended.eval_app₁ _ ht).trans (op_sc h x)

lemma ev_tgT {j k : Fin (m + 1)} (h : j < k) {s : S} {t : Extended.ETerm Sig (Fin (m + 1)) (k, s)}
    {x : TE hmn M (k, s)} (ht : t.eval (TE hmn M) val = Part.some x) :
    (Extended.ETerm.tgT h t).eval (TE hmn M) val = Part.some (ttg hmn M h x) :=
  (Extended.eval_app₁ _ ht).trans (op_tg h x)

lemma ev_idmT {j k : Fin (m + 1)} (h : j < k) {s : S}
    {t : Extended.ETerm Sig (Fin (m + 1)) (j, s)} {u : TE hmn M (j, s)}
    (ht : t.eval (TE hmn M) val = Part.some u) :
    (Extended.ETerm.idmT h t).eval (TE hmn M) val = Part.some (tidm hmn M h u) :=
  (Extended.eval_app₁ _ ht).trans (op_idm h u)

lemma ev_compT {j k : Fin (m + 1)} (h : j < k) {s : S}
    {t t' : Extended.ETerm Sig (Fin (m + 1)) (k, s)} {x y : TE hmn M (k, s)}
    (ht : t.eval (TE hmn M) val = Part.some x) (ht' : t'.eval (TE hmn M) val = Part.some y)
    (hxy : sc M (castDim_lt hmn h) x.1 = tg M (castDim_lt hmn h) y.1) :
    (Extended.ETerm.compT h t t').eval (TE hmn M) val = Part.some (tcomp hmn M h x y hxy) :=
  (Extended.eval_app₂ _ ht ht').trans (op_comp h x y hxy)

lemma ev_compT_dom {j k : Fin (m + 1)} (h : j < k) {s : S}
    {t t' : Extended.ETerm Sig (Fin (m + 1)) (k, s)} {x y : TE hmn M (k, s)}
    (ht : t.eval (TE hmn M) val = Part.some x) (ht' : t'.eval (TE hmn M) val = Part.some y)
    (hd : ((Extended.ETerm.compT h t t').eval (TE hmn M) val).Dom) :
    sc M (castDim_lt hmn h) x.1 = tg M (castDim_lt hmn h) y.1 :=
  (op_comp_dom h x y).mp ((Extended.eval_app₂ _ ht ht') ▸ hd)

lemma ev_opT (k : Fin (m + 1)) {ws : List S} {s : S} (σ : Sig ws s)
    {ts : (p : Fin ws.length) → Extended.ETerm Sig (Fin (m + 1)) (k, ws.get p)}
    {b : ∀ p, TE hmn M (k, ws.get p)} (h : ∀ p, (ts p).eval (TE hmn M) val = Part.some (b p)) :
    (Extended.ETerm.opT k σ ts).eval (TE hmn M) val = Part.some (top hmn M k σ b) :=
  (Extended.eval_opT k σ h).trans (op_op k σ b)

end Eval

/-- The variables of an axiom. -/
local macro "vm" : tactic => `(tactic| (
  simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, Extended.ETerm.scT, Extended.ETerm.tgT,
    Extended.ETerm.idmT, Extended.ETerm.compT, Extended.ETerm.x, Extended.vars_opT]))

/-- A premise of an axiom. -/
local macro "pm" : tactic => `(tactic| (
  first
    | exact List.Mem.head _
    | exact List.Mem.tail _ (List.Mem.head _)
    | exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    | exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

open Extended.ETerm in
theorem holds : ∀ q ∈ Extended.extendedSpec Sig (Fin (m + 1)), q.Holds (TE hmn M) := by
  intro q hq val hvars hprem
  have var : ∀ {t : Fin (m + 1) × S} (i : ℕ),
      (⟨t, i⟩ : Σ t, Extended.EVar S (Fin (m + 1)) t) ∈ q.vars →
      ∃ x, (Extended.ETerm.x (Sig := Sig) (t := t) i).eval (TE hmn M) val = Part.some x :=
    fun i hi => ⟨_, (Part.some_get (hvars _ hi)).symm⟩
  have prem : ∀ e ∈ q.premises, e.Holds (TE hmn M) val := hprem
  have cl := fun {a b : Fin (m + 1)} (h : a < b) => castDim_lt hmn h
  cases hq with
  | @EA0 k ws s σ xs =>
    choose b hb using fun p => var (t := (k, ws.get p)) (xs p) (by vm; exact ⟨p, rfl, rfl⟩)
    exact EEq.holds_defined_iff.mpr (Part.eq_some_iff.mp (ev_opT k σ hb)).1
  | @EA1_sc j k h s i =>
    obtain ⟨a, ha⟩ := var (t := (k, s)) i (by vm)
    exact EEq.holds_defined_iff.mpr (Part.eq_some_iff.mp (ev_scT h ha)).1
  | @EA1_tg j k h s i =>
    obtain ⟨a, ha⟩ := var (t := (k, s)) i (by vm)
    exact EEq.holds_defined_iff.mpr (Part.eq_some_iff.mp (ev_tgT h ha)).1
  | @EA1_idm j k h s i =>
    obtain ⟨a, ha⟩ := var (t := (j, s)) i (by vm)
    exact EEq.holds_defined_iff.mpr (Part.eq_some_iff.mp (ev_idmT h ha)).1
  | @EA2_sc j k h s i =>
    obtain ⟨u, hu⟩ := var (t := (j, s)) i (by vm)
    exact (EEq.holds_mk'_iff (ev_scT h (ev_idmT h hu)) hu).mpr (Subtype.ext (sc_idm _))
  | @EA2_tg j k h s i =>
    obtain ⟨u, hu⟩ := var (t := (j, s)) i (by vm)
    exact (EEq.holds_mk'_iff (ev_tgT h (ev_idmT h hu)) hu).mpr (Subtype.ext (tg_idm _))
  | @EA3_dom j k h s i i' =>
    obtain ⟨a, ha⟩ := var (t := (k, s)) i (by vm)
    obtain ⟨b, hb⟩ := var (t := (k, s)) i' (by vm)
    have hab := ev_compT_dom h ha hb (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_scT h ha) (ev_tgT h hb)).mpr (Subtype.ext hab)
  | @EA3_def j k h s i i' =>
    obtain ⟨a, ha⟩ := var (t := (k, s)) i (by vm)
    obtain ⟨b, hb⟩ := var (t := (k, s)) i' (by vm)
    have hab : sc M (cl h) a.1 = tg M (cl h) b.1 := congrArg Subtype.val
      ((EEq.holds_mk'_iff (ev_scT h ha) (ev_tgT h hb)).mp (prem _ (by pm)))
    exact EEq.holds_defined_iff.mpr (Part.eq_some_iff.mp (ev_compT h ha hb hab)).1
  | @EA4_sc j k h s i i' =>
    obtain ⟨a, ha⟩ := var (t := (k, s)) i (by vm)
    obtain ⟨b, hb⟩ := var (t := (k, s)) i' (by vm)
    have hab := ev_compT_dom h ha hb (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_scT h (ev_compT h ha hb hab)) (ev_scT h hb)).mpr
      (Subtype.ext (sc_comp hab))
  | @EA4_tg j k h s i i' =>
    obtain ⟨a, ha⟩ := var (t := (k, s)) i (by vm)
    obtain ⟨b, hb⟩ := var (t := (k, s)) i' (by vm)
    have hab := ev_compT_dom h ha hb (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_tgT h (ev_compT h ha hb hab)) (ev_tgT h ha)).mpr
      (Subtype.ext (tg_comp hab))
  | @EA5_sc j k h s i =>
    obtain ⟨a, ha⟩ := var (t := (k, s)) i (by vm)
    exact (EEq.holds_mk'_iff (ev_compT h ha (ev_idmT h (ev_scT h ha)) (tg_idm _).symm) ha).mpr
      (Subtype.ext (comp_idm_sc a.1))
  | @EA5_tg j k h s i =>
    obtain ⟨a, ha⟩ := var (t := (k, s)) i (by vm)
    exact (EEq.holds_mk'_iff (ev_compT h (ev_idmT h (ev_tgT h ha)) ha (sc_idm _)) ha).mpr
      (Subtype.ext (idm_tg_comp a.1))
  | @EA6 j k h s i i' i'' =>
    obtain ⟨a, ha⟩ := var (t := (k, s)) i (by vm)
    obtain ⟨b, hb⟩ := var (t := (k, s)) i' (by vm)
    obtain ⟨c, hc⟩ := var (t := (k, s)) i'' (by vm)
    have hab := ev_compT_dom h ha hb (EEq.holds_defined_iff.mp (prem _ (by pm)))
    have hbc := ev_compT_dom h hb hc (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_compT h (ev_compT h ha hb hab) hc ((sc_comp hab).trans hbc))
      (ev_compT h ha (ev_compT h hb hc hbc) (hab.trans (tg_comp hbc).symm))).mpr
      (Subtype.ext (comp_assoc hab hbc))
  | @EA7_sc j k h ws s σ xs =>
    choose b hb using fun p => var (t := (k, ws.get p)) (xs p) (by vm; exact ⟨p, rfl, rfl⟩)
    exact (EEq.holds_mk'_iff (ev_scT h (ev_opT k σ hb)) (ev_opT j σ fun p => ev_scT h (hb p))).mpr
      (Subtype.ext (sc_op (cl h) σ _))
  | @EA7_tg j k h ws s σ xs =>
    choose b hb using fun p => var (t := (k, ws.get p)) (xs p) (by vm; exact ⟨p, rfl, rfl⟩)
    exact (EEq.holds_mk'_iff (ev_tgT h (ev_opT k σ hb)) (ev_opT j σ fun p => ev_tgT h (hb p))).mpr
      (Subtype.ext (tg_op (cl h) σ _))
  | @EA7_idm j k h ws s σ us =>
    choose b hb using fun p => var (t := (j, ws.get p)) (us p) (by vm; exact ⟨p, rfl, rfl⟩)
    exact (EEq.holds_mk'_iff (ev_idmT h (ev_opT j σ hb)) (ev_opT k σ fun p => ev_idmT h (hb p))).mpr
      (Subtype.ext (idm_op (cl h) σ _))
  | @EA8 j k h ws s σ xs ys =>
    choose a ha using fun p => var (t := (k, ws.get p)) (xs p)
      (by vm; exact Or.inl (Or.inr (Or.inl ⟨p, rfl, rfl⟩)))
    choose b hb using fun p => var (t := (k, ws.get p)) (ys p)
      (by vm; exact Or.inl (Or.inr (Or.inr ⟨p, rfl, rfl⟩)))
    have hab : ∀ p, sc M (cl h) (a p).1 = tg M (cl h) (b p).1 := fun p =>
      ev_compT_dom h (ha p) (hb p) (EEq.holds_defined_iff.mp (prem _ (List.mem_ofFn.mpr ⟨p, rfl⟩)))
    exact (EEq.holds_mk'_iff (ev_opT k σ fun p => ev_compT h (ha p) (hb p) (hab p))
      (ev_compT h (ev_opT k σ ha) (ev_opT k σ hb)
        ((sc_op (cl h) σ _).trans ((congrArg (op M _ σ) (funext hab)).trans
          (tg_op (cl h) σ _).symm)))).mpr
      (Subtype.ext (Extended.Model.op_comp (cl h) σ _ _ hab))
  | @EA1'_sc_sc a b c h₁ h₂ s i =>
    obtain ⟨x, hx⟩ := var (t := (c, s)) i (by vm)
    exact (EEq.holds_mk'_iff (ev_scT h₁ (ev_scT h₂ hx)) (ev_scT (h₁.trans h₂) hx)).mpr
      (Subtype.ext (sc_sc (h₁ := cl h₁) (h₂ := cl h₂) x.1))
  | @EA1'_tg_tg a b c h₁ h₂ s i =>
    obtain ⟨x, hx⟩ := var (t := (c, s)) i (by vm)
    exact (EEq.holds_mk'_iff (ev_tgT h₁ (ev_tgT h₂ hx)) (ev_tgT (h₁.trans h₂) hx)).mpr
      (Subtype.ext (tg_tg (h₁ := cl h₁) (h₂ := cl h₂) x.1))
  | @EA1'_sc_tg a b c h₁ h₂ s i =>
    obtain ⟨x, hx⟩ := var (t := (c, s)) i (by vm)
    exact (EEq.holds_mk'_iff (ev_scT h₁ (ev_tgT h₂ hx)) (ev_scT (h₁.trans h₂) hx)).mpr
      (Subtype.ext (sc_tg (h₁ := cl h₁) (h₂ := cl h₂) x.1))
  | @EA1'_tg_sc a b c h₁ h₂ s i =>
    obtain ⟨x, hx⟩ := var (t := (c, s)) i (by vm)
    exact (EEq.holds_mk'_iff (ev_tgT h₁ (ev_scT h₂ hx)) (ev_tgT (h₁.trans h₂) hx)).mpr
      (Subtype.ext (tg_sc (h₁ := cl h₁) (h₂ := cl h₂) x.1))
  | @EA2' a b c h₁ h₂ s i =>
    obtain ⟨u, hu⟩ := var (t := (a, s)) i (by vm)
    exact (EEq.holds_mk'_iff (ev_idmT h₂ (ev_idmT h₁ hu)) (ev_idmT (h₁.trans h₂) hu)).mpr
      (Subtype.ext (idm_idm (h₁ := cl h₁) (h₂ := cl h₂) u.1))
  | @EA3'_sc a b c h₁ h₂ s i i' =>
    obtain ⟨x, hx⟩ := var (t := (c, s)) i (by vm)
    obtain ⟨y, hy⟩ := var (t := (c, s)) i' (by vm)
    have hxy := ev_compT_dom (h₁.trans h₂) hx hy (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_scT h₂ (ev_compT (h₁.trans h₂) hx hy hxy))
      (ev_compT h₁ (ev_scT h₂ hx) (ev_scT h₂ hy)
        ((sc_sc (h₁ := cl h₁) (h₂ := cl h₂) _).trans (hxy.trans
          (tg_sc (h₁ := cl h₁) (h₂ := cl h₂) _).symm)))).mpr
      (Subtype.ext (sc_comp' (h₁ := cl h₁) (h₂ := cl h₂) hxy))
  | @EA3'_tg a b c h₁ h₂ s i i' =>
    obtain ⟨x, hx⟩ := var (t := (c, s)) i (by vm)
    obtain ⟨y, hy⟩ := var (t := (c, s)) i' (by vm)
    have hxy := ev_compT_dom (h₁.trans h₂) hx hy (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_tgT h₂ (ev_compT (h₁.trans h₂) hx hy hxy))
      (ev_compT h₁ (ev_tgT h₂ hx) (ev_tgT h₂ hy)
        ((sc_tg (h₁ := cl h₁) (h₂ := cl h₂) _).trans (hxy.trans
          (tg_tg (h₁ := cl h₁) (h₂ := cl h₂) _).symm)))).mpr
      (Subtype.ext (tg_comp' (h₁ := cl h₁) (h₂ := cl h₂) hxy))
  | @EA4' a b c h₁ h₂ s i i' p q =>
    obtain ⟨x, hx⟩ := var (t := (c, s)) i (by vm)
    obtain ⟨y, hy⟩ := var (t := (c, s)) i' (by vm)
    obtain ⟨z, hz⟩ := var (t := (c, s)) p (by vm)
    obtain ⟨t, ht⟩ := var (t := (c, s)) q (by vm)
    have hxy := ev_compT_dom h₂ hx hy (EEq.holds_defined_iff.mp (prem _ (by pm)))
    have hzt := ev_compT_dom h₂ hz ht (EEq.holds_defined_iff.mp (prem _ (by pm)))
    have hxz := ev_compT_dom (h₁.trans h₂) hx hz (EEq.holds_defined_iff.mp (prem _ (by pm)))
    have hyt := ev_compT_dom (h₁.trans h₂) hy ht (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff
      (ev_compT (h₁.trans h₂) (ev_compT h₂ hx hy hxy) (ev_compT h₂ hz ht hzt)
        ((sc_comp_low (h₁ := cl h₁) (h₂ := cl h₂) hxy).trans
          ((sc_eq_sc_of_comp (h₁ := cl h₁) (h₂ := cl h₂) hxy).symm.trans
            (hxz.trans (tg_comp_low (h₁ := cl h₁) (h₂ := cl h₂) hzt).symm))))
      (ev_compT h₂ (ev_compT (h₁.trans h₂) hx hz hxz) (ev_compT (h₁.trans h₂) hy ht hyt)
        ((sc_comp' (h₁ := cl h₁) (h₂ := cl h₂) hxz).trans ((comp_congr hxy hzt _ _).trans
          (tg_comp' (h₁ := cl h₁) (h₂ := cl h₂) hyt).symm)))).mpr
      (Subtype.ext (interchange (h₁ := cl h₁) (h₂ := cl h₂) hxy hzt hxz hyt))
  | @EA5' a b c h₁ h₂ s i i' =>
    obtain ⟨u, hu⟩ := var (t := (b, s)) i (by vm)
    obtain ⟨v, hv⟩ := var (t := (b, s)) i' (by vm)
    have huv := ev_compT_dom h₁ hu hv (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_idmT h₂ (ev_compT h₁ hu hv huv))
      (ev_compT (h₁.trans h₂) (ev_idmT h₂ hu) (ev_idmT h₂ hv)
        ((sc_idm_low (h₁ := cl h₁) (h₂ := cl h₂) _).trans (huv.trans
          (tg_idm_low (h₁ := cl h₁) (h₂ := cl h₂) _).symm)))).mpr
      (Subtype.ext (idm_comp (h₁ := cl h₁) (h₂ := cl h₂) huv))

end TruncExt

end ExtTrunc
```

:::proposition (label := "truncation-ext-models") (central := true) (title := "Extended truncation sends models to models")
Let $`m \leq n`. $`(\boldsymbol{\tau}^{\mathrm{ext}(m,n)})^{\ast}_{\mathfrak{gd}}` sends the models of
$`(\mathbf{\Sigma}^{\mathrm{ext}(n)}, \mathcal{C}^{\Sigma^{\mathrm{ext}(n)}})` to models of
$`(\mathbf{\Sigma}^{\mathrm{ext}(m)}, \mathcal{C}^{\Sigma^{\mathrm{ext}(m)}})`.

```lean
theorem truncExt_sendsModels {m n : ℕ} (hmn : m ≤ n) :
    (truncExt Sig hmn).SendsModels.{u, max u v, u, max u v, w}
      (Extended.extendedSpec Sig (Fin (m + 1))) (Extended.extendedSpec Sig (Fin (n + 1))) :=
  fun B hB => ⟨TruncExt.isAlgebra (M := ⟨B, hB.2⟩), TruncExt.holds (M := ⟨B, hB.2⟩)⟩
```
:::

:::proof (of := "truncation-ext-models")
Every operation symbol is sent to itself, and all the cells of dimension at most $`m` are in the
domains, so the truncated algebra keeps the cells of dimension at most $`m` with the restrictions of
the operations, and it is an ep-algebra. Its axioms are axioms of
$`\mathcal{C}^{\Sigma^{\mathrm{ext}(n)}}`, with the dimensions renamed, and the values of terms are
their values in $`\mathbf{B}`.
:::

:::definition (label := "truncation-ext-functor") (central := false) (title := "The extended truncation functor")
Let $`m \leq n`. The *extended truncation functor* $`T^{\mathrm{ext}(m,n)}` is the birestriction of
$`(\boldsymbol{\tau}^{\mathrm{ext}(m,n)})^{\ast}_{\mathfrak{gd}}` to the categories of models.

```lean
/-- The extended truncation functor `T^{ext(m,n)}`. -/
noncomputable def truncExtFunctor {m n : ℕ} (hmn : m ≤ n) :
    EpSpec.EpAlg.{u, max u v, w} (extendedEpSpec Sig (Fin (n + 1))) ⥤
      EpSpec.EpAlg.{u, max u v, w} (extendedEpSpec Sig (Fin (m + 1))) :=
  (truncExt Sig hmn).restrict (truncExt_sendsModels Sig hmn)
```
:::

# Extended discretization

:::definition (label := "discretization-ext-derivor") (central := false) (title := "The extended discretization derivor")
Write $`\underline{k} = \min\{k, m\}`. The *extended discretization derivor*
$`\boldsymbol{\delta}^{\mathrm{ext}(n,m)} = (\varphi, D, d)` is the generalized ep-derivor from
$`\mathbf{\Sigma}^{\mathrm{ext}(n)}` to $`\mathbf{\Sigma}^{\mathrm{ext}(m)}` with
$`\varphi(k, s) = (\underline{k}, s)`, $`D_{(k,s)} = \varnothing`,
$`d(\sigma_k) = \sigma_{\underline{k}}((v_p)_p)`, and, for $`j < k`: if $`j < m`,
$`d(\mathrm{sc}^{(j,k)}_{s}) = \mathrm{sc}^{(j,\underline{k})}_{s}(v_0)`,
$`d(\mathrm{tg}^{(j,k)}_{s}) = \mathrm{tg}^{(j,\underline{k})}_{s}(v_0)`,
$`d(\mathrm{i}^{(k,j)}_{s}) = \mathrm{i}^{(\underline{k},j)}_{s}(v_0)` and
$`d(\circ^{(j,k)}_{s}) = v_0 \circ^{(j,\underline{k})}_{s} v_1`; if $`j \geq m`, all four are $`v_0`.

If $`j \geq m`, then $`\underline{j} = \underline{k} = m`, so that $`v_0` has the right sort; in the
Lean these two sorts are equal but not definitionally, and the variable carries the equality.

```lean
/-- The dimension `min(k, m)`. -/
def lowE {n : ℕ} (m : ℕ) (k : Fin (n + 1)) : Fin (m + 1) := ⟨min k.val m, by omega⟩

lemma lowE_lt {n m : ℕ} {j k : Fin (n + 1)} (h : j < k) (hj : j.val < m) : lowE m j < lowE m k := by
  have := Fin.lt_def.mp h
  simp only [lowE, Fin.lt_def]; omega

lemma lowE_eq {n m : ℕ} {j k : Fin (n + 1)} (h : j < k) (hj : ¬ j.val < m) : lowE m k = lowE m j := by
  have := Fin.lt_def.mp h
  simp only [lowE, Fin.ext_iff]; omega

/-- The terms of the extended discretization derivor. -/
def discExtOp (n m : ℕ) : ∀ {ws : List (Fin (n + 1) × S)} {t : Fin (n + 1) × S},
    Extended.ExtendedSignature Sig (Fin (n + 1)) ws t →
    Term (Extended.ExtendedSignature Sig (Fin (m + 1)))
      (Vars ((fun t => (lowE m t.1, t.2)) ∘ ws.get)) (lowE m t.1, t.2)
  | _, _, .op k σ => .app (.op (lowE m k) σ) fun q => .var ⟨Fin.cast (by simp) q, by simp⟩
  | _, _, @Extended.ExtendedSignature.sc _ _ _ _ j _ h s => if hj : j.val < m then app₁ (.sc (lowE_lt h hj) s) (.var ⟨⟨0, by simp⟩, rfl⟩)
      else .var ⟨⟨0, by simp⟩, by simp [lowE_eq h hj]⟩
  | _, _, @Extended.ExtendedSignature.tg _ _ _ _ j _ h s => if hj : j.val < m then app₁ (.tg (lowE_lt h hj) s) (.var ⟨⟨0, by simp⟩, rfl⟩)
      else .var ⟨⟨0, by simp⟩, by simp [lowE_eq h hj]⟩
  | _, _, @Extended.ExtendedSignature.idm _ _ _ _ j _ h s => if hj : j.val < m then app₁ (.idm (lowE_lt h hj) s) (.var ⟨⟨0, by simp⟩, rfl⟩)
      else .var ⟨⟨0, by simp⟩, by simp [lowE_eq h hj]⟩
  | _, _, @Extended.ExtendedSignature.comp _ _ _ _ j _ h s => if hj : j.val < m then
      app₂ (.comp (lowE_lt h hj) s) (.var ⟨⟨0, by simp⟩, rfl⟩) (.var ⟨⟨1, by simp⟩, rfl⟩)
      else .var ⟨⟨0, by simp⟩, rfl⟩

/-- The extended discretization derivor `𝛅^{ext(n,m)}`. -/
def discExt (n m : ℕ) : GenEpDerivor (extendedEpSig Sig (Fin (n + 1))) (extendedEpSig Sig (Fin (m + 1))) where
  sortMap t := (lowE m t.1, t.2)
  sortDom _ := ∅
  op := discExtOp Sig n m
```
:::

The discretized algebra $`(\boldsymbol{\delta}^{\mathrm{ext}(n,m)})^{\ast}_{\mathfrak{gd}}(\mathbf{B})`
has as cells of sort $`(k, s)` the $`\underline{k}`-cells of sort $`s` of $`\mathbf{B}`. Its structure in
the dimensions $`j < m` is that of $`\mathbf{B}`; for $`j \geq m` its $`(j,k)`-sources, targets and
identities are transports between two equal sorts, and $`x \circ^{(j,k)} y` is defined exactly when
$`x = y`, and then it is $`x`.

```lean
namespace DiscExt

open Extended.Model

variable {Sig n m}

/-- The discretized algebra of an extended model. -/
noncomputable abbrev DE (n : ℕ) (M : Extended.ExtendedPAlg.{u, v, w} Sig (Fin (m + 1))) :=
  (discExt Sig n m).derived M.1

variable {M : Extended.ExtendedPAlg.{u, v, w} Sig (Fin (m + 1))}

variable (M) in
/-- Transport along an equality of sorts. -/
def tp {t t' : Fin (m + 1) × S} (e : t = t') (y : M.1 t) : M.1 t' := e ▸ y

lemma tp_self {t : Fin (m + 1) × S} (e : t = t) (y : M.1 t) : tp M e y = y := rfl

lemma tp_tp {t t' t'' : Fin (m + 1) × S} (e : t = t') (e' : t' = t'') (y : M.1 t) :
    tp M e' (tp M e y) = tp M (e.trans e') y := by
  subst e e'; rfl

lemma tp_inj {t t' : Fin (m + 1) × S} (e : t = t') {y y' : M.1 t} (h : tp M e y = tp M e y') :
    y = y' := by
  subst e; exact h

lemma low_eq_s {j k : Fin (n + 1)} (h : j < k) (hj : ¬ j.val < m) (s : S) :
    (lowE m k, s) = (lowE m j, s) := by rw [lowE_eq h hj]

variable (M) in
noncomputable def esc {j k : Fin (n + 1)} (h : j < k) {s : S} (x : DE n M (k, s)) : DE n M (j, s) :=
  ⟨if hj : j.val < m then sc M (lowE_lt h hj) x.1 else tp M (low_eq_s h hj s) x.1,
    EEq.holdsAll_empty⟩

variable (M) in
noncomputable def etg {j k : Fin (n + 1)} (h : j < k) {s : S} (x : DE n M (k, s)) : DE n M (j, s) :=
  ⟨if hj : j.val < m then tg M (lowE_lt h hj) x.1 else tp M (low_eq_s h hj s) x.1,
    EEq.holdsAll_empty⟩

variable (M) in
noncomputable def eidm {j k : Fin (n + 1)} (h : j < k) {s : S} (u : DE n M (j, s)) : DE n M (k, s) :=
  ⟨if hj : j.val < m then idm M (lowE_lt h hj) u.1 else tp M (low_eq_s h hj s).symm u.1,
    EEq.holdsAll_empty⟩

lemma esc_pos {j k : Fin (n + 1)} {h : j < k} (hj : j.val < m) {s : S} (x : DE n M (k, s)) :
    (esc M h x).1 = sc M (lowE_lt h hj) x.1 := dif_pos hj

lemma esc_neg {j k : Fin (n + 1)} {h : j < k} (hj : ¬ j.val < m) {s : S} (x : DE n M (k, s)) :
    (esc M h x).1 = tp M (low_eq_s h hj s) x.1 := dif_neg hj

lemma etg_pos {j k : Fin (n + 1)} {h : j < k} (hj : j.val < m) {s : S} (x : DE n M (k, s)) :
    (etg M h x).1 = tg M (lowE_lt h hj) x.1 := dif_pos hj

lemma etg_neg {j k : Fin (n + 1)} {h : j < k} (hj : ¬ j.val < m) {s : S} (x : DE n M (k, s)) :
    (etg M h x).1 = tp M (low_eq_s h hj s) x.1 := dif_neg hj

lemma eidm_pos {j k : Fin (n + 1)} {h : j < k} (hj : j.val < m) {s : S} (u : DE n M (j, s)) :
    (eidm M h u).1 = idm M (lowE_lt h hj) u.1 := dif_pos hj

lemma eidm_neg {j k : Fin (n + 1)} {h : j < k} (hj : ¬ j.val < m) {s : S} (u : DE n M (j, s)) :
    (eidm M h u).1 = tp M (low_eq_s h hj s).symm u.1 := dif_neg hj

lemma cond_pos {j k : Fin (n + 1)} {h : j < k} (hj : j.val < m) {s : S} {x y : DE n M (k, s)} :
    esc M h x = etg M h y ↔ sc M (lowE_lt h hj) x.1 = tg M (lowE_lt h hj) y.1 :=
  ⟨fun e => (esc_pos hj x).symm.trans ((congrArg Subtype.val e).trans (etg_pos hj y)),
    fun e => Subtype.ext ((esc_pos hj x).trans (e.trans (etg_pos hj y).symm))⟩

lemma cond_neg {j k : Fin (n + 1)} {h : j < k} (hj : ¬ j.val < m) {s : S} {x y : DE n M (k, s)} :
    esc M h x = etg M h y ↔ x = y :=
  ⟨fun e => Subtype.ext (tp_inj (low_eq_s h hj s)
      ((esc_neg hj x).symm.trans ((congrArg Subtype.val e).trans (etg_neg hj y)))),
    fun e => e ▸ Subtype.ext ((esc_neg hj x).trans (etg_neg hj x).symm)⟩

variable (M) in
noncomputable def ecomp {j k : Fin (n + 1)} (h : j < k) {s : S} (x y : DE n M (k, s))
    (hxy : esc M h x = etg M h y) : DE n M (k, s) :=
  ⟨if hj : j.val < m then comp M (lowE_lt h hj) x.1 y.1 ((cond_pos hj).mp hxy) else x.1,
    EEq.holdsAll_empty⟩

lemma ecomp_pos {j k : Fin (n + 1)} {h : j < k} (hj : j.val < m) {s : S} (x y : DE n M (k, s))
    (hxy : esc M h x = etg M h y) :
    (ecomp M h x y hxy).1 = comp M (lowE_lt h hj) x.1 y.1 ((cond_pos hj).mp hxy) := dif_pos hj

lemma ecomp_neg {j k : Fin (n + 1)} {h : j < k} (hj : ¬ j.val < m) {s : S} (x y : DE n M (k, s))
    (hxy : esc M h x = etg M h y) : ecomp M h x y hxy = x := Subtype.ext (dif_neg hj)

variable (M) in
noncomputable def eop (k : Fin (n + 1)) {ws : List S} {s : S} (σ : Sig ws s)
    (b : ∀ p, DE n M (k, ws.get p)) : DE n M (k, s) :=
  ⟨op M (lowE m k) σ fun p => (b p).1, EEq.holdsAll_empty⟩

lemma op_sc {j k : Fin (n + 1)} (h : j < k) {s : S} (x : DE n M (k, s)) :
    (DE n M).op (.sc h s) (Extended.arg₁ x) = Part.some (esc M h x) := by
  refine (discExt Sig n m).derived_op_eq_some EEq.holdsAll_empty ?_ _
  by_cases hj : j.val < m
  · have e : (discExt Sig n m).op (.sc h s) =
        app₁ (.sc (lowE_lt h hj) s) (.var ⟨⟨0, by simp⟩, rfl⟩) := dif_pos hj
    rw [e]
    exact (Unif.meval_sc _ rfl).trans (congrArg Part.some (esc_pos (h := h) hj x).symm)
  · have e : (discExt Sig n m).op (.sc h s) = .var ⟨⟨0, by simp⟩, low_eq_s h hj s⟩ := dif_neg hj
    rw [e]
    exact congrArg Part.some (esc_neg (h := h) hj x).symm

lemma op_tg {j k : Fin (n + 1)} (h : j < k) {s : S} (x : DE n M (k, s)) :
    (DE n M).op (.tg h s) (Extended.arg₁ x) = Part.some (etg M h x) := by
  refine (discExt Sig n m).derived_op_eq_some EEq.holdsAll_empty ?_ _
  by_cases hj : j.val < m
  · have e : (discExt Sig n m).op (.tg h s) =
        app₁ (.tg (lowE_lt h hj) s) (.var ⟨⟨0, by simp⟩, rfl⟩) := dif_pos hj
    rw [e]
    exact (Unif.meval_tg _ rfl).trans (congrArg Part.some (etg_pos (h := h) hj x).symm)
  · have e : (discExt Sig n m).op (.tg h s) = .var ⟨⟨0, by simp⟩, low_eq_s h hj s⟩ := dif_neg hj
    rw [e]
    exact congrArg Part.some (etg_neg (h := h) hj x).symm

lemma op_idm {j k : Fin (n + 1)} (h : j < k) {s : S} (u : DE n M (j, s)) :
    (DE n M).op (.idm h s) (Extended.arg₁ u) = Part.some (eidm M h u) := by
  refine (discExt Sig n m).derived_op_eq_some EEq.holdsAll_empty ?_ _
  by_cases hj : j.val < m
  · have e : (discExt Sig n m).op (.idm h s) =
        app₁ (.idm (lowE_lt h hj) s) (.var ⟨⟨0, by simp⟩, rfl⟩) := dif_pos hj
    rw [e]
    exact (Unif.meval_idm _ rfl).trans (congrArg Part.some (eidm_pos (h := h) hj u).symm)
  · have e : (discExt Sig n m).op (.idm h s) =
        .var ⟨⟨0, by simp⟩, (low_eq_s h hj s).symm⟩ := dif_neg hj
    rw [e]
    exact congrArg Part.some (eidm_neg (h := h) hj u).symm

lemma eval_var_lift (k : Fin (n + 1)) {ws : List S} (b : ∀ p, DE n M (k, ws.get p))
    (q : Fin (ws.map fun t => (lowE m k, t)).length) (hq) :
    (Term.var ⟨Fin.cast (by simp) q, hq⟩ :
        Term (Extended.ExtendedSignature Sig (Fin (m + 1)))
          (Vars ((fun t => (lowE m t.1, t.2)) ∘ (ws.map fun t => (k, t)).get))
          ((ws.map fun t => (lowE m k, t)).get q)).eval M.1
      (famVal fun i => (Extended.liftFam k b i).1) =
      Part.some (Extended.liftFam (lowE m k) (fun p => (b p).1) q) := by
  have key : ∀ {t' : Fin (n + 1) × S} (e : (k, ws.get (Fin.cast (by simp) q)) = t')
      {u' : Fin (m + 1) × S} (hq : (lowE m t'.1, t'.2) = u')
      (e' : (lowE m k, ws.get (Fin.cast (by simp) q)) = u'),
      hq ▸ (cast (congrArg (DE n M) e) (b (Fin.cast (by simp) q))).1 =
        cast (congrArg M.1 e') (b (Fin.cast (by simp) q)).1 := by
    intro t' e; subst e; intro u' hq; subst hq; intro e'; rfl
  exact congrArg Part.some (key (by simp) hq (by simp))

lemma op_op (k : Fin (n + 1)) {ws : List S} {s : S} (σ : Sig ws s)
    (b : ∀ p, DE n M (k, ws.get p)) :
    (DE n M).op (.op k σ) (Extended.liftFam k b) = Part.some (eop M k σ b) :=
  (discExt Sig n m).derived_op_eq_some EEq.holdsAll_empty
    ((eval_app_of_eq_some _ _ _ fun q => eval_var_lift k b q _).trans (Part.some_get _).symm) _

lemma comp_defn_iff {j k : Fin (n + 1)} (h : j < k) {s : S} (x y : DE n M (k, s)) :
    EEq.HoldsAll (DE n M) (famVal (Extended.arg₂ x y))
      ((extendedEpSig Sig (Fin (n + 1))).defn (.comp h s)) ↔ esc M h x = etg M h y :=
  EEq.holdsAll_singleton.trans (EEq.holds_mk'_iff ((Extended.eval_app₁ _ rfl).trans (op_sc h x))
    ((Extended.eval_app₁ _ rfl).trans (op_tg h y)))

lemma op_comp {j k : Fin (n + 1)} (h : j < k) {s : S} (x y : DE n M (k, s))
    (hxy : esc M h x = etg M h y) :
    (DE n M).op (.comp h s) (Extended.arg₂ x y) = Part.some (ecomp M h x y hxy) := by
  refine (discExt Sig n m).derived_op_eq_some ((comp_defn_iff h x y).mpr hxy) ?_ _
  by_cases hj : j.val < m
  · have e : (discExt Sig n m).op (.comp h s) = app₂ (.comp (lowE_lt h hj) s)
        (.var ⟨⟨0, by simp⟩, rfl⟩) (.var ⟨⟨1, by simp⟩, rfl⟩) := dif_pos hj
    rw [e]
    exact (Unif.meval_comp _ rfl rfl ((cond_pos (h := h) hj).mp hxy)).trans
      (congrArg Part.some (ecomp_pos (h := h) hj x y hxy).symm)
  · have e : (discExt Sig n m).op (.comp h s) = .var ⟨⟨0, by simp⟩, rfl⟩ := dif_neg hj
    rw [e]
    exact congrArg Part.some (congrArg Subtype.val (ecomp_neg (h := h) hj x y hxy)).symm

lemma op_comp_dom {j k : Fin (n + 1)} (h : j < k) {s : S} (x y : DE n M (k, s)) :
    ((DE n M).op (.comp h s) (Extended.arg₂ x y)).Dom ↔ esc M h x = etg M h y :=
  ⟨fun hd => (comp_defn_iff h x y).mp (((discExt Sig n m).op_derived_dom_iff _ _).mp hd).1,
    fun hxy => (Part.eq_some_iff.mp (op_comp h x y hxy)).1⟩

theorem isAlgebra : (extendedEpSig Sig (Fin (n + 1))).IsAlgebra (DE n M) := by
  intro ws t σ a
  cases σ with
  | op k σ =>
    obtain ⟨b, rfl⟩ : ∃ b, Extended.liftFam k b = a := ⟨_, Extended.liftFam_unlift k a⟩
    exact ⟨fun _ => EEq.holdsAll_empty, fun _ => (Part.eq_some_iff.mp (op_op k σ b)).1⟩
  | sc h s =>
    have ha : Extended.arg₁ (a ⟨0, by simp⟩) = a := by funext i; match i with | ⟨0, _⟩ => rfl
    exact ⟨fun _ => EEq.holdsAll_empty, fun _ => ha ▸ (Part.eq_some_iff.mp (op_sc h _)).1⟩
  | tg h s =>
    have ha : Extended.arg₁ (a ⟨0, by simp⟩) = a := by funext i; match i with | ⟨0, _⟩ => rfl
    exact ⟨fun _ => EEq.holdsAll_empty, fun _ => ha ▸ (Part.eq_some_iff.mp (op_tg h _)).1⟩
  | idm h s =>
    have ha : Extended.arg₁ (a ⟨0, by simp⟩) = a := by funext i; match i with | ⟨0, _⟩ => rfl
    exact ⟨fun _ => EEq.holdsAll_empty, fun _ => ha ▸ (Part.eq_some_iff.mp (op_idm h _)).1⟩
  | comp h s =>
    have ha : Extended.arg₂ (a ⟨0, by simp⟩) (a ⟨1, by simp⟩) = a := by
      funext i; match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl
    exact ha ▸ (op_comp_dom h _ _).trans (comp_defn_iff h _ _).symm

/-! ### Transports commute with the operations of the model -/

section Transport

variable {s : S}

lemma tp_sc {a b b' : Fin (m + 1)} (e : (b, s) = (b', s)) (h : a < b) (h' : a < b')
    (x : M.1 (b, s)) : sc M h' (tp M e x) = sc M h x := by
  have hb : b = b' := congrArg Prod.fst e
  subst hb; rfl

lemma tp_tg {a b b' : Fin (m + 1)} (e : (b, s) = (b', s)) (h : a < b) (h' : a < b')
    (x : M.1 (b, s)) : tg M h' (tp M e x) = tg M h x := by
  have hb : b = b' := congrArg Prod.fst e
  subst hb; rfl

lemma tp_idm {a b b' : Fin (m + 1)} (e : (b, s) = (b', s)) (h : a < b) (h' : a < b')
    (u : M.1 (a, s)) : tp M e (idm M h u) = idm M h' u := by
  have hb : b = b' := congrArg Prod.fst e
  subst hb; rfl

lemma tp_comp {a b b' : Fin (m + 1)} (e : (b, s) = (b', s)) (h : a < b) (h' : a < b')
    (x y : M.1 (b, s)) (hxy : sc M h x = tg M h y) :
    tp M e (comp M h x y hxy) = comp M h' (tp M e x) (tp M e y)
      ((tp_sc e h h' x).trans (hxy.trans (tp_tg e h h' y).symm)) := by
  have hb : b = b' := congrArg Prod.fst e
  subst hb; rfl

lemma tp_op {a a' : Fin (m + 1)} (ha : a = a') {ws : List S} (σ : Sig ws s)
    (e : (a, s) = (a', s)) (b : ∀ p, M.1 (a, ws.get p)) :
    tp M e (op M a σ b) = op M a' σ (fun p => tp M (congrArg (·, ws.get p) ha) (b p)) := by
  subst ha; rfl

lemma tp_trans {t t' : Fin (m + 1) × S} (e e' : t = t') (y : M.1 t) : tp M e y = tp M e' y := rfl

end Transport

/-! ### The laws of the extended discretized algebra -/

section Laws

variable {j k : Fin (n + 1)} {h : j < k} {s : S}

lemma esc_eidm (u : DE n M (j, s)) : esc M h (eidm M h u) = u := by
  apply Subtype.ext
  by_cases hj : j.val < m
  · rw [esc_pos (h := h) hj, eidm_pos (h := h) hj]; exact sc_idm _
  · rw [esc_neg (h := h) hj, eidm_neg (h := h) hj]; exact tp_tp _ _ _

lemma etg_eidm (u : DE n M (j, s)) : etg M h (eidm M h u) = u := by
  apply Subtype.ext
  by_cases hj : j.val < m
  · rw [etg_pos (h := h) hj, eidm_pos (h := h) hj]; exact tg_idm _
  · rw [etg_neg (h := h) hj, eidm_neg (h := h) hj]; exact tp_tp _ _ _

lemma esc_ecomp {x y : DE n M (k, s)} (hxy : esc M h x = etg M h y) :
    esc M h (ecomp M h x y hxy) = esc M h y := by
  by_cases hj : j.val < m
  · apply Subtype.ext; rw [esc_pos (h := h) hj, ecomp_pos (h := h) hj, esc_pos (h := h) hj]; exact sc_comp _
  · rw [ecomp_neg (h := h) hj]; rw [(cond_neg (h := h) hj).mp hxy]

lemma etg_ecomp {x y : DE n M (k, s)} (hxy : esc M h x = etg M h y) :
    etg M h (ecomp M h x y hxy) = etg M h x := by
  by_cases hj : j.val < m
  · apply Subtype.ext; rw [etg_pos (h := h) hj, ecomp_pos (h := h) hj, etg_pos (h := h) hj]; exact tg_comp _
  · rw [ecomp_neg (h := h) hj]

lemma ecomp_eidm_esc (x : DE n M (k, s)) :
    ecomp M h x (eidm M h (esc M h x)) (etg_eidm _).symm = x := by
  by_cases hj : j.val < m
  · exact Subtype.ext ((ecomp_pos (h := h) hj _ _ _).trans ((comp_congr rfl
      ((eidm_pos (h := h) hj _).trans (congrArg _ (esc_pos (h := h) hj x))) _
      (tg_idm _).symm).trans (comp_idm_sc x.1)))
  · exact ecomp_neg (h := h) hj _ _ _

lemma ecomp_eidm_etg (x : DE n M (k, s)) :
    ecomp M h (eidm M h (etg M h x)) x (esc_eidm _) = x := by
  by_cases hj : j.val < m
  · exact Subtype.ext ((ecomp_pos (h := h) hj _ _ _).trans ((comp_congr
      ((eidm_pos (h := h) hj _).trans (congrArg _ (etg_pos (h := h) hj x))) rfl _
      (sc_idm _)).trans (idm_tg_comp x.1)))
  · exact (ecomp_neg (h := h) hj _ _ _).trans (Subtype.ext ((eidm_neg (h := h) hj _).trans
      ((congrArg _ (etg_neg (h := h) hj x)).trans (tp_tp _ _ _))))

lemma ecomp_assoc {a b c : DE n M (k, s)} (hab : esc M h a = etg M h b)
    (hbc : esc M h b = etg M h c) :
    ecomp M h (ecomp M h a b hab) c ((esc_ecomp hab).trans hbc) =
      ecomp M h a (ecomp M h b c hbc) (hab.trans (etg_ecomp hbc).symm) := by
  by_cases hj : j.val < m
  · have ha' := (cond_pos (h := h) hj).mp hab
    have hb' := (cond_pos (h := h) hj).mp hbc
    exact Subtype.ext ((ecomp_pos (h := h) hj _ _ _).trans
      ((comp_congr (ecomp_pos (h := h) hj a b hab) rfl _ ((sc_comp ha').trans hb')).trans
        ((comp_assoc ha' hb').trans
          ((comp_congr rfl (ecomp_pos (h := h) hj b c hbc).symm (ha'.trans (tg_comp hb').symm)
            _).trans (ecomp_pos (h := h) hj _ _ _).symm))))
  · simp only [ecomp_neg (h := h) hj]

lemma ecomp_congr {x x' y y' : DE n M (k, s)} (hx : x = x') (hy : y = y')
    (hxy : esc M h x = etg M h y) (hxy' : esc M h x' = etg M h y') :
    ecomp M h x y hxy = ecomp M h x' y' hxy' := by
  subst hx hy; rfl

lemma esc_eop {ws : List S} (σ : Sig ws s) (b : ∀ p, DE n M (k, ws.get p)) :
    esc M h (eop M k σ b) = eop M j σ (fun p => esc M h (b p)) := by
  apply Subtype.ext
  by_cases hj : j.val < m
  · rw [esc_pos (h := h) hj]
    exact (sc_op _ σ _).trans (congrArg (op M _ σ) (funext fun p => (esc_pos (h := h) hj (b p)).symm))
  · rw [esc_neg (h := h) hj]
    exact (tp_op (lowE_eq h hj) σ _ _).trans
      (congrArg (op M _ σ) (funext fun p => (esc_neg (h := h) hj (b p)).symm))

lemma etg_eop {ws : List S} (σ : Sig ws s) (b : ∀ p, DE n M (k, ws.get p)) :
    etg M h (eop M k σ b) = eop M j σ (fun p => etg M h (b p)) := by
  apply Subtype.ext
  by_cases hj : j.val < m
  · rw [etg_pos (h := h) hj]
    exact (tg_op _ σ _).trans (congrArg (op M _ σ) (funext fun p => (etg_pos (h := h) hj (b p)).symm))
  · rw [etg_neg (h := h) hj]
    exact (tp_op (lowE_eq h hj) σ _ _).trans
      (congrArg (op M _ σ) (funext fun p => (etg_neg (h := h) hj (b p)).symm))

lemma eidm_eop {ws : List S} (σ : Sig ws s) (u : ∀ p, DE n M (j, ws.get p)) :
    eidm M h (eop M j σ u) = eop M k σ (fun p => eidm M h (u p)) := by
  apply Subtype.ext
  by_cases hj : j.val < m
  · rw [eidm_pos (h := h) hj]
    exact (idm_op _ σ _).trans (congrArg (op M _ σ) (funext fun p => (eidm_pos (h := h) hj (u p)).symm))
  · rw [eidm_neg (h := h) hj]
    exact (tp_op (lowE_eq h hj).symm σ _ _).trans
      (congrArg (op M _ σ) (funext fun p => (eidm_neg (h := h) hj (u p)).symm))

lemma eop_ecomp {ws : List S} (σ : Sig ws s) (a b : ∀ p, DE n M (k, ws.get p))
    (hab : ∀ p, esc M h (a p) = etg M h (b p)) :
    eop M k σ (fun p => ecomp M h (a p) (b p) (hab p)) =
      ecomp M h (eop M k σ a) (eop M k σ b)
        ((esc_eop σ a).trans ((congrArg (eop M j σ) (funext hab)).trans (etg_eop σ b).symm)) := by
  by_cases hj : j.val < m
  · refine Subtype.ext (Eq.trans ?_ (ecomp_pos (h := h) hj _ _ _).symm)
    refine (congrArg (op M _ σ) (funext fun p => ecomp_pos (h := h) hj (a p) (b p) (hab p))).trans ?_
    exact Extended.Model.op_comp _ σ _ _ _
  · simp only [ecomp_neg (h := h) hj]

end Laws

section Laws₃

variable {a b c : Fin (n + 1)} (h₁ : a < b) (h₂ : b < c) {s : S}

include h₁ in
lemma lt_a (hb : b.val < m) : a.val < m := lt_trans (Fin.lt_def.mp h₁) hb

lemma esc_esc (x : DE n M (c, s)) : esc M h₁ (esc M h₂ x) = esc M (h₁.trans h₂) x := by
  apply Subtype.ext
  by_cases hb : b.val < m
  · have ha := lt_a h₁ hb
    rw [esc_pos (h := h₁) ha, esc_pos (h := h₂) hb, esc_pos (h := h₁.trans h₂) ha]
    exact sc_sc (h₁ := lowE_lt h₁ ha) (h₂ := lowE_lt h₂ hb) _
  · by_cases ha : a.val < m
    · rw [esc_pos (h := h₁) ha, esc_neg (h := h₂) hb, esc_pos (h := h₁.trans h₂) ha]
      exact tp_sc _ _ _ _
    · rw [esc_neg (h := h₁) ha, esc_neg (h := h₂) hb, esc_neg (h := h₁.trans h₂) ha]
      exact tp_tp _ _ _

lemma etg_etg (x : DE n M (c, s)) : etg M h₁ (etg M h₂ x) = etg M (h₁.trans h₂) x := by
  apply Subtype.ext
  by_cases hb : b.val < m
  · have ha := lt_a h₁ hb
    rw [etg_pos (h := h₁) ha, etg_pos (h := h₂) hb, etg_pos (h := h₁.trans h₂) ha]
    exact tg_tg (h₁ := lowE_lt h₁ ha) (h₂ := lowE_lt h₂ hb) _
  · by_cases ha : a.val < m
    · rw [etg_pos (h := h₁) ha, etg_neg (h := h₂) hb, etg_pos (h := h₁.trans h₂) ha]
      exact tp_tg _ _ _ _
    · rw [etg_neg (h := h₁) ha, etg_neg (h := h₂) hb, etg_neg (h := h₁.trans h₂) ha]
      exact tp_tp _ _ _

lemma esc_etg (x : DE n M (c, s)) : esc M h₁ (etg M h₂ x) = esc M (h₁.trans h₂) x := by
  apply Subtype.ext
  by_cases hb : b.val < m
  · have ha := lt_a h₁ hb
    rw [esc_pos (h := h₁) ha, etg_pos (h := h₂) hb, esc_pos (h := h₁.trans h₂) ha]
    exact sc_tg (h₁ := lowE_lt h₁ ha) (h₂ := lowE_lt h₂ hb) _
  · by_cases ha : a.val < m
    · rw [esc_pos (h := h₁) ha, etg_neg (h := h₂) hb, esc_pos (h := h₁.trans h₂) ha]
      exact tp_sc _ _ _ _
    · rw [esc_neg (h := h₁) ha, etg_neg (h := h₂) hb, esc_neg (h := h₁.trans h₂) ha]
      exact tp_tp _ _ _

lemma etg_esc (x : DE n M (c, s)) : etg M h₁ (esc M h₂ x) = etg M (h₁.trans h₂) x := by
  apply Subtype.ext
  by_cases hb : b.val < m
  · have ha := lt_a h₁ hb
    rw [etg_pos (h := h₁) ha, esc_pos (h := h₂) hb, etg_pos (h := h₁.trans h₂) ha]
    exact tg_sc (h₁ := lowE_lt h₁ ha) (h₂ := lowE_lt h₂ hb) _
  · by_cases ha : a.val < m
    · rw [etg_pos (h := h₁) ha, esc_neg (h := h₂) hb, etg_pos (h := h₁.trans h₂) ha]
      exact tp_tg _ _ _ _
    · rw [etg_neg (h := h₁) ha, esc_neg (h := h₂) hb, etg_neg (h := h₁.trans h₂) ha]
      exact tp_tp _ _ _

lemma eidm_eidm (u : DE n M (a, s)) : eidm M h₂ (eidm M h₁ u) = eidm M (h₁.trans h₂) u := by
  apply Subtype.ext
  by_cases hb : b.val < m
  · have ha := lt_a h₁ hb
    rw [eidm_pos (h := h₂) hb, eidm_pos (h := h₁) ha, eidm_pos (h := h₁.trans h₂) ha]
    exact idm_idm (h₁ := lowE_lt h₁ ha) (h₂ := lowE_lt h₂ hb) _
  · by_cases ha : a.val < m
    · rw [eidm_neg (h := h₂) hb, eidm_pos (h := h₁) ha, eidm_pos (h := h₁.trans h₂) ha]
      exact tp_idm _ _ _ _
    · rw [eidm_neg (h := h₂) hb, eidm_neg (h := h₁) ha, eidm_neg (h := h₁.trans h₂) ha]
      exact tp_tp _ _ _

lemma esc_ecomp' {x y : DE n M (c, s)} (hxy : esc M (h₁.trans h₂) x = etg M (h₁.trans h₂) y) :
    esc M h₂ (ecomp M (h₁.trans h₂) x y hxy) =
      ecomp M h₁ (esc M h₂ x) (esc M h₂ y)
        ((esc_esc h₁ h₂ x).trans (hxy.trans (etg_esc h₁ h₂ y).symm)) := by
  by_cases hb : b.val < m
  · have ha := lt_a h₁ hb
    have hxy' := (cond_pos (h := h₁.trans h₂) ha).mp hxy
    exact Subtype.ext ((esc_pos (h := h₂) hb _).trans
      ((congrArg _ (ecomp_pos (h := h₁.trans h₂) ha x y hxy)).trans
        ((sc_comp' (h₁ := lowE_lt h₁ ha) (h₂ := lowE_lt h₂ hb) hxy').trans
          ((comp_congr (esc_pos (h := h₂) hb x).symm (esc_pos (h := h₂) hb y).symm _ _).trans
            (ecomp_pos (h := h₁) ha _ _ _).symm))))
  · by_cases ha : a.val < m
    · have hxy' := (cond_pos (h := h₁.trans h₂) ha).mp hxy
      exact Subtype.ext ((esc_neg (h := h₂) hb _).trans
        ((congrArg _ (ecomp_pos (h := h₁.trans h₂) ha x y hxy)).trans
          ((tp_comp _ _ (lowE_lt h₁ ha) _ _ hxy').trans
            ((comp_congr (esc_neg (h := h₂) hb x).symm (esc_neg (h := h₂) hb y).symm _ _).trans
              (ecomp_pos (h := h₁) ha _ _ _).symm))))
    · simp only [ecomp_neg (h := h₁.trans h₂) ha, ecomp_neg (h := h₁) ha]

lemma etg_ecomp' {x y : DE n M (c, s)} (hxy : esc M (h₁.trans h₂) x = etg M (h₁.trans h₂) y) :
    etg M h₂ (ecomp M (h₁.trans h₂) x y hxy) =
      ecomp M h₁ (etg M h₂ x) (etg M h₂ y)
        ((esc_etg h₁ h₂ x).trans (hxy.trans (etg_etg h₁ h₂ y).symm)) := by
  by_cases hb : b.val < m
  · have ha := lt_a h₁ hb
    have hxy' := (cond_pos (h := h₁.trans h₂) ha).mp hxy
    exact Subtype.ext ((etg_pos (h := h₂) hb _).trans
      ((congrArg _ (ecomp_pos (h := h₁.trans h₂) ha x y hxy)).trans
        ((tg_comp' (h₁ := lowE_lt h₁ ha) (h₂ := lowE_lt h₂ hb) hxy').trans
          ((comp_congr (etg_pos (h := h₂) hb x).symm (etg_pos (h := h₂) hb y).symm _ _).trans
            (ecomp_pos (h := h₁) ha _ _ _).symm))))
  · by_cases ha : a.val < m
    · have hxy' := (cond_pos (h := h₁.trans h₂) ha).mp hxy
      exact Subtype.ext ((etg_neg (h := h₂) hb _).trans
        ((congrArg _ (ecomp_pos (h := h₁.trans h₂) ha x y hxy)).trans
          ((tp_comp _ _ (lowE_lt h₁ ha) _ _ hxy').trans
            ((comp_congr (etg_neg (h := h₂) hb x).symm (etg_neg (h := h₂) hb y).symm _ _).trans
              (ecomp_pos (h := h₁) ha _ _ _).symm))))
    · simp only [ecomp_neg (h := h₁.trans h₂) ha, ecomp_neg (h := h₁) ha]

lemma esc_low_ecomp {x y : DE n M (c, s)} (hxy : esc M h₂ x = etg M h₂ y) :
    esc M (h₁.trans h₂) (ecomp M h₂ x y hxy) = esc M (h₁.trans h₂) y :=
  (esc_esc h₁ h₂ _).symm.trans ((congrArg _ (esc_ecomp hxy)).trans (esc_esc h₁ h₂ y))

lemma etg_low_ecomp {x y : DE n M (c, s)} (hxy : esc M h₂ x = etg M h₂ y) :
    etg M (h₁.trans h₂) (ecomp M h₂ x y hxy) = etg M (h₁.trans h₂) x :=
  (etg_etg h₁ h₂ _).symm.trans ((congrArg _ (etg_ecomp hxy)).trans (etg_etg h₁ h₂ x))

lemma esc_eq_of {x y : DE n M (c, s)} (hxy : esc M h₂ x = etg M h₂ y) :
    esc M (h₁.trans h₂) x = esc M (h₁.trans h₂) y :=
  (esc_esc h₁ h₂ x).symm.trans ((congrArg _ hxy).trans (esc_etg h₁ h₂ y))

lemma einterchange {x y z t : DE n M (c, s)} (hxy : esc M h₂ x = etg M h₂ y)
    (hzt : esc M h₂ z = etg M h₂ t) (hxz : esc M (h₁.trans h₂) x = etg M (h₁.trans h₂) z)
    (hyt : esc M (h₁.trans h₂) y = etg M (h₁.trans h₂) t) :
    ecomp M (h₁.trans h₂) (ecomp M h₂ x y hxy) (ecomp M h₂ z t hzt)
        ((esc_low_ecomp h₁ h₂ hxy).trans ((esc_eq_of h₁ h₂ hxy).symm.trans
          (hxz.trans (etg_low_ecomp h₁ h₂ hzt).symm))) =
      ecomp M h₂ (ecomp M (h₁.trans h₂) x z hxz) (ecomp M (h₁.trans h₂) y t hyt)
        ((esc_ecomp' h₁ h₂ hxz).trans ((ecomp_congr hxy hzt _ _).trans
          (etg_ecomp' h₁ h₂ hyt).symm)) := by
  by_cases hb : b.val < m
  · have ha := lt_a h₁ hb
    have hxy' := (cond_pos (h := h₂) hb).mp hxy
    have hzt' := (cond_pos (h := h₂) hb).mp hzt
    have hxz' := (cond_pos (h := h₁.trans h₂) ha).mp hxz
    have hyt' := (cond_pos (h := h₁.trans h₂) ha).mp hyt
    exact Subtype.ext ((ecomp_pos (h := h₁.trans h₂) ha _ _ _).trans
      ((comp_congr (ecomp_pos (h := h₂) hb x y hxy) (ecomp_pos (h := h₂) hb z t hzt) _ _).trans
        ((interchange (h₁ := lowE_lt h₁ ha) (h₂ := lowE_lt h₂ hb) hxy' hzt' hxz' hyt').trans
          ((comp_congr (ecomp_pos (h := h₁.trans h₂) ha x z hxz).symm
            (ecomp_pos (h := h₁.trans h₂) ha y t hyt).symm _ _).trans
            (ecomp_pos (h := h₂) hb _ _ _).symm))))
  · obtain rfl := (cond_neg (h := h₂) hb).mp hxy
    obtain rfl := (cond_neg (h := h₂) hb).mp hzt
    simp only [ecomp_neg (h := h₂) hb]

lemma esc_low_eidm (u : DE n M (b, s)) :
    esc M (h₁.trans h₂) (eidm M h₂ u) = esc M h₁ u :=
  (esc_esc h₁ h₂ _).symm.trans (congrArg _ (esc_eidm u))

lemma etg_low_eidm (u : DE n M (b, s)) :
    etg M (h₁.trans h₂) (eidm M h₂ u) = etg M h₁ u :=
  (etg_etg h₁ h₂ _).symm.trans (congrArg _ (etg_eidm u))

lemma eidm_ecomp {u v : DE n M (b, s)} (huv : esc M h₁ u = etg M h₁ v) :
    eidm M h₂ (ecomp M h₁ u v huv) =
      ecomp M (h₁.trans h₂) (eidm M h₂ u) (eidm M h₂ v)
        ((esc_low_eidm h₁ h₂ u).trans (huv.trans (etg_low_eidm h₁ h₂ v).symm)) := by
  by_cases hb : b.val < m
  · have ha := lt_a h₁ hb
    have huv' := (cond_pos (h := h₁) ha).mp huv
    exact Subtype.ext ((eidm_pos (h := h₂) hb _).trans
      ((congrArg _ (ecomp_pos (h := h₁) ha u v huv)).trans
        ((idm_comp (h₁ := lowE_lt h₁ ha) (h₂ := lowE_lt h₂ hb) huv').trans
          ((comp_congr (eidm_pos (h := h₂) hb u).symm (eidm_pos (h := h₂) hb v).symm _ _).trans
            (ecomp_pos (h := h₁.trans h₂) ha _ _ _).symm))))
  · by_cases ha : a.val < m
    · have huv' := (cond_pos (h := h₁) ha).mp huv
      exact Subtype.ext ((eidm_neg (h := h₂) hb _).trans
        ((congrArg _ (ecomp_pos (h := h₁) ha u v huv)).trans
          ((tp_comp _ _ (lowE_lt (h₁.trans h₂) ha) _ _ huv').trans
            ((comp_congr (eidm_neg (h := h₂) hb u).symm (eidm_neg (h := h₂) hb v).symm _ _).trans
              (ecomp_pos (h := h₁.trans h₂) ha _ _ _).symm))))
    · obtain rfl := (cond_neg (h := h₁) ha).mp huv
      simp only [ecomp_neg (h := h₁) ha, ecomp_neg (h := h₁.trans h₂) ha]

end Laws₃

section Eval

variable {val : ∀ t, Extended.EVar S (Fin (n + 1)) t → Part ((DE n M) t)}

lemma ev_scT {j k : Fin (n + 1)} (h : j < k) {s : S} {t : Extended.ETerm Sig (Fin (n + 1)) (k, s)}
    {x : DE n M (k, s)} (ht : t.eval (DE n M) val = Part.some x) :
    (Extended.ETerm.scT h t).eval (DE n M) val = Part.some (esc M h x) :=
  (Extended.eval_app₁ _ ht).trans (op_sc h x)

lemma ev_tgT {j k : Fin (n + 1)} (h : j < k) {s : S} {t : Extended.ETerm Sig (Fin (n + 1)) (k, s)}
    {x : DE n M (k, s)} (ht : t.eval (DE n M) val = Part.some x) :
    (Extended.ETerm.tgT h t).eval (DE n M) val = Part.some (etg M h x) :=
  (Extended.eval_app₁ _ ht).trans (op_tg h x)

lemma ev_idmT {j k : Fin (n + 1)} (h : j < k) {s : S}
    {t : Extended.ETerm Sig (Fin (n + 1)) (j, s)} {u : DE n M (j, s)}
    (ht : t.eval (DE n M) val = Part.some u) :
    (Extended.ETerm.idmT h t).eval (DE n M) val = Part.some (eidm M h u) :=
  (Extended.eval_app₁ _ ht).trans (op_idm h u)

lemma ev_compT {j k : Fin (n + 1)} (h : j < k) {s : S}
    {t t' : Extended.ETerm Sig (Fin (n + 1)) (k, s)} {x y : DE n M (k, s)}
    (ht : t.eval (DE n M) val = Part.some x) (ht' : t'.eval (DE n M) val = Part.some y)
    (hxy : esc M h x = etg M h y) :
    (Extended.ETerm.compT h t t').eval (DE n M) val = Part.some (ecomp M h x y hxy) :=
  (Extended.eval_app₂ _ ht ht').trans (op_comp h x y hxy)

lemma ev_compT_dom {j k : Fin (n + 1)} (h : j < k) {s : S}
    {t t' : Extended.ETerm Sig (Fin (n + 1)) (k, s)} {x y : DE n M (k, s)}
    (ht : t.eval (DE n M) val = Part.some x) (ht' : t'.eval (DE n M) val = Part.some y)
    (hd : ((Extended.ETerm.compT h t t').eval (DE n M) val).Dom) : esc M h x = etg M h y :=
  (op_comp_dom h x y).mp ((Extended.eval_app₂ _ ht ht') ▸ hd)

lemma ev_opT (k : Fin (n + 1)) {ws : List S} {s : S} (σ : Sig ws s)
    {ts : (p : Fin ws.length) → Extended.ETerm Sig (Fin (n + 1)) (k, ws.get p)}
    {b : ∀ p, DE n M (k, ws.get p)} (h : ∀ p, (ts p).eval (DE n M) val = Part.some (b p)) :
    (Extended.ETerm.opT k σ ts).eval (DE n M) val = Part.some (eop M k σ b) :=
  (Extended.eval_opT k σ h).trans (op_op k σ b)

end Eval

/-- The variables of an axiom. -/
local macro "vm" : tactic => `(tactic| (
  simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, Extended.ETerm.scT, Extended.ETerm.tgT,
    Extended.ETerm.idmT, Extended.ETerm.compT, Extended.ETerm.x, Extended.vars_opT]))

/-- A premise of an axiom. -/
local macro "pm" : tactic => `(tactic| (
  first
    | exact List.Mem.head _
    | exact List.Mem.tail _ (List.Mem.head _)
    | exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    | exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

open Extended.ETerm in
theorem holds : ∀ q ∈ Extended.extendedSpec Sig (Fin (n + 1)), q.Holds (DE n M) := by
  intro q hq val hvars hprem
  have var : ∀ {t : Fin (n + 1) × S} (i : ℕ),
      (⟨t, i⟩ : Σ t, Extended.EVar S (Fin (n + 1)) t) ∈ q.vars →
      ∃ x, (Extended.ETerm.x (Sig := Sig) (t := t) i).eval (DE n M) val = Part.some x :=
    fun i hi => ⟨_, (Part.some_get (hvars _ hi)).symm⟩
  have prem : ∀ e ∈ q.premises, e.Holds (DE n M) val := hprem
  cases hq with
  | @EA0 k ws s σ xs =>
    choose b hb using fun p => var (t := (k, ws.get p)) (xs p) (by vm; exact ⟨p, rfl, rfl⟩)
    exact EEq.holds_defined_iff.mpr (Part.eq_some_iff.mp (ev_opT k σ hb)).1
  | @EA1_sc j k h s i =>
    obtain ⟨a, ha⟩ := var (t := (k, s)) i (by vm)
    exact EEq.holds_defined_iff.mpr (Part.eq_some_iff.mp (ev_scT h ha)).1
  | @EA1_tg j k h s i =>
    obtain ⟨a, ha⟩ := var (t := (k, s)) i (by vm)
    exact EEq.holds_defined_iff.mpr (Part.eq_some_iff.mp (ev_tgT h ha)).1
  | @EA1_idm j k h s i =>
    obtain ⟨a, ha⟩ := var (t := (j, s)) i (by vm)
    exact EEq.holds_defined_iff.mpr (Part.eq_some_iff.mp (ev_idmT h ha)).1
  | @EA2_sc j k h s i =>
    obtain ⟨u, hu⟩ := var (t := (j, s)) i (by vm)
    exact (EEq.holds_mk'_iff (ev_scT h (ev_idmT h hu)) hu).mpr (esc_eidm u)
  | @EA2_tg j k h s i =>
    obtain ⟨u, hu⟩ := var (t := (j, s)) i (by vm)
    exact (EEq.holds_mk'_iff (ev_tgT h (ev_idmT h hu)) hu).mpr (etg_eidm u)
  | @EA3_dom j k h s i i' =>
    obtain ⟨a, ha⟩ := var (t := (k, s)) i (by vm)
    obtain ⟨b, hb⟩ := var (t := (k, s)) i' (by vm)
    exact (EEq.holds_mk'_iff (ev_scT h ha) (ev_tgT h hb)).mpr
      (ev_compT_dom h ha hb (EEq.holds_defined_iff.mp (prem _ (by pm))))
  | @EA3_def j k h s i i' =>
    obtain ⟨a, ha⟩ := var (t := (k, s)) i (by vm)
    obtain ⟨b, hb⟩ := var (t := (k, s)) i' (by vm)
    have hab := (EEq.holds_mk'_iff (ev_scT h ha) (ev_tgT h hb)).mp (prem _ (by pm))
    exact EEq.holds_defined_iff.mpr (Part.eq_some_iff.mp (ev_compT h ha hb hab)).1
  | @EA4_sc j k h s i i' =>
    obtain ⟨a, ha⟩ := var (t := (k, s)) i (by vm)
    obtain ⟨b, hb⟩ := var (t := (k, s)) i' (by vm)
    have hab := ev_compT_dom h ha hb (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_scT h (ev_compT h ha hb hab)) (ev_scT h hb)).mpr (esc_ecomp hab)
  | @EA4_tg j k h s i i' =>
    obtain ⟨a, ha⟩ := var (t := (k, s)) i (by vm)
    obtain ⟨b, hb⟩ := var (t := (k, s)) i' (by vm)
    have hab := ev_compT_dom h ha hb (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_tgT h (ev_compT h ha hb hab)) (ev_tgT h ha)).mpr (etg_ecomp hab)
  | @EA5_sc j k h s i =>
    obtain ⟨a, ha⟩ := var (t := (k, s)) i (by vm)
    exact (EEq.holds_mk'_iff (ev_compT h ha (ev_idmT h (ev_scT h ha)) (etg_eidm _).symm) ha).mpr
      (ecomp_eidm_esc a)
  | @EA5_tg j k h s i =>
    obtain ⟨a, ha⟩ := var (t := (k, s)) i (by vm)
    exact (EEq.holds_mk'_iff (ev_compT h (ev_idmT h (ev_tgT h ha)) ha (esc_eidm _)) ha).mpr
      (ecomp_eidm_etg a)
  | @EA6 j k h s i i' i'' =>
    obtain ⟨a, ha⟩ := var (t := (k, s)) i (by vm)
    obtain ⟨b, hb⟩ := var (t := (k, s)) i' (by vm)
    obtain ⟨c, hc⟩ := var (t := (k, s)) i'' (by vm)
    have hab := ev_compT_dom h ha hb (EEq.holds_defined_iff.mp (prem _ (by pm)))
    have hbc := ev_compT_dom h hb hc (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_compT h (ev_compT h ha hb hab) hc ((esc_ecomp hab).trans hbc))
      (ev_compT h ha (ev_compT h hb hc hbc) (hab.trans (etg_ecomp hbc).symm))).mpr
      (ecomp_assoc hab hbc)
  | @EA7_sc j k h ws s σ xs =>
    choose b hb using fun p => var (t := (k, ws.get p)) (xs p) (by vm; exact ⟨p, rfl, rfl⟩)
    exact (EEq.holds_mk'_iff (ev_scT h (ev_opT k σ hb)) (ev_opT j σ fun p => ev_scT h (hb p))).mpr
      (esc_eop σ b)
  | @EA7_tg j k h ws s σ xs =>
    choose b hb using fun p => var (t := (k, ws.get p)) (xs p) (by vm; exact ⟨p, rfl, rfl⟩)
    exact (EEq.holds_mk'_iff (ev_tgT h (ev_opT k σ hb)) (ev_opT j σ fun p => ev_tgT h (hb p))).mpr
      (etg_eop σ b)
  | @EA7_idm j k h ws s σ us =>
    choose b hb using fun p => var (t := (j, ws.get p)) (us p) (by vm; exact ⟨p, rfl, rfl⟩)
    exact (EEq.holds_mk'_iff (ev_idmT h (ev_opT j σ hb)) (ev_opT k σ fun p => ev_idmT h (hb p))).mpr
      (eidm_eop σ b)
  | @EA8 j k h ws s σ xs ys =>
    choose a ha using fun p => var (t := (k, ws.get p)) (xs p)
      (by vm; exact Or.inl (Or.inr (Or.inl ⟨p, rfl, rfl⟩)))
    choose b hb using fun p => var (t := (k, ws.get p)) (ys p)
      (by vm; exact Or.inl (Or.inr (Or.inr ⟨p, rfl, rfl⟩)))
    have hab : ∀ p, esc M h (a p) = etg M h (b p) := fun p =>
      ev_compT_dom h (ha p) (hb p) (EEq.holds_defined_iff.mp (prem _ (List.mem_ofFn.mpr ⟨p, rfl⟩)))
    exact (EEq.holds_mk'_iff (ev_opT k σ fun p => ev_compT h (ha p) (hb p) (hab p))
      (ev_compT h (ev_opT k σ ha) (ev_opT k σ hb)
        ((esc_eop σ a).trans ((congrArg (eop M j σ) (funext hab)).trans (etg_eop σ b).symm)))).mpr
      (eop_ecomp σ a b hab)
  | @EA1'_sc_sc a b c h₁ h₂ s i =>
    obtain ⟨x, hx⟩ := var (t := (c, s)) i (by vm)
    exact (EEq.holds_mk'_iff (ev_scT h₁ (ev_scT h₂ hx)) (ev_scT (h₁.trans h₂) hx)).mpr
      (esc_esc h₁ h₂ x)
  | @EA1'_tg_tg a b c h₁ h₂ s i =>
    obtain ⟨x, hx⟩ := var (t := (c, s)) i (by vm)
    exact (EEq.holds_mk'_iff (ev_tgT h₁ (ev_tgT h₂ hx)) (ev_tgT (h₁.trans h₂) hx)).mpr
      (etg_etg h₁ h₂ x)
  | @EA1'_sc_tg a b c h₁ h₂ s i =>
    obtain ⟨x, hx⟩ := var (t := (c, s)) i (by vm)
    exact (EEq.holds_mk'_iff (ev_scT h₁ (ev_tgT h₂ hx)) (ev_scT (h₁.trans h₂) hx)).mpr
      (esc_etg h₁ h₂ x)
  | @EA1'_tg_sc a b c h₁ h₂ s i =>
    obtain ⟨x, hx⟩ := var (t := (c, s)) i (by vm)
    exact (EEq.holds_mk'_iff (ev_tgT h₁ (ev_scT h₂ hx)) (ev_tgT (h₁.trans h₂) hx)).mpr
      (etg_esc h₁ h₂ x)
  | @EA2' a b c h₁ h₂ s i =>
    obtain ⟨u, hu⟩ := var (t := (a, s)) i (by vm)
    exact (EEq.holds_mk'_iff (ev_idmT h₂ (ev_idmT h₁ hu)) (ev_idmT (h₁.trans h₂) hu)).mpr
      (eidm_eidm h₁ h₂ u)
  | @EA3'_sc a b c h₁ h₂ s i i' =>
    obtain ⟨x, hx⟩ := var (t := (c, s)) i (by vm)
    obtain ⟨y, hy⟩ := var (t := (c, s)) i' (by vm)
    have hxy := ev_compT_dom (h₁.trans h₂) hx hy (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_scT h₂ (ev_compT (h₁.trans h₂) hx hy hxy))
      (ev_compT h₁ (ev_scT h₂ hx) (ev_scT h₂ hy) _)).mpr (esc_ecomp' h₁ h₂ hxy)
  | @EA3'_tg a b c h₁ h₂ s i i' =>
    obtain ⟨x, hx⟩ := var (t := (c, s)) i (by vm)
    obtain ⟨y, hy⟩ := var (t := (c, s)) i' (by vm)
    have hxy := ev_compT_dom (h₁.trans h₂) hx hy (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_tgT h₂ (ev_compT (h₁.trans h₂) hx hy hxy))
      (ev_compT h₁ (ev_tgT h₂ hx) (ev_tgT h₂ hy) _)).mpr (etg_ecomp' h₁ h₂ hxy)
  | @EA4' a b c h₁ h₂ s i i' p q =>
    obtain ⟨x, hx⟩ := var (t := (c, s)) i (by vm)
    obtain ⟨y, hy⟩ := var (t := (c, s)) i' (by vm)
    obtain ⟨z, hz⟩ := var (t := (c, s)) p (by vm)
    obtain ⟨t, ht⟩ := var (t := (c, s)) q (by vm)
    have hxy := ev_compT_dom h₂ hx hy (EEq.holds_defined_iff.mp (prem _ (by pm)))
    have hzt := ev_compT_dom h₂ hz ht (EEq.holds_defined_iff.mp (prem _ (by pm)))
    have hxz := ev_compT_dom (h₁.trans h₂) hx hz (EEq.holds_defined_iff.mp (prem _ (by pm)))
    have hyt := ev_compT_dom (h₁.trans h₂) hy ht (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff
      (ev_compT (h₁.trans h₂) (ev_compT h₂ hx hy hxy) (ev_compT h₂ hz ht hzt) _)
      (ev_compT h₂ (ev_compT (h₁.trans h₂) hx hz hxz) (ev_compT (h₁.trans h₂) hy ht hyt) _)).mpr
      (einterchange h₁ h₂ hxy hzt hxz hyt)
  | @EA5' a b c h₁ h₂ s i i' =>
    obtain ⟨u, hu⟩ := var (t := (b, s)) i (by vm)
    obtain ⟨v, hv⟩ := var (t := (b, s)) i' (by vm)
    have huv := ev_compT_dom h₁ hu hv (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_idmT h₂ (ev_compT h₁ hu hv huv))
      (ev_compT (h₁.trans h₂) (ev_idmT h₂ hu) (ev_idmT h₂ hv) _)).mpr (eidm_ecomp h₁ h₂ huv)

end DiscExt
```

:::proposition (label := "discretization-ext-models") (central := true) (title := "Extended discretization sends models to models")
$`(\boldsymbol{\delta}^{\mathrm{ext}(n,m)})^{\ast}_{\mathfrak{gd}}` sends the models of
$`(\mathbf{\Sigma}^{\mathrm{ext}(m)}, \mathcal{C}^{\Sigma^{\mathrm{ext}(m)}})` to models of
$`(\mathbf{\Sigma}^{\mathrm{ext}(n)}, \mathcal{C}^{\Sigma^{\mathrm{ext}(n)}})`.

```lean
theorem discExt_sendsModels :
    (discExt Sig n m).SendsModels.{u, max u v, u, max u v, w}
      (Extended.extendedSpec Sig (Fin (n + 1))) (Extended.extendedSpec Sig (Fin (m + 1))) :=
  fun B hB => ⟨DiscExt.isAlgebra (M := ⟨B, hB.2⟩), DiscExt.holds (M := ⟨B, hB.2⟩)⟩
```
:::

:::proof (of := "discretization-ext-models")
The operations without domain conditions are total, and two $`k`-cells satisfy the domain
condition of $`\circ^{(j,k)}_{s}` if and only if
$`\mathrm{sc}^{(j,\underline{k})}_{s}(x) = \mathrm{tg}^{(j,\underline{k})}_{s}(y)`, for $`j < m`, and if
and only if $`x = y`, for $`j \geq m`. The axioms in which all the dimensions are at most $`m` become
axioms of $`\mathcal{C}^{\Sigma^{\mathrm{ext}(m)}}`. For $`j < m < k`, (EA$`^{j,k}`1)–(EA$`^{j,k}`8)
become (EA$`^{j,m}`1)–(EA$`^{j,m}`8), and for $`m \leq j` they become trivial. For $`h < j < k`, the
axioms (EA$`^{h,j,k}`1)–(EA$`^{h,j,k}`5) become those of $`\mathcal{C}^{\Sigma^{\mathrm{ext}(m)}}` with
dimensions $`(h, \underline{j}, \underline{k})` when $`j < m`; when $`h < m \leq j` the operations with
lower dimension $`j` are transports and the axioms become the compatibility of the operations of
$`\mathbf{B}` with transports; and when $`m \leq h` they become trivial.
:::

:::definition (label := "discretization-ext-functor") (central := false) (title := "The extended discretization functor")
The *extended discretization functor* $`\mathrm{D}^{\mathrm{ext}(n,m)}` is the birestriction of
$`(\boldsymbol{\delta}^{\mathrm{ext}(n,m)})^{\ast}_{\mathfrak{gd}}` to the categories of models.

```lean
/-- The extended discretization functor `D^{ext(n,m)}`. -/
noncomputable def discExtFunctor :
    EpSpec.EpAlg.{u, max u v, w} (extendedEpSpec Sig (Fin (m + 1))) ⥤
      EpSpec.EpAlg.{u, max u v, w} (extendedEpSpec Sig (Fin (n + 1))) :=
  (discExt Sig n m).restrict (discExt_sendsModels Sig n m)
```
:::

# Discretization and truncation

The operations of the discretized and truncated algebras of models are those computed above.

```lean
namespace Disc

variable {Sig n m} {M : Compact.CompactPAlg.{u, v, w} Sig (Fin m)}

variable (n M) in
/-- The discretized algebra of a model, as a model of the compact specification. -/
noncomputable abbrev model : Compact.CompactPAlg.{u, v, w} Sig (Fin n) := ⟨D n M, holds⟩

lemma sc_eq (k : Fin n) {s : S} (x : D n M s) : Compact.msc (model n M) k x = dsc M k x :=
  Part.get_eq_of_mem (Part.eq_some_iff.mp (op_sc k x)) _

lemma tg_eq (k : Fin n) {s : S} (x : D n M s) : Compact.mtg (model n M) k x = dtg M k x :=
  Part.get_eq_of_mem (Part.eq_some_iff.mp (op_tg k x)) _

lemma op_eq {ws : List S} {s : S} (σ : Sig ws s) (a : Arity (D n M) ws) :
    Compact.mop (model n M) σ a = dop M σ a :=
  Part.get_eq_of_mem (Part.eq_some_iff.mp (op_op σ a)) _

lemma pcomp_eq (k : Fin n) {s : S} (x y : D n M s) :
    @Compact.CategoryStruct.pcomp _ _ (Compact.modelStruct (M := model n M) s) k x y =
      (D n M).op (.comp k s) (arityTwo x y) := by
  show (D n M).op _ _ = _
  congr 1; funext j; match j with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl

lemma comp_eq (k : Fin n) {s : S} (x y : D n M s) (hxy) (hxy') :
    @Compact.CategoryStruct.comp _ _ (Compact.modelStruct (M := model n M) s) k x y hxy =
      dcomp M k x y hxy' := by
  unfold Compact.CategoryStruct.comp
  exact Part.get_eq_of_mem (pcomp_eq k x y ▸ Part.eq_some_iff.mp (op_comp k x y hxy')) _

end Disc

namespace Trunc

variable {Sig n m} {hmn : m ≤ n} {M : Compact.CompactPAlg.{u, v, w} Sig (Fin n)}

variable (hmn M) in
noncomputable abbrev model : Compact.CompactPAlg.{u, v, w} Sig (Fin m) := ⟨T hmn M, holds⟩

lemma sc_eq (k : Fin m) {s : S} (x : T hmn M s) : Compact.msc (model hmn M) k x = tsc hmn M k x :=
  Part.get_eq_of_mem (Part.eq_some_iff.mp (op_sc k x)) _

lemma tg_eq (k : Fin m) {s : S} (x : T hmn M s) : Compact.mtg (model hmn M) k x = ttg hmn M k x :=
  Part.get_eq_of_mem (Part.eq_some_iff.mp (op_tg k x)) _

lemma op_eq {ws : List S} {s : S} (σ : Sig ws s) (a : Arity (T hmn M) ws) :
    Compact.mop (model hmn M) σ a = top hmn M σ a :=
  Part.get_eq_of_mem (Part.eq_some_iff.mp (op_op σ a)) _

lemma pcomp_eq (k : Fin m) {s : S} (x y : T hmn M s) :
    @Compact.CategoryStruct.pcomp _ _ (Compact.modelStruct (M := model hmn M) s) k x y =
      (T hmn M).op (.comp k s) (arityTwo x y) := by
  show (T hmn M).op _ _ = _
  congr 1; funext j; match j with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl

lemma comp_eq (k : Fin m) {s : S} (x y : T hmn M s) (hxy) (hxy') :
    @Compact.CategoryStruct.comp _ _ (Compact.modelStruct (M := model hmn M) s) k x y hxy =
      tcomp hmn M k x y hxy' := by
  unfold Compact.CategoryStruct.comp
  exact Part.get_eq_of_mem (pcomp_eq k x y ▸ Part.eq_some_iff.mp (op_comp k x y hxy')) _

end Trunc

section TruncDisc

variable {Sig n m} (hmn : m ≤ n)

/-- The cells of `T(D(𝐀))` are those of `𝐀`. -/
noncomputable def tdEquiv (A : EpSpec.EpAlg.{u, max u v, w} (compactEpSpec Sig (Fin m))) (s : S) :
    A.1 s ≃ ((discFunctor Sig n m ⋙ truncFunctor Sig hmn).obj A).1 s where
  toFun a := ⟨⟨a, EEq.holdsAll_empty⟩, Trunc.mem_of (M := Disc.model n ⟨A.1, A.2.2⟩) _
    (fun hm => disc_isCell Sig n m hm _)⟩
  invFun y := y.1.1
  left_inv _ := rfl
  right_inv _ := rfl

theorem tdEquiv_op (A : EpSpec.EpAlg.{u, max u v, w} (compactEpSpec Sig (Fin m)))
    {ws : List S} {s : S} (σ : (compactEpSpec Sig (Fin m)).sg.sig ws s) (a : Arity A.1 ws) :
    ((discFunctor Sig n m ⋙ truncFunctor Sig hmn).obj A).1.op σ (fun j => tdEquiv hmn A _ (a j)) =
      (A.1.op σ a).map (tdEquiv hmn A s) := by
  let Am : Compact.CompactPAlg.{u, v, w} Sig (Fin m) := ⟨A.1, A.2.2⟩
  cases σ with
  | op σ =>
    have h1 : A.1.op (.op σ) a = Part.some (Compact.mop Am σ a) := (Part.some_get _).symm
    refine Eq.trans ?_ ((congrArg (Part.map (tdEquiv hmn A s)) h1).trans (Part.map_some _ _)).symm
    exact (Trunc.op_op (M := Disc.model n Am) σ _).trans (congrArg Part.some (Subtype.ext
      ((Disc.op_eq (M := Am) σ _).trans (Subtype.ext rfl))))
  | sc k s =>
    have hk : (Fin.castLE hmn k).val < m := k.isLt
    have h1 : A.1.op (.sc k s) a = Part.some (Compact.msc Am k (a ⟨0, by simp⟩)) :=
      Compact.op_get_eq (M := Am) (by funext j; match j with | ⟨0, _⟩ => rfl) _
    refine Eq.trans ?_ ((congrArg (Part.map (tdEquiv hmn A s)) h1).trans (Part.map_some _ _)).symm
    refine ((congrArg _ (by funext j; match j with | ⟨0, _⟩ => rfl)).trans
      (Trunc.op_sc (M := Disc.model n Am) k (tdEquiv hmn A s (a ⟨0, by simp⟩)))).trans ?_
    exact congrArg Part.some (Subtype.ext ((Disc.sc_eq (M := Am) _ _).trans
      (Subtype.ext (Disc.dsc_lt hk _))))
  | tg k s =>
    have hk : (Fin.castLE hmn k).val < m := k.isLt
    have h1 : A.1.op (.tg k s) a = Part.some (Compact.mtg Am k (a ⟨0, by simp⟩)) :=
      Compact.op_get_eq (M := Am) (by funext j; match j with | ⟨0, _⟩ => rfl) _
    refine Eq.trans ?_ ((congrArg (Part.map (tdEquiv hmn A s)) h1).trans (Part.map_some _ _)).symm
    refine ((congrArg _ (by funext j; match j with | ⟨0, _⟩ => rfl)).trans
      (Trunc.op_tg (M := Disc.model n Am) k (tdEquiv hmn A s (a ⟨0, by simp⟩)))).trans ?_
    exact congrArg Part.some (Subtype.ext ((Disc.tg_eq (M := Am) _ _).trans
      (Subtype.ext (Disc.dtg_lt hk _))))
  | comp k s =>
    have hk : (Fin.castLE hmn k).val < m := k.isLt
    have ha : (fun j => tdEquiv hmn A _ (a j)) = arityTwo (tdEquiv hmn A s (a ⟨0, by simp⟩))
        (tdEquiv hmn A s (a ⟨1, by simp⟩)) := by
      funext j; match j with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl
    refine (congrArg _ ha).trans ?_
    by_cases hxy : Compact.msc Am k (a ⟨0, by simp⟩) = Compact.mtg Am k (a ⟨1, by simp⟩)
    · have hd : Disc.dsc Am (Fin.castLE hmn k) (tdEquiv hmn A s (a ⟨0, by simp⟩)).1 =
          Disc.dtg Am (Fin.castLE hmn k) (tdEquiv hmn A s (a ⟨1, by simp⟩)).1 :=
        (Disc.cond_lt hk).mpr hxy
      have hc : Compact.msc (Disc.model n Am) (Fin.castLE hmn k)
          (tdEquiv hmn A s (a ⟨0, by simp⟩)).1 =
          Compact.mtg (Disc.model n Am) (Fin.castLE hmn k) (tdEquiv hmn A s (a ⟨1, by simp⟩)).1 :=
        (Disc.sc_eq (M := Am) _ _).trans (hd.trans (Disc.tg_eq (M := Am) _ _).symm)
      have h1 : A.1.op (.comp k s) a =
          Part.some (Compact.CategoryStruct.comp (C := Am.1 s) k _ _ hxy) :=
        Compact.op_get_eq (M := Am) (by funext j; match j with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl) _
      rw [h1, Part.map_some]
      refine (Trunc.op_comp (M := Disc.model n Am) k _ _ hc).trans ?_
      exact congrArg Part.some (Subtype.ext ((Disc.comp_eq (M := Am) _ _ _ hc hd).trans
        (Subtype.ext (Disc.dcomp_lt hk _ _ hd))))
    · have h1 : A.1.op (.comp k s) a = Part.none := by
        refine Part.eq_none_iff'.mpr fun hd => hxy ?_
        have hd' : (@Compact.CategoryStruct.pcomp _ _ (Compact.modelStruct (M := Am) s) k
            (a ⟨0, by simp⟩) (a ⟨1, by simp⟩)).Dom := by
          show (Am.1.op _ _).Dom
          exact (op_dom_congr (by funext j; match j with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl)).mp hd
        exact Compact.CategoryStruct.pcomp_dom.mp hd'
      rw [h1, Part.map_none]
      refine Part.eq_none_iff'.mpr fun hd => hxy ?_
      have hc := (Trunc.op_comp_dom (M := Disc.model n Am) k _ _).mp hd
      exact (Disc.cond_lt hk).mp
        ((Disc.sc_eq (M := Am) _ _).symm.trans (hc.trans (Disc.tg_eq (M := Am) _ _)))

end TruncDisc
```

:::proposition (label := "truncation-discretization") (central := false) (title := "Truncation after discretization")
Let $`m \leq n`. $`T^{(m,n)} \circ \mathrm{D}^{(n,m)} \cong \mathrm{Id}`, by isomorphisms that send
every cell to itself. In the draft (Proposition `PTruncDisc`) this is an equality of functors, which
follows from $`\boldsymbol{\delta}^{(n,m)} \circ \boldsymbol{\tau}^{(m,n)} = \mathrm{id}`; here the
cells of $`T^{(m,n)}(\mathrm{D}^{(n,m)}(\mathbf{A}))` are those of $`\mathbf{A}` seen as elements of a
subset.

```lean
section TruncDisc

variable {Sig n m} (hmn : m ≤ n)

/-- `T ∘ D ≅ Id`, by isomorphisms that send every cell to itself. -/
noncomputable def tdIso :
    𝟭 (EpSpec.EpAlg.{u, max u v, w} (compactEpSpec Sig (Fin m))) ≅
      discFunctor Sig n m ⋙ truncFunctor Sig hmn :=
  NatIso.ofComponents (fun A => EpSpec.isoOfEquiv (tdEquiv hmn A) (tdEquiv_op hmn A))
    (fun _ => PartialAlgebra.Hom.ext fun _ _ => rfl)

end TruncDisc
```
:::

:::proof (of := "truncation-discretization")
Every cell of a discretized algebra is an $`m`-cell, so the cells of
$`T^{(m,n)}(\mathrm{D}^{(n,m)}(\mathbf{A}))` are those of $`\mathbf{A}`, and in the dimensions $`k < m`
the operations are those of $`\mathbf{A}`.
:::

```lean
section TruncDisc

variable {Sig n m} (hmn : m ≤ n)

lemma get_of_eq {α : Type*} {o : Part α} {c : α} (e : o = Part.some c) (h : o.Dom) : o.get h = c :=
  Part.get_eq_of_mem (Part.eq_some_iff.mp e) h

variable {hmn}

/-- An `m`-cell is a `k`-cell for every `k ≥ m`. -/
lemma cell_sc_ge {M : Compact.CompactPAlg.{u, v, w} Sig (Fin n)} {k : Fin n} (hk : ¬ k.val < m)
    {s : S} (x : Trunc.T hmn M s) : Compact.msc M k x.1 = x.1 := by
  have hm : m < n := lt_of_le_of_lt (not_lt.mp hk) k.isLt
  rcases (not_lt.mp hk).eq_or_lt with e | e
  · obtain rfl : k = ⟨m, hm⟩ := Fin.ext e.symm
    exact Trunc.isCell x hm
  · calc Compact.msc M k x.1 = Compact.msc M k (Compact.msc M ⟨m, hm⟩ x.1) :=
          congrArg _ (Trunc.isCell x hm).symm
      _ = Compact.msc M ⟨m, hm⟩ x.1 := Compact.model_sc_k_sc_l _ (Fin.lt_def.mpr e)
      _ = x.1 := Trunc.isCell x hm

lemma cell_tg_ge {M : Compact.CompactPAlg.{u, v, w} Sig (Fin n)} {k : Fin n} (hk : ¬ k.val < m)
    {s : S} (x : Trunc.T hmn M s) : Compact.mtg M k x.1 = x.1 :=
  (congrArg _ (cell_sc_ge hk x).symm).trans ((Compact.model_tg_sc _).trans (cell_sc_ge hk x))

variable (hmn) in
/-- The counit `D(T(𝐁)) → 𝐁`: the inclusion of the `m`-cells. -/
noncomputable def tdCounit (B : EpSpec.EpAlg.{u, max u v, w} (compactEpSpec Sig (Fin n))) :
    (truncFunctor Sig hmn ⋙ discFunctor Sig n m).obj B ⟶ B where
  map _ y := y.1.1
  map_dom σ a h := by
    let Bm : Compact.CompactPAlg.{u, v, w} Sig (Fin n) := ⟨B.1, B.2.2⟩
    cases σ with
    | op σ => exact Compact.op_dom (M := Bm) σ _
    | sc k s =>
      exact (op_dom_congr (by funext j; match j with | ⟨0, _⟩ => rfl)).mp
        (Compact.sc_dom (M := Bm) k (a ⟨0, by simp⟩).1.1)
    | tg k s =>
      exact (op_dom_congr (by funext j; match j with | ⟨0, _⟩ => rfl)).mp
        (Compact.tg_dom (M := Bm) k (a ⟨0, by simp⟩).1.1)
    | comp k s =>
      obtain ⟨x, y, rfl⟩ : ∃ x y : Disc.D n (Trunc.model hmn Bm) _, arityTwo x y = a :=
        ⟨a ⟨0, by simp⟩, a ⟨1, by simp⟩, by funext j; match j with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl⟩
      have hxy := (Disc.op_comp_dom (M := Trunc.model hmn Bm) k x y).mp h
      have e : Compact.msc Bm k x.1.1 = Compact.mtg Bm k y.1.1 := by
        by_cases hk : k.val < m
        · exact congrArg Subtype.val ((Trunc.sc_eq (M := Bm) _ _).symm.trans
            (((Disc.cond_lt hk).mp hxy).trans (Trunc.tg_eq (M := Bm) _ _)))
        · obtain rfl := Disc.eq_of_cond_ge hk hxy
          exact (cell_sc_ge (M := Bm) hk x.1).trans (cell_tg_ge (M := Bm) hk x.1).symm
      have hd' : (@Compact.CategoryStruct.pcomp _ _ (Compact.modelStruct (M := Bm) _) k
          x.1.1 y.1.1).Dom := Compact.CategoryStruct.pcomp_dom.mpr e
      exact (op_dom_congr (by funext j; match j with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl)).mp hd'
  map_op σ a h := by
    let Bm : Compact.CompactPAlg.{u, v, w} Sig (Fin n) := ⟨B.1, B.2.2⟩
    cases σ with
    | op σ =>
      exact (congrArg (fun y => y.1.1) (get_of_eq (Disc.op_op (M := Trunc.model hmn Bm) σ a) h)).trans
        (congrArg Subtype.val (Trunc.op_eq (M := Bm) σ _))
    | sc k s =>
      obtain ⟨x, rfl⟩ : ∃ x : Disc.D n (Trunc.model hmn Bm) _, arityOne x = a :=
        ⟨a ⟨0, by simp⟩, by funext j; match j with | ⟨0, _⟩ => rfl⟩
      refine (congrArg (fun y => y.1.1) (get_of_eq (Disc.op_sc (M := Trunc.model hmn Bm) k x) h)).trans ?_
      refine Eq.trans ?_ (Part.get_eq_get_of_eq _ (Compact.sc_dom (M := Bm) k x.1.1)
        (congrArg _ (by funext j; match j with | ⟨0, _⟩ => rfl)))
      by_cases hk : k.val < m
      · exact congrArg Subtype.val ((Disc.dsc_lt hk x).trans (Trunc.sc_eq (M := Bm) _ _))
      · exact (congrArg (fun y => y.1.1) (Disc.dsc_ge hk x)).trans (cell_sc_ge (M := Bm) hk x.1).symm
    | tg k s =>
      obtain ⟨x, rfl⟩ : ∃ x : Disc.D n (Trunc.model hmn Bm) _, arityOne x = a :=
        ⟨a ⟨0, by simp⟩, by funext j; match j with | ⟨0, _⟩ => rfl⟩
      refine (congrArg (fun y => y.1.1) (get_of_eq (Disc.op_tg (M := Trunc.model hmn Bm) k x) h)).trans ?_
      refine Eq.trans ?_ (Part.get_eq_get_of_eq _ (Compact.tg_dom (M := Bm) k x.1.1)
        (congrArg _ (by funext j; match j with | ⟨0, _⟩ => rfl)))
      by_cases hk : k.val < m
      · exact congrArg Subtype.val ((Disc.dtg_lt hk x).trans (Trunc.tg_eq (M := Bm) _ _))
      · exact (congrArg (fun y => y.1.1) (Disc.dtg_ge hk x)).trans (cell_tg_ge (M := Bm) hk x.1).symm
    | comp k s =>
      obtain ⟨x, y, rfl⟩ : ∃ x y : Disc.D n (Trunc.model hmn Bm) _, arityTwo x y = a :=
        ⟨a ⟨0, by simp⟩, a ⟨1, by simp⟩, by funext j; match j with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl⟩
      have hxy := (Disc.op_comp_dom (M := Trunc.model hmn Bm) k x y).mp h
      have e : Compact.msc Bm k x.1.1 = Compact.mtg Bm k y.1.1 := by
        by_cases hk : k.val < m
        · exact congrArg Subtype.val ((Trunc.sc_eq (M := Bm) _ _).symm.trans
            (((Disc.cond_lt hk).mp hxy).trans (Trunc.tg_eq (M := Bm) _ _)))
        · obtain rfl := Disc.eq_of_cond_ge hk hxy
          exact (cell_sc_ge (M := Bm) hk x.1).trans (cell_tg_ge (M := Bm) hk x.1).symm
      refine (congrArg (fun z => z.1.1)
        (get_of_eq (Disc.op_comp (M := Trunc.model hmn Bm) k x y hxy) h)).trans ?_
      have hpe : @Compact.CategoryStruct.pcomp _ _ (Compact.modelStruct (M := Bm) _) k x.1.1 y.1.1 =
          B.1.op (.comp k _) (fun j => (arityTwo x y j).1.1) := by
        show B.1.op _ _ = _
        congr 1; funext j; match j with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl
      refine Eq.trans ?_ (Part.get_eq_get_of_eq _
        (@Compact.CategoryStruct.dom_of_sc_is_tg _ _ (Compact.modelStruct (M := Bm) _) k
          y.1.1 x.1.1 e) hpe)
      by_cases hk : k.val < m
      · exact congrArg Subtype.val ((Disc.dcomp_lt hk x y hxy).trans
          (Trunc.comp_eq (M := Bm) (hmn := hmn) ⟨k.val, hk⟩ x.1 y.1 ((Disc.cond_lt hk).mp hxy) e))
      · obtain rfl := Disc.eq_of_cond_ge hk hxy
        refine (congrArg (fun z => z.1.1) (Disc.dcomp_ge hk x x hxy)).trans ?_
        exact ((@Compact.congr_comp₁ _ _ (Compact.modelStruct (M := Bm) _) k _ _ _ _
          (cell_sc_ge (M := Bm) hk x.1).symm rfl e).trans (Compact.model_comp_sc x.1.1)).symm

lemma tdCounit_map (B : EpSpec.EpAlg.{u, max u v, w} (compactEpSpec Sig (Fin n))) (s : S) (y) :
    PartialAlgebra.Hom.map (tdCounit hmn B) s y = y.1.1 := rfl

end TruncDisc
```

:::proposition (label := "discretization-truncation-adjunction") (central := true) (title := "Discretization is left adjoint to truncation")
Let $`m \leq n`. $`\mathrm{D}^{(n,m)} \dashv T^{(m,n)}`, with unit the isomorphism of Proposition
`truncation-discretization` and counit $`\varepsilon_{\mathbf{B}} \colon
\mathrm{D}^{(n,m)}(T^{(m,n)}(\mathbf{B})) \to \mathbf{B}` the inclusion of the $`m`-cells.

```lean
section TruncDisc

variable {Sig n m}

variable (hmn) in
/-- Discretization is left adjoint to truncation, with unit the isomorphism `T ∘ D ≅ Id` and
counit the inclusion of the `m`-cells. -/
noncomputable def discTruncAdj : Adjunction (discFunctor Sig n m) (truncFunctor Sig hmn) :=
  Adjunction.mkOfUnitCounit
    { unit := (tdIso hmn).hom
      counit :=
        { app := tdCounit hmn
          naturality := fun _ _ _ => PartialAlgebra.Hom.ext fun _ _ => rfl }
      left_triangle := by ext; rfl
      right_triangle := by ext; rfl }

end TruncDisc
```
:::

:::proof (of := "discretization-truncation-adjunction")
The inclusion $`\varepsilon_{\mathbf{B}}` commutes with the operations of $`\Sigma` and with those of
dimension $`k < m`, which are restrictions. For $`k \geq m` and an $`m`-cell $`x`,
$`\mathrm{sc}^{k}_{s}(x) = x = \mathrm{tg}^{k}_{s}(x)` in $`\mathbf{B}`, by (AB$`^{m,k}`1), and
$`x \circ^{k}_{s} x = x \circ^{k}_{s} \mathrm{sc}^{k}_{s}(x) = x`, by (A$`^{k}`5); hence
$`\varepsilon_{\mathbf{B}}` is a homomorphism, natural in $`\mathbf{B}`. Both triangle identities hold
on the cells, since unit and counit send every cell to itself.
:::

# Extended discretization and truncation

```lean
namespace DiscExt

open Extended.Model

variable {Sig n m} {M : Extended.ExtendedPAlg.{u, v, w} Sig (Fin (m + 1))}

variable (n M) in
noncomputable abbrev model : Extended.ExtendedPAlg.{u, v, w} Sig (Fin (n + 1)) := ⟨DE n M, holds⟩

lemma sc_eq {j k : Fin (n + 1)} (h : j < k) {s : S} (x : DE n M (k, s)) :
    sc (model n M) h x = esc M h x := Part.get_eq_of_mem (Part.eq_some_iff.mp (op_sc h x)) _

lemma tg_eq {j k : Fin (n + 1)} (h : j < k) {s : S} (x : DE n M (k, s)) :
    tg (model n M) h x = etg M h x := Part.get_eq_of_mem (Part.eq_some_iff.mp (op_tg h x)) _

lemma idm_eq {j k : Fin (n + 1)} (h : j < k) {s : S} (u : DE n M (j, s)) :
    idm (model n M) h u = eidm M h u := Part.get_eq_of_mem (Part.eq_some_iff.mp (op_idm h u)) _

lemma op_eq (k : Fin (n + 1)) {ws : List S} {s : S} (σ : Sig ws s) (b : ∀ p, DE n M (k, ws.get p)) :
    op (model n M) k σ b = eop M k σ b := Part.get_eq_of_mem (Part.eq_some_iff.mp (op_op k σ b)) _

lemma comp_eq {j k : Fin (n + 1)} (h : j < k) {s : S} (x y : DE n M (k, s)) (hxy) (hxy') :
    comp (model n M) h x y hxy = ecomp M h x y hxy' :=
  Part.get_eq_of_mem (Part.eq_some_iff.mp (op_comp h x y hxy')) _

/-! Transports along equalities of both dimensions. -/

variable {s : S}

lemma tp2_sc {a a' b b' : Fin (m + 1)} (ea : a = a') (eb : b = b') (h : a < b) (h' : a' < b')
    (x : M.1 (b, s)) :
    tp M (by rw [ea]) (sc M h x) = sc M h' (tp M (by rw [eb] : (b, s) = (b', s)) x) := by
  subst ea eb; rfl

lemma tp2_tg {a a' b b' : Fin (m + 1)} (ea : a = a') (eb : b = b') (h : a < b) (h' : a' < b')
    (x : M.1 (b, s)) :
    tp M (by rw [ea]) (tg M h x) = tg M h' (tp M (by rw [eb] : (b, s) = (b', s)) x) := by
  subst ea eb; rfl

lemma tp2_idm {a a' b b' : Fin (m + 1)} (ea : a = a') (eb : b = b') (h : a < b) (h' : a' < b')
    (u : M.1 (a, s)) :
    tp M (by rw [eb]) (idm M h u) = idm M h' (tp M (by rw [ea] : (a, s) = (a', s)) u) := by
  subst ea eb; rfl

lemma tp2_op {k k' : Fin (m + 1)} (ek : k = k') {ws : List S} (σ : Sig ws s)
    (b : ∀ p, M.1 (k, ws.get p)) :
    tp M (by rw [ek]) (op M k σ b) =
      op M k' σ (fun p => tp M (by rw [ek] : (k, ws.get p) = (k', ws.get p)) (b p)) := by
  subst ek; rfl

lemma tp2_comp {a a' b b' : Fin (m + 1)} (ea : a = a') (eb : b = b') (h : a < b) (h' : a' < b')
    (x y : M.1 (b, s)) (hxy : sc M h x = tg M h y) :
    tp M (by rw [eb] : (b, s) = (b', s)) (comp M h x y hxy) =
      comp M h' (tp M (by rw [eb] : (b, s) = (b', s)) x) (tp M (by rw [eb] : (b, s) = (b', s)) y)
        ((tp2_sc ea eb h h' x).symm.trans ((congrArg _ hxy).trans (tp2_tg ea eb h h' y))) := by
  subst ea eb; rfl

end DiscExt

namespace TruncExt

open Extended.Model

variable {Sig n m} {hmn : m ≤ n} {M : Extended.ExtendedPAlg.{u, v, w} Sig (Fin (n + 1))}

variable (hmn M) in
noncomputable abbrev model : Extended.ExtendedPAlg.{u, v, w} Sig (Fin (m + 1)) := ⟨TE hmn M, holds⟩

lemma sc_eq {j k : Fin (m + 1)} (h : j < k) {s : S} (x : TE hmn M (k, s)) :
    sc (model hmn M) h x = tsc hmn M h x := Part.get_eq_of_mem (Part.eq_some_iff.mp (op_sc h x)) _

lemma tg_eq {j k : Fin (m + 1)} (h : j < k) {s : S} (x : TE hmn M (k, s)) :
    tg (model hmn M) h x = ttg hmn M h x := Part.get_eq_of_mem (Part.eq_some_iff.mp (op_tg h x)) _

lemma idm_eq {j k : Fin (m + 1)} (h : j < k) {s : S} (u : TE hmn M (j, s)) :
    idm (model hmn M) h u = tidm hmn M h u :=
  Part.get_eq_of_mem (Part.eq_some_iff.mp (op_idm h u)) _

lemma op_eq (k : Fin (m + 1)) {ws : List S} {s : S} (σ : Sig ws s)
    (b : ∀ p, TE hmn M (k, ws.get p)) :
    op (model hmn M) k σ b = top hmn M k σ b :=
  Part.get_eq_of_mem (Part.eq_some_iff.mp (op_op k σ b)) _

lemma comp_eq {j k : Fin (m + 1)} (h : j < k) {s : S} (x y : TE hmn M (k, s)) (hxy) (hxy') :
    comp (model hmn M) h x y hxy = tcomp hmn M h x y hxy' :=
  Part.get_eq_of_mem (Part.eq_some_iff.mp (op_comp h x y hxy')) _

end TruncExt

lemma lowE_castDim {n m : ℕ} (hmn : m ≤ n) (k : Fin (m + 1)) : lowE m (castDim hmn k) = k := by
  have := k.isLt
  ext; simp only [lowE, castDim, Fin.coe_castLE]; omega

section ExtTruncDisc

open Extended.Model

variable {Sig n m} (hmn : m ≤ n)

lemma eK (k : Fin (m + 1)) (s : S) : (k, s) = (lowE m (castDim hmn k), s) := by
  rw [lowE_castDim]

/-- The cells of `T^ext(D^ext(𝐀))` are those of `𝐀`, up to the transport along
`min(k, m) = k`. -/
noncomputable def tdExtEquiv (A : EpSpec.EpAlg.{u, max u v, w} (extendedEpSpec Sig (Fin (m + 1))))
    (t : Fin (m + 1) × S) :
    A.1 t ≃ ((discExtFunctor Sig n m ⋙ truncExtFunctor Sig hmn).obj A).1 t where
  toFun a := ⟨⟨DiscExt.tp (M := ⟨A.1, A.2.2⟩) (eK hmn t.1 t.2) a, EEq.holdsAll_empty⟩,
    EEq.holdsAll_empty⟩
  invFun y := DiscExt.tp (M := ⟨A.1, A.2.2⟩) (eK hmn t.1 t.2).symm y.1.1
  left_inv a := (DiscExt.tp_tp (M := ⟨A.1, A.2.2⟩) _ _ a).trans rfl
  right_inv y := Subtype.ext (Subtype.ext ((DiscExt.tp_tp (M := ⟨A.1, A.2.2⟩) _ _ _).trans rfl))

lemma castDim_val_lt {j k : Fin (m + 1)} (h : j < k) : (castDim hmn j).val < m := by
  have := Fin.lt_def.mp h; have := k.isLt; simp only [castDim, Fin.coe_castLE]; omega

theorem tdExtEquiv_op (A : EpSpec.EpAlg.{u, max u v, w} (extendedEpSpec Sig (Fin (m + 1))))
    {ws : List (Fin (m + 1) × S)} {t : Fin (m + 1) × S}
    (σ : (extendedEpSpec Sig (Fin (m + 1))).sg.sig ws t) (a : Arity A.1 ws) :
    ((discExtFunctor Sig n m ⋙ truncExtFunctor Sig hmn).obj A).1.op σ
        (fun j => tdExtEquiv hmn A _ (a j)) = (A.1.op σ a).map (tdExtEquiv hmn A t) := by
  let Am : Extended.ExtendedPAlg.{u, v, w} Sig (Fin (m + 1)) := ⟨A.1, A.2.2⟩
  let Dm := DiscExt.model n Am
  cases σ with
  | op k σ =>
    obtain ⟨b, rfl⟩ : ∃ b, Extended.liftFam k b = a := ⟨_, Extended.liftFam_unlift k a⟩
    have hf : (fun q => tdExtEquiv hmn A _ (Extended.liftFam k b q)) =
        Extended.liftFam k (fun p => tdExtEquiv hmn A _ (b p)) := by
      funext q
      have key : ∀ {t t' : Fin (m + 1) × S} (e : t = t') (x : A.1 t),
          tdExtEquiv hmn A t' (cast (congrArg (fun t => A.1 t) e) x) =
            cast (congrArg (fun t => ((discExtFunctor Sig n m ⋙ truncExtFunctor Sig hmn).obj A).1 t) e)
              (tdExtEquiv hmn A t x) := by
        intro t t' e; subst e; intro x; rfl
      exact key (by simp) _
    have h1 : A.1.op (.op k σ) (Extended.liftFam k b) = Part.some (op Am k σ b) :=
      (Part.some_get _).symm
    refine Eq.trans ?_ ((congrArg (Part.map _) h1).trans (Part.map_some _ _)).symm
    refine ((congrArg _ hf).trans (TruncExt.op_op (M := Dm) k σ _)).trans ?_
    exact congrArg Part.some (Subtype.ext ((DiscExt.op_eq (M := Am) _ σ _).trans
      (Subtype.ext (DiscExt.tp2_op (M := Am) (lowE_castDim hmn k).symm σ b).symm)))
  | @sc j k h s =>
    have hj := castDim_val_lt hmn h
    have h1 : A.1.op (.sc h s) a = Part.some (sc Am h (a ⟨0, by simp⟩)) :=
      op_eq_some_get (by funext i; match i with | ⟨0, _⟩ => rfl) _
    refine Eq.trans ?_ ((congrArg (Part.map _) h1).trans (Part.map_some _ _)).symm
    refine ((congrArg _ (by funext i; match i with | ⟨0, _⟩ => rfl)).trans
      (TruncExt.op_sc (M := Dm) h (tdExtEquiv hmn A (k, s) (a ⟨0, by simp⟩)))).trans ?_
    exact congrArg Part.some (Subtype.ext ((DiscExt.sc_eq (M := Am) _ _).trans (Subtype.ext
      ((DiscExt.esc_pos (M := Am) (h := castDim_lt hmn h) hj _).trans (DiscExt.tp2_sc (M := Am) (lowE_castDim hmn j).symm
        (lowE_castDim hmn k).symm h _ _).symm))))
  | @tg j k h s =>
    have hj := castDim_val_lt hmn h
    have h1 : A.1.op (.tg h s) a = Part.some (tg Am h (a ⟨0, by simp⟩)) :=
      op_eq_some_get (by funext i; match i with | ⟨0, _⟩ => rfl) _
    refine Eq.trans ?_ ((congrArg (Part.map _) h1).trans (Part.map_some _ _)).symm
    refine ((congrArg _ (by funext i; match i with | ⟨0, _⟩ => rfl)).trans
      (TruncExt.op_tg (M := Dm) h (tdExtEquiv hmn A (k, s) (a ⟨0, by simp⟩)))).trans ?_
    exact congrArg Part.some (Subtype.ext ((DiscExt.tg_eq (M := Am) _ _).trans (Subtype.ext
      ((DiscExt.etg_pos (M := Am) (h := castDim_lt hmn h) hj _).trans (DiscExt.tp2_tg (M := Am) (lowE_castDim hmn j).symm
        (lowE_castDim hmn k).symm h _ _).symm))))
  | @idm j k h s =>
    have hj := castDim_val_lt hmn h
    have h1 : A.1.op (.idm h s) a = Part.some (idm Am h (a ⟨0, by simp⟩)) :=
      op_eq_some_get (by funext i; match i with | ⟨0, _⟩ => rfl) _
    refine Eq.trans ?_ ((congrArg (Part.map _) h1).trans (Part.map_some _ _)).symm
    refine ((congrArg _ (by funext i; match i with | ⟨0, _⟩ => rfl)).trans
      (TruncExt.op_idm (M := Dm) h (tdExtEquiv hmn A (j, s) (a ⟨0, by simp⟩)))).trans ?_
    exact congrArg Part.some (Subtype.ext ((DiscExt.idm_eq (M := Am) _ _).trans (Subtype.ext
      ((DiscExt.eidm_pos (M := Am) (h := castDim_lt hmn h) hj _).trans (DiscExt.tp2_idm (M := Am) (lowE_castDim hmn j).symm
        (lowE_castDim hmn k).symm h _ _).symm))))
  | @comp j k h s =>
    have hj := castDim_val_lt hmn h
    have ha : (fun i => tdExtEquiv hmn A _ (a i)) =
        Extended.arg₂ (tdExtEquiv hmn A (k, s) (a ⟨0, by simp⟩))
          (tdExtEquiv hmn A (k, s) (a ⟨1, by simp⟩)) := by
      funext i; match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl
    have hA : Extended.arg₂ (a ⟨0, by simp⟩) (a ⟨1, by simp⟩) = a := by
      funext i; match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl
    refine (congrArg _ ha).trans ?_
    have ej := (lowE_castDim hmn j).symm
    have ek := (lowE_castDim hmn k).symm
    have hl := lowE_lt (castDim_lt hmn h) hj
    by_cases hxy : sc Am h (a ⟨0, by simp⟩) = tg Am h (a ⟨1, by simp⟩)
    · have P : sc Am hl (tdExtEquiv hmn A (k, s) (a ⟨0, by simp⟩)).1.1 =
          tg Am hl (tdExtEquiv hmn A (k, s) (a ⟨1, by simp⟩)).1.1 :=
        (DiscExt.tp2_sc (M := Am) ej ek h hl _).symm.trans
          ((congrArg _ hxy).trans (DiscExt.tp2_tg (M := Am) ej ek h hl _))
      have hd := (DiscExt.cond_pos (M := Am) (h := castDim_lt hmn h) hj).mpr P
      have hc := (DiscExt.sc_eq (M := Am) _ _).trans (hd.trans (DiscExt.tg_eq (M := Am) _ _).symm)
      have h1 : A.1.op (.comp h s) a = Part.some (comp Am h _ _ hxy) :=
        op_eq_some_get hA (Extended.Model.pcomp_dom_iff.mpr hxy)
      refine Eq.trans ?_ ((congrArg (Part.map _) h1).trans (Part.map_some _ _)).symm
      refine (TruncExt.op_comp (M := Dm) h _ _ hc).trans ?_
      exact congrArg Part.some (Subtype.ext ((DiscExt.comp_eq (M := Am) _ _ _ hc hd).trans
        (Subtype.ext ((DiscExt.ecomp_pos (M := Am) (h := castDim_lt hmn h) hj _ _ hd).trans
          (DiscExt.tp2_comp (M := Am) ej ek h hl _ _ hxy).symm))))
    · have h1 : A.1.op (.comp h s) a = Part.none :=
        Part.eq_none_iff'.mpr fun hd => hxy (Extended.Model.pcomp_dom_iff.mp
          ((op_dom_congr hA).mpr hd))
      refine Eq.trans ?_ ((congrArg (Part.map _) h1).trans (Part.map_none _)).symm
      refine Part.eq_none_iff'.mpr fun hd => hxy ?_
      have hc := (TruncExt.op_comp_dom (M := Dm) h _ _).mp hd
      have hd' := (DiscExt.sc_eq (M := Am) _ _).symm.trans (hc.trans (DiscExt.tg_eq (M := Am) _ _))
      have P := (DiscExt.cond_pos (M := Am) (h := castDim_lt hmn h) hj).mp hd'
      exact DiscExt.tp_inj (M := Am) _ ((DiscExt.tp2_sc (M := Am) ej ek h hl _).trans
        (P.trans (DiscExt.tp2_tg (M := Am) ej ek h hl _).symm))

end ExtTruncDisc
```

:::proposition (label := "truncation-discretization-ext") (central := false) (title := "Extended truncation after extended discretization")
Let $`m \leq n`. $`T^{\mathrm{ext}(m,n)} \circ \mathrm{D}^{\mathrm{ext}(n,m)} \cong \mathrm{Id}`, by the
isomorphisms that send a $`k`-cell to itself; in the Lean, along the transport of the sort
$`(\min\{k, m\}, s) = (k, s)`.

```lean
section ExtTruncDisc

variable {Sig n m} (hmn : m ≤ n)

/-- `T^ext ∘ D^ext ≅ Id`, by the transports along `min(k, m) = k`. -/
noncomputable def tdExtIso :
    𝟭 (EpSpec.EpAlg.{u, max u v, w} (extendedEpSpec Sig (Fin (m + 1)))) ≅
      discExtFunctor Sig n m ⋙ truncExtFunctor Sig hmn :=
  NatIso.ofComponents (fun A => EpSpec.isoOfEquiv (tdExtEquiv hmn A) (tdExtEquiv_op hmn A))
    (fun {X Y} f => PartialAlgebra.Hom.ext fun t x => by
      have key : ∀ {t' : Fin (m + 1) × S} (e : t = t') (y : X.1 t),
          DiscExt.tp (M := ⟨Y.1, Y.2.2⟩) e (PartialAlgebra.Hom.map f t y) =
            PartialAlgebra.Hom.map f t' (DiscExt.tp (M := ⟨X.1, X.2.2⟩) e y) := by
        intro t' e; subst e; intro y; rfl
      exact Subtype.ext (Subtype.ext (key _ x)))

end ExtTruncDisc
```
:::

:::proof (of := "truncation-discretization-ext")
On the dimensions $`k \leq m`, $`\boldsymbol{\delta}^{\mathrm{ext}(n,m)}` is the identity, so the cells
and the operations of $`T^{\mathrm{ext}(m,n)}(\mathrm{D}^{\mathrm{ext}(n,m)}(\mathbf{A}))` are those of
$`\mathbf{A}`.
:::

```lean

section ExtCounit

open Extended.Model

variable {Sig n m} (hmn : m ≤ n) {B : Extended.ExtendedPAlg.{u, v, w} Sig (Fin (n + 1))} {s : S}

lemma cl_eq {k : Fin (n + 1)} (hk : k.val ≤ m) : castDim hmn (lowE m k) = k := by
  ext; simp only [castDim, lowE, Fin.coe_castLE]; omega

lemma cl_lt {k : Fin (n + 1)} (hk : ¬ k.val ≤ m) : castDim hmn (lowE m k) < k := by
  rw [Fin.lt_def]; simp only [castDim, lowE, Fin.coe_castLE]; omega

variable (B) in
/-- The component of the extended counit at `(k, s)`: the transport for `k ≤ m`, and the
`(k,m)`-identity for `k > m`. -/
noncomputable def up' (k : Fin (n + 1)) (z : B.1 (castDim hmn (lowE m k), s)) : B.1 (k, s) :=
  if hk : k.val ≤ m then DiscExt.tp (M := B) (by rw [cl_eq hmn hk]) z else idm B (cl_lt hmn hk) z

lemma up'_le {k : Fin (n + 1)} (hk : k.val ≤ m) (z : B.1 (castDim hmn (lowE m k), s)) :
    up' hmn B k z = DiscExt.tp (M := B) (by rw [cl_eq hmn hk]) z := dif_pos hk

lemma up'_gt {k : Fin (n + 1)} (hk : ¬ k.val ≤ m) (z : B.1 (castDim hmn (lowE m k), s)) :
    up' hmn B k z = idm B (cl_lt hmn hk) z := dif_neg hk

omit hmn in
lemma sc_idm_tp {a j k : Fin (n + 1)} (e : a = j) (h : j < k) (h' : a < k) (z : B.1 (a, s)) :
    sc B h (idm B h' z) = DiscExt.tp (M := B) (by rw [e]) z := by
  subst e; exact sc_idm z

omit hmn in
lemma tg_idm_tp {a j k : Fin (n + 1)} (e : a = j) (h : j < k) (h' : a < k) (z : B.1 (a, s)) :
    tg B h (idm B h' z) = DiscExt.tp (M := B) (by rw [e]) z := by
  subst e; exact tg_idm z

omit hmn in
lemma idm_tp {a a' j : Fin (n + 1)} (e : a = a') (h : a' < j) (h' : a < j) (z : B.1 (a, s)) :
    idm B h (DiscExt.tp (M := B) (by rw [e]) z) = idm B h' z := by
  subst e; rfl

omit hmn in
lemma comp_lower {a a' b : Fin (n + 1)} (e : a = a') (h : a < b) (h' : a' < b) (x y : B.1 (b, s))
    (hxy : sc B h x = tg B h y) (hxy' : sc B h' x = tg B h' y) :
    comp B h x y hxy = comp B h' x y hxy' := by
  subst e; rfl

omit hmn in
lemma sc_idm_lower {a j k : Fin (n + 1)} (h₁ : a < j) (h₂ : j < k) (z : B.1 (a, s)) :
    sc B h₂ (idm B (h₁.trans h₂) z) = idm B h₁ z := by
  rw [← idm_idm (h₁ := h₁) (h₂ := h₂), sc_idm]

omit hmn in
lemma tg_idm_lower {a j k : Fin (n + 1)} (h₁ : a < j) (h₂ : j < k) (z : B.1 (a, s)) :
    tg B h₂ (idm B (h₁.trans h₂) z) = idm B h₁ z := by
  rw [← idm_idm (h₁ := h₁) (h₂ := h₂), tg_idm]

lemma lt_cl {j k : Fin (n + 1)} (hj : j.val < m) (hk : ¬ k.val ≤ m) : j < castDim hmn (lowE m k) := by
  rw [Fin.lt_def]; simp only [castDim, lowE, Fin.coe_castLE]; omega

lemma cl_eq_cl {j k : Fin (n + 1)} (h : j < k) (hj : ¬ j.val < m) :
    castDim hmn (lowE m k) = castDim hmn (lowE m j) := by rw [lowE_eq h hj]

lemma E_sc_pos {j k : Fin (n + 1)} (h : j < k) (hj : j.val < m)
    (z : B.1 (castDim hmn (lowE m k), s)) :
    up' hmn B j (sc B (castDim_lt hmn (lowE_lt h hj)) z) = sc B h (up' hmn B k z) := by
  rw [up'_le hmn hj.le]
  by_cases hk : k.val ≤ m
  · rw [up'_le hmn hk]; exact DiscExt.tp2_sc (M := B) (cl_eq hmn hj.le) (cl_eq hmn hk) _ h z
  · rw [up'_gt hmn hk]
    exact (DiscExt.tp2_sc (M := B) (cl_eq hmn hj.le) rfl _ (lt_cl hmn hj hk) z).trans
      (sc_idm_low (h₁ := lt_cl hmn hj hk) (h₂ := cl_lt hmn hk) z).symm

lemma E_tg_pos {j k : Fin (n + 1)} (h : j < k) (hj : j.val < m)
    (z : B.1 (castDim hmn (lowE m k), s)) :
    up' hmn B j (tg B (castDim_lt hmn (lowE_lt h hj)) z) = tg B h (up' hmn B k z) := by
  rw [up'_le hmn hj.le]
  by_cases hk : k.val ≤ m
  · rw [up'_le hmn hk]; exact DiscExt.tp2_tg (M := B) (cl_eq hmn hj.le) (cl_eq hmn hk) _ h z
  · rw [up'_gt hmn hk]
    exact (DiscExt.tp2_tg (M := B) (cl_eq hmn hj.le) rfl _ (lt_cl hmn hj hk) z).trans
      (tg_idm_low (h₁ := lt_cl hmn hj hk) (h₂ := cl_lt hmn hk) z).symm

lemma gt_of_neg {j k : Fin (n + 1)} (h : j < k) (hj : ¬ j.val < m) : ¬ k.val ≤ m := by
  have := Fin.lt_def.mp h; omega

lemma E_sc_neg {j k : Fin (n + 1)} (h : j < k) (hj : ¬ j.val < m)
    (z : B.1 (castDim hmn (lowE m k), s)) :
    up' hmn B j (DiscExt.tp (M := B) (by rw [cl_eq_cl hmn h hj]) z) = sc B h (up' hmn B k z) := by
  have hk := gt_of_neg h hj
  rw [up'_gt hmn hk]
  by_cases hj' : j.val ≤ m
  · rw [up'_le hmn hj']
    exact (DiscExt.tp_tp _ _ _).trans
      (sc_idm_tp (by rw [cl_eq_cl hmn h hj, cl_eq hmn hj']) h (cl_lt hmn hk) z).symm
  · rw [up'_gt hmn hj']
    have h₁ : castDim hmn (lowE m k) < j := by rw [cl_eq_cl hmn h hj]; exact cl_lt hmn hj'
    exact (idm_tp (cl_eq_cl hmn h hj) _ h₁ z).trans (sc_idm_lower h₁ h z).symm

lemma E_tg_neg {j k : Fin (n + 1)} (h : j < k) (hj : ¬ j.val < m)
    (z : B.1 (castDim hmn (lowE m k), s)) :
    up' hmn B j (DiscExt.tp (M := B) (by rw [cl_eq_cl hmn h hj]) z) = tg B h (up' hmn B k z) := by
  have hk := gt_of_neg h hj
  rw [up'_gt hmn hk]
  by_cases hj' : j.val ≤ m
  · rw [up'_le hmn hj']
    exact (DiscExt.tp_tp _ _ _).trans
      (tg_idm_tp (by rw [cl_eq_cl hmn h hj, cl_eq hmn hj']) h (cl_lt hmn hk) z).symm
  · rw [up'_gt hmn hj']
    have h₁ : castDim hmn (lowE m k) < j := by rw [cl_eq_cl hmn h hj]; exact cl_lt hmn hj'
    exact (idm_tp (cl_eq_cl hmn h hj) _ h₁ z).trans (tg_idm_lower h₁ h z).symm

lemma E_idm_pos {j k : Fin (n + 1)} (h : j < k) (hj : j.val < m)
    (u : B.1 (castDim hmn (lowE m j), s)) :
    up' hmn B k (idm B (castDim_lt hmn (lowE_lt h hj)) u) = idm B h (up' hmn B j u) := by
  rw [up'_le hmn hj.le]
  by_cases hk : k.val ≤ m
  · rw [up'_le hmn hk]; exact DiscExt.tp2_idm (M := B) (cl_eq hmn hj.le) (cl_eq hmn hk) _ h u
  · rw [up'_gt hmn hk, idm_idm]
    exact (idm_tp (cl_eq hmn hj.le) h _ u).symm

lemma E_idm_neg {j k : Fin (n + 1)} (h : j < k) (hj : ¬ j.val < m)
    (u : B.1 (castDim hmn (lowE m j), s)) :
    up' hmn B k (DiscExt.tp (M := B) (by rw [cl_eq_cl hmn h hj]) u) = idm B h (up' hmn B j u) := by
  have hk := gt_of_neg h hj
  rw [up'_gt hmn hk]
  have h₁ : castDim hmn (lowE m j) < k := by rw [← cl_eq_cl hmn h hj]; exact cl_lt hmn hk
  refine (idm_tp (cl_eq_cl hmn h hj).symm _ h₁ u).trans ?_
  by_cases hj' : j.val ≤ m
  · rw [up'_le hmn hj']; exact (idm_tp (cl_eq hmn hj') h h₁ u).symm
  · rw [up'_gt hmn hj', idm_idm]

lemma E_op (k : Fin (n + 1)) {ws : List S} (σ : Sig ws s)
    (c : ∀ p, B.1 (castDim hmn (lowE m k), ws.get p)) :
    up' hmn B k (op B (castDim hmn (lowE m k)) σ c) = op B k σ (fun p => up' hmn B k (c p)) := by
  by_cases hk : k.val ≤ m
  · rw [up'_le hmn hk]
    exact (DiscExt.tp2_op (M := B) (cl_eq hmn hk) σ c).trans
      (congrArg (op B k σ) (funext fun p => (up'_le hmn hk (c p)).symm))
  · rw [up'_gt hmn hk]
    exact (idm_op (cl_lt hmn hk) σ c).trans
      (congrArg (op B k σ) (funext fun p => (up'_gt hmn hk (c p)).symm))

lemma E_comp_pos {j k : Fin (n + 1)} (h : j < k) (hj : j.val < m)
    (z z' : B.1 (castDim hmn (lowE m k), s))
    (hzz : sc B (castDim_lt hmn (lowE_lt h hj)) z = tg B (castDim_lt hmn (lowE_lt h hj)) z') :
    up' hmn B k (comp B _ z z' hzz) = comp B h (up' hmn B k z) (up' hmn B k z')
      ((E_sc_pos hmn h hj z).symm.trans ((congrArg _ hzz).trans (E_tg_pos hmn h hj z'))) := by
  by_cases hk : k.val ≤ m
  · exact (up'_le hmn hk _).trans ((DiscExt.tp2_comp (M := B) (cl_eq hmn hj.le) (cl_eq hmn hk) _ h
      z z' hzz).trans (comp_congr (up'_le hmn hk z).symm (up'_le hmn hk z').symm _ _))
  · have X : sc B (lt_cl hmn hj hk) z = tg B (lt_cl hmn hj hk) z' :=
      (DiscExt.tp2_sc (M := B) (cl_eq hmn hj.le) rfl _ (lt_cl hmn hj hk) z).symm.trans
        ((congrArg _ hzz).trans (DiscExt.tp2_tg (M := B) (cl_eq hmn hj.le) rfl _ (lt_cl hmn hj hk) z'))
    have Q : sc B h (idm B (cl_lt hmn hk) z) = tg B h (idm B (cl_lt hmn hk) z') :=
      ((sc_idm_low (h₁ := lt_cl hmn hj hk) (h₂ := cl_lt hmn hk) z).trans X).trans
        (tg_idm_low (h₁ := lt_cl hmn hj hk) (h₂ := cl_lt hmn hk) z').symm
    exact (up'_gt hmn hk _).trans ((idm_comp (h₁ := castDim_lt hmn (lowE_lt h hj))
      (h₂ := cl_lt hmn hk) hzz).trans ((comp_lower (cl_eq hmn hj.le) _ h _ _ _ Q).trans
        (comp_congr (up'_gt hmn hk z).symm (up'_gt hmn hk z').symm _ _)))

omit hmn in
lemma comp_self_of {j k : Fin (n + 1)} (h : j < k) (x : B.1 (k, s))
    (hx : idm B h (sc B h x) = x) (P : sc B h x = tg B h x) : comp B h x x P = x :=
  (comp_congr rfl hx.symm P (tg_idm _).symm).trans (comp_idm_sc x)

lemma E_comp_neg {j k : Fin (n + 1)} (h : j < k) (hj : ¬ j.val < m)
    (z : B.1 (castDim hmn (lowE m k), s)) (P : sc B h (up' hmn B k z) = tg B h (up' hmn B k z)) :
    up' hmn B k z = comp B h (up' hmn B k z) (up' hmn B k z) P := by
  have hk := gt_of_neg h hj
  refine (comp_self_of h _ ?_ P).symm
  rw [up'_gt hmn hk]
  by_cases hj' : j.val ≤ m
  · have e1 : castDim hmn (lowE m k) = j := by rw [cl_eq_cl hmn h hj, cl_eq hmn hj']
    rw [sc_idm_tp e1 h (cl_lt hmn hk) z]
    exact idm_tp e1 h _ z
  · have h₁ : castDim hmn (lowE m k) < j := by rw [cl_eq_cl hmn h hj]; exact cl_lt hmn hj'
    rw [sc_idm_lower h₁ h z, idm_idm]

end ExtCounit

section ExtCounitHom

open Extended.Model

variable {Sig n m} (hmn : m ≤ n) {Bm : Extended.ExtendedPAlg.{u, v, w} Sig (Fin (n + 1))}

/-- Transports in the truncated algebra are transports of the underlying cells. -/
lemma tp_val {t t' : Fin (m + 1) × S} (e : t = t')
    (e' : (castDim hmn t.1, t.2) = (castDim hmn t'.1, t'.2)) (y : TruncExt.TE hmn Bm t) :
    (DiscExt.tp (M := TruncExt.model hmn Bm) e y).1 = DiscExt.tp (M := Bm) e' y.1 := by
  subst e; rfl

variable {s : S}

local notation "Tm" => TruncExt.model hmn Bm

lemma val_esc_pos {j k : Fin (n + 1)} (h : j < k) (hj : j.val < m) (x : DiscExt.DE n Tm (k, s)) :
    (DiscExt.esc Tm h x).1.1 = sc Bm (castDim_lt hmn (lowE_lt h hj)) x.1.1 :=
  congrArg Subtype.val ((DiscExt.esc_pos (M := Tm) (h := h) hj x).trans (TruncExt.sc_eq _ _))

lemma val_esc_neg {j k : Fin (n + 1)} (h : j < k) (hj : ¬ j.val < m) (x : DiscExt.DE n Tm (k, s)) :
    (DiscExt.esc Tm h x).1.1 =
      DiscExt.tp (M := Bm) (congrArg (·, s) (cl_eq_cl hmn h hj)) x.1.1 :=
  (congrArg Subtype.val (DiscExt.esc_neg (M := Tm) (h := h) hj x)).trans (tp_val hmn _ _ _)

lemma val_etg_pos {j k : Fin (n + 1)} (h : j < k) (hj : j.val < m) (x : DiscExt.DE n Tm (k, s)) :
    (DiscExt.etg Tm h x).1.1 = tg Bm (castDim_lt hmn (lowE_lt h hj)) x.1.1 :=
  congrArg Subtype.val ((DiscExt.etg_pos (M := Tm) (h := h) hj x).trans (TruncExt.tg_eq _ _))

lemma val_etg_neg {j k : Fin (n + 1)} (h : j < k) (hj : ¬ j.val < m) (x : DiscExt.DE n Tm (k, s)) :
    (DiscExt.etg Tm h x).1.1 =
      DiscExt.tp (M := Bm) (congrArg (·, s) (cl_eq_cl hmn h hj)) x.1.1 :=
  (congrArg Subtype.val (DiscExt.etg_neg (M := Tm) (h := h) hj x)).trans (tp_val hmn _ _ _)

lemma val_eidm_pos {j k : Fin (n + 1)} (h : j < k) (hj : j.val < m) (u : DiscExt.DE n Tm (j, s)) :
    (DiscExt.eidm Tm h u).1.1 = idm Bm (castDim_lt hmn (lowE_lt h hj)) u.1.1 :=
  congrArg Subtype.val ((DiscExt.eidm_pos (M := Tm) (h := h) hj u).trans (TruncExt.idm_eq _ _))

lemma val_eidm_neg {j k : Fin (n + 1)} (h : j < k) (hj : ¬ j.val < m) (u : DiscExt.DE n Tm (j, s)) :
    (DiscExt.eidm Tm h u).1.1 =
      DiscExt.tp (M := Bm) (congrArg (·, s) (cl_eq_cl hmn h hj).symm) u.1.1 :=
  (congrArg Subtype.val (DiscExt.eidm_neg (M := Tm) (h := h) hj u)).trans (tp_val hmn _ _ _)

lemma sc_up' {j k : Fin (n + 1)} (h : j < k) (x : DiscExt.DE n Tm (k, s)) :
    sc Bm h (up' hmn Bm k x.1.1) = up' hmn Bm j (DiscExt.esc Tm h x).1.1 := by
  by_cases hj : j.val < m
  · rw [val_esc_pos hmn h hj]; exact (E_sc_pos hmn h hj _).symm
  · rw [val_esc_neg hmn h hj]; exact (E_sc_neg hmn h hj _).symm

lemma tg_up' {j k : Fin (n + 1)} (h : j < k) (x : DiscExt.DE n Tm (k, s)) :
    tg Bm h (up' hmn Bm k x.1.1) = up' hmn Bm j (DiscExt.etg Tm h x).1.1 := by
  by_cases hj : j.val < m
  · rw [val_etg_pos hmn h hj]; exact (E_tg_pos hmn h hj _).symm
  · rw [val_etg_neg hmn h hj]; exact (E_tg_neg hmn h hj _).symm

lemma idm_up' {j k : Fin (n + 1)} (h : j < k) (u : DiscExt.DE n Tm (j, s)) :
    idm Bm h (up' hmn Bm j u.1.1) = up' hmn Bm k (DiscExt.eidm Tm h u).1.1 := by
  by_cases hj : j.val < m
  · rw [val_eidm_pos hmn h hj]; exact (E_idm_pos hmn h hj _).symm
  · rw [val_eidm_neg hmn h hj]; exact (E_idm_neg hmn h hj _).symm

lemma val_ecomp_pos {j k : Fin (n + 1)} (h : j < k) (hj : j.val < m) (x y : DiscExt.DE n Tm (k, s))
    (hc : DiscExt.esc Tm h x = DiscExt.etg Tm h y) :
    (DiscExt.ecomp Tm h x y hc).1.1 = comp Bm (castDim_lt hmn (lowE_lt h hj)) x.1.1 y.1.1
      ((val_esc_pos hmn h hj x).symm.trans ((congrArg (fun z => z.1.1) hc).trans
        (val_etg_pos hmn h hj y))) := by
  have P : sc Bm (castDim_lt hmn (lowE_lt h hj)) x.1.1 = tg Bm (castDim_lt hmn (lowE_lt h hj)) y.1.1 :=
    (val_esc_pos hmn h hj x).symm.trans ((congrArg (fun z => z.1.1) hc).trans (val_etg_pos hmn h hj y))
  exact congrArg Subtype.val ((DiscExt.ecomp_pos (M := Tm) hj x y hc).trans
    (TruncExt.comp_eq _ _ _ _ P))

end ExtCounitHom

section ExtCounitHom₂

open Extended.Model

variable {Sig n m} (hmn : m ≤ n)

lemma get_of_eq' {α : Type*} {o : Part α} {c : α} (e : o = Part.some c) (h : o.Dom) : o.get h = c :=
  Part.get_eq_of_mem (Part.eq_some_iff.mp e) h

/-- The extended counit `D^ext(T^ext(𝐁)) → 𝐁`. -/
noncomputable def tdExtCounit (B : EpSpec.EpAlg.{u, max u v, w} (extendedEpSpec Sig (Fin (n + 1)))) :
    (truncExtFunctor Sig hmn ⋙ discExtFunctor Sig n m).obj B ⟶ B where
  map t y := up' hmn ⟨B.1, B.2.2⟩ t.1 y.1.1
  map_dom σ a ha := by
    let Bm : Extended.ExtendedPAlg.{u, v, w} Sig (Fin (n + 1)) := ⟨B.1, B.2.2⟩
    cases σ with
    | op k σ => exact op_dom' (M := Bm) k σ _
    | sc h s =>
      exact (op_dom_congr (by funext i; match i with | ⟨0, _⟩ => rfl)).mp
        (sc_dom (M := Bm) h (up' hmn Bm _ (a ⟨0, by simp⟩).1.1))
    | tg h s =>
      exact (op_dom_congr (by funext i; match i with | ⟨0, _⟩ => rfl)).mp
        (tg_dom (M := Bm) h (up' hmn Bm _ (a ⟨0, by simp⟩).1.1))
    | idm h s =>
      exact (op_dom_congr (by funext i; match i with | ⟨0, _⟩ => rfl)).mp
        (idm_dom (M := Bm) h (up' hmn Bm _ (a ⟨0, by simp⟩).1.1))
    | @comp j k h s =>
      obtain ⟨x, y, rfl⟩ : ∃ x y : DiscExt.DE n (TruncExt.model hmn Bm) (k, s),
          Extended.arg₂ x y = a :=
        ⟨a ⟨0, by simp⟩, a ⟨1, by simp⟩, by funext i; match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl⟩
      have hc := (DiscExt.op_comp_dom (M := TruncExt.model hmn Bm) h x y).mp ha
      have e : sc Bm h (up' hmn Bm k x.1.1) = tg Bm h (up' hmn Bm k y.1.1) :=
        (sc_up' hmn h x).trans ((congrArg (fun z => up' hmn Bm j z.1.1) hc).trans
          (tg_up' hmn h y).symm)
      exact (op_dom_congr (by funext i; match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl)).mp
        (pcomp_dom_iff (M := Bm).mpr e)
  map_op σ a ha := by
    let Bm : Extended.ExtendedPAlg.{u, v, w} Sig (Fin (n + 1)) := ⟨B.1, B.2.2⟩
    cases σ with
    | @op k ws s σ =>
      obtain ⟨b, rfl⟩ : ∃ b, Extended.liftFam k b = a := ⟨_, Extended.liftFam_unlift k a⟩
      have hf : (fun q => up' hmn Bm _ (Extended.liftFam k b q).1.1) =
          Extended.liftFam k (fun p => up' hmn Bm k (b p).1.1) := by
        funext q
        have key : ∀ {t t' : Fin (n + 1) × S} (e : t = t')
            (x : ((truncExtFunctor Sig hmn ⋙ discExtFunctor Sig n m).obj B).1 t),
            up' hmn Bm t'.1 (cast (congrArg
              (fun t => ((truncExtFunctor Sig hmn ⋙ discExtFunctor Sig n m).obj B).1 t) e) x).1.1 =
              cast (congrArg Bm.1 e) (up' hmn Bm t.1 x.1.1) := by
          intro t t' e; subst e; intro x; rfl
        exact key (by simp) _
      refine (congrArg (fun z => up' hmn Bm k z.1.1)
        (get_of_eq' (DiscExt.op_op (M := TruncExt.model hmn Bm) k σ b) ha)).trans ?_
      refine (congrArg (up' hmn Bm k) (congrArg Subtype.val (TruncExt.op_eq _ σ _))).trans ?_
      refine (E_op hmn k σ _).trans ?_
      exact Part.get_eq_get_of_eq _ (op_dom k σ _) (congrArg _ hf.symm)
    | @sc j k h s =>
      obtain ⟨x, rfl⟩ : ∃ x : DiscExt.DE n (TruncExt.model hmn Bm) (k, s), Extended.arg₁ x = a :=
        ⟨a ⟨0, by simp⟩, by funext i; match i with | ⟨0, _⟩ => rfl⟩
      refine (congrArg (fun z => up' hmn Bm j z.1.1)
        (get_of_eq' (DiscExt.op_sc (M := TruncExt.model hmn Bm) h x) ha)).trans ?_
      exact (sc_up' hmn h x).symm.trans (Part.get_eq_get_of_eq _ (sc_dom (M := Bm) h _)
        (congrArg _ (by funext i; match i with | ⟨0, _⟩ => rfl)))
    | @tg j k h s =>
      obtain ⟨x, rfl⟩ : ∃ x : DiscExt.DE n (TruncExt.model hmn Bm) (k, s), Extended.arg₁ x = a :=
        ⟨a ⟨0, by simp⟩, by funext i; match i with | ⟨0, _⟩ => rfl⟩
      refine (congrArg (fun z => up' hmn Bm j z.1.1)
        (get_of_eq' (DiscExt.op_tg (M := TruncExt.model hmn Bm) h x) ha)).trans ?_
      exact (tg_up' hmn h x).symm.trans (Part.get_eq_get_of_eq _ (tg_dom (M := Bm) h _)
        (congrArg _ (by funext i; match i with | ⟨0, _⟩ => rfl)))
    | @idm j k h s =>
      obtain ⟨u, rfl⟩ : ∃ u : DiscExt.DE n (TruncExt.model hmn Bm) (j, s), Extended.arg₁ u = a :=
        ⟨a ⟨0, by simp⟩, by funext i; match i with | ⟨0, _⟩ => rfl⟩
      refine (congrArg (fun z => up' hmn Bm k z.1.1)
        (get_of_eq' (DiscExt.op_idm (M := TruncExt.model hmn Bm) h u) ha)).trans ?_
      exact (idm_up' hmn h u).symm.trans (Part.get_eq_get_of_eq _ (idm_dom (M := Bm) h _)
        (congrArg _ (by funext i; match i with | ⟨0, _⟩ => rfl)))
    | @comp j k h s =>
      obtain ⟨x, y, rfl⟩ : ∃ x y : DiscExt.DE n (TruncExt.model hmn Bm) (k, s),
          Extended.arg₂ x y = a :=
        ⟨a ⟨0, by simp⟩, a ⟨1, by simp⟩, by funext i; match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl⟩
      have hc := (DiscExt.op_comp_dom (M := TruncExt.model hmn Bm) h x y).mp ha
      have e : sc Bm h (up' hmn Bm k x.1.1) = tg Bm h (up' hmn Bm k y.1.1) :=
        (sc_up' hmn h x).trans ((congrArg (fun z => up' hmn Bm j z.1.1) hc).trans
          (tg_up' hmn h y).symm)
      refine (congrArg (fun z => up' hmn Bm k z.1.1)
        (get_of_eq' (DiscExt.op_comp (M := TruncExt.model hmn Bm) h x y hc) ha)).trans ?_
      refine Eq.trans ?_ (Part.get_eq_get_of_eq _ (pcomp_dom_iff (M := Bm).mpr e)
        (congrArg (B.1.op (.comp h s)) (by funext i; match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl)))
      by_cases hj : j.val < m
      · exact (congrArg (up' hmn Bm k) (val_ecomp_pos hmn h hj x y hc)).trans
          (E_comp_pos hmn h hj _ _ _)
      · obtain rfl := (DiscExt.cond_neg (M := TruncExt.model hmn Bm) hj).mp hc
        exact (congrArg (fun z => up' hmn Bm k z.1.1)
          (DiscExt.ecomp_neg (M := TruncExt.model hmn Bm) hj x x hc)).trans
          (E_comp_neg hmn h hj _ e)

lemma map_up' {B B' : EpSpec.EpAlg.{u, max u v, w} (extendedEpSpec Sig (Fin (n + 1)))} (f : B ⟶ B')
    (k : Fin (n + 1)) {s : S} (z : B.1 (castDim hmn (lowE m k), s)) :
    PartialAlgebra.Hom.map f _ (up' hmn ⟨B.1, B.2.2⟩ k z) =
      up' hmn ⟨B'.1, B'.2.2⟩ k (PartialAlgebra.Hom.map f _ z) := by
  by_cases hk : k.val ≤ m
  · have key : ∀ {t t' : Fin (n + 1) × S} (e : t = t') (y : B.1 t),
        PartialAlgebra.Hom.map f t' (DiscExt.tp (M := ⟨B.1, B.2.2⟩) e y) =
          DiscExt.tp (M := ⟨B'.1, B'.2.2⟩) e (PartialAlgebra.Hom.map f t y) := by
      intro t t' e; subst e; intro y; rfl
    exact (congrArg (PartialAlgebra.Hom.map f (k, s)) (up'_le (B := ⟨B.1, B.2.2⟩) hmn hk z)).trans
      ((key _ z).trans (up'_le (B := ⟨B'.1, B'.2.2⟩) hmn hk _).symm)
  · refine (congrArg (PartialAlgebra.Hom.map f (k, s)) (up'_gt (B := ⟨B.1, B.2.2⟩) hmn hk z)).trans
      (Eq.trans ?_ (up'_gt (B := ⟨B'.1, B'.2.2⟩) hmn hk _).symm)
    refine (PartialAlgebra.Hom.map_op f (.idm (cl_lt hmn hk) s) (Extended.arg₁ z)
      (idm_dom (M := ⟨B.1, B.2.2⟩) _ z)).trans (Part.get_eq_get_of_eq _ _ ?_)
    exact congrArg _ (by funext i; match i with | ⟨0, _⟩ => rfl)

lemma tpD_val {Am : Extended.ExtendedPAlg.{u, v, w} Sig (Fin (m + 1))} {t t' : Fin (n + 1) × S}
    (e : t = t') (e' : (lowE m t.1, t.2) = (lowE m t'.1, t'.2)) (y : DiscExt.DE n Am t) :
    (DiscExt.tp (M := DiscExt.model n Am) e y).1 = DiscExt.tp (M := Am) e' y.1 := by
  subst e; rfl

end ExtCounitHom₂
```

:::proposition (label := "discretization-truncation-ext-adjunction") (central := true) (title := "Extended discretization is left adjoint to extended truncation")
Let $`m \leq n`. $`\mathrm{D}^{\mathrm{ext}(n,m)} \dashv T^{\mathrm{ext}(m,n)}`, with unit the isomorphism
of Proposition `truncation-discretization-ext` and counit $`\varepsilon^{\mathrm{ext}}` whose component
at the sort $`(k, s)` is the identity if $`k \leq m` and $`\mathrm{i}^{(k,m)}_{s}` if $`k > m`.

```lean
section ExtCounitHom₂

variable {Sig n m} (hmn : m ≤ n)

/-- Extended discretization is left adjoint to extended truncation. -/
noncomputable def discTruncExtAdj :
    Adjunction (discExtFunctor Sig n m) (truncExtFunctor Sig hmn) :=
  Adjunction.mkOfUnitCounit
    { unit := (tdExtIso hmn).hom
      counit :=
        { app := tdExtCounit hmn
          naturality := fun _ _ f => PartialAlgebra.Hom.ext fun t z => (map_up' hmn f t.1 z.1.1).symm }
      left_triangle := by
        ext A ⟨k, s⟩ x
        apply Subtype.ext
        change (up' hmn (DiscExt.model n ⟨A.1, A.2.2⟩) k _).1 = x.1
        by_cases hk : k.val ≤ m
        · have e' : (lowE m (castDim hmn (lowE m k)), s) = (lowE m k, s) := by rw [lowE_castDim]
          exact (congrArg Subtype.val (up'_le hmn hk _)).trans ((tpD_val _ e' _).trans
            ((DiscExt.tp_tp (M := ⟨A.1, A.2.2⟩) _ e' _).trans rfl))
        · have hneg : ¬ (castDim hmn (lowE m k)).val < m := by
            simp only [castDim, lowE, Fin.coe_castLE]; omega
          exact (congrArg Subtype.val ((up'_gt hmn hk _).trans
            (DiscExt.idm_eq (M := ⟨A.1, A.2.2⟩) _ _))).trans
            ((DiscExt.eidm_neg (M := ⟨A.1, A.2.2⟩) (h := cl_lt hmn hk) hneg _).trans
              ((DiscExt.tp_tp (M := ⟨A.1, A.2.2⟩) _ _ _).trans rfl))
      right_triangle := by
        ext B ⟨a, s⟩ y
        apply Subtype.ext
        have hca : (castDim hmn a).val ≤ m := by
          have := a.isLt; simp only [castDim, Fin.coe_castLE]; omega
        have e'' : (castDim hmn (lowE m (castDim hmn a)), s) = (castDim hmn a, s) := by
          rw [lowE_castDim]
        have e3 : (castDim hmn a, s) = (castDim hmn (lowE m (castDim hmn a)), s) := by
          rw [lowE_castDim]
        exact (up'_le (B := ⟨B.1, B.2.2⟩) hmn hca _).trans
          ((congrArg (DiscExt.tp (M := ⟨B.1, B.2.2⟩) e'') (tp_val (Bm := ⟨B.1, B.2.2⟩) hmn (eK hmn a s) e3 y)).trans
          (DiscExt.tp_tp (M := ⟨B.1, B.2.2⟩) e3 e'' y.1)) }

end ExtCounitHom₂
```
:::

:::proof (of := "discretization-truncation-ext-adjunction")
By (EA$`^{m,k}`7), $`\mathrm{i}^{(k,m)}_{s}` commutes with the $`\sigma`'s. Let $`j < k` with $`k > m`. If
$`j < m`, then $`\mathrm{sc}^{(j,k)}_{s}(\mathrm{i}^{(k,m)}_{s}(x)) = \mathrm{sc}^{(j,m)}_{s}(x)`, by
(EA$`^{j,m,k}`1) and (EA$`^{m,k}`2), $`\mathrm{i}^{(k,m)}_{s}(\mathrm{i}^{(m,j)}_{s}(u)) = \mathrm{i}^{(k,j)}_{s}(u)`,
by (EA$`^{j,m,k}`2), and $`\mathrm{i}^{(k,m)}_{s}` preserves the $`j`-compositions, by (EA$`^{j,m,k}`5). If
$`j \geq m`, then $`\mathrm{i}^{(k,m)}_{s} = \mathrm{i}^{(k,j)}_{s} \circ \mathrm{i}^{(j,m)}_{s}`, so that
$`\mathrm{sc}^{(j,k)}_{s}(\mathrm{i}^{(k,m)}_{s}(x)) = \mathrm{i}^{(j,m)}_{s}(x)` and
$`\mathrm{i}^{(k,m)}_{s}(x) \circ^{(j,k)}_{s} \mathrm{i}^{(k,m)}_{s}(x) = \mathrm{i}^{(k,m)}_{s}(x)`, by
(EA$`^{j,k}`5). Hence $`\varepsilon^{\mathrm{ext}}_{\mathbf{B}}` is a homomorphism, natural because
homomorphisms commute with the identities. The triangle identities hold because
$`T^{\mathrm{ext}(m,n)}(\varepsilon^{\mathrm{ext}}_{\mathbf{B}})` is the identity and the
$`(k,m)`-identities of $`\mathrm{D}^{\mathrm{ext}(n,m)}(\mathbf{A})` are transports.
:::

```lean
end CategorialAlgebras
```
