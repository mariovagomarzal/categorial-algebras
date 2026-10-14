import Stemma
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

:::proposition (label := "discretization-models") (central := false) (title := "Compact discretization sends models to models")
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

```lean
end CategorialAlgebras
```
