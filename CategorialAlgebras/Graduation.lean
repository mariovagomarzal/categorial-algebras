import Stemma
import CategorialAlgebras.CategorialEp
import CategorialAlgebras.GenEpComposition
import CategorialAlgebras.DerivedEval

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "Graduation and unification" =>

A compact $`n`-categorial algebra keeps all its cells in a single set for every sort, whatever
their dimension; an extended one keeps the $`k`-cells in a sort of their own, for every
$`k \leq n`. Graduation distributes the cells of a compact algebra into sorts according to their
dimension, and unification keeps only the $`n`-cells of an extended algebra, in which every
$`k`-cell has been replaced by its identity $`n`-cell (Section `SGraduation` of the draft). Both
are induced by generalized ep-derivors between the ep-specifications of Document
`compact.ep-specification` and `extended.ep-specification`, and they are mutually quasi-inverse
equivalences of categories.

Throughout, $`\Sigma` is an $`S`-sorted signature and $`n \in \mathbb{N}`; the dimensions of the
compact presentation are the elements of $`n`, `Fin n` in the Lean, and those of the extended
presentation the elements of $`n + 1`, `Fin (n + 1)`.

```lean
universe u v w

namespace CategorialAlgebras

open Signature Term CategoryTheory

variable {S : Type u} (Sig : Signature.{u, v} S) (n : ℕ)

/-- The dimension `j ∈ n` of a `(j,k)`-source, for `j < k` in `n + 1`. -/
def lowDim {n : ℕ} {j k : Fin (n + 1)} (h : j < k) : Fin n :=
  ⟨j.val, by have := Fin.lt_def.mp h; have := k.isLt; omega⟩
```

# Graduation

Graduating a compact $`n`-categorial algebra $`\mathbf{B}` gives the extended algebra whose cells
of sort $`(k, s)`, for $`k \in n`, are the $`k`-cells of sort $`s` of $`\mathbf{B}`, the cells $`x`
with $`\mathrm{sc}^{k}_{s}(x) = x`, and whose cells of sort $`(n, s)` are all the cells of sort
$`s`. The $`(j,k)`-source and the $`(j,k)`-target of a $`k`-cell are its $`j`-source and its
$`j`-target, the $`(k,j)`-identity of a $`j`-cell is the cell itself, the $`j`-composition of two
$`k`-cells is their $`j`-composition, and $`\sigma_k` acts on $`k`-cells as $`\sigma`.

:::definition (label := "graduation-derivor") (central := false) (title := "The graduation derivor")
The *graduation derivor* $`\mathbf{g}^{(n)} = (\varphi, D, d)` is the generalized ep-derivor from
$`\mathbf{\Sigma}^{\mathrm{ext}(n)}` to $`\mathbf{\Sigma}^{(n)}` with $`\varphi(k, s) = s`,
$`D_{(k,s)} = \{\mathrm{sc}^{k}_{s}(v) \overset{\mathrm{e}}{=} v\}` for $`k \in n` and
$`D_{(n,s)} = \varnothing`, and, for $`j < k`,
$`d(\sigma_k) = \sigma((v_p)_p)`, $`d(\mathrm{sc}^{(j,k)}_{s}) = \mathrm{sc}^{j}_{s}(v_0)`,
$`d(\mathrm{tg}^{(j,k)}_{s}) = \mathrm{tg}^{j}_{s}(v_0)`, $`d(\mathrm{i}^{(k,j)}_{s}) = v_0` and
$`d(\circ^{(j,k)}_{s}) = v_0 \circ^{j}_{s} v_1`.

```lean
/-- The domains of the graduation derivor. -/
def gradDom (t : Fin (n + 1) × S) :
    Set (EEq (Compact.CompactSignature Sig (Fin n)) (Vars fun _ : Unit => t.2)) :=
  if hk : t.1.val < n then
    {EEq.mk' (app₁ (.sc ⟨t.1.val, hk⟩ t.2) (.var ⟨(), rfl⟩)) (.var ⟨(), rfl⟩)}
  else ∅

/-- The terms of the graduation derivor. -/
def gradOp : ∀ {ws : List (Fin (n + 1) × S)} {t : Fin (n + 1) × S},
    Extended.ExtendedSignature Sig (Fin (n + 1)) ws t →
    Term (Compact.CompactSignature Sig (Fin n)) (Vars (Prod.snd ∘ ws.get)) t.2
  | _, _, .op _ σ => .app (.op σ) fun p => .var ⟨Fin.cast (by simp) p, by simp⟩
  | _, _, .sc h s => app₁ (.sc (lowDim h) s) (.var ⟨⟨0, by simp⟩, rfl⟩)
  | _, _, .tg h s => app₁ (.tg (lowDim h) s) (.var ⟨⟨0, by simp⟩, rfl⟩)
  | _, _, .idm _ _ => .var ⟨⟨0, by simp⟩, rfl⟩
  | _, _, .comp h s =>
      app₂ (.comp (lowDim h) s) (.var ⟨⟨0, by simp⟩, rfl⟩) (.var ⟨⟨1, by simp⟩, rfl⟩)

/-- The graduation derivor `𝐠⁽ⁿ⁾`. -/
def grad : GenEpDerivor (extendedEpSig Sig (Fin (n + 1))) (compactEpSig Sig (Fin n)) where
  sortMap := Prod.snd
  sortDom := gradDom Sig n
  op := gradOp Sig n
```
:::

The graduated algebra $`(\mathbf{g}^{(n)})^{\ast}_{\mathfrak{gd}}(\mathbf{B})` of a model
$`\mathbf{B}` is computed below: its operations are those described at the beginning of this
section, and its domains are those of an ep-algebra.

```lean
namespace Grad

open Compact.CategoryStruct

variable {Sig n} (M : Compact.CompactPAlg.{u, v, w} Sig (Fin n))

/-- The cells of the graduated algebra. -/
noncomputable abbrev D := (grad Sig n).derived M.1

variable {M}

lemma dom_iff {k : Fin (n + 1)} (hk : k.val < n) {s : S} (b : M.1 s) :
    EEq.HoldsAll M.1 (val₁ b) (gradDom Sig n (k, s)) ↔ Compact.msc M ⟨k.val, hk⟩ b = b := by
  simp only [gradDom, dif_pos hk]
  rw [EEq.holdsAll_singleton, EEq.holds_mk'_iff (Compact.eval_sc rfl) rfl]

lemma dom_top {k : Fin (n + 1)} (hk : ¬ k.val < n) {s : S} (b : M.1 s) :
    EEq.HoldsAll M.1 (val₁ b) (gradDom Sig n (k, s)) := by
  simp only [gradDom, dif_neg hk]; exact EEq.holdsAll_empty

lemma isCell {k : Fin (n + 1)} {s : S} (x : D M (k, s)) (hk : k.val < n) :
    Compact.msc M ⟨k.val, hk⟩ x.1 = x.1 :=
  (dom_iff hk x.1).mp x.2

variable (M) in
/-- The `(j,k)`-source of the graduated algebra. -/
def gsc {j k : Fin (n + 1)} (h : j < k) {s : S} (x : D M (k, s)) : D M (j, s) :=
  ⟨Compact.msc M (lowDim h) x.1, (dom_iff (lowDim h).isLt _).mpr (Compact.model_sc_sc _)⟩

variable (M) in
/-- The `(j,k)`-target of the graduated algebra. -/
def gtg {j k : Fin (n + 1)} (h : j < k) {s : S} (x : D M (k, s)) : D M (j, s) :=
  ⟨Compact.mtg M (lowDim h) x.1, (dom_iff (lowDim h).isLt _).mpr (Compact.model_sc_tg _)⟩

lemma lowDim_lt {j k : Fin (n + 1)} (h : j < k) (hk : k.val < n) :
    lowDim h < (⟨k.val, hk⟩ : Fin n) :=
  Fin.lt_def.mpr (Fin.lt_def.mp h)

variable (M) in
/-- The `(k,j)`-identity of the graduated algebra: the inclusion of `j`-cells. -/
def gidm {j k : Fin (n + 1)} (h : j < k) {s : S} (u : D M (j, s)) : D M (k, s) :=
  ⟨u.1, by
    by_cases hk : k.val < n
    · refine (dom_iff hk _).mpr ?_
      calc Compact.msc M ⟨k.val, hk⟩ u.1
          = Compact.msc M ⟨k.val, hk⟩ (Compact.msc M (lowDim h) u.1) :=
            congrArg _ (isCell u (lowDim h).isLt).symm
        _ = Compact.msc M (lowDim h) u.1 := Compact.model_sc_k_sc_l _ (lowDim_lt h hk)
        _ = u.1 := isCell u (lowDim h).isLt
    · exact dom_top hk _⟩

variable (M) in
/-- The `j`-composite of two `k`-cells of the graduated algebra. -/
def gcomp {j k : Fin (n + 1)} (h : j < k) {s : S} (x y : D M (k, s))
    (hxy : sc_is_tg (lowDim h) x.1 y.1) : D M (k, s) :=
  ⟨comp (lowDim h) x.1 y.1 hxy, by
    by_cases hk : k.val < n
    · refine (dom_iff hk _).mpr ?_
      have hd : (pcomp (lowDim h) (Compact.msc M ⟨k.val, hk⟩ x.1)
          (Compact.msc M ⟨k.val, hk⟩ y.1)).Dom := by
        rw [isCell x hk, isCell y hk]; exact dom_of_sc_is_tg hxy
      refine (Compact.model_sc_comp_l (lowDim_lt h hk) hxy hd).trans ?_
      exact Part.get_eq_get_of_eq _ _ (congrArg₂ (pcomp (lowDim h)) (isCell x hk) (isCell y hk))
    · exact dom_top hk _⟩

variable (M) in
/-- The copy `σ_k` of the graduated algebra. -/
def gop (k : Fin (n + 1)) {ws : List S} {s : S} (σ : Sig ws s) (b : ∀ p, D M (k, ws.get p)) :
    D M (k, s) :=
  ⟨Compact.mop M σ fun p => (b p).1, by
    by_cases hk : k.val < n
    · refine (dom_iff hk _).mpr ?_
      refine ((Compact.modelOp M σ).map_sc_eq_sc_map ⟨k.val, hk⟩ fun p => (b p).1).symm.trans ?_
      exact congrArg (Compact.mop M σ) (funext fun p => isCell (b p) hk)
    · exact dom_top hk _⟩

/-! ### The operations of the graduated algebra -/

lemma op_sc {j k : Fin (n + 1)} (h : j < k) {s : S} (x : D M (k, s)) :
    (D M).op (.sc h s) (Extended.arg₁ x) = Part.some (gsc M h x) :=
  (grad Sig n).derived_op_eq_some EEq.holdsAll_empty (Compact.eval_sc rfl) _

lemma op_tg {j k : Fin (n + 1)} (h : j < k) {s : S} (x : D M (k, s)) :
    (D M).op (.tg h s) (Extended.arg₁ x) = Part.some (gtg M h x) :=
  (grad Sig n).derived_op_eq_some EEq.holdsAll_empty (Compact.eval_tg rfl) _

lemma op_idm {j k : Fin (n + 1)} (h : j < k) {s : S} (u : D M (j, s)) :
    (D M).op (.idm h s) (Extended.arg₁ u) = Part.some (gidm M h u) :=
  (grad Sig n).derived_op_eq_some EEq.holdsAll_empty rfl _

lemma eval_var_lift (k : Fin (n + 1)) {ws : List S} (b : ∀ p, D M (k, ws.get p))
    (p : Fin ws.length) (hp) :
    (Term.var ⟨Fin.cast (by simp) p, hp⟩ :
        Term (Compact.CompactSignature Sig (Fin n))
          (Vars (Prod.snd ∘ (ws.map fun t => (k, t)).get)) (ws.get p)).eval M.1
      (famVal fun q => (Extended.liftFam k b q).1) = Part.some (b p).1 := by
  have key : ∀ {t'} (e : (k, ws.get p) = t') (hq : t'.2 = ws.get p),
      hq ▸ (cast (congrArg (D M) e) (b p)).1 = (b p).1 := by
    rintro _ rfl _; rfl
  exact congrArg Part.some (key (by simp) hp)

lemma op_op (k : Fin (n + 1)) {ws : List S} {s : S} (σ : Sig ws s) (b : ∀ p, D M (k, ws.get p)) :
    (D M).op (.op k σ) (Extended.liftFam k b) = Part.some (gop M k σ b) :=
  (grad Sig n).derived_op_eq_some EEq.holdsAll_empty
    (Compact.eval_op σ fun p => eval_var_lift k b p _) _

lemma eval_sc_var {j k : Fin (n + 1)} (h : j < k) {s : S} (x y : D M (k, s)) :
    (app₁ (.sc h s) (.var ⟨⟨0, by simp⟩, rfl⟩) :
        Term (Extended.ExtendedSignature Sig (Fin (n + 1))) (Vars [(k, s), (k, s)].get) (j, s)).eval
      (D M) (famVal (Extended.arg₂ x y)) = Part.some (gsc M h x) :=
  (Extended.eval_app₁ _ rfl).trans (op_sc h x)

lemma eval_tg_var {j k : Fin (n + 1)} (h : j < k) {s : S} (x y : D M (k, s)) :
    (app₁ (.tg h s) (.var ⟨⟨1, by simp⟩, rfl⟩) :
        Term (Extended.ExtendedSignature Sig (Fin (n + 1))) (Vars [(k, s), (k, s)].get) (j, s)).eval
      (D M) (famVal (Extended.arg₂ x y)) = Part.some (gtg M h y) :=
  (Extended.eval_app₁ _ rfl).trans (op_tg h y)

lemma comp_defn_iff {j k : Fin (n + 1)} (h : j < k) {s : S} (x y : D M (k, s)) :
    EEq.HoldsAll (D M) (famVal (Extended.arg₂ x y)) ((extendedEpSig Sig (Fin (n + 1))).defn
      (.comp h s)) ↔ sc_is_tg (lowDim h) x.1 y.1 := by
  refine EEq.holdsAll_singleton.trans ?_
  refine (EEq.holds_mk'_iff (eval_sc_var h x y) (eval_tg_var h x y)).trans ?_
  exact ⟨fun e => congrArg Subtype.val e, fun e => Subtype.ext e⟩

lemma op_comp {j k : Fin (n + 1)} (h : j < k) {s : S} (x y : D M (k, s))
    (hxy : sc_is_tg (lowDim h) x.1 y.1) :
    (D M).op (.comp h s) (Extended.arg₂ x y) = Part.some (gcomp M h x y hxy) :=
  (grad Sig n).derived_op_eq_some ((comp_defn_iff h x y).mpr hxy) (Compact.eval_comp rfl rfl hxy) _

lemma op_comp_dom {j k : Fin (n + 1)} (h : j < k) {s : S} (x y : D M (k, s)) :
    ((D M).op (.comp h s) (Extended.arg₂ x y)).Dom ↔ sc_is_tg (lowDim h) x.1 y.1 :=
  ⟨fun hd => (comp_defn_iff h x y).mp (((grad Sig n).op_derived_dom_iff _ _).mp hd).1,
    fun hxy => by rw [op_comp h x y hxy]; trivial⟩

theorem isAlgebra : (extendedEpSig Sig (Fin (n + 1))).IsAlgebra (D M) := by
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

/-! ### Values of terms in the graduated algebra -/

section Eval

variable {val : ∀ t, Extended.EVar S (Fin (n + 1)) t → Part ((D M) t)}

lemma ev_scT {j k : Fin (n + 1)} (h : j < k) {s : S} {t : Extended.ETerm Sig (Fin (n + 1)) (k, s)}
    {x : D M (k, s)} (ht : t.eval (D M) val = Part.some x) :
    (Extended.ETerm.scT h t).eval (D M) val = Part.some (gsc M h x) :=
  (Extended.eval_app₁ _ ht).trans (op_sc h x)

lemma ev_tgT {j k : Fin (n + 1)} (h : j < k) {s : S} {t : Extended.ETerm Sig (Fin (n + 1)) (k, s)}
    {x : D M (k, s)} (ht : t.eval (D M) val = Part.some x) :
    (Extended.ETerm.tgT h t).eval (D M) val = Part.some (gtg M h x) :=
  (Extended.eval_app₁ _ ht).trans (op_tg h x)

lemma ev_idmT {j k : Fin (n + 1)} (h : j < k) {s : S} {t : Extended.ETerm Sig (Fin (n + 1)) (j, s)}
    {u : D M (j, s)} (ht : t.eval (D M) val = Part.some u) :
    (Extended.ETerm.idmT h t).eval (D M) val = Part.some (gidm M h u) :=
  (Extended.eval_app₁ _ ht).trans (op_idm h u)

lemma ev_compT {j k : Fin (n + 1)} (h : j < k) {s : S}
    {t t' : Extended.ETerm Sig (Fin (n + 1)) (k, s)} {x y : D M (k, s)}
    (ht : t.eval (D M) val = Part.some x) (ht' : t'.eval (D M) val = Part.some y)
    (hxy : sc_is_tg (lowDim h) x.1 y.1) :
    (Extended.ETerm.compT h t t').eval (D M) val = Part.some (gcomp M h x y hxy) :=
  (Extended.eval_app₂ _ ht ht').trans (op_comp h x y hxy)

lemma ev_compT_dom {j k : Fin (n + 1)} (h : j < k) {s : S}
    {t t' : Extended.ETerm Sig (Fin (n + 1)) (k, s)} {x y : D M (k, s)}
    (ht : t.eval (D M) val = Part.some x) (ht' : t'.eval (D M) val = Part.some y)
    (hd : ((Extended.ETerm.compT h t t').eval (D M) val).Dom) : sc_is_tg (lowDim h) x.1 y.1 :=
  (op_comp_dom h x y).mp ((Extended.eval_app₂ _ ht ht') ▸ hd)

lemma ev_opT (k : Fin (n + 1)) {ws : List S} {s : S} (σ : Sig ws s)
    {ts : (p : Fin ws.length) → Extended.ETerm Sig (Fin (n + 1)) (k, ws.get p)}
    {b : ∀ p, D M (k, ws.get p)} (h : ∀ p, (ts p).eval (D M) val = Part.some (b p)) :
    (Extended.ETerm.opT k σ ts).eval (D M) val = Part.some (gop M k σ b) :=
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
theorem holds : ∀ q ∈ Extended.extendedSpec Sig (Fin (n + 1)), q.Holds (D M) := by
  intro q hq val hvars hprem
  have var : ∀ {t : Fin (n + 1) × S} (i : ℕ),
      (⟨t, i⟩ : Σ t, Extended.EVar S (Fin (n + 1)) t) ∈ q.vars →
      ∃ x, (Extended.ETerm.x (Sig := Sig) (t := t) i).eval (D M) val = Part.some x :=
    fun i hi => ⟨_, (Part.some_get (hvars _ hi)).symm⟩
  have prem : ∀ e ∈ q.premises, e.Holds (D M) val := hprem
  have ll : ∀ {a b c : Fin (n + 1)} (h₁ : a < b) (h₂ : b < c), lowDim h₁ < lowDim h₂ :=
    fun h₁ _ => Fin.lt_def.mpr (Fin.lt_def.mp h₁)
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
    exact (EEq.holds_mk'_iff (ev_scT h (ev_idmT h hu)) hu).mpr (Subtype.ext (isCell u _))
  | @EA2_tg j k h s i =>
    obtain ⟨u, hu⟩ := var (t := (j, s)) i (by vm)
    refine (EEq.holds_mk'_iff (ev_tgT h (ev_idmT h hu)) hu).mpr (Subtype.ext ?_)
    change Compact.mtg M (lowDim h) u.1 = u.1
    calc Compact.mtg M (lowDim h) u.1
        = Compact.mtg M (lowDim h) (Compact.msc M (lowDim h) u.1) :=
          congrArg _ (isCell u (lowDim h).isLt).symm
      _ = u.1 := (Compact.model_tg_sc _).trans (isCell u _)
  | @EA3_dom j k h s i i' =>
    obtain ⟨a, ha⟩ := var (t := (k, s)) i (by vm)
    obtain ⟨b, hb⟩ := var (t := (k, s)) i' (by vm)
    have hab := ev_compT_dom h ha hb (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_scT h ha) (ev_tgT h hb)).mpr (Subtype.ext hab)
  | @EA3_def j k h s i i' =>
    obtain ⟨a, ha⟩ := var (t := (k, s)) i (by vm)
    obtain ⟨b, hb⟩ := var (t := (k, s)) i' (by vm)
    have hab : sc_is_tg (lowDim h) a.1 b.1 := congrArg Subtype.val
      ((EEq.holds_mk'_iff (ev_scT h ha) (ev_tgT h hb)).mp (prem _ (by pm)))
    exact EEq.holds_defined_iff.mpr (Part.eq_some_iff.mp (ev_compT h ha hb hab)).1
  | @EA4_sc j k h s i i' =>
    obtain ⟨a, ha⟩ := var (t := (k, s)) i (by vm)
    obtain ⟨b, hb⟩ := var (t := (k, s)) i' (by vm)
    have hab := ev_compT_dom h ha hb (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_scT h (ev_compT h ha hb hab)) (ev_scT h hb)).mpr
      (Subtype.ext (Compact.model_sc_comp hab))
  | @EA4_tg j k h s i i' =>
    obtain ⟨a, ha⟩ := var (t := (k, s)) i (by vm)
    obtain ⟨b, hb⟩ := var (t := (k, s)) i' (by vm)
    have hab := ev_compT_dom h ha hb (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_tgT h (ev_compT h ha hb hab)) (ev_tgT h ha)).mpr
      (Subtype.ext (Compact.model_tg_comp hab))
  | @EA5_sc j k h s i =>
    obtain ⟨a, ha⟩ := var (t := (k, s)) i (by vm)
    exact (EEq.holds_mk'_iff (ev_compT h ha (ev_idmT h (ev_scT h ha)) (Compact.model_tg_sc a.1).symm)
      ha).mpr (Subtype.ext (Compact.model_comp_sc a.1))
  | @EA5_tg j k h s i =>
    obtain ⟨a, ha⟩ := var (t := (k, s)) i (by vm)
    exact (EEq.holds_mk'_iff (ev_compT h (ev_idmT h (ev_tgT h ha)) ha (Compact.model_sc_tg a.1))
      ha).mpr (Subtype.ext (Compact.model_tg_comp_self a.1))
  | @EA6 j k h s i i' i'' =>
    obtain ⟨a, ha⟩ := var (t := (k, s)) i (by vm)
    obtain ⟨b, hb⟩ := var (t := (k, s)) i' (by vm)
    obtain ⟨c, hc⟩ := var (t := (k, s)) i'' (by vm)
    have hab := ev_compT_dom h ha hb (EEq.holds_defined_iff.mp (prem _ (by pm)))
    have hbc := ev_compT_dom h hb hc (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff
      (ev_compT h (ev_compT h ha hb hab) hc ((Compact.model_sc_comp hab).trans hbc))
      (ev_compT h ha (ev_compT h hb hc hbc) (hab.trans (Compact.model_tg_comp hbc).symm))).mpr
      (Subtype.ext (Compact.model_assoc hbc hab))
  | @EA7_sc j k h ws s σ xs =>
    choose b hb using fun p => var (t := (k, ws.get p)) (xs p) (by vm; exact ⟨p, rfl, rfl⟩)
    exact (EEq.holds_mk'_iff (ev_scT h (ev_opT k σ hb)) (ev_opT j σ fun p => ev_scT h (hb p))).mpr
      (Subtype.ext ((Compact.modelOp M σ).map_sc_eq_sc_map (lowDim h) _).symm)
  | @EA7_tg j k h ws s σ xs =>
    choose b hb using fun p => var (t := (k, ws.get p)) (xs p) (by vm; exact ⟨p, rfl, rfl⟩)
    exact (EEq.holds_mk'_iff (ev_tgT h (ev_opT k σ hb)) (ev_opT j σ fun p => ev_tgT h (hb p))).mpr
      (Subtype.ext ((Compact.modelOp M σ).map_tg_eq_tg_map (lowDim h) _).symm)
  | @EA7_idm j k h ws s σ us =>
    choose b hb using fun p => var (t := (j, ws.get p)) (us p) (by vm; exact ⟨p, rfl, rfl⟩)
    exact (EEq.holds_mk'_iff (ev_idmT h (ev_opT j σ hb)) (ev_opT k σ fun p => ev_idmT h (hb p))).mpr
      (Subtype.ext rfl)
  | @EA8 j k h ws s σ xs ys =>
    choose a ha using fun p => var (t := (k, ws.get p)) (xs p)
      (by vm; exact Or.inl (Or.inr (Or.inl ⟨p, rfl, rfl⟩)))
    choose b hb using fun p => var (t := (k, ws.get p)) (ys p)
      (by vm; exact Or.inl (Or.inr (Or.inr ⟨p, rfl, rfl⟩)))
    have hab : ∀ p, sc_is_tg (lowDim h) (a p).1 (b p).1 := fun p =>
      ev_compT_dom h (ha p) (hb p) (EEq.holds_defined_iff.mp (prem _ (List.mem_ofFn.mpr ⟨p, rfl⟩)))
    exact (EEq.holds_mk'_iff (ev_opT k σ fun p => ev_compT h (ha p) (hb p) (hab p))
      (ev_compT h (ev_opT k σ ha) (ev_opT k σ hb)
        ((Compact.modelOp M σ).comp_map (Compact.pi_sc_is_tg.mpr hab)))).mpr
      (Subtype.ext ((Compact.modelOp M σ).map_comp_eq_comp_map (Compact.pi_sc_is_tg.mpr hab)))
  | @EA1'_sc_sc a b c h₁ h₂ s i =>
    obtain ⟨x, hx⟩ := var (t := (c, s)) i (by vm)
    exact (EEq.holds_mk'_iff (ev_scT h₁ (ev_scT h₂ hx)) (ev_scT (h₁.trans h₂) hx)).mpr
      (Subtype.ext (Compact.model_sc_l_sc_k x.1 (ll h₁ h₂)))
  | @EA1'_tg_tg a b c h₁ h₂ s i =>
    obtain ⟨x, hx⟩ := var (t := (c, s)) i (by vm)
    exact (EEq.holds_mk'_iff (ev_tgT h₁ (ev_tgT h₂ hx)) (ev_tgT (h₁.trans h₂) hx)).mpr
      (Subtype.ext (Compact.model_tg_l_tg_k x.1 (ll h₁ h₂)))
  | @EA1'_sc_tg a b c h₁ h₂ s i =>
    obtain ⟨x, hx⟩ := var (t := (c, s)) i (by vm)
    exact (EEq.holds_mk'_iff (ev_scT h₁ (ev_tgT h₂ hx)) (ev_scT (h₁.trans h₂) hx)).mpr
      (Subtype.ext (Compact.model_sc_l_tg_k x.1 (ll h₁ h₂)))
  | @EA1'_tg_sc a b c h₁ h₂ s i =>
    obtain ⟨x, hx⟩ := var (t := (c, s)) i (by vm)
    exact (EEq.holds_mk'_iff (ev_tgT h₁ (ev_scT h₂ hx)) (ev_tgT (h₁.trans h₂) hx)).mpr
      (Subtype.ext (Compact.model_tg_l_sc_k x.1 (ll h₁ h₂)))
  | @EA2' a b c h₁ h₂ s i =>
    obtain ⟨u, hu⟩ := var (t := (a, s)) i (by vm)
    exact (EEq.holds_mk'_iff (ev_idmT h₂ (ev_idmT h₁ hu)) (ev_idmT (h₁.trans h₂) hu)).mpr (Subtype.ext rfl)
  | @EA3'_sc a b c h₁ h₂ s i i' =>
    obtain ⟨x, hx⟩ := var (t := (c, s)) i (by vm)
    obtain ⟨y, hy⟩ := var (t := (c, s)) i' (by vm)
    have hxy := ev_compT_dom (h₁.trans h₂) hx hy (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_scT h₂ (ev_compT (h₁.trans h₂) hx hy hxy))
      (ev_compT h₁ (ev_scT h₂ hx) (ev_scT h₂ hy) (Compact.Category.sc_tg_j_sc (ll h₁ h₂) hxy))).mpr
      (Subtype.ext (Compact.Category.sck_compj_eq_compj_sck (ll h₁ h₂) hxy))
  | @EA3'_tg a b c h₁ h₂ s i i' =>
    obtain ⟨x, hx⟩ := var (t := (c, s)) i (by vm)
    obtain ⟨y, hy⟩ := var (t := (c, s)) i' (by vm)
    have hxy := ev_compT_dom (h₁.trans h₂) hx hy (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_tgT h₂ (ev_compT (h₁.trans h₂) hx hy hxy))
      (ev_compT h₁ (ev_tgT h₂ hx) (ev_tgT h₂ hy) (Compact.Category.sc_tg_j_tg (ll h₁ h₂) hxy))).mpr
      (Subtype.ext (Compact.Category.tgk_compj_eq_compj_tgk (ll h₁ h₂) hxy))
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
        (Compact.Category.sc_tg_j_interchange (ll h₁ h₂) hxy hzt hxz))
      (ev_compT h₂ (ev_compT (h₁.trans h₂) hx hz hxz) (ev_compT (h₁.trans h₂) hy ht hyt)
        (Compact.Category.sc_tg_k_interchange (ll h₁ h₂) hxy hzt hxz hyt))).mpr
      (Subtype.ext (Compact.Category.interchange (ll h₁ h₂) hxy hzt hxz hyt).symm)
  | @EA5' a b c h₁ h₂ s i i' =>
    obtain ⟨u, hu⟩ := var (t := (b, s)) i (by vm)
    obtain ⟨v, hv⟩ := var (t := (b, s)) i' (by vm)
    have huv := ev_compT_dom h₁ hu hv (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_idmT h₂ (ev_compT h₁ hu hv huv))
      (ev_compT (h₁.trans h₂) (ev_idmT h₂ hu) (ev_idmT h₂ hv) huv)).mpr (Subtype.ext rfl)

end Grad
```

:::proposition (label := "graduation-models") (central := false) (title := "Graduation sends models to models")
$`(\mathbf{g}^{(n)})^{\ast}_{\mathfrak{gd}}` sends the models of
$`(\mathbf{\Sigma}^{(n)}, \mathcal{C}^{\Sigma^{(n)}})` to models of
$`(\mathbf{\Sigma}^{\mathrm{ext}(n)}, \mathcal{C}^{\Sigma^{\mathrm{ext}(n)}})`.

```lean
theorem grad_sendsModels :
    (grad Sig n).SendsModels.{u, max u v, u, max u v, w}
      (Extended.extendedSpec Sig (Fin (n + 1))) (Compact.compactSpec Sig (Fin n)) :=
  fun B hB => ⟨Grad.isAlgebra (M := ⟨B, hB.2⟩), Grad.holds (M := ⟨B, hB.2⟩)⟩
```
:::

:::proof (of := "graduation-models")
Let $`\mathbf{B}` be a model and $`\mathbf{A} = (\mathbf{g}^{(n)})^{\ast}_{\mathfrak{gd}}(\mathbf{B})`.
The terms $`d(\sigma_k)`, $`d(\mathrm{sc}^{(j,k)}_{s})`, $`d(\mathrm{tg}^{(j,k)}_{s})` and
$`d(\mathrm{i}^{(k,j)}_{s})` are defined in $`\mathbf{B}`, and their values are cells of the right
sort: if the $`x_p` are $`k`-cells, so is $`\sigma((x_p)_p)`, by (A$`^{k}`7); the $`j`-source and
the $`j`-target of a cell are $`j`-cells, by (A$`^{j}`2); and a $`j`-cell is a $`k`-cell, for
$`j < k`, by (AB$`^{j,k}`1). Hence these operations are total in $`\mathbf{A}`, and two $`k`-cells
satisfy the domain condition of $`\circ^{(j,k)}_{s}` in $`\mathbf{A}` if and only if
$`\mathrm{sc}^{j}_{s}(x) = \mathrm{tg}^{j}_{s}(y)`; then $`x \circ^{j}_{s} y` is defined, by
(A$`^{j}`3), and it is a $`k`-cell, by (AB$`^{j,k}`2). So $`\mathbf{A}` is an ep-algebra. Under this
description, every axiom of $`\mathcal{C}^{\Sigma^{\mathrm{ext}(n)}}` becomes an axiom of
$`\mathcal{C}^{\Sigma^{(n)}}`, or a trivial equation: (EA$`^{j,k}`2) becomes
$`\mathrm{sc}^{j}_{s}(u) = u = \mathrm{tg}^{j}_{s}(u)` for a $`j`-cell $`u`, (EA$`^{j,k}`3)–(EA$`^{j,k}`8)
become (A$`^{j}`3)–(A$`^{j}`8), (EA$`^{h,j,k}`1), (EA$`^{h,j,k}`3) and (EA$`^{h,j,k}`4) become
(AB$`^{h,j}`1), (AB$`^{h,j}`2) and (AB$`^{h,j}`3), and (EA$`^{h,j,k}`2), (EA$`^{h,j,k}`5) and the last
equation of (EA$`^{j,k}`7) become trivial.
:::

:::definition (label := "graduation-functor") (central := false) (title := "The graduation functor")
The *graduation functor* $`\mathrm{Gd}^{(n)}` is the birestriction of
$`(\mathbf{g}^{(n)})^{\ast}_{\mathfrak{gd}}` to the categories of models, from
$`\mathsf{PAlg}(\mathcal{C}^{\Sigma^{(n)}})` to $`\mathsf{PAlg}(\mathcal{C}^{\Sigma^{\mathrm{ext}(n)}})`.

```lean
/-- The graduation functor `Gd⁽ⁿ⁾`. -/
noncomputable def gradFunctor :
    EpSpec.EpAlg.{u, max u v, w} (compactEpSpec Sig (Fin n)) ⥤
      EpSpec.EpAlg.{u, max u v, w} (extendedEpSpec Sig (Fin (n + 1))) :=
  (grad Sig n).restrict (grad_sendsModels Sig n)
```
:::

# Unification

Unifying an extended $`n`-categorial algebra $`\mathbf{A}` keeps only its $`n`-cells: the
$`k`-source of an $`n`-cell is the $`(n,k)`-identity of its $`(k,n)`-source, the $`k`-composition
is the $`k`-composition of $`n`-cells, and $`\sigma` acts as $`\sigma_n`.

:::definition (label := "unification-derivor") (central := false) (title := "The unification derivor")
The *unification derivor* $`\mathbf{u}^{(n)} = (\varphi, D, d)` is the generalized ep-derivor from
$`\mathbf{\Sigma}^{(n)}` to $`\mathbf{\Sigma}^{\mathrm{ext}(n)}` with $`\varphi(s) = (n, s)`,
$`D_s = \varnothing`, and, for $`k \in n`, $`d(\sigma) = \sigma_n((v_p)_p)`,
$`d(\mathrm{sc}^{k}_{s}) = \mathrm{i}^{(n,k)}_{s}(\mathrm{sc}^{(k,n)}_{s}(v_0))`,
$`d(\mathrm{tg}^{k}_{s}) = \mathrm{i}^{(n,k)}_{s}(\mathrm{tg}^{(k,n)}_{s}(v_0))` and
$`d(\circ^{k}_{s}) = v_0 \circ^{(k,n)}_{s} v_1`.

```lean
/-- The terms of the unification derivor. -/
def unifOp : ∀ {ws : List S} {s : S}, Compact.CompactSignature Sig (Fin n) ws s →
    Term (Extended.ExtendedSignature Sig (Fin (n + 1)))
      (Vars ((fun s => (Fin.last n, s)) ∘ ws.get)) (Fin.last n, s)
  | _, _, .op σ => .app (.op (Fin.last n) σ) fun q => .var ⟨Fin.cast (by simp) q, by simp⟩
  | _, _, .sc k s => app₁ (.idm (Fin.castSucc_lt_last k) s)
      (app₁ (.sc (Fin.castSucc_lt_last k) s) (.var ⟨⟨0, by simp⟩, rfl⟩))
  | _, _, .tg k s => app₁ (.idm (Fin.castSucc_lt_last k) s)
      (app₁ (.tg (Fin.castSucc_lt_last k) s) (.var ⟨⟨0, by simp⟩, rfl⟩))
  | _, _, .comp k s => app₂ (.comp (Fin.castSucc_lt_last k) s)
      (.var ⟨⟨0, by simp⟩, rfl⟩) (.var ⟨⟨1, by simp⟩, rfl⟩)

/-- The unification derivor `𝐮⁽ⁿ⁾`. -/
def unif : GenEpDerivor (compactEpSig Sig (Fin n)) (extendedEpSig Sig (Fin (n + 1))) where
  sortMap s := (Fin.last n, s)
  sortDom _ := ∅
  op := unifOp Sig n
```
:::

:::proposition (label := "unification-models") (central := false) (title := "Unification sends models to models")
$`(\mathbf{u}^{(n)})^{\ast}_{\mathfrak{gd}}` sends the models of
$`(\mathbf{\Sigma}^{\mathrm{ext}(n)}, \mathcal{C}^{\Sigma^{\mathrm{ext}(n)}})` to models of
$`(\mathbf{\Sigma}^{(n)}, \mathcal{C}^{\Sigma^{(n)}})`.

```lean
theorem unif_sendsModels :
    (unif Sig n).SendsModels.{u, max u v, u, max u v, w}
      (Compact.compactSpec Sig (Fin n)) (Extended.extendedSpec Sig (Fin (n + 1))) := by
  sorry
```
:::

:::definition (label := "unification-functor") (central := false) (title := "The unification functor")
The *unification functor* $`\mathrm{Uf}^{(n)}` is the birestriction of
$`(\mathbf{u}^{(n)})^{\ast}_{\mathfrak{gd}}` to the categories of models.

```lean
/-- The unification functor `Uf⁽ⁿ⁾`. -/
noncomputable def unifFunctor :
    EpSpec.EpAlg.{u, max u v, w} (extendedEpSpec Sig (Fin (n + 1))) ⥤
      EpSpec.EpAlg.{u, max u v, w} (compactEpSpec Sig (Fin n)) :=
  (unif Sig n).restrict (unif_sendsModels Sig n)
```
:::

```lean
end CategorialAlgebras
```
