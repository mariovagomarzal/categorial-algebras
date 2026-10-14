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

The unified algebra $`(\mathbf{u}^{(n)})^{\ast}_{\mathfrak{gd}}(\mathbf{A})` of a model
$`\mathbf{A}` is computed below. Its cells of sort $`s` are the $`n`-cells of sort $`s` of
$`\mathbf{A}`, and we write $`\overline{\mathrm{sc}}^{k}_{s}(x)` and $`\overline{\mathrm{tg}}^{k}_{s}(x)`
for $`\mathrm{i}^{(n,k)}_{s}(\mathrm{sc}^{(k,n)}_{s}(x))` and
$`\mathrm{i}^{(n,k)}_{s}(\mathrm{tg}^{(k,n)}_{s}(x))`.

```lean
namespace Unif

open Extended.Model

variable {Sig n} (M : Extended.ExtendedPAlg.{u, v, w} Sig (Fin (n + 1)))

/-- The unified algebra. -/
noncomputable abbrev U := (unif Sig n).derived M.1

variable {M}

/-- The dimension `n`. -/
abbrev top (k : Fin n) : k.castSucc < Fin.last n := Fin.castSucc_lt_last k

section MEval
variable {V : Fin (n + 1) × S → Type} {val : ∀ t, V t → Part (M.1 t)}

lemma meval_sc {j k : Fin (n + 1)} (h : j < k) {s : S}
    {r : Term (Extended.ExtendedSignature Sig (Fin (n + 1))) V (k, s)} {a : M.1 (k, s)}
    (hr : r.eval M.1 val = Part.some a) : (app₁ (.sc h s) r).eval M.1 val = Part.some (sc M h a) :=
  (Extended.eval_app₁ _ hr).trans (Part.some_get _).symm

lemma meval_tg {j k : Fin (n + 1)} (h : j < k) {s : S}
    {r : Term (Extended.ExtendedSignature Sig (Fin (n + 1))) V (k, s)} {a : M.1 (k, s)}
    (hr : r.eval M.1 val = Part.some a) : (app₁ (.tg h s) r).eval M.1 val = Part.some (tg M h a) :=
  (Extended.eval_app₁ _ hr).trans (Part.some_get _).symm

lemma meval_idm {j k : Fin (n + 1)} (h : j < k) {s : S}
    {r : Term (Extended.ExtendedSignature Sig (Fin (n + 1))) V (j, s)} {a : M.1 (j, s)}
    (hr : r.eval M.1 val = Part.some a) : (app₁ (.idm h s) r).eval M.1 val = Part.some (idm M h a) :=
  (Extended.eval_app₁ _ hr).trans (Part.some_get _).symm

lemma meval_comp {j k : Fin (n + 1)} (h : j < k) {s : S}
    {r r' : Term (Extended.ExtendedSignature Sig (Fin (n + 1))) V (k, s)} {a b : M.1 (k, s)}
    (hr : r.eval M.1 val = Part.some a) (hr' : r'.eval M.1 val = Part.some b)
    (hab : sc M h a = tg M h b) :
    (app₂ (.comp h s) r r').eval M.1 val = Part.some (comp M h a b hab) :=
  (Extended.eval_app₂ _ hr hr').trans (pcomp_eq hab)

end MEval

lemma op_eq_liftFam (k : Fin (n + 1)) {ws : List S} (b : ∀ p, M.1 (k, ws.get p)) (q) (hq) :
    (Term.var ⟨Fin.cast (by simp) q, hq⟩ :
        Term (Extended.ExtendedSignature Sig (Fin (n + 1)))
          (Vars ((fun s => (k, s)) ∘ ws.get)) ((ws.map fun t => (k, t)).get q)).eval M.1
      (famVal b) = Part.some (Extended.liftFam k b q) := by
  have key : ∀ {t t'} (e : t = t') (y : M.1 t), e ▸ y = cast (congrArg M.1 e) y := by
    rintro _ _ rfl _; rfl
  exact congrArg Part.some (key hq _)

variable (M) in
/-- The `k`-source of the unified algebra. -/
noncomputable def usc (k : Fin n) {s : S} (x : U M s) : U M s :=
  ⟨idm M (top k) (sc M (top k) x.1), EEq.holdsAll_empty⟩

variable (M) in
/-- The `k`-target of the unified algebra. -/
noncomputable def utg (k : Fin n) {s : S} (x : U M s) : U M s :=
  ⟨idm M (top k) (tg M (top k) x.1), EEq.holdsAll_empty⟩

variable (M) in
/-- The `k`-composite of the unified algebra. -/
noncomputable def ucomp (k : Fin n) {s : S} (x y : U M s)
    (hxy : sc M (top k) x.1 = tg M (top k) y.1) : U M s :=
  ⟨comp M (top k) x.1 y.1 hxy, EEq.holdsAll_empty⟩

variable (M) in
/-- The operations of `Σ` in the unified algebra. -/
noncomputable def uop {ws : List S} {s : S} (σ : Sig ws s) (a : Arity (U M) ws) : U M s :=
  ⟨op M (Fin.last n) σ fun p => (a p).1, EEq.holdsAll_empty⟩

lemma op_sc (k : Fin n) {s : S} (x : U M s) :
    (U M).op (.sc k s) (arityOne x) = Part.some (usc M k x) :=
  (unif Sig n).derived_op_eq_some EEq.holdsAll_empty (meval_idm _ (meval_sc _ rfl)) _

lemma op_tg (k : Fin n) {s : S} (x : U M s) :
    (U M).op (.tg k s) (arityOne x) = Part.some (utg M k x) :=
  (unif Sig n).derived_op_eq_some EEq.holdsAll_empty (meval_idm _ (meval_tg _ rfl)) _

lemma op_op {ws : List S} {s : S} (σ : Sig ws s) (a : Arity (U M) ws) :
    (U M).op (.op σ) a = Part.some (uop M σ a) :=
  (unif Sig n).derived_op_eq_some EEq.holdsAll_empty
    ((eval_app_of_eq_some _ _ _ fun q => op_eq_liftFam (Fin.last n) (fun p => (a p).1) q _).trans
      (Part.some_get _).symm) _

lemma comp_defn_iff (k : Fin n) {s : S} (x y : U M s) :
    EEq.HoldsAll (U M) (famVal (arityTwo x y)) ((compactEpSig Sig (Fin n)).defn (.comp k s)) ↔
      sc M (top k) x.1 = tg M (top k) y.1 := by
  refine EEq.holdsAll_singleton.trans ?_
  refine (EEq.holds_mk'_iff ((eval_app₁_arity _ rfl).trans (op_sc k x))
    ((eval_app₁_arity _ rfl).trans (op_tg k y))).trans ?_
  constructor
  · intro e
    have := congrArg (fun z : U M s => sc M (top k) z.1) e
    simpa only [usc, utg, sc_idm] using this
  · intro e
    exact Subtype.ext (congrArg (idm M (top k)) e)

lemma op_comp (k : Fin n) {s : S} (x y : U M s) (hxy : sc M (top k) x.1 = tg M (top k) y.1) :
    (U M).op (.comp k s) (arityTwo x y) = Part.some (ucomp M k x y hxy) :=
  (unif Sig n).derived_op_eq_some ((comp_defn_iff k x y).mpr hxy) (meval_comp _ rfl rfl hxy) _

lemma op_comp_dom (k : Fin n) {s : S} (x y : U M s) :
    ((U M).op (.comp k s) (arityTwo x y)).Dom ↔ sc M (top k) x.1 = tg M (top k) y.1 :=
  ⟨fun hd => (comp_defn_iff k x y).mp (((unif Sig n).op_derived_dom_iff _ _).mp hd).1,
    fun hxy => (Part.eq_some_iff.mp (op_comp k x y hxy)).1⟩

theorem isAlgebra : (compactEpSig Sig (Fin n)).IsAlgebra (U M) := by
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

/-! ### Values of terms in the unified algebra -/

section Eval

variable {val : ∀ s, Compact.Var S s → Part ((U M) s)}

lemma ev_scT (k : Fin n) {s : S} {t : Compact.CTerm Sig (Fin n) s} {x : U M s}
    (ht : t.eval (U M) val = Part.some x) :
    (Compact.CTerm.scT k t).eval (U M) val = Part.some (usc M k x) :=
  (eval_app₁_arity _ ht).trans (op_sc k x)

lemma ev_tgT (k : Fin n) {s : S} {t : Compact.CTerm Sig (Fin n) s} {x : U M s}
    (ht : t.eval (U M) val = Part.some x) :
    (Compact.CTerm.tgT k t).eval (U M) val = Part.some (utg M k x) :=
  (eval_app₁_arity _ ht).trans (op_tg k x)

lemma ev_compT (k : Fin n) {s : S} {t t' : Compact.CTerm Sig (Fin n) s} {x y : U M s}
    (ht : t.eval (U M) val = Part.some x) (ht' : t'.eval (U M) val = Part.some y)
    (hxy : sc M (top k) x.1 = tg M (top k) y.1) :
    (Compact.CTerm.compT k t t').eval (U M) val = Part.some (ucomp M k x y hxy) :=
  (eval_app₂_arity _ ht ht').trans (op_comp k x y hxy)

lemma ev_compT_dom (k : Fin n) {s : S} {t t' : Compact.CTerm Sig (Fin n) s} {x y : U M s}
    (ht : t.eval (U M) val = Part.some x) (ht' : t'.eval (U M) val = Part.some y)
    (hd : ((Compact.CTerm.compT k t t').eval (U M) val).Dom) :
    sc M (top k) x.1 = tg M (top k) y.1 :=
  (op_comp_dom k x y).mp ((eval_app₂_arity _ ht ht') ▸ hd)

lemma ev_opT {ws : List S} {s : S} (σ : Sig ws s)
    {ts : (j : Fin ws.length) → Compact.CTerm Sig (Fin n) (ws.get j)} {a : Arity (U M) ws}
    (h : ∀ j, (ts j).eval (U M) val = Part.some (a j)) :
    (Compact.CTerm.opT σ ts).eval (U M) val = Part.some (uop M σ a) :=
  (eval_app_of_eq_some _ _ _ h).trans (op_op σ a)

end Eval

lemma usc_eq_utg_iff (k : Fin n) {s : S} (x y : U M s) :
    usc M k x = utg M k y ↔ sc M (top k) x.1 = tg M (top k) y.1 := by
  constructor
  · intro e
    have := congrArg (fun z : U M s => sc M (top k) z.1) e
    simpa only [usc, utg, sc_idm] using this
  · intro e
    exact Subtype.ext (congrArg (idm M (top k)) e)

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
theorem holds : ∀ q ∈ Compact.compactSpec Sig (Fin n), q.Holds (U M) := by
  intro q hq val hvars hprem
  have var : ∀ {s : S} (i : ℕ), (⟨s, i⟩ : Σ t, Compact.Var S t) ∈ q.vars →
      ∃ x, (Compact.CTerm.x (Sig := Sig) (Index := Fin n) (s := s) i).eval (U M) val =
        Part.some x :=
    fun i hi => ⟨_, (Part.some_get (hvars _ hi)).symm⟩
  have prem : ∀ e ∈ q.premises, e.Holds (U M) val := hprem
  have ll : ∀ {l k : Fin n}, l < k → l.castSucc < k.castSucc :=
    fun h => Fin.castSucc_lt_castSucc_iff.mpr h
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
      (Subtype.ext (congrArg (idm M (top k)) (sc_idm _)))
  | A2_sc_tg k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_scT k (ev_tgT k ha)) (ev_tgT k ha)).mpr
      (Subtype.ext (congrArg (idm M (top k)) (sc_idm _)))
  | A2_tg_sc k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_tgT k (ev_scT k ha)) (ev_scT k ha)).mpr
      (Subtype.ext (congrArg (idm M (top k)) (tg_idm _)))
  | A2_tg_tg k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_tgT k (ev_tgT k ha)) (ev_tgT k ha)).mpr
      (Subtype.ext (congrArg (idm M (top k)) (tg_idm _)))
  | A3_dom k s i j =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    obtain ⟨b, hb⟩ := var (s := s) j (by vm)
    have hab := ev_compT_dom k ha hb (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_scT k ha) (ev_tgT k hb)).mpr ((usc_eq_utg_iff k a b).mpr hab)
  | A3_def k s i j =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    obtain ⟨b, hb⟩ := var (s := s) j (by vm)
    have hab := (usc_eq_utg_iff k a b).mp
      ((EEq.holds_mk'_iff (ev_scT k ha) (ev_tgT k hb)).mp (prem _ (by pm)))
    exact EEq.holds_defined_iff.mpr (Part.eq_some_iff.mp (ev_compT k ha hb hab)).1
  | A4_sc k s i j =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    obtain ⟨b, hb⟩ := var (s := s) j (by vm)
    have hab := ev_compT_dom k ha hb (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_scT k (ev_compT k ha hb hab)) (ev_scT k hb)).mpr
      (Subtype.ext (congrArg (idm M (top k)) (sc_comp hab)))
  | A4_tg k s i j =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    obtain ⟨b, hb⟩ := var (s := s) j (by vm)
    have hab := ev_compT_dom k ha hb (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_tgT k (ev_compT k ha hb hab)) (ev_tgT k ha)).mpr
      (Subtype.ext (congrArg (idm M (top k)) (tg_comp hab)))
  | A5_sc k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_compT k ha (ev_scT k ha) (tg_idm _).symm) ha).mpr
      (Subtype.ext (comp_idm_sc a.1))
  | A5_tg k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_compT k (ev_tgT k ha) ha (sc_idm _)) ha).mpr
      (Subtype.ext (idm_tg_comp a.1))
  | A6 k s i j l =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    obtain ⟨b, hb⟩ := var (s := s) j (by vm)
    obtain ⟨c, hc⟩ := var (s := s) l (by vm)
    have hab := ev_compT_dom k ha hb (EEq.holds_defined_iff.mp (prem _ (by pm)))
    have hbc := ev_compT_dom k hb hc (EEq.holds_defined_iff.mp (prem _ (by pm)))
    exact (EEq.holds_mk'_iff (ev_compT k (ev_compT k ha hb hab) hc ((sc_comp hab).trans hbc))
      (ev_compT k ha (ev_compT k hb hc hbc) (hab.trans (tg_comp hbc).symm))).mpr
      (Subtype.ext (comp_assoc hab hbc))
  | @A7_sc k ws s σ xs =>
    choose a ha using fun j => var (s := ws.get j) (xs j) (by vm; try exact ⟨j, rfl, rfl⟩)
    exact (EEq.holds_mk'_iff (ev_scT k (ev_opT σ ha)) (ev_opT σ fun j => ev_scT k (ha j))).mpr
      (Subtype.ext ((congrArg (idm M (top k)) (sc_op (top k) σ _)).trans (idm_op (top k) σ _)))
  | @A7_tg k ws s σ xs =>
    choose a ha using fun j => var (s := ws.get j) (xs j) (by vm; try exact ⟨j, rfl, rfl⟩)
    exact (EEq.holds_mk'_iff (ev_tgT k (ev_opT σ ha)) (ev_opT σ fun j => ev_tgT k (ha j))).mpr
      (Subtype.ext ((congrArg (idm M (top k)) (tg_op (top k) σ _)).trans (idm_op (top k) σ _)))
  | @A8 k ws s σ xs ys =>
    choose a ha using fun j => var (s := ws.get j) (xs j)
      (by vm; exact Or.inl (Or.inr (Or.inl ⟨j, rfl, rfl⟩)))
    choose b hb using fun j => var (s := ws.get j) (ys j)
      (by vm; exact Or.inl (Or.inr (Or.inr ⟨j, rfl, rfl⟩)))
    have hab : ∀ j, sc M (top k) (a j).1 = tg M (top k) (b j).1 := fun j =>
      ev_compT_dom k (ha j) (hb j) (EEq.holds_defined_iff.mp (prem _ (List.mem_ofFn.mpr ⟨j, rfl⟩)))
    exact (EEq.holds_mk'_iff (ev_opT σ fun j => ev_compT k (ha j) (hb j) (hab j))
      (ev_compT k (ev_opT σ ha) (ev_opT σ hb)
        ((sc_op (top k) σ _).trans ((congrArg (op M _ σ) (funext hab)).trans
          (tg_op (top k) σ _).symm)))).mpr
      (Subtype.ext (Extended.Model.op_comp (top k) σ _ _ hab))
  | AB1_sc_sc l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    refine (EEq.holds_mk'_iff (ev_scT k (ev_scT l ha)) (ev_scT l ha)).mpr (Subtype.ext ?_)
    change idm M (top k) (sc M (top k) (idm M (top l) (sc M (top l) a.1))) =
      idm M (top l) (sc M (top l) a.1)
    rw [← idm_idm (h₁ := ll h) (h₂ := top k), sc_idm, idm_idm]
  | AB1_tg_tg l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    refine (EEq.holds_mk'_iff (ev_tgT k (ev_tgT l ha)) (ev_tgT l ha)).mpr (Subtype.ext ?_)
    change idm M (top k) (tg M (top k) (idm M (top l) (tg M (top l) a.1))) =
      idm M (top l) (tg M (top l) a.1)
    rw [← idm_idm (h₁ := ll h) (h₂ := top k), tg_idm, idm_idm]
  | AB1_sc_sck l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_scT l (ev_scT k ha)) (ev_scT l ha)).mpr (Subtype.ext
      (congrArg (idm M (top l)) ((sc_idm_low (h₁ := ll h) (h₂ := top k) _).trans (sc_sc _))))
  | AB1_tg_tgk l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_tgT l (ev_tgT k ha)) (ev_tgT l ha)).mpr (Subtype.ext
      (congrArg (idm M (top l)) ((tg_idm_low (h₁ := ll h) (h₂ := top k) _).trans (tg_tg _))))
  | AB1_sc_tgk l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_scT l (ev_tgT k ha)) (ev_scT l ha)).mpr (Subtype.ext
      (congrArg (idm M (top l)) ((sc_idm_low (h₁ := ll h) (h₂ := top k) _).trans (sc_tg _))))
  | AB1_tg_sck l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    exact (EEq.holds_mk'_iff (ev_tgT l (ev_scT k ha)) (ev_tgT l ha)).mpr (Subtype.ext
      (congrArg (idm M (top l)) ((tg_idm_low (h₁ := ll h) (h₂ := top k) _).trans (tg_sc _))))
  | AB2_sc l k h s i j =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    obtain ⟨b, hb⟩ := var (s := s) j (by vm)
    have hab := ev_compT_dom l ha hb (EEq.holds_defined_iff.mp (prem _ (by pm)))
    have P : sc M (top l) (usc M k a).1 = tg M (top l) (usc M k b).1 :=
      (sc_idm_low (h₁ := ll h) (h₂ := top k) _).trans ((sc_sc (h₁ := ll h) (h₂ := top k) _).trans
        (hab.trans ((tg_sc (h₁ := ll h) (h₂ := top k) _).symm.trans
          (tg_idm_low (h₁ := ll h) (h₂ := top k) _).symm)))
    exact (EEq.holds_mk'_iff (ev_scT k (ev_compT l ha hb hab))
      (ev_compT l (ev_scT k ha) (ev_scT k hb) P)).mpr (Subtype.ext
      ((congrArg (idm M (top k)) (sc_comp' (h₁ := ll h) (h₂ := top k) hab)).trans (idm_comp _)))
  | AB2_tg l k h s i j =>
    obtain ⟨a, ha⟩ := var (s := s) i (by vm)
    obtain ⟨b, hb⟩ := var (s := s) j (by vm)
    have hab := ev_compT_dom l ha hb (EEq.holds_defined_iff.mp (prem _ (by pm)))
    have P : sc M (top l) (utg M k a).1 = tg M (top l) (utg M k b).1 :=
      (sc_idm_low (h₁ := ll h) (h₂ := top k) _).trans ((sc_tg (h₁ := ll h) (h₂ := top k) _).trans
        (hab.trans ((tg_tg (h₁ := ll h) (h₂ := top k) _).symm.trans
          (tg_idm_low (h₁ := ll h) (h₂ := top k) _).symm)))
    exact (EEq.holds_mk'_iff (ev_tgT k (ev_compT l ha hb hab))
      (ev_compT l (ev_tgT k ha) (ev_tgT k hb) P)).mpr (Subtype.ext
      ((congrArg (idm M (top k)) (tg_comp' (h₁ := ll h) (h₂ := top k) hab)).trans (idm_comp _)))
  | AB3 l k h s i j p q =>
    obtain ⟨x, hx⟩ := var (s := s) i (by vm)
    obtain ⟨y, hy⟩ := var (s := s) j (by vm)
    obtain ⟨z, hz⟩ := var (s := s) p (by vm)
    obtain ⟨t, ht⟩ := var (s := s) q (by vm)
    have hxy := ev_compT_dom l hx hy (EEq.holds_defined_iff.mp (prem _ (by pm)))
    have hzt := ev_compT_dom l hz ht (EEq.holds_defined_iff.mp (prem _ (by pm)))
    have hxz := ev_compT_dom k hx hz (EEq.holds_defined_iff.mp (prem _ (by pm)))
    have hyt := ev_compT_dom k hy ht (EEq.holds_defined_iff.mp (prem _ (by pm)))
    have P1 : sc M (top k) (ucomp M l x y hxy).1 = tg M (top k) (ucomp M l z t hzt).1 :=
      (sc_comp' (h₁ := ll h) (h₂ := top k) hxy).trans ((comp_congr hxz hyt _ _).trans
        (tg_comp' (h₁ := ll h) (h₂ := top k) hzt).symm)
    have P2 : sc M (top l) (ucomp M k x z hxz).1 = tg M (top l) (ucomp M k y t hyt).1 :=
      (sc_comp_low (h₁ := ll h) (h₂ := top k) hxz).trans
        ((sc_eq_sc_of_comp (h₁ := ll h) (h₂ := top k) hxz).symm.trans
          (hxy.trans (tg_comp_low (h₁ := ll h) (h₂ := top k) hyt).symm))
    exact (EEq.holds_mk'_iff (ev_compT k (ev_compT l hx hy hxy) (ev_compT l hz ht hzt) P1)
      (ev_compT l (ev_compT k hx hz hxz) (ev_compT k hy ht hyt) P2)).mpr
      (Subtype.ext (interchange (h₁ := ll h) (h₂ := top k) hxz hyt hxy hzt).symm)

end Unif
```

:::proposition (label := "unification-models") (central := false) (title := "Unification sends models to models")
$`(\mathbf{u}^{(n)})^{\ast}_{\mathfrak{gd}}` sends the models of
$`(\mathbf{\Sigma}^{\mathrm{ext}(n)}, \mathcal{C}^{\Sigma^{\mathrm{ext}(n)}})` to models of
$`(\mathbf{\Sigma}^{(n)}, \mathcal{C}^{\Sigma^{(n)}})`.

```lean
theorem unif_sendsModels :
    (unif Sig n).SendsModels.{u, max u v, u, max u v, w}
      (Compact.compactSpec Sig (Fin n)) (Extended.extendedSpec Sig (Fin (n + 1))) :=
  fun A hA => ⟨Unif.isAlgebra (M := ⟨A, hA.2⟩), Unif.holds (M := ⟨A, hA.2⟩)⟩
```
:::

:::proof (of := "unification-models")
Let $`\mathbf{A}` be a model and $`\mathbf{B} = (\mathbf{u}^{(n)})^{\ast}_{\mathfrak{gd}}(\mathbf{A})`.
By (EA$`^{k,n}`2), $`\mathrm{sc}^{(k,n)}_{s}(\mathrm{i}^{(n,k)}_{s}(u)) = u` for every $`k`-cell
$`u`, so $`\mathrm{i}^{(n,k)}_{s}` is injective. The derived operations of $`\sigma`,
$`\mathrm{sc}^{k}_{s}` and $`\mathrm{tg}^{k}_{s}` are total, and two $`n`-cells satisfy the domain
condition of $`\circ^{k}_{s}` in $`\mathbf{B}` if and only if
$`\overline{\mathrm{sc}}^{k}_{s}(x) = \overline{\mathrm{tg}}^{k}_{s}(y)`, that is, by injectivity, if
and only if $`\mathrm{sc}^{(k,n)}_{s}(x) = \mathrm{tg}^{(k,n)}_{s}(y)`; then $`x \circ^{(k,n)}_{s} y`
is defined, by (EA$`^{k,n}`3). So $`\mathbf{B}` is an ep-algebra, in which $`\sigma`,
$`\mathrm{sc}^{k}_{s}`, $`\mathrm{tg}^{k}_{s}` and $`\circ^{k}_{s}` act as $`\sigma_n`,
$`\overline{\mathrm{sc}}^{k}_{s}`, $`\overline{\mathrm{tg}}^{k}_{s}` and $`\circ^{(k,n)}_{s}`. Every
axiom of $`\mathcal{C}^{\Sigma^{(n)}}` follows from the extended axioms: (A$`^{k}`2) from
(EA$`^{k,n}`2); (A$`^{k}`3)–(A$`^{k}`6) and (A$`^{k}`8) from (EA$`^{k,n}`3)–(EA$`^{k,n}`6) and
(EA$`^{k,n}`8); (A$`^{k}`7) from the first and the third equations of (EA$`^{k,n}`7); and, for
$`l < k`, (AB$`^{l,k}`1) from (EA$`^{l,k,n}`1), (EA$`^{l,k,n}`2) and (EA$`^{k,n}`2), (AB$`^{l,k}`2) from
(EA$`^{l,k,n}`3) and (EA$`^{l,k,n}`5), and (AB$`^{l,k}`3) from (EA$`^{l,k,n}`4), after exchanging the
variables $`y` and $`z`.
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

# Graduation and unification

Graduation followed by unification gives nothing new: the composite of the two derivors is the
identity.

:::proposition (label := "unification-graduation-derivor") (central := false) (title := "Unification after graduation")
$`\mathbf{g}^{(n)} \circ \mathbf{u}^{(n)} = \mathrm{id}_{\mathbf{\Sigma}^{(n)}}`.

```lean
theorem grad_comp_unif :
    (grad Sig n).comp.{u, max u v, w} (unif Sig n) =
      GenEpDerivor.id.{u, max u v, w} (compactEpSig Sig (Fin n)) := by
  unfold GenEpDerivor.comp GenEpDerivor.id
  congr 1
  · funext s
    have h1 : (grad Sig n).sortDom ((unif Sig n).sortMap s) = ∅ := dif_neg (lt_irrefl n)
    have h2 : (grad Sig n).trSet ((unif Sig n).sortDom s) = ∅ := Set.biUnion_empty _
    rw [h1, h2, Set.empty_union]
    rfl
  · funext ws s σ
    cases σ with
    | op σ =>
      show Term.app _ _ = Term.app _ _
      congr 1; funext p
      have key : ∀ {I : Type} {κ : I → S} {t t' : S} (e : t = t') (i : I) (h : κ i = t),
          (e ▸ (Term.var ⟨i, h⟩ : Term (Compact.CompactSignature Sig (Fin n)) (Vars κ) t)) =
            Term.var ⟨i, h.trans e⟩ := by
        intro I κ t t' e; subst e; intro i h; rfl
      simp only [Term.subst, famSubst, Derivor.lift]
      exact key _ _ _
    | sc k s =>
      show Term.app _ _ = Term.app _ _
      congr 1; funext j; match j with | ⟨0, _⟩ => rfl
    | tg k s =>
      show Term.app _ _ = Term.app _ _
      congr 1; funext j; match j with | ⟨0, _⟩ => rfl
    | comp k s =>
      show Term.app _ _ = Term.app _ _
      congr 1; funext j; match j with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl
```
:::

:::proof (of := "unification-graduation-derivor")
The composite has the mapping of sorts $`s \mapsto s`. Its domains are
$`\mathrm{Cn}(D_{(n,s)} \cup \mathrm{tr}_{\mathbf{g}}[\varnothing]) = \mathrm{Cn}(\varnothing)`,
since $`D_{(n,s)}` and the domains of $`\mathbf{u}^{(n)}` are empty, and its terms are
$`d_{\mathbf{g}}^{\sharp}(\sigma_n((v_p)_p)) = \sigma((v_p)_p)`,
$`d_{\mathbf{g}}^{\sharp}(\mathrm{i}^{(n,k)}_{s}(\mathrm{sc}^{(k,n)}_{s}(v_0))) = \mathrm{sc}^{k}_{s}(v_0)`,
likewise for the targets, and $`d_{\mathbf{g}}^{\sharp}(v_0 \circ^{(k,n)}_{s} v_1) = v_0 \circ^{k}_{s} v_1`:
those of the identity.
:::

```lean
end CategorialAlgebras
```
