import Stemma
import Mathlib.Data.Fin.VecNotation
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EqToHom
import CategorialAlgebras.Evaluation
import CategorialAlgebras.Compact.Specification
import CategorialAlgebras.Compact.OmegaAlgebra

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "Compact categorial algebras as models" =>

Proposition `PCompactIdent` of the draft identifies the compact $`n`-categorial
$`\Sigma`-algebras with the models of the specification $`\mathcal{C}^{\Sigma^{(n)}}`: a pair
$`(\mathsf{A}, F)` is read as the partial $`\Sigma^{(n)}`-algebra of its cells, in which the
$`k`-sources, $`k`-targets and $`k`-compositions of the compact $`n`-categories
$`\mathsf{A}_s` interpret the symbols $`\mathrm{sc}^{k}_{s}`, $`\mathrm{tg}^{k}_{s}` and
$`\circ^{k}_{s}`, and the functors $`F_\sigma` the operation symbols of $`\Sigma`. This
document builds that partial algebra, shows that it is a model of the specification, and shows
that every model of the specification arises in this way, from exactly one algebra. For
$`I = n`, the homomorphisms correspond as well, and the two categories are isomorphic. As the
specification, it is written once for every preordered set of dimensions $`I`, so that it covers
$`n \in \mathbb{N}` and $`\omega` at once.

```lean
universe u v w

namespace CategorialAlgebras.Compact

open Signature Term CTerm CategoryStruct

variable {S : Type u} {Sig : Signature.{u, v} S} {Index : Type} [Preorder Index]
```

# The partial algebra of cells

:::construction (label := "compact.cell-algebra") (central := false) (title := "The partial algebra of cells")
Let $`\Sigma` be an $`S`-sorted signature, $`I` a preordered set of dimensions, $`\mathsf{A}`
an $`S`-sorted compact category with dimensions in $`I`, and $`F` an assignment to every
operation symbol $`\sigma \in \Sigma_{\mathbf{s}, s}` of a compact functor
$`F_\sigma \colon \mathsf{A}_{\mathbf{s}} \to \mathsf{A}_s`. The *partial algebra of cells*
of $`(\mathsf{A}, F)` is the partial algebra of the compact categorial signature with dimensions
in $`I` whose carrier of sort $`s` is the set $`A_s` of cells of $`\mathsf{A}_s`, and in which,
for every $`k \in I` and every $`s \in S`,

* $`\sigma` is interpreted as the total operation $`F_\sigma`;
* $`\mathrm{sc}^{k}_{s}` and $`\mathrm{tg}^{k}_{s}` as the total operations $`\mathrm{sc}^{k}`
  and $`\mathrm{tg}^{k}` of $`\mathsf{A}_s`;
* $`\circ^{k}_{s}` as the partial operation $`\#^{k}` of $`\mathsf{A}_s`, defined at
  $`(x, y)` exactly when $`\mathrm{sc}^{k}(x) = \mathrm{tg}^{k}(y)`.

For $`I = n` this is the identification of Proposition `PCompactIdent` of the draft.

```lean
/-- The operations of the partial algebra of cells. -/
def cellOp (C : S → Type w) [∀ s, Category Index (C s)]
    (F : ∀ {ws : List S} {s : S}, Sig ws s → Functor Index (Arity C ws) (C s)) :
    (ws : List S) → (s : S) → CompactSignature Sig Index ws s → Arity C ws →. C s
  | _, _, .op σ, a => Part.some (F σ a)
  | _, _, .sc k _, a => Part.some (sc k (a ⟨0, by simp⟩))
  | _, _, .tg k _, a => Part.some (tg k (a ⟨0, by simp⟩))
  | _, _, .comp k _, a => a ⟨0, by simp⟩ ♯.[k] a ⟨1, by simp⟩

/-- The partial algebra of cells of an `S`-sorted compact category with operations. -/
abbrev cellAlgebra (C : S → Type w) [∀ s, Category Index (C s)]
    (F : ∀ {ws : List S} {s : S}, Sig ws s → Functor Index (Arity C ws) (C s)) :
    PartialAlgebra.{u, max u v, w} (CompactSignature Sig Index) where
  carrier := C
  op {ws s} σ := cellOp C F ws s σ
```
:::

The proof that it is a model evaluates the terms of the specification: a source, a target or an
operation of $`\Sigma` applied to terms with known values has the expected value, and a
composite of two terms with known values $`a` and $`b` is defined exactly when
$`\mathrm{sc}^{k}(a) = \mathrm{tg}^{k}(b)`.

```lean
section CellAlgebra

variable {C : S → Type w} [∀ s, Category Index (C s)]
  {F : ∀ {ws : List S} {s : S}, Sig ws s → Functor Index (Arity C ws) (C s)}
  {val : ∀ s, Var S s → Part (C s)}

local notation "M" => cellAlgebra C F

lemma cell_eval_scT {k : Index} {s : S} {t : CTerm Sig Index s} {a : C s}
    (h : t.eval M val = Part.some a) : (scT k t).eval M val = Part.some (sc k a) := by
  rw [scT, eval_app₁_of_eq_some _ _ _ h]; rfl

lemma cell_eval_tgT {k : Index} {s : S} {t : CTerm Sig Index s} {a : C s}
    (h : t.eval M val = Part.some a) : (tgT k t).eval M val = Part.some (tg k a) := by
  rw [tgT, eval_app₁_of_eq_some _ _ _ h]; rfl

lemma cell_eval_compT {k : Index} {s : S} {t t' : CTerm Sig Index s} {a b : C s}
    (h : t.eval M val = Part.some a) (h' : t'.eval M val = Part.some b) :
    (compT k t t').eval M val = a ♯.[k] b := by
  rw [compT, eval_app₂_of_eq_some _ _ _ h h']; rfl

lemma cell_eval_compT_some {k : Index} {s : S} {t t' : CTerm Sig Index s} {a b : C s}
    (h : t.eval M val = Part.some a) (h' : t'.eval M val = Part.some b)
    (hab : sc_is_tg k a b) :
    (compT k t t').eval M val = Part.some (a ♯[k] b ← hab) := by
  rw [cell_eval_compT h h']; exact (Part.some_get _).symm

lemma cell_eval_opT {ws : List S} {s : S} (σ : Sig ws s)
    {ts : (j : Fin ws.length) → CTerm Sig Index (ws.get j)} {a : Arity C ws}
    (h : ∀ j, (ts j).eval M val = Part.some (a j)) :
    (opT σ ts).eval M val = Part.some (F σ a) := by
  rw [opT, eval_app_of_eq_some _ _ _ h]; rfl

lemma cell_eval_x {s : S} {i : ℕ} (h : (val s i).Dom) :
    (x (Sig := Sig) (Index := Index) (s := s) i).eval M val = Part.some ((val s i).get h) := by
  simp only [CTerm.x]; exact (Part.some_get h).symm

/-- The value of a composite that is defined. -/
lemma cell_comp_dom {k : Index} {s : S} {t t' : CTerm Sig Index s} {a b : C s}
    (h : t.eval M val = Part.some a) (h' : t'.eval M val = Part.some b)
    (hd : (EEq.defined (compT k t t')).Holds M val) : sc_is_tg k a b := by
  rw [EEq.holds_defined_iff, cell_eval_compT h h'] at hd
  exact sc_is_tg_of_dom hd
```

:::proposition (label := "compact.cell-algebra-model") (central := false) (title := "The partial algebra of cells is a model")
Let $`(\mathsf{A}, F)` be as in Construction `compact.cell-algebra`. Its partial algebra of
cells satisfies every $`\mathrm{QE}`$-equation of the specification with dimensions in $`I`.
In particular, for $`I = n`, the partial algebra of cells of a compact $`n`-categorial
$`\Sigma`-algebra is a model of $`\mathcal{C}^{\Sigma^{(n)}}`; this is one half of the first
part of Proposition `PCompactIdent` of the draft.

```lean
open PreCategory Category in
/-- The partial algebra of cells is a model of the compact specification. -/
theorem cellAlgebra_holds : ∀ q ∈ compactSpec Sig Index, q.Holds (cellAlgebra C F) := by
  intro q hq val hvars hprem
  have var : ∀ {s : S} (i : ℕ), (⟨s, i⟩ : Σ t, Var S t) ∈ q.vars →
      ∃ a, (x (Sig := Sig) (Index := Index) (s := s) i).eval M val = Part.some a :=
    fun i hi => ⟨_, cell_eval_x (hvars _ hi)⟩
  cases hq with
  | @A0 ws s σ xs =>
    choose a ha using fun j => var (s := ws.get j) (xs j) (by simp [QEEq.vars, EEq.vars, EEq.defined, opT, x]; try exact ⟨j, rfl, rfl⟩)
    rw [EEq.holds_defined_iff, cell_eval_opT σ ha]; trivial
  | A1_sc k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.defined, scT, x])
    rw [EEq.holds_defined_iff, cell_eval_scT ha]; trivial
  | A1_tg k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.defined, tgT, x])
    rw [EEq.holds_defined_iff, cell_eval_tgT ha]; trivial
  | A2_sc_sc k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', scT, x])
    rw [EEq.holds_mk'_iff (cell_eval_scT (cell_eval_scT ha)) (cell_eval_scT ha)]
    exact sck_sck_eq_sck k a
  | A2_sc_tg k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', scT, tgT, x])
    rw [EEq.holds_mk'_iff (cell_eval_scT (cell_eval_tgT ha)) (cell_eval_tgT ha)]
    exact sck_tgk_eq_tgk k a
  | A2_tg_sc k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', scT, tgT, x])
    rw [EEq.holds_mk'_iff (cell_eval_tgT (cell_eval_scT ha)) (cell_eval_scT ha)]
    exact tgk_sck_eq_sck k a
  | A2_tg_tg k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', tgT, x])
    rw [EEq.holds_mk'_iff (cell_eval_tgT (cell_eval_tgT ha)) (cell_eval_tgT ha)]
    exact tgk_tgk_eq_tgk k a
  | A3_dom k s i j =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    obtain ⟨b, hb⟩ := var (s := s) j (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    have hab := cell_comp_dom (k := k) ha hb (hprem _ (by simp))
    rw [EEq.holds_mk'_iff (cell_eval_scT ha) (cell_eval_tgT hb)]
    exact hab
  | A3_def k s i j =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    obtain ⟨b, hb⟩ := var (s := s) j (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    have hab := (EEq.holds_mk'_iff (cell_eval_scT (k := k) ha) (cell_eval_tgT (k := k) hb)).mp (hprem _ (by simp))
    rw [EEq.holds_defined_iff, cell_eval_compT ha hb]
    exact dom_of_sc_is_tg hab
  | A4_sc k s i j =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    obtain ⟨b, hb⟩ := var (s := s) j (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    have hab := cell_comp_dom (k := k) ha hb (hprem _ (by simp))
    rw [EEq.holds_mk'_iff (cell_eval_scT (cell_eval_compT_some ha hb hab)) (cell_eval_scT hb)]
    exact sck_compk_eq_sck hab
  | A4_tg k s i j =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    obtain ⟨b, hb⟩ := var (s := s) j (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    have hab := cell_comp_dom (k := k) ha hb (hprem _ (by simp))
    rw [EEq.holds_mk'_iff (cell_eval_tgT (cell_eval_compT_some ha hb hab)) (cell_eval_tgT ha)]
    exact tgk_compk_eq_tgk hab
  | A5_sc k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', compT, scT, x])
    rw [EEq.holds_mk'_iff
      (cell_eval_compT_some ha (cell_eval_scT ha) (tgk_sck_eq_sck k a).symm) ha]
    exact compk_sck_eq_id k a
  | A5_tg k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', compT, tgT, x])
    rw [EEq.holds_mk'_iff (cell_eval_compT_some (cell_eval_tgT ha) ha (sck_tgk_eq_tgk k a)) ha]
    exact compk_tgk_eq_id k a
  | A6 k s i j l =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    obtain ⟨b, hb⟩ := var (s := s) j (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    obtain ⟨c, hc⟩ := var (s := s) l (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    have hab := cell_comp_dom (k := k) ha hb (hprem _ (by simp))
    have hbc := cell_comp_dom (k := k) hb hc (hprem _ (by simp))
    rw [EEq.holds_mk'_iff
      (cell_eval_compT_some (cell_eval_compT_some ha hb hab) hc (PreCategory.compl_assoc hbc hab))
      (cell_eval_compT_some ha (cell_eval_compT_some hb hc hbc) (PreCategory.compr_assoc hbc hab))]
    exact assoc hbc hab
  | @A7_sc k ws s σ xs =>
    choose a ha using fun j => var (s := ws.get j) (xs j) (by simp [QEEq.vars, EEq.vars, EEq.mk', opT, scT, x]; try exact ⟨j, rfl, rfl⟩)
    rw [EEq.holds_mk'_iff (cell_eval_scT (cell_eval_opT σ ha))
      (cell_eval_opT σ fun j => cell_eval_scT (ha j))]
    exact ((F σ).map_sc_eq_sc_map k a).symm
  | @A7_tg k ws s σ xs =>
    choose a ha using fun j => var (s := ws.get j) (xs j) (by simp [QEEq.vars, EEq.vars, EEq.mk', opT, tgT, x]; try exact ⟨j, rfl, rfl⟩)
    rw [EEq.holds_mk'_iff (cell_eval_tgT (cell_eval_opT σ ha))
      (cell_eval_opT σ fun j => cell_eval_tgT (ha j))]
    exact ((F σ).map_tg_eq_tg_map k a).symm
  | @A8 k ws s σ xs ys =>
    choose a ha using fun j => var (s := ws.get j) (xs j)
      (by simp [QEEq.vars, EEq.vars, EEq.mk', opT, compT, x]
          exact Or.inl (Or.inr (Or.inl ⟨j, rfl, rfl⟩)))
    choose b hb using fun j => var (s := ws.get j) (ys j)
      (by simp [QEEq.vars, EEq.vars, EEq.mk', opT, compT, x]
          exact Or.inl (Or.inr (Or.inr ⟨j, rfl, rfl⟩)))
    have hab : ∀ j, sc_is_tg k (a j) (b j) := fun j =>
      cell_comp_dom (ha j) (hb j) (hprem _ (List.mem_ofFn.mpr ⟨j, rfl⟩))
    have hF : sc_is_tg k (F σ a) (F σ b) := (F σ).comp_map (pi_sc_is_tg.mpr hab)
    rw [EEq.holds_mk'_iff
      (cell_eval_opT σ fun j => cell_eval_compT_some (ha j) (hb j) (hab j))
      (cell_eval_compT_some (cell_eval_opT σ ha) (cell_eval_opT σ hb) hF)]
    exact (F σ).map_comp_eq_comp_map (pi_sc_is_tg.mpr hab)
  | AB1_sc_sc l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', scT, x])
    rw [EEq.holds_mk'_iff (cell_eval_scT (cell_eval_scT ha)) (cell_eval_scT ha)]
    exact sck_scj_eq_scj a h
  | AB1_tg_tg l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', tgT, x])
    rw [EEq.holds_mk'_iff (cell_eval_tgT (cell_eval_tgT ha)) (cell_eval_tgT ha)]
    exact tgk_tgj_eq_tgj a h
  | AB1_sc_sck l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', scT, x])
    rw [EEq.holds_mk'_iff (cell_eval_scT (cell_eval_scT ha)) (cell_eval_scT ha)]
    exact scj_sck_eq_scj a h
  | AB1_tg_tgk l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', tgT, x])
    rw [EEq.holds_mk'_iff (cell_eval_tgT (cell_eval_tgT ha)) (cell_eval_tgT ha)]
    exact tgj_tgk_eq_tgj a h
  | AB1_sc_tgk l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', scT, tgT, x])
    rw [EEq.holds_mk'_iff (cell_eval_scT (cell_eval_tgT ha)) (cell_eval_scT ha)]
    exact scj_tgk_eq_scj a h
  | AB1_tg_sck l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', scT, tgT, x])
    rw [EEq.holds_mk'_iff (cell_eval_tgT (cell_eval_scT ha)) (cell_eval_tgT ha)]
    exact tgj_sck_eq_tgj a h
  | AB2_sc l k h s i j =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    obtain ⟨b, hb⟩ := var (s := s) j (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    have hab := cell_comp_dom (k := l) ha hb (hprem _ (by simp))
    rw [EEq.holds_mk'_iff (cell_eval_scT (cell_eval_compT_some ha hb hab))
      (cell_eval_compT_some (cell_eval_scT ha) (cell_eval_scT hb) (Category.sc_tg_j_sc h hab))]
    exact sck_compj_eq_compj_sck h hab
  | AB2_tg l k h s i j =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    obtain ⟨b, hb⟩ := var (s := s) j (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    have hab := cell_comp_dom (k := l) ha hb (hprem _ (by simp))
    rw [EEq.holds_mk'_iff (cell_eval_tgT (cell_eval_compT_some ha hb hab))
      (cell_eval_compT_some (cell_eval_tgT ha) (cell_eval_tgT hb) (Category.sc_tg_j_tg h hab))]
    exact tgk_compj_eq_compj_tgk h hab
  | AB3 l k h s i j p q =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    obtain ⟨b, hb⟩ := var (s := s) j (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    obtain ⟨c, hc⟩ := var (s := s) p (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    obtain ⟨d, hd⟩ := var (s := s) q (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    have h₁ := cell_comp_dom (k := l) ha hb (hprem _ (by simp))
    have h₂ := cell_comp_dom (k := l) hc hd (hprem _ (by simp))
    have h₃ := cell_comp_dom (k := k) ha hc (hprem _ (by simp))
    have h₄ := cell_comp_dom (k := k) hb hd (hprem _ (by simp))
    rw [EEq.holds_mk'_iff
      (cell_eval_compT_some (cell_eval_compT_some ha hb h₁) (cell_eval_compT_some hc hd h₂)
        (Category.sc_tg_k_interchange h h₃ h₄ h₁ h₂))
      (cell_eval_compT_some (cell_eval_compT_some ha hc h₃) (cell_eval_compT_some hb hd h₄)
        (Category.sc_tg_j_interchange h h₃ h₄ h₁))]
    exact interchange h h₃ h₄ h₁ h₂
```
:::

:::proof (of := "compact.cell-algebra-model")
Take an axiom and a valuation of its variables in the cells for which its premises hold. Every
variable then has a value, so every term of the axiom built from sources, targets and
operations of $`\Sigma` has a value, by the totality of these operations; this gives (A0) and
(A$`^k`1). A premise stating that $`x \circ^{k} y` is defined says that
$`\mathrm{sc}^{k}(x) = \mathrm{tg}^{k}(y)`, which is (A$`^k`3) in one direction; conversely,
this equation makes $`x \#^{k} y` defined. Each remaining axiom, once both sides are evaluated,
is a law of compact categories or of compact functors:

* (A$`^k`2), (A$`^k`4), (A$`^k`5) and (A$`^k`6) are the axioms of the compact category
  $`\mathsf{A}_s` in dimension $`k`; for (A$`^k`6), both composites are defined because
  $`x \#^{k} y` and $`y \#^{k} z` are;
* (A$`^k`7) and (A$`^k`8) say that $`F_\sigma` preserves $`k`-sources, $`k`-targets and
  $`k`-composites; in (A$`^k`8), the composite $`F_\sigma((x_j)_j) \#^{k} F_\sigma((y_j)_j)` is
  defined because the family $`(x_j)_j` is $`k`-composable with $`(y_j)_j` in the product
  $`\mathsf{A}_{\mathbf{s}}`, componentwise;
* (AB$`^{l,k}`1), (AB$`^{l,k}`2) and (AB$`^{l,k}`3) are the laws that relate dimensions
  $`l < k` in $`\mathsf{A}_s`, the last one being the interchange law.
:::

```lean
end CellAlgebra
```

# From models to compact categorial algebras

Conversely, every model of the specification is the partial algebra of cells of a compact
categorial algebra: the structure of the categorial algebra is read off from the
operations of the model. Let $`\mathbf{M}` be a model of the specification with dimensions in
$`I`. By (A$`^k`1) and (A0), the $`k`-sources, the $`k`-targets and the operations of
$`\Sigma` are total in $`\mathbf{M}`, and by (A$`^k`3) the composite $`x \circ^{k}_{s} y` is
defined exactly when $`\mathrm{sc}^{k}_{s}(x) = \mathrm{tg}^{k}_{s}(y)`. Each law of compact
categories and of compact functors is then an axiom of the specification, evaluated at the
cells it speaks about.

To evaluate an axiom at given cells, the variables $`x_0, \ldots, x_{m-1}` of the axiom are sent
to them, and the other variables are left without value: since the valuations of the library
are partial, this works even when some sort of $`\mathbf{M}` is empty.

```lean
section Model

variable (M : CompactPAlg.{u, v, w} Sig Index)

/-- Every axiom of the specification holds in a model, under a valuation of finitely many
variables that covers its variables. -/
lemma model_holds {q : QEEq (CompactSignature Sig Index) (Var S)} (hq : CompactAxiom Sig Index q)
    {ι : Type} {pts : ι → Σ t, Var S t} (a : ∀ i, M.1 (pts i).1)
    (hvars : q.vars ⊆ Set.range pts)
    (hprem : ∀ e ∈ q.premises, e.Holds M.1 (assign pts a)) :
    q.conclusion.Holds M.1 (assign pts a) :=
  M.2 q hq _ (fun _ hx => (assign_dom a).mpr (hvars hx)) hprem

lemma injective_of_snd {ι : Type} {pts : ι → Σ t, Var S t}
    (h : Function.Injective fun i => ((pts i).2 : ℕ)) : Function.Injective pts :=
  fun _ _ e => h (congrArg (fun y : Σ t, Var S t => (y.2 : ℕ)) e)

lemma eval_assign {ι : Type} {pts : ι → Σ t, Var S t} (hinj : Function.Injective pts)
    (a : ∀ i, M.1 (pts i).1) (i : ι) :
    (x (Sig := Sig) (Index := Index) (s := (pts i).1) (pts i).2).eval M.1 (assign pts a) =
      Part.some (a i) := by
  simp only [x, eval_var]; exact assign_apply a hinj i

/-- The variables `x_0, …, x_{m-1}` of sort `s`. -/
def ptsOf (s : S) (m : ℕ) : Fin m → Σ t, Var S t := fun i => ⟨s, i.val⟩

lemma ptsOf_injective (s : S) (m : ℕ) : Function.Injective (ptsOf s m) :=
  injective_of_snd fun _ _ h => Fin.ext h

lemma mem_range_ptsOf {s : S} {m : ℕ} {y : Σ t, Var S t} :
    y ∈ Set.range (ptsOf s m) ↔ y.1 = s ∧ (y.2 : ℕ) < m := by
  obtain ⟨t, i⟩ := y
  constructor
  · rintro ⟨j, hj⟩; cases hj; exact ⟨rfl, j.2⟩
  · rintro ⟨rfl, h⟩; exact ⟨⟨i, h⟩, rfl⟩

lemma eval_ptsOf {s : S} {m : ℕ} (a : Fin m → M.1 s) (i : ℕ) (h : i < m) :
    (x (Sig := Sig) (Index := Index) (s := s) i).eval M.1 (assign (ptsOf s m) a) =
      Part.some (a ⟨i, h⟩) :=
  eval_assign M (ptsOf_injective s m) a ⟨i, h⟩

lemma eval_ptsOf' {s : S} {m : ℕ} (a : Fin m → M.1 s) (i : ℕ) (h : i < m) {b : M.1 s}
    (hb : a ⟨i, h⟩ = b) :
    (x (Sig := Sig) (Index := Index) (s := s) i).eval M.1 (assign (ptsOf s m) a) =
      Part.some b :=
  hb ▸ eval_ptsOf M a i h

/-- The variables `x_j` of sort `s_j`, for a word `s`. -/
def ptsFam (ws : List S) : Fin ws.length → Σ t, Var S t := fun j => ⟨ws.get j, j.val⟩

lemma ptsFam_injective (ws : List S) : Function.Injective (ptsFam ws) :=
  injective_of_snd fun _ _ h => Fin.ext h

/-- The variables `x_{2j}` and `x_{2j+1}` of sort `s_j`, for a word `s`. -/
def ptsFam₂ (ws : List S) : Fin ws.length ⊕ Fin ws.length → Σ t, Var S t :=
  Sum.elim (fun j => ⟨ws.get j, 2 * j.val⟩) (fun j => ⟨ws.get j, 2 * j.val + 1⟩)

lemma ptsFam₂_injective (ws : List S) : Function.Injective (ptsFam₂ ws) := by
  refine injective_of_snd ?_
  rintro (i | i) (j | j) h <;> simp only [ptsFam₂, Sum.elim_inl, Sum.elim_inr] at h
  · exact congrArg Sum.inl (Fin.ext (by omega))
  · omega
  · omega
  · exact congrArg Sum.inr (Fin.ext (by omega))

/-- The families `a` and `b` as values of `x_{2j}` and `x_{2j+1}`. -/
def vals₂ {ws : List S} (a b : Arity M.1 ws) : ∀ i, M.1 (ptsFam₂ ws i).1
  | .inl j => a j
  | .inr j => b j

end Model

/-- The variables of an axiom with variables `x_0, …, x_{m-1}` of sort `s`. -/
local macro "model_vars" : tactic => `(tactic| (
  rintro ⟨t, i⟩ hy
  rw [mem_range_ptsOf]
  simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, scT, tgT, compT, opT, x] at hy
  aesop))

section Model

variable {M : CompactPAlg.{u, v, w} Sig Index}

lemma sc_dom (k : Index) {s : S} (a : M.1 s) :
    (M.1.op (.sc k s) (fun | ⟨0, _⟩ => a)).Dom := by
  have := model_holds M (.A1_sc k s 0) (pts := ptsOf s 1) (fun _ => a) (by model_vars) (by simp)
  rwa [EEq.holds_defined_iff, scT, eval_app₁_of_eq_some _ _ _ (eval_ptsOf M _ 0 (by omega))] at this

lemma tg_dom (k : Index) {s : S} (a : M.1 s) :
    (M.1.op (.tg k s) (fun | ⟨0, _⟩ => a)).Dom := by
  have := model_holds M (.A1_tg k s 0) (pts := ptsOf s 1) (fun _ => a) (by model_vars) (by simp)
  rwa [EEq.holds_defined_iff, tgT, eval_app₁_of_eq_some _ _ _ (eval_ptsOf M _ 0 (by omega))] at this

lemma op_dom {ws : List S} {s : S} (σ : Sig ws s) (a : Arity M.1 ws) :
    (M.1.op (.op σ) a).Dom := by
  have := model_holds M (.A0 σ fun j => j.val) (pts := ptsFam ws) a
    (by
      rintro y hy
      simp [QEEq.vars, EEq.vars, EEq.defined, opT, x] at hy
      obtain ⟨j, rfl⟩ := hy
      exact ⟨j, rfl⟩)
    (by simp)
  rwa [EEq.holds_defined_iff, opT, eval_app_of_eq_some M.1 _ (.op σ) (ts := fun j => x (j : ℕ))
    fun j => eval_assign M (ptsFam_injective ws) a j] at this

variable (M) in
/-- The `k`-source of a model. -/
def msc (k : Index) {s : S} (a : M.1 s) : M.1 s :=
  (M.1.op (.sc k s) (fun | ⟨0, _⟩ => a)).get (sc_dom k a)

variable (M) in
/-- The `k`-target of a model. -/
def mtg (k : Index) {s : S} (a : M.1 s) : M.1 s :=
  (M.1.op (.tg k s) (fun | ⟨0, _⟩ => a)).get (tg_dom k a)

variable (M) in
/-- The operation of `σ` in a model. -/
def mop {ws : List S} {s : S} (σ : Sig ws s) (a : Arity M.1 ws) : M.1 s :=
  (M.1.op (.op σ) a).get (op_dom σ a)

variable {val : ∀ s, Var S s → Part (M.1 s)}

lemma meval_scT {k : Index} {s : S} {t : CTerm Sig Index s} {a : M.1 s}
    (h : t.eval M.1 val = Part.some a) : (scT k t).eval M.1 val = Part.some (msc M k a) := by
  rw [scT, eval_app₁_of_eq_some _ _ _ h]; exact (Part.some_get _).symm

lemma meval_tgT {k : Index} {s : S} {t : CTerm Sig Index s} {a : M.1 s}
    (h : t.eval M.1 val = Part.some a) : (tgT k t).eval M.1 val = Part.some (mtg M k a) := by
  rw [tgT, eval_app₁_of_eq_some _ _ _ h]; exact (Part.some_get _).symm

lemma meval_compT {k : Index} {s : S} {t t' : CTerm Sig Index s} {a b : M.1 s}
    (h : t.eval M.1 val = Part.some a) (h' : t'.eval M.1 val = Part.some b) :
    (compT k t t').eval M.1 val = M.1.op (.comp k s) (fun | ⟨0, _⟩ => a | ⟨1, _⟩ => b) := by
  rw [compT, eval_app₂_of_eq_some _ _ _ h h']
  congr 1; funext j
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

lemma meval_opT {ws : List S} {s : S} (σ : Sig ws s)
    {ts : (j : Fin ws.length) → CTerm Sig Index (ws.get j)} {a : Arity M.1 ws}
    (h : ∀ j, (ts j).eval M.1 val = Part.some (a j)) :
    (opT σ ts).eval M.1 val = Part.some (mop M σ a) := by
  rw [opT, eval_app_of_eq_some _ _ _ h]; exact (Part.some_get _).symm

/-- The compact categorial structure of a model. -/
instance modelStruct (s : S) : CategoryStruct Index (M.1 s) where
  sc k a := msc M k a
  tg k a := mtg M k a
  pcomp k g f := M.1.op (.comp k s) (fun | ⟨0, _⟩ => g | ⟨1, _⟩ => f)
  pcomp_dom := by
    intro k f g
    constructor
    · intro hd
      have := model_holds M (.A3_dom k s 0 1) (pts := ptsOf s 2) ![g, f] (by model_vars)
        (by
          intro e he
          simp only [List.mem_singleton] at he; subst he
          rw [EEq.holds_defined_iff,
            meval_compT (eval_ptsOf M _ 0 (by omega)) (eval_ptsOf M _ 1 (by omega))]
          exact hd)
      rwa [EEq.holds_mk'_iff (meval_scT (eval_ptsOf M _ 0 (by omega)))
        (meval_tgT (eval_ptsOf M _ 1 (by omega)))] at this
    · intro hgf
      have := model_holds M (.A3_def k s 0 1) (pts := ptsOf s 2) ![g, f] (by model_vars)
        (by
          intro e he
          simp only [List.mem_singleton] at he; subst he
          rw [EEq.holds_mk'_iff (meval_scT (eval_ptsOf M _ 0 (by omega)))
            (meval_tgT (eval_ptsOf M _ 1 (by omega)))]
          exact hgf)
      rwa [EEq.holds_defined_iff,
        meval_compT (eval_ptsOf M _ 0 (by omega)) (eval_ptsOf M _ 1 (by omega))] at this

lemma meval_compT_some {k : Index} {s : S} {t t' : CTerm Sig Index s} {a b : M.1 s}
    (h : t.eval M.1 val = Part.some a) (h' : t'.eval M.1 val = Part.some b)
    (hab : sc_is_tg k a b) :
    (compT k t t').eval M.1 val = Part.some (a ♯[k] b ← hab) := by
  rw [meval_compT h h']; exact (Part.some_get _).symm

lemma holds_defined_compT {k : Index} {s : S} {t t' : CTerm Sig Index s} {a b : M.1 s}
    (h : t.eval M.1 val = Part.some a) (h' : t'.eval M.1 val = Part.some b)
    (hab : sc_is_tg k a b) : (EEq.defined (compT k t t')).Holds M.1 val := by
  rw [EEq.holds_defined_iff, meval_compT_some h h' hab]; trivial

lemma meval_pcomp {k : Index} {s : S} {t t' : CTerm Sig Index s} {a b : M.1 s}
    (h : t.eval M.1 val = Part.some a) (h' : t'.eval M.1 val = Part.some b) :
    (compT k t t').eval M.1 val = a ♯.[k] b :=
  meval_compT h h'

lemma holds_mk'_of_eval {s : S} {t t' : CTerm Sig Index s} {p p' : Part (M.1 s)}
    (ht : t.eval M.1 val = p) (ht' : t'.eval M.1 val = p') :
    (EEq.mk' t t').Holds M.1 val ↔ ∃ (h₁ : p.Dom) (h₂ : p'.Dom), p.get h₁ = p'.get h₂ := by
  subst ht ht'; rfl

end Model

set_option hygiene false in
/-- The value of the variable `x_i` under a valuation of `x_0, …, x_{m-1}`. -/
local macro "ev" i:num : term => `(eval_ptsOf' M _ $i (by omega) (by rfl))

set_option hygiene false in
/-- Read an equation off an axiom of the specification, for variables of one sort. -/
local macro "law" ax:term:max m:num vals:term:max l:term:max r:term:max prem:term:max :
    tactic =>
  `(tactic| (
    obtain ⟨_, _, e⟩ := (holds_mk'_of_eval $l $r).mp
      (model_holds M $ax (pts := ptsOf _ $m) $vals (by model_vars) $prem)
    exact e))

/-- Premises stating that composites are defined, one term for each premise. -/
local syntax "prems" term,* : term

set_option hygiene false in
macro_rules
  | `(prems $h) => `(by
      intro e he
      obtain rfl := List.mem_singleton.mp he
      exact $h)
  | `(prems $h₁, $h₂) => `(by
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      exacts [$h₁, $h₂])
  | `(prems $h₁, $h₂, $h₃, $h₄) => `(by
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      exacts [$h₁, $h₂, $h₃, $h₄])

section Model

variable {M : CompactPAlg.{u, v, w} Sig Index} {k l : Index} {s : S}

lemma model_sc_sc (a : M.1 s) : sc k (sc k a) = sc k a := by
  law (.A2_sc_sc k s 0) 1 ![a] (meval_scT (meval_scT (ev 0))) (meval_scT (ev 0)) (by simp)

lemma model_tg_sc (a : M.1 s) : tg k (sc k a) = sc k a := by
  law (.A2_tg_sc k s 0) 1 ![a] (meval_tgT (meval_scT (ev 0))) (meval_scT (ev 0)) (by simp)

lemma model_sc_tg (a : M.1 s) : sc k (tg k a) = tg k a := by
  law (.A2_sc_tg k s 0) 1 ![a] (meval_scT (meval_tgT (ev 0))) (meval_tgT (ev 0)) (by simp)

lemma model_tg_tg (a : M.1 s) : tg k (tg k a) = tg k a := by
  law (.A2_tg_tg k s 0) 1 ![a] (meval_tgT (meval_tgT (ev 0))) (meval_tgT (ev 0)) (by simp)

lemma model_sc_comp {g f : M.1 s} (h : sc_is_tg k g f) : sc k (g ♯[k] f ← h) = sc k f := by
  law (.A4_sc k s 0 1) 2 ![g, f] (meval_scT (meval_compT_some (ev 0) (ev 1) h))
    (meval_scT (ev 1)) (prems holds_defined_compT (ev 0) (ev 1) h)

lemma model_tg_comp {g f : M.1 s} (h : sc_is_tg k g f) : tg k (g ♯[k] f ← h) = tg k g := by
  law (.A4_tg k s 0 1) 2 ![g, f] (meval_tgT (meval_compT_some (ev 0) (ev 1) h))
    (meval_tgT (ev 0)) (prems holds_defined_compT (ev 0) (ev 1) h)

lemma model_comp_sc (a : M.1 s) :
    a ♯[k] (sc k a) ← (model_tg_sc a).symm = a := by
  law (.A5_sc k s 0) 1 ![a] (meval_compT_some (ev 0) (meval_scT (ev 0)) (model_tg_sc a).symm)
    (ev 0) (by simp)

lemma model_tg_comp_self (a : M.1 s) :
    (tg k a) ♯[k] a ← (model_sc_tg a) = a := by
  law (.A5_tg k s 0) 1 ![a] (meval_compT_some (meval_tgT (ev 0)) (ev 0) (model_sc_tg a))
    (ev 0) (by simp)

lemma model_assoc {f g h : M.1 s} (hgf : sc_is_tg k g f) (hhg : sc_is_tg k h g) :
    ((h ♯[k] g ← hhg) ♯[k] f ← ((model_sc_comp hhg).trans hgf)) =
      (h ♯[k] (g ♯[k] f ← hgf) ← (hhg.trans (model_tg_comp hgf).symm)) := by
  law (.A6 k s 0 1 2) 3 ![h, g, f] (meval_pcomp (meval_compT_some (ev 0) (ev 1) hhg) (ev 2))
    (meval_pcomp (ev 0) (meval_compT_some (ev 1) (ev 2) hgf))
    (prems holds_defined_compT (ev 0) (ev 1) hhg, holds_defined_compT (ev 1) (ev 2) hgf)

instance modelPreCategory (s : S) : PreCategory Index (M.1 s) where
  sck_sck_eq_sck _ := model_sc_sc
  tgk_sck_eq_sck _ := model_tg_sc
  sck_tgk_eq_tgk _ := model_sc_tg
  tgk_tgk_eq_tgk _ := model_tg_tg
  sck_compk_eq_sck := model_sc_comp
  tgk_compk_eq_tgk := model_tg_comp
  compk_sck_eq_id _ := model_comp_sc
  compk_tgk_eq_id _ := model_tg_comp_self
  assoc := model_assoc

lemma model_sc_k_sc_l (a : M.1 s) (h : l < k) : sc k (sc l a) = sc l a := by
  law (.AB1_sc_sc l k h s 0) 1 ![a] (meval_scT (meval_scT (ev 0))) (meval_scT (ev 0)) (by simp)

lemma model_tg_k_tg_l (a : M.1 s) (h : l < k) : tg k (tg l a) = tg l a := by
  law (.AB1_tg_tg l k h s 0) 1 ![a] (meval_tgT (meval_tgT (ev 0))) (meval_tgT (ev 0)) (by simp)

lemma model_sc_l_sc_k (a : M.1 s) (h : l < k) : sc l (sc k a) = sc l a := by
  law (.AB1_sc_sck l k h s 0) 1 ![a] (meval_scT (meval_scT (ev 0))) (meval_scT (ev 0)) (by simp)

lemma model_tg_l_tg_k (a : M.1 s) (h : l < k) : tg l (tg k a) = tg l a := by
  law (.AB1_tg_tgk l k h s 0) 1 ![a] (meval_tgT (meval_tgT (ev 0))) (meval_tgT (ev 0)) (by simp)

lemma model_sc_l_tg_k (a : M.1 s) (h : l < k) : sc l (tg k a) = sc l a := by
  law (.AB1_sc_tgk l k h s 0) 1 ![a] (meval_scT (meval_tgT (ev 0))) (meval_scT (ev 0)) (by simp)

lemma model_tg_l_sc_k (a : M.1 s) (h : l < k) : tg l (sc k a) = tg l a := by
  law (.AB1_tg_sck l k h s 0) 1 ![a] (meval_tgT (meval_scT (ev 0))) (meval_tgT (ev 0)) (by simp)

lemma model_sc_comp_l {g f : M.1 s} (h : l < k) (hgf : sc_is_tg l g f) (hd) :
    sc k (g ♯[l] f ← hgf) = (sc k g ♯.[l] sc k f).get hd := by
  law (.AB2_sc l k h s 0 1) 2 ![g, f] (meval_scT (meval_compT_some (ev 0) (ev 1) hgf))
    (meval_pcomp (meval_scT (ev 0)) (meval_scT (ev 1)))
    (prems holds_defined_compT (ev 0) (ev 1) hgf)

lemma model_tg_comp_l {g f : M.1 s} (h : l < k) (hgf : sc_is_tg l g f) (hd) :
    tg k (g ♯[l] f ← hgf) = (tg k g ♯.[l] tg k f).get hd := by
  law (.AB2_tg l k h s 0 1) 2 ![g, f] (meval_tgT (meval_compT_some (ev 0) (ev 1) hgf))
    (meval_pcomp (meval_tgT (ev 0)) (meval_tgT (ev 1)))
    (prems holds_defined_compT (ev 0) (ev 1) hgf)

lemma model_interchange {f₁ f₂ g₁ g₂ : M.1 s} (h : l < k)
    (hg : sc_is_tg k g₂ g₁) (hf : sc_is_tg k f₂ f₁)
    (h₂ : sc_is_tg l g₂ f₂) (h₁ : sc_is_tg l g₁ f₁) (hd) (hd') :
    ((g₂ ♯[l] f₂ ← h₂) ♯.[k] (g₁ ♯[l] f₁ ← h₁)).get hd =
      ((g₂ ♯[k] g₁ ← hg) ♯.[l] (f₂ ♯[k] f₁ ← hf)).get hd' := by
  law (.AB3 l k h s 0 1 2 3) 4 ![g₂, f₂, g₁, f₁]
    (meval_pcomp (meval_compT_some (ev 0) (ev 1) h₂) (meval_compT_some (ev 2) (ev 3) h₁))
    (meval_pcomp (meval_compT_some (ev 0) (ev 2) hg) (meval_compT_some (ev 1) (ev 3) hf))
    (prems holds_defined_compT (ev 0) (ev 1) h₂, holds_defined_compT (ev 2) (ev 3) h₁,
      holds_defined_compT (ev 0) (ev 2) hg, holds_defined_compT (ev 1) (ev 3) hf)

```

:::construction (label := "compact.model-category") (central := false) (title := "The compact categories of a model")
Let $`\mathbf{M}` be a model of the specification with dimensions in $`I`. For every sort
$`s`, the carrier $`M_s` is a compact category with dimensions in $`I` in which
$`\mathrm{sc}^{k}` and $`\mathrm{tg}^{k}` are the total operations
$`\mathrm{sc}^{k}_{s}` and $`\mathrm{tg}^{k}_{s}` of $`\mathbf{M}`, and $`\#^{k}` is the partial
operation $`\circ^{k}_{s}`. Its axioms are (A$`^k`3) for the domain of $`\#^{k}`; (A$`^k`2),
(A$`^k`4), (A$`^k`5) and (A$`^k`6) for (C1), (C3), (C4) and (C5); and (AB$`^{l,k}`1),
(AB$`^{l,k}`2) and (AB$`^{l,k}`3) for (2C1), (2C2) and (2C3).

```lean
/-- The compact category of each sort of a model. -/
instance modelCategory (s : S) : Category Index (M.1 s) where
  sck_scj_eq_scj := model_sc_k_sc_l
  scj_sck_eq_scj := model_sc_l_sc_k
  scj_tgk_eq_scj := model_sc_l_tg_k
  tgk_tgj_eq_tgj := model_tg_k_tg_l
  tgj_tgk_eq_tgj := model_tg_l_tg_k
  tgj_sck_eq_tgj := model_tg_l_sc_k
  sck_compj_eq_compj_sck h hgf := model_sc_comp_l h hgf _
  tgk_compj_eq_compj_tgk h hgf := model_tg_comp_l h hgf _
  interchange h hg hf h₂ h₁ := model_interchange h hg hf h₂ h₁ _ _
```
:::

:::construction (label := "compact.model-algebra") (central := false) (title := "The compact categorial algebra of a model")
Let $`\mathbf{M}` be as above. For every $`\sigma \in \Sigma_{\mathbf{s}, s}`, the total
operation $`\sigma^{\mathbf{M}} \colon M_{\mathbf{s}} \to M_s` is a compact functor from the
product $`\mathsf{M}_{\mathbf{s}}` of the compact categories of Construction
`compact.model-category` to $`\mathsf{M}_s`: it preserves $`k`-sources and $`k`-targets by
(A$`^k`7), and $`k`-composites by (A$`^k`8), since two families are $`k`-composable in the
product exactly when they are componentwise. For $`I = n`, this makes $`\mathbf{M}` a compact
$`n`-categorial $`\Sigma`-algebra.

```lean
variable (M) in
/-- The compact functor of an operation symbol of `Σ` in a model. -/
def modelOp {ws : List S} {s : S} (σ : Sig ws s) : Functor Index (Arity M.1 ws) (M.1 s) where
  map a := mop M σ a
  map_sc_eq_sc_map k a := by
    have ha := fun j => eval_assign M (ptsFam_injective ws) a j
    obtain ⟨_, _, e⟩ := (holds_mk'_of_eval (meval_scT (meval_opT σ ha))
      (meval_opT σ fun j => meval_scT (ha j))).mp
      (model_holds M (.A7_sc k σ fun j => j.val) (pts := ptsFam ws) a
        (by
          rintro y hy
          simp [QEEq.vars, EEq.vars, EEq.mk', opT, scT, x] at hy
          obtain ⟨j, rfl⟩ := hy; exact ⟨j, rfl⟩)
        (by simp))
    exact e.symm
  map_tg_eq_tg_map k a := by
    have ha := fun j => eval_assign M (ptsFam_injective ws) a j
    obtain ⟨_, _, e⟩ := (holds_mk'_of_eval (meval_tgT (meval_opT σ ha))
      (meval_opT σ fun j => meval_tgT (ha j))).mp
      (model_holds M (.A7_tg k σ fun j => j.val) (pts := ptsFam ws) a
        (by
          rintro y hy
          simp [QEEq.vars, EEq.vars, EEq.mk', opT, tgT, x] at hy
          obtain ⟨j, rfl⟩ := hy; exact ⟨j, rfl⟩)
        (by simp))
    exact e.symm
  map_comp_eq_comp_map {k f g} h := by
    have hg : ∀ j, (x (Sig := Sig) (Index := Index) (s := ws.get j) (2 * j.val)).eval M.1
        (assign (ptsFam₂ ws) (vals₂ M g f)) = Part.some (g j) :=
      fun j => eval_assign M (ptsFam₂_injective ws) (vals₂ M g f) (.inl j)
    have hf : ∀ j, (x (Sig := Sig) (Index := Index) (s := ws.get j) (2 * j.val + 1)).eval M.1
        (assign (ptsFam₂ ws) (vals₂ M g f)) = Part.some (f j) :=
      fun j => eval_assign M (ptsFam₂_injective ws) (vals₂ M g f) (.inr j)
    have h' := fun j => pi_sc_is_tg.mp h j
    obtain ⟨_, _, e⟩ := (holds_mk'_of_eval
      (meval_opT σ fun j => meval_compT_some (hg j) (hf j) (h' j))
      (meval_pcomp (meval_opT σ hg) (meval_opT σ hf))).mp
      (model_holds M (.A8 k σ (fun j => 2 * j.val) (fun j => 2 * j.val + 1)) (pts := ptsFam₂ ws)
        (vals₂ M g f)
        (by
          rintro y hy
          simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, opT, compT, x] at hy
          rcases hy with ((⟨j, rfl | rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl | rfl⟩) <;>
            first | exact ⟨.inl j, rfl⟩ | exact ⟨.inr j, rfl⟩)
        (by
          intro e he
          simp only [List.mem_ofFn] at he
          obtain ⟨j, rfl⟩ := he
          exact holds_defined_compT (hg j) (hf j) (h' j)))
    exact e

/-- The compact `n`-categorial algebra of a model of `C^{Σ^{(n)}}`. -/
def modelCatAlgebra {n : ℕ} (N : CompactPAlg.{u, v, w} Sig (Fin n)) :
    CatAlgebra.{u, v, w} Sig n where
  carrier := N.1.carrier
  op σ := modelOp N σ
```
:::

:::proposition (label := "compact.model-cell-algebra") (central := false) (title := "Every model is a partial algebra of cells")
Every model $`\mathbf{M}` of the specification with dimensions in $`I` is the partial algebra of
cells (Construction `compact.cell-algebra`) of the compact categorial algebra of Construction
`compact.model-algebra`. In particular, for $`I = n`, every model of
$`\mathcal{C}^{\Sigma^{(n)}}` is the partial algebra of cells of a compact $`n`-categorial
$`\Sigma`-algebra; this is the other half of the identification of objects in the first part of
Proposition `PCompactIdent` of the draft.

```lean
variable (M) in
/-- A model is the partial algebra of cells of its compact categorial structure. -/
theorem cellAlgebra_model : cellAlgebra M.1.carrier (fun σ => modelOp M σ) = M.1 := by
  apply congrArg (PartialAlgebra.mk M.1.carrier)
  funext ws s σ a
  cases σ with
  | op σ => exact Part.some_get _
  | sc k s =>
    refine (Part.some_get _).trans (congrArg _ ?_)
    funext j; match j with | ⟨0, _⟩ => rfl
  | tg k s =>
    refine (Part.some_get _).trans (congrArg _ ?_)
    funext j; match j with | ⟨0, _⟩ => rfl
  | comp k s =>
    refine congrArg (M.1.op (.comp k s)) ?_
    funext j; match j with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl

theorem cellAlgebra_modelCatAlgebra {n : ℕ} (N : CompactPAlg.{u, v, w} Sig (Fin n)) :
    cellAlgebra (modelCatAlgebra N).carrier (modelCatAlgebra N).op = N.1 :=
  cellAlgebra_model N

end Model
```
:::

:::proof (of := "compact.model-cell-algebra")
Both partial algebras have the same carriers, and their operations agree symbol by symbol: an
operation $`\sigma` of $`\Sigma`, a $`k`-source or a $`k`-target is interpreted in the partial
algebra of cells by its value in $`\mathbf{M}`, which is defined, and the $`k`-composition is
interpreted by $`\circ^{k}_{s}` itself.
:::

# The bijection

The two constructions are inverse to each other. Starting from a model, Proposition
`compact.model-cell-algebra` says that the partial algebra of cells of its compact categorial
algebra is the model itself. Starting from a compact categorial algebra $`(\mathsf{A}, F)`,
reading the structure off its partial algebra of cells gives back the same sources, targets and
compositions, and the same functors $`F_\sigma`, since the partial algebra of cells interprets
the symbols by them. A compact category is determined by its sources, targets and compositions,
the rest of its structure being properties.

```lean
/-- Two compact categories with dimensions in `I` on the same set are equal when their
sources, targets and compositions are. -/
lemma Category.ext' {C : Type w} {i j : Category Index C}
    (hsc : ∀ k a, @sc Index C i.toCategoryStruct k a = @sc Index C j.toCategoryStruct k a)
    (htg : ∀ k a, @tg Index C i.toCategoryStruct k a = @tg Index C j.toCategoryStruct k a)
    (hc : ∀ k g f, @CategoryStruct.pcomp Index C i.toCategoryStruct k g f =
      @CategoryStruct.pcomp Index C j.toCategoryStruct k g f) : i = j := by
  cases i with | @mk pi => cases pi with | @mk si => cases si with | mk sci tgi pi =>
  cases j with | @mk pj => cases pj with | @mk sj => cases sj with | mk scj tgj pj =>
  obtain rfl : sci = scj := funext fun k => funext (hsc k)
  obtain rfl : tgi = tgj := funext fun k => funext (htg k)
  obtain rfl : pi = pj := funext fun k => funext fun g => funext (hc k g)
  rfl

section CellModel

variable (C : S → Type w) [∀ s, Category Index (C s)]
  (F : ∀ {ws : List S} {s : S}, Sig ws s → Functor Index (Arity C ws) (C s))

/-- The model of the specification of a compact categorial algebra: its partial algebra of
cells. -/
def cellModel : CompactPAlg.{u, v, w} Sig Index := ⟨cellAlgebra C F, cellAlgebra_holds⟩
```

:::proposition (label := "compact.model-of-cell-algebra") (central := false) (title := "The structure of the partial algebra of cells")
Let $`\mathsf{A}` be an $`S`-sorted compact category with dimensions in $`I` and $`F` an
assignment of compact functors $`F_\sigma \colon \mathsf{A}_{\mathbf{s}} \to \mathsf{A}_s`
to the operation symbols of $`\Sigma`. The compact categories of its partial algebra of cells
(Construction `compact.model-category`) are the compact categories $`\mathsf{A}_s`, and the
functors of its operation symbols (Construction `compact.model-algebra`) are the functors
$`F_\sigma`. In particular, for $`I = n`, the compact $`n`-categorial algebra of the partial
algebra of cells of a compact $`n`-categorial $`\Sigma`-algebra $`\boldsymbol{\mathsf{A}}` is
$`\boldsymbol{\mathsf{A}}`.

```lean
theorem modelCategory_cellModel (s : S) :
    modelCategory (M := cellModel C F) s = ‹∀ s, Category Index (C s)› s :=
  Category.ext' (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)

theorem modelOp_cellModel {ws : List S} {s : S} (σ : Sig ws s) (a : Arity C ws) :
    (modelOp (cellModel C F) σ).map a = (F σ).map a := rfl

end CellModel

lemma CatAlgebra.mk_eq_mk {n : ℕ} {C : S → Type w} {str str' : ∀ s, NCategory n (C s)}
    {F : ∀ {ws : List S} {s : S}, Sig ws s → letI := str; NFunctor n (Arity C ws) (C s)}
    {F' : ∀ {ws : List S} {s : S}, Sig ws s → letI := str'; NFunctor n (Arity C ws) (C s)}
    (h : str = str') (hF : ∀ {ws : List S} {s : S} (σ : Sig ws s) a,
      (letI := str; (F σ).map a) = (letI := str'; (F' σ).map a)) :
    @CatAlgebra.mk S Sig n C str F = @CatAlgebra.mk S Sig n C str' F' := by
  subst h; congr; funext ws s σ; exact Functor.ext (hF σ)

theorem modelCatAlgebra_cellModel {n : ℕ} (A : CatAlgebra.{u, v, w} Sig n) :
    modelCatAlgebra (cellModel A.carrier A.op) = A := by
  cases A with | @mk C str F =>
  exact CatAlgebra.mk_eq_mk (funext (modelCategory_cellModel C F)) fun _ _ => rfl
```
:::

:::proof (of := "compact.model-of-cell-algebra")
In the partial algebra of cells, the symbols $`\mathrm{sc}^{k}_{s}`, $`\mathrm{tg}^{k}_{s}`,
$`\circ^{k}_{s}` and $`\sigma` are interpreted by $`\mathrm{sc}^{k}`, $`\mathrm{tg}^{k}` and
$`\#^{k}` of $`\mathsf{A}_s` and by $`F_\sigma`; the constructions of the previous section
read them back unchanged. Two compact categories on the same set with the same sources, targets
and compositions are equal, and two compact functors with the same underlying mapping are equal.
:::

:::construction (label := "compact.cat-algebra-equiv-model") (central := false) (title := "Compact n-categorial algebras are the models of C^Σ⁽ⁿ⁾")
For $`n \in \mathbb{N}`, sending a compact $`n`-categorial $`\Sigma`-algebra to its partial
algebra of cells is a bijection from the compact $`n`-categorial $`\Sigma`-algebras to the
models of $`\mathcal{C}^{\Sigma^{(n)}}`, whose inverse sends a model to its compact
$`n`-categorial algebra (Construction `compact.model-algebra`): the two composites are identities
by Propositions `compact.model-cell-algebra` and `compact.model-of-cell-algebra`. This is the
identification of objects in the first part of Proposition `PCompactIdent` of the draft.

```lean
/-- Compact `n`-categorial algebras are in bijection with the models of `C^{Σ^{(n)}}`. -/
def catAlgebraEquivModel (n : ℕ) :
    CatAlgebra.{u, v, w} Sig n ≃ CompactPAlg.{u, v, w} Sig (Fin n) where
  toFun A := cellModel A.carrier A.op
  invFun M := modelCatAlgebra M
  left_inv A := modelCatAlgebra_cellModel A
  right_inv M := Subtype.ext (cellAlgebra_modelCatAlgebra M)
```
:::

# Homomorphisms and the isomorphism of categories

A homomorphism of compact $`n`-categorial algebras is a family of compact $`n`-functors that
commutes with the operations of $`\Sigma`. On the partial algebras of cells, this says exactly
that the family is a homomorphism of partial algebras: preserving $`k`-sources and $`k`-targets is
commuting with the total operations $`\mathrm{sc}^{k}_{s}` and $`\mathrm{tg}^{k}_{s}`, and
preserving $`k`-composites is sending defined composites to defined composites, with the
composite of the images as image. The homomorphisms of partial algebras of the library need not
reflect definedness, as in the draft; this is what compact functors ask.

:::construction (label := "compact.hom-cells") (central := false) (title := "Homomorphisms as homomorphisms of cells")
Let $`\boldsymbol{\mathsf{A}}` and $`\boldsymbol{\mathsf{B}}` be compact $`n`-categorial
$`\Sigma`-algebras. Every homomorphism $`H \colon \boldsymbol{\mathsf{A}} \to
\boldsymbol{\mathsf{B}}` is, with the same mappings $`H_s`, a homomorphism between their
partial algebras of cells; and every homomorphism $`h` between the partial algebras of cells is,
with the same mappings $`h_s`, a homomorphism $`\boldsymbol{\mathsf{A}} \to
\boldsymbol{\mathsf{B}}`: each $`h_s` is a compact $`n`-functor because $`h` commutes with
$`\mathrm{sc}^{k}_{s}`, $`\mathrm{tg}^{k}_{s}` and $`\circ^{k}_{s}`, and the family commutes with
the operations of $`\Sigma` because $`h` commutes with the symbols $`\sigma`.

```lean
namespace CatAlgebra

variable {n : ℕ} {A B : CatAlgebra.{u, v, w} Sig n}

/-- A homomorphism of compact `n`-categorial algebras is a homomorphism of their partial
algebras of cells. -/
def Hom.toCells (H : Hom A B) :
    PartialAlgebra.Hom (cellAlgebra A.carrier A.op) (cellAlgebra B.carrier B.op) where
  map s := H.map s
  map_dom σ a h := by
    cases σ with
    | op σ => trivial
    | sc k s => trivial
    | tg k s => trivial
    | comp k s => exact dom_of_sc_is_tg ((H.map _).comp_map (sc_is_tg_of_dom h))
  map_op σ a h := by
    cases σ with
    | op σ => exact H.map_op σ a
    | sc k s => exact (H.map _).map_sc_eq_sc_map k _
    | tg k s => exact (H.map _).map_tg_eq_tg_map k _
    | comp k s => exact (H.map _).map_comp_eq_comp_map (sc_is_tg_of_dom h)

/-- A homomorphism of the partial algebras of cells is a homomorphism of compact `n`-categorial
algebras. -/
def Hom.ofCells (h : PartialAlgebra.Hom (cellAlgebra A.carrier A.op) (cellAlgebra B.carrier B.op)) :
    Hom A B where
  map s :=
    { map := h.map s
      map_sc_eq_sc_map := fun k f => h.map_op (.sc k s) (fun | ⟨0, _⟩ => f) trivial
      map_tg_eq_tg_map := fun k f => h.map_op (.tg k s) (fun | ⟨0, _⟩ => f) trivial
      map_comp_eq_comp_map := fun {k f g} hgf =>
        h.map_op (.comp k s) (fun | ⟨0, _⟩ => g | ⟨1, _⟩ => f) (dom_of_sc_is_tg hgf) }
  map_op σ a := h.map_op (.op σ) a trivial

end CatAlgebra
```
:::

:::construction (label := "compact.cells-functor") (central := false) (title := "The functor of cells")
For $`n \in \mathbb{N}`, sending a compact $`n`-categorial $`\Sigma`-algebra to its partial
algebra of cells, a model of $`\mathcal{C}^{\Sigma^{(n)}}` by Proposition
`compact.cell-algebra-model`, and a homomorphism to itself as a homomorphism of partial algebras
(Construction `compact.hom-cells`) is a functor
$`\mathsf{nCatAlg}(\Sigma) \to \mathsf{PAlg}(\mathcal{C}^{\Sigma^{(n)}})`. The two constructions
of Construction `compact.hom-cells` are inverse to each other, which makes it fully faithful.

```lean
open CatAlgebra in
/-- The functor from `nCatAlg(Σ)` to `PAlg(C^{Σ^{(n)}})` that sends a compact `n`-categorial
algebra to its partial algebra of cells. -/
def cellsFunctor (n : ℕ) :
    CategoryTheory.Functor (CatAlgebra.{u, v, w} Sig n) (CompactPAlg.{u, v, w} Sig (Fin n)) where
  obj A := cellModel A.carrier A.op
  map H := Hom.toCells H
  map_id _ := rfl
  map_comp _ _ := rfl

open CatAlgebra in
/-- The functor of cells is fully faithful. -/
def cellsFunctor.fullyFaithful (n : ℕ) : (cellsFunctor.{u, v, w} (Sig := Sig) n).FullyFaithful where
  preimage h := Hom.ofCells h
  map_preimage _ := rfl
  preimage_map _ := rfl
```
:::

:::theorem (label := "compact.cat-alg-iso") (central := false) (title := "nCatAlg(Σ) = PAlg(C^Σ⁽ⁿ⁾)")
For every many-sorted signature $`\Sigma` and every $`n \in \mathbb{N}`, the functor of cells
$`\mathsf{nCatAlg}(\Sigma) \to \mathsf{PAlg}(\mathcal{C}^{\Sigma^{(n)}})` is full, faithful and
bijective on objects: it is an isomorphism of categories. This is the first part of
Proposition `PCompactIdent` of the draft, which writes it
$`\mathsf{nCatAlg}(\Sigma) = \mathsf{PAlg}(\mathcal{C}^{\Sigma^{(n)}})`. In particular it is an
equivalence of categories.

```lean
theorem cellsFunctor_obj_bijective (n : ℕ) :
    Function.Bijective (cellsFunctor.{u, v, w} (Sig := Sig) n).obj :=
  (catAlgebraEquivModel n).bijective

theorem cellsFunctor_isIso (n : ℕ) :
    (cellsFunctor.{u, v, w} (Sig := Sig) n).Full ∧ (cellsFunctor.{u, v, w} (Sig := Sig) n).Faithful ∧
      Function.Bijective (cellsFunctor.{u, v, w} (Sig := Sig) n).obj :=
  ⟨(cellsFunctor.fullyFaithful n).full, (cellsFunctor.fullyFaithful n).faithful,
    (catAlgebraEquivModel n).bijective⟩

instance (n : ℕ) : (cellsFunctor.{u, v, w} (Sig := Sig) n).IsEquivalence where
  faithful := (cellsFunctor.fullyFaithful n).faithful
  full := (cellsFunctor.fullyFaithful n).full
  essSurj := ⟨fun M => ⟨modelCatAlgebra M,
    ⟨CategoryTheory.eqToIso (Subtype.ext (cellAlgebra_modelCatAlgebra M))⟩⟩⟩
```
:::

:::proof (of := "compact.cat-alg-iso")
The functor is fully faithful by Construction `compact.cells-functor`, and bijective on objects by
Construction `compact.cat-algebra-equiv-model`, whose bijection is its action on objects. A
fully faithful functor that is surjective on objects is an equivalence.
:::
