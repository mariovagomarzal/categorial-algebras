import Stemma
import Mathlib.Data.PFun
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases
import CategorialAlgebras.Tactic

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "Globular higher-order categories" =>

In the *globular* presentation of a higher-order category the cells of each dimension form a
separate set: $`C_k` is the set of $`k`-cells, and for $`j < k` there are mappings sending a
$`k`-cell to its $`(j,k)`-source and $`(j,k)`-target, a mapping sending a $`j`-cell to its
$`(k,j)`-identity, and a partial $`j`-composition of $`k`-cells. This is the presentation of
Section `SGlobular` of the draft (the globular $`\omega`-categories of Definition `DOmegaCatGl`). The formalization
is ported from the group's repository
[`higher_category_theory`](https://github.com/mariovagomarzal/higher_category_theory), where it
is called *many-sorted*.

As in the single-set case, a single definition covers every preordered set of dimensions: a
globular $`n`-category has the dimensions $`0, \ldots, n` (so $`n + 1` sets of cells), and a
globular $`\omega`-category the dimensions $`k \in \mathbb{N}`.

```lean
universe u

namespace CategorialAlgebras.Extended

/-- Abbreviation for `Fin (n + 1)`, the dimensions of a globular `n`-category. -/
abbrev FinSucc (n : ℕ) := Fin (n + 1)

/-- A family of sets of cells, one for each dimension. -/
abbrev TypeFamily (Index : Type) := Index → Type u

/-- The families of sets of cells of a globular `n`-category. -/
abbrev NTypeFamily (n : ℕ) := TypeFamily.{u} (FinSucc n)

/-- The families of sets of cells of a globular `ω`-category. -/
abbrev OmegaTypeFamily := TypeFamily.{u} ℕ

/-- Notation for `lt_trans`, to pass composite inequalities to the operations. -/
scoped infixr:100 "≫" => lt_trans
```

# The data

:::definition (label := "extended.category-struct") (central := false) (title := "Globular categorial structure")
Let $`I` be a preordered set of dimensions and $`(C_k)_{k \in I}` a family of sets. A *globular
categorial structure* on it consists, for all $`j < k` in $`I`, of mappings
$`\mathrm{sc}^{(j,k)}, \mathrm{tg}^{(j,k)} \colon C_k \to C_j`, the $`(j,k)`-*source* and
*target*, a mapping $`\mathrm{i}^{(k,j)} \colon C_j \to C_k`, the $`(k,j)`-*identity*, and a
partial operation $`\circ^{(j)}` on $`C_k`, the $`j`-*composition of* $`k`-*cells*, whose
domain is the set of pairs $`(g, f)` with $`\mathrm{sc}^{(j,k)} g = \mathrm{tg}^{(j,k)} f`.

```lean
class CategoryStruct (Index : Type) [Preorder Index] (C : TypeFamily.{u} Index) where
  /-- Source operation at dimensions `(k, j)`. Maps `k`-morphisms to `j`-morphisms. -/
  sc : {k j : Index} → j < k → C k → C j
  /-- Target operation at dimensions `(k, j)`. Maps `k`-morphisms to `j`-morphisms. -/
  tg : {k j : Index} → j < k → C k → C j
  /-- Identity operation at dimensions `(k, j)`. Lifts `j`-morphisms to `k`-morphisms. -/
  idm : {k j : Index} → j < k → C j → C k
  /-- Partial composition operation at dimensions `(k, j)`. -/
  pcomp : {k j : Index} → j < k → C k → C k →. C k
  /-- The composition of `g` and `f` at dimensions `(k, j)` is defined if and only if the source of
  `g` at `(k, j)` equals the target of `f` at `(k, j)`. -/
  pcomp_dom : ∀ {k j : Index} {j_lt_k : j < k} {f g : C k},
      (pcomp j_lt_k g f).Dom ↔ sc j_lt_k g = tg j_lt_k f := by
    hcat_disch
```
:::

```lean
attribute [simp] CategoryStruct.pcomp_dom

namespace CategoryStruct

variable {Index : Type} [Preorder Index] {C : TypeFamily.{u} Index} [CategoryStruct Index C]
  {k j : Index} {j_lt_k : j < k} {f g : C k}

@[inherit_doc]
scoped[CategorialAlgebras.Extended] notation g " ♯.[" j_lt_k "] " f:100 =>
  CategoryStruct.pcomp j_lt_k g f

/-- A method to express the composability condition for morphisms `g` and `f` at dimensions `(k,
j)`, that is, that the source of `g` at `(k, j)` equals the target of `f` at `(k, j)`. -/
@[simp high]
def sc_is_tg {k j : Index} (j_lt_k : j < k) (g f : C k) : Prop :=
  sc j_lt_k g = tg j_lt_k f

/-- If `g` and `f` satisfy the composability condition `sc_is_tg j_lt_k g f`, then the partial
composition `g ♯.[j_lt_k] f` is defined. This lemma represents the forward direction of the
`pcomp_dom` axiom. -/
lemma dom_of_sc_is_tg (sc_tg_gf : sc_is_tg j_lt_k g f) : (g ♯.[j_lt_k] f).Dom :=
  pcomp_dom.mpr sc_tg_gf

/-- If the partial composition `g ♯.[j_lt_k] f` is defined, then `g` and `f` satisfy the
composability condition `sc_is_tg j_lt_k g f`. This is the backward direction of the `pcomp_dom`
axiom, that is, the converse of `dom_of_sc_is_tg`. -/
lemma sc_is_tg_of_dom (dom_gf : (g ♯.[j_lt_k] f).Dom) : sc_is_tg j_lt_k g f :=
  pcomp_dom.mp dom_gf

/-- The (total) composition operation at dimensions `(k, j)`, defined for composable morphisms.
Given morphisms `f` and `g` with a proof of `sc_is_tg j_lt_k g f`, this returns their composite
`g ♯[j_lt_k] f`. -/
@[simp high]
def comp {k j : Index} (j_lt_k : j < k) (g f : C k) (sc_tg_gf : sc_is_tg j_lt_k g f) : C k :=
  (g ♯.[j_lt_k] f).get (dom_of_sc_is_tg sc_tg_gf)

@[inherit_doc]
scoped[CategorialAlgebras.Extended] notation g " ♯[" j_lt_k "] " f " ← " sc_tg_gf:100 =>
  CategoryStruct.comp j_lt_k g f sc_tg_gf

end CategoryStruct

-- Export the main components of `CategoryStruct` for easier access.
export CategoryStruct (sc tg idm sc_is_tg)

section Congruence

variable {Index : Type} [Preorder Index] {C : TypeFamily.{u} Index} [CategoryStruct Index C]
  {k j : Index} {j_lt_k : j < k} {f₁ f₂ g₁ g₂ : C k}

/-- Congruence lemma for the domain of partial composition: if `f₁ = f₂` and `g₁ = g₂`, and the
partial composition `g₁ ♯.[j_lt_k] f₁` is defined, then `g₂ ♯.[j_lt_k] f₂` is also defined. -/
lemma congr_dom (eq_f : f₁ = f₂) (eq_g : g₁ = g₂) (dom_g₁f₁ : (g₁ ♯.[j_lt_k] f₁).Dom) :
    (g₂ ♯.[j_lt_k] f₂).Dom := by
  grind

/-- Congruence lemma for composability: if `f₁ = f₂` and `g₁ = g₂`, and `g₁` is composable with
`f₁` at dimensions `(k, j)`, then `g₂` is composable with `f₂` at dimensions `(k, j)`. -/
lemma congr_sc_is_tg (eq_f : f₁ = f₂) (eq_g : g₁ = g₂)
    (sc_tg_g₁f₁ : sc_is_tg j_lt_k g₁ f₁) : sc_is_tg j_lt_k g₂ f₂ := by
  grind

/-- Congruence lemma for partial composition: if `f₁ = f₂` and `g₁ = g₂`, then the partial
compositions `g₁ ♯.[j_lt_k] f₁` and `g₂ ♯.[j_lt_k] f₂` are equal as partial functions. -/
lemma congr_pcomp (eq_f : f₁ = f₂) (eq_g : g₁ = g₂) :
    g₁ ♯.[j_lt_k] f₁ = g₂ ♯.[j_lt_k] f₂ := by
  grind

/-- Congruence lemma for total composition (first-pair version): if `f₁ = f₂` and `g₁ = g₂`, then
the compositions `g₁ ♯[j_lt_k] f₁` and `g₂ ♯[j_lt_k] f₂` are equal, using the composability proof
from the first pair. -/
lemma congr_comp₁ (eq_f : f₁ = f₂) (eq_g : g₁ = g₂)
    (sc_tg_g₁f₁ : sc_is_tg j_lt_k g₁ f₁) :
    g₁ ♯[j_lt_k] f₁ ← sc_tg_g₁f₁ =
    g₂ ♯[j_lt_k] f₂ ← congr_sc_is_tg eq_f eq_g sc_tg_g₁f₁ := by
  grind

/-- Congruence lemma for total composition (second-pair version): if `f₁ = f₂` and `g₁ = g₂`, then
the compositions `g₁ ♯[j_lt_k] f₁` and `g₂ ♯[j_lt_k] f₂` are equal, using the composability proof
from the second pair. -/
lemma congr_comp₂ (eq_f : f₁ = f₂) (eq_g : g₁ = g₂)
    (sc_tg_g₂f₂ : sc_is_tg j_lt_k g₂ f₂) :
    g₁ ♯[j_lt_k] f₁ ← congr_sc_is_tg eq_f.symm eq_g.symm sc_tg_g₂f₂ =
    g₂ ♯[j_lt_k] f₂ ← sc_tg_g₂f₂ := by
  grind

end Congruence
```

# Globular categories

:::definition (label := "extended.precategory") (central := false) (title := "Globular precategory")
A globular categorial structure is a *globular precategory* if, for all $`j < k`, the
$`j`-cells and the $`k`-cells, with $`\mathrm{sc}^{(j,k)}`, $`\mathrm{tg}^{(j,k)}`,
$`\mathrm{i}^{(k,j)}` and $`\circ^{(j)}`, are the objects and the morphisms of a category:

1. (MS2) $`\mathrm{sc}^{(j,k)}(g \circ^{(j)} f) = \mathrm{sc}^{(j,k)} f` and
   $`\mathrm{tg}^{(j,k)}(g \circ^{(j)} f) = \mathrm{tg}^{(j,k)} g` when $`g \circ^{(j)} f`
   is defined;
2. (MS5) $`\mathrm{sc}^{(j,k)}\mathrm{i}^{(k,j)} u = u = \mathrm{tg}^{(j,k)}\mathrm{i}^{(k,j)} u`;
3. (MS6) $`f \circ^{(j)} \mathrm{i}^{(k,j)}\mathrm{sc}^{(j,k)} f = f = \mathrm{i}^{(k,j)}\mathrm{tg}^{(j,k)} f \circ^{(j)} f`;
4. (MS7) $`\circ^{(j)}` is associative where defined.

```lean
class PreCategory (Index : Type) [Preorder Index] (C : TypeFamily.{u} Index)
    extends CategoryStruct Index C where
  /-- The source of a composite `g ♯[j_lt_k] f` at dimensions `(k, j)` is the source of `f`. -/
  sckj_compkj_eq_sckj : ∀ {k j : Index} {j_lt_k : j < k} {f g : C k}
      (sc_tg_gf : sc_is_tg j_lt_k g f),
      sc j_lt_k (g ♯[j_lt_k] f ← sc_tg_gf) = sc j_lt_k f := by
    hcat_disch
  /-- The target of a composite `g ♯[j_lt_k] f` at dimensions `(k, j)` is the target of `g`. -/
  tgkj_compkj_eq_tgkj : ∀ {k j : Index} {j_lt_k : j < k} {f g : C k}
      (sc_tg_gf : sc_is_tg j_lt_k g f),
      tg j_lt_k (g ♯[j_lt_k] f ← sc_tg_gf) = tg j_lt_k g := by
    hcat_disch
  /-- The source of an identity `idm j_lt_k f` at dimensions `(k, j)` is `f`. -/
  sckj_idmkj : ∀ {k j : Index} (j_lt_k : j < k) (f : C j),
      sc j_lt_k (idm j_lt_k f) = f := by
    hcat_disch
  /-- The target of an identity `idm j_lt_k f` at dimensions `(k, j)` is `f`. -/
  tgkj_idmkj : ∀ {k j : Index} (j_lt_k : j < k) (f : C j),
      tg j_lt_k (idm j_lt_k f) = f := by
    hcat_disch
  /-- Composing `f` with the identity of its source at dimensions `(k, j)` yields `f`. -/
  compkj_idmkj_sckj_eq_id : ∀ {k j : Index} (j_lt_k : j < k) (f : C k),
      f ♯[j_lt_k] (idm j_lt_k (sc j_lt_k f)) ← (tgkj_idmkj j_lt_k (sc j_lt_k f)).symm = f := by
    hcat_disch
  /-- Composing the identity of the target of `f` with `f` at dimensions `(k, j)` yields `f`. -/
  compkj_tgkj_idmkj_eq_id : ∀ {k j : Index} (j_lt_k : j < k) (f : C k),
      (idm j_lt_k (tg j_lt_k f)) ♯[j_lt_k] f ← sckj_idmkj j_lt_k (tg j_lt_k f) = f := by
    hcat_disch
  /-- If `g` and `f` compose and `h` and `g` compose at dimensions `(k, j)`, then `h ♯[j_lt_k] g`
  and `f` compose. This is an auxiliary method for the associativity axiom. -/
  protected compl_assoc {k j : Index} {j_lt_k : j < k} {f g h : C k}
      (sc_tg_gf : sc_is_tg j_lt_k g f) (sc_tg_hg : sc_is_tg j_lt_k h g) :
      sc_is_tg j_lt_k (h ♯[j_lt_k] g ← sc_tg_hg) f := calc
    _
    _ = sc j_lt_k g := sckj_compkj_eq_sckj sc_tg_hg
    _ = tg j_lt_k f := sc_tg_gf
  /-- If `g` and `f` compose and `h` and `g` compose at dimensions `(k, j)`, then `h` and
  `g ♯[j_lt_k] f` compose. This is an auxiliary method for the associativity axiom. -/
  protected compr_assoc {k j : Index} {j_lt_k : j < k} {f g h : C k}
      (sc_tg_gf : sc_is_tg j_lt_k g f) (sc_tg_hg : sc_is_tg j_lt_k h g) :
      sc_is_tg j_lt_k h (g ♯[j_lt_k] f ← sc_tg_gf) := calc
    sc j_lt_k h
    _ = tg j_lt_k g := sc_tg_hg
    _ = _ := (tgkj_compkj_eq_tgkj sc_tg_gf).symm
  /-- The **associative property**: if `g` and `f` compose and `h` and `g` compose at dimensions
  `(k, j)`, then the two ways of composing `h`, `g`, and `f` exist and are equal. -/
  assoc : ∀ {k j : Index} {j_lt_k : j < k} {f g h : C k}
      (sc_tg_gf : sc_is_tg j_lt_k g f) (sc_tg_hg : sc_is_tg j_lt_k h g),
      ((h ♯[j_lt_k] g ← sc_tg_hg) ♯[j_lt_k] f ← (compl_assoc sc_tg_gf sc_tg_hg)) =
      (h ♯[j_lt_k] (g ♯[j_lt_k] f ← sc_tg_gf) ← (compr_assoc sc_tg_gf sc_tg_hg)) := by
    hcat_disch
```
:::

```lean
open PreCategory in
attribute [simp] sckj_compkj_eq_sckj tgkj_compkj_eq_tgkj sckj_idmkj tgkj_idmkj
  compkj_idmkj_sckj_eq_id compkj_tgkj_idmkj_eq_id assoc

/-- In a `PreCategory`, the identity map at `(k, j)` is injective as a function from `C j` to
`C k`. -/
theorem PreCategory.injetive_idm {Index : Type} [Preorder Index] {C : TypeFamily.{u} Index}
    [PreCategory Index C] {k j : Index} {j_lt_k : j < k} :
    Function.Injective (idm j_lt_k : C j → C k) := by
  intros f g eq_idm
  calc
    f
    _ = sc j_lt_k (idm j_lt_k f) := (sckj_idmkj j_lt_k f).symm
    _ = sc j_lt_k (idm j_lt_k g) := congrArg (sc j_lt_k) eq_idm
    _ = g := sckj_idmkj j_lt_k g
```

The conditions that relate three dimensions $`i < j < k` are (MS1), (MS3), (MS4), (MS8) and
(MS9) of Definition `DOmegaCatGl` of the draft; in this form they are those of the ported repository.

:::definition (label := "extended.category") (central := false) (title := "Globular higher-order category")
A *globular category with dimensions in* $`I` is a globular precategory such that, for all
$`i < j < k` in $`I`:

1. (MS1) $`\mathrm{sc}^{(i,j)}\mathrm{sc}^{(j,k)} f = \mathrm{sc}^{(i,k)} f = \mathrm{sc}^{(i,j)}\mathrm{tg}^{(j,k)} f`
   and $`\mathrm{tg}^{(i,j)}\mathrm{tg}^{(j,k)} f = \mathrm{tg}^{(i,k)} f = \mathrm{tg}^{(i,j)}\mathrm{sc}^{(j,k)} f`
   for $`f \in C_k`;
2. (MS3) if $`g \circ^{(i)} f` is defined in $`C_k`, then
   $`\mathrm{sc}^{(j,k)}(g \circ^{(i)} f) = \mathrm{sc}^{(j,k)} g \circ^{(i)} \mathrm{sc}^{(j,k)} f`,
   and likewise for targets;
3. (MS4) $`\mathrm{i}^{(k,j)}\mathrm{i}^{(j,i)} u = \mathrm{i}^{(k,i)} u` for $`u \in C_i`;
4. (MS8) if $`g \circ^{(i)} f` is defined in $`C_j`, then
   $`\mathrm{i}^{(k,j)}(g \circ^{(i)} f) = \mathrm{i}^{(k,j)} g \circ^{(i)} \mathrm{i}^{(k,j)} f`;
5. (MS9) the interchange law: if $`g' \circ^{(j)} g`, $`f' \circ^{(j)} f`, $`g' \circ^{(i)} f'`
   and $`g \circ^{(i)} f` are defined in $`C_k`, then
   $`(g' \circ^{(i)} f') \circ^{(j)} (g \circ^{(i)} f) = (g' \circ^{(j)} g) \circ^{(i)} (f' \circ^{(j)} f)`.

In the Lean, $`g'`, $`g`, $`f'`, $`f` are `g₂`, `g₁`, `f₂`, `f₁`, and the $`i`-composition of
$`k`-cells is written with the proof `i_lt_j ≫ j_lt_k` of $`i < k`.

```lean
class Category (Index : Type) [Preorder Index] (C : TypeFamily.{u} Index)
    extends PreCategory Index C where
  /-- Applying source at `(j, i)` to a source at `(k, j)` yields the source at `(k, i)`. -/
  scji_sckj_eq_scki : ∀ {k j i : Index} (j_lt_k : j < k) (i_lt_j : i < j) (f : C k),
      sc i_lt_j (sc j_lt_k f) = sc (i_lt_j ≫ j_lt_k) f := by
    hcat_disch
  /-- Applying source at `(j, i)` to a target at `(k, j)` yields the source at `(k, i)`. -/
  scji_tgkj_eq_scki : ∀ {k j i : Index} (j_lt_k : j < k) (i_lt_j : i < j) (f : C k),
      sc i_lt_j (tg j_lt_k f) = sc (i_lt_j ≫ j_lt_k) f := by
    hcat_disch
  /-- Applying target at `(j, i)` to a target at `(k, j)` yields the target at `(k, i)`. -/
  tgji_tgkj_eq_tgki : ∀ {k j i : Index} (j_lt_k : j < k) (i_lt_j : i < j) (f : C k),
      tg i_lt_j (tg j_lt_k f) = tg (i_lt_j ≫ j_lt_k) f := by
    hcat_disch
  /-- Applying target at `(j, i)` to a source at `(k, j)` yields the target at `(k, i)`. -/
  tgji_sckj_eq_tgki : ∀ {k j i : Index} (j_lt_k : j < k) (i_lt_j : i < j) (f : C k),
      tg i_lt_j (sc j_lt_k f) = tg (i_lt_j ≫ j_lt_k) f := by
    hcat_disch
  /-- If `g` and `f` are `(k, i)`-composable, then `sc j_lt_k g` and `sc j_lt_k f` are
  `(j, i)`-composable. This is an auxiliary method for the distributivity axioms. -/
  protected sc_tg_ji_sc {k j i : Index} {j_lt_k : j < k} {i_lt_j : i < j} {f g : C k}
      (sc_tg_ki_gf : sc_is_tg (i_lt_j ≫ j_lt_k) g f) :
      sc_is_tg i_lt_j (sc j_lt_k g) (sc j_lt_k f) := calc
    sc i_lt_j (sc j_lt_k g)
    _ = sc (i_lt_j ≫ j_lt_k) g := scji_sckj_eq_scki j_lt_k i_lt_j g
    _ = tg (i_lt_j ≫ j_lt_k) f := sc_tg_ki_gf
    _ = tg i_lt_j (sc j_lt_k f) := (tgji_sckj_eq_tgki j_lt_k i_lt_j f).symm
  /-- If `g` and `f` are `(k, i)`-composable, then `tg j_lt_k g` and `tg j_lt_k f` are
  `(j, i)`-composable. This is an auxiliary method for the distributivity axioms. -/
  protected sc_tg_ji_tg {k j i : Index} {j_lt_k : j < k} {i_lt_j : i < j} {f g : C k}
      (sc_tg_ki_gf : sc_is_tg (i_lt_j ≫ j_lt_k) g f) :
      sc_is_tg i_lt_j (tg j_lt_k g) (tg j_lt_k f) := calc
    sc i_lt_j (tg j_lt_k g)
    _ = sc (i_lt_j ≫ j_lt_k) g := scji_tgkj_eq_scki j_lt_k i_lt_j g
    _ = tg (i_lt_j ≫ j_lt_k) f := sc_tg_ki_gf
    _ = tg i_lt_j (tg j_lt_k f) := (tgji_tgkj_eq_tgki j_lt_k i_lt_j f).symm
  /-- Source at `(k, j)` distributes over composition at `(k, i)` with `i < j < k`. -/
  sckj_compki_eq_compji_sckj : ∀ {k j i : Index} {j_lt_k : j < k} {i_lt_j : i < j} {f g : C k}
      (sc_tg_ki_gf : sc_is_tg (i_lt_j ≫ j_lt_k) g f),
      sc j_lt_k (g ♯[i_lt_j ≫ j_lt_k] f ← sc_tg_ki_gf) =
      (sc j_lt_k g) ♯[i_lt_j] (sc j_lt_k f) ← (sc_tg_ji_sc sc_tg_ki_gf) := by
    hcat_disch
  /-- Target at `(k, j)` distributes over composition at `(k, i)` with `i < j < k`. -/
  tgkj_compki_eq_compji_tgkj :
      ∀ {k j i : Index} {j_lt_k : j < k} {i_lt_j : i < j} {f g : C k}
      (sc_tg_ki_gf : sc_is_tg (i_lt_j ≫ j_lt_k) g f),
      tg j_lt_k (g ♯[i_lt_j ≫ j_lt_k] f ← sc_tg_ki_gf) =
      (tg j_lt_k g) ♯[i_lt_j] (tg j_lt_k f) ← (sc_tg_ji_tg sc_tg_ki_gf) := by
    hcat_disch
  /-- Iterated identity maps compose transitively: `idm j_lt_k (idm i_lt_j f) = idm i_lt_k f`. -/
  idmkj_idmji_eq_idmki : ∀ {k j i : Index} (j_lt_k : j < k) (i_lt_j : i < j) (f : C i),
      idm j_lt_k (idm i_lt_j f) = idm (i_lt_j ≫ j_lt_k) f := by
    hcat_disch
  /-- If `g` and `f` are `(j, i)`-composable, then `idm j_lt_k g` and `idm j_lt_k f` are `(k,
  i)`-composable. This is an auxiliary method for the identity composition axiom. -/
  protected sc_tg_ki_idmkj {k j i : Index} {j_lt_k : j < k} {i_lt_j : i < j} {f g : C j}
      (sc_tg_ji_gf : sc_is_tg i_lt_j g f) :
      sc_is_tg (i_lt_j ≫ j_lt_k) (idm j_lt_k g) (idm j_lt_k f) := calc
    sc (i_lt_j ≫ j_lt_k) (idm j_lt_k g)
    _ = sc i_lt_j (sc j_lt_k (idm j_lt_k g)) := (scji_sckj_eq_scki j_lt_k i_lt_j _).symm
    _ = sc i_lt_j g := congrArg (sc i_lt_j) (sckj_idmkj j_lt_k g)
    _ = tg i_lt_j f := sc_tg_ji_gf
    _ = tg i_lt_j (tg j_lt_k (idm j_lt_k f)) := congrArg (tg i_lt_j) (tgkj_idmkj j_lt_k f).symm
    _ = tg (i_lt_j ≫ j_lt_k) (idm j_lt_k f) :=
      tgji_tgkj_eq_tgki j_lt_k i_lt_j (idm j_lt_k f)
  /-- Identity at `(k, j)` preserves composition at `(j, i)` with `i < j < k`. -/
  idmkj_compji_eq_compki_idmkj : ∀ {k j i : Index} {j_lt_k : j < k} {i_lt_j : i < j} {f g : C j}
      (sc_tg_ji_gf : sc_is_tg i_lt_j g f),
      idm j_lt_k (g ♯[i_lt_j] f ← sc_tg_ji_gf) =
      (idm j_lt_k g) ♯[i_lt_j ≫ j_lt_k] (idm j_lt_k f) ←
        (sc_tg_ki_idmkj sc_tg_ji_gf) := by
    hcat_disch
  /-- Given morphisms `f₁, f₂, g₁, g₂` with `g₂` and `g₁` `(k, j)`-composable, `f₂` and `f₁`
  `(k, j)`-composable, `g₂` and `f₂` `(k, i)`-composable, and `g₁` and `f₁` `(k,
  i)`-composable (with `i < j < k`), then `g₂ ♯[i_lt_k] f₂` and `g₁ ♯[i_lt_k] f₁` are `(k,
  j)`-composable. This is an auxiliary method for the `interchange` axiom. -/
  protected sc_tg_kj_interchange {k j i : Index} {j_lt_k : j < k} (i_lt_j : i < j)
      {f₁ f₂ g₁ g₂ : C k}
      (sc_tg_kj_g₂g₁ : sc_is_tg j_lt_k g₂ g₁)
      (sc_tg_kj_f₂f₁ : sc_is_tg j_lt_k f₂ f₁)
      (sc_tg_ki_g₂f₂ : sc_is_tg (i_lt_j ≫ j_lt_k) g₂ f₂)
      (sc_tg_ki_g₁f₁ : sc_is_tg (i_lt_j ≫ j_lt_k) g₁ f₁) :
      sc_is_tg j_lt_k
        (g₂ ♯[i_lt_j ≫ j_lt_k] f₂ ← sc_tg_ki_g₂f₂)
        (g₁ ♯[i_lt_j ≫ j_lt_k] f₁ ← sc_tg_ki_g₁f₁) := calc
    _
    _ = (sc j_lt_k g₂) ♯[i_lt_j] (sc j_lt_k f₂) ← (sc_tg_ji_sc sc_tg_ki_g₂f₂) :=
      sckj_compki_eq_compji_sckj sc_tg_ki_g₂f₂
    _ = (tg j_lt_k g₁) ♯[i_lt_j] (tg j_lt_k f₁) ← (sc_tg_ji_tg sc_tg_ki_g₁f₁) :=
      congr_comp₁ sc_tg_kj_f₂f₁ sc_tg_kj_g₂g₁ (sc_tg_ji_sc sc_tg_ki_g₂f₂)
    _ = _ := (tgkj_compki_eq_compji_tgkj sc_tg_ki_g₁f₁).symm
  /--
  Given morphisms `f₁, f₂, g₁, g₂` with `g₂` and `g₁` `(k, j)`-composable, `f₂` and `f₁` `(k,
  j)`-composable, and `g₂` and `f₂` `(k, i)`-composable (with `i < j < k`), then `g₂ ♯[j_lt_k] g₁`
  and `f₂ ♯[j_lt_k] f₁` are `(k, i)`-composable. This is an auxiliary method for the `interchange`
  axiom.

  Note: an equivalent formulation replaces the hypothesis `sc_is_tg (i_lt_j ≫ j_lt_k) g₂ f₂`
  with `sc_is_tg (i_lt_j ≫ j_lt_k) g₁ f₁`. Both are interderivable from the remaining
  hypotheses and the cross-dimensional axioms, so either one suffices. We choose
  `sc_is_tg (i_lt_j ≫ j_lt_k) g₂ f₂` because it aligns directly with the target side of the
  goal, yielding a shorter proof.
  -/
  protected sc_tg_ki_interchange {k j i : Index} {j_lt_k : j < k} (i_lt_j : i < j)
      {f₁ f₂ g₁ g₂ : C k}
      (sc_tg_kj_g₂g₁ : sc_is_tg j_lt_k g₂ g₁)
      (sc_tg_kj_f₂f₁ : sc_is_tg j_lt_k f₂ f₁)
      (sc_tg_ki_g₂f₂ : sc_is_tg (i_lt_j ≫ j_lt_k) g₂ f₂) :
      sc_is_tg (i_lt_j ≫ j_lt_k)
        (g₂ ♯[j_lt_k] g₁ ← sc_tg_kj_g₂g₁)
        (f₂ ♯[j_lt_k] f₁ ← sc_tg_kj_f₂f₁) := calc
    _
    _ = sc i_lt_j (tg j_lt_k (g₂ ♯[j_lt_k] g₁ ← sc_tg_kj_g₂g₁)) :=
      (scji_tgkj_eq_scki j_lt_k i_lt_j _).symm
    _ = sc i_lt_j (tg j_lt_k g₂) := by rw [tgkj_compkj_eq_tgkj sc_tg_kj_g₂g₁]
    _ = sc (i_lt_j ≫ j_lt_k) g₂ := scji_tgkj_eq_scki j_lt_k i_lt_j g₂
    _ = tg (i_lt_j ≫ j_lt_k) f₂ := sc_tg_ki_g₂f₂
    _ = tg i_lt_j (tg j_lt_k f₂) := (tgji_tgkj_eq_tgki j_lt_k i_lt_j f₂).symm
    _ = tg i_lt_j (tg j_lt_k (f₂ ♯[j_lt_k] f₁ ← sc_tg_kj_f₂f₁)) :=
      congrArg (tg i_lt_j) (tgkj_compkj_eq_tgkj sc_tg_kj_f₂f₁).symm
    _ = tg (i_lt_j ≫ j_lt_k) (f₂ ♯[j_lt_k] f₁ ← sc_tg_kj_f₂f₁) :=
      tgji_tgkj_eq_tgki j_lt_k i_lt_j _
  /--
  The **interchange law**: Given morphisms `f₁, f₂, g₁, g₂` and indices `i < j < k` such that:
  - `g₂` is composable with `g₁` at dimensions `(k, j)`,
  - `f₂` is composable with `f₁` at dimensions `(k, j)`,
  - `g₂` is composable with `f₂` at dimensions `(k, i)`, and
  - `g₁` is composable with `f₁` at dimensions `(k, i)`,

  then both `(g₂ ♯[i_lt_k] f₂) ♯[j_lt_k] (g₁ ♯[i_lt_k] f₁)` and
  `(g₂ ♯[j_lt_k] g₁) ♯[i_lt_k] (f₂ ♯[j_lt_k] f₁)` are defined and equal. That is, composing first
  at dimension `i` and then at dimension `j` yields the same result as composing first at dimension
  `j` and then at dimension `i`.
  -/
  interchange : ∀ {k j i : Index} {j_lt_k : j < k} {i_lt_j : i < j} {f₁ f₂ g₁ g₂ : C k}
      (sc_tg_kj_g₂g₁ : sc_is_tg j_lt_k g₂ g₁)
      (sc_tg_kj_f₂f₁ : sc_is_tg j_lt_k f₂ f₁)
      (sc_tg_ki_g₂f₂ : sc_is_tg (i_lt_j ≫ j_lt_k) g₂ f₂)
      (sc_tg_ki_g₁f₁ : sc_is_tg (i_lt_j ≫ j_lt_k) g₁ f₁),
      (g₂ ♯[i_lt_j ≫ j_lt_k] f₂ ← sc_tg_ki_g₂f₂) ♯[j_lt_k]
        (g₁ ♯[i_lt_j ≫ j_lt_k] f₁ ← sc_tg_ki_g₁f₁) ←
        (sc_tg_kj_interchange i_lt_j sc_tg_kj_g₂g₁ sc_tg_kj_f₂f₁
          sc_tg_ki_g₂f₂ sc_tg_ki_g₁f₁) =
      (g₂ ♯[j_lt_k] g₁ ← sc_tg_kj_g₂g₁) ♯[i_lt_j ≫ j_lt_k]
        (f₂ ♯[j_lt_k] f₁ ← sc_tg_kj_f₂f₁) ←
        (sc_tg_ki_interchange i_lt_j sc_tg_kj_g₂g₁ sc_tg_kj_f₂f₁
          sc_tg_ki_g₂f₂) := by
    hcat_disch
```
:::

```lean
open Category in
attribute [simp] scji_sckj_eq_scki scji_tgkj_eq_scki tgji_tgkj_eq_tgki tgji_sckj_eq_tgki
  sckj_compki_eq_compji_sckj tgkj_compki_eq_compji_tgkj idmkj_idmji_eq_idmki
  idmkj_compji_eq_compki_idmkj interchange
```

:::definition (label := "extended.n-category") (central := false) (title := "Globular n-category and ω-category")
A *globular* $`n`-*category* is a globular category with dimensions in
$`n + 1 = \{0, \ldots, n\}`, and a *globular* $`\omega`-*category* one with dimensions in
$`\mathbb{N}` (Definition `DOmegaCatGl` of the draft and the paragraph after it).

```lean
abbrev NCategory (n : ℕ) (C : NTypeFamily.{u} n) := Category (FinSucc n) C

abbrev OmegaCategory (C : OmegaTypeFamily.{u}) := Category ℕ C
```
:::

:::construction (label := "extended.one-category-of-precategory") (central := false) (title := "Globular 1-categories")
A globular precategory with dimensions $`0, 1` is a globular $`1`-category: there are no
three dimensions $`i < j < k`, and the conditions relating them hold vacuously.

```lean
@[instance_reducible]
def PreCategory.lift {C : NTypeFamily.{u} 1} [S : PreCategory (FinSucc 1) C] : NCategory 1 C :=
  { S with
    scji_sckj_eq_scki := by fin_omega
    scji_tgkj_eq_scki := by fin_omega
    tgji_tgkj_eq_tgki := by fin_omega
    tgji_sckj_eq_tgki := by fin_omega
    sckj_compki_eq_compji_sckj := by fin_omega
    tgkj_compki_eq_compji_tgkj := by fin_omega
    idmkj_idmji_eq_idmki := by fin_omega
    idmkj_compji_eq_compki_idmkj := by fin_omega
    interchange := by fin_omega }
```
:::

```lean
end CategorialAlgebras.Extended
```
