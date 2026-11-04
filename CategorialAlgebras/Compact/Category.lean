import Mathlib.Data.PFun
import Mathlib.Order.Fin.Basic
import CategorialAlgebras.Tactic

/-!
# Single-set higher-order categories

In the *single-set* presentation of a higher-order category all the cells, whatever their
dimension, live in a single set, and the dimension of a cell is read off from sources and
targets: a cell is a $k$-cell when its $k$-source is itself. This is the presentation of
Section `SSingleSet` of the draft on higher-order categorial algebras. The formalization below is ported
from the group's repository
[`higher_category_theory`](https://github.com/mariovagomarzal/higher_category_theory) (by Enric
Cosme Llópez, Raúl Ruiz Mora and Mario Vago Marzal, Apache 2.0), where the single-set presentation
is called *single-sorted*.

Instead of defining single-set categories, single-set $2$-categories and single-set $n$-categories one
after the other, the three are instances of a single definition, indexed by a preordered set
of dimensions: a single-set category has one dimension, a single-set $n$-category has the
dimensions $k \in n = \{0, \ldots, n-1\}$, and a single-set $\omega$-category has the dimensions
$k \in \mathbb{N}$.
-/

universe u

namespace CategorialAlgebras.Compact

/-!
## The data
-/

/-- Let $I$ be a set of dimensions. A *single-set categorial structure* on a set $C$ indexed by $I$
consists, for every $k \in I$, of two mappings $\mathrm{sc}^{k}, \mathrm{tg}^{k} \colon C \to C$,
the $k$-*source* and the $k$-*target*, and of a partial binary operation $\#^{k}$ on $C$,
the $k$-*composition*, such that $g \#^{k} f$ is defined if and only if
$\mathrm{sc}^{k}(g) = \mathrm{tg}^{k}(f)$. This is condition (C2) of Definition `DSingleSetCat` of the
draft, for every dimension.
-/
class CategoryStruct (Index : Type) (C : Type u) where
  /-- Source operation at dimension `k`. -/
  sc : Index → C → C
  /-- Target operation at dimension `k`. -/
  tg : Index → C → C
  /-- Partial composition operation at dimension `k`. -/
  pcomp : Index → C → C →. C
  /-- The composition of `g` and `f` at dimension `k` is defined if and only if the source of `g`
  at dimension `k` equals the target of `f` at dimension `k`. -/
  pcomp_dom : ∀ {k : Index} {f g : C}, (pcomp k g f).Dom ↔ sc k g = tg k f := by hcat_disch

attribute [simp] CategoryStruct.pcomp_dom

namespace CategoryStruct

variable {Index : Type} {C : Type u} [CategoryStruct Index C] {k : Index} {f g : C}

@[inherit_doc]
scoped[CategorialAlgebras.Compact] notation g " ♯.[" k "] " f:100 =>
  CategoryStruct.pcomp k g f

/-- The composability condition: the source of `g` at dimension `k` is the target of `f`. -/
@[simp high]
def sc_is_tg (k : Index) (g f : C) : Prop := sc k g = tg k f

lemma dom_of_sc_is_tg (sc_tg_gf : sc_is_tg k g f) : (g ♯.[k] f).Dom := pcomp_dom.mpr sc_tg_gf

lemma sc_is_tg_of_dom (dom_gf : (g ♯.[k] f).Dom) : sc_is_tg k g f := pcomp_dom.mp dom_gf

/-- The composite `g ♯[k] f` of two composable cells. -/
@[simp high]
def comp (k : Index) (g f : C) (sc_tg_gf : sc_is_tg k g f) : C :=
  (g ♯.[k] f).get (dom_of_sc_is_tg sc_tg_gf)

@[inherit_doc]
scoped[CategorialAlgebras.Compact] notation g " ♯[" k "] " f " ← " sc_tg_gf:100 =>
  CategoryStruct.comp k g f sc_tg_gf

end CategoryStruct

export CategoryStruct (sc tg sc_is_tg)

section Congruence

variable {Index : Type} {C : Type u} [CategoryStruct Index C] {k : Index} {f₁ f₂ g₁ g₂ : C}

lemma congr_dom (eq_f : f₁ = f₂) (eq_g : g₁ = g₂) (dom_g₁f₁ : (g₁ ♯.[k] f₁).Dom) :
    (g₂ ♯.[k] f₂).Dom := by
  rw [eq_f, eq_g] at dom_g₁f₁
  exact dom_g₁f₁

lemma congr_sc_is_tg (eq_f : f₁ = f₂) (eq_g : g₁ = g₂) (sc_tg_g₁f₁ : sc_is_tg k g₁ f₁) :
    sc_is_tg k g₂ f₂ := by
  rw [eq_f, eq_g] at sc_tg_g₁f₁
  exact sc_tg_g₁f₁

lemma congr_pcomp (k : Index) (eq_f : f₁ = f₂) (eq_g : g₁ = g₂) :
    g₁ ♯.[k] f₁ = g₂ ♯.[k] f₂ := by
  rw [eq_f, eq_g]

lemma congr_comp₁ (eq_f : f₁ = f₂) (eq_g : g₁ = g₂)
    (sc_tg_g₁f₁ : sc_is_tg k g₁ f₁) :
    g₁ ♯[k] f₁ ← sc_tg_g₁f₁ = g₂ ♯[k] f₂ ← congr_sc_is_tg eq_f eq_g sc_tg_g₁f₁ := by
  subst eq_f eq_g
  simp only [CategoryStruct.comp]

lemma congr_comp₂ (eq_f : f₁ = f₂) (eq_g : g₁ = g₂)
    (sc_tg_g₂f₂ : sc_is_tg k g₂ f₂) :
    g₁ ♯[k] f₁ ← congr_sc_is_tg eq_f.symm eq_g.symm sc_tg_g₂f₂ = g₂ ♯[k] f₂ ← sc_tg_g₂f₂ := by
  subst eq_f eq_g
  simp only [CategoryStruct.comp]

end Congruence

/-!
## Single-set categories
-/

/-- A single-set categorial structure is a *single-set precategory* if, for every dimension $k$, the
triple $(\#^{k}, \mathrm{sc}^{k}, \mathrm{tg}^{k})$ is a structure of single-set category on
$C$ (Definition `DSingleSetCat` of the draft): for all $f, g, h \in C$,

1. (C1) $\mathrm{sc}^{k}\mathrm{sc}^{k} f = \mathrm{sc}^{k} f$,
   $\mathrm{tg}^{k}\mathrm{sc}^{k} f = \mathrm{sc}^{k} f$,
   $\mathrm{sc}^{k}\mathrm{tg}^{k} f = \mathrm{tg}^{k} f$ and
   $\mathrm{tg}^{k}\mathrm{tg}^{k} f = \mathrm{tg}^{k} f$;
2. (C3) if $\mathrm{sc}^{k} g = \mathrm{tg}^{k} f$, then
   $\mathrm{sc}^{k}(g \#^{k} f) = \mathrm{sc}^{k} f$ and
   $\mathrm{tg}^{k}(g \#^{k} f) = \mathrm{tg}^{k} g$;
3. (C4) $f \#^{k} \mathrm{sc}^{k} f = f = \mathrm{tg}^{k} f \#^{k} f$;
4. (C5) if $\mathrm{sc}^{k} h = \mathrm{tg}^{k} g$ and $\mathrm{sc}^{k} g = \mathrm{tg}^{k} f$,
   then $h \#^{k} (g \#^{k} f) = (h \#^{k} g) \#^{k} f$.

A single-set category in the sense of Definition `DSingleSetCat` is a single-set precategory with a single
dimension.
-/
class PreCategory (Index : Type) (C : Type u)
    extends CategoryStruct Index C where
  /-- Applying source twice at dimension `k` is idempotent. -/
  sck_sck_eq_sck : ∀ (k : Index) (f : C), sc k (sc k f) = sc k f := by hcat_disch
  /-- The target of a source is itself. -/
  tgk_sck_eq_sck : ∀ (k : Index) (f : C), tg k (sc k f) = sc k f := by hcat_disch
  /-- The source of a target is itself. -/
  sck_tgk_eq_tgk : ∀ (k : Index) (f : C), sc k (tg k f) = tg k f := by hcat_disch
  /-- Applying target twice at dimension `k` is idempotent. -/
  tgk_tgk_eq_tgk : ∀ (k : Index) (f : C), tg k (tg k f) = tg k f := by hcat_disch
  /-- The source of a composite `g ♯[k] f` is the source of `f`. -/
  sck_compk_eq_sck : ∀ {k : Index} {f g : C} (sc_tg_gf : sc_is_tg k g f),
      sc k (g ♯[k] f ← sc_tg_gf) = sc k f := by
    hcat_disch
  /-- The target of a composite `g ♯[k] f` is the target of `g`. -/
  tgk_compk_eq_tgk : ∀ {k : Index} {f g : C} (sc_tg_gf : sc_is_tg k g f),
      tg k (g ♯[k] f ← sc_tg_gf) = tg k g := by
    hcat_disch
  /-- Composing `f` with its source `sc k f` yields `f`. -/
  compk_sck_eq_id : ∀ (k : Index) (f : C),
      f ♯[k] (sc k f) ← (tgk_sck_eq_sck k f).symm = f := by
    hcat_disch
  /-- Composing the target `tg k f` with `f` yields `f`. -/
  compk_tgk_eq_id : ∀ (k : Index) (f : C),
      (tg k f) ♯[k] f ← (sck_tgk_eq_tgk k f) = f := by
    hcat_disch
  /-- Auxiliary: if `g` and `f` compose and `h` and `g` compose, then `h ♯[k] g` and `f`
  compose. -/
  protected compl_assoc {k : Index} {f g h : C}
      (sc_tg_gf : sc_is_tg k g f) (sc_tg_hg : sc_is_tg k h g) :
      sc_is_tg k (h ♯[k] g ← sc_tg_hg) f := calc
    _
    _ = sc k g := sck_compk_eq_sck sc_tg_hg
    _ = tg k f := sc_tg_gf
  /-- Auxiliary: if `g` and `f` compose and `h` and `g` compose, then `h` and `g ♯[k] f`
  compose. -/
  protected compr_assoc {k : Index} {f g h : C}
      (sc_tg_gf : sc_is_tg k g f) (sc_tg_hg : sc_is_tg k h g) :
      sc_is_tg k h (g ♯[k] f ← sc_tg_gf) := calc
    sc k h
    _ = tg k g := sc_tg_hg
    _ = _ := (tgk_compk_eq_tgk sc_tg_gf).symm
  /-- Associativity of the composition at every dimension. -/
  assoc : ∀ {k : Index} {f g h : C} (sc_tg_gf : sc_is_tg k g f) (sc_tg_hg : sc_is_tg k h g),
      ((h ♯[k] g ← sc_tg_hg) ♯[k] f ← (compl_assoc sc_tg_gf sc_tg_hg)) =
      (h ♯[k] (g ♯[k] f ← sc_tg_gf) ← (compr_assoc sc_tg_gf sc_tg_hg)) := by
    hcat_disch

open PreCategory in
attribute [simp] sck_sck_eq_sck tgk_sck_eq_sck sck_tgk_eq_tgk tgk_tgk_eq_tgk sck_compk_eq_sck
  tgk_compk_eq_tgk compk_sck_eq_id compk_tgk_eq_id assoc

/-!
## Single-set higher-order categories

The conditions (2C1)–(2C3) of Definition `DSingleSet2Cat` of the draft relate two dimensions $j < k$; a
single-set $n$-category (Definition `DSingleSetnCat`) asks them for every pair of dimensions $j < k$ in $n$.
Here they are asked for every pair $j < k$ of any preordered set of dimensions.
-/

/-- Let $I$ be a preordered set of dimensions. A *single-set category with dimensions in* $I$ is a
single-set precategory such that, for all dimensions $j < k$ and all $f, g, f', g' \in C$,

1. (2C1) $\mathrm{sc}^{k}\mathrm{sc}^{j} f = \mathrm{sc}^{j} f = \mathrm{sc}^{j}\mathrm{sc}^{k} f = \mathrm{sc}^{j}\mathrm{tg}^{k} f$
   and $\mathrm{tg}^{k}\mathrm{tg}^{j} f = \mathrm{tg}^{j} f = \mathrm{tg}^{j}\mathrm{tg}^{k} f = \mathrm{tg}^{j}\mathrm{sc}^{k} f$;
2. (2C2) if $\mathrm{sc}^{j} g = \mathrm{tg}^{j} f$, then
   $\mathrm{sc}^{k}(g \#^{j} f) = \mathrm{sc}^{k} g \#^{j} \mathrm{sc}^{k} f$ and
   $\mathrm{tg}^{k}(g \#^{j} f) = \mathrm{tg}^{k} g \#^{j} \mathrm{tg}^{k} f$;
3. (2C3) the *interchange law*: if $\mathrm{sc}^{k} g' = \mathrm{tg}^{k} g$,
   $\mathrm{sc}^{k} f' = \mathrm{tg}^{k} f$, $\mathrm{sc}^{j} g' = \mathrm{tg}^{j} f'$ and
   $\mathrm{sc}^{j} g = \mathrm{tg}^{j} f$, then
   $(g' \#^{j} f') \#^{k} (g \#^{j} f) = (g' \#^{k} g) \#^{j} (f' \#^{k} f)$.

In the Lean, $g'$, $g$, $f'$, $f$ are `g₂`, `g₁`, `f₂`, `f₁`. That both sides of the
interchange law are defined is a consequence of the other axioms: the auxiliary fields
`sc_tg_k_interchange` and `sc_tg_j_interchange` prove it, and the second one shows that one of
the four hypotheses of the draft, $\mathrm{sc}^{j} g = \mathrm{tg}^{j} f$, is not needed for
the right-hand side to be defined.
-/
class Category (Index : Type) [Preorder Index] (C : Type u)
    extends PreCategory Index C where
  /-- (2C1) -/
  sck_scj_eq_scj : ∀ {k j : Index} (f : C) (_ : j < k), sc k (sc j f) = sc j f := by hcat_disch
  /-- (2C1) -/
  scj_sck_eq_scj : ∀ {k j : Index} (f : C) (_ : j < k), sc j (sc k f) = sc j f := by hcat_disch
  /-- (2C1) -/
  scj_tgk_eq_scj : ∀ {k j : Index} (f : C) (_ : j < k), sc j (tg k f) = sc j f := by hcat_disch
  /-- (2C1) -/
  tgk_tgj_eq_tgj : ∀ {k j : Index} (f : C) (_ : j < k), tg k (tg j f) = tg j f := by hcat_disch
  /-- (2C1) -/
  tgj_tgk_eq_tgj : ∀ {k j : Index} (f : C) (_ : j < k), tg j (tg k f) = tg j f := by hcat_disch
  /-- (2C1) -/
  tgj_sck_eq_tgj : ∀ {k j : Index} (f : C) (_ : j < k), tg j (sc k f) = tg j f := by hcat_disch
  /-- Auxiliary: the `k`-sources of `j`-composable cells are `j`-composable. -/
  protected sc_tg_j_sc {k j : Index} {f g : C} (j_lt_k : j < k) (sc_tg_j_gf : sc_is_tg j g f) :
      sc_is_tg j (sc k g) (sc k f) := calc
    sc j (sc k g)
    _ = sc j g := scj_sck_eq_scj g j_lt_k
    _ = tg j f := sc_tg_j_gf
    _ = tg j (sc k f) := (tgj_sck_eq_tgj f j_lt_k).symm
  /-- Auxiliary: the `k`-targets of `j`-composable cells are `j`-composable. -/
  protected sc_tg_j_tg {k j : Index} {f g : C} (j_lt_k : j < k) (sc_tg_j_gf : sc_is_tg j g f) :
      sc_is_tg j (tg k g) (tg k f) := calc
    sc j (tg k g)
    _ = sc j g := scj_tgk_eq_scj g j_lt_k
    _ = tg j f := sc_tg_j_gf
    _ = tg j (tg k f) := (tgj_tgk_eq_tgj f j_lt_k).symm
  /-- (2C2) -/
  sck_compj_eq_compj_sck : ∀ {k j : Index} {f g : C} (j_lt_k : j < k)
      (sc_tg_j_gf : sc_is_tg j g f),
      sc k (g ♯[j] f ← sc_tg_j_gf) = (sc k g) ♯[j] (sc k f) ← (sc_tg_j_sc j_lt_k sc_tg_j_gf) := by
    hcat_disch
  /-- (2C2) -/
  tgk_compj_eq_compj_tgk : ∀ {k j : Index} {f g : C} (j_lt_k : j < k)
      (sc_tg_j_gf : sc_is_tg j g f),
      tg k (g ♯[j] f ← sc_tg_j_gf) = (tg k g) ♯[j] (tg k f) ← (sc_tg_j_tg j_lt_k sc_tg_j_gf) := by
    hcat_disch
  /-- Auxiliary: the left-hand side of the interchange law is defined. -/
  protected sc_tg_k_interchange {k j : Index} {f₁ f₂ g₁ g₂ : C} (j_lt_k : j < k)
      (sc_tg_k_g₂g₁ : sc_is_tg k g₂ g₁) (sc_tg_k_f₂f₁ : sc_is_tg k f₂ f₁)
      (sc_tg_j_g₂f₂ : sc_is_tg j g₂ f₂) (sc_tg_j_g₁f₁ : sc_is_tg j g₁ f₁) :
      sc_is_tg k (g₂ ♯[j] f₂ ← sc_tg_j_g₂f₂) (g₁ ♯[j] f₁ ← sc_tg_j_g₁f₁) := calc
    _
    _ = (sc k g₂) ♯[j] (sc k f₂) ← (sc_tg_j_sc j_lt_k sc_tg_j_g₂f₂) :=
      sck_compj_eq_compj_sck j_lt_k sc_tg_j_g₂f₂
    _ = (tg k g₁) ♯[j] (tg k f₁) ← (sc_tg_j_tg j_lt_k sc_tg_j_g₁f₁) :=
      congr_comp₁ sc_tg_k_f₂f₁ sc_tg_k_g₂g₁ (sc_tg_j_sc j_lt_k sc_tg_j_g₂f₂)
    _ = _ := (tgk_compj_eq_compj_tgk j_lt_k sc_tg_j_g₁f₁).symm
  /-- Auxiliary: the right-hand side of the interchange law is defined. -/
  protected sc_tg_j_interchange {k j : Index} {f₁ f₂ g₁ g₂ : C} (j_lt_k : j < k)
      (sc_tg_k_g₂g₁ : sc_is_tg k g₂ g₁) (sc_tg_k_f₂f₁ : sc_is_tg k f₂ f₁)
      (sc_tg_j_g₂f₂ : sc_is_tg j g₂ f₂) :
      sc_is_tg j (g₂ ♯[k] g₁ ← sc_tg_k_g₂g₁) (f₂ ♯[k] f₁ ← sc_tg_k_f₂f₁) := calc
    _
    _ = sc j (tg k (g₂ ♯[k] g₁ ← sc_tg_k_g₂g₁)) := (scj_tgk_eq_scj _ j_lt_k).symm
    _ = sc j (tg k g₂) := by rw [tgk_compk_eq_tgk sc_tg_k_g₂g₁]
    _ = sc j g₂ := scj_tgk_eq_scj g₂ j_lt_k
    _ = tg j f₂ := sc_tg_j_g₂f₂
    _ = tg j (tg k f₂) := (tgj_tgk_eq_tgj f₂ j_lt_k).symm
    _ = tg j (tg k (f₂ ♯[k] f₁ ← sc_tg_k_f₂f₁)) := by rw [tgk_compk_eq_tgk sc_tg_k_f₂f₁]
    _ = tg j (f₂ ♯[k] f₁ ← sc_tg_k_f₂f₁) := tgj_tgk_eq_tgj _ j_lt_k
  /-- (2C3) The interchange law. -/
  interchange : ∀ {k j : Index} {f₁ f₂ g₁ g₂ : C} (j_lt_k : j < k)
      (sc_tg_k_g₂g₁ : sc_is_tg k g₂ g₁) (sc_tg_k_f₂f₁ : sc_is_tg k f₂ f₁)
      (sc_tg_j_g₂f₂ : sc_is_tg j g₂ f₂) (sc_tg_j_g₁f₁ : sc_is_tg j g₁ f₁),
      (g₂ ♯[j] f₂ ← sc_tg_j_g₂f₂) ♯[k] (g₁ ♯[j] f₁ ← sc_tg_j_g₁f₁) ←
        (sc_tg_k_interchange j_lt_k sc_tg_k_g₂g₁ sc_tg_k_f₂f₁ sc_tg_j_g₂f₂ sc_tg_j_g₁f₁) =
      (g₂ ♯[k] g₁ ← sc_tg_k_g₂g₁) ♯[j] (f₂ ♯[k] f₁ ← sc_tg_k_f₂f₁) ←
        (sc_tg_j_interchange j_lt_k sc_tg_k_g₂g₁ sc_tg_k_f₂f₁ sc_tg_j_g₂f₂) := by
    hcat_disch

open Category in
attribute [simp] sck_scj_eq_scj scj_sck_eq_scj scj_tgk_eq_scj tgk_tgj_eq_tgj tgj_tgk_eq_tgj
  tgj_sck_eq_tgj sck_compj_eq_compj_sck tgk_compj_eq_compj_tgk interchange

/-- For $n \in \mathbb{N}$, a *single-set* $n$-*category* is a single-set category with dimensions in
$n = \{0, \ldots, n-1\}$.

As in Definition `DSingleSetnCat` of the draft, the definition is made for every $n$. A single-set $0$-category is a set, with no structure; a single-set
$1$-category is a single-set category in the sense of Definition `DSingleSetCat`, and a single-set
$2$-category is one in the sense of Definition `DSingleSet2Cat`.
-/
abbrev NCategory (n : ℕ) (C : Type u) := Category (Fin n) C

set_option hcat.tactic.omega true in
/-- A single-set precategory with a single dimension is a single-set $1$-category: with one dimension
there are no pairs $j < k$, and the axioms (2C1)–(2C3) hold vacuously.
-/
@[instance_reducible]
def PreCategory.lift {C : Type u} [S : PreCategory (Fin 1) C] : NCategory 1 C := {S with}

/-!
## Cells
-/

section Cells

variable {Index : Type} [Preorder Index] {C : Type u} [Category Index C]

/-!
### k-cells

In a single-set category $C$ with dimensions in $I$, a cell $f$ is a $k$-*cell*, for
$k \in I$, if $\mathrm{sc}^{k} f = f$ (equivalently, by (C1), if $\mathrm{tg}^{k} f = f$).
We write $C_{k}$ for the set of $k$-cells.
-/

@[simp]
def cell (k : Index) (f : C) : Prop :=
  sc k f = f

@[simp]
def cells (k : Index) (C : Type u) [Category Index C] : Set C :=
  {f : C | cell k f}

end Cells

open Category in
/-- A *single-set* $\omega$-*category* is a single-set category with dimensions in $\mathbb{N}$ in which
every cell is a $k$-cell for some $k \in \mathbb{N}$.
-/
class OmegaCategory (C : Type u) extends Category ℕ C where
  /-- Every cell is a `k`-cell for some `k : ℕ`. -/
  is_cell : ∀ f : C, ∃ k : ℕ, cell k f

attribute [simp] OmegaCategory.is_cell

end CategorialAlgebras.Compact
