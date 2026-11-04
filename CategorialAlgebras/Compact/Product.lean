import CategorialAlgebras.Compact.Functor

/-!
# Products of single-set categories

The operations of a many-sorted categorial algebra are functors out of finite products of
single-set categories: an operation symbol of arity $\mathbf{s} = (s_0, \ldots, s_{m-1})$ is
interpreted as a functor from $\mathsf{A}_{\mathbf{s}} = \prod_{j \in m} \mathsf{A}_{s_j}$
(Definition `DManySortedCatAlg` of the draft). This file builds the product of any family of single-set
categories with the same dimensions, with sources, targets and compositions computed
componentwise. The draft takes the product for granted.
-/

universe u v

namespace CategorialAlgebras.Compact

open CategoryStruct

variable {Index : Type} {J : Type v} {C : J → Type u}

/-- Let $(C_j)_{j \in J}$ be a family of sets, each with a single-set categorial structure with
dimensions in $I$. The product $\prod_{j \in J} C_j$ has the single-set categorial structure
in which sources and targets are taken componentwise, and $g \#^{k} f$ is defined exactly when
$g_j \#^{k} f_j$ is defined for every $j \in J$, and then is the family of the
$g_j \#^{k} f_j$.
-/
instance CategoryStruct.pi [∀ j, CategoryStruct Index (C j)] :
    CategoryStruct Index ((j : J) → C j) where
  sc k f j := sc k (f j)
  tg k f j := tg k (f j)
  pcomp k g f := ⟨∀ j, sc k (g j) = tg k (f j), fun h j => g j ♯[k] f j ← h j⟩
  pcomp_dom := by
    intro k f g
    exact ⟨fun h => funext h, fun h j => congrFun h j⟩

section Pi

variable [∀ j, CategoryStruct Index (C j)]

@[simp] lemma pi_sc_apply (k : Index) (f : (j : J) → C j) (j : J) :
    sc k f j = sc k (f j) := rfl

@[simp] lemma pi_tg_apply (k : Index) (f : (j : J) → C j) (j : J) :
    tg k f j = tg k (f j) := rfl

lemma pi_sc_is_tg {k : Index} {g f : (j : J) → C j} :
    sc_is_tg k g f ↔ ∀ j, sc_is_tg k (g j) (f j) :=
  ⟨fun h j => congrFun h j, fun h => funext h⟩

@[simp] lemma pi_comp_apply {k : Index} {g f : (j : J) → C j} (h : sc_is_tg k g f) (j : J) :
    (g ♯[k] f ← h) j = g j ♯[k] f j ← (pi_sc_is_tg.mp h j) := rfl

end Pi

/-!
### Product of single-set categories

If every $C_j$ is a single-set category with dimensions in $I$, so is $\prod_{j \in J} C_j$
with the componentwise structure: every axiom holds because it holds in each component. In
particular, finite products of single-set $n$-categories are single-set $n$-categories, and the
empty product is the final single-set $n$-category, with a single cell.
-/

instance PreCategory.pi [∀ j, PreCategory Index (C j)] :
    PreCategory Index ((j : J) → C j) where
  sck_sck_eq_sck k f := by funext j; simp
  tgk_sck_eq_sck k f := by funext j; simp
  sck_tgk_eq_tgk k f := by funext j; simp
  tgk_tgk_eq_tgk k f := by funext j; simp
  sck_compk_eq_sck h := funext fun j => PreCategory.sck_compk_eq_sck (pi_sc_is_tg.mp h j)
  tgk_compk_eq_tgk h := funext fun j => PreCategory.tgk_compk_eq_tgk (pi_sc_is_tg.mp h j)
  compk_sck_eq_id k f := funext fun j => PreCategory.compk_sck_eq_id k (f j)
  compk_tgk_eq_id k f := funext fun j => PreCategory.compk_tgk_eq_id k (f j)
  assoc h₁ h₂ := funext fun j => PreCategory.assoc (pi_sc_is_tg.mp h₁ j) (pi_sc_is_tg.mp h₂ j)

instance Category.pi [Preorder Index] [∀ j, Category Index (C j)] :
    Category Index ((j : J) → C j) where
  sck_scj_eq_scj f h := by funext j; simp [h]
  scj_sck_eq_scj f h := by funext j; simp [h]
  scj_tgk_eq_scj f h := by funext j; simp [h]
  tgk_tgj_eq_tgj f h := by funext j; simp [h]
  tgj_tgk_eq_tgj f h := by funext j; simp [h]
  tgj_sck_eq_tgj f h := by funext j; simp [h]
  sck_compj_eq_compj_sck h₁ h₂ :=
    funext fun j => Category.sck_compj_eq_compj_sck h₁ (pi_sc_is_tg.mp h₂ j)
  tgk_compj_eq_compj_tgk h₁ h₂ :=
    funext fun j => Category.tgk_compj_eq_compj_tgk h₁ (pi_sc_is_tg.mp h₂ j)
  interchange h₁ h₂ h₃ h₄ h₅ :=
    funext fun j => Category.interchange h₁ (pi_sc_is_tg.mp h₂ j) (pi_sc_is_tg.mp h₃ j)
      (pi_sc_is_tg.mp h₄ j) (pi_sc_is_tg.mp h₅ j)

end CategorialAlgebras.Compact
