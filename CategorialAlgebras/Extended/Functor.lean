import Stemma
import Mathlib.CategoryTheory.Category.Basic
import CategorialAlgebras.Extended.Category

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "Extended functors" =>

An extended functor is a family of mappings, one for each dimension, that preserves sources,
targets, identities and compositions (the extended $`n`-functors after Definition 6.1 of the
draft). Ported from the group's repository `higher_category_theory`.

```lean
universe u u₁ u₂ u₃

namespace CategorialAlgebras.Extended
```

:::definition (label := "extended.functor") (central := false) (title := "Extended functor")
Let $`C` and $`D` be extended categories with dimensions in $`I`. An *extended functor* from
$`C` to $`D` is a family $`F = (F_k \colon C_k \to D_k)_{k \in I}` such that, for all
$`j < k`,
$`F_j \circ \mathrm{sc}^{(j,k)} = \mathrm{sc}^{(j,k)} \circ F_k`,
$`F_j \circ \mathrm{tg}^{(j,k)} = \mathrm{tg}^{(j,k)} \circ F_k`,
$`F_k \circ \mathrm{i}^{(k,j)} = \mathrm{i}^{(k,j)} \circ F_j`, and
$`F_k(g \circ^{(j)} f) = F_k g \circ^{(j)} F_k f` whenever $`g \circ^{(j)} f` is defined.

```lean
structure Functor (Index : Type) [Preorder Index] (C : TypeFamily.{u₁} Index) [Category Index C]
    (D : TypeFamily.{u₂} Index) [Category Index D] where
  /-- The underlying family of functions on morphisms. -/
  map : (k : Index) → C k → D k
  /-- The map preserves sources at dimensions `(k, j)`. -/
  map_sc_eq_sc_map : ∀ {k j : Index} (j_lt_k : j < k) (f : C k),
      map j (sc j_lt_k f) = sc j_lt_k (map k f) := by
    hcat_disch
  /-- The map preserves targets at dimensions `(k, j)`. -/
  map_tg_eq_tg_map : ∀ {k j : Index} (j_lt_k : j < k) (f : C k),
      map j (tg j_lt_k f) = tg j_lt_k (map k f) := by
    hcat_disch
  /-- The map preserves identities at dimensions `(k, j)`. -/
  map_idm_eq_idm_map : ∀ {k j : Index} (j_lt_k : j < k) (f : C j),
      map k (idm j_lt_k f) = idm j_lt_k (map j f) := by
    hcat_disch
  /-- If `g` and `f` are `(k, j)`-composable in `C`, then `F k g` and `F k f` are
  `(k, j)`-composable in `D`. This is an auxiliary method for `map_comp_eq_comp_map`. -/
  protected comp_map {k j : Index} {j_lt_k : j < k} {f g : C k}
      (sc_tg_gf : sc_is_tg j_lt_k g f) :
      sc_is_tg j_lt_k (map k g) (map k f) := calc
    sc j_lt_k (map k g)
    _ = map j (sc j_lt_k g) := (map_sc_eq_sc_map j_lt_k g).symm
    _ = map j (tg j_lt_k f) := by rw [sc_tg_gf]
    _ = tg j_lt_k (map k f) := map_tg_eq_tg_map j_lt_k f
  /-- The map preserves composition at dimensions `(k, j)`. -/
  map_comp_eq_comp_map : ∀ {k j : Index} {j_lt_k : j < k} {f g : C k}
      (sc_tg_gf : sc_is_tg j_lt_k g f),
      map k (g ♯[j_lt_k] f ← sc_tg_gf) =
      (map k g) ♯[j_lt_k] (map k f) ← (comp_map sc_tg_gf) := by
    hcat_disch
```
:::

```lean
attribute [simp] Functor.map_sc_eq_sc_map Functor.map_tg_eq_tg_map Functor.map_idm_eq_idm_map
  Functor.map_comp_eq_comp_map

namespace Functor

variable {Index : Type} [Preorder Index]
  {C : TypeFamily.{u₁} Index} [Category Index C]
  {D : TypeFamily.{u₂} Index} [Category Index D]
  {E : TypeFamily.{u₃} Index} [Category Index E]

instance : CoeFun (Functor Index C D) fun _ ↦ (k : Index) → C k → D k := ⟨fun F ↦ F.map⟩

attribute [coe] Functor.map

/-- Two extended functors with the same mappings are equal. -/
@[ext]
lemma ext {F G : Functor Index C D} (h : ∀ k f, F k f = G k f) : F = G := by
  cases F; cases G; congr; funext k f; exact h k f
```

:::definition (label := "extended.functor-comp") (central := false) (title := "Composition and identities")
Extended functors compose dimensionwise, and the identity mappings form an extended functor.

```lean
@[simp]
def comp (G : Functor Index D E) (F : Functor Index C D) :
    Functor Index C E where
  map k f := G k (F k f)
  map_sc_eq_sc_map := by
    intro k j j_lt_k f
    calc
      G j (F j (sc j_lt_k f))
      _ = G j (sc j_lt_k (F k f)) := by rw [F.map_sc_eq_sc_map j_lt_k f]
      _ = sc j_lt_k (G k (F k f)) := G.map_sc_eq_sc_map j_lt_k (F k f)
  map_tg_eq_tg_map := by
    intro k j j_lt_k f
    calc
      G j (F j (tg j_lt_k f))
      _ = G j (tg j_lt_k (F k f)) := by rw [F.map_tg_eq_tg_map j_lt_k f]
      _ = tg j_lt_k (G k (F k f)) := G.map_tg_eq_tg_map j_lt_k (F k f)
  map_idm_eq_idm_map := by
    intro k j j_lt_k f
    calc
      G k (F k (idm j_lt_k f))
      _ = G k (idm j_lt_k (F j f)) := by rw [F.map_idm_eq_idm_map j_lt_k f]
      _ = idm j_lt_k (G j (F j f)) := G.map_idm_eq_idm_map j_lt_k (F j f)
  map_comp_eq_comp_map := by
    intro k j j_lt_k f g sc_tg_gf
    calc
      G k (F k (g ♯[j_lt_k] f ← sc_tg_gf))
      _ = G k ((F k g) ♯[j_lt_k] (F k f) ← F.comp_map sc_tg_gf) := by
        rw [F.map_comp_eq_comp_map sc_tg_gf]
      _ = (G k (F k g)) ♯[j_lt_k] (G k (F k f)) ←
        G.comp_map (F.comp_map sc_tg_gf) :=
        G.map_comp_eq_comp_map (F.comp_map sc_tg_gf)

@[simp]
def id (C : TypeFamily.{u₁} Index) [Category Index C] : Functor Index C C where
  map _ f := f
```
:::

```lean
@[inherit_doc] scoped[CategorialAlgebras.Extended] infixr:100 " ⊚ " => Functor.comp

@[inherit_doc] scoped[CategorialAlgebras.Extended] notation "idₘ" => Functor.id

end Functor
```

:::definition (label := "extended.n-functor") (central := false) (title := "Extended n-functors")
An *extended* $`n`-*functor* is an extended functor between extended $`n`-categories, and an
*extended* $`\omega`-*functor* one between extended $`\omega`-categories.

```lean
abbrev NFunctor (n : ℕ)
    (C : NTypeFamily.{u₁} n) [NCategory n C]
    (D : NTypeFamily.{u₂} n) [NCategory n D] :=
  Functor (FinSucc n) C D

/-- A functor between many-sorted $\omega$-categories. -/
abbrev OmegaFunctor
    (C : OmegaTypeFamily.{u₁}) [OmegaCategory C]
    (D : OmegaTypeFamily.{u₂}) [OmegaCategory D] :=
  Functor ℕ C D
```
:::

# The categories of extended categories

```lean
structure Cat (Index : Type) [Preorder Index] where
  /-- Build a `Cat` from a carrier family with a `Category` instance. -/
  of ::
  /-- The underlying family of sets of cells. -/
  carrier : TypeFamily.{u} Index
  /-- The extended categorial structure on the family. -/
  [str : Category Index carrier]

attribute [instance] Cat.str

instance {Index : Type} [Preorder Index] : CoeFun (Cat Index) fun _ ↦ Index → Type u :=
  ⟨Cat.carrier⟩

attribute [coe] Cat.carrier
```

:::definition (label := "extended.cat") (central := false) (title := "The category of extended categories")
Extended categories with dimensions in $`I` and extended functors form a category. For
$`I = n + 1` this is the category $`\mathsf{nCat}^{\mathrm{ext}}` of extended $`n`-categories
and extended $`n`-functors.

```lean
instance Cat.category {Index : Type} [Preorder Index] :
    CategoryTheory.LargeCategory.{u} (Cat Index) where
  Hom C D := Functor Index C D
  comp F G := G ⊚ F
  id C := idₘ C

abbrev NCat (n : ℕ) := Cat.{u} (FinSucc n)
```
:::

```lean
end CategorialAlgebras.Extended
```
