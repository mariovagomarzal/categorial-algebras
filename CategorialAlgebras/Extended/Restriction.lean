import Stemma
import CategorialAlgebras.Extended.Product

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "Restriction of globular categories" =>

A globular category has a set of cells for each dimension, and its structure only relates
dimensions $`j < k`. Keeping only some of the dimensions therefore gives again a globular
category. This is how truncation works in the globular presentation: the globular
$`m`-category underlying a globular $`n`-category, for $`m \leq n`, keeps the dimensions
$`0, \ldots, m`, and the globular $`n`-category underlying a globular $`\omega`-category keeps
the dimensions $`0, \ldots, n`.

The construction is done once, for any strictly monotone mapping $`e \colon J \to I` between
preordered sets of dimensions, which says which dimension of $`I` the dimension $`j \in J`
becomes.

```lean
universe u u₁ u₂

namespace CategorialAlgebras.Extended

variable {I J : Type} [Preorder I] [Preorder J] {e : J → I}
```

:::construction (label := "extended.restrict-category") (central := false) (title := "Restriction along a mapping of dimensions")
Let $`e \colon J \to I` be a strictly monotone mapping and $`\mathsf{C} = (C_i)_{i \in I}` a
globular category with dimensions in $`I`. The *restriction* $`e^{*}\mathsf{C}` of
$`\mathsf{C}` along $`e` is the globular category with dimensions in $`J` whose $`j`-cells are
the $`e(j)`-cells of $`\mathsf{C}`, and whose sources, targets, identities and compositions are
those of $`\mathsf{C}`: for $`j < k` in $`J`, $`\mathrm{sc}^{(j,k)}` of $`e^{*}\mathsf{C}` is
$`\mathrm{sc}^{(e(j),e(k))}` of $`\mathsf{C}`, and so on. Every axiom of $`e^{*}\mathsf{C}` for
dimensions $`i < j < k` is the axiom of $`\mathsf{C}` for $`e(i) < e(j) < e(k)`.

```lean
@[reducible]
def CategoryStruct.restrict (he : StrictMono e) (C : TypeFamily.{u} I) [CategoryStruct I C] :
    CategoryStruct J (fun k => C (e k)) where
  sc h f := sc (he h) f
  tg h f := tg (he h) f
  idm h u := idm (he h) u
  pcomp h g f := g ♯.[he h] f
  pcomp_dom := CategoryStruct.pcomp_dom

@[reducible]
def PreCategory.restrict (he : StrictMono e) (C : TypeFamily.{u} I) [PreCategory I C] :
    PreCategory J (fun k => C (e k)) where
  toCategoryStruct := CategoryStruct.restrict he C
  sckj_compkj_eq_sckj h := PreCategory.sckj_compkj_eq_sckj h
  tgkj_compkj_eq_tgkj h := PreCategory.tgkj_compkj_eq_tgkj h
  sckj_idmkj h u := PreCategory.sckj_idmkj (he h) u
  tgkj_idmkj h u := PreCategory.tgkj_idmkj (he h) u
  compkj_idmkj_sckj_eq_id h f := PreCategory.compkj_idmkj_sckj_eq_id (he h) f
  compkj_tgkj_idmkj_eq_id h f := PreCategory.compkj_tgkj_idmkj_eq_id (he h) f
  assoc h₁ h₂ := PreCategory.assoc h₁ h₂

@[reducible]
def Category.restrict (he : StrictMono e) (C : TypeFamily.{u} I) [Category I C] :
    Category J (fun k => C (e k)) where
  toPreCategory := PreCategory.restrict he C
  scji_sckj_eq_scki h₁ h₂ f := Category.scji_sckj_eq_scki (he h₁) (he h₂) f
  scji_tgkj_eq_scki h₁ h₂ f := Category.scji_tgkj_eq_scki (he h₁) (he h₂) f
  tgji_tgkj_eq_tgki h₁ h₂ f := Category.tgji_tgkj_eq_tgki (he h₁) (he h₂) f
  tgji_sckj_eq_tgki h₁ h₂ f := Category.tgji_sckj_eq_tgki (he h₁) (he h₂) f
  sckj_compki_eq_compji_sckj h := Category.sckj_compki_eq_compji_sckj h
  tgkj_compki_eq_compji_tgkj h := Category.tgkj_compki_eq_compji_tgkj h
  idmkj_idmji_eq_idmki h₁ h₂ u := Category.idmkj_idmji_eq_idmki (he h₁) (he h₂) u
  idmkj_compji_eq_compki_idmkj h := Category.idmkj_compji_eq_compki_idmkj h
  interchange := by
    intro _ _ _ _ i_lt_j _ _ _ _ h₁ h₂ h₃ h₄
    exact Category.interchange (i_lt_j := he i_lt_j) h₁ h₂ h₃ h₄
```
:::

:::construction (label := "extended.restrict-functor") (central := false) (title := "Restriction of globular functors")
A globular functor $`F = (F_i)_{i \in I}` from $`\mathsf{C}` to $`\mathsf{D}` restricts to the
globular functor $`e^{*}F = (F_{e(j)})_{j \in J}` from $`e^{*}\mathsf{C}` to $`e^{*}\mathsf{D}`.
Restriction preserves identities and composition of globular functors, both on the nose.

```lean
def Functor.restrict (he : StrictMono e)
    {C : TypeFamily.{u₁} I} [Category I C] {D : TypeFamily.{u₂} I} [Category I D]
    (F : Functor I C D) :
    @Functor J _ (fun k => C (e k)) (Category.restrict he C) (fun k => D (e k))
      (Category.restrict he D) :=
  letI := Category.restrict he C
  letI := Category.restrict he D
  { map := fun k f => F (e k) f
    map_sc_eq_sc_map := fun h f => F.map_sc_eq_sc_map (he h) f
    map_tg_eq_tg_map := fun h f => F.map_tg_eq_tg_map (he h) f
    map_idm_eq_idm_map := fun h f => F.map_idm_eq_idm_map (he h) f
    map_comp_eq_comp_map := fun {_ _ j_lt_k _ _} h => F.map_comp_eq_comp_map (j_lt_k := he j_lt_k) h }
```
:::

The product of a family of globular categories is computed dimensionwise, so restricting it
is the same as taking the product of the restrictions: the two structures on
$`\prod_{j} C^{j}_{e(k)}` coincide.

```lean
example {L : Type} (C : L → TypeFamily.{u} I) [∀ l, Category I (C l)] (he : StrictMono e) :
    Category.restrict he (fun k => (l : L) → C l k) =
      @Category.pi J _ L (fun l k => C l (e k)) (fun l => Category.restrict he (C l)) :=
  rfl

end CategorialAlgebras.Extended
```
