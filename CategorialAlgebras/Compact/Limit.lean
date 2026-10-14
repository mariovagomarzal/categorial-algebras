import Stemma
import Mathlib.CategoryTheory.Equivalence
import CategorialAlgebras.Compact.Truncation

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "ωCatAlg(Σ) as a pseudo-limit" =>

Proposition `PUnivPropCatAlg` of the draft states that $`\omega\mathsf{CatAlg}(\Sigma)`, with the
truncation functors $`T^{(n,\omega)}_{\Sigma}`, is the projective limit of the categories
$`\mathsf{nCatAlg}(\Sigma)` and the truncation functors $`T^{(m,n)}_{\Sigma}`. In the compact
presentation these functors compose only up to the canonical isomorphisms of Proposition
`compact.truncation-proj-system`: a cell of a truncation is a cell together with the proof that it
has the right dimension, and truncating twice nests these proofs. The equations
$`T^{(m,n)}_{\Sigma} \circ T^{(n,\omega)}_{\Sigma} = T^{(m,\omega)}_{\Sigma}` fail already for the
projections themselves, so the strict universal property cannot be stated faithfully.

This document states it as a *pseudo-limit*: compatible families are compatible up to specified
isomorphisms, and the universal property says that $`\omega\mathsf{CatAlg}(\Sigma)` is equivalent
to the category of these families, through its truncations. This is the form in which the draft
uses the universal property (Corollary `CLimitNat`), and it agrees with the strict one wherever the
latter makes sense. For a tower indexed by $`\mathbb{N}`, it is enough to give the isomorphisms
between consecutive levels: those between any two levels are their composites, and no coherence
condition is needed.

```lean
universe u v w

namespace CategorialAlgebras.Compact

open CategoryTheory

variable {S : Type u} (Sig : Signature.{u, v} S)
```

# Compatible families

:::definition (label := "compact.compatible-family") (central := false) (title := "Compatible families")
A *compatible family* of compact categorial $`\Sigma`-algebras is a family
$`(\boldsymbol{\mathsf{A}}_n)_{n \in \mathbb{N}}`, with $`\boldsymbol{\mathsf{A}}_n` a compact
$`n`-categorial $`\Sigma`-algebra, together with isomorphisms
$`\varphi_n \colon T^{(n,n+1)}_{\Sigma}(\boldsymbol{\mathsf{A}}_{n+1}) \cong \boldsymbol{\mathsf{A}}_n`.
A *morphism* of compatible families from $`(\boldsymbol{\mathsf{A}}_n, \varphi_n)` to
$`(\boldsymbol{\mathsf{B}}_n, \psi_n)` is a family of homomorphisms
$`H_n \colon \boldsymbol{\mathsf{A}}_n \to \boldsymbol{\mathsf{B}}_n` such that
$`\psi_n \circ T^{(n,n+1)}_{\Sigma}(H_{n+1}) = H_n \circ \varphi_n` for every $`n`. With the
levelwise composition and identities, compatible families form a category, the pseudo-limit of the
categories $`\mathsf{nCatAlg}(\Sigma)` along the truncation functors.

In the draft, a compatible family is one with
$`T^{(m,n)}_{\Sigma}(\boldsymbol{\mathsf{A}}_n) = \boldsymbol{\mathsf{A}}_m`, and a morphism one with
$`T^{(m,n)}_{\Sigma}(H_n) = H_m`; here the equalities are replaced by the isomorphisms $`\varphi_n`.

```lean
structure CompatibleFamily where
  /-- The compact `n`-categorial algebra at level `n`. -/
  alg : ∀ n, CatAlgebra.{u, v, w} Sig n
  /-- The truncation of level `n + 1` is level `n`, up to isomorphism. -/
  iso : ∀ n, (truncation Sig (Nat.le_succ n)).obj (alg (n + 1)) ≅ alg n

namespace CompatibleFamily

variable {Sig}

@[ext]
structure Hom (A B : CompatibleFamily.{u, v, w} Sig) where
  /-- The homomorphism at level `n`. -/
  map : ∀ n, A.alg n ⟶ B.alg n
  /-- The homomorphisms commute with the isomorphisms of the families. -/
  comm : ∀ n, (truncation Sig (Nat.le_succ n)).map (map (n + 1)) ≫ (B.iso n).hom =
    (A.iso n).hom ≫ map n

instance category : CategoryTheory.Category.{max u w} (CompatibleFamily.{u, v, w} Sig) where
  Hom A B := Hom A B
  id A := ⟨fun n => 𝟙 (A.alg n), fun n => by simp⟩
  comp H K := ⟨fun n => H.map n ≫ K.map n, fun n => by
    rw [Functor.map_comp, CategoryTheory.Category.assoc, K.comm,
      ← CategoryTheory.Category.assoc, H.comm, CategoryTheory.Category.assoc]⟩
  id_comp _ := Hom.ext (funext fun _ => CategoryTheory.Category.id_comp _)
  comp_id _ := Hom.ext (funext fun _ => CategoryTheory.Category.comp_id _)
  assoc _ _ _ := Hom.ext (funext fun _ => CategoryTheory.Category.assoc _ _ _)

end CompatibleFamily
```
:::

# The family of truncations

:::definition (label := "compact.trunc-family") (central := false) (title := "The family of truncations")
The truncations $`(T^{(n,\omega)}_{\Sigma}(\boldsymbol{\mathsf{B}}))_{n \in \mathbb{N}}` of a compact
$`\omega`-categorial $`\Sigma`-algebra $`\boldsymbol{\mathsf{B}}`, with the canonical isomorphisms
$`T^{(n,n+1)}_{\Sigma}(T^{(n+1,\omega)}_{\Sigma}(\boldsymbol{\mathsf{B}})) \cong
T^{(n,\omega)}_{\Sigma}(\boldsymbol{\mathsf{B}})` of Proposition `compact.truncation-proj-system`, are a
compatible family, and the truncations of a homomorphism are a morphism of compatible families, by
the naturality of these isomorphisms. This is a functor from $`\omega\mathsf{CatAlg}(\Sigma)` to the
category of compatible families.

```lean
def truncFamilies : OmegaCatAlgebra.{u, v, w} Sig ⥤ CompatibleFamily.{u, v, w} Sig where
  obj B :=
    { alg := fun n => (truncationω Sig n).obj B
      iso := fun n => (truncationω_comp_iso Sig (Nat.le_succ n)).app B }
  map H :=
    { map := fun n => (truncationω Sig n).map H
      comm := fun n => (truncationω_comp_iso Sig (Nat.le_succ n)).hom.naturality H }
  map_id _ := rfl
  map_comp _ _ := rfl
```
:::

# Homomorphisms

Every cell of a compact $`\omega`-categorial algebra is a $`k`-cell for some $`k`, and then it lies
in all the truncations from level $`k` on. A morphism $`(H_n)_n` between the families of
truncations of $`\boldsymbol{\mathsf{A}}` and $`\boldsymbol{\mathsf{B}}` thus gives a value at every
cell $`x`, by computing $`H_n(x)` at any level $`n` at which $`x` lies; the compatibility of the
$`H_n` with the isomorphisms of the families says that $`H_{n+1}(x) = H_n(x)`, so the value does not
depend on the level.

```lean
variable {Sig}

section Cells

variable {C : Type w} [OmegaCategory C]

/-- A cell of a compact ω-category lives in the truncations from some level on. -/
lemma exists_level (x : C) : ∃ n, ∀ u ∈ upperω n, CategoryStruct.sc u x = x := by
  obtain ⟨k, hk⟩ := OmegaCategory.is_cell x
  exact ⟨k, fun u hu => cell_of_le hk hu⟩

lemma level_mono {x : C} {n n' : ℕ} (h : n ≤ n')
    (hx : ∀ u ∈ upperω n, CategoryStruct.sc u x = x) :
    ∀ u ∈ upperω n', CategoryStruct.sc u x = x :=
  fun u hu => hx u (le_trans h hu)

end Cells

namespace OmegaCatAlgebra

variable {A B : OmegaCatAlgebra.{u, v, w} Sig}
  (Φ : (truncFamilies Sig).obj A ⟶ (truncFamilies Sig).obj B)

/-- The value of a morphism of families of truncations at a cell, computed at level `n`. -/
def valAt {s : S} (x : A s) (n : ℕ) (hx : ∀ u ∈ upperω n, CategoryStruct.sc u x = x) : B s :=
  (((Φ.map n).map s).map ⟨x, hx⟩).1

lemma valAt_succ {s : S} (x : A s) (n : ℕ) (hx : ∀ u ∈ upperω n, CategoryStruct.sc u x = x) :
    valAt Φ x (n + 1) (level_mono (Nat.le_succ n) hx) = valAt Φ x n hx := by
  have := congrArg
    (fun H : (truncation Sig (Nat.le_succ n)).obj (A.truncate (n + 1)) ⟶ B.truncate n =>
    ((H.map s).map ⟨⟨x, level_mono (Nat.le_succ n) hx⟩, fun u hu => Subtype.ext (hx u hu)⟩).1)
    (Φ.comm n)
  exact this

lemma valAt_eq {s : S} (x : A s) {n n' : ℕ} (hx : ∀ u ∈ upperω n, CategoryStruct.sc u x = x)
    (hx' : ∀ u ∈ upperω n', CategoryStruct.sc u x = x) : valAt Φ x n hx = valAt Φ x n' hx' := by
  suffices key : ∀ n n' (hx : ∀ u ∈ upperω n, CategoryStruct.sc u x = x)
      (hx' : ∀ u ∈ upperω n', CategoryStruct.sc u x = x), n ≤ n' →
      valAt Φ x n hx = valAt Φ x n' hx' by
    rcases le_total n n' with h | h
    · exact key n n' hx hx' h
    · exact (key n' n hx' hx h).symm
  intro n n' hx hx' h
  induction n', h using Nat.le_induction with
  | base => rfl
  | succ m hm ih => exact (ih (level_mono hm hx)).trans (valAt_succ Φ x m _).symm

/-- A level at which a cell lives. -/
noncomputable def lvl {s : S} (x : A s) : ℕ := Classical.choose (exists_level x)

lemma lvl_spec {s : S} (x : A s) : ∀ u ∈ upperω (lvl x), CategoryStruct.sc u x = x :=
  Classical.choose_spec (exists_level x)
```

:::construction (label := "compact.hom-of-family") (central := false) (title := "The homomorphism of a morphism of families")
Let $`\boldsymbol{\mathsf{A}}` and $`\boldsymbol{\mathsf{B}}` be compact $`\omega`-categorial
$`\Sigma`-algebras and $`(H_n)_n` a morphism between their families of truncations. The mapping
that sends a cell $`x` of $`\boldsymbol{\mathsf{A}}` to $`H_n(x)`, for any level $`n` at which $`x`
lies, is a homomorphism $`H \colon \boldsymbol{\mathsf{A}} \to \boldsymbol{\mathsf{B}}`: to compare
$`H` with a $`k`-source, a $`k`-target, a $`k`-composite or an operation of $`\Sigma`, compute every
value involved at a level above $`k` at which all the cells involved lie, where $`H_n` preserves
them. Its truncations are the $`H_n`.

```lean
/-- The homomorphism of `ω`-categorial algebras of a morphism of families of truncations. -/
noncomputable def homOfFamily : Hom A B where
  map s :=
    { map := fun x => valAt Φ x (lvl x) (lvl_spec x)
      map_sc_eq_sc_map := fun k x => by
        have hx := level_mono (le_max_left (lvl x) (k + 1)) (lvl_spec x)
        let y : (A.truncate (max (lvl x) (k + 1))).carrier s := ⟨x, hx⟩
        let kk : Fin (max (lvl x) (k + 1)) := ⟨k, by omega⟩
        refine (valAt_eq Φ (CategoryStruct.sc k x) (lvl_spec _)
          (CategoryStruct.sc kk y).2).trans ?_
        rw [valAt_eq Φ x (lvl_spec x) hx]
        exact congrArg Subtype.val (((Φ.map _).map s).map_sc_eq_sc_map kk y)
      map_tg_eq_tg_map := fun k x => by
        have hx := level_mono (le_max_left (lvl x) (k + 1)) (lvl_spec x)
        let y : (A.truncate (max (lvl x) (k + 1))).carrier s := ⟨x, hx⟩
        let kk : Fin (max (lvl x) (k + 1)) := ⟨k, by omega⟩
        refine (valAt_eq Φ (CategoryStruct.tg k x) (lvl_spec _)
          (CategoryStruct.tg kk y).2).trans ?_
        rw [valAt_eq Φ x (lvl_spec x) hx]
        exact congrArg Subtype.val (((Φ.map _).map s).map_tg_eq_tg_map kk y)
      map_comp_eq_comp_map := fun {k f g} h => by
        let N := max (max (lvl f) (lvl g)) (k + 1)
        have hf := level_mono (show lvl f ≤ N by omega) (lvl_spec f)
        have hg := level_mono (show lvl g ≤ N by omega) (lvl_spec g)
        let kk : Fin N := ⟨k, by omega⟩
        let g' : (A.truncate N).carrier s := ⟨g, hg⟩
        let f' : (A.truncate N).carrier s := ⟨f, hf⟩
        have p : sc_is_tg kk g' f' := Subtype.ext h
        refine (valAt_eq Φ _ (lvl_spec _) (CategoryStruct.comp kk g' f' p).2).trans ?_
        exact (congrArg Subtype.val (((Φ.map N).map s).map_comp_eq_comp_map p)).trans
          (congr_comp₂ (valAt_eq Φ f hf (lvl_spec f)) (valAt_eq Φ g hg (lvl_spec g)) _) }
  map_op {ws s} σ a := by
    classical
    let N := Finset.univ.sup fun j => lvl (a j)
    have ha : ∀ j, ∀ u ∈ upperω N, CategoryStruct.sc u (a j) = a j := fun j =>
      level_mono (Finset.le_sup (f := fun j => lvl (a j)) (Finset.mem_univ j)) (lvl_spec (a j))
    let b : Signature.Arity (A.truncate N) ws := fun j => ⟨a j, ha j⟩
    change valAt Φ _ _ _ = B.op σ fun j => valAt Φ _ _ _
    refine (valAt_eq Φ (A.op σ a) (lvl_spec _) ((A.truncate N).op σ b).2).trans ?_
    have := congrArg Subtype.val ((Φ.map N).map_op σ b)
    refine this.trans ?_
    exact congrArg (B.op σ) (funext fun j => valAt_eq Φ (a j) (ha j) _)

lemma truncation_homOfFamily (n : ℕ) : (truncationω Sig n).map (homOfFamily Φ) = Φ.map n := by
  apply CatAlgebra.Hom.ext
  intro s
  apply Functor.ext
  intro x
  exact Subtype.ext (valAt_eq Φ x.1 (lvl_spec x.1) x.2)

end OmegaCatAlgebra
```
:::

:::proposition (label := "compact.trunc-families-fully-faithful") (central := false) (title := "The functor of truncations is fully faithful")
A homomorphism of compact $`\omega`-categorial $`\Sigma`-algebras is determined by its truncations,
and every morphism between the families of truncations is the family of truncations of a
homomorphism: the functor of truncations is faithful and full. This is the first part of
Corollary `CLimitNat` of the draft.

```lean
open OmegaCatAlgebra in
instance truncFamilies_faithful : (truncFamilies.{u, v, w} Sig).Faithful where
  map_injective {A B} {H K} h := by
    apply OmegaCatAlgebra.Hom.ext
    intro s
    apply Functor.ext
    intro x
    have := congrArg (fun Φ : (truncFamilies Sig).obj A ⟶ (truncFamilies Sig).obj B =>
      (((Φ.map (lvl x)).map s).map ⟨x, lvl_spec x⟩).1) h
    exact this

open OmegaCatAlgebra in
instance truncFamilies_full : (truncFamilies.{u, v, w} Sig).Full where
  map_surjective {A B} Φ :=
    ⟨homOfFamily Φ, CompatibleFamily.Hom.ext (funext fun n => truncation_homOfFamily Φ n)⟩
```
:::

:::proof (of := "compact.trunc-families-fully-faithful")
If two homomorphisms have the same truncations, they agree at every cell, since every cell lies in
some truncation. A morphism of families is the family of truncations of the homomorphism of
Construction `compact.hom-of-family`.
:::

# The universal property

:::theorem (label := "compact.omega-cat-alg-pseudo-limit") (central := true) (title := "ωCatAlg(Σ) is the pseudo-limit of the nCatAlg(Σ)")
For every many-sorted signature $`\Sigma`, the functor of truncations from
$`\omega\mathsf{CatAlg}(\Sigma)` to the category of compatible families is an equivalence of
categories. That is:

1. it is faithful and full: the homomorphisms $`\boldsymbol{\mathsf{A}} \to \boldsymbol{\mathsf{B}}`
   of compact $`\omega`-categorial $`\Sigma`-algebras correspond bijectively, through their
   truncations, to the morphisms between the families of truncations (Corollary `CLimitNat` of the
   draft, first part);
2. it is essentially surjective: every compatible family is isomorphic to the family of
   truncations of a compact $`\omega`-categorial $`\Sigma`-algebra, its limit.

This is Proposition `PUnivPropCatAlg` of the draft, up to isomorphism: a family of functors
$`F_n \colon \mathsf{L} \to \mathsf{nCatAlg}(\Sigma)` with natural isomorphisms
$`T^{(n,n+1)}_{\Sigma} \circ F_{n+1} \cong F_n` is a functor from $`\mathsf{L}` to the category of
compatible families, and thus factors through $`\omega\mathsf{CatAlg}(\Sigma)`, uniquely up to a
unique natural isomorphism.

```lean
theorem truncFamilies_isEquivalence : (truncFamilies.{u, v, w} Sig).IsEquivalence := by
  sorry
```
:::

```lean
end CategorialAlgebras.Compact
```
