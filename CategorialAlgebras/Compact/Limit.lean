import Stemma
import Mathlib.CategoryTheory.Equivalence
import CategorialAlgebras.Compact.Truncation
import CategorialAlgebras.Compact.Tower

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "Compact ω-categorial algebras as a pseudo-limit" =>

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
categories $`\mathsf{nCatAlg}(\Sigma)` along the truncation functors. The index $`n` is the
*level* of $`\boldsymbol{\mathsf{A}}_n` in the family.

In the draft, a compatible family is one with
$`T^{(m,n)}_{\Sigma}(\boldsymbol{\mathsf{A}}_n) = \boldsymbol{\mathsf{A}}_m`, and a morphism one with
$`T^{(m,n)}_{\Sigma}(H_n) = H_m`; here the equalities are replaced by the isomorphisms $`\varphi_n`.
In the extended (globular) presentation the truncations compose strictly, and the compatible
families of the document on extended $`\omega`-categorial algebras as a projective limit keep the
equalities of the draft.

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
in all the truncations from level $`k` on: in the compact (single-set) presentation, a cell lies at
level $`n`, that is, in $`T^{(n,\omega)}_{\Sigma}`, exactly when it is an $`n`-cell. A morphism $`(H_n)_n` between the families of
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

# The limit of a compatible family

Let $`(\boldsymbol{\mathsf{A}}_n, \varphi_n)_n` be a compatible family. For every sort $`s`, the
inverse of $`\varphi_n` sends the cells of $`\boldsymbol{\mathsf{A}}_n` to cells of
$`\boldsymbol{\mathsf{A}}_{n+1}`, bijectively onto its $`n`-cells and preserving the structure of
the dimensions below $`n`. The cells of sort $`s` thus form a chain
$`A_{0,s} \hookrightarrow A_{1,s} \hookrightarrow \cdots`, a *tower* of compact categories, whose
limit is a compact $`\omega`-category (the Lean module `CategorialAlgebras.Compact.Tower`): its cells
are those of all the levels, each identified with its images, and the sources, targets and
compositions of dimension $`k` are computed at any level above $`k` that contains the cells
involved. This is the union of the draft, where the $`\boldsymbol{\mathsf{A}}_m` are subsets of the
$`\boldsymbol{\mathsf{A}}_n`.

```lean
open CategoryStruct

namespace CompatibleFamily

variable (F : CompatibleFamily.{u, v, w} Sig)

/-- The embedding of level `n` into level `n + 1`, at sort `s`. -/
def emb (s : S) (n : ℕ) (a : F.alg n s) : F.alg (n + 1) s :=
  (((F.iso n).inv.map s).map a).1

lemma hom_emb (s : S) (n : ℕ) (a : F.alg n s) :
    ((F.iso n).hom.map s).map (((F.iso n).inv.map s).map a) = a :=
  congrArg (fun H : F.alg n ⟶ F.alg n => (H.map s).map a) (F.iso n).inv_hom_id

lemma inv_hom (s : S) (n : ℕ) (x : (truncation Sig (Nat.le_succ n)).obj (F.alg (n + 1)) s) :
    ((F.iso n).inv.map s).map (((F.iso n).hom.map s).map x) = x :=
  congrArg (fun H : (truncation Sig (Nat.le_succ n)).obj (F.alg (n + 1)) ⟶ _ => (H.map s).map x)
    (F.iso n).hom_inv_id
```

:::construction (label := "compact.family-tower") (central := false) (title := "The tower of a compatible family")
For every sort $`s`, the cells of sort $`s` of the levels of a compatible family, with the
embeddings $`A_{n,s} \to A_{n+1,s}` given by the inverses of the isomorphisms $`\varphi_n`, are a
tower of compact categories: each embedding is injective, preserves the $`k`-sources, $`k`-targets
and $`k`-compositions for $`k < n`, and its image is the set of $`n`-cells, since the cells of
$`T^{(n,n+1)}_{\Sigma}(\boldsymbol{\mathsf{A}}_{n+1})` are the $`n`-cells of
$`\boldsymbol{\mathsf{A}}_{n+1}`.

```lean
/-- The tower of the cells of sort `s` of a compatible family. -/
@[reducible]
def tower (s : S) : Tower.{w} where
  X n := F.alg n s
  str n := (F.alg n).str s
  e := F.emb s
  e_injective n a b h := by
    rw [← F.hom_emb s n a, ← F.hom_emb s n b]
    exact congrArg _ (Subtype.ext h)
  e_sc n k a := congrArg Subtype.val (((F.iso n).inv.map s).map_sc_eq_sc_map k a)
  e_tg n k a := congrArg Subtype.val (((F.iso n).inv.map s).map_tg_eq_tg_map k a)
  e_comp n k g f h := congrArg Subtype.val (((F.iso n).inv.map s).map_comp_eq_comp_map h)
  e_cell n a := (((F.iso n).inv.map s).map a).2 (Fin.last n) (by simp [upper])
  e_surj n x hx := by
    have hx' : ∀ u ∈ upper n (n + 1), sc u x = x := fun u hu => by
      have : u = Fin.last n := Fin.ext (by
        have := u.isLt
        simp only [upper, Set.mem_ofPred_eq] at hu
        rw [Fin.val_last]; omega)
      rw [this]; exact hx
    exact ⟨((F.iso n).hom.map s).map ⟨x, hx'⟩, congrArg Subtype.val (F.inv_hom s n ⟨x, hx'⟩)⟩
```
:::

The operations of $`\Sigma` commute with the embeddings, since the $`\varphi_n^{-1}` are
homomorphisms. An operation is therefore computed on finitely many cells of the limit at any level
that contains them all.

```lean
open Signature

lemma emb_op {ws : List S} {s : S} (σ : Sig ws s) (n : ℕ) (b : Arity (F.alg n) ws) :
    F.emb s n ((F.alg n).op σ b) = (F.alg (n + 1)).op σ (fun j => F.emb (ws.get j) n (b j)) :=
  congrArg Subtype.val ((F.iso n).inv.map_op σ b)

lemma up_op {ws : List S} {s : S} (σ : Sig ws s) {n m : ℕ} (h : n ≤ m) (b : Arity (F.alg n) ws) :
    (F.tower s).up h ((F.alg n).op σ b) =
      (F.alg m).op σ (fun j => (F.tower (ws.get j)).up h (b j)) := by
  induction m, h using Nat.le_induction with
  | base => simp only [Tower.up_self]
  | succ m hm ih =>
    rw [Tower.up_succ _ hm, ih]
    change F.emb s m _ = _
    rw [F.emb_op]
    congr 1
    funext j
    exact ((F.tower (ws.get j)).up_succ hm (b j)).symm

/-- The cells of sort `s` of the limit. -/
abbrev L (s : S) := (F.tower s).Lim

/-- A family of cells of the limit comes from a common level above any bound. -/
lemma exists_cls_arity {ws : List S} (z : Arity F.L ws) (bd : ℕ) :
    ∃ N, bd < N ∧ ∃ b : Arity (F.alg N) ws, ∀ j, (F.tower (ws.get j)).cls N (b j) = z j := by
  classical
  let N := max (Finset.univ.sup fun j => (F.tower (ws.get j)).lvl (z j)) bd + 1
  refine ⟨N, by omega, fun j => (F.tower (ws.get j)).rep (z j) N ?_,
    fun j => (F.tower (ws.get j)).cls_rep _ _ _⟩
  exact le_trans (Finset.le_sup (f := fun j => (F.tower (ws.get j)).lvl (z j))
    (Finset.mem_univ j)) (by omega)

/-- The level used to compute an operation on a family of cells of the limit. -/
noncomputable def opLevel {ws : List S} (z : Arity F.L ws) : ℕ :=
  Classical.choose (F.exists_cls_arity z 0)

/-- The operation of `σ` on the limit, computed at a level that contains the arguments. -/
noncomputable def opL {ws : List S} {s : S} (σ : Sig ws s) (z : Arity F.L ws) : F.L s :=
  (F.tower s).cls (F.opLevel z)
    ((F.alg _).op σ (Classical.choose (Classical.choose_spec (F.exists_cls_arity z 0)).2))

lemma op_cls_eq {ws : List S} {s : S} (σ : Sig ws s) {N n : ℕ} {c : Arity (F.alg N) ws}
    {b : Arity (F.alg n) ws}
    (hc : ∀ j, (F.tower (ws.get j)).cls N (c j) = (F.tower (ws.get j)).cls n (b j)) :
    (F.tower s).cls N ((F.alg N).op σ c) = (F.tower s).cls n ((F.alg n).op σ b) := by
  have hc' : ∀ j, (F.tower (ws.get j)).up (le_max_left N n) (c j) =
      (F.tower (ws.get j)).up (le_max_right N n) (b j) := fun j =>
    ((F.tower (ws.get j)).cls_eq_iff (le_max_left N n) (le_max_right N n)).mp (hc j)
  rw [(F.tower s).cls_eq_iff (le_max_left N n) (le_max_right N n), F.up_op, F.up_op]
  exact congrArg _ (funext hc')

lemma opL_cls {ws : List S} {s : S} (σ : Sig ws s) {n : ℕ} (b : Arity (F.alg n) ws) :
    F.opL σ (fun j => (F.tower (ws.get j)).cls n (b j)) = (F.tower s).cls n ((F.alg n).op σ b) :=
  F.op_cls_eq σ (Classical.choose_spec (Classical.choose_spec (F.exists_cls_arity _ 0)).2)

lemma exists_cls_arity_ge {ws : List S} (z : Arity F.L ws) :
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ b : Arity (F.alg N) ws, ∀ j, (F.tower (ws.get j)).cls N (b j) = z j := by
  classical
  refine ⟨Finset.univ.sup fun j => (F.tower (ws.get j)).lvl (z j), fun N hN =>
    ⟨fun j => (F.tower (ws.get j)).rep (z j) N ?_, fun j => (F.tower (ws.get j)).cls_rep _ _ _⟩⟩
  exact le_trans (Finset.le_sup (f := fun j => (F.tower (ws.get j)).lvl (z j))
    (Finset.mem_univ j)) hN
```

:::construction (label := "compact.limit-algebra") (central := false) (title := "The limit of a compatible family")
The *limit* of a compatible family is the compact $`\omega`-categorial $`\Sigma`-algebra whose cells
of sort $`s` are those of the limit of the tower of sort $`s`, and in which every
$`\sigma \in \Sigma_{\mathbf{s}, s}` acts on a family of cells by acting at a common level. This
is a compact $`\omega`-functor because, at every level $`n`, $`\sigma` is a compact $`n`-functor. This is the
limit $`\varprojlim_n \boldsymbol{\mathsf{A}}_n` of the proof of Proposition `PUnivPropCatAlg` of
the draft.

```lean
/-- The compact `ω`-functor of an operation symbol on the limit. -/
noncomputable def opFunctor {ws : List S} {s : S} (σ : Sig ws s) :
    OmegaFunctor (Arity F.L ws) (F.L s) where
  map := F.opL σ
  map_sc_eq_sc_map k a := by
    obtain ⟨N, hN, b, hb⟩ := F.exists_cls_arity a k
    obtain rfl : (fun j => (F.tower (ws.get j)).cls N (b j)) = a := funext hb
    calc F.opL σ (sc k fun j => (F.tower (ws.get j)).cls N (b j))
      _ = F.opL σ (fun j => (F.tower (ws.get j)).cls N (sc (⟨k, hN⟩ : Fin N) (b j))) :=
          congrArg _ (funext fun j => Tower.sc_cls _ hN _)
      _ = (F.tower s).cls N ((F.alg N).op σ (sc (⟨k, hN⟩ : Fin N) b)) := F.opL_cls σ _
      _ = (F.tower s).cls N (sc (⟨k, hN⟩ : Fin N) ((F.alg N).op σ b)) :=
          congrArg _ (((F.alg N).op σ).map_sc_eq_sc_map _ b)
      _ = sc k (F.opL σ fun j => (F.tower (ws.get j)).cls N (b j)) := by
          rw [F.opL_cls, Tower.sc_cls _ hN]
  map_tg_eq_tg_map k a := by
    obtain ⟨N, hN, b, hb⟩ := F.exists_cls_arity a k
    obtain rfl : (fun j => (F.tower (ws.get j)).cls N (b j)) = a := funext hb
    calc F.opL σ (tg k fun j => (F.tower (ws.get j)).cls N (b j))
      _ = F.opL σ (fun j => (F.tower (ws.get j)).cls N (tg (⟨k, hN⟩ : Fin N) (b j))) :=
          congrArg _ (funext fun j => Tower.tg_cls _ hN _)
      _ = (F.tower s).cls N ((F.alg N).op σ (tg (⟨k, hN⟩ : Fin N) b)) := F.opL_cls σ _
      _ = (F.tower s).cls N (tg (⟨k, hN⟩ : Fin N) ((F.alg N).op σ b)) :=
          congrArg _ (((F.alg N).op σ).map_tg_eq_tg_map _ b)
      _ = tg k (F.opL σ fun j => (F.tower (ws.get j)).cls N (b j)) := by
          rw [F.opL_cls, Tower.tg_cls _ hN]
  map_comp_eq_comp_map {k f g} h := by
    obtain ⟨N₁, h₁⟩ := F.exists_cls_arity_ge g
    obtain ⟨N₂, h₂⟩ := F.exists_cls_arity_ge f
    let N := max (max N₁ N₂) (k + 1)
    have hN : k < N := by omega
    obtain ⟨gb, hg⟩ := h₁ N (by omega)
    obtain ⟨fb, hf⟩ := h₂ N (by omega)
    obtain rfl : (fun j => (F.tower (ws.get j)).cls N (gb j)) = g := funext hg
    obtain rfl : (fun j => (F.tower (ws.get j)).cls N (fb j)) = f := funext hf
    have hb : sc_is_tg (⟨k, hN⟩ : Fin N) gb fb :=
      pi_sc_is_tg.mpr fun j => (Tower.sc_is_tg_cls _ hN).mp (pi_sc_is_tg.mp h j)
    calc F.opL σ (_ ♯[k] _ ← h)
      _ = F.opL σ (fun j => (F.tower (ws.get j)).cls N
            (gb j ♯[(⟨k, hN⟩ : Fin N)] fb j ← pi_sc_is_tg.mp hb j)) :=
          congrArg _ (funext fun j => Tower.comp_eq _ hN rfl rfl (pi_sc_is_tg.mp h j))
      _ = (F.tower s).cls N ((F.alg N).op σ (gb ♯[(⟨k, hN⟩ : Fin N)] fb ← hb)) := F.opL_cls σ _
      _ = (F.tower s).cls N ((F.alg N).op σ gb ♯[(⟨k, hN⟩ : Fin N)] (F.alg N).op σ fb ←
            ((F.alg N).op σ).comp_map hb) :=
          congrArg _ (((F.alg N).op σ).map_comp_eq_comp_map hb)
      _ = _ := (Tower.comp_eq _ hN (F.opL_cls σ gb) (F.opL_cls σ fb) _).symm

/-- The limit of a compatible family: a compact `ω`-categorial algebra. -/
noncomputable def limAlgebra : OmegaCatAlgebra.{u, v, w} Sig where
  carrier := F.L
  str s := Tower.limOmegaCategory _
  op σ := F.opFunctor σ
```
:::

# The family of truncations of the limit

The cells of $`\boldsymbol{\mathsf{A}}_n` are exactly the $`n`-cells of the limit: they are
$`n`-cells, being $`n`-cells of $`\boldsymbol{\mathsf{A}}_{n+1}`, and an $`n`-cell of a higher
level comes down to level $`n`. Sending a cell
of $`\boldsymbol{\mathsf{A}}_n` to itself in the limit is thus a homomorphism from
$`\boldsymbol{\mathsf{A}}_n` to the $`n`-truncation of the limit, bijective at every sort; and a
homomorphism of compact $`n`-categorial algebras that is bijective at every sort is an isomorphism,
its inverse preserving the structure because the homomorphism does and is injective.

```lean
end CompatibleFamily

namespace CatAlgebra

variable {n : ℕ} {A B : CatAlgebra.{u, v, w} Sig n}

open Signature in
/-- The inverse of a homomorphism that is bijective at every sort. -/
noncomputable def Hom.inverse (H : Hom A B) (hb : ∀ s, Function.Bijective (H.map s)) :
    Hom B A where
  map s :=
    have e : ∀ y, (H.map s) (Function.surjInv (hb s).2 y) = y := Function.surjInv_eq (hb s).2
    { map := Function.surjInv (hb s).2
      map_sc_eq_sc_map := fun k y => (hb s).1 (by
        rw [e, (H.map s).map_sc_eq_sc_map, e])
      map_tg_eq_tg_map := fun k y => (hb s).1 (by
        rw [e, (H.map s).map_tg_eq_tg_map, e])
      map_comp_eq_comp_map := fun {k f g} h => (hb s).1 (by
        rw [e]
        exact (((H.map s).map_comp_eq_comp_map _).trans (congr_comp₂ (e f) (e g) h)).symm) }
  map_op {ws s} σ b := (hb s).1 (by
    change H.map s (Function.surjInv (hb s).2 _) = H.map s (A.op σ _)
    rw [Function.surjInv_eq (f := ⇑(H.map s)) (hb s).2, H.map_op]
    exact congrArg _ (funext fun j =>
      (Function.surjInv_eq (f := ⇑(H.map (ws.get j))) (hb _).2 (b j)).symm))

lemma Hom.isIso_of_bijective (H : Hom A B) (hb : ∀ s, Function.Bijective (H.map s)) :
    IsIso (show A ⟶ B from H) :=
  ⟨⟨H.inverse hb,
    Hom.ext fun s => Functor.ext fun x => Function.leftInverse_surjInv (hb s) x,
    Hom.ext fun s => Functor.ext fun y => Function.rightInverse_surjInv (hb s).2 y⟩⟩

end CatAlgebra

namespace CompatibleFamily

variable (F : CompatibleFamily.{u, v, w} Sig)

lemma cls_mem (s : S) (n : ℕ) (a : F.alg n s) :
    ∀ u ∈ upperω n, sc u ((F.tower s).cls n a) = (F.tower s).cls n a := by
  intro u hu
  have hnu : n ≤ u + 1 := Nat.le_succ_of_le hu
  rw [← (F.tower s).cls_up hnu a, Tower.sc_cls _ (Nat.lt_succ_self u)]
  exact congrArg _ ((F.tower s).up_cell hnu a u hu (Nat.lt_succ_self u))

lemma exists_cls_of_mem (s : S) (n : ℕ) (z : F.L s) (hz : ∀ u ∈ upperω n, sc u z = z) :
    ∃ a, (F.tower s).cls n a = z := by
  obtain ⟨m, hm, b, rfl⟩ := (F.tower s).exists_cls₁ z n
  obtain ⟨a, rfl⟩ := (F.tower s).up_surj hm.le b fun u hu hum => by
    have := hz u hu
    rwa [Tower.sc_cls _ hum, Tower.cls_inj] at this
  exact ⟨a, ((F.tower s).cls_up hm.le a).symm⟩

open Signature in
/-- Level `n` of a compatible family in the `n`-truncation of its limit. -/
noncomputable def toLim (n : ℕ) : F.alg n ⟶ (truncationω Sig n).obj F.limAlgebra where
  map s :=
    { map := fun a => ⟨(F.tower s).cls n a, F.cls_mem s n a⟩
      map_sc_eq_sc_map := fun k a => Subtype.ext ((Tower.sc_cls (F.tower s) k.isLt a).symm)
      map_tg_eq_tg_map := fun k a => Subtype.ext ((Tower.tg_cls (F.tower s) k.isLt a).symm)
      map_comp_eq_comp_map := fun {k f g} h =>
        Subtype.ext ((Tower.comp_eq (F.tower s) k.isLt rfl rfl
        ((Tower.sc_is_tg_cls (F.tower s) k.isLt).mpr h)).symm) }
  map_op σ a := Subtype.ext (F.opL_cls σ a).symm

lemma toLim_bijective (n : ℕ) (s : S) : Function.Bijective ((F.toLim n).map s) :=
  ⟨fun a b h => by
    have h' : (F.tower s).cls n a = (F.tower s).cls n b := congrArg Subtype.val h
    exact (Tower.cls_inj _).mp h', fun z => by
    obtain ⟨a, ha⟩ := F.exists_cls_of_mem s n z.1 z.2
    exact ⟨a, Subtype.ext (show (F.tower s).cls n a = z.1 from ha)⟩⟩

instance (n : ℕ) : IsIso (F.toLim n) := CatAlgebra.Hom.isIso_of_bijective _ (F.toLim_bijective n)
```

:::construction (label := "compact.limit-iso") (central := false) (title := "A compatible family is the family of truncations of its limit")
The isomorphisms $`\boldsymbol{\mathsf{A}}_n \cong T^{(n,\omega)}_{\Sigma}(\varprojlim_m \boldsymbol{\mathsf{A}}_m)`
that send a cell to itself are compatible with the isomorphisms $`\varphi_n` of the family and with
the canonical isomorphisms of the family of truncations: they form an isomorphism of compatible
families from $`(\boldsymbol{\mathsf{A}}_n, \varphi_n)_n` to the family of truncations of its limit.
Compatibility holds because a cell $`x` of $`T^{(n,n+1)}_{\Sigma}(\boldsymbol{\mathsf{A}}_{n+1})` and its
image $`\varphi_n(x)` in $`\boldsymbol{\mathsf{A}}_n` are the same cell of the limit, the embedding
being $`\varphi_n^{-1}`.

```lean
/-- A compatible family is isomorphic to the family of truncations of its limit. -/
noncomputable def toLimFamily : F ⟶ (truncFamilies Sig).obj F.limAlgebra where
  map := F.toLim
  comm n := by
    apply CatAlgebra.Hom.ext
    intro s
    apply Functor.ext
    intro y
    apply Subtype.ext
    show (F.tower s).cls (n + 1) y.1 = (F.tower s).cls n (((F.iso n).hom.map s).map y)
    rw [← (F.tower s).cls_up (Nat.le_succ n), Tower.up_succ _ le_rfl, Tower.up_self]
    exact congrArg _ (congrArg Subtype.val (F.inv_hom s n y)).symm

end CompatibleFamily

namespace CompatibleFamily

variable {A B : CompatibleFamily.{u, v, w} Sig}

/-- A morphism of compatible families whose components are isomorphisms is an isomorphism. -/
lemma isIso_of_components (Ψ : A ⟶ B) [∀ n, IsIso (Ψ.map n)] : IsIso Ψ := by
  refine ⟨⟨⟨fun n => inv (Ψ.map n), fun n => ?_⟩, ?_, ?_⟩⟩
  · rw [← cancel_epi ((truncation Sig (Nat.le_succ n)).map (Ψ.map (n + 1))),
      ← CategoryTheory.Functor.map_comp_assoc, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
      CategoryTheory.Category.id_comp, ← CategoryTheory.Category.assoc, Ψ.comm,
      CategoryTheory.Category.assoc, IsIso.hom_inv_id, CategoryTheory.Category.comp_id]
  · exact Hom.ext (funext fun n => IsIso.hom_inv_id (Ψ.map n))
  · exact Hom.ext (funext fun n => IsIso.inv_hom_id (Ψ.map n))

end CompatibleFamily

instance (F : CompatibleFamily.{u, v, w} Sig) : IsIso F.toLimFamily :=
  haveI : ∀ n, IsIso (F.toLimFamily.map n) := fun n => inferInstanceAs (IsIso (F.toLim n))
  CompatibleFamily.isIso_of_components _
```
:::

:::proposition (label := "compact.trunc-families-ess-surj") (central := false) (title := "Every compatible family comes from an ω-categorial algebra")
Every compatible family is isomorphic to the family of truncations of a compact
$`\omega`-categorial $`\Sigma`-algebra, its limit: the functor of truncations is essentially
surjective.

```lean
instance truncFamilies_essSurj : (truncFamilies.{u, v, w} Sig).EssSurj where
  mem_essImage F := ⟨F.limAlgebra, ⟨(asIso F.toLimFamily).symm⟩⟩
```
:::

:::proof (of := "compact.trunc-families-ess-surj")
By Construction `compact.limit-iso`, a compatible family is isomorphic to the family of truncations
of its limit (Construction `compact.limit-algebra`).
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

This is Proposition `PUnivPropCatAlg` of the draft, with the projective limit replaced by the
pseudo-limit.

```lean
theorem truncFamilies_isEquivalence : (truncFamilies.{u, v, w} Sig).IsEquivalence :=
  { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }
```
:::

:::proof (of := "compact.omega-cat-alg-pseudo-limit")
The functor of truncations is faithful and full by Proposition
`compact.trunc-families-fully-faithful`, and essentially surjective by Proposition
`compact.trunc-families-ess-surj`; a functor with these three properties is an equivalence.
:::

:::remark (title := "The universal property for functors")
The form of Proposition `PUnivPropCatAlg` of the draft with functors follows: a family of functors
$`F_n \colon \mathsf{L} \to \mathsf{nCatAlg}(\Sigma)` with natural isomorphisms
$`T^{(n,n+1)}_{\Sigma} \circ F_{n+1} \cong F_n` is the same as a functor from $`\mathsf{L}` to the
category of compatible families, and composing it with an inverse of the equivalence gives a functor
$`\mathsf{L} \to \omega\mathsf{CatAlg}(\Sigma)` whose truncations are the $`F_n`, up to compatible
natural isomorphisms, unique up to a unique natural isomorphism. Likewise, the second part of
Corollary `CLimitNat` of the draft, on natural transformations, is the full faithfulness of
composing with an equivalence. These consequences are not formalized here.
:::

```lean
end CategorialAlgebras.Compact
```
