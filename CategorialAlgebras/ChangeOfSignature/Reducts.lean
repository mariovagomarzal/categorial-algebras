import CategorialAlgebras.ChangeOfSignature.HomogeneousTerms
import CategorialAlgebras.ChangeOfSignature.HeterogeneousTerms
import Mathlib.CategoryTheory.Category.Cat

/-!
# Reducts of categorial algebras along a derivor

A derivor $\mathbf{c}=(\varphi,c)$ from $\Sigma$ to $\Lambda$ sends a categorial
$\Lambda$-algebra $\mathbf{B}$ to the categorial $\Sigma$-algebra whose higher category of
sort $s$ is that of sort $\varphi(s)$ of $\mathbf{B}$ and in which every operation symbol
$\sigma$ of $\Sigma$ acts as the higher functor of the term $c(\sigma)$; in the heterogeneous
presentation, $\sigma_k$ acts as $c(\sigma)_k$. Homomorphisms are reindexed along $\varphi$.

These reducts preserve compositions and identities of derivors strictly, so that the
categories of homogeneous and of heterogeneous categorial algebras are split indexed
categories over many-sorted signatures and derivors.
-/

universe i u u' u'' v v' v'' w x

namespace CategorialAlgebras.ChangeOfSignature

open CategoryTheory

variable {S : Type u} {T : Type u'} {U : Type u''}
variable {sig : Signature.{u, v} S} {tau : Signature.{u', v'} T} {ups : Signature.{u'', v''} U}

/-! ## The homogeneous presentation -/

section Homogeneous

variable {I : Type i} [LT I]

open Homogeneous

/-- The reduct of a homogeneous categorial algebra along a derivor: the sort $s$ is the
sort $\varphi(s)$ and every symbol $\sigma$ acts as the term functor of $c(\sigma)$. -/
def homogeneousReduct (c : Derivor sig tau) (B : CategorialAlgebra.{i, u', v', w} I tau) :
    CategorialAlgebra.{i, u, v, w} I sig where
  sort s := B.sort (c.sortMap s)
  op {a _} σ := B.termFunctor c.sortMap a (c.image σ)

/-- The reduct of a homomorphism, reindexed along the sort map. -/
def homogeneousReductHom (c : Derivor sig tau) {B C : CategorialAlgebra.{i, u', v', w} I tau}
    (f : B ⟶ C) : homogeneousReduct c B ⟶ homogeneousReduct c C where
  sort s := f.sort (c.sortMap s)
  map_op σ x := CategorialAlgebra.Hom.map_termFunctor f c.sortMap _ (c.image σ) x

/-- The reduct functor along a derivor. -/
def homogeneousReductFunctor (I : Type i) [LT I] (c : Derivor sig tau) :
    CategorialAlgebra.{i, u', v', w} I tau ⥤ CategorialAlgebra.{i, u, v, w} I sig where
  obj := homogeneousReduct c
  map := homogeneousReductHom c

/-- The reduct functor reindexes homomorphisms along the sort map. -/
@[simp] theorem homogeneousReductFunctor_map_sort (c : Derivor sig tau)
    {B C : CategorialAlgebra.{i, u', v', w} I tau} (f : B ⟶ C) (s : S) :
    ((homogeneousReductFunctor I c).map f).sort s = f.sort (c.sortMap s) := rfl

/-- Term functors of translated terms are the term functors in the reduct. -/
theorem termFunctor_translate (d : Derivor tau ups)
    (B : CategorialAlgebra.{i, u'', v'', w} I ups) {R : Type x} (ρ : R → T) (a : List R)
    {t} (P : Term tau (Word.MappedVariables ρ a) t) :
    B.termFunctor (d.sortMap ∘ ρ) a (d.translate (d.positionMap ρ a) P) =
      (homogeneousReduct d B).termFunctor ρ a P := by
  induction P with
  | var y =>
    obtain ⟨j, h⟩ := y
    cases h
    rfl
  | app σ t ih =>
    change B.termFunctor (d.sortMap ∘ ρ) a
        (Term.substFamily (fun j => d.translate (d.positionMap ρ a) (t j)) (d.image σ)) = _
    rw [CategorialAlgebra.termFunctor_substFamily]
    change _ = (HigherCategory.productLift fun j => (homogeneousReduct d B).termFunctor ρ a (t j)).comp
      (B.termFunctor d.sortMap _ (d.image σ))
    congr 2
    funext j
    exact ih j

/-- Homomorphisms between equal categorial algebras with the same underlying functors are
heterogeneously equal. -/
theorem hom_heq {A A' B B' : CategorialAlgebra.{i, u, v, w} I sig} (hA : A = A')
    (hB : B = B') (f : A ⟶ B) (g : A' ⟶ B') (h : HEq f.sort g.sort) : HEq f g := by
  subst hA hB
  cases f
  cases g
  cases h
  rfl

/-- The reduct along a composite derivor is the successive reduct. -/
theorem homogeneousReduct_comp (c : Derivor sig tau) (d : Derivor tau ups)
    (B : CategorialAlgebra.{i, u'', v'', w} I ups) :
    homogeneousReduct (c.comp d) B = homogeneousReduct c (homogeneousReduct d B) := by
  unfold homogeneousReduct
  congr 1
  funext a s σ
  exact termFunctor_translate d B c.sortMap a (c.image σ)

/-- The reduct along an identity derivor is the original algebra. -/
theorem homogeneousReduct_identity (B : CategorialAlgebra.{i, u', v', w} I tau) :
    homogeneousReduct (Derivor.identity tau) B = B := by
  cases B with
  | mk sort op =>
    unfold homogeneousReduct
    congr 1

/-- The reduct functor of a composite derivor is the composite of the reduct functors, in
the opposite order. -/
theorem homogeneousReductFunctor_comp (c : Derivor sig tau) (d : Derivor tau ups) :
    homogeneousReductFunctor.{i, u, u'', v, v'', w} I (c.comp d) =
      homogeneousReductFunctor I d ⋙ homogeneousReductFunctor I c :=
  Functor.hext (homogeneousReduct_comp c d) (fun _ _ _ =>
    hom_heq (homogeneousReduct_comp c d _) (homogeneousReduct_comp c d _) _ _ HEq.rfl)

/-- The reduct functor of an identity derivor is the identity functor. -/
theorem homogeneousReductFunctor_identity (tau : Signature.{u', v'} T) :
    homogeneousReductFunctor.{i, u', u', v', v', w} I (Derivor.identity tau) = 𝟭 _ :=
  Functor.hext homogeneousReduct_identity (fun _ _ _ =>
    hom_heq (homogeneousReduct_identity _) (homogeneousReduct_identity _) _ _ HEq.rfl)

end Homogeneous

/-! ## The heterogeneous presentation -/

section Heterogeneous

variable {I : Type i} [Preorder I]

open Heterogeneous

/-- The reduct of a heterogeneous categorial algebra along a derivor: the sort $s$ is the
sort $\varphi(s)$ and every symbol $\sigma_k$ acts as $c(\sigma)_k$, that is, as the term
functor of $c(\sigma)$ in dimension $k$. -/
def heterogeneousReduct (c : Derivor sig tau) (B : CategorialAlgebra.{i, u', v', w} I tau) :
    CategorialAlgebra.{i, u, v, w} I sig where
  sort s := B.sort (c.sortMap s)
  op {a _} σ := B.termFunctor c.sortMap a (c.image σ)

/-- The reduct of a homomorphism, reindexed along the sort map. -/
def heterogeneousReductHom (c : Derivor sig tau) {B C : CategorialAlgebra.{i, u', v', w} I tau}
    (f : B ⟶ C) : heterogeneousReduct c B ⟶ heterogeneousReduct c C where
  sort s := f.sort (c.sortMap s)
  map_op σ k x := CategorialAlgebra.Hom.map_termFunctor f c.sortMap _ (c.image σ) k x

/-- The reduct functor along a derivor. -/
def heterogeneousReductFunctor (I : Type i) [Preorder I] (c : Derivor sig tau) :
    CategorialAlgebra.{i, u', v', w} I tau ⥤ CategorialAlgebra.{i, u, v, w} I sig where
  obj := heterogeneousReduct c
  map := heterogeneousReductHom c

/-- The reduct functor reindexes homomorphisms along the sort map. -/
@[simp] theorem heterogeneousReductFunctor_map_sort (c : Derivor sig tau)
    {B C : CategorialAlgebra.{i, u', v', w} I tau} (f : B ⟶ C) (s : S) :
    ((heterogeneousReductFunctor I c).map f).sort s = f.sort (c.sortMap s) := rfl

/-- Term functors of translated terms are the term functors in the reduct. -/
theorem heterogeneous_termFunctor_translate (d : Derivor tau ups)
    (B : CategorialAlgebra.{i, u'', v'', w} I ups) {R : Type x} (ρ : R → T) (a : List R)
    {t} (P : Term tau (Word.MappedVariables ρ a) t) :
    B.termFunctor (d.sortMap ∘ ρ) a (d.translate (d.positionMap ρ a) P) =
      (heterogeneousReduct d B).termFunctor ρ a P := by
  induction P with
  | var y =>
    obtain ⟨j, h⟩ := y
    cases h
    rfl
  | app σ t ih =>
    change B.termFunctor (d.sortMap ∘ ρ) a
        (Term.substFamily (fun j => d.translate (d.positionMap ρ a) (t j)) (d.image σ)) = _
    rw [CategorialAlgebra.termFunctor_substFamily]
    change _ = (HigherCategory.productLift fun j =>
      (heterogeneousReduct d B).termFunctor ρ a (t j)).comp
      (B.termFunctor d.sortMap _ (d.image σ))
    congr 2
    funext j
    exact ih j

/-- Homomorphisms between equal categorial algebras with the same underlying functors are
heterogeneously equal. -/
theorem heterogeneous_hom_heq {A A' B B' : CategorialAlgebra.{i, u, v, w} I sig}
    (hA : A = A') (hB : B = B') (f : A ⟶ B) (g : A' ⟶ B') (h : HEq f.sort g.sort) :
    HEq f g := by
  subst hA hB
  cases f
  cases g
  cases h
  rfl

/-- The reduct along a composite derivor is the successive reduct. -/
theorem heterogeneousReduct_comp (c : Derivor sig tau) (d : Derivor tau ups)
    (B : CategorialAlgebra.{i, u'', v'', w} I ups) :
    heterogeneousReduct (c.comp d) B = heterogeneousReduct c (heterogeneousReduct d B) := by
  unfold heterogeneousReduct
  congr 1
  funext a s σ
  exact heterogeneous_termFunctor_translate d B c.sortMap a (c.image σ)

/-- The reduct along an identity derivor is the original algebra. -/
theorem heterogeneousReduct_identity (B : CategorialAlgebra.{i, u', v', w} I tau) :
    heterogeneousReduct (Derivor.identity tau) B = B := by
  cases B with
  | mk sort op =>
    unfold heterogeneousReduct
    congr 1

/-- The reduct functor of a composite derivor is the composite of the reduct functors, in
the opposite order. -/
theorem heterogeneousReductFunctor_comp (c : Derivor sig tau) (d : Derivor tau ups) :
    heterogeneousReductFunctor.{i, u, u'', v, v'', w} I (c.comp d) =
      heterogeneousReductFunctor I d ⋙ heterogeneousReductFunctor I c :=
  Functor.hext (heterogeneousReduct_comp c d) (fun _ _ _ =>
    heterogeneous_hom_heq (heterogeneousReduct_comp c d _) (heterogeneousReduct_comp c d _)
      _ _ HEq.rfl)

/-- The reduct functor of an identity derivor is the identity functor. -/
theorem heterogeneousReductFunctor_identity (tau : Signature.{u', v'} T) :
    heterogeneousReductFunctor.{i, u', u', v', v', w} I (Derivor.identity tau) = 𝟭 _ :=
  Functor.hext heterogeneousReduct_identity (fun _ _ _ =>
    heterogeneous_hom_heq (heterogeneousReduct_identity _) (heterogeneousReduct_identity _)
      _ _ HEq.rfl)

end Heterogeneous

/-! ## Split indexed categories -/

/-- Homogeneous categorial algebras, with dimensions in $I$, form a split indexed category
over many-sorted signatures and derivors, with reindexing given by reducts. -/
def homogeneousIndexed (I : Type i) [LT I] :
    ManySortedSignature.{u, v}ᵒᵖ ⥤ Cat.{max u w, max i u v (w + 1)} where
  obj sig := Cat.of (Homogeneous.CategorialAlgebra.{i, u, v, w} I sig.unop.symbol)
  map c := (homogeneousReductFunctor I c.unop).toCatHom
  map_id sig := congrArg Functor.toCatHom (homogeneousReductFunctor_identity sig.unop.symbol)
  map_comp c d := congrArg Functor.toCatHom (homogeneousReductFunctor_comp d.unop c.unop)

/-- Heterogeneous categorial algebras, with dimensions in $I$, form a split indexed category
over many-sorted signatures and derivors, with reindexing given by reducts. -/
def heterogeneousIndexed (I : Type i) [Preorder I] :
    ManySortedSignature.{u, v}ᵒᵖ ⥤ Cat.{max i u w, max i u v (w + 1)} where
  obj sig := Cat.of (Heterogeneous.CategorialAlgebra.{i, u, v, w} I sig.unop.symbol)
  map c := (heterogeneousReductFunctor I c.unop).toCatHom
  map_id sig := congrArg Functor.toCatHom (heterogeneousReductFunctor_identity sig.unop.symbol)
  map_comp c d := congrArg Functor.toCatHom (heterogeneousReductFunctor_comp d.unop c.unop)

end CategorialAlgebras.ChangeOfSignature
