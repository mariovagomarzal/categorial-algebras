import CategorialAlgebras.Presentations.Realization
import CategorialAlgebras.Heterogeneous.Identification
import CategorialAlgebras.Homogeneous.Omega

/-!
# Recognizing isomorphisms of categorial algebras

An injective homomorphism reflects composition domains, since it preserves
boundaries. Consequently a sortwise bijective homomorphism is an isomorphism.
-/

universe i u v w
namespace CategorialAlgebras.Omega
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
variable {I : Type i} [Preorder I] {S : Type u} {sig : Signature.{u, v} S}

/-- Injective homogeneous homomorphisms reflect all partial operation domains. -/
theorem homogeneous_reflectsDefinedness
    {A B : Homogeneous.CategorialAlgebra.{i, u, v, w} I sig} (f : A ⟶ B)
    (hf : ∀ s, Function.Injective (f.sort s).toFun) : f.toPartialHom.ReflectsDefinedness := by
  intro a s σ x hd
  cases σ with
  | base _ => trivial
  | source _ _ => trivial
  | target _ _ => trivial
  | comp k s =>
    change (((B.sort s).str.dim k).comp ((f.sort s).toFun (x 0))
      ((f.sort s).toFun (x 1))).Dom at hd
    change (((A.sort s).str.dim k).comp (x 0) (x 1)).Dom
    rw [Homogeneous.CategoryStructure.comp_dom] at hd ⊢
    apply hf s
    rw [(f.sort s).map_source, (f.sort s).map_target]
    exact hd

/-- A bijective homogeneous homomorphism determines an isomorphism with that forward map. -/
noncomputable def homogeneousIsoOfBijective
    {A B : Homogeneous.CategorialAlgebra.{i, u, v, w} I sig} (f : A ⟶ B)
    (hf : ∀ s, Function.Bijective (f.sort s).toFun) : A ≅ B where
  hom := f
  inv := Homogeneous.CategorialAlgebra.Hom.ofPartialHom
    (f.toPartialHom.inverse hf (homogeneous_reflectsDefinedness f (fun s => (hf s).1)))
  hom_inv_id := by
    apply Homogeneous.CategorialAlgebra.Hom.ext
    funext s
    apply Homogeneous.Functor.ext
    funext x
    exact (Equiv.ofBijective (f.sort s).toFun (hf s)).symm_apply_apply x
  inv_hom_id := by
    apply Homogeneous.CategorialAlgebra.Hom.ext
    funext s
    apply Homogeneous.Functor.ext
    funext x
    exact (Equiv.ofBijective (f.sort s).toFun (hf s)).apply_symm_apply x

/-- Injective heterogeneous homomorphisms reflect all partial operation domains. -/
theorem heterogeneous_reflectsDefinedness
    {A B : Heterogeneous.CategorialAlgebra.{i, u, v, w} I sig} (f : A ⟶ B)
    (hf : ∀ s k, Function.Injective ((f.sort s).toFun k)) :
    f.toPartialHom.ReflectsDefinedness := by
  intro a s σ x hd
  cases σ with
  | base _ => trivial
  | source _ _ => trivial
  | target _ _ => trivial
  | identity _ _ => trivial
  | @comp j k h s =>
    change (((B.sort s).str.dim j k h).comp ((f.sort s).toFun k (x 0))
      ((f.sort s).toFun k (x 1))).Dom at hd
    change (((A.sort s).str.dim j k h).comp (x 0) (x 1)).Dom
    rw [Heterogeneous.CategoryStructure.comp_dom] at hd ⊢
    apply hf s j
    rw [(f.sort s).map_source, (f.sort s).map_target]
    exact hd

/-- A bijective heterogeneous homomorphism determines an isomorphism with that forward map. -/
noncomputable def heterogeneousIsoOfBijective
    {A B : Heterogeneous.CategorialAlgebra.{i, u, v, w} I sig} (f : A ⟶ B)
    (hf : ∀ s k, Function.Bijective ((f.sort s).toFun k)) : A ≅ B where
  hom := f
  inv := Heterogeneous.CategorialAlgebra.Hom.ofPartialHom
    (f.toPartialHom.inverse (fun p => hf p.2 p.1)
      (heterogeneous_reflectsDefinedness f (fun s k => (hf s k).1)))
  hom_inv_id := by
    apply Heterogeneous.CategorialAlgebra.Hom.ext
    funext s
    apply Heterogeneous.Functor.ext
    funext k x
    exact (Equiv.ofBijective ((f.sort s).toFun k) (hf s k)).symm_apply_apply x
  inv_hom_id := by
    apply Heterogeneous.CategorialAlgebra.Hom.ext
    funext s
    apply Heterogeneous.Functor.ext
    funext k x
    exact (Equiv.ofBijective ((f.sort s).toFun k) (hf s k)).apply_symm_apply x

end CategorialAlgebras.Omega
