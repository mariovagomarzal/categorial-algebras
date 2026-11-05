import CategorialAlgebras.Dimensions.OmegaDescriptions

/-!
# Transport between recovered models and their original carriers

Recovery changes only operation data. Its equality with the original model
therefore transports elements by the identity, independently of dimensions.
-/

universe i u v w

namespace CategorialAlgebras.Limits

open CategoryTheory Dimensions Presentations

/-- Equality of partial algebras with a fixed carrier acts identically on elements. -/
theorem fixedCarrier_eqToHom {S : Type u} {sig : Signature.{u, v} S} {C : S → Type w}
    {op op' : PartialAlgebraStructure sig C}
    (h : (⟨C, op⟩ : PartialAlgebra sig) = ⟨C, op'⟩) (s) (x : C s) :
    (eqToHom h).toMap s x = x := by
  rw [partial_eqToHom_toMap]
  rfl

/-- The inverse of any reindexing realization forgets the empty-domain cell proof. -/
theorem dimensionRealization_inv {I J : Type} [LinearOrder I] [LinearOrder J]
    {S : Type u} {sig : Signature.{u, v} S} (f : I →o J) (hf : Saturating f)
    (C : Heterogeneous.CategorialAlgebra.{0, u, v, w} J sig) (p)
    (x : (heterogeneousDimension sig f).Cell C.toPartialAlgebra p) :
    (heterogeneousDimensionRealization sig f hf C).inv.toMap p x = x.val := by
  let e := heterogeneousDimensionRealization sig f hf C
  exact congrArg (fun g : (heterogeneousDimension sig f).transformed C.toPartialAlgebra ⟶
    (heterogeneousDimension sig f).transformed C.toPartialAlgebra => (g.toMap p x).val)
    e.inv_hom_id

end CategorialAlgebras.Limits
