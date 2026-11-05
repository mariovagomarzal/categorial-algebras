import CategorialAlgebras.Limits.Truncations

/-!
# Finite truncations detect morphisms

A heterogeneous cell has its dimension in its sort. A homogeneous cell belongs
to some finite truncation by the finite-dimensional-cell condition. Therefore
all finite truncations together distinguish homomorphisms in either presentation.
-/

universe u v w

namespace CategorialAlgebras.Limits

open CategoryTheory Dimensions

variable {S : Type u} (sig : Signature.{u, v} S)

/-- Homogeneous finite truncations jointly detect homomorphisms. -/
instance homogeneousCone_faithful : (homogeneousCone.{u, v, w} sig).Faithful where
  map_injective {A B} f g h := by
    apply ObjectProperty.hom_ext
    apply model_hom_ext
    intro s x
    obtain ⟨n, hn⟩ := A.property s x
    have hx : (homogeneousOmegaTruncation sig n).IsCell A.obj.obj.obj s x := by
      apply (satisfies_omegaTruncationEquation_iff sig A.obj.obj.obj
        ⟨A.obj.obj.property, A.obj.property⟩ n s x).mpr
      change (Homogeneous.boundaryValue (Homogeneous.model_equations A.obj) n false x) = x
      have he := (Homogeneous.boundary_op (Homogeneous.model_equations A.obj) n false
        (Homogeneous.single x))
      change A.obj.obj.obj.op (.source n s) (Homogeneous.single x) = _ at he
      rw [he] at hn
      exact (Part.mem_some_iff.mp hn).symm
    have he := congrArg (fun t => (t.app n).hom.hom.toMap s ⟨x, hx⟩) h
    exact congrArg Subtype.val he

/-- Heterogeneous finite truncations jointly detect homomorphisms. -/
instance heterogeneousCone_faithful : (heterogeneousCone.{u, v, w} sig).Faithful where
  map_injective {A B} f g h := by
    apply model_hom_ext
    intro p x
    let q : Fin (p.1 + 1) × S := (Fin.last p.1, p.2)
    let y : ((heterogeneousOmegaTruncationModels sig p.1).obj A).obj.obj.carrier q :=
      ⟨x, heterogeneousDimension_isCell sig (omegaInclusion (p.1 + 1)).toOrderHom A.obj.obj q x⟩
    have he := congrArg (fun t => (t.app p.1).hom.hom.toMap q y) h
    exact congrArg Subtype.val he

end CategorialAlgebras.Limits
