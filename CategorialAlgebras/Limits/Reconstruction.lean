import CategorialAlgebras.Limits.HomogeneousReconstruction
import CategorialAlgebras.Limits.HeterogeneousReconstruction
import CategorialAlgebras.Limits.HomogeneousMorphisms
import CategorialAlgebras.Limits.HeterogeneousMorphisms

/-!
# Reconstruction of natural-dimensional models

The reconstruction carriers and operations are the explicit increasing union
and diagonal constructions. The comparison with each finite stage is required
to agree with the canonical inclusions and transports of elements.
-/

universe u v w

namespace CategorialAlgebras.Limits

open CategoryTheory Dimensions

variable {S : Type u} (sig : Signature.{u, v} S)

/-- Model and comparison data for the explicit homogeneous union construction. -/
structure HomogeneousReconstruction (A : (homogeneousSystem.{u, v, w} sig).Family) where
  /-- The union operations satisfy the natural-dimensional specification. -/
  isModel : (Homogeneous.specification ℕ sig).IsModel (homogeneousUnionPartial A)
  /-- Every union cell is fixed by some source. -/
  finiteCells : Homogeneous.FiniteCells (homogeneousUnionPartial A)
  /-- The compatible finite restrictions of the union are the given family. -/
  comparison : (homogeneousCone sig).obj
    ⟨⟨⟨homogeneousUnionPartial A, isModel.1⟩, isModel.2⟩, finiteCells⟩ ≅ A
  /-- The inverse comparison inserts the original finite-stage element into the union. -/
  comparison_inv_val : ∀ n s (x : (A.obj n).obj.obj.carrier s),
    ((comparison.inv.app n).hom.hom.toMap s x).val = homogeneousUnionIn A n s x

/-- The explicit union reconstructs every coherent homogeneous family. -/
theorem homogeneous_reconstruction (A : (homogeneousSystem.{u, v, w} sig).Family) :
    Nonempty (HomogeneousReconstruction sig A) := by
  exact ⟨{
    isModel := homogeneousUnion_isModel A
    finiteCells := homogeneousUnion_finite A
    comparison := homogeneousUnionComparison A
    comparison_inv_val := homogeneousUnionFiniteIso_hom A }⟩

/-- Model and comparison data for the explicit heterogeneous diagonal construction. -/
structure HeterogeneousReconstruction (A : (heterogeneousSystem.{u, v, w} sig).Family) where
  /-- The diagonal operations satisfy the natural-dimensional specification. -/
  isModel : (Heterogeneous.specification ℕ sig).IsModel (heterogeneousDiagonalPartial A)
  /-- The compatible finite restrictions of the diagonal are the given family. -/
  comparison : (heterogeneousCone sig).obj
    ⟨⟨heterogeneousDiagonalPartial A, isModel.1⟩, isModel.2⟩ ≅ A
  /-- The inverse comparison transports an element to its diagonal carrier. -/
  comparison_inv_val : ∀ n (j : Fin (n + 1)) s
    (x : (A.obj n).obj.obj.carrier (j, s)),
    ((comparison.inv.app n).hom.hom.toMap (j, s) x).val =
      heterogeneousStageDown A (Nat.le_of_lt_succ j.isLt) s x

/-- The explicit diagonal reconstructs every coherent heterogeneous family. -/
theorem heterogeneous_reconstruction (A : (heterogeneousSystem.{u, v, w} sig).Family) :
    Nonempty (HeterogeneousReconstruction sig A) := by
  exact ⟨{
    isModel := heterogeneousDiagonal_isModel A
    comparison := heterogeneousDiagonalComparison A
    comparison_inv_val := heterogeneousDiagonalFiniteIso_inv A }⟩

/-- Every compatible family of homogeneous truncated homomorphisms lifts to a homomorphism. -/
theorem homogeneousCone_full : (homogeneousCone.{u, v, w} sig).Full :=
  homogeneousCone_full_proof

/-- Every compatible family of heterogeneous truncated homomorphisms lifts to a homomorphism. -/
theorem heterogeneousCone_full : (heterogeneousCone.{u, v, w} sig).Full :=
  heterogeneousCone_full_proof

/-- The homogeneous reconstruction on its explicit union carrier. -/
noncomputable def homogeneousReconstruction (A : (homogeneousSystem.{u, v, w} sig).Family) :
    HomogeneousReconstruction sig A := Classical.choice (homogeneous_reconstruction sig A)

/-- The heterogeneous reconstruction on its explicit diagonal carriers. -/
noncomputable def heterogeneousReconstruction (A : (heterogeneousSystem.{u, v, w} sig).Family) :
    HeterogeneousReconstruction sig A := Classical.choice (heterogeneous_reconstruction sig A)

/-- The homogeneous cone is essentially surjective by the explicit union construction. -/
instance homogeneousCone_essSurj : (homogeneousCone.{u, v, w} sig).EssSurj where
  mem_essImage A :=
    let r := homogeneousReconstruction sig A
    ⟨⟨⟨⟨homogeneousUnionPartial A, r.isModel.1⟩, r.isModel.2⟩, r.finiteCells⟩,
      ⟨r.comparison⟩⟩

/-- The heterogeneous cone is essentially surjective by the explicit diagonal construction. -/
instance heterogeneousCone_essSurj : (heterogeneousCone.{u, v, w} sig).EssSurj where
  mem_essImage A :=
    let r := heterogeneousReconstruction sig A
    ⟨⟨⟨heterogeneousDiagonalPartial A, r.isModel.1⟩, r.isModel.2⟩, ⟨r.comparison⟩⟩

/-- The homogeneous cone identifies natural-dimensional models with compatible families. -/
instance homogeneousCone_isEquivalence : (homogeneousCone.{u, v, w} sig).IsEquivalence :=
  ⟨inferInstance, homogeneousCone_full sig, inferInstance⟩

/-- The heterogeneous cone identifies natural-dimensional models with compatible families. -/
instance heterogeneousCone_isEquivalence : (heterogeneousCone.{u, v, w} sig).IsEquivalence :=
  ⟨inferInstance, heterogeneousCone_full sig, inferInstance⟩

end CategorialAlgebras.Limits
