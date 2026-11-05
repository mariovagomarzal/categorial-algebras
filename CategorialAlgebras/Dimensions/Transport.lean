import CategorialAlgebras.Dimensions.Relation
import Mathlib.CategoryTheory.Whiskering

/-!
# Dimension comparisons on categorial algebras

Strict model isomorphisms transport the canonical comparisons to the
categories of categorial algebras, cancelling the intermediate presentation.
-/

universe u v w

namespace CategorialAlgebras.Dimensions

open CategoryTheory

/-- Transport a composite natural isomorphism through three strict category isomorphisms. -/
noncomputable def conjugateCompositeIso {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E] [Category C'] [Category D'] [Category E']
    (a : IsoCat C C') (b : IsoCat D D') (c : IsoCat E E')
    {F : C' ⥤ D'} {G : D' ⥤ E'} {H : C' ⥤ E'} (i : F ⋙ G ≅ H) :
    (a.functor ⋙ F ⋙ b.inverse) ⋙ (b.functor ⋙ G ⋙ c.inverse) ≅
      a.functor ⋙ H ⋙ c.inverse :=
  eqToIso (by
    change (a.functor ⋙ F) ⋙ (b.inverse ⋙ b.functor) ⋙ G ⋙ c.inverse = _
    rw [b.counit_eq]
    rfl) ≪≫ Functor.isoWhiskerRight (Functor.isoWhiskerLeft a.functor i) c.inverse

/-- Transport a round-trip comparison through strict category isomorphisms. -/
noncomputable def conjugateRoundTripIso {C D C' D' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    (a : IsoCat C C') (b : IsoCat D D') {F : C' ⥤ D'} {G : D' ⥤ C'}
    (i : F ⋙ G ≅ 𝟭 C') :
    (a.functor ⋙ F ⋙ b.inverse) ⋙ (b.functor ⋙ G ⋙ a.inverse) ≅ 𝟭 C :=
  conjugateCompositeIso a b a i ≪≫ eqToIso (by
    change a.functor ⋙ (𝟭 C' ⋙ a.inverse) = _
    rw [Functor.id_comp, ← a.unit_eq])

/-- Transport an identity comparison through a strict category isomorphism. -/
noncomputable def conjugateIdentityIso {C C' : Type*} [Category C] [Category C']
    (a : IsoCat C C') {F : C' ⥤ C'} (i : F ≅ 𝟭 C') :
    a.functor ⋙ F ⋙ a.inverse ≅ 𝟭 C :=
  Functor.isoWhiskerRight (Functor.isoWhiskerLeft a.functor i) a.inverse ≪≫ eqToIso (by
    change a.functor ⋙ (𝟭 C' ⋙ a.inverse) = _
    rw [Functor.id_comp, ← a.unit_eq])

variable {S : Type u} (sig : Signature.{u, v} S)

/-- The corresponding composite of homogeneous algebra functors is naturally identified
with the direct induced functor. -/
noncomputable def homogeneousDiscretizationFunctorComp {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    homogeneousDiscretizationFunctor.{u, v, w} sig hmn ⋙ homogeneousDiscretizationFunctor sig hnp ≅ homogeneousDiscretizationFunctor sig (le_trans hmn hnp) :=
  conjugateCompositeIso Homogeneous.modelIsomorphism Homogeneous.modelIsomorphism
    Homogeneous.modelIsomorphism (homogeneousDiscretizationModelsComp sig hmn hnp)

/-- The corresponding composite of homogeneous algebra functors is naturally identified
with the direct induced functor. -/
noncomputable def homogeneousTruncationFunctorComp {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    homogeneousTruncationFunctor.{u, v, w} sig hnp ⋙ homogeneousTruncationFunctor sig hmn ≅ homogeneousTruncationFunctor sig (le_trans hmn hnp) :=
  conjugateCompositeIso Homogeneous.modelIsomorphism Homogeneous.modelIsomorphism
    Homogeneous.modelIsomorphism (homogeneousTruncationModelsComp sig hmn hnp)

/-- The corresponding composite of homogeneous algebra functors is naturally identified
with the direct induced functor. -/
noncomputable def homogeneousMixedUpperFunctor {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    homogeneousDiscretizationFunctor.{u, v, w} sig (le_trans hmn hnp) ⋙ homogeneousTruncationFunctor sig hnp ≅ homogeneousDiscretizationFunctor sig hmn :=
  conjugateCompositeIso Homogeneous.modelIsomorphism Homogeneous.modelIsomorphism
    Homogeneous.modelIsomorphism (homogeneousMixedUpperModels sig hmn hnp)

/-- The corresponding composite of homogeneous algebra functors is naturally identified
with the direct induced functor. -/
noncomputable def homogeneousMixedLowerFunctor {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    homogeneousDiscretizationFunctor.{u, v, w} sig hnp ⋙ homogeneousTruncationFunctor sig (le_trans hmn hnp) ≅ homogeneousTruncationFunctor sig hmn :=
  conjugateCompositeIso Homogeneous.modelIsomorphism Homogeneous.modelIsomorphism
    Homogeneous.modelIsomorphism (homogeneousMixedLowerModels sig hmn hnp)

/-- Truncation retracts homogeneous discretization on categorial algebras. -/
noncomputable def homogeneousRoundTripFunctor {m n : ℕ} (h : m ≤ n) :
    homogeneousDiscretizationFunctor.{u, v, w} sig h ⋙ homogeneousTruncationFunctor sig h ≅ 𝟭 _ :=
  conjugateRoundTripIso Homogeneous.modelIsomorphism Homogeneous.modelIsomorphism
    (homogeneousRoundTripModels sig h)

/-- The corresponding composite of heterogeneous algebra functors is naturally identified
with the direct induced functor. -/
noncomputable def heterogeneousDiscretizationFunctorComp {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    heterogeneousDiscretizationFunctor.{u, v, w} sig hmn ⋙ heterogeneousDiscretizationFunctor sig hnp ≅ heterogeneousDiscretizationFunctor sig (le_trans hmn hnp) :=
  conjugateCompositeIso Heterogeneous.modelIsomorphism Heterogeneous.modelIsomorphism
    Heterogeneous.modelIsomorphism (heterogeneousDiscretizationModelsComp sig hmn hnp)

/-- The corresponding composite of heterogeneous algebra functors is naturally identified
with the direct induced functor. -/
noncomputable def heterogeneousTruncationFunctorComp {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    heterogeneousTruncationFunctor.{u, v, w} sig hnp ⋙ heterogeneousTruncationFunctor sig hmn ≅ heterogeneousTruncationFunctor sig (le_trans hmn hnp) :=
  conjugateCompositeIso Heterogeneous.modelIsomorphism Heterogeneous.modelIsomorphism
    Heterogeneous.modelIsomorphism (heterogeneousTruncationModelsComp sig hmn hnp)

/-- The corresponding composite of heterogeneous algebra functors is naturally identified
with the direct induced functor. -/
noncomputable def heterogeneousMixedUpperFunctor {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    heterogeneousDiscretizationFunctor.{u, v, w} sig (le_trans hmn hnp) ⋙ heterogeneousTruncationFunctor sig hnp ≅ heterogeneousDiscretizationFunctor sig hmn :=
  conjugateCompositeIso Heterogeneous.modelIsomorphism Heterogeneous.modelIsomorphism
    Heterogeneous.modelIsomorphism (heterogeneousMixedUpperModels sig hmn hnp)

/-- The corresponding composite of heterogeneous algebra functors is naturally identified
with the direct induced functor. -/
noncomputable def heterogeneousMixedLowerFunctor {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    heterogeneousDiscretizationFunctor.{u, v, w} sig hnp ⋙ heterogeneousTruncationFunctor sig (le_trans hmn hnp) ≅ heterogeneousTruncationFunctor sig hmn :=
  conjugateCompositeIso Heterogeneous.modelIsomorphism Heterogeneous.modelIsomorphism
    Heterogeneous.modelIsomorphism (heterogeneousMixedLowerModels sig hmn hnp)

/-- Truncation retracts heterogeneous discretization on categorial algebras. -/
noncomputable def heterogeneousRoundTripFunctor {m n : ℕ} (h : m ≤ n) :
    heterogeneousDiscretizationFunctor.{u, v, w} sig h ⋙ heterogeneousTruncationFunctor sig h ≅ 𝟭 _ :=
  conjugateRoundTripIso Heterogeneous.modelIsomorphism Heterogeneous.modelIsomorphism
    (heterogeneousRoundTripModels sig h)


/-- Equal-dimensional homogeneous discretization is naturally identity on categorial algebras. -/
noncomputable def homogeneousDiscretizationFunctorSelf (n : ℕ) :
    homogeneousDiscretizationFunctor.{u, v, w} sig (le_refl n) ≅ 𝟭 _ :=
  conjugateIdentityIso Homogeneous.modelIsomorphism (homogeneousDiscretizationModelsSelf sig n)

/-- Equal-dimensional homogeneous truncation is naturally identity on categorial algebras. -/
noncomputable def homogeneousTruncationFunctorSelf (n : ℕ) :
    homogeneousTruncationFunctor.{u, v, w} sig (le_refl n) ≅ 𝟭 _ :=
  conjugateIdentityIso Homogeneous.modelIsomorphism (homogeneousTruncationModelsSelf sig n)

/-- Equal-dimensional heterogeneous discretization is naturally identity on categorial algebras. -/
noncomputable def heterogeneousDiscretizationFunctorSelf (n : ℕ) :
    heterogeneousDiscretizationFunctor.{u, v, w} sig (le_refl n) ≅ 𝟭 _ :=
  conjugateIdentityIso Heterogeneous.modelIsomorphism (heterogeneousDiscretizationModelsSelf sig n)

/-- Equal-dimensional heterogeneous truncation is naturally identity on categorial algebras. -/
noncomputable def heterogeneousTruncationFunctorSelf (n : ℕ) :
    heterogeneousTruncationFunctor.{u, v, w} sig (le_refl n) ≅ 𝟭 _ :=
  conjugateIdentityIso Heterogeneous.modelIsomorphism (heterogeneousTruncationModelsSelf sig n)

end CategorialAlgebras.Dimensions
