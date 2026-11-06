import CategorialAlgebras.ChangeOfSignature.Compatibility
import CategorialAlgebras.Dimensions.OmegaComposition

/-!
# Change of signature in dimension $\omega$

The derivors of a change of signature in dimension $\omega$ are the derivors
$\mathbf{c}^{(\omega)}$ and $\mathbf{c}^{\mathrm{htg}(\omega)}$ of the general construction
with natural dimensions; their translation of terms and their compositions and identities
are covered by the general results. In the heterogeneous presentation the categories of
$\omega$-categorial algebras are those of all categorial algebras with natural dimensions,
so the functors are those of the general construction. In the homogeneous presentation the
functor induced by $\mathbf{c}^{(\omega)}$ also preserves the condition that every cell has
a finite dimension, since the cells of sort $s$ are those of sort $\varphi(s)$ with the same
sources, and so does the reduct; this gives the functor between homogeneous
$\omega$-categorial algebras and the split indexed category of these algebras.
-/

universe u v w

namespace CategorialAlgebras.ChangeOfSignature

open CategoryTheory Presentations Dimensions

set_option backward.isDefEq.respectTransparency false

variable {S T U : Type u} {sig : Signature.{u, v} S} {tau : Signature.{u, v} T}
  {ups : Signature.{u, v} U}

/-- An isomorphism of functors to a full subcategory, from one after the inclusion. -/
noncomputable def liftIso {C : Type*} {D : Type*} [Category C] [Category D]
    {P : ObjectProperty D} {F G : C ⥤ P.FullSubcategory} (e : F ⋙ P.ι ≅ G ⋙ P.ι) : F ≅ G :=
  NatIso.ofComponents (fun X => ObjectProperty.isoMk _ (e.app X)) (fun f => by
    apply ObjectProperty.hom_ext
    exact e.hom.naturality f)

/-! ## Finite-dimensional cells -/

/-- The homogeneous derivor of a change of signature in natural dimensions preserves the
condition that every cell has a finite dimension. -/
theorem homogeneous_finiteCells (c : Derivor sig tau)
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol ℕ tau))
    (hB : Homogeneous.FiniteCells B) :
    Homogeneous.FiniteCells ((homogeneous ℕ c).transformed B) := by
  intro s x
  obtain ⟨k, hk⟩ := hB (c.sortMap s) x.val
  refine ⟨k, ((homogeneous ℕ c).mem_transformed_op B _ _ _).mpr ⟨fun _ _ he => he.elim, ?_⟩⟩
  change x.val ∈ Term.partialEval _ (Homogeneous.unary (.source k (c.sortMap s)) _)
  erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some]
  exact hk

/-- The reduct of a homogeneous $\omega$-categorial algebra has finite-dimensional cells. -/
theorem homogeneousReduct_finiteDimensional (c : Derivor sig tau)
    (B : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ tau) (hB : B.FiniteDimensional) :
    (homogeneousReduct c B).FiniteDimensional :=
  fun s => hB (c.sortMap s)

/-! ## The homogeneous functors -/

/-- The functor induced by $\mathbf{c}^{(\omega)}$ on homogeneous models with
finite-dimensional cells. -/
noncomputable def homogeneousOmegaModels (c : Derivor sig tau) :
    Homogeneous.OmegaModels.{u, v, w} tau ⥤ Homogeneous.OmegaModels.{u, v, w} sig :=
  corestrict (Homogeneous.omegaInclusion tau ⋙ homogeneousModels ℕ c) _ (fun B =>
    homogeneous_finiteCells c B.obj.obj.obj B.property)

/-- The functor $\mathbf{c}^{(\omega)\ast}_{\mathfrak{gd}}$ between homogeneous
$\omega$-categorial algebras, transported along the model isomorphisms. -/
noncomputable def homogeneousOmegaFunctor (c : Derivor sig tau) :
    Homogeneous.OmegaCategorialAlgebra.{u, v, w} tau ⥤
      Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig :=
  Homogeneous.omegaModelIsomorphism.functor ⋙ homogeneousOmegaModels c ⋙
    Homogeneous.omegaModelIsomorphism.inverse

/-- The reduct functor between homogeneous $\omega$-categorial algebras. -/
def homogeneousOmegaReductFunctor (c : Derivor sig tau) :
    Homogeneous.OmegaCategorialAlgebra.{u, v, w} tau ⥤
      Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig :=
  corestrict (ObjectProperty.ι _ ⋙ homogeneousReductFunctor ℕ c) _ (fun B =>
    homogeneousReduct_finiteDimensional c B.obj B.property)

/-- The reduct and the induced model functor agree after expansion to models. -/
noncomputable def homogeneousOmegaModelsReductIso (c : Derivor sig tau) :
    homogeneousOmegaReductFunctor.{u, v, w} c ⋙ Homogeneous.omegaModelIsomorphism.functor ≅
      Homogeneous.omegaModelIsomorphism.functor ⋙ homogeneousOmegaModels c :=
  liftIso (NatIso.ofComponents (fun B => modelIso _ _ (homogeneousRealization c B.obj)) (by
    intro B C f
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply PartialAlgebra.Hom.ext
    funext s x
    rfl))

/-- The functor of a change of signature between homogeneous $\omega$-categorial algebras
is the reduct functor, up to a natural isomorphism that retains the underlying elements. -/
noncomputable def homogeneousOmegaFunctorReductIso (c : Derivor sig tau) :
    homogeneousOmegaFunctor.{u, v, w} c ≅ homogeneousOmegaReductFunctor c :=
  Functor.isoWhiskerRight (homogeneousOmegaModelsReductIso c).symm
      Homogeneous.omegaModelIsomorphism.inverse ≪≫
    eqToIso (by
      change homogeneousOmegaReductFunctor c ⋙
        (Homogeneous.omegaModelIsomorphism.functor ⋙
          Homogeneous.omegaModelIsomorphism.inverse) = _
      rw [← Homogeneous.omegaModelIsomorphism.unit_eq]
      rfl)

/-- The functor of a composite derivor between homogeneous $\omega$-categorial algebras is
the composite of the functors, up to a natural isomorphism. -/
noncomputable def homogeneousOmegaModelsComp (c : Derivor sig tau) (d : Derivor tau ups) :
    homogeneousOmegaModels.{u, v, w} d ⋙ homogeneousOmegaModels c ≅
      homogeneousOmegaModels (c.comp d) :=
  liftIso (Functor.isoWhiskerLeft (Homogeneous.omegaInclusion ups)
    (homogeneousModelsComp ℕ c d))

/-- The functor of an identity derivor between homogeneous $\omega$-categorial algebras is
the identity, up to a natural isomorphism. -/
noncomputable def homogeneousOmegaModelsIdentity (sig : Signature.{u, v} S) :
    homogeneousOmegaModels.{u, v, w} (Derivor.identity sig) ≅ 𝟭 _ :=
  liftIso (Functor.isoWhiskerLeft (Homogeneous.omegaInclusion sig)
    (homogeneousModelsIdentity ℕ sig))

/-- On homogeneous $\omega$-categorial algebras, the functor of a composite derivor is the
composite of the functors, up to a natural isomorphism. -/
noncomputable def homogeneousOmegaFunctorComp (c : Derivor sig tau) (d : Derivor tau ups) :
    homogeneousOmegaFunctor.{u, v, w} d ⋙ homogeneousOmegaFunctor c ≅
      homogeneousOmegaFunctor (c.comp d) :=
  conjugateCompositeIso Homogeneous.omegaModelIsomorphism Homogeneous.omegaModelIsomorphism
    Homogeneous.omegaModelIsomorphism (homogeneousOmegaModelsComp c d)

/-- On homogeneous $\omega$-categorial algebras, the functor of an identity derivor is the
identity, up to a natural isomorphism. -/
noncomputable def homogeneousOmegaFunctorIdentity (sig : Signature.{u, v} S) :
    homogeneousOmegaFunctor.{u, v, w} (Derivor.identity sig) ≅ 𝟭 _ :=
  conjugateIdentityIso Homogeneous.omegaModelIsomorphism (homogeneousOmegaModelsIdentity sig)

/-- The reduct functor of a composite derivor between homogeneous $\omega$-categorial
algebras is the composite of the reduct functors. -/
theorem homogeneousOmegaReductFunctor_comp (c : Derivor sig tau) (d : Derivor tau ups) :
    homogeneousOmegaReductFunctor.{u, v, w} (c.comp d) =
      homogeneousOmegaReductFunctor d ⋙ homogeneousOmegaReductFunctor c := by
  apply inclusion_comp_injective
  change ObjectProperty.ι _ ⋙ homogeneousReductFunctor ℕ (c.comp d) =
    ObjectProperty.ι _ ⋙ homogeneousReductFunctor ℕ d ⋙ homogeneousReductFunctor ℕ c
  rw [homogeneousReductFunctor_comp]

/-- The reduct functor of an identity derivor between homogeneous $\omega$-categorial
algebras is the identity. -/
theorem homogeneousOmegaReductFunctor_identity (sig : Signature.{u, v} S) :
    homogeneousOmegaReductFunctor.{u, v, w} (Derivor.identity sig) = 𝟭 _ := by
  apply inclusion_comp_injective
  change ObjectProperty.ι _ ⋙ homogeneousReductFunctor ℕ (Derivor.identity sig) =
    ObjectProperty.ι _
  rw [homogeneousReductFunctor_identity]
  rfl

/-- Homogeneous $\omega$-categorial algebras form a split indexed category over many-sorted
signatures and derivors, with reindexing given by reducts. -/
def homogeneousOmegaIndexed :
    ManySortedSignature.{u, v}ᵒᵖ ⥤ Cat.{max u w, max u v (w + 1)} where
  obj sig := Cat.of (Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig.unop.symbol)
  map c := (homogeneousOmegaReductFunctor c.unop).toCatHom
  map_id sig := congrArg Functor.toCatHom (homogeneousOmegaReductFunctor_identity sig.unop.symbol)
  map_comp c d := congrArg Functor.toCatHom (homogeneousOmegaReductFunctor_comp d.unop c.unop)

end CategorialAlgebras.ChangeOfSignature
