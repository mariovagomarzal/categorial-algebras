import CategorialAlgebras.Omega.DimensionRetractions
import CategorialAlgebras.Dimensions.HeterogeneousCounitStructure

/-!
# The heterogeneous counit

Clamping and reinserting a dimension gives an endomap below identity. Its
identity inclusions realize the counit of discretization and truncation.
-/

universe u v w

namespace CategorialAlgebras.Omega

open CategoryTheory Presentations Dimensions
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Type u} {sig : Signature.{u, v} S} (m : ℕ)

/-- Clamp a dimension and include it again in the original dimension type. -/
def counitDimension : ℕ →o ℕ :=
  (omegaInclusion (m+1)).toOrderHom.comp (omegaClamp m)

/-- The reinserted clamping map is saturating. -/
theorem counitDimension_saturating : Saturating (counitDimension m) := by
  intro i j k hij hjk he
  have hv := he
  change min i m = min j m at hv
  change min j m = min k m
  have hi : i < j := hij
  have hj : j < k := hjk
  omega

/-- Reinserted clamping lies below the identity dimension map. -/
theorem counitDimension_le (k : ℕ) : counitDimension m k ≤ k :=
  show min k m ≤ k from min_le_left _ _

/-- The lower dimension of a strict pair is retained unless both images coincide. -/
theorem counitDimension_shape (j k : ℕ) (hjk : j < k) :
    counitDimension m j = counitDimension m k ∨ counitDimension m j = j := by
  by_cases hj : j ≤ m
  · right
    exact min_eq_left hj
  · left
    change min j m = min k m
    have hh : j < k := hjk
    omega

/-- The counit dimension map is exactly the composite underlying generalized derivor. -/
theorem heterogeneousCounit_derivor :
    (heterogeneousOmegaDiscretization sig m).comp (heterogeneousOmegaTruncation sig m) =
      heterogeneousDimension sig (counitDimension m) :=
  heterogeneousDimension_compose sig (omegaClamp m) (omegaInclusion (m+1)).toOrderHom

/-- Recover the heterogeneous categorial algebra of a model on its exact carriers. -/
noncomputable def recoveredHeterogeneousAlgebra
    (B : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol ℕ sig))
    (hB : (Heterogeneous.specification ℕ sig).IsModel B) :
    Heterogeneous.OmegaCategorialAlgebra sig :=
  Heterogeneous.ofEquations B (fun e => hB.2 _ ⟨e, rfl⟩)

/-- The explicit counit source realizes the successive induced transformations. -/
noncomputable def heterogeneousCounitRealization
    (B : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol ℕ sig))
    (hB : (Heterogeneous.specification ℕ sig).IsModel B) :
    (reindexedAlgebra (recoveredHeterogeneousAlgebra B hB)
      (counitDimension m) (counitDimension_saturating m)).toPartialAlgebra ≅
      (heterogeneousOmegaDiscretization sig m).transformed ((heterogeneousOmegaTruncation sig m).transformed B) :=
  let C := recoveredHeterogeneousAlgebra B hB
  let hc : C.toPartialAlgebra = B := Heterogeneous.toPartialAlgebra_ofEquations B _
  let hC : (Heterogeneous.specification ℕ sig).IsModel C.toPartialAlgebra := hc.symm ▸ hB
  heterogeneousDimensionRealization sig (counitDimension m) (counitDimension_saturating m) C ≪≫
    eqToIso (congrArg (fun c => GeneralizedHepDerivor.transformed c C.toPartialAlgebra)
      (heterogeneousCounit_derivor (sig := sig) m).symm) ≪≫
    ((heterogeneousOmegaDiscretization sig m).comparisonIso (heterogeneousOmegaTruncation sig m) C.toPartialAlgebra
      ((heterogeneousOmegaDiscretization sig m).comparison_surjective_of_empty
        (heterogeneousOmegaTruncation sig m) C.toPartialAlgebra (fun _ => rfl))
      (heterogeneousOmegaDiscretization_isModel sig m _ (heterogeneousOmegaTruncation_isModel sig m _ hC)).1).symm ≪≫
    ((heterogeneousOmegaTruncation sig m).transformedFunctor ⋙ (heterogeneousOmegaDiscretization sig m).transformedFunctor).mapIso
      (eqToIso hc)

/-- The heterogeneous counit realization retains the underlying cell. -/
theorem heterogeneousCounitRealization_hom_val
    (B : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol ℕ sig))
    (hB : (Heterogeneous.specification ℕ sig).IsModel B) (p : ℕ × S)
    (x : (recoveredHeterogeneousAlgebra B hB).carrier (counitDimension m p.1, p.2)) :
    (((heterogeneousCounitRealization m B hB).hom.toMap p x).val).val = x := by
  let C := recoveredHeterogeneousAlgebra B hB
  let hc : C.toPartialAlgebra = B := Heterogeneous.toPartialAlgebra_ofEquations B _
  let hC : (Heterogeneous.specification ℕ sig).IsModel C.toPartialAlgebra := hc.symm ▸ hB
  let z := (eqToHom (congrArg (fun c => GeneralizedHepDerivor.transformed c C.toPartialAlgebra)
    (heterogeneousCounit_derivor (sig := sig) m).symm)).toMap p
      ((heterogeneousDimensionRealization sig (counitDimension m)
        (counitDimension_saturating m) C).hom.toMap p x)
  let hs := (heterogeneousOmegaDiscretization sig m).comparison_surjective_of_empty
    (heterogeneousOmegaTruncation sig m) C.toPartialAlgebra (fun _ => rfl)
  have hA : (Heterogeneous.hepSignature (ℕ) sig).IsEPAlgebra
      ((heterogeneousOmegaDiscretization sig m).transformed
        ((heterogeneousOmegaTruncation sig m).transformed C.toPartialAlgebra)) :=
    (heterogeneousOmegaDiscretization_isModel sig m _ (heterogeneousOmegaTruncation_isModel sig m _ hC)).1
  change (eqToHom hc).toMap _ (((((heterogeneousOmegaDiscretization sig m).comparisonIso
    (heterogeneousOmegaTruncation sig m) C.toPartialAlgebra hs hA).inv.toMap p z).val).val) = x
  erw [partial_eqToHom_toMap, cast_eq]
  exact ((heterogeneousOmegaDiscretization sig m).comparisonIso_inv_val
    (heterogeneousOmegaTruncation sig m) C.toPartialAlgebra hs hA p z).trans
    (eq_of_heq (transformed_transport_val (heterogeneousCounit_derivor (sig := sig) m).symm
      C.toPartialAlgebra p
      ((heterogeneousDimensionRealization sig (counitDimension m)
        (counitDimension_saturating m) C).hom.toMap p x) _))

/-- The inverse heterogeneous realization removes the two cell proofs. -/
theorem heterogeneousCounitRealization_inv_val
    (B : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol ℕ sig))
    (hB : (Heterogeneous.specification ℕ sig).IsModel B) (p : ℕ × S)
    (x : (heterogeneousOmegaDiscretization sig m).Cell ((heterogeneousOmegaTruncation sig m).transformed B) p) :
    (heterogeneousCounitRealization m B hB).inv.toMap p x = x.val.val := by
  have hv := heterogeneousCounitRealization_hom_val m B hB p
    ((heterogeneousCounitRealization m B hB).inv.toMap p x)
  exact hv.symm.trans (congrArg (fun f : _ ⟶ _ => (f.toMap p x).val.val)
    (heterogeneousCounitRealization m B hB).inv_hom_id)

/-- The heterogeneous counit on partial algebras underlying a model. -/
noncomputable def heterogeneousCounitPartial
    (B : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol ℕ sig))
    (hB : (Heterogeneous.specification ℕ sig).IsModel B) :
    (heterogeneousOmegaDiscretization sig m).transformed ((heterogeneousOmegaTruncation sig m).transformed B) ⟶ B :=
  (heterogeneousCounitRealization m B hB).inv ≫
    (reindexedCounitHom (recoveredHeterogeneousAlgebra B hB) (counitDimension m)
      (counitDimension_saturating m) (counitDimension_le m) (counitDimension_shape m)).toPartialHom ≫
        eqToHom (Heterogeneous.toPartialAlgebra_ofEquations B _)

/-- The heterogeneous counit uses the identity from the clamped dimension into the original one. -/
theorem heterogeneousCounitPartial_val
    (B : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol ℕ sig))
    (hB : (Heterogeneous.specification ℕ sig).IsModel B) (k : ℕ) (s : S)
    (x : (heterogeneousOmegaDiscretization sig m).Cell ((heterogeneousOmegaTruncation sig m).transformed B) (k, s)) :
    (heterogeneousCounitPartial m B hB).toMap (k, s) x =
      (dimensionLE ((recoveredHeterogeneousAlgebra B hB).sort s).str
        (counitDimension_le m k)).identity x.val.val := by
  change (eqToHom (Heterogeneous.toPartialAlgebra_ofEquations B _)).toMap (k, s) _ = _
  erw [partial_eqToHom_toMap, cast_eq]
  change (dimensionLE ((recoveredHeterogeneousAlgebra B hB).sort s).str
    (counitDimension_le m k)).identity ((heterogeneousCounitRealization m B hB).inv.toMap (k, s) x) = _
  rw [heterogeneousCounitRealization_inv_val]

/-- Homomorphisms of models preserve recovered weak-pair identities. -/
theorem recovered_identity_natural
    {B C : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol ℕ sig)}
    (f : B ⟶ C) (hB : (Heterogeneous.specification ℕ sig).IsModel B)
    (hC : (Heterogeneous.specification ℕ sig).IsModel C)
    {j k : ℕ} (hjk : j ≤ k) (s : S) (x : B.carrier (j, s)) :
    f.toMap (k, s) ((dimensionLE ((recoveredHeterogeneousAlgebra B hB).sort s).str hjk).identity x) =
      (dimensionLE ((recoveredHeterogeneousAlgebra C hC).sort s).str hjk).identity (f.toMap (j, s) x) := by
  rcases hjk.lt_or_eq with hj | rfl
  · erw [dimensionLE_of_lt _ _ hj, dimensionLE_of_lt _ _ hj]
    have hx : (((recoveredHeterogeneousAlgebra B hB).sort s).str.dim j k hj).identity x ∈
        B.op (.identity hj s) (Heterogeneous.single x) := by
      erw [Heterogeneous.identity_op (fun e => hB.2 _ ⟨e, rfl⟩)]
      exact Part.mem_some _
    have hh := f.map_op (.identity hj s) (Heterogeneous.single x) hx
    erw [Heterogeneous.identity_op (fun e => hC.2 _ ⟨e, rfl⟩)] at hh
    exact Part.mem_some_iff.mp hh
  · rw [dimensionLE_self, dimensionLE_self]
    rfl

/-- The heterogeneous identity inclusions are natural on models. -/
noncomputable def heterogeneousCounit : heterogeneousOmegaTruncationModels.{u, v, w} sig m ⋙
    heterogeneousOmegaDiscretizationModels sig m ⟶ 𝟭 _ where
  app B := ObjectProperty.homMk (ObjectProperty.homMk
    (heterogeneousCounitPartial m B.obj.obj ⟨B.obj.property, B.property⟩))
  naturality {B C} f := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply PartialAlgebra.Hom.ext
    funext p x
    rcases p with ⟨k, s⟩
    change (heterogeneousCounitPartial m C.obj.obj _).toMap (k, s) _ =
      f.hom.hom.toMap (k, s) ((heterogeneousCounitPartial m B.obj.obj _).toMap (k, s) x)
    erw [heterogeneousCounitPartial_val, heterogeneousCounitPartial_val]
    exact (recovered_identity_natural f.hom.hom ⟨B.obj.property, B.property⟩
      ⟨C.obj.property, C.property⟩ (counitDimension_le m k) s x.val.val).symm


/-- Below the cutoff the heterogeneous counit is identity, up to sort transport. -/
theorem heterogeneousCounitPartial_low
    (B : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol ℕ sig))
    (hB : (Heterogeneous.specification ℕ sig).IsModel B)
    (k : ℕ) (hk : k ≤ m) (s : S)
    (x : (heterogeneousOmegaDiscretization sig m).Cell ((heterogeneousOmegaTruncation sig m).transformed B) (k, s)) :
    HEq ((heterogeneousCounitPartial m B hB).toMap (k, s) x) x.val.val := by
  rw [heterogeneousCounitPartial_val]
  exact dimensionLE_identity_heq _ _ (min_eq_left hk) _

/-- Above the cutoff the clamped source dimension is exactly $m$. -/
theorem counitDimension_high (k : ℕ) (hk : m < k) :
    counitDimension m k = m := min_eq_right hk.le

/-- Above the cutoff the counit is the original identity from dimension $m$ to $k$. -/
theorem heterogeneousCounitPartial_high
    (B : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol ℕ sig))
    (hB : (Heterogeneous.specification ℕ sig).IsModel B)
    (k : ℕ) (hk : m < k) (s : S)
    (x : (heterogeneousOmegaDiscretization sig m).Cell ((heterogeneousOmegaTruncation sig m).transformed B) (k, s)) :
    (heterogeneousCounitPartial m B hB).toMap (k, s) x =
      (((recoveredHeterogeneousAlgebra B hB).sort s).str.dim (counitDimension m k) k
        (show counitDimension m k < k from
          (show min k m < k from lt_of_le_of_lt (min_le_right _ _) hk))).identity x.val.val := by
  rw [heterogeneousCounitPartial_val]
  erw [dimensionLE_of_lt _ _ (show counitDimension m k < k from
          (show min k m < k from lt_of_le_of_lt (min_le_right _ _) hk))]

/-- Identities between dimensions collapsed by discretization retain their underlying value. -/
theorem heterogeneousDiscretization_identity_val
    (B : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol (Fin (m + 1)) sig))
    (hB : (Heterogeneous.specification (Fin (m + 1)) sig).IsModel B)
    {j k : ℕ} (hjk : j ≤ k) (he : omegaClamp m j = omegaClamp m k)
    (s : S) (x : (heterogeneousOmegaDiscretization sig m).Cell B (j, s)) :
    HEq (((dimensionLE ((recoveredHeterogeneousAlgebra
      ((heterogeneousOmegaDiscretization sig m).transformed B)
      (heterogeneousOmegaDiscretization_isModel sig m B hB)).sort s).str hjk).identity x).val) x.val := by
  rcases hjk.lt_or_eq with hj | rfl
  · erw [dimensionLE_of_lt _ _ hj]
    let hA := heterogeneousOmegaDiscretization_isModel sig m B hB
    let C := recoveredHeterogeneousAlgebra ((heterogeneousOmegaDiscretization sig m).transformed B) hA
    let q := ((C.sort s).str.dim j k hj).identity x
    have hq : q ∈ ((heterogeneousOmegaDiscretization sig m).transformed B).op
        (.identity hj s) (Heterogeneous.single x) := by
      erw [Heterogeneous.identity_op (fun e => hA.2 _ ⟨e, rfl⟩)]
      exact Part.mem_some _
    have hv := ((heterogeneousOmegaDiscretization sig m).mem_transformed_op B _ _ _).mp hq |>.2
    change q.val ∈ Term.partialEval (A := B)
      (Word.valuation (φ := dimensionSortMap (omegaClamp m))
        (fun t => (Heterogeneous.single x t).val))
      ((heterogeneousDimensionDerivor sig (omegaClamp m)).image (.identity hj s)) at hv
    rw [heterogeneousDimensionDerivor_identity] at hv
    have hn : ¬ omegaClamp m j < omegaClamp m k := by rw [he]; exact lt_irrefl _
    erw [dite_eq_right hn, Term.partialEval_var] at hv
    exact (heq_of_eq (Part.mem_some_iff.mp hv)).trans
      (valuation_heq (φ := dimensionSortMap (omegaClamp m)) (A := B.carrier)
        (fun t => (Heterogeneous.single x t).val) (s := (omegaClamp m k, s))
        ⟨0, Prod.ext he rfl⟩)
  · rw [dimensionLE_self]
    rfl

/-- Clamping a reinserted clamped dimension has no further effect. -/
theorem omegaClamp_counitDimension (k : ℕ) :
    omegaClamp m (counitDimension m k) = omegaClamp m k := by
  apply Fin.ext
  exact min_eq_left (min_le_right k m)

end CategorialAlgebras.Omega
