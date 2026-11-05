import CategorialAlgebras.Dimensions.Relation
import CategorialAlgebras.Dimensions.HeterogeneousCounitStructure

/-!
# The heterogeneous counit

Clamping and reinserting a dimension gives an endomap below identity. Its
identity inclusions realize the counit of discretization and truncation.
-/

universe u v w

namespace CategorialAlgebras.Dimensions

open CategoryTheory Presentations

variable {S : Type u} {sig : Signature.{u, v} S} {m n : ℕ} (h : m ≤ n)

/-- Clamp a dimension and include it again in the original dimension type. -/
def counitDimension : Fin (n + 1) →o Fin (n + 1) :=
  (cellInclusion h).toOrderHom.comp (clampDimension m)

/-- The reinserted clamping map is saturating. -/
theorem counitDimension_saturating : Saturating (counitDimension h) := by
  intro i j k hij hjk he
  apply Fin.ext
  have hv := congrArg Fin.val he
  change min i.val m = min j.val m at hv
  change min j.val m = min k.val m
  have hi : i.val < j.val := hij
  have hj : j.val < k.val := hjk
  omega

/-- Reinserted clamping lies below the identity dimension map. -/
theorem counitDimension_le (k : Fin (n + 1)) : counitDimension h k ≤ k :=
  show min k.val m ≤ k.val from min_le_left _ _

/-- The lower dimension of a strict pair is retained unless both images coincide. -/
theorem counitDimension_shape (j k : Fin (n + 1)) (hjk : j < k) :
    counitDimension h j = counitDimension h k ∨ counitDimension h j = j := by
  by_cases hj : j.val ≤ m
  · right
    apply Fin.ext
    exact min_eq_left hj
  · left
    apply Fin.ext
    change min j.val m = min k.val m
    have hh : j.val < k.val := hjk
    omega

/-- The counit dimension map is exactly the composite underlying generalized derivor. -/
theorem heterogeneousCounit_derivor :
    (heterogeneousDiscretization sig h).comp (heterogeneousTruncation sig h) =
      heterogeneousDimension sig (counitDimension h) :=
  heterogeneousDimension_compose sig (clampDimension m) (cellInclusion h).toOrderHom

/-- Recover the heterogeneous categorial algebra of a model on its exact carriers. -/
noncomputable def recoveredHeterogeneousAlgebra
    (B : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol (Fin (n + 1)) sig))
    (hB : (Heterogeneous.specification (Fin (n + 1)) sig).IsModel B) :
    Heterogeneous.NCategorialAlgebra n sig :=
  Heterogeneous.ofEquations B (fun e => hB.2 _ ⟨e, rfl⟩)

/-- The explicit counit source realizes the successive induced transformations. -/
noncomputable def heterogeneousCounitRealization
    (B : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol (Fin (n + 1)) sig))
    (hB : (Heterogeneous.specification (Fin (n + 1)) sig).IsModel B) :
    (reindexedAlgebra (recoveredHeterogeneousAlgebra B hB)
      (counitDimension h) (counitDimension_saturating h)).toPartialAlgebra ≅
      (heterogeneousDiscretization sig h).transformed ((heterogeneousTruncation sig h).transformed B) :=
  let C := recoveredHeterogeneousAlgebra B hB
  let hc : C.toPartialAlgebra = B := Heterogeneous.toPartialAlgebra_ofEquations B _
  let hC : (Heterogeneous.specification (Fin (n + 1)) sig).IsModel C.toPartialAlgebra := hc.symm ▸ hB
  heterogeneousDimensionRealization sig (counitDimension h) (counitDimension_saturating h) C ≪≫
    eqToIso (congrArg (fun c => GeneralizedHepDerivor.transformed c C.toPartialAlgebra)
      (heterogeneousCounit_derivor (sig := sig) h).symm) ≪≫
    ((heterogeneousDiscretization sig h).comparisonIso (heterogeneousTruncation sig h) C.toPartialAlgebra
      ((heterogeneousDiscretization sig h).comparison_surjective_of_empty
        (heterogeneousTruncation sig h) C.toPartialAlgebra (fun _ => rfl))
      (heterogeneousDiscretization_isModel sig h _ (heterogeneousTruncation_isModel sig h _ hC)).1).symm ≪≫
    (heterogeneousTruncationPartialFunctor sig h ⋙ heterogeneousDiscretizationPartialFunctor sig h).mapIso
      (eqToIso hc)

/-- The heterogeneous counit realization retains the underlying cell. -/
theorem heterogeneousCounitRealization_hom_val
    (B : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol (Fin (n + 1)) sig))
    (hB : (Heterogeneous.specification (Fin (n + 1)) sig).IsModel B) (p : Fin (n + 1) × S)
    (x : (recoveredHeterogeneousAlgebra B hB).carrier (counitDimension h p.1, p.2)) :
    (((heterogeneousCounitRealization h B hB).hom.toMap p x).val).val = x := by
  let C := recoveredHeterogeneousAlgebra B hB
  let hc : C.toPartialAlgebra = B := Heterogeneous.toPartialAlgebra_ofEquations B _
  let hC : (Heterogeneous.specification (Fin (n + 1)) sig).IsModel C.toPartialAlgebra := hc.symm ▸ hB
  let z := (eqToHom (congrArg (fun c => GeneralizedHepDerivor.transformed c C.toPartialAlgebra)
    (heterogeneousCounit_derivor (sig := sig) h).symm)).toMap p
      ((heterogeneousDimensionRealization sig (counitDimension h)
        (counitDimension_saturating h) C).hom.toMap p x)
  let hs := (heterogeneousDiscretization sig h).comparison_surjective_of_empty
    (heterogeneousTruncation sig h) C.toPartialAlgebra (fun _ => rfl)
  have hA : (Heterogeneous.hepSignature (Fin (n + 1)) sig).IsEPAlgebra
      ((heterogeneousDiscretization sig h).transformed
        ((heterogeneousTruncation sig h).transformed C.toPartialAlgebra)) :=
    (heterogeneousDiscretization_isModel sig h _ (heterogeneousTruncation_isModel sig h _ hC)).1
  change (eqToHom hc).toMap _ (((((heterogeneousDiscretization sig h).comparisonIso
    (heterogeneousTruncation sig h) C.toPartialAlgebra hs hA).inv.toMap p z).val).val) = x
  erw [partial_eqToHom_toMap, cast_eq]
  exact ((heterogeneousDiscretization sig h).comparisonIso_inv_val
    (heterogeneousTruncation sig h) C.toPartialAlgebra hs hA p z).trans
    (eq_of_heq (transformed_transport_val (heterogeneousCounit_derivor (sig := sig) h).symm
      C.toPartialAlgebra p
      ((heterogeneousDimensionRealization sig (counitDimension h)
        (counitDimension_saturating h) C).hom.toMap p x) _))

/-- The inverse heterogeneous realization removes the two cell proofs. -/
theorem heterogeneousCounitRealization_inv_val
    (B : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol (Fin (n + 1)) sig))
    (hB : (Heterogeneous.specification (Fin (n + 1)) sig).IsModel B) (p : Fin (n + 1) × S)
    (x : (heterogeneousDiscretization sig h).Cell ((heterogeneousTruncation sig h).transformed B) p) :
    (heterogeneousCounitRealization h B hB).inv.toMap p x = x.val.val := by
  have hv := heterogeneousCounitRealization_hom_val h B hB p
    ((heterogeneousCounitRealization h B hB).inv.toMap p x)
  exact hv.symm.trans (congrArg (fun f : _ ⟶ _ => (f.toMap p x).val.val)
    (heterogeneousCounitRealization h B hB).inv_hom_id)

/-- The heterogeneous counit on partial algebras underlying a model. -/
noncomputable def heterogeneousCounitPartial
    (B : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol (Fin (n + 1)) sig))
    (hB : (Heterogeneous.specification (Fin (n + 1)) sig).IsModel B) :
    (heterogeneousDiscretization sig h).transformed ((heterogeneousTruncation sig h).transformed B) ⟶ B :=
  (heterogeneousCounitRealization h B hB).inv ≫
    (reindexedCounitHom (recoveredHeterogeneousAlgebra B hB) (counitDimension h)
      (counitDimension_saturating h) (counitDimension_le h) (counitDimension_shape h)).toPartialHom ≫
        eqToHom (Heterogeneous.toPartialAlgebra_ofEquations B _)

/-- The heterogeneous counit uses the identity from the clamped dimension into the original one. -/
theorem heterogeneousCounitPartial_val
    (B : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol (Fin (n + 1)) sig))
    (hB : (Heterogeneous.specification (Fin (n + 1)) sig).IsModel B) (k : Fin (n + 1)) (s : S)
    (x : (heterogeneousDiscretization sig h).Cell ((heterogeneousTruncation sig h).transformed B) (k, s)) :
    (heterogeneousCounitPartial h B hB).toMap (k, s) x =
      (dimensionLE ((recoveredHeterogeneousAlgebra B hB).sort s).str
        (counitDimension_le h k)).identity x.val.val := by
  change (eqToHom (Heterogeneous.toPartialAlgebra_ofEquations B _)).toMap (k, s) _ = _
  erw [partial_eqToHom_toMap, cast_eq]
  change (dimensionLE ((recoveredHeterogeneousAlgebra B hB).sort s).str
    (counitDimension_le h k)).identity ((heterogeneousCounitRealization h B hB).inv.toMap (k, s) x) = _
  rw [heterogeneousCounitRealization_inv_val]

/-- Homomorphisms of models preserve recovered weak-pair identities. -/
theorem recovered_identity_natural
    {B C : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol (Fin (n + 1)) sig)}
    (f : B ⟶ C) (hB : (Heterogeneous.specification (Fin (n + 1)) sig).IsModel B)
    (hC : (Heterogeneous.specification (Fin (n + 1)) sig).IsModel C)
    {j k : Fin (n + 1)} (hjk : j ≤ k) (s : S) (x : B.carrier (j, s)) :
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
noncomputable def heterogeneousCounit : heterogeneousTruncationModels.{u, v, w} sig h ⋙
    heterogeneousDiscretizationModels sig h ⟶ 𝟭 _ where
  app B := ObjectProperty.homMk (ObjectProperty.homMk
    (heterogeneousCounitPartial h B.obj.obj ⟨B.obj.property, B.property⟩))
  naturality {B C} f := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply PartialAlgebra.Hom.ext
    funext p x
    rcases p with ⟨k, s⟩
    change (heterogeneousCounitPartial h C.obj.obj _).toMap (k, s) _ =
      f.hom.hom.toMap (k, s) ((heterogeneousCounitPartial h B.obj.obj _).toMap (k, s) x)
    erw [heterogeneousCounitPartial_val, heterogeneousCounitPartial_val]
    exact (recovered_identity_natural f.hom.hom ⟨B.obj.property, B.property⟩
      ⟨C.obj.property, C.property⟩ (counitDimension_le h k) s x.val.val).symm


/-- Below the cutoff the heterogeneous counit is identity, up to sort transport. -/
theorem heterogeneousCounitPartial_low
    (B : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol (Fin (n + 1)) sig))
    (hB : (Heterogeneous.specification (Fin (n + 1)) sig).IsModel B)
    (k : Fin (n + 1)) (hk : k.val ≤ m) (s : S)
    (x : (heterogeneousDiscretization sig h).Cell ((heterogeneousTruncation sig h).transformed B) (k, s)) :
    HEq ((heterogeneousCounitPartial h B hB).toMap (k, s) x) x.val.val := by
  rw [heterogeneousCounitPartial_val]
  exact dimensionLE_identity_heq _ _ (Fin.ext (min_eq_left hk)) _

/-- Above the cutoff the clamped source dimension is exactly $m$. -/
theorem counitDimension_high (k : Fin (n + 1)) (hk : m < k.val) :
    (counitDimension h k).val = m := min_eq_right hk.le

/-- Above the cutoff the counit is the original identity from dimension $m$ to $k$. -/
theorem heterogeneousCounitPartial_high
    (B : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol (Fin (n + 1)) sig))
    (hB : (Heterogeneous.specification (Fin (n + 1)) sig).IsModel B)
    (k : Fin (n + 1)) (hk : m < k.val) (s : S)
    (x : (heterogeneousDiscretization sig h).Cell ((heterogeneousTruncation sig h).transformed B) (k, s)) :
    (heterogeneousCounitPartial h B hB).toMap (k, s) x =
      (((recoveredHeterogeneousAlgebra B hB).sort s).str.dim (counitDimension h k) k
        (show counitDimension h k < k from
          (show min k.val m < k.val from lt_of_le_of_lt (min_le_right _ _) hk))).identity x.val.val := by
  rw [heterogeneousCounitPartial_val]
  erw [dimensionLE_of_lt _ _ (show counitDimension h k < k from
          (show min k.val m < k.val from lt_of_le_of_lt (min_le_right _ _) hk))]

/-- Identities between dimensions collapsed by discretization retain their underlying value. -/
theorem heterogeneousDiscretization_identity_val
    (B : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol (Fin (m + 1)) sig))
    (hB : (Heterogeneous.specification (Fin (m + 1)) sig).IsModel B)
    {j k : Fin (n + 1)} (hjk : j ≤ k) (he : clampDimension m j = clampDimension m k)
    (s : S) (x : (heterogeneousDiscretization sig h).Cell B (j, s)) :
    HEq (((dimensionLE ((recoveredHeterogeneousAlgebra
      ((heterogeneousDiscretization sig h).transformed B)
      (heterogeneousDiscretization_isModel sig h B hB)).sort s).str hjk).identity x).val) x.val := by
  rcases hjk.lt_or_eq with hj | rfl
  · erw [dimensionLE_of_lt _ _ hj]
    let hA := heterogeneousDiscretization_isModel sig h B hB
    let C := recoveredHeterogeneousAlgebra ((heterogeneousDiscretization sig h).transformed B) hA
    let q := ((C.sort s).str.dim j k hj).identity x
    have hq : q ∈ ((heterogeneousDiscretization sig h).transformed B).op
        (.identity hj s) (Heterogeneous.single x) := by
      erw [Heterogeneous.identity_op (fun e => hA.2 _ ⟨e, rfl⟩)]
      exact Part.mem_some _
    have hv := ((heterogeneousDiscretization sig h).mem_transformed_op B _ _ _).mp hq |>.2
    change q.val ∈ Term.partialEval (A := B)
      (Word.valuation (φ := dimensionSortMap (clampDimension m))
        (fun t => (Heterogeneous.single x t).val))
      ((heterogeneousDimensionDerivor sig (clampDimension m)).image (.identity hj s)) at hv
    rw [heterogeneousDimensionDerivor_identity] at hv
    have hn : ¬ clampDimension m j < clampDimension m k := by rw [he]; exact lt_irrefl _
    erw [dite_eq_right hn, Term.partialEval_var] at hv
    exact (heq_of_eq (Part.mem_some_iff.mp hv)).trans
      (valuation_heq (φ := dimensionSortMap (clampDimension m)) (A := B.carrier)
        (fun t => (Heterogeneous.single x t).val) (s := (clampDimension m k, s))
        ⟨0, Prod.ext he rfl⟩)
  · rw [dimensionLE_self]
    rfl

end CategorialAlgebras.Dimensions
