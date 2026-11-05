import CategorialAlgebras.Dimensions.GraduationCompatibility
import CategorialAlgebras.Dimensions.Adjunctions
import CategorialAlgebras.Presentations.Equivalence
import CategorialAlgebras.Preliminaries.AlgebraicSquare

/-!
# Truncation and unification

The conjugate of the graduation-discretization comparison identifies truncation
followed by unification with unification followed by truncation. Its components
are the identities from the retained dimension to the top dimension.
-/

universe u v w

namespace CategorialAlgebras.Dimensions

open CategoryTheory Presentations

set_option backward.isDefEq.respectTransparency false

variable {S : Type u} (sig : Signature.{u, v} S) {m n : ℕ} (h : m ≤ n)

/-- The right comparison on models, conjugate to the graduation-discretization comparison. -/
noncomputable def truncationUnificationModels :
    heterogeneousTruncationModels.{u, v, w} sig h ⋙ unificationModels m sig ≅
      unificationModels n sig ⋙ homogeneousTruncationModels sig h :=
  AlgebraicSquare.conjugateIso (modelPresentationAdjunction m sig)
    (modelPresentationAdjunction n sig) (homogeneousModelAdjunction sig h)
    (heterogeneousModelAdjunction sig h) (discretizationGraduationModels sig h)

/-- Equal source dimensions and equal inputs give the same identity inclusion. -/
theorem dimensionLE_identity_input_eq {I : Type*} [LinearOrder I] {A : I → Type*}
    (C : Heterogeneous.Structure I A) {j j' k : I} (hjk : j ≤ k) (hj'k : j' ≤ k)
    (hj : j = j') (x : A j) (y : A j') (he : HEq x y) :
    (dimensionLE C hjk).identity x = (dimensionLE C hj'k).identity y := by
  cases hj
  cases eq_of_heq he
  rfl

/-- At a dimension equal to the top, the presentation counit retains the underlying truncated cell. -/
theorem theta_truncation_top_val_heq
    (B : (Heterogeneous.specification (Fin (n + 1)) sig).Models)
    (k : Fin (m + 1)) (hk : k = Fin.last m) (s : S)
    (z : (graduation m sig).Cell ((unification m sig).transformed
      ((heterogeneousTruncation sig h).transformed B.obj.obj)) (k, s)) :
    HEq (((thetaPartial m sig ((heterogeneousTruncation sig h).transformed B.obj.obj)
      (heterogeneousTruncation_isModel sig h B.obj.obj ⟨B.obj.property, B.property⟩)).inv.toMap (k, s) z).val)
      z.val.val.val := by
  subst k
  rw [thetaPartial_inv_val, topSource_last]
  rfl

/-- The component of the right comparison is the identity from dimension $m$ to $n$. -/
theorem truncationUnificationModels_hom_val
    (B : (Heterogeneous.specification (Fin (n + 1)) sig).Models) (s : S)
    (x : ((heterogeneousTruncationModels sig h ⋙ unificationModels m sig).obj B).obj.obj.carrier s) :
    ((((truncationUnificationModels sig h).hom.app B).hom.hom.toMap s x).val).val =
      (dimensionLE ((recoveredHeterogeneousAlgebra B.obj.obj ⟨B.obj.property, B.property⟩).sort s).str
        (show cellInclusion h (Fin.last m) ≤ Fin.last n from h)).identity x.val.val := by
  unfold truncationUnificationModels
  rw [AlgebraicSquare.conjugateIso_hom_app]
  simp only [Adjunction.comp_unit_app, Adjunction.comp_counit_app, Functor.comp_map,
    Functor.map_comp]
  let X := (heterogeneousTruncationModels sig h ⋙ unificationModels m sig).obj B
  let u := ((homogeneousModelAdjunction sig h).unit.app X).hom.hom.toMap s x
  let v := ((modelPresentationAdjunction n sig).unit.app
    ((homogeneousDiscretizationModels sig h).obj X)).hom.hom.toMap s u.val
  let z := ((discretizationGraduationModels sig h).hom.app X).hom.hom.toMap (Fin.last n, s) v.val
  let r := ((heterogeneousDiscretizationModels sig h).map
    ((modelPresentationAdjunction m sig).counit.app
      ((heterogeneousTruncationModels sig h).obj B))).hom.hom.toMap (Fin.last n, s) z
  change (heterogeneousCounitPartial h B.obj.obj ⟨B.obj.property, B.property⟩).toMap (Fin.last n, s) r = _
  rw [heterogeneousCounitPartial_val]
  apply dimensionLE_identity_input_eq _ _ _ (Fin.ext (min_eq_right h))
  have ht := theta_truncation_top_val_heq sig h B (clampDimension m (Fin.last n))
    (Fin.ext (min_eq_right h)) s z.val
  change HEq r.val.val _ at ht
  apply ht.trans
  apply heq_of_eq
  have hz := discretizationGraduationModels_hom_val sig h X (Fin.last n, s) v.val
  have hv := modelPresentationAdjunction_unit_val n sig ((homogeneousDiscretizationModels sig h).obj X) s u.val
  have hu := homogeneousModelAdjunction_unit_val sig h X s x
  change z.val.val = v.val.val.val at hz
  change v.val.val = u.val at hv
  change u.val.val = x at hu
  exact congrArg (fun q => q.val.val) (hz.trans (congrArg Subtype.val hv |>.trans hu))

/-- On an expanded categorial algebra, the component is its original identity inclusion. -/
theorem truncationUnificationModels_hom_val_expansion
    (B : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig) (s : S)
    (x : ((heterogeneousTruncationModels sig h ⋙ unificationModels m sig).obj B.toModel).obj.obj.carrier s) :
    ((((truncationUnificationModels sig h).hom.app B.toModel).hom.hom.toMap s x).val).val =
      (dimensionLE (B.sort s).str
        (show cellInclusion h (Fin.last m) ≤ Fin.last n from h)).identity x.val.val :=
  truncationUnificationModels_hom_val sig h B.toModel s x

/-- For a proper truncation the right comparison is the original $(n,m)$-identity. -/
theorem truncationUnificationModels_hom_val_of_lt {m n : ℕ} (h : m < n)
    (B : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig) (s : S)
    (x : ((heterogeneousTruncationModels sig h.le ⋙ unificationModels m sig).obj B.toModel).obj.obj.carrier s) :
    ((((truncationUnificationModels sig h.le).hom.app B.toModel).hom.hom.toMap s x).val).val =
      ((B.sort s).str.dim (cellInclusion h.le (Fin.last m)) (Fin.last n)
        (show cellInclusion h.le (Fin.last m) < Fin.last n from h)).identity x.val.val := by
  rw [truncationUnificationModels_hom_val_expansion, dimensionLE_of_lt _ _ (show
    cellInclusion h.le (Fin.last m) < Fin.last n from h)]

/-- In equal dimensions the right comparison retains every underlying element. -/
theorem truncationUnificationModels_self_val (n : ℕ)
    (B : (Heterogeneous.specification (Fin (n + 1)) sig).Models) (s : S)
    (x : ((heterogeneousTruncationModels sig (le_refl n) ⋙ unificationModels n sig).obj B).obj.obj.carrier s) :
    ((((truncationUnificationModels sig (le_refl n)).hom.app B).hom.hom.toMap s x).val).val = x.val.val := by
  rw [truncationUnificationModels_hom_val]
  change (dimensionLE ((recoveredHeterogeneousAlgebra B.obj.obj ⟨B.obj.property, B.property⟩).sort s).str
    (le_refl (Fin.last n))).identity x.val.val = _
  rw [dimensionLE_self]
  rfl

/-- The right comparison is exactly the conjugate of the specified left comparison on models. -/
theorem truncationUnificationModels_eq_conjugate :
    truncationUnificationModels.{u, v, w} sig h =
      AlgebraicSquare.conjugateIso (modelPresentationAdjunction m sig)
        (modelPresentationAdjunction n sig) (homogeneousModelAdjunction sig h)
        (heterogeneousModelAdjunction sig h) (discretizationGraduationModels sig h) := rfl

/-- The right comparison transported to the existing functors on categorial algebras. -/
noncomputable def truncationUnificationFunctor :
    heterogeneousTruncationFunctor.{u, v, w} sig h ⋙ unificationFunctor m sig ≅
      unificationFunctor n sig ⋙ homogeneousTruncationFunctor sig h :=
  conjugateSquareIso Heterogeneous.modelIsomorphism Heterogeneous.modelIsomorphism
    Homogeneous.modelIsomorphism Homogeneous.modelIsomorphism (truncationUnificationModels sig h)

end CategorialAlgebras.Dimensions
