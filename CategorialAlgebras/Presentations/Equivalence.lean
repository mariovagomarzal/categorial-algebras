import CategorialAlgebras.Presentations.Relation
import CategorialAlgebras.Presentations.Theta
import CategorialAlgebras.Presentations.CompositeCells

/-!
# The adjoint equivalence of finite presentations

Graduation is left adjoint to unification. The unit inserts only proofs of cell
membership; the counit is the inverse of the top-identity isomorphism.
-/

universe u v w

namespace CategorialAlgebras.Presentations

open CategoryTheory

variable (n : ℕ) {S : Type u} (sig : Signature.{u, v} S)

/-- The inverse homogeneous identification inserts cell proofs and retains every element. -/
theorem homogeneousRoundTripIso_inv_val
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig))
    (hB : (Homogeneous.specification (Fin n) sig).IsModel B) (s : S) (x : B.carrier s) :
    (((homogeneousRoundTripIso n sig B hB).inv.toMap s x).val).val = x := by
  have he := congrArg (fun f : B ⟶ B => f.toMap s x)
    (homogeneousRoundTripIso n sig B hB).inv_hom_id
  exact (homogeneousRoundTripIso_hom n sig B hB s _).symm.trans he

/-- Any graduated identity has the same underlying element as its input. -/
theorem graduation_identity_mem_val
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig))
    {j k : Fin (n + 1)} (h : j < k) (s)
    (x : (graduation n sig).Cell B (j, s)) (y : (graduation n sig).Cell B (k, s))
    (hy : y ∈ ((graduation n sig).transformed B).op (.identity h s) (Heterogeneous.single x)) :
    y.val = x.val :=
  Part.mem_some_iff.mp (((graduation n sig).mem_transformed_op B _ _ y).mp hy).2

/-- In a recovered graduated model, every top identity acts as inclusion on elements. -/
theorem recovered_topIdentity_graduation_val
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig))
    (hG : (Heterogeneous.specification (Fin (n + 1)) sig).IsModel
      ((graduation n sig).transformed B)) (k s) (x : (graduation n sig).Cell B (k, s)) :
    (topIdentity ((Heterogeneous.ofEquations ((graduation n sig).transformed B)
      (fun e => hG.2 _ ⟨e, rfl⟩)).sort s) k x).val = x.val := by
  revert x
  refine Fin.lastCases ?_ (fun j => ?_) k
  · intro x
    rw [topIdentity_last]
    rfl
  · intro x
    apply graduation_identity_mem_val n sig B (castSucc_lt_last j) s x
    erw [Heterogeneous.identity_op (fun e => hG.2 _ ⟨e, rfl⟩)]
    rw [topIdentity_castSucc]
    exact Part.mem_some _

/-- The forward triangle compares the unit with the top-identity component on a graduated model. -/
theorem graduation_unit_eq_theta
    (B : (Homogeneous.specification (Fin n) sig).Models) :
    (graduationModels.{u, v, w} n sig).map ((homogeneousRoundTrip n sig).inv.app B) =
      (theta n sig).hom.app ((graduationModels n sig).obj B) := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply PartialAlgebra.Hom.ext
  funext p x
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rcases p with ⟨k, s⟩
  have hu := homogeneousRoundTripIso_inv_val n sig B.obj.obj
    ⟨B.obj.property, B.property⟩ s x.val
  have ht := thetaPartial_hom_val n sig ((graduation n sig).transformed B.obj.obj)
    (graduation_isModel n sig B.obj.obj ⟨B.obj.property, B.property⟩) k s x
  exact hu.trans ((congrArg Subtype.val ht).trans
    (recovered_topIdentity_graduation_val n sig B.obj.obj
      (graduation_isModel n sig B.obj.obj ⟨B.obj.property, B.property⟩) k s x)).symm

/-- The induced functors give an equivalence on models, with the specified unit and counit. -/
noncomputable def modelPresentationEquivalence :
    (Homogeneous.specification (Fin n) sig).Models ≌
      (Heterogeneous.specification (Fin (n + 1)) sig).Models where
  functor := graduationModels.{u, v, w} n sig
  inverse := unificationModels n sig
  unitIso := (homogeneousRoundTrip n sig).symm
  counitIso := (theta n sig).symm
  functor_unitIso_comp B := by
    change (graduationModels n sig).map ((homogeneousRoundTrip n sig).inv.app B) ≫
      (theta n sig).inv.app ((graduationModels n sig).obj B) = _
    rw [graduation_unit_eq_theta]
    exact (theta n sig).hom_inv_id_app _

/-- Graduation is left adjoint to unification on models. -/
noncomputable def modelPresentationAdjunction :
    graduationModels.{u, v, w} n sig ⊣ unificationModels n sig :=
  (modelPresentationEquivalence n sig).toAdjunction

/-- The unit is the canonical identity on underlying elements. -/
theorem modelPresentationAdjunction_unit_val
    (B : (Homogeneous.specification (Fin n) sig).Models) (s : S) (x : B.obj.obj.carrier s) :
    ((((modelPresentationAdjunction n sig).unit.app B).hom.hom.toMap s x).val).val = x :=
  homogeneousRoundTripIso_inv_val n sig B.obj.obj ⟨B.obj.property, B.property⟩ s x

/-- The counit is exactly the inverse of the top-identity natural isomorphism. -/
theorem modelPresentationAdjunction_counit :
    (modelPresentationAdjunction.{u, v, w} n sig).counit = (theta n sig).inv := rfl

/-- Both the unit and counit of the model adjunction are invertible. -/
theorem modelPresentationAdjunction_isIso :
    IsIso (modelPresentationAdjunction.{u, v, w} n sig).unit ∧
      IsIso (modelPresentationAdjunction.{u, v, w} n sig).counit := by
  change IsIso (modelPresentationEquivalence n sig).unitIso.hom ∧
    IsIso (modelPresentationEquivalence n sig).counitIso.hom
  constructor <;> infer_instance

/-- The adjoint equivalence between finite categorial algebras in the two presentations. -/
noncomputable def presentationEquivalence : Homogeneous.NCategorialAlgebra.{u, v, w} n sig ≌
    Heterogeneous.NCategorialAlgebra.{u, v, w} n sig :=
  Homogeneous.modelIsomorphism.toEquivalence.trans
    ((modelPresentationEquivalence n sig).trans Heterogeneous.modelIsomorphism.symm.toEquivalence)

/-- The forward functor of the equivalence is the transported induced graduation. -/
theorem presentationEquivalence_functor :
    (presentationEquivalence.{u, v, w} n sig).functor = graduationFunctor n sig := rfl

/-- The inverse functor of the equivalence is the transported induced unification. -/
theorem presentationEquivalence_inverse :
    (presentationEquivalence.{u, v, w} n sig).inverse = unificationFunctor n sig := rfl

/-- Graduation is left adjoint to unification between categorial algebras. -/
noncomputable def presentationAdjunction :
    graduationFunctor.{u, v, w} n sig ⊣ unificationFunctor n sig :=
  (presentationEquivalence n sig).toAdjunction

/-- The transported adjunction is an adjoint equivalence: unit and counit are isomorphisms. -/
theorem presentationAdjunction_isIso :
    IsIso (presentationAdjunction.{u, v, w} n sig).unit ∧
      IsIso (presentationAdjunction.{u, v, w} n sig).counit := by
  change IsIso (presentationEquivalence n sig).unitIso.hom ∧
    IsIso (presentationEquivalence n sig).counitIso.hom
  constructor <;> infer_instance

/-- Graduation followed by unification is naturally isomorphic to identity
on categorial algebras. -/
noncomputable def homogeneousPresentationRoundTrip :
    graduationFunctor.{u, v, w} n sig ⋙ unificationFunctor n sig ≅ 𝟭 _ :=
  (presentationEquivalence n sig).unitIso.symm

/-- The top-identity isomorphism transported to the categories of categorial algebras. -/
noncomputable def heterogeneousPresentationTheta :
    𝟭 _ ≅ unificationFunctor.{u, v, w} n sig ⋙ graduationFunctor n sig :=
  (presentationEquivalence n sig).counitIso.symm

/-- The transported graduation functor is an equivalence. -/
instance graduationFunctor_isEquivalence :
    (graduationFunctor.{u, v, w} n sig).IsEquivalence := by
  change (presentationEquivalence n sig).functor.IsEquivalence
  infer_instance

/-- The transported unification functor is an equivalence. -/
instance unificationFunctor_isEquivalence :
    (unificationFunctor.{u, v, w} n sig).IsEquivalence := by
  change (presentationEquivalence n sig).inverse.IsEquivalence
  infer_instance

end CategorialAlgebras.Presentations
