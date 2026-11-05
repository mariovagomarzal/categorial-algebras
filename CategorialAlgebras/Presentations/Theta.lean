import CategorialAlgebras.Presentations.IdentityImage

/-!
# The natural identity-image isomorphism

The component from a heterogeneous model to its unification followed by graduation
sends a cell to its identity in the top dimension.
-/

universe u v w

namespace CategorialAlgebras.Presentations

open CategoryTheory

variable (n : ℕ) {S : Type u} (sig : Signature.{u, v} S)

/-- The identity-image isomorphism on expansions, followed by the induced graduation
of the unification realization. -/
noncomputable def thetaExpansion (A : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig) :
    A.toPartialAlgebra ≅
      (graduation n sig).transformed ((unification n sig).transformed A.toPartialAlgebra) :=
  identityImageIso A ≪≫ eqToIso (graduation_transformed n sig (unifiedAlgebra A)).symm ≪≫
    (graduation n sig).transformedFunctor.mapIso (unificationRealization n sig A)

/-- The component on any model, using recovery on its unchanged carrier. -/
noncomputable def thetaPartial (A : PartialAlgebra.{u, max v u, w}
    (Heterogeneous.Symbol (Fin (n + 1)) sig))
    (hA : (Heterogeneous.specification (Fin (n + 1)) sig).IsModel A) :
    A ≅ (graduation n sig).transformed ((unification n sig).transformed A) := by
  let C := Heterogeneous.ofEquations A (fun e => hA.2 _ ⟨e, rfl⟩)
  let hc : C.toPartialAlgebra = A := Heterogeneous.toPartialAlgebra_ofEquations A _
  exact eqToIso hc.symm ≪≫ thetaExpansion n sig C ≪≫
    (graduation n sig).transformedFunctor.mapIso
      ((unification n sig).transformedFunctor.mapIso (eqToIso hc))

/-- The component on an expansion sends $x$ to its top identity on underlying elements. -/
theorem thetaExpansion_hom_val (A : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig)
    (k s) (x : (A.sort s).carrier k) :
    (((thetaExpansion n sig A).hom.toMap (k, s) x).val).val = topIdentity (A.sort s) k x := by
  change ((eqToHom (graduation_transformed n sig (unifiedAlgebra A)).symm).toMap
    (k, s) (identityImageCell A k s x)).val = _
  erw [partial_eqToHom_toMap]
  rfl

/-- On arbitrary models the component is still the top identity of the recovered structure. -/
theorem thetaPartial_hom_val (A : PartialAlgebra.{u, max v u, w}
    (Heterogeneous.Symbol (Fin (n + 1)) sig))
    (hA : (Heterogeneous.specification (Fin (n + 1)) sig).IsModel A)
    (k s) (x : A.carrier (k, s)) :
    (((thetaPartial n sig A hA).hom.toMap (k, s) x).val).val =
      topIdentity ((Heterogeneous.ofEquations A (fun e => hA.2 _ ⟨e, rfl⟩)).sort s) k x := by
  change (eqToHom (Heterogeneous.toPartialAlgebra_ofEquations A _)).toMap (Fin.last n, s)
    (((thetaExpansion n sig _).hom.toMap (k, s)
      ((eqToHom (Heterogeneous.toPartialAlgebra_ofEquations A _).symm).toMap (k, s) x)).val).val = _
  erw [partial_eqToHom_toMap, partial_eqToHom_toMap]
  exact thetaExpansion_hom_val n sig
    (Heterogeneous.ofEquations A (fun e => hA.2 _ ⟨e, rfl⟩)) k s x

/-- The inverse component sends a selected top identity to its source in the original dimension. -/
theorem thetaPartial_inv_val (A : PartialAlgebra.{u, max v u, w}
    (Heterogeneous.Symbol (Fin (n + 1)) sig))
    (hA : (Heterogeneous.specification (Fin (n + 1)) sig).IsModel A)
    (k s) (y : (graduation n sig).Cell ((unification n sig).transformed A) (k, s)) :
    (thetaPartial n sig A hA).inv.toMap (k, s) y =
      topSource ((Heterogeneous.ofEquations A (fun e => hA.2 _ ⟨e, rfl⟩)).sort s) k y.val.val := by
  have ht := thetaPartial_hom_val n sig A hA k s
    ((thetaPartial n sig A hA).inv.toMap (k, s) y)
  have he := congrArg (fun f :
    (graduation n sig).transformed ((unification n sig).transformed A) ⟶
      (graduation n sig).transformed ((unification n sig).transformed A) =>
        ((f.toMap (k, s) y).val).val) (thetaPartial n sig A hA).inv_hom_id
  exact (topSource_topIdentity _ k _).symm.trans
    (congrArg (topSource _ k) (ht.symm.trans he))

/-- Naturality of top identities in the recovered structures of two models. -/
theorem recovered_topIdentity_natural
    {A B : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol (Fin (n + 1)) sig)}
    (hA : (Heterogeneous.specification (Fin (n + 1)) sig).IsModel A)
    (hB : (Heterogeneous.specification (Fin (n + 1)) sig).IsModel B)
    (f : A ⟶ B) (k s) (x : A.carrier (k, s)) :
    f.toMap (Fin.last n, s)
      (topIdentity ((Heterogeneous.ofEquations A (fun e => hA.2 _ ⟨e, rfl⟩)).sort s) k x) =
      topIdentity ((Heterogeneous.ofEquations B (fun e => hB.2 _ ⟨e, rfl⟩)).sort s) k
        (f.toMap (k, s) x) := by
  let C := Heterogeneous.ofEquations A (fun e => hA.2 _ ⟨e, rfl⟩)
  let D := Heterogeneous.ofEquations B (fun e => hB.2 _ ⟨e, rfl⟩)
  let g : C.toPartialAlgebra ⟶ D.toPartialAlgebra :=
    eqToHom (Heterogeneous.toPartialAlgebra_ofEquations A _) ≫ f ≫
      eqToHom (Heterogeneous.toPartialAlgebra_ofEquations B _).symm
  have hg : ∀ p z, g.toMap p z = f.toMap p z := by
    intro p z
    change (eqToHom (Heterogeneous.toPartialAlgebra_ofEquations B _).symm).toMap p
      (f.toMap p ((eqToHom (Heterogeneous.toPartialAlgebra_ofEquations A _)).toMap p z)) = _
    erw [partial_eqToHom_toMap, partial_eqToHom_toMap]
    rfl
  have hh := topIdentity_natural
    ((Heterogeneous.CategorialAlgebra.Hom.ofPartialHom g).sort s) k x
  change g.toMap (Fin.last n, s) _ = topIdentity (D.sort s) k (g.toMap (k, s) x) at hh
  erw [hg, hg] at hh
  exact hh

/-- The identity-image components form a natural isomorphism on heterogeneous models. -/
noncomputable def theta : 𝟭 (Heterogeneous.specification (Fin (n + 1)) sig).Models ≅
    unificationModels.{u, v, w} n sig ⋙ graduationModels n sig :=
  NatIso.ofComponents (fun A => modelIso _ _
    (thetaPartial n sig A.obj.obj ⟨A.obj.property, A.property⟩)) (by
      intro A B f
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply PartialAlgebra.Hom.ext
      funext p x
      apply Subtype.ext
      apply Subtype.ext
      rcases p with ⟨k, s⟩
      change (((thetaPartial n sig B.obj.obj ⟨B.obj.property, B.property⟩).hom.toMap (k, s)
        (f.hom.hom.toMap (k, s) x)).val).val =
        f.hom.hom.toMap (Fin.last n, s)
          (((thetaPartial n sig A.obj.obj ⟨A.obj.property, A.property⟩).hom.toMap (k, s) x).val).val
      erw [thetaPartial_hom_val, thetaPartial_hom_val]
      exact (recovered_topIdentity_natural n sig ⟨A.obj.property, A.property⟩
        ⟨B.obj.property, B.property⟩ f.hom.hom k s x).symm)

end CategorialAlgebras.Presentations
