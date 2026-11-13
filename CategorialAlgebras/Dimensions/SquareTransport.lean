import CategorialAlgebras.Dimensions.CompatibilityComparison
import CategorialAlgebras.Preliminaries.AlgebraicSquare

/-!
# Transport of conjugate square comparisons

Conjugation of natural isomorphisms commutes with transport through strict
isomorphisms of categories. The transport uses the specified adjunctions
of the isomorphisms and retains their equality transports.
-/

namespace CategorialAlgebras.Dimensions

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

/-- Transport an adjunction through strict category isomorphisms. -/
noncomputable def conjugateAdjunction {C D C' D' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    (a : IsoCat C C') (b : IsoCat D D') {F : C' ⥤ D'} {G : D' ⥤ C'} (adj : F ⊣ G) :
    (a.functor ⋙ F ⋙ b.inverse) ⊣ (b.functor ⋙ G ⋙ a.inverse) :=
  a.toEquivalence.toAdjunction.comp (adj.comp b.symm.toEquivalence.toAdjunction)

/-- The inverse followed by the forward functor returns each object exactly. -/
theorem isoCat_counit_obj {C D : Type*} [Category C] [Category D]
    (e : IsoCat C D) (X : D) : e.functor.obj (e.inverse.obj X) = X :=
  Functor.congr_obj e.counit_eq X

/-- The inverse followed by the forward functor transports each morphism by object equalities. -/
theorem isoCat_counit_map {C D : Type*} [Category C] [Category D]
    (e : IsoCat C D) {X Y : D} (f : X ⟶ Y) :
    e.functor.map (e.inverse.map f) = eqToHom (isoCat_counit_obj e X) ≫ f ≫
      eqToHom (isoCat_counit_obj e Y).symm := Functor.congr_hom e.counit_eq f

set_option maxHeartbeats 800000 in
/-- Transporting the conjugate comparison agrees with conjugating the transported left comparison. -/
theorem conjugateSquareIso_conjugateIso
    {C D E F C' D' E' F' : Type*}
    [Category C] [Category D] [Category E] [Category F]
    [Category C'] [Category D'] [Category E'] [Category F']
    (a : IsoCat C C') (b : IsoCat D D') (c : IsoCat E E') (d : IsoCat F F')
    {L : C' ⥤ E'} {R : E' ⥤ C'} {L' : D' ⥤ F'} {R' : F' ⥤ D'}
    {J : C' ⥤ D'} {K : D' ⥤ C'} {H : E' ⥤ F'} {I : F' ⥤ E'}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (v : J ⊣ K) (v' : H ⊣ I)
    (α : J ⋙ L' ≅ L ⋙ H) :
    conjugateSquareIso d c b a (AlgebraicSquare.conjugateIso adj adj' v v' α) =
      AlgebraicSquare.conjugateIso (conjugateAdjunction a c adj) (conjugateAdjunction b d adj')
        (conjugateAdjunction a b v) (conjugateAdjunction c d v') (conjugateSquareIso a b c d α) := by
  apply Iso.ext
  ext X
  simp [AlgebraicSquare.conjugateIso, conjugateIsoEquiv, conjugateEquiv_apply_app,
    conjugateAdjunction, conjugateSquareIso, conjugateCompositeIso,
    Adjunction.comp_unit_app, Adjunction.comp_counit_app, Functor.map_comp,
    IsoCat.toEquivalence, IsoCat.symm, Category.assoc, eqToHom_map]
  simp only [isoCat_counit_map b, isoCat_counit_map c, isoCat_counit_map d,
    Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc]
  let Y := I.obj (d.functor.obj X)
  have hy : c.functor.obj (c.inverse.obj Y) = Y := isoCat_counit_obj c Y
  have hz : a.functor.obj (a.inverse.obj (R.obj (c.functor.obj (c.inverse.obj Y)))) = R.obj Y :=
    (isoCat_counit_obj a _).trans (congrArg R.obj hy)
  let Z := a.functor.obj (a.inverse.obj (R.obj (c.functor.obj (c.inverse.obj Y))))
  have hj : b.functor.obj (b.inverse.obj (J.obj Z)) = J.obj (R.obj Y) :=
    (isoCat_counit_obj b _).trans (congrArg J.obj hz)
  erw [eqToHom_naturality_assoc (fun Z => a.inverse.map (K.map (R'.map (H.map (adj.counit.app Z))))) hy]
  simp only [eqToHom_trans_assoc]
  erw [eqToHom_naturality_assoc (fun Z => a.inverse.map (K.map (R'.map (α.hom.app Z)))) hz]
  simp only [eqToHom_trans_assoc]
  erw [eqToHom_naturality_assoc (fun Z => a.inverse.map (K.map (adj'.unit.app Z))) hj]
  simp only [eqToHom_trans_assoc]
  erw [eqToHom_naturality_assoc (fun Z => a.inverse.map (v.unit.app Z)) hz]
  simp
  rfl

end CategorialAlgebras.Dimensions
