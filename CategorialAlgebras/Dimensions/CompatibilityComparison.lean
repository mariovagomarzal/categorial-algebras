import CategorialAlgebras.Dimensions.Comparison
import CategorialAlgebras.Dimensions.Transport

/-!
# Comparing squares on model categories

The square comparison for partial algebras lifts through the full model
categories. Strict category isomorphisms then transport it to categorial
algebras, cancelling both intermediate presentations.
-/

universe u v w x y z t

namespace CategorialAlgebras.Dimensions

open CategoryTheory Presentations

variable {S T U V : Type u} {sig : HepSignature.{u, v} S}
  {tau : HepSignature.{u, v} T} {ups : HepSignature.{u, v} U}
  {xi : HepSignature.{u, v} V}
  (c : GeneralizedHepDerivor sig tau) (d : GeneralizedHepDerivor tau ups)
  (c' : GeneralizedHepDerivor sig xi) (d' : GeneralizedHepDerivor xi ups)
  (h : (c.comp d).toDerivor = (c'.comp d').toDerivor)
  (E : EPSpecification.{u, v, x} sig.toEPSignature)
  (F : EPSpecification.{u, v, y} tau.toEPSignature)
  (G : EPSpecification.{u, v, z} ups.toEPSignature)
  (H : EPSpecification.{u, v, t} xi.toEPSignature)
  (hc : ∀ B : PartialAlgebra.{u, v, w} tau.symbol, F.IsModel B → E.IsModel (c.transformed B))
  (hd : ∀ B : PartialAlgebra.{u, v, w} ups.symbol, G.IsModel B → F.IsModel (d.transformed B))
  (hc' : ∀ B : PartialAlgebra.{u, v, w} xi.symbol, H.IsModel B → E.IsModel (c'.transformed B))
  (hd' : ∀ B : PartialAlgebra.{u, v, w} ups.symbol, G.IsModel B → H.IsModel (d'.transformed B))
  (hs : ∀ B : PartialAlgebra.{u, v, w} ups.symbol, G.IsModel B →
    ∀ s, Function.Surjective ((c.comparison d B).toMap s))
  (hs' : ∀ B : PartialAlgebra.{u, v, w} ups.symbol, G.IsModel B →
    ∀ s, Function.Surjective ((c'.comparison d' B).toMap s))
  (hb : ∀ B : PartialAlgebra.{u, v, w} ups.symbol, G.IsModel B → ∀ s b,
    (c.comp d).IsCell B s b ↔ (c'.comp d').IsCell B s
      (cast (congrArg (fun q : Derivor sig.symbol ups.symbol => B.carrier (q.sortMap s)) h) b))

/-- The canonical square comparison, restricted and corestricted to models. -/
noncomputable def inducedSquareModelsNatIso :
    inducedModelFunctor d F G hd ⋙ inducedModelFunctor c E F hc ≅
      inducedModelFunctor d' H G hd' ⋙ inducedModelFunctor c' E H hc' :=
  let i := c.squareNatIso d c' d' h G.IsModel hs hs'
    (fun B hB => (hc _ (hd B hB)).1) (fun B hB => (hc' _ (hd' B hB)).1) hb
  NatIso.ofComponents (fun B => modelIso _ _ (i.app ⟨B.obj.obj, B.obj.property, B.property⟩)) (by
    intro B B' f
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact i.hom.naturality (X := ⟨B.obj.obj, B.obj.property, B.property⟩)
      (Y := ⟨B'.obj.obj, B'.obj.property, B'.property⟩) ⟨f.hom.hom⟩)

/-- The square comparison retains each underlying element, with its canonical sort transport. -/
theorem inducedSquareModelsNatIso_hom_heq (B : G.Models) (s : S)
    (b : c.Cell (d.transformed B.obj.obj) s) :
    HEq (((((inducedSquareModelsNatIso c d c' d' h E F G H hc hd hc' hd' hs hs' hb).hom.app B).hom.hom.toMap s b).val).val) b.val.val := by
  change HEq (((((c'.comparisonIso d' B.obj.obj (hs' _ ⟨B.obj.property, B.property⟩)
    (hc' _ (hd' _ ⟨B.obj.property, B.property⟩)).1).inv.toMap s
      (((c.comp d).sameDerivorIso (c'.comp d') h B.obj.obj
        (hb _ ⟨B.obj.property, B.property⟩)).hom.toMap s
          ((c.comparison d B.obj.obj).toMap s b))).val).val)) b.val.val
  exact (heq_of_eq (c'.comparisonIso_inv_val d' B.obj.obj
    (hs' _ ⟨B.obj.property, B.property⟩) (hc' _ (hd' _ ⟨B.obj.property, B.property⟩)).1 s _)).trans
      (sameDerivorIso_hom_heq _ _ h B.obj.obj (hb _ ⟨B.obj.property, B.property⟩) s _)

/-- The inverse square comparison also retains each underlying element. -/
theorem inducedSquareModelsNatIso_inv_heq (B : G.Models) (s : S)
    (b : c'.Cell (d'.transformed B.obj.obj) s) :
    HEq (((((inducedSquareModelsNatIso c d c' d' h E F G H hc hd hc' hd' hs hs' hb).inv.app B).hom.hom.toMap s b).val).val) b.val.val := by
  let i := inducedSquareModelsNatIso c d c' d' h E F G H hc hd hc' hd' hs hs' hb
  have hv := inducedSquareModelsNatIso_hom_heq c d c' d' h E F G H hc hd hc' hd' hs hs' hb B s
    ((i.inv.app B).hom.hom.toMap s b)
  exact hv.symm.trans (heq_of_eq (congrArg (fun f => ((f.hom.hom.toMap s b).val).val)
    (i.inv_hom_id_app B)))

/-- Transport a commuting square through four strict category isomorphisms. -/
noncomputable def conjugateSquareIso {C D E F C' D' E' F' : Type*}
    [Category C] [Category D] [Category E] [Category F]
    [Category C'] [Category D'] [Category E'] [Category F']
    (a : IsoCat C C') (b : IsoCat D D') (c : IsoCat E E') (d : IsoCat F F')
    {J : C' ⥤ D'} {K : D' ⥤ F'} {L : C' ⥤ E'} {M : E' ⥤ F'}
    (i : J ⋙ K ≅ L ⋙ M) :
    (a.functor ⋙ J ⋙ b.inverse) ⋙ (b.functor ⋙ K ⋙ d.inverse) ≅
      (a.functor ⋙ L ⋙ c.inverse) ⋙ (c.functor ⋙ M ⋙ d.inverse) :=
  conjugateCompositeIso a b d i ≪≫
    (conjugateCompositeIso a c d (Iso.refl (L ⋙ M))).symm

end CategorialAlgebras.Dimensions
