import CategorialAlgebras.Dimensions.Functors

/-!
# Comparing induced model functors

Canonical composition comparisons and equal selected cells give natural
isomorphisms on models. Their components retain the underlying elements,
including the sort transports required by equality of underlying derivors.
-/

universe u v w x y z

namespace CategorialAlgebras.Dimensions

open CategoryTheory Presentations

variable {S T U : Type u} {sig : HepSignature.{u, v} S}
  {tau : HepSignature.{u, v} T} {ups : HepSignature.{u, v} U}

/-- Equal generalized hep-derivors select the same cells after their canonical sort transport. -/
theorem cells_of_eq {c d : GeneralizedHepDerivor sig tau} (h : c = d)
    (B : PartialAlgebra.{u, v, w} tau.symbol) (s : S) (b : B.carrier (c.sortMap s)) :
    c.IsCell B s b ↔ d.IsCell B s
      (cast (congrArg (fun q : Derivor sig.symbol tau.symbol => B.carrier (q.sortMap s))
        (congrArg GeneralizedHepDerivor.toDerivor h)) b) := by
  cases h
  rfl

/-- Identifying equal underlying derivors and equal cells retains every underlying element. -/
theorem sameDerivorIso_hom_heq (c d : GeneralizedHepDerivor sig tau)
    (h : c.toDerivor = d.toDerivor) (B : PartialAlgebra.{u, v, w} tau.symbol)
    (hc : ∀ s b, c.IsCell B s b ↔ d.IsCell B s
      (cast (congrArg (fun q : Derivor sig.symbol tau.symbol => B.carrier (q.sortMap s)) h) b))
    (s : S) (b : c.Cell B s) :
    HEq (((c.sameDerivorIso d h B hc).hom.toMap s b).val) b.val := by
  rcases c with ⟨c, D⟩
  rcases d with ⟨d, D'⟩
  cases h
  rfl

variable (c : GeneralizedHepDerivor sig tau) (d : GeneralizedHepDerivor tau ups)
  (e : GeneralizedHepDerivor sig ups)
  (h : (c.comp d).toDerivor = e.toDerivor)
  (E : EPSpecification.{u, v, x} sig.toEPSignature)
  (F : EPSpecification.{u, v, y} tau.toEPSignature)
  (G : EPSpecification.{u, v, z} ups.toEPSignature)
  (hc : ∀ B : PartialAlgebra.{u, v, w} tau.symbol, F.IsModel B → E.IsModel (c.transformed B))
  (hd : ∀ B : PartialAlgebra.{u, v, w} ups.symbol, G.IsModel B → F.IsModel (d.transformed B))
  (he : ∀ B : PartialAlgebra.{u, v, w} ups.symbol, G.IsModel B → E.IsModel (e.transformed B))
  (hs : ∀ B : PartialAlgebra.{u, v, w} ups.symbol, G.IsModel B →
    ∀ s, Function.Surjective ((c.comparison d B).toMap s))
  (hb : ∀ B : PartialAlgebra.{u, v, w} ups.symbol, G.IsModel B → ∀ s b,
    (c.comp d).IsCell B s b ↔ e.IsCell B s
      (cast (congrArg (fun q : Derivor sig.symbol ups.symbol => B.carrier (q.sortMap s)) h) b))

/-- A composite transformation is identified with a direct one by the canonical comparison
and by equality of underlying derivors and selected cells. -/
noncomputable def inducedCompositeIso (B : PartialAlgebra.{u, v, w} ups.symbol)
    (hB : G.IsModel B) : c.transformed (d.transformed B) ≅ e.transformed B :=
  c.comparisonIso d B (hs B hB) (hc _ (hd B hB)).1 ≪≫
    (c.comp d).sameDerivorIso e h B (hb B hB)

/-- The composite identification retains each underlying element. -/
theorem inducedCompositeIso_hom_heq (B : PartialAlgebra.{u, v, w} ups.symbol)
    (hB : G.IsModel B) (s : S) (b : c.Cell (d.transformed B) s) :
    HEq (((inducedCompositeIso c d e h E F G hc hd hs hb B hB).hom.toMap s b).val)
      b.val.val :=
  sameDerivorIso_hom_heq _ _ h B (hb B hB) s _

/-- The inverse composite identification also retains each underlying element. -/
theorem inducedCompositeIso_inv_heq (B : PartialAlgebra.{u, v, w} ups.symbol)
    (hB : G.IsModel B) (s : S) (b : e.Cell B s) :
    HEq ((((inducedCompositeIso c d e h E F G hc hd hs hb B hB).inv.toMap s b).val).val)
      b.val := by
  let i := inducedCompositeIso c d e h E F G hc hd hs hb B hB
  have hv := inducedCompositeIso_hom_heq c d e h E F G hc hd hs hb B hB s (i.inv.toMap s b)
  exact hv.symm.trans (heq_of_eq (congrArg (fun f : e.transformed B ⟶ e.transformed B =>
    (f.toMap s b).val) i.inv_hom_id))

/-- The canonical composite identification commutes with homomorphisms of models. -/
theorem inducedCompositeIso_naturality {B B' : PartialAlgebra.{u, v, w} ups.symbol}
    (f : B ⟶ B') (hB : G.IsModel B) (hB' : G.IsModel B') :
    c.transformedHom (d.transformedHom f) ≫
        (inducedCompositeIso c d e h E F G hc hd hs hb B' hB').hom =
      (inducedCompositeIso c d e h E F G hc hd hs hb B hB).hom ≫ e.transformedHom f := by
  change c.transformedHom (d.transformedHom f) ≫
      (c.comparison d B' ≫ ((c.comp d).sameDerivorIso e h B' (hb B' hB')).hom) =
    (c.comparison d B ≫ ((c.comp d).sameDerivorIso e h B (hb B hB)).hom) ≫ e.transformedHom f
  rw [← Category.assoc, c.comparison_naturality d f, Category.assoc,
    (c.comp d).sameDerivorIso_naturality e h f (hb B hB) (hb B' hB'), ← Category.assoc]

/-- Composition of induced model functors is naturally identified with a direct model functor. -/
noncomputable def inducedCompositeModelsNatIso :
    inducedModelFunctor d F G hd ⋙ inducedModelFunctor c E F hc ≅
      inducedModelFunctor e E G he :=
  NatIso.ofComponents (fun B => modelIso _ _
    (inducedCompositeIso c d e h E F G hc hd hs hb B.obj.obj ⟨B.obj.property, B.property⟩)) (by
      intro B B' f
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      exact inducedCompositeIso_naturality c d e h E F G hc hd hs hb f.hom.hom
        ⟨B.obj.property, B.property⟩ ⟨B'.obj.property, B'.property⟩)

/-- Components of the model composition identification retain each underlying element. -/
theorem inducedCompositeModelsNatIso_hom_heq (B : G.Models) (s : S)
    (b : ((inducedModelFunctor d F G hd ⋙ inducedModelFunctor c E F hc).obj B).obj.obj.carrier s) :
    HEq ((((inducedCompositeModelsNatIso c d e h E F G hc hd he hs hb).hom.app B).hom.hom.toMap s b).val)
      b.val.val :=
  inducedCompositeIso_hom_heq c d e h E F G hc hd hs hb B.obj.obj ⟨B.obj.property, B.property⟩ s b

/-- Equality of complete composite derivors is a sufficient case of the composite comparison. -/
noncomputable def inducedCompositeModelsNatIsoOfEq
    (hcd : c.comp d = e) :
    inducedModelFunctor d F G hd ⋙ inducedModelFunctor c E F hc ≅
      inducedModelFunctor e E G he :=
  inducedCompositeModelsNatIso c d e (congrArg GeneralizedHepDerivor.toDerivor hcd)
    E F G hc hd he hs (fun B _ s b => cells_of_eq hcd B s b)

/-- The identity generalized derivor preserves models. -/
theorem identity_isModel (E : EPSpecification.{u, v, x} sig.toEPSignature)
    (B : PartialAlgebra.{u, v, w} sig.symbol) (hB : E.IsModel B) :
    E.IsModel ((GeneralizedHepDerivor.identity sig).transformed B) :=
  model_of_iso E (GeneralizedHepDerivor.identityIso B
    (EPSignature.IsEPAlgebra.isWeak (sig := sig.toEPSignature) hB.1)) hB

/-- The induced identity model functor is naturally isomorphic to identity. -/
noncomputable def inducedIdentityModelsIso (E : EPSpecification.{u, v, x} sig.toEPSignature) :
    inducedModelFunctor (GeneralizedHepDerivor.identity sig) E E (identity_isModel E) ≅ 𝟭 E.Models :=
  NatIso.ofComponents (fun B => modelIso _ _
    (GeneralizedHepDerivor.identityIso B.obj.obj
      (EPSignature.IsEPAlgebra.isWeak B.obj.property)).symm) (by
        intro B B' f
        apply ObjectProperty.hom_ext
        apply ObjectProperty.hom_ext
        rfl)

/-- Equal generalized derivors induce naturally identified model functors. -/
noncomputable def inducedModelsCongr {S T : Type u} {sig : HepSignature.{u, v} S}
    {tau : HepSignature.{u, v} T} {c d : GeneralizedHepDerivor sig tau} (h : c = d)
    (E : EPSpecification.{u, v, x} sig.toEPSignature)
    (F : EPSpecification.{u, v, y} tau.toEPSignature)
    (hc : ∀ B : PartialAlgebra.{u, v, w} tau.symbol, F.IsModel B → E.IsModel (c.transformed B))
    (hd : ∀ B : PartialAlgebra.{u, v, w} tau.symbol, F.IsModel B → E.IsModel (d.transformed B)) :
    inducedModelFunctor c E F hc ≅ inducedModelFunctor d E F hd :=
  eqToIso (by cases h; rfl)

/-- A model functor induced by a derivor equal to identity is identified with identity. -/
noncomputable def inducedIdentityModelsIsoOfEq {c : GeneralizedHepDerivor sig sig}
    (h : c = GeneralizedHepDerivor.identity sig)
    (E : EPSpecification.{u, v, x} sig.toEPSignature)
    (hc : ∀ B : PartialAlgebra.{u, v, w} sig.symbol, E.IsModel B → E.IsModel (c.transformed B)) :
    inducedModelFunctor c E E hc ≅ 𝟭 E.Models := by
  cases h
  exact inducedIdentityModelsIso E

/-- The identity model identification forgets only the cell proof. -/
theorem inducedIdentityModelsIsoOfEq_hom_heq {c : GeneralizedHepDerivor sig sig}
    (h : c = GeneralizedHepDerivor.identity sig)
    (E : EPSpecification.{u, v, x} sig.toEPSignature)
    (hc : ∀ B : PartialAlgebra.{u, v, w} sig.symbol, E.IsModel B → E.IsModel (c.transformed B))
    (B : E.Models) (s : S) (b : c.Cell B.obj.obj s) :
    HEq (((inducedIdentityModelsIsoOfEq h E hc).hom.app B).hom.hom.toMap s b) b.val := by
  cases h
  rfl

end CategorialAlgebras.Dimensions
