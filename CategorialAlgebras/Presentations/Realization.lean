import CategorialAlgebras.HepDerivor.Comparison

/-!
# Recognizing induced transformations

An ep-algebra on the selected carriers coincides with a transformation once its
operations preserve the interpreting term values. Hierarchy supplies reflection.
-/

universe u v u' v' w

namespace CategorialAlgebras.Presentations

open CategoryTheory

/-- An ep-algebra on the exact cell carriers realizes the induced transformation if its
operations have the prescribed interpreting values. -/
theorem transformed_eq_of_realization {S : Type u} {T : Type u'}
    {sig : HepSignature.{u, v} S} {tau : HepSignature.{u', v'} T}
    (c : GeneralizedHepDerivor sig tau) (B : PartialAlgebra.{u', v', w} tau.symbol)
    (op : PartialAlgebraStructure sig.symbol (c.Cell B))
    (hA : sig.IsEPAlgebra ⟨c.Cell B, op⟩)
    (hv : ∀ {a s} (σ : sig.symbol a s) (x : Word.Family (c.Cell B) a) {q},
      q ∈ op σ x → q.val ∈ c.imageValue B σ x) :
    c.transformed B = ⟨c.Cell B, op⟩ := by
  let A : PartialAlgebra sig.symbol := ⟨c.Cell B, op⟩
  let f : A ⟶ c.transformed B :=
    ⟨fun _ => id, c.mem_op_of_imageValue B hA.isWeak (fun _ => id) hv⟩
  have : IsIso f := sig.isIso_of_bijective hA (c.transformed_isWeak B) f
    (fun _ => Function.bijective_id)
  apply congrArg (PartialAlgebra.mk (c.Cell B))
  funext a s σ x
  apply Part.ext
  intro q
  constructor
  · intro hq
    have hd := f.reflectsDefinedness_of_isIso σ x hq.1
    have hm := f.map_op σ x (Part.get_mem hd)
    have he : (op σ x).get hd = q := Part.mem_unique hm hq
    exact he ▸ Part.get_mem hd
  · exact f.map_op σ x

/-- Quasi-existence validity is invariant under partial-algebra isomorphisms. -/
theorem valid_of_iso {S : Type u} {sig : Signature.{u, v} S}
    {A B : PartialAlgebra.{u, v, w} sig} (e : A ≅ B) {X : S → Type u'}
    {a s} (q : QEEquation sig X a s) (hA : QEEquation.Valid A q) :
    QEEquation.Valid B q := by
  intro z hz
  have he : (fun s x => e.hom.toMap s (e.inv.toMap s (z s x))) = z := by
    funext s x
    exact congrArg (fun f : B ⟶ B => f.toMap s (z s x)) e.inv_hom_id
  have h := EEquation.satisfies_hom e.hom (fun s x => e.inv.toMap s (z s x))
    q.conclusion (hA _ (fun j => EEquation.satisfies_hom e.inv z _ (hz j)))
  rwa [he] at h

/-- An ep-specification's model condition is invariant under isomorphisms. -/
theorem model_of_iso {S : Type u} {sig : EPSignature.{u, v} S}
    (E : EPSpecification.{u, v, u'} sig) {A B : PartialAlgebra.{u, v, w} sig.symbol}
    (e : A ≅ B) (hA : E.IsModel A) : E.IsModel B :=
  ⟨sig.isEPAlgebra_of_iso e hA.1, fun q hq => valid_of_iso e q.equation (hA.2 q hq)⟩

/-- A bijective realization gives an isomorphism to the induced transformation. -/
noncomputable def realizationIso {S : Type u} {T : Type u'}
    {sig : HepSignature.{u, v} S} {tau : HepSignature.{u', v'} T}
    (c : GeneralizedHepDerivor sig tau) (B : PartialAlgebra.{u', v', w} tau.symbol)
    (A : PartialAlgebra.{u, v, w} sig.symbol) (hA : sig.IsEPAlgebra A)
    (f : SortedSet.Map A.carrier (c.Cell B)) (hf : ∀ s, Function.Bijective (f s))
    (hv : ∀ {a s} (σ : sig.symbol a s) (x : Word.Family A.carrier a) {q},
      q ∈ A.op σ x → (f s q).val ∈ c.imageValue B σ (fun j => f _ (x j))) :
    A ≅ c.transformed B := by
  let g : A ⟶ c.transformed B :=
    ⟨f, c.mem_op_of_imageValue B hA.isWeak f hv⟩
  have : IsIso g := sig.isIso_of_bijective hA (c.transformed_isWeak B) g hf
  exact asIso g

/-- Translation of a sorted singleton equation set is satisfied exactly when its translated
pair is satisfied. The source context is a single variable. -/
theorem satisfies_translated_singleton {S : Type u} {T : Type u'}
    {sig : Signature.{u, v} S} {tau : Signature.{u', v'} T}
    (c : Derivor sig tau) {s : S} (e : EEquation sig (Word.Variables [s]) s)
    (A : PartialAlgebra.{u', v', w} tau) (x : A.carrier (c.sortMap s)) :
    EEquationSet.Satisfies A (Word.singletonValuation x)
      (c.translateSingletonSet s (fun t => {p | ∃ h : s = t, p = h ▸ e})) ↔
      EEquation.Satisfies A (Word.singletonValuation x)
        (c.translateSingleton s e.1, c.translateSingleton s e.2) := by
  constructor
  · intro h
    exact h _ _ ⟨s, rfl, e, ⟨rfl, rfl⟩, rfl⟩
  · intro h t p ⟨r, hr, q, ⟨hs, hq⟩, hp⟩
    cases hs
    cases hq
    cases hr
    cases hp
    exact h

/-- Equality transport between transformations retains the underlying element. -/
theorem transformed_transport_val {S : Type u} {T : Type u'}
    {sig : HepSignature.{u, v} S} {tau : HepSignature.{u', v'} T}
    {c d : GeneralizedHepDerivor sig tau} (h : c = d)
    (A : PartialAlgebra.{u', v', w} tau.symbol) (s : S) (x : c.Cell A s)
    (p : c.transformed A = d.transformed A) :
    HEq (((eqToHom p).toMap s x).val) x.val := by
  cases h
  rfl

/-- An isomorphism of underlying partial algebras lifts to the double full category of models. -/
def modelIso {S : Type u} {sig : EPSignature.{u, v} S}
    {E : EPSpecification.{u, v, u'} sig} (A B : EPSpecification.Models.{u, v, w, u'} E)
    (e : A.obj.obj ≅ B.obj.obj) : A ≅ B where
  hom := ObjectProperty.homMk (ObjectProperty.homMk e.hom)
  inv := ObjectProperty.homMk (ObjectProperty.homMk e.inv)
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact e.hom_inv_id
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact e.inv_hom_id

/-- The underlying function of equality transport is transport in the carrier. -/
theorem partial_eqToHom_toMap {S : Type u} {sig : Signature.{u, v} S}
    {A B : PartialAlgebra.{u, v, w} sig} (h : A = B) (s : S) (x : A.carrier s) :
    (eqToHom h).toMap s x = cast (congrArg (fun A => A.carrier s) h) x := by
  cases h
  rfl

/-- Equality of partial algebras on a fixed carrier is equality of their operation structures. -/
theorem op_eq_of_same_carrier {S : Type u} {sig : Signature.{u, v} S} {C : S → Type w}
    {op op' : PartialAlgebraStructure sig C}
    (h : (⟨C, op⟩ : PartialAlgebra sig) = ⟨C, op'⟩) : @op = @op' :=
  eq_of_heq (PartialAlgebra.mk.inj h).2

end CategorialAlgebras.Presentations
