import CategorialAlgebras.HepDerivor.Transformed

/-!
# Composition of generalized hep-derivors

A composite combines the second sort domain with the translated first domain.
Translation retains the unique positional variable, including when sort maps are
not injective. Bundled hierarchical signatures and generalized hep-derivors form
a category at fixed sort and symbol universes.
-/

universe u v u' v' u'' v'' u''' v'''

namespace CategorialAlgebras

open CategoryTheory

namespace Word

/-- Change the sort of the unique positional variable of a singleton word. -/
def singletonMap {S : Type u} {T : Type u'} (φ : S → T) (s : S) :
    ∀ t, Variables [s] t → Variables [φ s] (φ t) :=
  fun _ x => mappedVariablesEquiv φ [s] _ ⟨x.val, congrArg φ x.property⟩

/-- Changing singleton sorts by the identity fixes their variables. -/
@[simp] theorem singletonMap_id {S : Type u} (s t : S) (x : Variables [s] t) :
    singletonMap id s t x = x := by
  apply Subtype.ext
  rfl

/-- Successive changes of singleton sorts compose. -/
@[simp] theorem singletonMap_comp {S : Type u} {T : Type u'} {U : Type u''}
    (φ : S → T) (ψ : T → U) (s t : S) (x : Variables [s] t) :
    singletonMap ψ (φ s) (φ t) (singletonMap φ s t x) =
      singletonMap (ψ ∘ φ) s t x := by
  apply Subtype.ext
  rfl

end Word

namespace Derivor

variable {S : Type u} {T : Type u'} {U : Type u''}
variable {sig : Signature.{u, v} S} {tau : Signature.{u', v'} T}
variable {ups : Signature.{u'', v''} U}

/-- Translate a term in one variable and identify the translated positions with
those of the singleton word of its new sort. -/
def translateSingleton (c : Derivor sig tau) (s : S) {t}
    (p : Term sig (Word.Variables [s]) t) :
    Term tau (Word.Variables [c.sortMap s]) (c.sortMap t) :=
  c.translate (fun t x => Term.var (Word.singletonMap c.sortMap s t x)) p

/-- Singleton translation is word translation followed by the positional equivalence. -/
theorem translateSingleton_eq (c : Derivor sig tau) (s : S) {t}
    (p : Term sig (Word.Variables [s]) t) :
    c.translateSingleton s p = Term.subst
      (fun t x => Term.var (Word.mappedVariablesEquiv c.sortMap [s] t x))
      (c.translateWord [s] p) := by
  rw [translateWord, subst_translate]
  rfl

/-- Singleton translation by the identity fixes terms. -/
@[simp] theorem translateSingleton_identity (s : S) {t}
    (p : Term sig (Word.Variables [s]) t) :
    (identity sig).translateSingleton s p = p := by
  unfold translateSingleton
  rw [translate_identity]
  simpa only [Word.singletonMap_id] using Term.subst_id p

/-- Singleton translation commutes with composition. -/
theorem translateSingleton_comp (c : Derivor sig tau) (d : Derivor tau ups)
    (s : S) {t} (p : Term sig (Word.Variables [s]) t) :
    (c.comp d).translateSingleton s p =
      d.translateSingleton (c.sortMap s) (c.translateSingleton s p) := by
  unfold translateSingleton
  rw [← translate_comp]
  simp only [translate_var, Word.singletonMap_comp]

/-- Translate a sorted set of singleton equations, taking the union over source sorts. -/
def translateSingletonSet (c : Derivor sig tau) (s : S)
    (E : EEquationSet sig (Word.Variables [s])) :
    EEquationSet tau (Word.Variables [c.sortMap s]) := fun t =>
  {e | ∃ r, ∃ h : c.sortMap r = t, ∃ p ∈ E r,
    e = h ▸ (c.translateSingleton s p.1, c.translateSingleton s p.2)}

/-- Translation preserves the empty sorted set. -/
@[simp] theorem translateSingletonSet_empty (c : Derivor sig tau) (s : S) :
    c.translateSingletonSet s ⊥ = ⊥ := by
  funext t
  ext e
  simp [translateSingletonSet]

/-- Translation preserves unions of sorted sets. -/
theorem translateSingletonSet_union (c : Derivor sig tau) (s : S)
    (E H : EEquationSet sig (Word.Variables [s])) :
    c.translateSingletonSet s (E ⊔ H) =
      c.translateSingletonSet s E ⊔ c.translateSingletonSet s H := by
  funext t
  ext e
  simp only [translateSingletonSet, Set.mem_ofPred_eq, Pi.sup_apply]
  aesop

/-- The identity fixes singleton equation sets. -/
@[simp] theorem translateSingletonSet_identity (s : S)
    (E : EEquationSet sig (Word.Variables [s])) :
    (identity sig).translateSingletonSet s E = E := by
  funext t
  ext e
  constructor
  · rintro ⟨r, h, p, hp, he⟩
    change r = t at h
    subst t
    have he' : e = p := by simpa using he
    rwa [he']
  · intro he
    exact ⟨t, rfl, e, he, by simp⟩

/-- Successive translations of singleton equation sets equal composite translation. -/
theorem translateSingletonSet_comp (c : Derivor sig tau) (d : Derivor tau ups)
    (s : S) (E : EEquationSet sig (Word.Variables [s])) :
    (c.comp d).translateSingletonSet s E =
      d.translateSingletonSet (c.sortMap s) (c.translateSingletonSet s E) := by
  funext t
  ext e
  constructor
  · rintro ⟨r, h, p, hp, he⟩
    subst t
    refine ⟨c.sortMap r, rfl, (c.translateSingleton s p.1, c.translateSingleton s p.2),
      ⟨r, rfl, p, hp, rfl⟩, ?_⟩
    simpa only [translateSingleton_comp] using he
  · rintro ⟨q, h, p, ⟨r, hr, z, hz, hp⟩, he⟩
    subst q
    subst t
    subst p
    exact ⟨r, rfl, z, hz, by simpa only [translateSingleton_comp] using he⟩

end Derivor

namespace GeneralizedHepDerivor

variable {S : Type u} {T : Type u'} {U : Type u''} {V : Type u'''}
variable {sig : HepSignature.{u, v} S} {tau : HepSignature.{u', v'} T}
variable {ups : HepSignature.{u'', v''} U} {xi : HepSignature.{u''', v'''} V}

/-- Equality is determined by the underlying derivor and its dependent sort domains. -/
theorem ext {c d : GeneralizedHepDerivor sig tau} (h : c.toDerivor = d.toDerivor)
    (hd : HEq c.domain d.domain) : c = d := by
  cases c
  cases d
  cases h
  cases hd
  rfl

/-- Identity generalized hep-derivor, with no restrictions on cells. -/
abbrev identity (sig : HepSignature.{u, v} S) : GeneralizedHepDerivor sig sig where
  toDerivor := Derivor.identity sig.symbol
  domain _ := ⊥

/-- Composition translates the first domain and adjoins the second domain. -/
abbrev comp (c : GeneralizedHepDerivor sig tau) (d : GeneralizedHepDerivor tau ups) :
    GeneralizedHepDerivor sig ups where
  toDerivor := c.toDerivor.comp d.toDerivor
  domain s := d.domain (c.sortMap s) ⊔ d.toDerivor.translateSingletonSet _ (c.domain s)

/-- The identity is a left unit for composition. -/
@[simp] theorem identity_comp (c : GeneralizedHepDerivor sig tau) :
    (identity sig).comp c = c := by
  apply ext (Derivor.identity_comp c.toDerivor)
  apply heq_of_eq
  funext s
  simp only [comp, identity, Derivor.translateSingletonSet_empty, sup_bot_eq, id_eq]

/-- The identity is a right unit for composition. -/
@[simp] theorem comp_identity (c : GeneralizedHepDerivor sig tau) :
    c.comp (identity tau) = c := by
  apply ext (Derivor.comp_identity c.toDerivor)
  apply heq_of_eq
  funext s
  simp only [comp, identity, Derivor.translateSingletonSet_identity, bot_sup_eq]

/-- Composition of generalized hep-derivors is associative. -/
theorem comp_assoc (c : GeneralizedHepDerivor sig tau) (d : GeneralizedHepDerivor tau ups)
    (e : GeneralizedHepDerivor ups xi) : (c.comp d).comp e = c.comp (d.comp e) := by
  apply ext (Derivor.comp_assoc c.toDerivor d.toDerivor e.toDerivor)
  apply heq_of_eq
  funext s
  simp only [comp, Derivor.translateSingletonSet_union, Derivor.translateSingletonSet_comp,
    sup_assoc, Function.comp_apply]

end GeneralizedHepDerivor

/-- A hierarchical signature with its sort type, at fixed sort and symbol universes. -/
structure BundledHepSignature where
  /-- The sort type. -/
  sorts : Type u
  /-- The hierarchical signature on these sorts. -/
  signature : HepSignature.{u, v} sorts

/-- Hierarchical signatures and generalized hep-derivors form a category. -/
instance : Category (BundledHepSignature.{u, v}) where
  Hom A B := GeneralizedHepDerivor A.signature B.signature
  id A := GeneralizedHepDerivor.identity A.signature
  comp := GeneralizedHepDerivor.comp
  id_comp := GeneralizedHepDerivor.identity_comp
  comp_id := GeneralizedHepDerivor.comp_identity
  assoc := GeneralizedHepDerivor.comp_assoc

end CategorialAlgebras
