import CategorialAlgebras.HepDerivor.Category

/-!
# Comparisons between transformed algebras

Defined term values in a transformed algebra translate to defined values in the
original algebra. Successive transformations therefore include naturally in the
transformation by the composite. Identity transformations and transformations
selecting the same cells are identified by maps acting identically on underlying
elements.
-/

universe u v u' v' u'' v'' u''' v''' w w' x y z

namespace CategorialAlgebras

open CategoryTheory

namespace Term

/-- Evaluation of a family substitution agrees with evaluation at any family
realizing its substituted terms. -/
theorem partialEval_substFamily_of_mem {S : Type u} {R : Type z}
    {sig : Signature.{u, v} S} {X : S → Type x} {φ : R → S} {a : List R}
    {B : PartialAlgebra.{u, v, w} sig} (q : Word.Family (fun r => Term sig X (φ r)) a)
    (b : SortedSet.Map X B.carrier) (r : Word.Family (fun s => B.carrier (φ s)) a)
    (hq : ∀ j, r j ∈ partialEval b (q j)) {s}
    (p : Term sig (Word.MappedVariables φ a) s) :
    partialEval b (substFamily q p) = partialEval (Word.valuation r) p := by
  apply partialEval_subst_of_mem
  intro t ⟨j, h⟩
  cases h
  exact hq j

end Term

/-! ## Invertibility and ep-algebra structure -/

namespace HepSignature

/-- A bijective homomorphism from an ep-algebra to a weak ep-algebra is invertible.
Hierarchical induction reflects domain satisfaction through the inverse mapping. -/
theorem isIso_of_bijective {S : Type u} (sig : HepSignature.{u, v} S)
    {A B : PartialAlgebra.{u, v, w} sig.symbol} (hA : sig.IsEPAlgebra A)
    (hB : sig.IsWeakEPAlgebra B) (f : A ⟶ B)
    (hf : ∀ s, Function.Bijective (f.toMap s)) : IsIso f := by
  classical
  let e s := Equiv.ofBijective (f.toMap s) (hf s)
  have hall : ∀ p : OperationSymbol sig.symbol, ∀ (b : Word.Family B.carrier p.1) q,
      q ∈ B.op p.2.2 b →
      (e _).symm q ∈ A.op p.2.2 (fun j => (e _).symm (b j)) := by
    refine sig.symbol_induction ?_
    intro p ih b q hq
    have hd := hB p.2.2 b hq.1
    have hh := EEquationSet.satisfies_map_of_symbols (A := B) (B := A)
      (fun s => (e s).symm) (Word.valuation (φ := id) b) (sig.domain p.2.2)
      (fun {a s} σ hσ z {q} hq => ih ⟨a, s, σ⟩ hσ z q hq) hd
    have hdA : (A.op p.2.2 (fun j => (e _).symm (b j))).Dom :=
      (hA p.2.2 _).mpr (Eq.mp (congrArg
        (fun a => EEquationSet.Satisfies A a (sig.domain p.2.2))
        (Word.valuation_map (φ := id) (fun s => (e s).symm) b)) hh)
    have hm := f.map_op p.2.2 _ (Part.get_mem hdA)
    have he : (fun j => f.toMap _ ((e _).symm (b j))) = b :=
      funext (fun j => (e _).apply_symm_apply (b j))
    rw [he] at hm
    have hv : (e _).symm q = (A.op p.2.2 (fun j => (e _).symm (b j))).get hdA := by
      apply (e _).injective
      exact ((e _).apply_symm_apply q).trans (Part.mem_unique hq hm)
    rw [hv]
    exact Part.get_mem hdA
  apply (f.isIso_iff_inverse).mpr
  exact ⟨hf, ⟨fun s => (e s).symm, fun {a s} σ b {q} hq => hall ⟨_, _, σ⟩ b q hq⟩,
    fun s y => (e s).apply_symm_apply y⟩

end HepSignature

namespace EPSignature

/-- Ep-algebra structure is invariant under a partial-algebra isomorphism. -/
theorem isEPAlgebra_of_iso {S : Type u} (sig : EPSignature.{u, v} S)
    {A B : PartialAlgebra.{u, v, w} sig.symbol} (e : A ≅ B) (hA : sig.IsEPAlgebra A) :
    sig.IsEPAlgebra B := by
  intro a s σ b
  have hb : (fun j => e.hom.toMap _ (e.inv.toMap _ (b j))) = b := by
    funext j
    exact congrArg (fun f : B ⟶ B => f.toMap _ (b j)) e.inv_hom_id
  have toB (h : EEquationSet.Satisfies A
      (Word.valuation (φ := id) (fun j => e.inv.toMap _ (b j))) (sig.domain σ)) :
      b ∈ sig.domainSet B σ := by
    have hh := EEquationSet.satisfies_hom e.hom _ _ h
    have hv := Word.valuation_map (φ := id) e.hom.toMap
      (fun j => e.inv.toMap _ (b j))
    change _ = Word.valuation (φ := id) (fun j => e.hom.toMap _ (e.inv.toMap _ (b j))) at hv
    simp only [id_eq] at hv
    rw [hb] at hv
    exact Eq.mp (congrArg (fun v => EEquationSet.Satisfies B v (sig.domain σ)) hv) hh
  constructor
  · intro h
    exact toB ((hA σ _).mp (e.inv.map_dom σ b h))
  · intro h
    have hh := EEquationSet.satisfies_hom e.inv (Word.valuation (φ := id) b) _ h
    have hd : (A.op σ (fun j => e.inv.toMap _ (b j))).Dom :=
      (hA σ _).mpr (Eq.mp (congrArg
        (fun v => EEquationSet.Satisfies A v (sig.domain σ))
        (Word.valuation_map (φ := id) e.inv.toMap b)) hh)
    have hr := e.hom.map_dom σ _ hd
    rwa [hb] at hr

end EPSignature

namespace GeneralizedHepDerivor

variable {S : Type u} {T : Type u'} {U : Type u''}
variable {sig : HepSignature.{u, v} S} {tau : HepSignature.{u', v'} T}
variable {ups : HepSignature.{u'', v''} U}

/-! ## Translation of defined values and equations -/

/-- Every defined transformed term value is a value of its translated term.
The variable assignment may itself consist of arbitrary defined target terms. -/
theorem partialEval_translate (c : GeneralizedHepDerivor sig tau)
    (B : PartialAlgebra.{u', v', w} tau.symbol) {X : S → Type x} {Y : T → Type y}
    (a : SortedSet.Map X (c.Cell B)) (b : SortedSet.Map Y B.carrier)
    (f : ∀ s, X s → Term tau.symbol Y (c.sortMap s))
    (hf : ∀ s x, (a s x).val ∈ Term.partialEval b (f s x))
    {s} (p : Term sig.symbol X s) {q : c.Cell B s}
    (hq : q ∈ Term.partialEval (A := c.transformed B) a p) :
    q.val ∈ Term.partialEval b (c.translate f p) := by
  induction p with
  | var x =>
    have h := Part.mem_some_iff.mp hq
    exact h ▸ hf _ x
  | app σ p ih =>
    obtain ⟨r, hr, hq⟩ := (Term.mem_partialEval_app (A := c.transformed B) a σ p q).mp hq
    rw [Derivor.translate_app, Term.partialEval_substFamily_of_mem _ b
      (fun j => (r j).val) (fun j => ih j (hr j))]
    exact ((c.mem_transformed_op B σ r q).mp hq).2

/-- Defined term values translate on the positional variables of any input word. -/
theorem partialEval_translateWord (c : GeneralizedHepDerivor sig tau)
    (B : PartialAlgebra.{u', v', w} tau.symbol) (a : List S)
    (b : Word.Family (c.Cell B) a) {s}
    (p : Term sig.symbol (Word.Variables a) s) {q : c.Cell B s}
    (hq : q ∈ Term.partialEval (A := c.transformed B) (Word.valuation (φ := id) b) p) :
    q.val ∈ Term.partialEval (A := B) (Word.valuation (fun j => (b j).val))
      (c.translateWord a p) := by
  apply c.partialEval_translate B (Word.valuation (φ := id) b) _ _ ?_ p hq
  intro s ⟨j, h⟩
  cases h
  exact Part.mem_some _

/-- Satisfaction of positional existence equations implies satisfaction of their
translated sorted set. -/
theorem satisfies_translateWord (c : GeneralizedHepDerivor sig tau)
    (B : PartialAlgebra.{u', v', w} tau.symbol) (a : List S)
    (b : Word.Family (c.Cell B) a) (E : EEquationSet sig.symbol (Word.Variables a))
    (h : EEquationSet.Satisfies (c.transformed B) (Word.valuation (φ := id) b) E) :
    EEquationSet.Satisfies B (Word.valuation (fun j => (b j).val))
      (EEquationSet.translateWord c.toDerivor a E) := by
  rintro t e ⟨s, hs, p, hp, he⟩
  subst t
  subst e
  obtain ⟨q, hq, hr⟩ := h s p hp
  exact ⟨q.val, c.partialEval_translateWord B a b p.1 hq,
    c.partialEval_translateWord B a b p.2 hr⟩

/-- The unique variable keeps its assigned underlying value after singleton translation. -/
private theorem singleton_variable_value (c : GeneralizedHepDerivor sig tau)
    (B : PartialAlgebra.{u', v', w} tau.symbol) {s} (b : c.Cell B s)
    (t : S) (x : Word.Variables [s] t) :
    (Word.singletonValuation b t x).val =
      Word.singletonValuation b.val (c.sortMap t) (Word.singletonMap c.sortMap s t x) := by
  rcases x with ⟨j, h⟩
  have hj : j = 0 := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt))
  subst j
  cases h
  rfl

/-- Singleton equations satisfied by cells hold after translation in the original algebra. -/
theorem satisfies_translateSingletonSet (c : GeneralizedHepDerivor sig tau)
    (B : PartialAlgebra.{u', v', w} tau.symbol) {s} (b : c.Cell B s)
    (E : EEquationSet sig.symbol (Word.Variables [s]))
    (h : EEquationSet.Satisfies (c.transformed B) (Word.singletonValuation b) E) :
    EEquationSet.Satisfies B (Word.singletonValuation b.val)
      (c.translateSingletonSet s E) := by
  rintro t e ⟨r, hr, p, hp, he⟩
  subst t
  subst e
  obtain ⟨q, hq, hq'⟩ := h r p hp
  have hf t x : (Word.singletonValuation b t x).val ∈ Term.partialEval
      (A := B) (Word.singletonValuation b.val)
      (Term.var (Word.singletonMap c.sortMap s t x)) := by
    rw [Term.partialEval_var, Part.mem_some_iff]
    exact c.singleton_variable_value B b t x
  exact ⟨q.val, c.partialEval_translate B _ _ _ hf p.1 hq,
    c.partialEval_translate B _ _ _ hf p.2 hq'⟩

/-- A map from a weak ep-algebra to cells preserves transformed operations
provided it preserves the values of all interpreting terms. -/
theorem mem_op_of_imageValue (c : GeneralizedHepDerivor sig tau)
    (B : PartialAlgebra.{u', v', w} tau.symbol)
    {A : PartialAlgebra.{u, v, w'} sig.symbol} (hA : sig.IsWeakEPAlgebra A)
    (f : SortedSet.Map A.carrier (c.Cell B))
    (hf : ∀ {a s} (σ : sig.symbol a s) (b : Word.Family A.carrier a) {q},
      q ∈ A.op σ b → (f s q).val ∈ c.imageValue B σ (fun j => f _ (b j)))
    {a s} (σ : sig.symbol a s) (b : Word.Family A.carrier a) {q}
    (hq : q ∈ A.op σ b) : f s q ∈ (c.transformed B).op σ (fun j => f _ (b j)) := by
  have hall : ∀ p : OperationSymbol sig.symbol, ∀ b q,
      q ∈ A.op p.2.2 b → f _ q ∈ (c.transformed B).op p.2.2 (fun j => f _ (b j)) := by
    refine sig.symbol_induction ?_
    intro p ih b q hq
    apply (c.mem_transformed_op B p.2.2 _ _).mpr
    refine ⟨?_, hf p.2.2 b hq⟩
    have h := EEquationSet.satisfies_map_of_symbols (A := A) (B := c.transformed B)
      f (Word.valuation (φ := id) b) (sig.domain p.2.2)
      (fun {a s} σ hσ z {q} hq => ih ⟨a, s, σ⟩ hσ z q hq) (hA p.2.2 b hq.1)
    exact Eq.mp (congrArg
      (fun a => EEquationSet.Satisfies (c.transformed B) a (sig.domain p.2.2))
      (Word.valuation_map (φ := id) f b)) h
  exact hall ⟨a, s, σ⟩ b q hq

/-! ## Dependence on selected cells -/

/-- A generalized hep-derivor reconstructed from an underlying derivor and domains. -/
abbrev withDomains (c : Derivor sig.symbol tau.symbol)
    (D : ∀ s, EEquationSet tau.symbol (Word.Variables [c.sortMap s])) :
    GeneralizedHepDerivor sig tau := ⟨c, D⟩

/-- Equal selected cells for a common derivor give a homomorphism acting identically
on the underlying elements. Only inclusion of the first cell set is required. -/
noncomputable def sameCellsHom (c : Derivor sig.symbol tau.symbol)
    (D D' : ∀ s, EEquationSet tau.symbol (Word.Variables [c.sortMap s]))
    (B : PartialAlgebra.{u', v', w} tau.symbol)
    (h : ∀ s b, (withDomains c D).IsCell B s b → (withDomains c D').IsCell B s b) :
    (withDomains c D).transformed B ⟶ (withDomains c D').transformed B where
  toMap s b := ⟨b.val, h s b.val b.property⟩
  map_op σ b _ hq := (withDomains c D').mem_op_of_imageValue B
    ((withDomains c D).transformed_isWeak B)
    (fun s b => ⟨b.val, h s b.val b.property⟩)
    (fun {_a _s} σ b {_q} hq => ((withDomains c D).mem_transformed_op B σ b _).mp hq |>.2) σ b hq

/-- Domains selecting the same cells give isomorphic transformed algebras.
Both directions are identities on underlying elements. -/
noncomputable def sameCellsIso (c : Derivor sig.symbol tau.symbol)
    (D D' : ∀ s, EEquationSet tau.symbol (Word.Variables [c.sortMap s]))
    (B : PartialAlgebra.{u', v', w} tau.symbol)
    (h : ∀ s b, (withDomains c D).IsCell B s b ↔ (withDomains c D').IsCell B s b) :
    (withDomains c D).transformed B ≅ (withDomains c D').transformed B where
  hom := sameCellsHom c D D' B (fun s b => (h s b).mp)
  inv := sameCellsHom c D' D B (fun s b => (h s b).mpr)
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The identification of equal cells commutes with transformed homomorphisms. -/
theorem sameCellsIso_naturality (c : Derivor sig.symbol tau.symbol)
    (D D' : ∀ s, EEquationSet tau.symbol (Word.Variables [c.sortMap s]))
    {B B' : PartialAlgebra.{u', v', w} tau.symbol} (f : B ⟶ B')
    (h : ∀ s b, (withDomains c D).IsCell B s b ↔ (withDomains c D').IsCell B s b)
    (h' : ∀ s b, (withDomains c D).IsCell B' s b ↔ (withDomains c D').IsCell B' s b) :
    (withDomains c D).transformedHom f ≫ (sameCellsIso c D D' B' h').hom =
      (sameCellsIso c D D' B h).hom ≫ (withDomains c D').transformedHom f := rfl

/-- Equal cell sets throughout a subcategory give a natural identification of
its two transformed-algebra functors. -/
noncomputable def sameCellsNatIso (c : Derivor sig.symbol tau.symbol)
    (D D' : ∀ s, EEquationSet tau.symbol (Word.Variables [c.sortMap s]))
    (P : ObjectProperty (PartialAlgebra.{u', v', w} tau.symbol))
    (h : ∀ B, P B → ∀ s b,
      (withDomains c D).IsCell B s b ↔ (withDomains c D').IsCell B s b) :
    restrict (withDomains c D).transformedFunctor P ≅
      restrict (withDomains c D').transformedFunctor P :=
  NatIso.ofComponents (fun B => sameCellsIso c D D' B.obj (h B.obj B.property))
    (fun f => sameCellsIso_naturality c D D' f.hom _ _)

/-- Equal underlying derivors and equal selected cells identify transformed algebras.
The cast only changes the sort index along the equality of underlying derivors. -/
noncomputable def sameDerivorIso (c c' : GeneralizedHepDerivor sig tau)
    (h : c.toDerivor = c'.toDerivor) (B : PartialAlgebra.{u', v', w} tau.symbol)
    (hc : ∀ s b, c.IsCell B s b ↔ c'.IsCell B s
      (cast (congrArg (fun p : Derivor sig.symbol tau.symbol => B.carrier (p.sortMap s)) h) b)) :
    c.transformed B ≅ c'.transformed B := by
  rcases c with ⟨c, D⟩
  rcases c' with ⟨c', D'⟩
  cases h
  exact sameCellsIso c D D' B hc

/-- The identification for equal underlying derivors commutes with all homomorphisms
whose source and target have the same selected cells. -/
theorem sameDerivorIso_naturality (c c' : GeneralizedHepDerivor sig tau)
    (h : c.toDerivor = c'.toDerivor) {B B' : PartialAlgebra.{u', v', w} tau.symbol}
    (f : B ⟶ B')
    (hc : ∀ s b, c.IsCell B s b ↔ c'.IsCell B s
      (cast (congrArg (fun p : Derivor sig.symbol tau.symbol => B.carrier (p.sortMap s)) h) b))
    (hc' : ∀ s b, c.IsCell B' s b ↔ c'.IsCell B' s
      (cast (congrArg (fun p : Derivor sig.symbol tau.symbol => B'.carrier (p.sortMap s)) h) b)) :
    c.transformedHom f ≫ (sameDerivorIso c c' h B' hc').hom =
      (sameDerivorIso c c' h B hc).hom ≫ c'.transformedHom f := by
  rcases c with ⟨c, D⟩
  rcases c' with ⟨c', D'⟩
  cases h
  rfl

/-- Equal derivors selecting the same cells throughout a subcategory induce
naturally isomorphic restricted functors. -/
noncomputable def sameDerivorNatIso (c c' : GeneralizedHepDerivor sig tau)
    (h : c.toDerivor = c'.toDerivor)
    (P : ObjectProperty (PartialAlgebra.{u', v', w} tau.symbol))
    (hc : ∀ B, P B → ∀ s b, c.IsCell B s b ↔ c'.IsCell B s
      (cast (congrArg (fun p : Derivor sig.symbol tau.symbol => B.carrier (p.sortMap s)) h) b)) :
    restrict c.transformedFunctor P ≅ restrict c'.transformedFunctor P :=
  NatIso.ofComponents (fun B => sameDerivorIso c c' h B.obj (hc B.obj B.property))
    (fun f => sameDerivorIso_naturality c c' h f.hom _ _)

/-! ## Identity reindexing -/

/-- The interpreting term of the identity derivor is the basic partial operation. -/
theorem identity_imageValue (A : PartialAlgebra.{u, v, w} sig.symbol)
    {a s} (σ : sig.symbol a s) (b : Word.Family ((identity sig).Cell A) a) :
    (identity sig).imageValue A σ b = A.op σ (fun j => (b j).val) := by
  apply Part.ext
  intro y
  rw [imageValue, Term.mem_partialEval_app]
  constructor
  · rintro ⟨r, hr, hy⟩
    have he : r = fun j => (b j).val := funext (fun j => Part.mem_some_iff.mp (hr j))
    rwa [he] at hy
  · intro hy
    exact ⟨_, fun _ => Part.mem_some _, hy⟩

/-- Forgetting the identity cell proof is a homomorphism on every partial algebra. -/
noncomputable def identityForget (A : PartialAlgebra.{u, v, w} sig.symbol) :
    (identity sig).transformed A ⟶ A where
  toMap _ := Subtype.val
  map_op σ b _ hq := by
    have h := ((identity sig).mem_transformed_op A σ b _).mp hq |>.2
    rwa [identity_imageValue (sig := sig) A σ b] at h

/-- Every element belongs to the unrestricted identity cell set. -/
def identityCell (A : PartialAlgebra.{u, v, w} sig.symbol) (s : S)
    (b : A.carrier s) : (identity sig).Cell A s :=
  ⟨b, (identity sig).isCell_of_empty (fun _ => rfl) A s b⟩

/-- Adding the identity cell proof preserves operations of a weak ep-algebra. -/
noncomputable def identityLift (A : PartialAlgebra.{u, v, w} sig.symbol)
    (hA : sig.IsWeakEPAlgebra A) : A ⟶ (identity sig).transformed A where
  toMap := identityCell A
  map_op σ b _ hq := (identity sig).mem_op_of_imageValue A hA
    (identityCell A)
    (fun {a s} σ b {q} hq => by
      rw [identity_imageValue (sig := sig) A σ (fun j => identityCell A _ (b j))]
      exact hq) σ b hq

/-- Identity reindexing is isomorphic to the original weak ep-algebra by adding
and removing cell proofs. These maps are identities on underlying elements. -/
noncomputable def identityIso (A : PartialAlgebra.{u, v, w} sig.symbol)
    (hA : sig.IsWeakEPAlgebra A) : A ≅ (identity sig).transformed A where
  hom := identityLift A hA
  inv := identityForget A
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The invertible unit of reindexing on weak ep-algebras.
It expresses strict normality after identifying cell subtypes with their elements. -/
noncomputable def weakIdentityIso (sig : HepSignature.{u, v} S) :
    𝟭 (EPSignature.WEPAlg.{u, v, w} sig.toEPSignature) ≅ (identity sig).weakFunctor :=
  NatIso.ofComponents (fun A => ObjectProperty.isoMk _ (identityIso A.obj A.property))

/-- Identity transformation preserves ep-algebras. -/
theorem identity_isEPAlgebra (A : PartialAlgebra.{u, v, w} sig.symbol)
    (hA : sig.IsEPAlgebra A) : sig.IsEPAlgebra ((identity sig).transformed A) :=
  sig.toEPSignature.isEPAlgebra_of_iso (identityIso A hA.isWeak) hA

/-- Identity reindexing restricted and corestricted to ep-algebras. -/
noncomputable def epIdentityFunctor (sig : HepSignature.{u, v} S) :
    EPSignature.EPAlg.{u, v, w} sig.toEPSignature ⥤ sig.toEPSignature.EPAlg :=
  corestrict (restrict (identity sig).transformedFunctor sig.IsEPAlgebra)
    sig.IsEPAlgebra (fun A => identity_isEPAlgebra A.obj A.property)

/-- The identity transformation induces the identity on ep-algebras up to the
canonical identification of cell subtypes. -/
noncomputable def epIdentityIso (sig : HepSignature.{u, v} S) :
    𝟭 (EPSignature.EPAlg.{u, v, w} sig.toEPSignature) ≅ epIdentityFunctor sig :=
  NatIso.ofComponents (fun A => ObjectProperty.isoMk _ (identityIso A.obj
    (EPSignature.IsEPAlgebra.isWeak (sig := sig.toEPSignature) A.property)))

/-! ## The composition comparison -/

/-- A cell of successive transformations is a cell for the composite. -/
theorem isCell_comp (c : GeneralizedHepDerivor sig tau) (d : GeneralizedHepDerivor tau ups)
    (C : PartialAlgebra.{u'', v'', w} ups.symbol) {s}
    (x : c.Cell (d.transformed C) s) : (c.comp d).IsCell C s x.val.val := by
  intro t e he
  rcases he with he | he
  · exact x.val.property t e he
  · exact d.satisfies_translateSingletonSet C x.val (c.domain s) x.property t e he

/-- The inclusion of iterated cells into composite cells. -/
def comparisonMap (c : GeneralizedHepDerivor sig tau) (d : GeneralizedHepDerivor tau ups)
    (C : PartialAlgebra.{u'', v'', w} ups.symbol) :
    SortedSet.Map (c.Cell (d.transformed C)) ((c.comp d).Cell C) :=
  fun _ x => ⟨x.val.val, c.isCell_comp d C x⟩

/-- The comparison acts as the identity on underlying elements. -/
@[simp] theorem comparisonMap_val (c : GeneralizedHepDerivor sig tau)
    (d : GeneralizedHepDerivor tau ups) (C : PartialAlgebra.{u'', v'', w} ups.symbol)
    {s} (x : c.Cell (d.transformed C) s) : (c.comparisonMap d C s x).val = x.val.val := rfl

/-- Interpreting a symbol successively preserves its value under composite translation. -/
theorem imageValue_comp (c : GeneralizedHepDerivor sig tau)
    (d : GeneralizedHepDerivor tau ups) (C : PartialAlgebra.{u'', v'', w} ups.symbol)
    {a s} (σ : sig.symbol a s) (b : Word.Family (c.Cell (d.transformed C)) a)
    {q : d.Cell C (c.sortMap s)} (hq : q ∈ c.imageValue (d.transformed C) σ b) :
    q.val ∈ (c.comp d).imageValue C σ (fun j => c.comparisonMap d C _ (b j)) := by
  apply d.partialEval_translate C (Word.valuation (fun j => (b j).val)) _ _ ?_ (c.image σ) hq
  intro t ⟨j, h⟩
  cases h
  exact Part.mem_some _

/-- The inclusion of iterated cells preserves the transformed operations. -/
theorem comparisonMap_mem_op (c : GeneralizedHepDerivor sig tau)
    (d : GeneralizedHepDerivor tau ups) (C : PartialAlgebra.{u'', v'', w} ups.symbol)
    {a s} (σ : sig.symbol a s) (b : Word.Family (c.Cell (d.transformed C)) a)
    {q} (hq : q ∈ (c.transformed (d.transformed C)).op σ b) :
    c.comparisonMap d C s q ∈ ((c.comp d).transformed C).op σ
      (fun j => c.comparisonMap d C _ (b j)) := by
  have hall : ∀ p : OperationSymbol sig.symbol, ∀ b q,
      q ∈ (c.transformed (d.transformed C)).op p.2.2 b →
      c.comparisonMap d C _ q ∈ ((c.comp d).transformed C).op p.2.2
        (fun j => c.comparisonMap d C _ (b j)) := by
    refine sig.symbol_induction ?_
    intro p ih b q hq
    obtain ⟨hd, hv⟩ := (c.mem_transformed_op _ p.2.2 b q).mp hq
    apply ((c.comp d).mem_transformed_op C p.2.2 _ _).mpr
    refine ⟨?_, c.imageValue_comp d C p.2.2 b hv⟩
    have h := EEquationSet.satisfies_map_of_symbols
      (A := c.transformed (d.transformed C)) (B := (c.comp d).transformed C)
      (c.comparisonMap d C) (Word.valuation (φ := id) b) (sig.domain p.2.2)
      (fun {a s} σ hσ z {q} hq => ih ⟨a, s, σ⟩ hσ z q hq) hd
    exact Eq.mp (congrArg
      (fun a => EEquationSet.Satisfies ((c.comp d).transformed C) a (sig.domain p.2.2))
      (Word.valuation_map (φ := id) (c.comparisonMap d C) b)) h
  exact hall ⟨a, s, σ⟩ b q hq

/-- The natural comparison homomorphism $\kappa$ from successive to composite transformation. -/
noncomputable def comparison (c : GeneralizedHepDerivor sig tau)
    (d : GeneralizedHepDerivor tau ups) (C : PartialAlgebra.{u'', v'', w} ups.symbol) :
    c.transformed (d.transformed C) ⟶ (c.comp d).transformed C where
  toMap := c.comparisonMap d C
  map_op := c.comparisonMap_mem_op d C

/-- Naturality of the comparison homomorphism in the original partial algebra. -/
theorem comparison_naturality (c : GeneralizedHepDerivor sig tau)
    (d : GeneralizedHepDerivor tau ups)
    {C C' : PartialAlgebra.{u'', v'', w} ups.symbol} (f : C ⟶ C') :
    c.transformedHom (d.transformedHom f) ≫ c.comparison d C' =
      c.comparison d C ≫ (c.comp d).transformedHom f := rfl

/-- Comparison as a natural transformation of partial-algebra functors. -/
noncomputable def comparisonNat (c : GeneralizedHepDerivor sig tau)
    (d : GeneralizedHepDerivor tau ups) :
    d.transformedFunctor ⋙ c.transformedFunctor ⟶ (c.comp d).transformedFunctor where
  app := c.comparison d
  naturality _ _ f := c.comparison_naturality d f

/-! ## Invertible comparisons and squares of functors -/

/-- The comparison is injective on cells. -/
theorem comparison_injective (c : GeneralizedHepDerivor sig tau)
    (d : GeneralizedHepDerivor tau ups) (C : PartialAlgebra.{u'', v'', w} ups.symbol)
    (s : S) : Function.Injective ((c.comparison d C).toMap s) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : (c.comp d).Cell C s => z.val) h

/-- A sufficient condition for the comparison to be an identity on elements:
its cell inclusion is surjective and the iterated transformation is an ep-algebra. -/
theorem comparison_isIso (c : GeneralizedHepDerivor sig tau)
    (d : GeneralizedHepDerivor tau ups) (C : PartialAlgebra.{u'', v'', w} ups.symbol)
    (hc : ∀ s, Function.Surjective ((c.comparison d C).toMap s))
    (hA : sig.IsEPAlgebra (c.transformed (d.transformed C))) :
    IsIso (c.comparison d C) :=
  sig.isIso_of_bijective hA ((c.comp d).transformed_isWeak C) (c.comparison d C)
    (fun s => ⟨c.comparison_injective d C s, hc s⟩)

/-- Canonical isomorphism when successive and composite transformations have the
same cells and the successive transformation is an ep-algebra. -/
noncomputable def comparisonIso (c : GeneralizedHepDerivor sig tau)
    (d : GeneralizedHepDerivor tau ups) (C : PartialAlgebra.{u'', v'', w} ups.symbol)
    (hc : ∀ s, Function.Surjective ((c.comparison d C).toMap s))
    (hA : sig.IsEPAlgebra (c.transformed (d.transformed C))) :
    c.transformed (d.transformed C) ≅ (c.comp d).transformed C := by
  letI := c.comparison_isIso d C hc hA
  exact asIso (c.comparison d C)

/-- The canonical comparison isomorphism is the cell inclusion. -/
@[simp] theorem comparisonIso_hom (c : GeneralizedHepDerivor sig tau)
    (d : GeneralizedHepDerivor tau ups) (C : PartialAlgebra.{u'', v'', w} ups.symbol)
    (hc : ∀ s, Function.Surjective ((c.comparison d C).toMap s))
    (hA : sig.IsEPAlgebra (c.transformed (d.transformed C))) :
    (c.comparisonIso d C hc hA).hom = c.comparison d C := rfl

/-- The inverse of an invertible comparison also retains the underlying element. -/
@[simp] theorem comparisonIso_inv_val (c : GeneralizedHepDerivor sig tau)
    (d : GeneralizedHepDerivor tau ups) (C : PartialAlgebra.{u'', v'', w} ups.symbol)
    (hc : ∀ s, Function.Surjective ((c.comparison d C).toMap s))
    (hA : sig.IsEPAlgebra (c.transformed (d.transformed C)))
    (s : S) (x : (c.comp d).Cell C s) :
    (((c.comparisonIso d C hc hA).inv.toMap s x).val).val = x.val :=
  congrArg (fun f : (c.comp d).transformed C ⟶ (c.comp d).transformed C =>
    (f.toMap s x).val) (c.comparisonIso d C hc hA).inv_hom_id

/-- Surjectivity of the cell inclusion is exactly reflection of the translated
first-domain equations on the cells of the second derivor. -/
theorem comparison_surjective_iff (c : GeneralizedHepDerivor sig tau)
    (d : GeneralizedHepDerivor tau ups) (C : PartialAlgebra.{u'', v'', w} ups.symbol) :
    (∀ s, Function.Surjective ((c.comparison d C).toMap s)) ↔
      ∀ s (x : d.Cell C (c.sortMap s)),
        EEquationSet.Satisfies C (Word.singletonValuation x.val)
          (d.translateSingletonSet (c.sortMap s) (c.domain s)) →
        c.IsCell (d.transformed C) s x := by
  constructor
  · intro h s x hx
    let y : (c.comp d).Cell C s := ⟨x.val, fun t e he => he.elim
      (x.property t e) (hx t e)⟩
    obtain ⟨z, hz⟩ := h s y
    have he : z.val = x := Subtype.ext (congrArg (fun z : (c.comp d).Cell C s => z.val) hz)
    exact he ▸ z.property
  · intro h s x
    let y : d.Cell C (c.sortMap s) := ⟨x.val, fun t e he => x.property t e (Or.inl he)⟩
    refine ⟨⟨y, h s y (fun t e he => x.property t e (Or.inr he))⟩, ?_⟩
    rfl

/-- Empty first domains ensure equality of successive and composite cell sets. -/
theorem comparison_surjective_of_empty (c : GeneralizedHepDerivor sig tau)
    (d : GeneralizedHepDerivor tau ups) (C : PartialAlgebra.{u'', v'', w} ups.symbol)
    (hc : ∀ s, c.domain s = ⊥) :
    ∀ s, Function.Surjective ((c.comparison d C).toMap s) :=
  (c.comparison_surjective_iff d C).mpr
    (fun s x _ => c.isCell_of_empty hc (d.transformed C) s x)

/-- The comparison is a natural isomorphism on any subcategory satisfying
cell equality and the ep-algebra condition for successive transformations. -/
noncomputable def comparisonNatIso (c : GeneralizedHepDerivor sig tau)
    (d : GeneralizedHepDerivor tau ups)
    (P : ObjectProperty (PartialAlgebra.{u'', v'', w} ups.symbol))
    (hc : ∀ C, P C → ∀ s, Function.Surjective ((c.comparison d C).toMap s))
    (hA : ∀ C, P C → sig.IsEPAlgebra (c.transformed (d.transformed C))) :
    restrict (d.transformedFunctor ⋙ c.transformedFunctor) P ≅
      restrict (c.comp d).transformedFunctor P :=
  NatIso.ofComponents (fun C => c.comparisonIso d C.obj (hc C.obj C.property) (hA C.obj C.property))
    (fun f => c.comparison_naturality d f.hom)

/-- A square of induced functors commutes up to a natural isomorphism when both
successive transformations are ep-algebras with the composite cells, and the
composite derivors agree and select the same cells. -/
noncomputable def squareNatIso {T' : Type u'''} {tau' : HepSignature.{u''', v'''} T'}
    (c : GeneralizedHepDerivor sig tau) (d : GeneralizedHepDerivor tau ups)
    (c' : GeneralizedHepDerivor sig tau') (d' : GeneralizedHepDerivor tau' ups)
    (h : (c.comp d).toDerivor = (c'.comp d').toDerivor)
    (P : ObjectProperty (PartialAlgebra.{u'', v'', w} ups.symbol))
    (hc : ∀ C, P C → ∀ s, Function.Surjective ((c.comparison d C).toMap s))
    (hc' : ∀ C, P C → ∀ s, Function.Surjective ((c'.comparison d' C).toMap s))
    (hA : ∀ C, P C → sig.IsEPAlgebra (c.transformed (d.transformed C)))
    (hA' : ∀ C, P C → sig.IsEPAlgebra (c'.transformed (d'.transformed C)))
    (hcell : ∀ C, P C → ∀ s b, (c.comp d).IsCell C s b ↔ (c'.comp d').IsCell C s
      (cast (congrArg (fun p : Derivor sig.symbol ups.symbol => C.carrier (p.sortMap s)) h) b)) :
    restrict (d.transformedFunctor ⋙ c.transformedFunctor) P ≅
      restrict (d'.transformedFunctor ⋙ c'.transformedFunctor) P :=
  c.comparisonNatIso d P hc hA ≪≫ sameDerivorNatIso (c.comp d) (c'.comp d') h P hcell ≪≫
    (c'.comparisonNatIso d' P hc' hA').symm

end GeneralizedHepDerivor
end CategorialAlgebras
