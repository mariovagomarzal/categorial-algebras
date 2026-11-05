import CategorialAlgebras.HepDerivor.Signature

/-!
# Generalized hep-derivors and transformed algebras

A generalized hep-derivor selects cells by existence equations in one variable.
Its transformed operations are defined by well-founded recursion on source symbols.
Their public characterization uses the domain conditions in the transformed algebra
itself, definedness of the interpreting term, and membership of its value in the cells.
-/

universe u v u' v' w w' x

namespace CategorialAlgebras

open CategoryTheory

namespace Word

/-- Family valuations commute with every sorted map, also after changing sorts. -/
theorem valuation_map {S : Type u} {T : Type u'} {φ : S → T} {a : List S}
    {A : T → Type w} {B : T → Type w'} (f : SortedSet.Map A B)
    (b : Family (fun s => A (φ s)) a) :
    (fun t z => f t (valuation b t z)) = valuation (fun j => f _ (b j)) := by
  funext t ⟨j, h⟩
  cases h
  rfl

/-- The valuation of a one-letter word assigning its unique position the value $b$. -/
def singletonValuation {S : Type u} {A : S → Type w} {s : S} (b : A s) :
    SortedSet.Map (Variables [s]) A :=
  valuation (φ := id) (w := [s]) (fun j => by simpa using b)

/-- Single-variable valuation commutes with every sorted map. -/
theorem singletonValuation_natural {S : Type u} {A : S → Type w} {B : S → Type w'}
    (f : SortedSet.Map A B) {s} (b : A s) :
    (fun t z => f t (singletonValuation b t z)) = singletonValuation (f s b) := by
  funext t ⟨j, h⟩
  have hj : j = 0 := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt))
  subst j
  cases h
  rfl

end Word

/-- A derivor equipped with a single-variable existence domain for each source sort. -/
structure GeneralizedHepDerivor {S : Type u} {T : Type u'}
    (sig : HepSignature.{u, v} S) (tau : HepSignature.{u', v'} T)
    extends Derivor sig.symbol tau.symbol where
  /-- The equations selecting cells of each source sort. -/
  domain : ∀ s, EEquationSet tau.symbol (Word.Variables [sortMap s])

namespace GeneralizedHepDerivor

variable {S : Type u} {T : Type u'} {sig : HepSignature.{u, v} S}
variable {tau : HepSignature.{u', v'} T}

/-! ## Cells and their functor -/

/-- An element is a cell when it satisfies the domain of its source sort. -/
def IsCell (c : GeneralizedHepDerivor sig tau) (B : PartialAlgebra.{u', v', w} tau.symbol)
    (s : S) (b : B.carrier (c.sortMap s)) : Prop :=
  EEquationSet.Satisfies B (Word.singletonValuation b) (c.domain s)

/-- The sorted carrier of cells. -/
def Cell (c : GeneralizedHepDerivor sig tau) (B : PartialAlgebra.{u', v', w} tau.symbol)
    (s : S) := {b : B.carrier (c.sortMap s) // c.IsCell B s b}

/-- Homomorphisms send cells to cells. -/
theorem isCell_map (c : GeneralizedHepDerivor sig tau)
    {B : PartialAlgebra.{u', v', w} tau.symbol} {B' : PartialAlgebra.{u', v', w'} tau.symbol}
    (f : PartialAlgebra.Hom B B') {s} {b : B.carrier (c.sortMap s)} (h : c.IsCell B s b) :
    c.IsCell B' s (f.toMap _ b) := by
  have hf := EEquationSet.satisfies_hom f (Word.singletonValuation b) (c.domain s) h
  rwa [Word.singletonValuation_natural] at hf

/-- The birrestriction of a homomorphism to the selected cells. -/
def cellMap (c : GeneralizedHepDerivor sig tau)
    {B : PartialAlgebra.{u', v', w} tau.symbol} {B' : PartialAlgebra.{u', v', w'} tau.symbol}
    (f : PartialAlgebra.Hom B B') : SortedSet.Map (c.Cell B) (c.Cell B') :=
  fun _ b => ⟨f.toMap _ b.val, c.isCell_map f b.property⟩

/-- The functor sending a partial algebra to its sorted set of cells. -/
def cellsFunctor (c : GeneralizedHepDerivor sig tau) :
    PartialAlgebra.{u', v', w} tau.symbol ⥤ SortedSet.{u, w} S where
  obj := c.Cell
  map f := SortedSet.homOfMap (c.cellMap f)

/-- With empty domains every element is a cell. -/
theorem isCell_of_empty (c : GeneralizedHepDerivor sig tau)
    (h : ∀ s, c.domain s = ⊥) (B : PartialAlgebra.{u', v', w} tau.symbol)
    (s : S) (b : B.carrier (c.sortMap s)) : c.IsCell B s b := by
  intro t e he
  rw [h s] at he
  exact he.elim

/-- With empty domains, forgetting the subtype of cells gives the usual change of sorts.
Both directions act identically on the underlying elements. -/
def cellsFunctorIsoDelta (c : GeneralizedHepDerivor sig tau) (h : ∀ s, c.domain s = ⊥) :
    cellsFunctor.{u, v, u', v', w} c ≅
      PartialAlgebra.forget tau.symbol ⋙ SortedSet.delta c.sortMap :=
  NatIso.ofComponents (fun B =>
    { hom := SortedSet.homOfMap (fun _ b => b.val)
      inv := SortedSet.homOfMap (fun s b => ⟨b, c.isCell_of_empty h B s b⟩) })

/-! ## Well-founded construction -/

/-- The interpreting term evaluated on the underlying elements of a family of cells. -/
def imageValue (c : GeneralizedHepDerivor sig tau) (B : PartialAlgebra.{u', v', w} tau.symbol)
    {a s} (σ : sig.symbol a s) (b : Word.Family (c.Cell B) a) :
    Part (B.carrier (c.sortMap s)) :=
  Term.partialEval (A := B) (Word.valuation (fun j => (b j).val)) (c.image σ)

/-- The type of a partial operation indexed by a bundled symbol. -/
private abbrev Operation (c : GeneralizedHepDerivor sig tau)
    (B : PartialAlgebra.{u', v', w} tau.symbol) (p : OperationSymbol sig.symbol) :=
  Word.Family (c.Cell B) p.1 → Part (c.Cell B p.2.1)

/-- Extend the previously constructed operations by undefined operations elsewhere. -/
private noncomputable def lowerAlgebra (c : GeneralizedHepDerivor sig tau)
    (B : PartialAlgebra.{u', v', w} tau.symbol) (p : OperationSymbol sig.symbol)
    (rec : ∀ q, sig.DependsOn q p → c.Operation B q) : PartialAlgebra sig.symbol where
  carrier := c.Cell B
  op {a s} σ := by
    classical
    exact if h : sig.DependsOn ⟨a, s, σ⟩ p then rec ⟨a, s, σ⟩ h else fun _ => Part.none

/-- The recursive step checks the lower domain conditions and selects a defined cell value. -/
private noncomputable def operationStep (c : GeneralizedHepDerivor sig tau)
    (B : PartialAlgebra.{u', v', w} tau.symbol) (p : OperationSymbol sig.symbol)
    (rec : ∀ q, sig.DependsOn q p → c.Operation B q) : c.Operation B p := fun b =>
  { Dom := b ∈ sig.domainSet (c.lowerAlgebra B p rec) p.2.2 ∧
      ∃ y : c.Cell B p.2.1, y.val ∈ c.imageValue B p.2.2 b
    get h := Classical.choose h.2 }

/-- Simultaneous construction of all operations by well-founded recursion. -/
private noncomputable def operation (c : GeneralizedHepDerivor sig tau)
    (B : PartialAlgebra.{u', v', w} tau.symbol) : ∀ p, c.Operation B p :=
  sig.wellFounded.fix (c.operationStep B)

/-- The partial algebra on cells obtained by recursion over domain dependencies. -/
noncomputable def transformed (c : GeneralizedHepDerivor sig tau)
    (B : PartialAlgebra.{u', v', w} tau.symbol) : PartialAlgebra sig.symbol where
  carrier := c.Cell B
  op {a s} σ := c.operation B ⟨a, s, σ⟩

/-- Completing the lower operations does not change satisfaction of the current domain. -/
private theorem lower_domain_iff (c : GeneralizedHepDerivor sig tau)
    (B : PartialAlgebra.{u', v', w} tau.symbol) (p : OperationSymbol sig.symbol)
    (b : Word.Family (c.Cell B) p.1) :
    b ∈ sig.domainSet (c.lowerAlgebra B p (fun q _ => c.operation B q)) p.2.2 ↔
      b ∈ sig.domainSet (c.transformed B) p.2.2 := by
  classical
  apply EEquationSet.satisfies_iff_of_symbols
  intro a s σ hσ z
  change (if h : sig.DependsOn ⟨a, s, σ⟩ p then c.operation B ⟨a, s, σ⟩
    else fun _ => Part.none) z = _
  split
  · rfl
  · rename_i h
    exact (h hσ).elim

/-- A transformed operation has value $y$ exactly when its domain conditions hold in
the transformed algebra itself and the interpreting term has underlying value $y$.
The subtype of $y$ supplies the third condition, that this value is a cell. -/
theorem mem_transformed_op (c : GeneralizedHepDerivor sig tau)
    (B : PartialAlgebra.{u', v', w} tau.symbol) {a s} (σ : sig.symbol a s)
    (b : Word.Family (c.Cell B) a) (y : c.Cell B s) :
    y ∈ (c.transformed B).op σ b ↔
      b ∈ sig.domainSet (c.transformed B) σ ∧ y.val ∈ c.imageValue B σ b := by
  change y ∈ c.operation B ⟨a, s, σ⟩ b ↔ _
  rw [operation, WellFounded.fix_eq]
  change (∃ h, Classical.choose h.2 = y) ↔ _
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨(c.lower_domain_iff B ⟨a, s, σ⟩ b).mp h.1, Classical.choose_spec h.2⟩
  · rintro ⟨hd, hy⟩
    have h : b ∈ sig.domainSet
        (c.lowerAlgebra B ⟨a, s, σ⟩ (fun q _ => c.operation B q)) σ ∧
        ∃ y : c.Cell B s, y.val ∈ c.imageValue B σ b :=
      ⟨(c.lower_domain_iff B ⟨a, s, σ⟩ b).mpr hd, y, hy⟩
    refine ⟨h, Subtype.ext ?_⟩
    exact Part.mem_unique (Classical.choose_spec h.2) hy

/-- The domain of a transformed operation expresses all three defining conditions. -/
theorem transformed_op_dom (c : GeneralizedHepDerivor sig tau)
    (B : PartialAlgebra.{u', v', w} tau.symbol) {a s} (σ : sig.symbol a s)
    (b : Word.Family (c.Cell B) a) :
    ((c.transformed B).op σ b).Dom ↔
      b ∈ sig.domainSet (c.transformed B) σ ∧
        ∃ h : (c.imageValue B σ b).Dom, c.IsCell B s ((c.imageValue B σ b).get h) := by
  constructor
  · intro h
    obtain ⟨hd, hy⟩ := (c.mem_transformed_op B σ b _).mp (Part.get_mem h)
    exact ⟨hd, hy.1, (Part.get_eq_of_mem hy hy.1).symm ▸
      (((c.transformed B).op σ b).get h).property⟩
  · rintro ⟨hd, hv, hc⟩
    exact ((c.mem_transformed_op B σ b ⟨_, hc⟩).mpr ⟨hd, Part.get_mem hv⟩).1

/-- Every transformed algebra is a weak ep-algebra. -/
theorem transformed_isWeak (c : GeneralizedHepDerivor sig tau)
    (B : PartialAlgebra.{u', v', w} tau.symbol) : sig.IsWeakEPAlgebra (c.transformed B) :=
  fun σ b h => ((c.transformed_op_dom B σ b).mp h).1

/-- The transformed algebra is an ep-algebra precisely when domain satisfaction
ensures that the interpreting term is defined and its value is a cell. -/
theorem transformed_isEPAlgebra_iff (c : GeneralizedHepDerivor sig tau)
    (B : PartialAlgebra.{u', v', w} tau.symbol) :
    sig.IsEPAlgebra (c.transformed B) ↔
      ∀ {a s} (σ : sig.symbol a s) (b : Word.Family (c.Cell B) a),
        b ∈ sig.domainSet (c.transformed B) σ →
        ∃ h : (c.imageValue B σ b).Dom, c.IsCell B s ((c.imageValue B σ b).get h) := by
  constructor
  · intro h a s σ b hd
    exact ((c.transformed_op_dom B σ b).mp ((h σ b).mpr hd)).2
  · intro h a s σ b
    exact ⟨c.transformed_isWeak B σ b, fun hd => (c.transformed_op_dom B σ b).mpr
      ⟨hd, h σ b hd⟩⟩

/-! ## The induced functors -/

/-- Homomorphisms preserve the values of interpreting terms on families of cells. -/
theorem imageValue_map (c : GeneralizedHepDerivor sig tau)
    {B : PartialAlgebra.{u', v', w} tau.symbol} {B' : PartialAlgebra.{u', v', w'} tau.symbol}
    (f : PartialAlgebra.Hom B B') {a s} (σ : sig.symbol a s)
    (b : Word.Family (c.Cell B) a) {q} (hq : q ∈ c.imageValue B σ b) :
    f.toMap _ q ∈ c.imageValue B' σ (fun j => c.cellMap f _ (b j)) := by
  have h := Term.partialEval_hom f (Word.valuation (fun j => (b j).val)) (c.image σ) hq
  rwa [Word.valuation_map] at h

/-- The birrestriction to cells preserves every transformed operation.
The proof uses well-founded induction, requiring preservation only at symbols
occurring in the current domain conditions. -/
theorem cellMap_mem_op (c : GeneralizedHepDerivor sig tau)
    {B : PartialAlgebra.{u', v', w} tau.symbol} {B' : PartialAlgebra.{u', v', w'} tau.symbol}
    (f : PartialAlgebra.Hom B B') {a s} (σ : sig.symbol a s)
    (b : Word.Family (c.Cell B) a) {y} (hy : y ∈ (c.transformed B).op σ b) :
    c.cellMap f s y ∈ (c.transformed B').op σ (fun j => c.cellMap f _ (b j)) := by
  have hall : ∀ p : OperationSymbol sig.symbol, ∀ (b : Word.Family (c.Cell B) p.1)
      (y : c.Cell B p.2.1), y ∈ (c.transformed B).op p.2.2 b →
      c.cellMap f _ y ∈ (c.transformed B').op p.2.2 (fun j => c.cellMap f _ (b j)) := by
    refine sig.symbol_induction (P := fun p => ∀ (b : Word.Family (c.Cell B) p.1)
      (y : c.Cell B p.2.1), y ∈ (c.transformed B).op p.2.2 b →
      c.cellMap f _ y ∈ (c.transformed B').op p.2.2 (fun j => c.cellMap f _ (b j))) ?_
    intro p ih b y hy
    obtain ⟨hd, hv⟩ := (c.mem_transformed_op B p.2.2 b y).mp hy
    apply (c.mem_transformed_op B' p.2.2 _ _).mpr
    refine ⟨?_, c.imageValue_map f p.2.2 b hv⟩
    have h := EEquationSet.satisfies_map_of_symbols
      (A := c.transformed B) (B := c.transformed B') (c.cellMap f)
      (Word.valuation (φ := id) b) (sig.domain p.2.2)
      (fun {a s} σ hσ z {q} hq => ih ⟨a, s, σ⟩ hσ z q hq) hd
    exact Eq.mp (congrArg
      (fun a => EEquationSet.Satisfies (c.transformed B') a (sig.domain p.2.2))
      (Word.valuation_map (φ := id) (c.cellMap f) b)) h
  exact hall ⟨a, s, σ⟩ b y hy

/-- A homomorphism induces a homomorphism of transformed algebras by birrestriction. -/
noncomputable def transformedHom (c : GeneralizedHepDerivor sig tau)
    {B : PartialAlgebra.{u', v', w} tau.symbol} {B' : PartialAlgebra.{u', v', w'} tau.symbol}
    (f : PartialAlgebra.Hom B B') : PartialAlgebra.Hom (c.transformed B) (c.transformed B') where
  toMap := c.cellMap f
  map_op := c.cellMap_mem_op f

/-- The functor induced by a generalized hep-derivor on all partial algebras. -/
noncomputable def transformedFunctor (c : GeneralizedHepDerivor sig tau) :
    PartialAlgebra.{u', v', w} tau.symbol ⥤ PartialAlgebra.{u, v, w} sig.symbol where
  obj := c.transformed
  map := c.transformedHom

/-- The forgetful triangle commutes strictly: the underlying functor is the cell functor. -/
@[simp] theorem transformedFunctor_comp_forget (c : GeneralizedHepDerivor sig tau) :
    transformedFunctor.{u, v, u', v', w} c ⋙ PartialAlgebra.forget sig.symbol =
      c.cellsFunctor := rfl

/-- The induced functor restricted and corestricted to weak ep-algebras. -/
noncomputable def weakFunctor (c : GeneralizedHepDerivor sig tau) :
    EPSignature.WEPAlg.{u', v', w} tau.toEPSignature ⥤ sig.toEPSignature.WEPAlg :=
  corestrict (restrict c.transformedFunctor tau.IsWeakEPAlgebra)
    sig.IsWeakEPAlgebra (fun B => c.transformed_isWeak B.obj)

/-- The weak-algebra functor agrees with the partial-algebra functor after inclusion. -/
@[simp] theorem weakFunctor_comp_inclusion (c : GeneralizedHepDerivor sig tau) :
    weakFunctor.{u, v, u', v', w} c ⋙ sig.weakInclusion =
      tau.weakInclusion ⋙ c.transformedFunctor := rfl

end GeneralizedHepDerivor
end CategorialAlgebras
