import CategorialAlgebras.HepDerivor.Symbols
import CategorialAlgebras.Preliminaries.Corestriction

/-!
# Equationally partial signatures and specifications

Domain conditions are existence equations in the positions of an input word.
Ep-algebras have exactly these domains; weak ep-algebras may have smaller domains.
Hierarchical signatures have a well-founded dependency relation on symbols.
Specifications retain a separate finite variable context for every axiom.
-/

universe u v w x

namespace CategorialAlgebras

open CategoryTheory

/-- An equationally partial signature, with existence conditions for each operation. -/
structure EPSignature (S : Type u) where
  /-- The underlying many-sorted signature. -/
  symbol : Signature.{u, v} S
  /-- The domain conditions, in the positions of the input word. -/
  domain : ∀ {a s}, symbol a s → EEquationSet symbol (Word.Variables a)

namespace EPSignature

variable {S : Type u}

/-- The families satisfying the domain conditions of a symbol in $A$ itself. -/
def domainSet (sig : EPSignature.{u, v} S) (A : PartialAlgebra.{u, v, w} sig.symbol)
    {a s} (σ : sig.symbol a s) : Set (Word.Family A.carrier a) :=
  {z | EEquationSet.Satisfies A (Word.valuation (φ := id) z) (sig.domain σ)}

/-- In an ep-algebra, definedness is equivalent to satisfaction of domain conditions. -/
def IsEPAlgebra (sig : EPSignature.{u, v} S) (A : PartialAlgebra.{u, v, w} sig.symbol) :
    Prop := ∀ {a s} (σ : sig.symbol a s) z, (A.op σ z).Dom ↔ z ∈ sig.domainSet A σ

/-- In a weak ep-algebra, definedness implies satisfaction of domain conditions. -/
def IsWeakEPAlgebra (sig : EPSignature.{u, v} S)
    (A : PartialAlgebra.{u, v, w} sig.symbol) : Prop :=
  ∀ {a s} (σ : sig.symbol a s) z, (A.op σ z).Dom → z ∈ sig.domainSet A σ

/-- Every ep-algebra is a weak ep-algebra. -/
theorem IsEPAlgebra.isWeak {sig : EPSignature.{u, v} S}
    {A : PartialAlgebra.{u, v, w} sig.symbol} (h : sig.IsEPAlgebra A) :
    sig.IsWeakEPAlgebra A := fun σ z => (h σ z).mp

/-- The full category of ep-algebras with carriers in a fixed universe. -/
abbrev EPAlg (sig : EPSignature.{u, v} S) :=
  ObjectProperty.FullSubcategory
    (sig.IsEPAlgebra : ObjectProperty (PartialAlgebra.{u, v, w} sig.symbol))

/-- The full category of weak ep-algebras with carriers in a fixed universe. -/
abbrev WEPAlg (sig : EPSignature.{u, v} S) :=
  ObjectProperty.FullSubcategory
    (sig.IsWeakEPAlgebra : ObjectProperty (PartialAlgebra.{u, v, w} sig.symbol))

/-- Inclusion of ep-algebras into partial algebras. -/
def inclusion (sig : EPSignature.{u, v} S) : sig.EPAlg ⥤ PartialAlgebra.{u, v, w} sig.symbol :=
  ObjectProperty.ι _

/-- Inclusion of weak ep-algebras into partial algebras. -/
def weakInclusion (sig : EPSignature.{u, v} S) :
    sig.WEPAlg ⥤ PartialAlgebra.{u, v, w} sig.symbol := ObjectProperty.ι _

/-- The inclusion of ep-algebras is fully faithful. -/
def inclusionFullyFaithful (sig : EPSignature.{u, v} S) :
    (inclusion.{u, v, w} sig).FullyFaithful := ObjectProperty.fullyFaithfulι _

/-- The inclusion of weak ep-algebras is fully faithful. -/
def weakInclusionFullyFaithful (sig : EPSignature.{u, v} S) :
    (weakInclusion.{u, v, w} sig).FullyFaithful := ObjectProperty.fullyFaithfulι _

/-- The inclusion of ep-algebras into weak ep-algebras. -/
def toWeak (sig : EPSignature.{u, v} S) : EPAlg.{u, v, w} sig ⥤ sig.WEPAlg :=
  corestrict sig.inclusion sig.IsWeakEPAlgebra (fun A => IsEPAlgebra.isWeak A.property)

/-- The inclusion from ep-algebras to weak ep-algebras is fully faithful. -/
def toWeakFullyFaithful (sig : EPSignature.{u, v} S) :
    (toWeak.{u, v, w} sig).FullyFaithful where
  preimage f := ObjectProperty.homMk f.hom

/-- Forgetting that an ep-algebra is weak recovers its partial algebra. -/
@[simp] theorem toWeak_comp_inclusion (sig : EPSignature.{u, v} S) :
    toWeak.{u, v, w} sig ⋙ sig.weakInclusion = sig.inclusion := rfl

/-- A many-sorted signature as an ep-signature with empty domain conditions. -/
abbrev ofSignature (sig : Signature.{u, v} S) : EPSignature S :=
  ⟨sig, fun _ _ => ∅⟩

/-- Empty domain conditions characterize precisely everywhere defined operations.

**Formally weaker** than the informal statement. Informally, the category of ep-algebras of a
signature without domain conditions is the category of total algebras; here only their objects are
identified: an ep-algebra is a partial algebra whose operations are all total. -/
theorem ofSignature_isEPAlgebra_iff (sig : Signature.{u, v} S)
    (A : PartialAlgebra.{u, v, w} sig) :
    (ofSignature sig).IsEPAlgebra A ↔ ∀ {a s} (σ : sig a s) z, (A.op σ z).Dom := by
  constructor
  · intro h a s σ z
    exact (h σ z).mpr (fun _ _ he => he.elim)
  · intro h a s σ z
    exact ⟨fun _ _ _ he => he.elim, fun _ => h σ z⟩

/-- Total algebras satisfy the ep-signature with empty domain conditions. -/
theorem ofSignature_ofAlgebra (sig : Signature.{u, v} S) (A : Algebra.{u, v, w} sig) :
    (ofSignature sig).IsEPAlgebra (PartialAlgebra.ofAlgebra A) :=
  (ofSignature_isEPAlgebra_iff sig _).mpr (fun _ _ => Part.some_dom _)

/-- Recover a total algebra from an ep-algebra with empty domain conditions. -/
def toAlgebra (sig : Signature.{u, v} S) (A : PartialAlgebra.{u, v, w} sig)
    (h : (ofSignature sig).IsEPAlgebra A) : Algebra sig where
  carrier := A.carrier
  op σ z := (A.op σ z).get ((ofSignature_isEPAlgebra_iff sig A).mp h σ z)

/-- Recovering a total algebra preserves the original partial operations. -/
theorem ofAlgebra_toAlgebra (sig : Signature.{u, v} S) (A : PartialAlgebra.{u, v, w} sig)
    (h : (ofSignature sig).IsEPAlgebra A) :
    PartialAlgebra.ofAlgebra (toAlgebra sig A h) = A := by
  cases A with
  | mk C op =>
    apply congrArg (PartialAlgebra.mk C)
    funext a s σ z
    exact (Part.eq_some_iff.mpr (Part.get_mem _)).symm

/-- Recovering the total operations of a total algebra returns that algebra. -/
@[simp] theorem toAlgebra_ofAlgebra (sig : Signature.{u, v} S) (A : Algebra.{u, v, w} sig) :
    toAlgebra sig (PartialAlgebra.ofAlgebra A) (ofSignature_ofAlgebra sig A) = A := rfl

/-- A symbol depends on another when the latter occurs in its domain conditions. -/
def DependsOn (sig : EPSignature.{u, v} S) (τ σ : OperationSymbol sig.symbol) : Prop :=
  τ ∈ EEquationSet.symbols (sig.domain σ.2.2)

end EPSignature

/-- A hierarchical ep-signature has well-founded domain dependencies. -/
structure HepSignature (S : Type u) extends EPSignature.{u, v} S where
  /-- Well-foundedness of the dependency relation on all symbols. -/
  wellFounded : WellFounded toEPSignature.DependsOn

namespace HepSignature

variable {S : Type u}

/-- Well-founded induction on symbols, with all domain dependencies as hypotheses. -/
theorem symbol_induction (sig : HepSignature.{u, v} S)
    {P : OperationSymbol sig.symbol → Prop}
    (step : ∀ σ, (∀ τ, sig.DependsOn τ σ → P τ) → P σ) : ∀ σ, P σ :=
  fun σ => sig.wellFounded.induction σ step

/-- A symbol never occurs in its own domain conditions. -/
theorem not_dependsOn_self (sig : HepSignature.{u, v} S)
    (σ : OperationSymbol sig.symbol) : ¬ sig.DependsOn σ σ :=
  sig.wellFounded.irrefl.irrefl σ

/-- Every signature with empty domain conditions is hierarchical. -/
abbrev ofSignature (sig : Signature.{u, v} S) : HepSignature S where
  toEPSignature := EPSignature.ofSignature sig
  wellFounded := ⟨fun σ => Acc.intro σ (fun _ h => by
    obtain ⟨_, _, h, _⟩ := h
    exact h.elim)⟩

end HepSignature

/-- A quasi-existence axiom with its own finite sorted variable context. -/
structure ContextualQEEquation {S : Type u} (sig : Signature.{u, v} S) where
  /-- The context is retained even for variables not occurring in the terms. -/
  vars : S → Type x
  /-- There are finitely many variables in total. -/
  finite : Finite (Σ s, vars s)
  /-- The word of sorts of the premises. -/
  premises : List S
  /-- The sort of the conclusion. -/
  sort : S
  /-- The contextual quasi-existence equation. -/
  equation : QEEquation sig vars premises sort

/-- An ep-specification adds a set of contextual axioms to an ep-signature. -/
structure EPSpecification {S : Type u} (sig : EPSignature.{u, v} S) where
  /-- Each axiom has its own finite context. -/
  equations : Set (ContextualQEEquation.{u, v, x} sig.symbol)

namespace EPSpecification

variable {S : Type u} {sig : EPSignature.{u, v} S}

/-- A model is an ep-algebra in which every contextual axiom is valid. -/
def IsModel (E : EPSpecification.{u, v, x} sig)
    (A : PartialAlgebra.{u, v, w} sig.symbol) : Prop :=
  sig.IsEPAlgebra A ∧ ∀ e ∈ E.equations, QEEquation.Valid A e.equation

/-- The ep-variety determined by a specification. -/
def variety (E : EPSpecification.{u, v, x} sig) : Set (PartialAlgebra.{u, v, w} sig.symbol) :=
  {A | E.IsModel A}

/-- The full category of models inside the category of ep-algebras. -/
abbrev Models (E : EPSpecification.{u, v, x} sig) :=
  ObjectProperty.FullSubcategory (fun A : EPSignature.EPAlg.{u, v, w} sig =>
    ∀ e ∈ E.equations, QEEquation.Valid A.obj e.equation : ObjectProperty sig.EPAlg)

/-- The inclusion of models into ep-algebras. -/
def inclusion (E : EPSpecification.{u, v, x} sig) : Models.{u, v, w, x} E ⥤ sig.EPAlg :=
  ObjectProperty.ι _

/-- The inclusion of the model category is fully faithful. -/
def inclusionFullyFaithful (E : EPSpecification.{u, v, x} sig) :
    (inclusion.{u, v, w, x} E).FullyFaithful := ObjectProperty.fullyFaithfulι _

/-- The empty specification imposes exactly the ep-algebra conditions. -/
theorem empty_isModel_iff (A : PartialAlgebra.{u, v, w} sig.symbol) :
    (⟨∅⟩ : EPSpecification.{u, v, x} sig).IsModel A ↔ sig.IsEPAlgebra A := by
  simp [IsModel]

end EPSpecification
end CategorialAlgebras
