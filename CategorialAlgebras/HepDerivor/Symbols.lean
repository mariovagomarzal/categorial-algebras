import CategorialAlgebras.Preliminaries.Equation

/-!
# Operation symbols and dependence of evaluation

Symbols retain their input word and output sort. Partial evaluation and existence
equations depend only on the interpretations of the symbols occurring in them.
The corresponding local preservation results do not require a homomorphism on
symbols that do not occur.
-/

universe u v w x y

namespace CategorialAlgebras

/-- All operation symbols, including their input words and output sorts. -/
abbrev OperationSymbol {S : Type u} (sig : Signature.{u, v} S) :=
  Σ a, Σ s, sig a s

namespace Term

variable {S : Type u} {sig : Signature.{u, v} S} {X : S → Type x}

/-- The set $\mathrm{Op}(P)$ of operation symbols occurring in a term. -/
def symbols : ∀ {s}, Term sig X s → Set (OperationSymbol sig)
  | _, var _ => ∅
  | _, @app _ _ _ a s σ t => {⟨a, s, σ⟩} ∪ {p | ∃ j, p ∈ symbols (t j)}

/-- A variable contains no operation symbols. -/
@[simp] theorem symbols_var {s} (x : X s) : symbols (var (sig := sig) x) = ∅ := rfl

/-- An application contains its head symbol and the symbols of its arguments. -/
@[simp] theorem mem_symbols_app {a s} (σ : sig a s)
    (t : Word.Family (Term sig X) a) (p : OperationSymbol sig) :
    p ∈ symbols (app σ t) ↔ p = ⟨a, s, σ⟩ ∨ ∃ j, p ∈ symbols (t j) := Iff.rfl

/-- Preserving just the symbols of a term suffices to preserve its defined values. -/
theorem partialEval_map_of_symbols {A : PartialAlgebra.{u, v, w} sig}
    {B : PartialAlgebra.{u, v, y} sig} (f : SortedSet.Map A.carrier B.carrier)
    (a : SortedSet.Map X A.carrier) {s} (t : Term sig X s)
    (hf : ∀ {b r} (σ : sig b r), (⟨b, r, σ⟩ : OperationSymbol sig) ∈ symbols t →
      ∀ (z : Word.Family A.carrier b) {q}, q ∈ A.op σ z →
        f r q ∈ B.op σ (fun j => f _ (z j)))
    {q} (hq : q ∈ partialEval a t) :
    f s q ∈ partialEval (fun s x => f s (a s x)) t := by
  induction t with
  | var x =>
    simp only [partialEval_var, Part.mem_some_iff] at hq ⊢
    exact congrArg (f _) hq
  | app σ t ih =>
    obtain ⟨z, hz, hq⟩ := (mem_partialEval_app a σ t q).mp hq
    exact (mem_partialEval_app _ σ t _).mpr ⟨fun j => f _ (z j),
      fun j => ih j (fun τ hτ => hf τ (Or.inr ⟨j, hτ⟩)) (hz j),
      hf σ (Or.inl rfl) z hq⟩

/-- Evaluation depends only on the operations of the symbols occurring in the term. -/
theorem partialEval_eq_of_symbols {C : S → Type w}
    (op op' : PartialAlgebraStructure sig C) (a : SortedSet.Map X C)
    {s} (t : Term sig X s)
    (h : ∀ {b r} (σ : sig b r), (⟨b, r, σ⟩ : OperationSymbol sig) ∈ symbols t →
      ∀ z, op σ z = op' σ z) :
    partialEval (A := ⟨C, op⟩) a t = partialEval (A := ⟨C, op'⟩) a t := by
  induction t with
  | var _ => rfl
  | app σ t ih =>
    simp only [partialEval_app]
    have ht := funext (fun j => ih j (fun τ hτ => h τ (Or.inr ⟨j, hτ⟩)))
    rw [ht]
    exact congrArg _ (funext (h σ (Or.inl rfl)))

end Term

namespace EEquation

variable {S : Type u} {sig : Signature.{u, v} S} {X : S → Type x}

/-- The symbols occurring on either side of an existence equation. -/
def symbols {s} (e : EEquation sig X s) : Set (OperationSymbol sig) :=
  Term.symbols e.1 ∪ Term.symbols e.2

/-- Local preservation of operation values preserves an existence equation. -/
theorem satisfies_map_of_symbols {A : PartialAlgebra.{u, v, w} sig}
    {B : PartialAlgebra.{u, v, y} sig} (f : SortedSet.Map A.carrier B.carrier)
    (a : SortedSet.Map X A.carrier) {s} (e : EEquation sig X s)
    (hf : ∀ {b r} (σ : sig b r), (⟨b, r, σ⟩ : OperationSymbol sig) ∈ symbols e →
      ∀ (z : Word.Family A.carrier b) {q}, q ∈ A.op σ z →
        f r q ∈ B.op σ (fun j => f _ (z j)))
    (he : Satisfies A a e) : Satisfies B (fun s x => f s (a s x)) e := by
  obtain ⟨q, hp, hq⟩ := he
  exact ⟨f _ q, Term.partialEval_map_of_symbols f a e.1
    (fun σ h => hf σ (Or.inl h)) hp,
    Term.partialEval_map_of_symbols f a e.2 (fun σ h => hf σ (Or.inr h)) hq⟩

/-- Satisfaction depends only on the symbols occurring in the equation. -/
theorem satisfies_iff_of_symbols {C : S → Type w}
    (op op' : PartialAlgebraStructure sig C) (a : SortedSet.Map X C)
    {s} (e : EEquation sig X s)
    (h : ∀ {b r} (σ : sig b r), (⟨b, r, σ⟩ : OperationSymbol sig) ∈ symbols e →
      ∀ z, op σ z = op' σ z) :
    Satisfies ⟨C, op⟩ a e ↔ Satisfies ⟨C, op'⟩ a e := by
  unfold Satisfies
  rw [Term.partialEval_eq_of_symbols op op' a e.1 (fun σ hσ => h σ (Or.inl hσ)),
    Term.partialEval_eq_of_symbols op op' a e.2 (fun σ hσ => h σ (Or.inr hσ))]

end EEquation

namespace EEquationSet

variable {S : Type u} {sig : Signature.{u, v} S} {X : S → Type x}

/-- The union of the symbols of all equations in a sorted set. -/
def symbols (E : EEquationSet sig X) : Set (OperationSymbol sig) :=
  {p | ∃ s, ∃ e ∈ E s, p ∈ EEquation.symbols e}

/-- Local preservation on the symbols of a set of equations preserves satisfaction. -/
theorem satisfies_map_of_symbols {A : PartialAlgebra.{u, v, w} sig}
    {B : PartialAlgebra.{u, v, y} sig} (f : SortedSet.Map A.carrier B.carrier)
    (a : SortedSet.Map X A.carrier) (E : EEquationSet sig X)
    (hf : ∀ {b r} (σ : sig b r), (⟨b, r, σ⟩ : OperationSymbol sig) ∈ symbols E →
      ∀ (z : Word.Family A.carrier b) {q}, q ∈ A.op σ z →
        f r q ∈ B.op σ (fun j => f _ (z j)))
    (he : Satisfies A a E) : Satisfies B (fun s x => f s (a s x)) E :=
  fun s e hm => EEquation.satisfies_map_of_symbols f a e
    (fun σ hσ => hf σ ⟨s, e, hm, hσ⟩) (he s e hm)

/-- Satisfaction of a set depends only on the symbols occurring in its equations. -/
theorem satisfies_iff_of_symbols {C : S → Type w}
    (op op' : PartialAlgebraStructure sig C) (a : SortedSet.Map X C)
    (E : EEquationSet sig X)
    (h : ∀ {b r} (σ : sig b r), (⟨b, r, σ⟩ : OperationSymbol sig) ∈ symbols E →
      ∀ z, op σ z = op' σ z) :
    Satisfies ⟨C, op⟩ a E ↔ Satisfies ⟨C, op'⟩ a E := by
  constructor <;> intro he s e hm
  · exact (EEquation.satisfies_iff_of_symbols op op' a e
      (fun σ hσ => h σ ⟨s, e, hm, hσ⟩)).mp (he s e hm)
  · exact (EEquation.satisfies_iff_of_symbols op op' a e
      (fun σ hσ => h σ ⟨s, e, hm, hσ⟩)).mpr (he s e hm)

end EEquationSet
end CategorialAlgebras
