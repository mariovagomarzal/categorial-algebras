import CategorialAlgebras.Preliminaries.SortedSet
import Mathlib.Data.List.Count

/-!
# Words, positions and valuations

Words are `List S`; length, concatenation, occurrences and change of alphabet use
`List.length`, `List.append`, `List.count` and `List.map`. A family indexed by a word always
has one entry for each `Fin w.length`. Variables are positions, retaining their sorts.
-/

universe u v w z

namespace CategorialAlgebras

namespace Word

/-! ## Families and positional variables -/

/-- Families $A_w$ indexed by the letters of a word $w$. -/
abbrev Family {S : Type u} (A : S → Type w) (w : List S) :=
  (j : Fin w.length) → A (w.get j)

/-- Positions of $w$ sorted by the images of their letters under $\varphi$.
This is a cast-free presentation of the variables of `w.map φ`. -/
def MappedVariables {S : Type u} {T : Type v} (φ : S → T) (w : List S) (t : T) :=
  {j : Fin w.length // φ (w.get j) = t}

/-- The sorted set $\downarrow w$ of positions of each sort in $w$. -/
abbrev Variables {S : Type u} (w : List S) := MappedVariables id w

/-- The variable at a specified position of $w$, after changing sorts. -/
def mappedVariable {S : Type u} {T : Type v} (φ : S → T) (w : List S)
    (j : Fin w.length) : MappedVariables φ w (φ (w.get j)) := ⟨j, rfl⟩

/-- The variable at a specified position of $w$. -/
abbrev position {S : Type u} (w : List S) (j : Fin w.length) : Variables w (w.get j) :=
  mappedVariable id w j

/-- The cast-free translated positions are equivalent to the positions of the mapped word. -/
def mappedVariablesEquiv {S : Type u} {T : Type v} (φ : S → T) (w : List S) (t : T) :
    MappedVariables φ w t ≃ Variables (w.map φ) t where
  toFun x := ⟨Fin.cast (List.length_map φ).symm x.val, by
    simpa [List.get_eq_getElem] using x.property⟩
  invFun x := ⟨Fin.cast (List.length_map φ) x.val, by
    simpa [List.get_eq_getElem] using x.property⟩
  left_inv x := by apply Subtype.ext; apply Fin.ext; rfl
  right_inv x := by apply Subtype.ext; apply Fin.ext; rfl

/-! ## Valuations -/

/-- A family determines the valuation sending each position to its entry. -/
def valuation {S : Type u} {T : Type v} {φ : S → T} {w : List S} {A : T → Type z}
    (a : Family (fun s => A (φ s)) w) : SortedSet.Map (MappedVariables φ w) A :=
  fun _ ⟨j, h⟩ => h ▸ a j

/-- Evaluating a family valuation at a position returns that entry. -/
@[simp] theorem valuation_variable {S : Type u} {T : Type v} {φ : S → T}
    {w : List S} {A : T → Type z} (a : Family (fun s => A (φ s)) w)
    (j : Fin w.length) : valuation a _ (mappedVariable φ w j) = a j := rfl

/-- Valuations of the positions are equivalent to families indexed by the word.

**Formally weaker** than the informal statement. Informally, the positional variables of a word are
also identified with standard variables; the library uses positional variables throughout and does
not need that identification. -/
def valuationEquiv {S : Type u} {T : Type v} (φ : S → T) (w : List S) (A : T → Type z) :
    SortedSet.Map (MappedVariables φ w) A ≃ Family (fun s => A (φ s)) w where
  toFun f j := f _ (mappedVariable φ w j)
  invFun := valuation
  left_inv f := by
    funext t ⟨j, h⟩
    cases h
    rfl
  right_inv _ := rfl

/-- The valuation-family equivalence is natural in its target sorted set. -/
theorem valuation_equiv_natural {S : Type u} {T : Type v} (φ : S → T) (w : List S)
    {A : T → Type w} {B : T → Type z} (f : SortedSet.Map A B)
    (a : SortedSet.Map (MappedVariables φ w) A) :
    valuationEquiv φ w B (fun t x => f t (a t x)) =
      fun j => f _ (valuationEquiv φ w A a j) := rfl

end Word
end CategorialAlgebras
