import CategorialAlgebras.Presentations.Dimensions

/-!
# Unification by a generalized hep-derivor

Unification selects the top-dimensional carrier. Boundaries are followed by their
identities into the top dimension, and all cell domains are empty.
-/

universe u v w

namespace CategorialAlgebras.Presentations

open CategoryTheory

variable (n : ℕ) {S : Type u} (sig : Signature.{u, v} S)

/-- The derivor interpreting homogeneous operations on top-dimensional cells. -/
def unificationDerivor : Derivor (Homogeneous.Symbol (Fin n) sig)
    (Heterogeneous.Symbol (Fin (n + 1)) sig) where
  sortMap s := (Fin.last n, s)
  image
    | @Homogeneous.Symbol.base _ _ _ a s σ => .app (.base (Fin.last n) σ)
        (fun j => .var ⟨Fin.cast (List.length_map _) j, by
          simp [Heterogeneous.dimensionWord, List.get_eq_getElem]⟩)
    | .source k _ => Heterogeneous.identityTerm (castSucc_lt_last k)
        (Heterogeneous.boundary (castSucc_lt_last k) false
          (.var (Word.mappedVariable (fun s => (Fin.last n, s)) _ 0)))
    | .target k _ => Heterogeneous.identityTerm (castSucc_lt_last k)
        (Heterogeneous.boundary (castSucc_lt_last k) true
          (.var (Word.mappedVariable (fun s => (Fin.last n, s)) _ 0)))
    | .comp k _ => Heterogeneous.binary (castSucc_lt_last k)
        (.var (Word.mappedVariable (fun s => (Fin.last n, s)) _ 0))
        (.var (Word.mappedVariable (fun s => (Fin.last n, s)) _ 1))

/-- The generalized unification derivor, with empty cell domains. -/
def unification : GeneralizedHepDerivor (Homogeneous.hepSignature (Fin n) sig)
    (Heterogeneous.hepSignature (Fin (n + 1)) sig) where
  toDerivor := unificationDerivor n sig
  domain _ := ⊥

/-- Unification has no cell equations. -/
@[simp] theorem unification_domain (s : S) : (unification n sig).domain s = ⊥ := rfl

/-- Every top-dimensional element is a unification cell. -/
theorem unification_isCell
    (A : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol (Fin (n + 1)) sig))
    (s : S) (x : A.carrier (Fin.last n, s)) : (unification n sig).IsCell A s x :=
  (unification n sig).isCell_of_empty (fun _ => rfl) A s x

/-- The unification functor on partial algebras is the induced transformation. -/
noncomputable def unificationPartialFunctor :
    PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol (Fin (n + 1)) sig) ⥤
      PartialAlgebra (Homogeneous.Symbol (Fin n) sig) :=
  (unification n sig).transformedFunctor

end CategorialAlgebras.Presentations
