import CategorialAlgebras.Presentations.Graduation
import CategorialAlgebras.Presentations.Unification

/-!
# Composites of the presentation derivors

Unification followed by graduation is exactly the identity generalized derivor.
The other composite moves every sort to the top dimension and selects identity images.
-/

universe u v

namespace CategorialAlgebras.Presentations

variable (n : ℕ) {S : Type u} (sig : Signature.{u, v} S)

/-- The homogeneous round trip has the identity underlying derivor. -/
theorem unification_comp_graduation_derivor :
    (unificationDerivor n sig).comp (graduationDerivor n sig) =
      Derivor.identity (Homogeneous.Symbol (Fin n) sig) := by
  apply Derivor.ext (c := (unificationDerivor n sig).comp (graduationDerivor n sig))
    (d := Derivor.identity (Homogeneous.Symbol (Fin n) sig)) rfl
  apply heq_of_eq
  funext a s σ
  cases σ with
  | base σ =>
    change Term.app (sig := Homogeneous.Symbol (Fin n) sig)
      (X := Word.Variables a) (.base σ) _ = _
    apply congrArg (Term.app (sig := Homogeneous.Symbol (Fin n) sig) (.base σ))
    funext j
    simp [unificationDerivor, graduationDerivor, graduationBase, Term.eval,
      Word.valuation, Derivor.positionMap, Word.mappedVariable, List.get_eq_getElem]
    apply eq_of_heq
    rw [eqRec_heq_iff]
    have hv (t : S) (p : Fin a.length) (hp : a.get p = t) :
        HEq (Term.var (sig := Homogeneous.Symbol (Fin n) sig) (X := Word.Variables a) ⟨p, hp⟩)
          (Term.var (sig := Homogeneous.Symbol (Fin n) sig) (Word.position a p)) := by
      cases hp
      rfl
    exact hv _ j _
  | source k s =>
    change Term.app (sig := Homogeneous.Symbol (Fin n) sig)
      (X := Word.Variables [s]) (.source k s) _ = _
    apply congrArg (Term.app (sig := Homogeneous.Symbol (Fin n) sig) (.source k s))
    funext j
    fin_cases j
    rfl
  | target k s =>
    change Term.app (sig := Homogeneous.Symbol (Fin n) sig)
      (X := Word.Variables [s]) (.target k s) _ = _
    apply congrArg (Term.app (sig := Homogeneous.Symbol (Fin n) sig) (.target k s))
    funext j
    fin_cases j
    rfl
  | comp k s =>
    change Term.app (sig := Homogeneous.Symbol (Fin n) sig)
      (X := Word.Variables [s, s]) (.comp k s) _ = _
    apply congrArg (Term.app (sig := Homogeneous.Symbol (Fin n) sig) (.comp k s))
    funext j
    fin_cases j <;> rfl

/-- The homogeneous round trip is exactly the identity generalized hep-derivor,
including its empty domain equations. -/
theorem unification_comp_graduation :
    (unification n sig).comp (graduation n sig) =
      GeneralizedHepDerivor.identity (Homogeneous.hepSignature (Fin n) sig) := by
  apply GeneralizedHepDerivor.ext (unification_comp_graduation_derivor n sig)
  apply heq_of_eq
  funext s
  change (graduation n sig).domain (Fin.last n, s) ⊔
    (graduationDerivor n sig).translateSingletonSet _ ⊥ = ⊥
  rw [graduation_domain_last, Derivor.translateSingletonSet_empty]
  exact bot_sup_eq _

/-- The heterogeneous round trip sends every sort to the top-dimensional sort. -/
@[simp] theorem graduation_comp_unification_sort (k : Fin (n + 1)) (s : S) :
    ((graduation n sig).comp (unification n sig)).sortMap (k, s) = (Fin.last n, s) := rfl

/-- The heterogeneous round trip interprets identities by the sole variable. -/
theorem graduation_comp_unification_identity {j k : Fin (n + 1)} (h : j < k) (s : S) :
    ((graduation n sig).comp (unification n sig)).image (.identity h s) =
      .var (Word.mappedVariable (fun p => (Fin.last n, p.2)) [(j, s)] 0) := rfl

/-- The heterogeneous composite sends a boundary to that boundary into its lower carrier,
followed by the identity into the top carrier. -/
theorem graduation_comp_unification_boundary {j k : Fin (n + 1)} (h : j < k) (s : S)
    (b : Bool) :
    ((graduation n sig).comp (unification n sig)).image (.boundary h s b) =
      Heterogeneous.identityTerm (castSucc_lt_last (lowerDimension h))
        (Heterogeneous.boundary (castSucc_lt_last (lowerDimension h)) b
          (.var (Word.mappedVariable (fun p => (Fin.last n, p.2)) [(k, s)] 0))) := by
  cases b <;>
    apply congrArg (Term.app (sig := Heterogeneous.Symbol (Fin (n + 1)) sig)
      (.identity (castSucc_lt_last (lowerDimension h)) s)) <;>
    funext q <;> fin_cases q
  · apply congrArg (Term.app (sig := Heterogeneous.Symbol (Fin (n + 1)) sig)
      (.source (castSucc_lt_last (lowerDimension h)) s))
    funext q
    fin_cases q
    rfl
  · apply congrArg (Term.app (sig := Heterogeneous.Symbol (Fin (n + 1)) sig)
      (.target (castSucc_lt_last (lowerDimension h)) s))
    funext q
    fin_cases q
    rfl

/-- The heterogeneous composite interprets composition by composition of top cells. -/
theorem graduation_comp_unification_comp {j k : Fin (n + 1)} (h : j < k) (s : S) :
    ((graduation n sig).comp (unification n sig)).image (.comp h s) =
      Heterogeneous.binary (castSucc_lt_last (lowerDimension h))
        (.var (Word.mappedVariable (fun p => (Fin.last n, p.2)) [(k, s), (k, s)] 0))
        (.var (Word.mappedVariable (fun p => (Fin.last n, p.2)) [(k, s), (k, s)] 1)) := by
  apply congrArg (Term.app (sig := Heterogeneous.Symbol (Fin (n + 1)) sig)
    (.comp (castSucc_lt_last (lowerDimension h)) s))
  funext q
  fin_cases q <;> rfl

/-- The explicit base-operation term of the heterogeneous composite uses the top copy
of the symbol and preserves each original position. -/
def compositeBase (k : Fin (n + 1)) {a s} (σ : sig a s) :
    Term (Heterogeneous.Symbol (Fin (n + 1)) sig)
      (Word.MappedVariables (fun p => (Fin.last n, p.2)) (Heterogeneous.dimensionWord k a))
      (Fin.last n, s) :=
  Heterogeneous.base (Fin.last n) σ (fun j => .var
    ⟨Fin.cast (List.length_map _).symm j, by simp [List.get_eq_getElem]⟩)

/-- Original symbols in the heterogeneous composite act in the top dimension. -/
theorem graduation_comp_unification_base (k : Fin (n + 1)) {a s} (σ : sig a s) :
    ((graduation n sig).comp (unification n sig)).image (.base k σ) = compositeBase n sig k σ := by
  change Term.app (sig := Heterogeneous.Symbol (Fin (n + 1)) sig)
    (X := Word.MappedVariables (fun p => (Fin.last n, p.2)) (Heterogeneous.dimensionWord k a))
    (.base (Fin.last n) σ) _ = _
  apply congrArg (Term.app (sig := Heterogeneous.Symbol (Fin (n + 1)) sig) (.base (Fin.last n) σ))
  funext j
  simp [graduation, unification, graduationDerivor, graduationBase,
    unificationDerivor, Heterogeneous.dimensionFamily,
    Term.eval, Word.valuation, Derivor.positionMap, Word.mappedVariable, List.get_eq_getElem]
  apply eq_of_heq
  erw [eqRec_heq_iff]
  apply HEq.trans ?_ (cast_heq _ _).symm
  have hv {t r : Fin (n + 1) × S}
      (p q : Fin (Heterogeneous.dimensionWord k a).length)
      (hp : (Fin.last n, (Heterogeneous.dimensionWord k a).get p |>.2) = t)
      (hq : (Fin.last n, (Heterogeneous.dimensionWord k a).get q |>.2) = r)
      (he : p = q) :
      HEq (Term.var (sig := Heterogeneous.Symbol (Fin (n + 1)) sig)
        (X := Word.MappedVariables (fun p => (Fin.last n, p.2))
          (Heterogeneous.dimensionWord k a)) ⟨p, hp⟩)
        (Term.var (sig := Heterogeneous.Symbol (Fin (n + 1)) sig)
          (X := Word.MappedVariables (fun p => (Fin.last n, p.2))
            (Heterogeneous.dimensionWord k a)) ⟨q, hq⟩) := by
    cases he
    cases hp
    cases hq
    rfl
  exact hv _ _ _ _ (Fin.ext rfl)

end CategorialAlgebras.Presentations
