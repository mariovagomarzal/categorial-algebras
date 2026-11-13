import CategorialAlgebras.Presentations.Dimensions

/-!
# Graduation by a generalized hep-derivor

The map of sorts forgets dimension. Lower sorts select fixed points of source;
the top sort selects every element. Identities are interpreted by a variable.
-/

universe u v w

namespace CategorialAlgebras.Presentations

open CategoryTheory

variable (n : ℕ) {S : Type u} (sig : Signature.{u, v} S)

/-- The graduation image of an original operation, retaining its input positions. -/
def graduationBase (k : Fin (n + 1)) {a s} (σ : sig a s) :
    Term (Homogeneous.Symbol (Fin n) sig)
      (Word.MappedVariables Prod.snd (Heterogeneous.dimensionWord k a)) s :=
  .app (.base σ) (fun j => .var ⟨Fin.cast (List.length_map _).symm j, by
    simp [Heterogeneous.dimensionWord, List.get_eq_getElem]⟩)

/-- The derivor interpreting heterogeneous operations on a single carrier per sort. -/
def graduationDerivor : Derivor (Heterogeneous.Symbol (Fin (n + 1)) sig)
    (Homogeneous.Symbol (Fin n) sig) where
  sortMap := Prod.snd
  image
    | .base k σ => graduationBase n sig k σ
    | .source h s => Homogeneous.unary (.source (lowerDimension h) s)
        (.var (Word.mappedVariable Prod.snd _ 0))
    | .target h s => Homogeneous.unary (.target (lowerDimension h) s)
        (.var (Word.mappedVariable Prod.snd _ 0))
    | .identity _ _ => .var (Word.mappedVariable Prod.snd _ 0)
    | .comp h _ => Homogeneous.binary (lowerDimension h)
        (.var (Word.mappedVariable Prod.snd _ 0)) (.var (Word.mappedVariable Prod.snd _ 1))

/-- The equation selecting a cell at a lower dimension. -/
def graduationEquation (k : Fin n) (s : S) :
    EEquation (Homogeneous.Symbol (Fin n) sig) (Word.Variables [s]) s :=
  (.var (Word.position [s] 0),
    Homogeneous.unary (.source k s) (.var (Word.position [s] 0)))

/-- Graduation has empty domains at the top and fixed-source domains below it. -/
def graduation : GeneralizedHepDerivor (Heterogeneous.hepSignature (Fin (n + 1)) sig)
    (Homogeneous.hepSignature (Fin n) sig) where
  toDerivor := graduationDerivor n sig
  domain p := if h : p.1.val < n then
    Homogeneous.singletonEquation (graduationEquation n sig ⟨p.1.val, h⟩ p.2)
    else ⊥

/-- The top sort of graduation imposes no equations. -/
@[simp] theorem graduation_domain_last (s : S) :
    (graduation n sig).domain (Fin.last n, s) = ⊥ := by
  change (if h : n < n then _ else _) = _
  erw [dite_eq_right (Nat.lt_irrefl n)]
  rfl

/-- Every underlying element belongs to the top sort of graduation. -/
theorem graduation_isCell_last
    (B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig)) (s : S)
    (x : B.carrier s) : (graduation n sig).IsCell B (Fin.last n, s) x := by
  intro t e he
  rw [graduation_domain_last] at he
  exact he.elim

/-- The graduation functor on all partial algebras is the induced transformation. -/
noncomputable def graduationPartialFunctor :
    PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig) ⥤
      PartialAlgebra (Heterogeneous.Symbol (Fin (n + 1)) sig) :=
  (graduation n sig).transformedFunctor

/-- In an expansion, graduation selects exactly the cells of the indicated dimension. -/
theorem graduation_isCell_iff (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig)
    (k : Fin (n + 1)) (s : S) (x : B.carrier s) :
    (graduation n sig).IsCell B.toPartialAlgebra (k, s) x ↔
      IsFiniteCell (B.sort s).str k x := by
  change EEquationSet.Satisfies _ _ (if h : k.val < n then _ else _) ↔ _
  by_cases h : k.val < n
  · erw [dite_eq_left h]
    constructor
    · intro hx hk
      obtain ⟨q, hq, hr⟩ := hx s (graduationEquation n sig ⟨k.val, h⟩ s) ⟨rfl, rfl⟩
      have hq' : q = x := Part.mem_some_iff.mp hq
      have hr' : q = ((B.sort s).str.dim ⟨k.val, h⟩).source x := by
        change q ∈ Term.partialEval _ (Homogeneous.unary _ _) at hr
        erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some] at hr
        change q ∈ Part.some (((B.sort s).str.dim ⟨k.val, h⟩).source x) at hr
        exact Part.mem_some_iff.mp hr
      exact hr'.symm.trans hq'
    · intro hx t e ⟨ht, he⟩
      cases ht
      cases he
      refine ⟨x, Part.mem_some _, ?_⟩
      change x ∈ Term.partialEval (A := B.toPartialAlgebra) (Word.singletonValuation x)
        (Homogeneous.unary (.source ⟨k.val, h⟩ s) (.var (Word.position [s] 0)))
      erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some]
      change x ∈ Part.some (((B.sort s).str.dim ⟨k.val, h⟩).source x)
      exact Part.mem_some_iff.mpr (hx h).symm
  · erw [dite_eq_right h]
    exact ⟨fun _ hk => (h hk).elim, fun _ _ _ he => he.elim⟩

/-- In dimension zero every graduation domain is empty, so only sorts are relabelled. -/
theorem graduation_zero_domain (k : Fin 1) (s : S) :
    (graduation 0 sig).domain (k, s) = ⊥ := by
  have hk : k = Fin.last 0 := Subsingleton.elim _ _
  subst k
  exact graduation_domain_last 0 sig s

end CategorialAlgebras.Presentations
