import CategorialAlgebras.Presentations.UnifiedStructure
import CategorialAlgebras.Presentations.Realization

/-!
# Unification of models

The top-carrier description realizes the induced transformation by a bijective
homomorphism inserting only the empty-domain subtype. This gives corestriction to models.
-/

universe u v w

namespace CategorialAlgebras.Presentations

open CategoryTheory

variable (n : ℕ) {S : Type u} (sig : Signature.{u, v} S)

/-- Insert a top-dimensional element into the carrier of the transformation. -/
def unificationCell (A : PartialAlgebra.{u, max v u, w}
    (Heterogeneous.Symbol (Fin (n + 1)) sig)) (s : S) (x : A.carrier (Fin.last n, s)) :
    (unification n sig).Cell A s := ⟨x, unification_isCell n sig A s x⟩

/-- Insertion of the empty-domain subtype is bijective in each sort. -/
theorem unificationCell_bijective (A : PartialAlgebra.{u, max v u, w}
    (Heterogeneous.Symbol (Fin (n + 1)) sig)) (s : S) :
    Function.Bijective (unificationCell n sig A s) :=
  ⟨fun _ _ h => congrArg Subtype.val h, fun x => ⟨x.val, Subtype.ext rfl⟩⟩

/-- The explicit unified operations have precisely the prescribed interpreting values. -/
theorem unified_imageValue (A : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig)
    {a s} (σ : Homogeneous.Symbol (Fin n) sig a s)
    (x : Word.Family (unifiedAlgebra A).carrier a) {q}
    (hq : q ∈ (unifiedAlgebra A).toPartialAlgebra.op σ x) :
    q ∈ (unification n sig).imageValue A.toPartialAlgebra σ
      (fun j => unificationCell n sig A.toPartialAlgebra _ (x j)) := by
  cases σ with
  | @base a s σ =>
    apply (Term.mem_partialEval_app _ _ _ _).mpr
    refine ⟨(Heterogeneous.dimensionFamily (Fin.last n) a).symm x, ?_, ?_⟩
    · intro j
      apply Part.mem_some_iff.mpr
      dsimp only [Heterogeneous.dimensionFamily, Word.valuation, Equiv.coe_fn_symm_mk]
      have transport (p q : Fin (n + 1) × S) (h : p = q)
          (h' : A.carrier p = A.carrier q) (z : A.carrier p) : h'.mp z = h ▸ z := by
        cases h
        rfl
      exact transport (Fin.last n, a.get (Fin.cast (List.length_map _) j)) _ _ _ _
    · change q ∈ Part.some ((A.op σ).toFun (Fin.last n)
        ((Heterogeneous.dimensionFamily (A := A.carrier) (Fin.last n) a)
          ((Heterogeneous.dimensionFamily (A := A.carrier) (Fin.last n) a).symm x)))
      erw [Equiv.apply_symm_apply]
      exact hq
  | source k s =>
    change q ∈ Term.partialEval (A := A.toPartialAlgebra)
      (Word.valuation (φ := fun s => (Fin.last n, s)) x)
      (Heterogeneous.identityTerm _ (Heterogeneous.boundary _ _ _))
    erw [Heterogeneous.eval_expansion_identity, Heterogeneous.eval_expansion_boundary,
      Term.partialEval_var, Part.bind_some, Part.bind_some]
    exact hq
  | target k s =>
    change q ∈ Term.partialEval (A := A.toPartialAlgebra)
      (Word.valuation (φ := fun s => (Fin.last n, s)) x)
      (Heterogeneous.identityTerm _ (Heterogeneous.boundary _ _ _))
    erw [Heterogeneous.eval_expansion_identity, Heterogeneous.eval_expansion_boundary,
      Term.partialEval_var, Part.bind_some, Part.bind_some]
    exact hq
  | comp k s =>
    change q ∈ Term.partialEval (A := A.toPartialAlgebra)
      (Word.valuation (φ := fun s => (Fin.last n, s)) x) (Heterogeneous.binary _ _ _)
    erw [Heterogeneous.partialEval_binary, Term.partialEval_var, Part.bind_some,
      Term.partialEval_var, Part.bind_some]
    exact hq

/-- The explicit top-carrier algebra is isomorphic to the induced transformation.
The forward map inserts the empty-domain subtype and keeps every underlying element. -/
noncomputable def unificationRealization
    (A : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig) :
    (unifiedAlgebra A).toPartialAlgebra ≅ (unification n sig).transformed A.toPartialAlgebra :=
  realizationIso (unification n sig) A.toPartialAlgebra (unifiedAlgebra A).toPartialAlgebra
    (Homogeneous.equations_isEPAlgebra (unifiedAlgebra A).satisfiesEquations)
    (unificationCell n sig A.toPartialAlgebra)
    (unificationCell_bijective n sig A.toPartialAlgebra) (unified_imageValue n sig A)

/-- Unification's realization is the identity on underlying elements. -/
@[simp] theorem unificationRealization_hom_val
    (A : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig) (s : S)
    (x : (unifiedAlgebra A).carrier s) :
    ((unificationRealization n sig A).hom.toMap s x).val = x := rfl

/-- Unification sends every heterogeneous model to a homogeneous model. -/
theorem unification_isModel (A : PartialAlgebra.{u, max v u, w}
    (Heterogeneous.Symbol (Fin (n + 1)) sig))
    (hA : (Heterogeneous.specification (Fin (n + 1)) sig).IsModel A) :
    (Homogeneous.specification (Fin n) sig).IsModel ((unification n sig).transformed A) := by
  let C := Heterogeneous.ofEquations A (fun e => hA.2 _ ⟨e, rfl⟩)
  have hc : C.toPartialAlgebra = A := Heterogeneous.toPartialAlgebra_ofEquations A _
  rw [← hc]
  exact model_of_iso _ (unificationRealization n sig C)
    ⟨Homogeneous.equations_isEPAlgebra (unifiedAlgebra C).satisfiesEquations,
      fun _ ⟨e, he⟩ => he ▸ (unifiedAlgebra C).satisfiesEquations e⟩

/-- Unification restricted to heterogeneous models, with values in partial algebras. -/
noncomputable def unificationOnModels : (Heterogeneous.specification (Fin (n + 1)) sig).Models ⥤
    PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig) :=
  (Heterogeneous.specification (Fin (n + 1)) sig).inclusion ⋙
    (Heterogeneous.epSignature (Fin (n + 1)) sig).inclusion ⋙ unificationPartialFunctor n sig

/-- First corestriction: every unified model is an ep-algebra. -/
noncomputable def unificationEpModels : (Heterogeneous.specification (Fin (n + 1)) sig).Models ⥤
    EPSignature.EPAlg.{u, max v u, w} (Homogeneous.epSignature (Fin n) sig) :=
  corestrict (unificationOnModels n sig) _ (fun A =>
    (unification_isModel n sig A.obj.obj ⟨A.obj.property, A.property⟩).1)

/-- The induced unification functor between the categories of models. -/
noncomputable def unificationModels : (Heterogeneous.specification (Fin (n + 1)) sig).Models ⥤
    (Homogeneous.specification (Fin n) sig).Models :=
  corestrict (unificationEpModels n sig) _ (fun A =>
    (unification_isModel n sig A.obj.obj ⟨A.obj.property, A.property⟩).2)

/-- Unification between categorial algebras, transported through the presentation isomorphisms. -/
noncomputable def unificationFunctor : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig ⥤
    Homogeneous.NCategorialAlgebra.{u, v, w} n sig :=
  Heterogeneous.modelIsomorphism.functor ⋙ unificationModels n sig ⋙
    Homogeneous.modelIsomorphism.inverse

end CategorialAlgebras.Presentations
