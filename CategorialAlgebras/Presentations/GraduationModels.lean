import CategorialAlgebras.Presentations.GraduatedStructure
import CategorialAlgebras.Presentations.Realization

/-!
# Graduation of models

The induced transformation agrees on the exact carriers with the explicit graduated
structure. Consequently it restricts and corestricts to the categories of models.
-/

universe u v w

namespace CategorialAlgebras.Presentations

open CategoryTheory

variable (n : ℕ) {S : Type u} (sig : Signature.{u, v} S)

/-- The explicit graduated operations have the interpreting values of the derivor. -/
theorem graduated_imageValue (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig)
    {a s} (σ : Heterogeneous.Symbol (Fin (n + 1)) sig a s)
    (x : Word.Family ((graduation n sig).Cell B.toPartialAlgebra) a) {q}
    (hq : q ∈ (graduatedAlgebra B).toPartialAlgebra.op σ x) :
    q.val ∈ (graduation n sig).imageValue B.toPartialAlgebra σ x := by
  cases σ with
  | @base k a s σ =>
    have he := Part.mem_some_iff.mp hq
    subst q
    apply (Term.mem_partialEval_app _ _ _ _).mpr
    refine ⟨fun j => ((Heterogeneous.dimensionFamily k _ x) j).val, ?_, Part.mem_some _⟩
    intro j
    apply Part.mem_some_iff.mpr
    have ht := congrFun (Heterogeneous.dimensionFamily_natural
      (A := fun p => GraduatedCell B p.1 p.2) (B := fun p => B.carrier p.2)
      (fun _ z => z.val) k _ x) j
    refine ht.symm.trans ?_
    dsimp only [Heterogeneous.dimensionFamily, Word.valuation, Equiv.coe_fn_mk]
    have transport (s t : S) (h : s = t) (h' : B.carrier s = B.carrier t)
        (z : B.carrier s) : h'.mp z = h ▸ z := by
      cases h
      rfl
    exact transport _ (a.get j) _ _ _
  | source h s =>
    change q.val ∈ Term.partialEval _ (Homogeneous.unary _ _)
    erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some]
    exact Part.mem_some_iff.mpr (congrArg Subtype.val (Part.mem_some_iff.mp hq))
  | target h s =>
    change q.val ∈ Term.partialEval _ (Homogeneous.unary _ _)
    erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some]
    exact Part.mem_some_iff.mpr (congrArg Subtype.val (Part.mem_some_iff.mp hq))
  | identity h s =>
    exact Part.mem_some_iff.mpr (congrArg Subtype.val (Part.mem_some_iff.mp hq))
  | comp h s =>
    change q.val ∈ Term.partialEval _ (Homogeneous.binary _ _ _)
    erw [Homogeneous.partialEval_binary, Term.partialEval_var, Part.bind_some,
      Term.partialEval_var, Part.bind_some]
    exact (mem_graduatedComp B h _ _ _).mp hq

/-- The transformation is exactly the expansion of the explicit graduated algebra. -/
theorem graduation_transformed (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig) :
    (graduation n sig).transformed B.toPartialAlgebra =
      (graduatedAlgebra B).toPartialAlgebra :=
  transformed_eq_of_realization _ _ _
    (Heterogeneous.equations_isEPAlgebra (graduatedAlgebra B).satisfiesEquations)
    (graduated_imageValue n sig B)

/-- Graduation sends every homogeneous model to a heterogeneous model. -/
theorem graduation_isModel (B : PartialAlgebra.{u, max v u, w}
    (Homogeneous.Symbol (Fin n) sig))
    (hB : (Homogeneous.specification (Fin n) sig).IsModel B) :
    (Heterogeneous.specification (Fin (n + 1)) sig).IsModel
      ((graduation n sig).transformed B) := by
  let C := Homogeneous.ofEquations B (fun e => hB.2 _ ⟨e, rfl⟩)
  have he := graduation_transformed n sig C
  have hc : C.toPartialAlgebra = B := Homogeneous.toPartialAlgebra_ofEquations B _
  rw [hc] at he
  rw [he]
  exact ⟨Heterogeneous.equations_isEPAlgebra (graduatedAlgebra C).satisfiesEquations,
    fun _ ⟨e, he⟩ => he ▸ (graduatedAlgebra C).satisfiesEquations e⟩

/-- Graduation restricted to homogeneous models, with values in partial algebras. -/
noncomputable def graduationOnModels : (Homogeneous.specification (Fin n) sig).Models ⥤
    PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol (Fin (n + 1)) sig) :=
  (Homogeneous.specification (Fin n) sig).inclusion ⋙
    (Homogeneous.epSignature (Fin n) sig).inclusion ⋙ graduationPartialFunctor n sig

/-- First corestriction: every graduated model is an ep-algebra. -/
noncomputable def graduationEpModels : (Homogeneous.specification (Fin n) sig).Models ⥤
    EPSignature.EPAlg.{u, max v u, w} (Heterogeneous.epSignature (Fin (n + 1)) sig) :=
  corestrict (graduationOnModels n sig) _ (fun B =>
    (graduation_isModel n sig B.obj.obj ⟨B.obj.property, B.property⟩).1)

/-- The induced graduation functor between the categories of models. -/
noncomputable def graduationModels : (Homogeneous.specification (Fin n) sig).Models ⥤
    (Heterogeneous.specification (Fin (n + 1)) sig).Models :=
  corestrict (graduationEpModels n sig) _ (fun B =>
    (graduation_isModel n sig B.obj.obj ⟨B.obj.property, B.property⟩).2)

/-- Graduation between categorial algebras, transported through the presentation isomorphisms. -/
noncomputable def graduationFunctor : Homogeneous.NCategorialAlgebra.{u, v, w} n sig ⥤
    Heterogeneous.NCategorialAlgebra.{u, v, w} n sig :=
  Homogeneous.modelIsomorphism.functor ⋙ graduationModels n sig ⋙
    Heterogeneous.modelIsomorphism.inverse

end CategorialAlgebras.Presentations
