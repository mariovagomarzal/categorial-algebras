import CategorialAlgebras.Homogeneous.Algebra
import CategorialAlgebras.Preliminaries.Derivor

/-!
# Term functors in homogeneous categorial algebras

A term of the original signature, with one variable for each position of a word, is
interpreted in a homogeneous categorial algebra as a higher functor from the product of
the categories of its positions. Variables are projections and operations are composed
with the tuples of their arguments. The underlying function is the term operation of the
total algebra of cells, so the term operations of the original terms are total and
preserve sources, targets and composites in every dimension.

Term functors commute with substitution and with homomorphisms of categorial algebras.
-/

universe i u u' v v' w x

namespace CategorialAlgebras
namespace Homogeneous

open CategoryTheory

variable {I : Type i} [LT I] {T : Type u} {tau : Signature.{u, v} T}

namespace CategorialAlgebra

/-- The product of the categories of the positions of a word, after a change of sorts. -/
abbrev positionProduct (B : CategorialAlgebra.{i, u, v, w} I tau) {R : Type u'} (φ : R → T)
    (a : List R) : HigherCategory.{i, w} I :=
  HigherCategory.product (fun j : Fin a.length => B.sort (φ (a.get j)))

/-- The higher functor interpreting a term whose variables are the positions of a word.
A variable is a projection, transported along its sort, and an operation is composed
with the tuple of the functors of its arguments. -/
def termFunctor (B : CategorialAlgebra.{i, u, v, w} I tau) {R : Type u'} (φ : R → T)
    (a : List R) : ∀ {t}, Term tau (Word.MappedVariables φ a) t →
      Functor (B.positionProduct φ a) (B.sort t)
  | _, .var ⟨j, rfl⟩ => HigherCategory.projection _ j
  | _, .app σ t => (HigherCategory.productLift (fun j => B.termFunctor φ a (t j))).comp (B.op σ)

/-- A term functor computes the term operation of the total algebra of cells. -/
theorem termFunctor_toFun (B : CategorialAlgebra.{i, u, v, w} I tau) {R : Type u'}
    (φ : R → T) (a : List R) {t} (P : Term tau (Word.MappedVariables φ a) t)
    (x : Word.Family (fun r => B.carrier (φ r)) a) :
    (B.termFunctor φ a P).toFun x = Term.eval (A := B.toAlgebra) (Word.valuation x) P := by
  induction P with
  | var y =>
    obtain ⟨j, h⟩ := y
    cases h
    rfl
  | app σ t ih =>
    change (B.op σ).toFun (fun j => (B.termFunctor φ a (t j)).toFun x) = _
    exact congrArg (B.op σ).toFun (funext ih)

/-- Term functors of variables at their own positions are projections. -/
@[simp] theorem termFunctor_mappedVariable_toFun (B : CategorialAlgebra.{i, u, v, w} I tau)
    {R : Type u'} (φ : R → T) (a : List R) (j : Fin a.length)
    (x : Word.Family (fun r => B.carrier (φ r)) a) :
    (B.termFunctor φ a (.var (Word.mappedVariable φ a j))).toFun x = x j := rfl

/-- Term operations of terms of the original signature preserve sources. -/
theorem termFunctor_source (B : CategorialAlgebra.{i, u, v, w} I tau) {R : Type u'}
    (φ : R → T) (a : List R) {t} (P : Term tau (Word.MappedVariables φ a) t) (k : I)
    (x : Word.Family (fun r => B.carrier (φ r)) a) :
    ((B.sort t).str.dim k).source ((B.termFunctor φ a P).toFun x) =
      (B.termFunctor φ a P).toFun (fun j => ((B.sort _).str.dim k).source (x j)) :=
  ((B.termFunctor φ a P).map_source k x).symm

/-- Term operations of terms of the original signature preserve targets. -/
theorem termFunctor_target (B : CategorialAlgebra.{i, u, v, w} I tau) {R : Type u'}
    (φ : R → T) (a : List R) {t} (P : Term tau (Word.MappedVariables φ a) t) (k : I)
    (x : Word.Family (fun r => B.carrier (φ r)) a) :
    ((B.sort t).str.dim k).target ((B.termFunctor φ a P).toFun x) =
      (B.termFunctor φ a P).toFun (fun j => ((B.sort _).str.dim k).target (x j)) :=
  ((B.termFunctor φ a P).map_target k x).symm

/-- Term operations of terms of the original signature preserve composites: if the
arguments are composable at every position, then the values are composable, with
composite the value at the composites. -/
theorem termFunctor_comp (B : CategorialAlgebra.{i, u, v, w} I tau) {R : Type u'}
    (φ : R → T) (a : List R) {t} (P : Term tau (Word.MappedVariables φ a) t) (k : I)
    (x y z : Word.Family (fun r => B.carrier (φ r)) a)
    (h : ∀ j, z j ∈ ((B.sort _).str.dim k).comp (x j) (y j)) :
    (B.termFunctor φ a P).toFun z ∈
      ((B.sort t).str.dim k).comp ((B.termFunctor φ a P).toFun x)
        ((B.termFunctor φ a P).toFun y) :=
  (B.termFunctor φ a P).map_comp k x y z ((mem_partFamily _ _).mpr h)

/-- Term functors commute with substitution of terms for the positions. -/
theorem termFunctor_substFamily (B : CategorialAlgebra.{i, u, v, w} I tau) {R : Type u'}
    {R' : Type x} (φ : R → T) (ψ : R' → T) (a : List R) (b : List R')
    (q : Word.Family (fun r => Term tau (Word.MappedVariables φ a) (ψ r)) b)
    {t} (P : Term tau (Word.MappedVariables ψ b) t) :
    B.termFunctor φ a (Term.substFamily (φ := ψ) q P) =
      (HigherCategory.productLift (fun j => B.termFunctor φ a (q j))).comp
        (B.termFunctor ψ b P) := by
  apply Functor.ext
  funext x
  induction P with
  | var y =>
    obtain ⟨j, h⟩ := y
    cases h
    rfl
  | app σ t ih =>
    change (B.op σ).toFun (fun j => (B.termFunctor φ a _).toFun x) =
      (B.op σ).toFun (fun j => (B.termFunctor ψ b (t j)).toFun _)
    exact congrArg (B.op σ).toFun (funext ih)

/-- Homomorphisms of categorial algebras commute with term operations. -/
theorem Hom.map_termFunctor {B C : CategorialAlgebra.{i, u, v, w} I tau} (f : B ⟶ C)
    {R : Type u'} (φ : R → T) (a : List R) {t} (P : Term tau (Word.MappedVariables φ a) t)
    (x : Word.Family (fun r => B.carrier (φ r)) a) :
    (f.sort t).toFun ((B.termFunctor φ a P).toFun x) =
      (C.termFunctor φ a P).toFun (fun j => (f.sort _).toFun (x j)) := by
  induction P with
  | var y =>
    obtain ⟨j, h⟩ := y
    cases h
    rfl
  | app σ t ih =>
    exact (f.map_op σ (fun j => (B.termFunctor φ a (t j)).toFun x)).trans
      (congrArg (C.op σ).toFun (funext ih))

end CategorialAlgebra
end Homogeneous
end CategorialAlgebras
