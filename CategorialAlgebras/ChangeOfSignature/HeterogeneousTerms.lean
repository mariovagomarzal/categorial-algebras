import CategorialAlgebras.Heterogeneous.Algebra
import CategorialAlgebras.Preliminaries.Derivor

/-!
# Term functors in heterogeneous categorial algebras

A term $P$ of the original signature, with one variable for each position of a word, is
interpreted in a heterogeneous categorial algebra as a heterogeneous higher functor from
the product of the categories of its positions. In dimension $k$ it computes the term
operation of $P_k$, the term obtained from $P$ by replacing every operation symbol $\tau$
by its copy $\tau_k$. Hence these term operations are total and preserve sources, targets,
identities and composites between every pair of dimensions.

Term functors commute with substitution and with homomorphisms of categorial algebras.
-/

universe i u u' v v' w x

namespace CategorialAlgebras
namespace Heterogeneous

open CategoryTheory

variable {I : Type i} [Preorder I] {T : Type u} {tau : Signature.{u, v} T}

namespace CategorialAlgebra

/-- The product of the categories of the positions of a word, after a change of sorts. -/
abbrev positionProduct (B : CategorialAlgebra.{i, u, v, w} I tau) {R : Type u'} (φ : R → T)
    (a : List R) : HigherCategory.{i, w} I :=
  HigherCategory.product (fun j : Fin a.length => B.sort (φ (a.get j)))

/-- The heterogeneous higher functor interpreting a term whose variables are the positions
of a word. A variable is a projection and an operation is composed with the tuple of the
functors of its arguments. -/
def termFunctor (B : CategorialAlgebra.{i, u, v, w} I tau) {R : Type u'} (φ : R → T)
    (a : List R) : ∀ {t}, Term tau (Word.MappedVariables φ a) t →
      Functor (B.positionProduct φ a) (B.sort t)
  | _, .var ⟨j, rfl⟩ => HigherCategory.projection _ j
  | _, .app σ t => (HigherCategory.productLift (fun j => B.termFunctor φ a (t j))).comp (B.op σ)

/-- In each dimension, a term functor computes the term operation of the total algebra of
the cells of that dimension. -/
theorem termFunctor_toFun (B : CategorialAlgebra.{i, u, v, w} I tau) {R : Type u'}
    (φ : R → T) (a : List R) {t} (P : Term tau (Word.MappedVariables φ a) t) (k : I)
    (x : Word.Family (fun r => B.carrier (k, φ r)) a) :
    (B.termFunctor φ a P).toFun k x =
      Term.eval (A := B.toAlgebra k) (Word.valuation (A := fun t => B.carrier (k, t)) x) P := by
  induction P with
  | var y =>
    obtain ⟨j, h⟩ := y
    cases h
    rfl
  | app σ t ih =>
    change (B.op σ).toFun k (fun j => (B.termFunctor φ a (t j)).toFun k x) = _
    exact congrArg ((B.op σ).toFun k) (funext ih)

/-- Term functors of variables at their own positions are projections. -/
@[simp] theorem termFunctor_mappedVariable_toFun (B : CategorialAlgebra.{i, u, v, w} I tau)
    {R : Type u'} (φ : R → T) (a : List R) (j : Fin a.length) (k : I)
    (x : Word.Family (fun r => B.carrier (k, φ r)) a) :
    (B.termFunctor φ a (.var (Word.mappedVariable φ a j))).toFun k x = x j := rfl

/-- Term functors commute with substitution of terms for the positions. -/
theorem termFunctor_substFamily (B : CategorialAlgebra.{i, u, v, w} I tau) {R : Type u'}
    {R' : Type x} (φ : R → T) (ψ : R' → T) (a : List R) (b : List R')
    (q : Word.Family (fun r => Term tau (Word.MappedVariables φ a) (ψ r)) b)
    {t} (P : Term tau (Word.MappedVariables ψ b) t) :
    B.termFunctor φ a (Term.substFamily (φ := ψ) q P) =
      (HigherCategory.productLift (fun j => B.termFunctor φ a (q j))).comp
        (B.termFunctor ψ b P) := by
  apply Functor.ext
  funext k x
  induction P with
  | var y =>
    obtain ⟨j, h⟩ := y
    cases h
    rfl
  | app σ t ih =>
    change (B.op σ).toFun k (fun j => (B.termFunctor φ a _).toFun k x) =
      (B.op σ).toFun k (fun j => (B.termFunctor ψ b (t j)).toFun k _)
    exact congrArg ((B.op σ).toFun k) (funext ih)

/-- Homomorphisms of categorial algebras commute with term operations. -/
theorem Hom.map_termFunctor {B C : CategorialAlgebra.{i, u, v, w} I tau} (f : B ⟶ C)
    {R : Type u'} (φ : R → T) (a : List R) {t} (P : Term tau (Word.MappedVariables φ a) t)
    (k : I) (x : Word.Family (fun r => B.carrier (k, φ r)) a) :
    (f.sort t).toFun k ((B.termFunctor φ a P).toFun k x) =
      (C.termFunctor φ a P).toFun k (fun j => (f.sort _).toFun k (x j)) := by
  induction P with
  | var y =>
    obtain ⟨j, h⟩ := y
    cases h
    rfl
  | app σ t ih =>
    exact (f.map_op σ k (fun j => (B.termFunctor φ a (t j)).toFun k x)).trans
      (congrArg ((C.op σ).toFun k) (funext ih))

end CategorialAlgebra
end Heterogeneous
end CategorialAlgebras
