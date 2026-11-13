import CategorialAlgebras.Limits.Truncations

/-!
# Diagonal carriers of a heterogeneous projective family

The carrier at $(k, s)$ is taken from stage $k$. The transition isomorphisms
transport lower-dimensional cells between stages. Every operation is computed
in the stage given by its highest dimension.
-/

universe u v w

namespace CategorialAlgebras.Limits

open CategoryTheory Dimensions

variable {S : Type u} {sig : Signature.{u, v} S}
variable (A : (heterogeneousSystem.{u, v, w} sig).Family)

/-- The algebra recovered on the exact carriers of a heterogeneous finite stage. -/
noncomputable def heterogeneousStage (n : ℕ) : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig :=
  Heterogeneous.ofEquations (A.obj n).obj.obj (Heterogeneous.model_equations (A.obj n))

/-- The carrier of dimension $k$ is the top carrier of the $k$th stage. -/
def HeterogeneousDiagonal (p : ℕ × S) : Type w :=
  (A.obj p.1).obj.obj.carrier (Fin.last p.1, p.2)

/-- Transport a diagonal cell into a later finite stage. -/
noncomputable def heterogeneousStageUp {m n : ℕ} (h : m ≤ n) (s : S)
    (x : HeterogeneousDiagonal A (m, s)) :
    (A.obj n).obj.obj.carrier (⟨m, Nat.lt_succ_of_le h⟩, s) :=
  ((A.transition h).inv.hom.hom.toMap (Fin.last m, s) x).val

/-- Transport a cell in a finite stage to its diagonal carrier. -/
noncomputable def heterogeneousStageDown {m n : ℕ} (h : m ≤ n) (s : S)
    (x : (A.obj n).obj.obj.carrier (⟨m, Nat.lt_succ_of_le h⟩, s)) :
    HeterogeneousDiagonal A (m, s) :=
  (A.transition h).hom.hom.hom.toMap (Fin.last m, s)
    ⟨x, heterogeneousDimension_isCell sig (cellInclusion h).toOrderHom (A.obj n).obj.obj (Fin.last m, s) x⟩

/-- Diagonal transport upwards and then downwards is identity. -/
@[simp] theorem heterogeneousStageDown_up {m n : ℕ} (h : m ≤ n) (s : S)
    (x : HeterogeneousDiagonal A (m, s)) :
    heterogeneousStageDown A h s (heterogeneousStageUp A h s x) = x :=
  congrArg (fun f : A.obj m ⟶ A.obj m => f.hom.hom.toMap (Fin.last m, s) x)
    (A.transition h).inv_hom_id

/-- Diagonal transport downwards and then upwards is identity. -/
@[simp] theorem heterogeneousStageUp_down {m n : ℕ} (h : m ≤ n) (s : S)
    (x : (A.obj n).obj.obj.carrier (⟨m, Nat.lt_succ_of_le h⟩, s)) :
    heterogeneousStageUp A h s (heterogeneousStageDown A h s x) = x :=
  congrArg (fun f : ((heterogeneousTruncationModels sig h).obj (A.obj n)) ⟶
      ((heterogeneousTruncationModels sig h).obj (A.obj n)) =>
        (f.hom.hom.toMap (Fin.last m, s)
          ⟨x, heterogeneousDimension_isCell sig (cellInclusion h).toOrderHom (A.obj n).obj.obj (Fin.last m, s) x⟩).val)
    (A.transition h).hom_inv_id

/-- The explicit partial algebra with its carrier of dimension $k$ taken from stage $k$. -/
noncomputable def heterogeneousDiagonalPartial :
    PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol ℕ sig) where
  carrier := HeterogeneousDiagonal A
  op
    | .base k σ, x => Part.some
        (((heterogeneousStage A k).op σ).toFun (Fin.last k)
          (Heterogeneous.dimensionFamily k _ x))
    | .source (j := j) (k := k) h s, x => Part.some
        (heterogeneousStageDown A h.le s
          ((((heterogeneousStage A k).sort s).str.dim
            ⟨j, Nat.lt_succ_of_lt h⟩ (Fin.last k) h).source (x 0)))
    | .target (j := j) (k := k) h s, x => Part.some
        (heterogeneousStageDown A h.le s
          ((((heterogeneousStage A k).sort s).str.dim
            ⟨j, Nat.lt_succ_of_lt h⟩ (Fin.last k) h).target (x 0)))
    | .identity (j := j) (k := k) h s, x => Part.some
        ((((heterogeneousStage A k).sort s).str.dim
          ⟨j, Nat.lt_succ_of_lt h⟩ (Fin.last k) h).identity
            (heterogeneousStageUp A h.le s (x 0)))
    | .comp (j := j) (k := k) h s, x =>
        (((heterogeneousStage A k).sort s).str.dim
          ⟨j, Nat.lt_succ_of_lt h⟩ (Fin.last k) h).comp (x 0) (x 1)

end CategorialAlgebras.Limits
