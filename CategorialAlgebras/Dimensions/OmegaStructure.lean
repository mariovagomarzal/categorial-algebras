import CategorialAlgebras.Dimensions.OmegaDerivors
import CategorialAlgebras.Dimensions.HomogeneousStructure
import CategorialAlgebras.Homogeneous.Omega

/-!
# Explicit structures in natural dimensions

Discretization adds discrete structures above a finite cutoff. Restriction
retains the carrier and the selected structures, while truncation restricts
the carrier to the cells at its cutoff.
-/

universe u v w

namespace CategorialAlgebras.Dimensions

/-- Extend a homogeneous structure by discrete structures at and above the cutoff. -/
noncomputable def omegaDiscretizedStructure {m : ℕ} {A : Type w}
    (C : Homogeneous.Structure (Fin m) A)  : Homogeneous.Structure ℕ A where
  dim k := if hk : k < m then C.dim ⟨k, hk⟩
    else Homogeneous.CategoryStructure.discrete A
  compatible j k h := by
    by_cases hk : k < m
    · have hj : j < m := lt_trans h hk
      simp only [dite_eq_left hk, dite_eq_left hj]
      exact C.compatible _ _ h
    · simp only [dite_eq_right hk]
      exact compatible_discrete_upper _

/-- A discretized sort retains exactly its original carrier. -/
noncomputable def omegaDiscretizedSort {m : ℕ} (C : Homogeneous.NCategory.{w} m)  :
    Homogeneous.HigherCategory ℕ where
  carrier := C.carrier
  str := omegaDiscretizedStructure C.str

/-- The explicit discretization retains the original operations on elements. -/
noncomputable def omegaDiscretizedAlgebra {m : ℕ} {S : Type u} {sig : Signature.{u, v} S}
    (B : Homogeneous.NCategorialAlgebra.{u, v, w} m sig)  :
    Homogeneous.CategorialAlgebra ℕ sig where
  sort s := omegaDiscretizedSort (B.sort s)
  op {a} {s} σ :=
    { toFun := (B.op σ).toFun
      map_source k x := by
        by_cases hk : k < m
        · change (B.op σ).toFun (fun q => (if hk : k < m then (B.sort (a.get q)).str.dim ⟨k, hk⟩ else Homogeneous.CategoryStructure.discrete _).source (x q)) =
            (if hk : k < m then (B.sort s).str.dim ⟨k, hk⟩ else Homogeneous.CategoryStructure.discrete _).source _
          simp only [dite_eq_left hk]
          exact (B.op σ).map_source ⟨k, hk⟩ x
        · change (B.op σ).toFun (fun q => (if hk : k < m then (B.sort (a.get q)).str.dim ⟨k, hk⟩ else Homogeneous.CategoryStructure.discrete _).source (x q)) =
            (if hk : k < m then (B.sort s).str.dim ⟨k, hk⟩ else Homogeneous.CategoryStructure.discrete _).source _
          simp only [dite_eq_right hk]
          rfl
      map_target k x := by
        by_cases hk : k < m
        · change (B.op σ).toFun (fun q => (if hk : k < m then (B.sort (a.get q)).str.dim ⟨k, hk⟩ else Homogeneous.CategoryStructure.discrete _).target (x q)) =
            (if hk : k < m then (B.sort s).str.dim ⟨k, hk⟩ else Homogeneous.CategoryStructure.discrete _).target _
          simp only [dite_eq_left hk]
          exact (B.op σ).map_target ⟨k, hk⟩ x
        · change (B.op σ).toFun (fun q => (if hk : k < m then (B.sort (a.get q)).str.dim ⟨k, hk⟩ else Homogeneous.CategoryStructure.discrete _).target (x q)) =
            (if hk : k < m then (B.sort s).str.dim ⟨k, hk⟩ else Homogeneous.CategoryStructure.discrete _).target _
          simp only [dite_eq_right hk]
          rfl
      map_comp k x y z hz := by
        have hz' : ∀ q : Fin a.length, z q ∈
            (if hk : k < m then (B.sort (a.get q)).str.dim ⟨k, hk⟩
              else Homogeneous.CategoryStructure.discrete _).comp (x q) (y q) :=
          (mem_partFamily _ _).mp hz
        change (B.op σ).toFun z ∈ (if hk : k < m then (B.sort s).str.dim ⟨k, hk⟩ else Homogeneous.CategoryStructure.discrete _).comp _ _
        by_cases hk : k < m
        · simp only [dite_eq_left hk] at hz' ⊢
          exact (B.op σ).map_comp ⟨k, hk⟩ x y z ((mem_partFamily _ _).mpr hz')
        · simp only [dite_eq_right hk] at hz' ⊢
          have hxy : x = y := funext (fun q => (hz' q).1)
          have hxz : x = z := funext (fun q => (hz' q).2)
          exact ⟨congrArg (B.op σ).toFun hxy, congrArg (B.op σ).toFun hxz⟩ }

/-- Every cell of an infinite discretization is fixed by the cutoff source. -/
theorem omegaDiscretizedAlgebra_isCell {n : ℕ} {S : Type u} {sig : Signature.{u, v} S}
    (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig) (s : S) (x : B.carrier s) :
    ((omegaDiscretizedAlgebra B).sort s).str.IsCell n x := by
  change (if h : n < n then _ else Homogeneous.CategoryStructure.discrete _).source x = x
  rw [dite_eq_right (lt_irrefl n)]
  rfl

/-- Infinite discretization has finite-dimensional cells, including cutoff zero. -/
theorem omegaDiscretizedAlgebra_finite {n : ℕ} {S : Type u} {sig : Signature.{u, v} S}
    (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig) :
    (omegaDiscretizedAlgebra B).FiniteDimensional :=
  fun s x => ⟨n, omegaDiscretizedAlgebra_isCell B s x⟩

/-- Restrict a natural-dimensional homogeneous algebra without changing its carrier. -/
def omegaRestrictedAlgebra {S : Type u} {sig : Signature.{u, v} S}
    (B : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig) (n : ℕ) :
    Homogeneous.NCategorialAlgebra n sig where
  sort s := ⟨(B.sort s).carrier, (B.sort s).str.restrict (omegaInclusion n)⟩
  op σ :=
    { toFun := (B.op σ).toFun
      map_source k x := (B.op σ).map_source k.val x
      map_target k x := (B.op σ).map_target k.val x
      map_comp k x y z hz := (B.op σ).map_comp k.val x y z hz }

/-- Truncate by taking the cutoff cells in the restriction to one extra dimension. -/
noncomputable def omegaTruncatedAlgebra {S : Type u} {sig : Signature.{u, v} S}
    (B : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig) (n : ℕ) :
    Homogeneous.NCategorialAlgebra n sig :=
  truncatedAlgebra (Nat.le_succ n) (omegaRestrictedAlgebra B (n + 1))

end CategorialAlgebras.Dimensions
