import CategorialAlgebras.Dimensions.HomogeneousDerivors
import CategorialAlgebras.Dimensions.HeterogeneousStructure
import CategorialAlgebras.Presentations.GraduatedStructure
import CategorialAlgebras.Presentations.UnifiedStructure

/-!
# Explicit homogeneous changes of dimension

Discretization appends discrete category structures. Truncation takes the
subtype of cells at the cutoff and restricts the original operations to it.
The latter is constructed from the already verified structure on finite cells.
-/

universe u v w

namespace CategorialAlgebras.Dimensions

/-- Every category structure is compatible with a discrete upper structure. -/
theorem compatible_discrete_upper {A : Type w} (C : Homogeneous.CategoryStructure A) :
    Homogeneous.Compatible C (Homogeneous.CategoryStructure.discrete A) where
  source_source _ := rfl
  target_target _ := rfl
  source_source_low _ := rfl
  target_target_low _ := rfl
  source_target _ := rfl
  target_source _ := rfl
  source_comp _ _ _ h := h
  target_comp _ _ _ h := h
  interchange x y z t xy zt xz yt hxy hzt hxz hyt := by
    rcases hxz with ⟨rfl, rfl⟩
    rcases hyt with ⟨rfl, rfl⟩
    have he := Part.mem_unique hxy hzt
    subst zt
    exact ⟨xy, ⟨rfl, rfl⟩, hxy⟩

/-- Extend a homogeneous structure by discrete structures at and above the cutoff. -/
noncomputable def discretizedStructure {m : ℕ} {A : Type w}
    (C : Homogeneous.Structure (Fin m) A) (n : ℕ) : Homogeneous.Structure (Fin n) A where
  dim k := if hk : k.val < m then C.dim ⟨k.val, hk⟩
    else Homogeneous.CategoryStructure.discrete A
  compatible j k h := by
    by_cases hk : k.val < m
    · have hj : j.val < m := lt_trans h hk
      simp only [dite_eq_left hk, dite_eq_left hj]
      exact C.compatible _ _ h
    · simp only [dite_eq_right hk]
      exact compatible_discrete_upper _

/-- A discretized sort retains exactly its original carrier. -/
noncomputable def discretizedSort {m : ℕ} (C : Homogeneous.NCategory.{w} m) (n : ℕ) :
    Homogeneous.NCategory n where
  carrier := C.carrier
  str := discretizedStructure C.str n

/-- The explicit discretization retains the original operations on elements. -/
noncomputable def discretizedAlgebra {m : ℕ} {S : Type u} {sig : Signature.{u, v} S}
    (B : Homogeneous.NCategorialAlgebra.{u, v, w} m sig) (n : ℕ) :
    Homogeneous.NCategorialAlgebra n sig where
  sort s := discretizedSort (B.sort s) n
  op {a} {s} σ :=
    { toFun := (B.op σ).toFun
      map_source k x := by
        by_cases hk : k.val < m
        · change (B.op σ).toFun (fun q => (if hk : k.val < m then (B.sort (a.get q)).str.dim ⟨k.val, hk⟩ else Homogeneous.CategoryStructure.discrete _).source (x q)) =
            (if hk : k.val < m then (B.sort s).str.dim ⟨k.val, hk⟩ else Homogeneous.CategoryStructure.discrete _).source _
          simp only [dite_eq_left hk]
          exact (B.op σ).map_source ⟨k.val, hk⟩ x
        · change (B.op σ).toFun (fun q => (if hk : k.val < m then (B.sort (a.get q)).str.dim ⟨k.val, hk⟩ else Homogeneous.CategoryStructure.discrete _).source (x q)) =
            (if hk : k.val < m then (B.sort s).str.dim ⟨k.val, hk⟩ else Homogeneous.CategoryStructure.discrete _).source _
          simp only [dite_eq_right hk]
          rfl
      map_target k x := by
        by_cases hk : k.val < m
        · change (B.op σ).toFun (fun q => (if hk : k.val < m then (B.sort (a.get q)).str.dim ⟨k.val, hk⟩ else Homogeneous.CategoryStructure.discrete _).target (x q)) =
            (if hk : k.val < m then (B.sort s).str.dim ⟨k.val, hk⟩ else Homogeneous.CategoryStructure.discrete _).target _
          simp only [dite_eq_left hk]
          exact (B.op σ).map_target ⟨k.val, hk⟩ x
        · change (B.op σ).toFun (fun q => (if hk : k.val < m then (B.sort (a.get q)).str.dim ⟨k.val, hk⟩ else Homogeneous.CategoryStructure.discrete _).target (x q)) =
            (if hk : k.val < m then (B.sort s).str.dim ⟨k.val, hk⟩ else Homogeneous.CategoryStructure.discrete _).target _
          simp only [dite_eq_right hk]
          rfl
      map_comp k x y z hz := by
        have hz' : ∀ q : Fin a.length, z q ∈
            (if hk : k.val < m then (B.sort (a.get q)).str.dim ⟨k.val, hk⟩
              else Homogeneous.CategoryStructure.discrete _).comp (x q) (y q) :=
          (mem_partFamily _ _).mp hz
        change (B.op σ).toFun z ∈ (if hk : k.val < m then (B.sort s).str.dim ⟨k.val, hk⟩ else Homogeneous.CategoryStructure.discrete _).comp _ _
        by_cases hk : k.val < m
        · simp only [dite_eq_left hk] at hz' ⊢
          exact (B.op σ).map_comp ⟨k.val, hk⟩ x y z ((mem_partFamily _ _).mpr hz')
        · simp only [dite_eq_right hk] at hz' ⊢
          have hxy : x = y := funext (fun q => (hz' q).1)
          have hxz : x = z := funext (fun q => (hz' q).2)
          exact ⟨congrArg (B.op σ).toFun hxy, congrArg (B.op σ).toFun hxz⟩ }

/-- The explicit truncation is the algebra of finite cells at the cutoff,
with boundaries and composition inherited from the original algebra. -/
noncomputable def truncatedAlgebra {m n : ℕ} {S : Type u} {sig : Signature.{u, v} S}
    (h : m ≤ n) (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig) :
    Homogeneous.NCategorialAlgebra m sig :=
  Presentations.unifiedAlgebra (reindexedAlgebra (Presentations.graduatedAlgebra B)
    (cellInclusion h).toOrderHom (orderEmbedding_saturating _))

end CategorialAlgebras.Dimensions
