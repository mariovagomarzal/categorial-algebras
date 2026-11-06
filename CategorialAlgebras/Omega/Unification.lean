import CategorialAlgebras.Omega.Descriptions

/-!
# The unification functor

A homomorphism acts on classes by applying its dimensional component to a
representative. Every preservation law is checked in a common finite dimension.
-/

universe u v w
namespace CategorialAlgebras.Omega
open CategoryTheory Dimensions
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Type u} {sig : Signature.{u, v} S}

/-- A heterogeneous homomorphism preserves dimensional identity inclusions. -/
theorem inclusion_natural {A B : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig}
    (f : A ⟶ B) {j k : ℕ} (h : j ≤ k) (s : S) (x : A.carrier (j, s)) :
    (f.sort s).toFun k (inclusion A h s x) =
      inclusion B h s ((f.sort s).toFun j x) :=
  map_dimensionLE_identity (f.sort s) h x

/-- The function on unified cells induced by a heterogeneous homomorphism. -/
noncomputable def unifiedMap {A B : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig}
    (f : A ⟶ B) (s : S) : Cell A s → Cell B s :=
  cellDesc A (fun k x => cellIn B k s ((f.sort s).toFun k x)) (by
    intro j k h x
    rw [inclusion_natural, cellIn_inclusion])

/-- Unification applies the dimensional component to a representative. -/
@[simp] theorem unifiedMap_in {A B : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig}
    (f : A ⟶ B) (k : ℕ) (s : S) (x : A.carrier (k, s)) :
    unifiedMap f s (cellIn A k s x) = cellIn B k s ((f.sort s).toFun k x) := rfl

/-- Dimensional components preserve the collapsed homogeneous stage structures. -/
def stageHom {A B : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig}
    (f : A ⟶ B) (n : ℕ) : stageAlgebra A n ⟶ stageAlgebra B n where
  sort s :=
    { toFun := (f.sort s).toFun n
      map_source k x := ((f.sort s).map_identity _ _ k.isLt _).trans
        (congrArg ((B.sort s).str.dim _ _ k.isLt).identity
          ((f.sort s).map_source _ _ k.isLt x))
      map_target k x := ((f.sort s).map_identity _ _ k.isLt _).trans
        (congrArg ((B.sort s).str.dim _ _ k.isLt).identity
          ((f.sort s).map_target _ _ k.isLt x))
      map_comp k x y z hz := (f.sort s).map_comp _ _ k.isLt x y z hz }
  map_op σ x := f.map_op σ n x

/-- The induced function on unified cells preserves every homogeneous operation. -/
noncomputable def unifiedHom {A B : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig}
    (f : A ⟶ B) : unifiedAlgebra A ⟶ unifiedAlgebra B where
  sort s :=
    { toFun := unifiedMap f s
      map_source k x := by
        obtain ⟨n, hn, y, hy⟩ := cell_cover A (fun _ : Fin 1 => s) ![x] (k + 1)
        have h0 : cellIn A n s (y 0) = x := hy 0
        rw [← h0]
        let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
        change unifiedMap f s (unifiedSource A k s _) = unifiedSource B k s (unifiedMap f s _)
        rw [unifiedSource_in A k', unifiedMap_in, unifiedMap_in, unifiedSource_in B k']
        exact congrArg (cellIn B n s) (((stageHom f n).sort s).map_source k' (y 0))
      map_target k x := by
        obtain ⟨n, hn, y, hy⟩ := cell_cover A (fun _ : Fin 1 => s) ![x] (k + 1)
        have h0 : cellIn A n s (y 0) = x := hy 0
        rw [← h0]
        let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
        change unifiedMap f s (unifiedTarget A k s _) = unifiedTarget B k s (unifiedMap f s _)
        rw [unifiedTarget_in A k', unifiedMap_in, unifiedMap_in, unifiedTarget_in B k']
        exact congrArg (cellIn B n s) (((stageHom f n).sort s).map_target k' (y 0))
      map_comp k x y z hz := by
        obtain ⟨n, hn, t, ht⟩ := cell_cover A (fun _ : Fin 3 => s) ![x, y, z] (k + 1)
        have h0 : cellIn A n s (t 0) = x := ht 0
        have h1 : cellIn A n s (t 1) = y := ht 1
        have h2 : cellIn A n s (t 2) = z := ht 2
        simp only [← h0, ← h1, ← h2] at hz ⊢
        let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
        change _ ∈ unifiedComp A k s _ _ at hz
        change unifiedMap f s _ ∈ unifiedComp B k s (unifiedMap f s _) (unifiedMap f s _)
        rw [unifiedComp_mem A k'] at hz
        simp only [unifiedMap_in]
        rw [unifiedComp_mem B k']
        exact ((stageHom f n).sort s).map_comp k' _ _ _ hz }
  map_op {a} {s} σ x := by
    obtain ⟨n, _, y, hy⟩ := cell_cover A (fun j => a.get j) x 0
    have hx : (fun j => cellIn A n _ (y j)) = x := funext hy
    rw [← hx]
    change unifiedMap f s (unifiedBase A σ (fun j => cellIn A n _ (y j))) =
      unifiedBase B σ (fun j => unifiedMap f _ (cellIn A n _ (y j)))
    rw [unifiedBase_in, unifiedMap_in]
    simp only [unifiedMap_in]
    rw [unifiedBase_in]
    exact congrArg (cellIn B n s) (f.map_op σ n y)

/-- Unification on the quotient carriers, with the finite-dimensional-cell condition. -/
noncomputable def unificationFunctor (sig : Signature.{u, v} S) :
    Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig ⥤
      Homogeneous.OmegaCategorialAlgebra sig where
  obj B := ⟨unifiedAlgebra B, unified_finite B⟩
  map f := ObjectProperty.homMk (unifiedHom f)
  map_id B := by
    apply ObjectProperty.hom_ext
    apply Homogeneous.CategorialAlgebra.Hom.ext
    funext s
    apply Homogeneous.Functor.ext
    funext x
    obtain ⟨k, y, rfl⟩ := cellIn_surjective B s x
    rfl
  map_comp {A B C} f g := by
    apply ObjectProperty.hom_ext
    apply Homogeneous.CategorialAlgebra.Hom.ext
    funext s
    apply Homogeneous.Functor.ext
    funext x
    obtain ⟨k, y, rfl⟩ := cellIn_surjective A s x
    rfl

/-- The functor on morphisms sends $[x]_k$ to $[f_k(x)]_k$. -/
@[simp] theorem unification_map_in {A B : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig}
    (f : A ⟶ B) (k : ℕ) (s : S) (x : A.carrier (k, s)) :
    ((((unificationFunctor sig).map f).hom.sort s).toFun (cellIn A k s x)) =
      cellIn B k s ((f.sort s).toFun k x) := rfl

end CategorialAlgebras.Omega
