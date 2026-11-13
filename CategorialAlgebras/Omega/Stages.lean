import CategorialAlgebras.Omega.Cells
import CategorialAlgebras.Presentations.UnifiedStructure

/-!
# Finite structures on dimensional carriers

The carrier in dimension $n$ is a homogeneous $n$-categorial algebra by
representing boundaries by their identities. Identity inclusions preserve
and reflect all operations in lower dimensions.
-/

universe u v w
namespace CategorialAlgebras.Omega
open Dimensions Presentations
set_option backward.isDefEq.respectTransparency false
variable {S : Type u} {sig : Signature.{u, v} S}
variable (B : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig)
variable (n : ℕ)

/-- The homogeneous higher category on a heterogeneous sort's top cells. -/
def stageSort (s : S) : Homogeneous.NCategory n where
  carrier := (B.sort s).carrier (n)
  str.dim k := collapseDimension ((B.sort s).str.dim k.val (n) k.isLt)
  str.compatible j k h := collapse_compatible ((B.sort s).str.compatible
    j.val k.val (n) h k.isLt)

/-- The explicit unified categorial algebra, before inserting the empty-domain subtype. -/
def stageAlgebra : Homogeneous.NCategorialAlgebra.{u, v, w} n sig where
  sort := stageSort B n
  op {a} {s} σ :=
    { toFun := (B.op σ).toFun (n)
      map_source k x := ((B.op σ).map_identity _ _ k.isLt
        (((Heterogeneous.wordProduct B.sort a).str.dim _ _ k.isLt).source x)).trans
          (congrArg ((B.sort s).str.dim _ _ k.isLt).identity
            ((B.op σ).map_source _ _ k.isLt x))
      map_target k x := ((B.op σ).map_identity _ _ k.isLt
        (((Heterogeneous.wordProduct B.sort a).str.dim _ _ k.isLt).target x)).trans
          (congrArg ((B.sort s).str.dim _ _ k.isLt).identity
            ((B.op σ).map_target _ _ k.isLt x))
      map_comp k x y z hz := (B.op σ).map_comp _ _ k.isLt x y z hz }


/-- Identity inclusions preserve lower sources. -/
theorem inclusion_source {m n : ℕ} (h : m ≤ n) (s : S) (k : Fin m)
    (x : B.carrier (m, s)) :
    inclusion B h s ((((stageAlgebra B m).sort s).str.dim k).source x) =
      (((stageAlgebra B n).sort s).str.dim ⟨k.val, lt_of_lt_of_le k.isLt h⟩).source
        (inclusion B h s x) := by
  dsimp only [stageAlgebra, stageSort, collapseDimension]
  rw [← dimensionLE_of_lt (B.sort s).str k.isLt.le k.isLt,
    ← dimensionLE_of_lt (B.sort s).str (le_trans k.isLt.le h) (lt_of_lt_of_le k.isLt h)]
  change (dimensionLE (B.sort s).str h).identity
    ((dimensionLE (B.sort s).str k.isLt.le).identity
      ((dimensionLE (B.sort s).str k.isLt.le).source x)) = _
  rw [dimensionLE_identity_trans]
  exact congrArg (dimensionLE (B.sort s).str (le_trans k.isLt.le h)).identity
    (dimensionLE_boundary_upperIdentity (B.sort s).str k.isLt.le h false x).symm

/-- Identity inclusions preserve lower targets. -/
theorem inclusion_target {m n : ℕ} (h : m ≤ n) (s : S) (k : Fin m)
    (x : B.carrier (m, s)) :
    inclusion B h s ((((stageAlgebra B m).sort s).str.dim k).target x) =
      (((stageAlgebra B n).sort s).str.dim ⟨k.val, lt_of_lt_of_le k.isLt h⟩).target
        (inclusion B h s x) := by
  dsimp only [stageAlgebra, stageSort, collapseDimension]
  rw [← dimensionLE_of_lt (B.sort s).str k.isLt.le k.isLt,
    ← dimensionLE_of_lt (B.sort s).str (le_trans k.isLt.le h) (lt_of_lt_of_le k.isLt h)]
  change (dimensionLE (B.sort s).str h).identity
    ((dimensionLE (B.sort s).str k.isLt.le).identity
      ((dimensionLE (B.sort s).str k.isLt.le).target x)) = _
  rw [dimensionLE_identity_trans]
  exact congrArg (dimensionLE (B.sort s).str (le_trans k.isLt.le h)).identity
    (dimensionLE_boundary_upperIdentity (B.sort s).str k.isLt.le h true x).symm

/-- Identity inclusions preserve lower composites. -/
theorem inclusion_comp {m n : ℕ} (h : m ≤ n) (s : S) (k : Fin m)
    (x y z : B.carrier (m, s))
    (hz : z ∈ (((stageAlgebra B m).sort s).str.dim k).comp x y) :
    inclusion B h s z ∈
      (((stageAlgebra B n).sort s).str.dim ⟨k.val, lt_of_lt_of_le k.isLt h⟩).comp
        (inclusion B h s x) (inclusion B h s y) := by
  dsimp only [stageAlgebra, stageSort, collapseDimension] at hz ⊢
  have he := dimensionLE_identity_comp (B.sort s).str k.isLt.le h x y z
    (by simpa only [dimensionLE_of_lt _ _ k.isLt] using hz)
  simpa only [inclusion, dimensionLE_of_lt _ _ (lt_of_lt_of_le k.isLt h)] using he

/-- Identity inclusions preserve the original operations. -/
theorem inclusion_op {m n : ℕ} (h : m ≤ n) {a s} (σ : sig a s)
    (x : Word.Family (fun s => B.carrier (m, s)) a) :
    inclusion B h s (((stageAlgebra B m).op σ).toFun x) =
      ((stageAlgebra B n).op σ).toFun (fun j => inclusion B h _ (x j)) := by
  exact (map_dimensionLE_identity (B.op σ) h x).symm.trans
    (congrArg ((B.op σ).toFun n)
      (dimensionLE_product_identity (C := fun j : Fin a.length => B.sort (a.get j)) h x))

end CategorialAlgebras.Omega
