import CategorialAlgebras.Presentations.GraduationModels
import CategorialAlgebras.Presentations.UnificationModels

/-!
# Explicit operations of the induced functors

These descriptions include definedness as well as values: graduation restricts operations
to cells, and unification retains top operations while replacing objects by identities.
-/

universe u v w

namespace CategorialAlgebras.Presentations

open CategoryTheory

variable (n : ℕ) {S : Type u} (sig : Signature.{u, v} S)

/-- All graduated operations agree with the explicit structure on the exact same carriers. -/
theorem graduation_op (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig)
    {a s} (σ : Heterogeneous.Symbol (Fin (n + 1)) sig a s)
    (x : Word.Family ((graduation n sig).Cell B.toPartialAlgebra) a) :
    ((graduation n sig).transformed B.toPartialAlgebra).op σ x =
      (graduatedAlgebra B).toPartialAlgebra.op σ x :=
  congrArg (fun op => @op a s σ x) (op_eq_of_same_carrier (graduation_transformed n sig B))

/-- A graduated original operation is total and is the restriction of the original operation. -/
theorem graduation_base (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig)
    (k : Fin (n + 1)) {a s} (σ : sig a s)
    (x : Word.Family ((graduation n sig).Cell B.toPartialAlgebra)
      (Heterogeneous.dimensionWord k a)) :
    ((graduation n sig).transformed B.toPartialAlgebra).op (.base k σ) x =
      Part.some (graduatedOperation B σ k (Heterogeneous.dimensionFamily k a x)) := by
  exact graduation_op n sig B (.base k σ) x

/-- Graduated sources are total restrictions of homogeneous sources. -/
theorem graduation_source (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig)
    {j k : Fin (n + 1)} (h : j < k) (s) (x : GraduatedCell B k s) :
    ((graduation n sig).transformed B.toPartialAlgebra).op (.source h s) (Heterogeneous.single x) =
      Part.some (graduatedSource B h x) := by
  exact graduation_op n sig B (.source h s) (Heterogeneous.single x)

/-- Graduated targets are total restrictions of homogeneous targets. -/
theorem graduation_target (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig)
    {j k : Fin (n + 1)} (h : j < k) (s) (x : GraduatedCell B k s) :
    ((graduation n sig).transformed B.toPartialAlgebra).op (.target h s) (Heterogeneous.single x) =
      Part.some (graduatedTarget B h x) := by
  exact graduation_op n sig B (.target h s) (Heterogeneous.single x)

/-- Graduated identities are total inclusions. -/
theorem graduation_identity (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig)
    {j k : Fin (n + 1)} (h : j < k) (s) (x : GraduatedCell B j s) :
    ((graduation n sig).transformed B.toPartialAlgebra).op (.identity h s)
      (Heterogeneous.single x) =
      Part.some (graduatedIdentity B h x) := by
  exact graduation_op n sig B (.identity h s) (Heterogeneous.single x)

/-- A graduated composite has exactly the original underlying partial value. -/
theorem graduation_comp_mem (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig)
    {j k : Fin (n + 1)} (h : j < k) (s) (x y z : GraduatedCell B k s) :
    z ∈ ((graduation n sig).transformed B.toPartialAlgebra).op (.comp h s)
      (Heterogeneous.pair x y) ↔
      z.val ∈ ((B.sort s).str.dim (lowerDimension h)).comp x.val y.val := by
  exact (congrArg (fun p => z ∈ p)
    (graduation_op n sig B (.comp h s) (Heterogeneous.pair x y))).to_iff.trans
      (mem_graduatedComp B h x y z)

/-- The exact domain of graduated composition is equality of the original lower boundaries. -/
theorem graduation_comp_dom (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig)
    {j k : Fin (n + 1)} (h : j < k) (s) (x y : GraduatedCell B k s) :
    (((graduation n sig).transformed B.toPartialAlgebra).op (.comp h s)
      (Heterogeneous.pair x y)).Dom ↔
      ((B.sort s).str.dim (lowerDimension h)).source x.val =
        ((B.sort s).str.dim (lowerDimension h)).target y.val := by
  exact (congrArg Part.Dom
    (graduation_op n sig B (.comp h s) (Heterogeneous.pair x y))).to_iff.trans
      (((B.sort s).str.dim (lowerDimension h)).comp_dom _ _)

/-- The inverse unification realization also keeps the underlying element. -/
theorem unificationRealization_inv_val
    (A : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig) (s)
    (x : (unification n sig).Cell A.toPartialAlgebra s) :
    (unificationRealization n sig A).inv.toMap s x = x.val :=
  congrArg (fun f : (unification n sig).transformed A.toPartialAlgebra ⟶
    (unification n sig).transformed A.toPartialAlgebra => (f.toMap s x).val)
    (unificationRealization n sig A).inv_hom_id

/-- Every induced unified operation has precisely the value of the explicit
top-carrier operation. -/
theorem unification_op_mem (A : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig)
    {a s} (σ : Homogeneous.Symbol (Fin n) sig a s)
    (x : Word.Family ((unification n sig).Cell A.toPartialAlgebra) a)
    (y : (unification n sig).Cell A.toPartialAlgebra s) :
    y ∈ ((unification n sig).transformed A.toPartialAlgebra).op σ x ↔
      y.val ∈ (unifiedAlgebra A).toPartialAlgebra.op σ (fun j => (x j).val) := by
  constructor
  · intro hy
    have hv := (unificationRealization n sig A).inv.map_op σ x hy
    simp only [unificationRealization_inv_val] at hv
    exact hv
  · intro hy
    have hv := (unificationRealization n sig A).hom.map_op σ (fun j => (x j).val) hy
    have hx : (fun j : Fin a.length =>
        (unificationRealization n sig A).hom.toMap (a.get j) (x j).val) = x := by
      funext j
      apply Subtype.ext
      rfl
    have he : (unificationRealization n sig A).hom.toMap s y.val = y := Subtype.ext rfl
    rw [hx, he] at hv
    exact hv

/-- Unified compositions have the same values as heterogeneous top-dimensional compositions. -/
theorem unification_comp_mem (A : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig)
    (k : Fin n) (s) (x y z : (unification n sig).Cell A.toPartialAlgebra s) :
    z ∈ ((unification n sig).transformed A.toPartialAlgebra).op (.comp k s)
      (Homogeneous.pair x y) ↔
      z.val ∈ ((A.sort s).str.dim _ _ (castSucc_lt_last k)).comp x.val y.val :=
  unification_op_mem n sig A _ _ _

/-- The exact unified composition domain is equality of the heterogeneous boundaries. -/
theorem unification_comp_dom (A : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig)
    (k : Fin n) (s) (x y : (unification n sig).Cell A.toPartialAlgebra s) :
    (((unification n sig).transformed A.toPartialAlgebra).op (.comp k s)
      (Homogeneous.pair x y)).Dom ↔
      ((A.sort s).str.dim _ _ (castSucc_lt_last k)).source x.val =
        ((A.sort s).str.dim _ _ (castSucc_lt_last k)).target y.val := by
  constructor
  · intro h
    exact (((A.sort s).str.dim _ _ (castSucc_lt_last k)).comp_dom _ _).mp
      (((unification_comp_mem n sig A k s x y _).mp (Part.get_mem h)).1)
  · intro h
    have hd := (((A.sort s).str.dim _ _ (castSucc_lt_last k)).comp_dom _ _).mpr h
    exact ((unification_comp_mem n sig A k s x y
      (unificationCell n sig A.toPartialAlgebra s
        ((((A.sort s).str.dim _ _ (castSucc_lt_last k)).comp x.val y.val).get hd))).mpr
          (Part.get_mem hd)).1

/-- Unified sources are identity after heterogeneous source, with total domain. -/
theorem unification_source (A : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig)
    (k : Fin n) (s) (x : (unification n sig).Cell A.toPartialAlgebra s) :
    ((unification n sig).transformed A.toPartialAlgebra).op (.source k s) (Homogeneous.single x) =
      Part.some (unificationCell n sig A.toPartialAlgebra s
        (((A.sort s).str.dim _ _ (castSucc_lt_last k)).identity
          (((A.sort s).str.dim _ _ (castSucc_lt_last k)).source x.val))) := by
  apply Part.ext
  intro y
  exact (unification_op_mem n sig A _ _ y).trans
    (by
      constructor
      · intro h
        exact Part.mem_some_iff.mpr (Subtype.ext (Part.mem_some_iff.mp h))
      · intro h
        exact Part.mem_some_iff.mpr (congrArg Subtype.val (Part.mem_some_iff.mp h)))

/-- Unified targets are identity after heterogeneous target, with total domain. -/
theorem unification_target (A : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig)
    (k : Fin n) (s) (x : (unification n sig).Cell A.toPartialAlgebra s) :
    ((unification n sig).transformed A.toPartialAlgebra).op (.target k s) (Homogeneous.single x) =
      Part.some (unificationCell n sig A.toPartialAlgebra s
        (((A.sort s).str.dim _ _ (castSucc_lt_last k)).identity
          (((A.sort s).str.dim _ _ (castSucc_lt_last k)).target x.val))) := by
  apply Part.ext
  intro y
  exact (unification_op_mem n sig A _ _ y).trans
    (by
      constructor
      · intro h
        exact Part.mem_some_iff.mpr (Subtype.ext (Part.mem_some_iff.mp h))
      · intro h
        exact Part.mem_some_iff.mpr (congrArg Subtype.val (Part.mem_some_iff.mp h)))

/-- Unified original operations are total and act as their top-dimensional copies. -/
theorem unification_base (A : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig)
    {a s} (σ : sig a s) (x : Word.Family ((unification n sig).Cell A.toPartialAlgebra) a) :
    ((unification n sig).transformed A.toPartialAlgebra).op (.base σ) x =
      Part.some (unificationCell n sig A.toPartialAlgebra s
        ((A.op σ).toFun (Fin.last n) (fun j => (x j).val))) := by
  apply Part.ext
  intro y
  exact (unification_op_mem n sig A _ _ y).trans
    (by
      constructor
      · intro h
        exact Part.mem_some_iff.mpr (Subtype.ext (Part.mem_some_iff.mp h))
      · intro h
        exact Part.mem_some_iff.mpr (congrArg Subtype.val (Part.mem_some_iff.mp h)))

/-- Graduation acts on a homomorphism by restricting its function to each cell sort. -/
theorem graduation_map_val
    {A B : PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol (Fin n) sig)}
    (f : A ⟶ B) (k s) (x : (graduation n sig).Cell A (k, s)) :
    (((graduationPartialFunctor n sig).map f).toMap (k, s) x).val = f.toMap s x.val := rfl

/-- Unification acts on a homomorphism by taking its top-dimensional component. -/
theorem unification_map_val
    {A B : PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol (Fin (n + 1)) sig)}
    (f : A ⟶ B) (s) (x : (unification n sig).Cell A s) :
    (((unificationPartialFunctor n sig).map f).toMap s x).val =
      f.toMap (Fin.last n, s) x.val := rfl

end CategorialAlgebras.Presentations
