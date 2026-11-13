import CategorialAlgebras.Omega.GraduatedStructure

/-!
# Graduation in dimension $\omega$

Graduation takes fixed-source subtypes in each dimension. Homomorphisms
restrict to these subtypes, preserving all the heterogeneous operations.
-/

universe u v w
namespace CategorialAlgebras.Omega
open CategoryTheory
variable {S : Type u} {sig : Signature.{u, v} S}

/-- A homogeneous homomorphism restricts to a homomorphism of graduated algebras. -/
noncomputable def graduatedHom
    {A B : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig} (f : A ⟶ B) :
    graduatedAlgebra A ⟶ graduatedAlgebra B where
  sort s :=
    { toFun k x := ⟨(f.sort s).toFun x.val,
        ((f.sort s).map_source k x.val).symm.trans (congrArg (f.sort s).toFun x.property)⟩
      map_source _ _ _ x := Subtype.ext ((f.sort s).map_source _ x.val)
      map_target _ _ _ x := Subtype.ext ((f.sort s).map_target _ x.val)
      map_identity _ _ _ _ := Subtype.ext rfl
      map_comp _ _ h x y z hz := (mem_graduatedComp B h _ _ _).mpr
        ((f.sort s).map_comp _ _ _ _ ((mem_graduatedComp A h x y z).mp hz)) }
  map_op σ _ x := Subtype.ext (f.map_op σ (fun j => (x j).val))

/-- The explicit graduation functor from homogeneous to heterogeneous $\omega$-algebras.

**Formally weaker** than the informal statement. Informally, this functor is defined as the unique
one whose truncations are the finite graduations; here it is defined explicitly, and identified with
the functor given by the projective limit by a unique compatible isomorphism. -/
noncomputable def graduationFunctor (sig : Signature.{u, v} S) :
    Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig ⥤
      Heterogeneous.OmegaCategorialAlgebra sig where
  obj A := graduatedAlgebra A.obj
  map f := graduatedHom f.hom
  map_id A := by
    apply Heterogeneous.CategorialAlgebra.Hom.ext
    funext s
    apply Heterogeneous.Functor.ext
    funext k x
    rfl
  map_comp f g := by
    apply Heterogeneous.CategorialAlgebra.Hom.ext
    funext s
    apply Heterogeneous.Functor.ext
    funext k x
    rfl

/-- Graduation restricts the original function on each homomorphism. -/
@[simp] theorem graduation_map_val
    {A B : Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig} (f : A ⟶ B)
    (s : S) (k : ℕ) (x : GraduatedCell A.obj k s) :
    ((((graduationFunctor sig).map f).sort s).toFun k x).val = (f.hom.sort s).toFun x.val := rfl

/-- Graduated sources are the original sources on the underlying elements. -/
@[simp] theorem graduation_source (A : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig)
    {j k : ℕ} (h : j < k) (s : S) (x : GraduatedCell A k s) :
    ((((graduatedAlgebra A).sort s).str.dim j k h).source x).val =
      (((A.sort s).str.dim j).source x.val) := rfl

/-- Graduated targets are the original targets on the underlying elements. -/
@[simp] theorem graduation_target (A : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig)
    {j k : ℕ} (h : j < k) (s : S) (x : GraduatedCell A k s) :
    ((((graduatedAlgebra A).sort s).str.dim j k h).target x).val =
      (((A.sort s).str.dim j).target x.val) := rfl

/-- Graduated identities are inclusions of subtypes. -/
@[simp] theorem graduation_identity (A : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig)
    {j k : ℕ} (h : j < k) (s : S) (x : GraduatedCell A j s) :
    ((((graduatedAlgebra A).sort s).str.dim j k h).identity x).val = x.val := rfl

/-- Original operations act on graduated cells by restriction. -/
@[simp] theorem graduation_base (A : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig)
    {a s} (σ : sig a s) (k : ℕ) (x : Word.Family (fun s => GraduatedCell A k s) a) :
    (((graduatedAlgebra A).op σ).toFun k x).val = (A.op σ).toFun (fun j => (x j).val) := rfl

/-- Graduated composition is defined precisely when the original lower boundaries match. -/
theorem graduation_comp_dom (A : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig)
    {j k : ℕ} (h : j < k) (s : S) (x y : GraduatedCell A k s) :
    (graduatedComp A h x y).Dom ↔
      ((A.sort s).str.dim j).source x.val = ((A.sort s).str.dim j).target y.val :=
  ((A.sort s).str.dim j).comp_dom x.val y.val

end CategorialAlgebras.Omega
