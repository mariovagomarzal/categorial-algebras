import CategorialAlgebras.Limits.Faithful
import CategorialAlgebras.Dimensions.OmegaDescriptions

/-!
# Gluing homogeneous homomorphisms

A cell is evaluated in any finite truncation containing it. Coherence makes
this independent of the chosen finite dimension. The explicit truncation
realizations then check preservation of all operations in a sufficiently large
finite stage.
-/

universe u v w

namespace CategorialAlgebras.Limits

open CategoryTheory Dimensions

variable {S : Type u} {sig : Signature.{u, v} S}
variable {A B : Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig}

/-- Regard an original cutoff cell as a cell of the infinite truncation derivor. -/
def homogeneousCutoffCell (C : Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig)
    (n : ℕ) (s : S) (x : C.obj.carrier s) (h : (C.obj.sort s).str.IsCell n x) :
    (homogeneousOmegaTruncation sig n).Cell C.obj.toPartialAlgebra s :=
  ⟨x, (homogeneousOmegaTruncation_isCell_iff sig n C.obj s x).mpr h⟩

/-- The dimension chosen to evaluate a finite-dimensional cell. -/
noncomputable def homogeneousCellDimension (C : Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig)
    (s : S) (x : C.obj.carrier s) : ℕ := Classical.choose (C.property s x)

/-- The chosen dimension contains the given homogeneous cell. -/
theorem homogeneousCellDimension_spec (C : Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig)
    (s : S) (x : C.obj.carrier s) :
    (C.obj.sort s).str.IsCell (homogeneousCellDimension C s x) x :=
  Classical.choose_spec (C.property s x)

/-- A compatible family acts on a cell at a chosen finite dimension containing it. -/
noncomputable def homogeneousFamilyMap
    (f : (homogeneousCone sig).obj (Homogeneous.omegaModelFunctor.obj A) ⟶
      (homogeneousCone sig).obj (Homogeneous.omegaModelFunctor.obj B))
    (s : S) (x : A.obj.carrier s) : B.obj.carrier s :=
  ((f.app (homogeneousCellDimension A s x)).hom.hom.toMap s
    (homogeneousCutoffCell A _ s x (homogeneousCellDimension_spec A s x))).val

/-- Compatible finite components agree on every common element. -/
theorem homogeneousFamilyValue_mono
    (f : (homogeneousCone sig).obj (Homogeneous.omegaModelFunctor.obj A) ⟶
      (homogeneousCone sig).obj (Homogeneous.omegaModelFunctor.obj B))
    {m n : ℕ} (h : m ≤ n) (s : S)
    (x : (homogeneousOmegaTruncation sig m).Cell A.obj.toPartialAlgebra s)
    (y : (homogeneousOmegaTruncation sig n).Cell A.obj.toPartialAlgebra s) (hxy : x.val = y.val) :
    ((f.app m).hom.hom.toMap s x).val = ((f.app n).hom.hom.toMap s y).val := by
  let e := (homogeneousOmegaTruncationModelsComp sig h).app (Homogeneous.omegaModelFunctor.obj A)
  let z := e.inv.hom.hom.toMap s x
  have hz : z.val.val = x.val := by
    have he := congrArg (fun g => (g.hom.hom.toMap s x).val) e.inv_hom_id
    exact (homogeneousCone_val sig h (Homogeneous.omegaModelFunctor.obj A) s z).symm.trans he
  have hzy : z.val = y := Subtype.ext (hz.trans hxy)
  have he : e.hom.hom.hom.toMap s z = x :=
    congrArg (fun g => g.hom.hom.toMap s x) e.inv_hom_id
  have hc := congrArg (fun g => (g.hom.hom.toMap s z).val) (f.comm h)
  change
    (((homogeneousOmegaTruncationModelsComp sig h).hom.app (Homogeneous.omegaModelFunctor.obj B)).hom.hom.toMap s
      (((homogeneousTruncationModels sig h).map (f.app n)).hom.hom.toMap s z)).val =
    ((f.app m).hom.hom.toMap s (e.hom.hom.hom.toMap s z)).val at hc
  rw [he] at hc
  have hl := homogeneousCone_val sig h (Homogeneous.omegaModelFunctor.obj B) s
    (((homogeneousTruncationModels sig h).map (f.app n)).hom.hom.toMap s z)
  change _ = ((f.app n).hom.hom.toMap s z.val).val at hl
  rw [hzy] at hl
  exact hc.symm.trans hl

/-- The action of a family can be computed at any finite dimension containing the cell. -/
theorem homogeneousFamilyMap_at
    (f : (homogeneousCone sig).obj (Homogeneous.omegaModelFunctor.obj A) ⟶
      (homogeneousCone sig).obj (Homogeneous.omegaModelFunctor.obj B))
    (n : ℕ) (s : S) (x : (homogeneousOmegaTruncation sig n).Cell A.obj.toPartialAlgebra s) :
    homogeneousFamilyMap f s x.val = ((f.app n).hom.hom.toMap s x).val := by
  let m := homogeneousCellDimension A s x.val
  have hm := homogeneousCellDimension_spec A s x.val
  let y := homogeneousCutoffCell A (max m n) s x.val
    ((A.obj.sort s).str.isCell_mono (le_max_left m n) hm)
  exact (homogeneousFamilyValue_mono f (le_max_left m n) s
    (homogeneousCutoffCell A m s x.val hm) y rfl).trans
      (homogeneousFamilyValue_mono f (le_max_right m n) s x y rfl).symm

/-- The finite-construction subtype of an original cutoff cell. -/
def homogeneousFiniteCell (C : Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig)
    (n : ℕ) (s : S) (x : C.obj.carrier s) (h : (C.obj.sort s).str.IsCell n x) :
    (omegaTruncatedAlgebra C.obj n).carrier s :=
  ⟨x, (homogeneousTruncation_isCell_iff sig (Nat.le_succ n)
    (omegaRestrictedAlgebra C.obj (n + 1)) s x).mpr (fun _ => h)⟩

/-- A finite component between the explicit algebras of cutoff cells. -/
noncomputable def homogeneousLocalHom
    (f : (homogeneousCone sig).obj (Homogeneous.omegaModelFunctor.obj A) ⟶
      (homogeneousCone sig).obj (Homogeneous.omegaModelFunctor.obj B)) (n : ℕ) :
    Homogeneous.CategorialAlgebra.Hom (omegaTruncatedAlgebra A.obj n) (omegaTruncatedAlgebra B.obj n) :=
  Homogeneous.CategorialAlgebra.Hom.ofPartialHom
    ((homogeneousOmegaTruncationRealization sig n A.obj).hom ≫ (f.app n).hom.hom ≫
      (homogeneousOmegaTruncationRealization sig n B.obj).inv)

/-- The finite component of the family has the global function on its underlying cells. -/
theorem homogeneousLocalHom_val
    (f : (homogeneousCone sig).obj (Homogeneous.omegaModelFunctor.obj A) ⟶
      (homogeneousCone sig).obj (Homogeneous.omegaModelFunctor.obj B))
    (n : ℕ) (s : S) (x : (omegaTruncatedAlgebra A.obj n).carrier s) :
    (((homogeneousLocalHom f n).sort s).toFun x).val = homogeneousFamilyMap f s x.val := by
  have he := homogeneousOmegaTruncationRealization_inv_val sig n B.obj s
    ((f.app n).hom.hom.toMap s (omegaTruncationCell sig n A.obj s x))
  exact he.trans (homogeneousFamilyMap_at f n s (omegaTruncationCell sig n A.obj s x)).symm

/-- The glued homogeneous higher functor at an original sort. -/
noncomputable def homogeneousFamilyFunctor
    (f : (homogeneousCone sig).obj (Homogeneous.omegaModelFunctor.obj A) ⟶
      (homogeneousCone sig).obj (Homogeneous.omegaModelFunctor.obj B))
    (s : S) : Homogeneous.Functor (A.obj.sort s) (B.obj.sort s) where
  toFun := homogeneousFamilyMap f s
  map_source k x := by
    let n := max (k + 1) (homogeneousCellDimension A s x)
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_left _ _)⟩
    let y := homogeneousFiniteCell A n s x
      ((A.obj.sort s).str.isCell_mono (le_max_right _ _) (homogeneousCellDimension_spec A s x))
    have hh := congrArg Subtype.val (((homogeneousLocalHom f n).sort s).map_source k' y)
    have hvC := truncated_source_val sig (Nat.le_succ n) (omegaRestrictedAlgebra A.obj (n + 1)) k' s y
    have hvD := truncated_source_val sig (Nat.le_succ n) (omegaRestrictedAlgebra B.obj (n + 1)) k' s
      (((homogeneousLocalHom f n).sort s).toFun y)
    rw [homogeneousLocalHom_val] at hh
    erw [hvC] at hh
    exact hh.trans (hvD.trans (congrArg ((B.obj.sort s).str.dim k).source
      (homogeneousLocalHom_val f n s y)))
  map_target k x := by
    let n := max (k + 1) (homogeneousCellDimension A s x)
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_left _ _)⟩
    let y := homogeneousFiniteCell A n s x
      ((A.obj.sort s).str.isCell_mono (le_max_right _ _) (homogeneousCellDimension_spec A s x))
    have hh := congrArg Subtype.val (((homogeneousLocalHom f n).sort s).map_target k' y)
    have hvC := truncated_target_val sig (Nat.le_succ n) (omegaRestrictedAlgebra A.obj (n + 1)) k' s y
    have hvD := truncated_target_val sig (Nat.le_succ n) (omegaRestrictedAlgebra B.obj (n + 1)) k' s
      (((homogeneousLocalHom f n).sort s).toFun y)
    rw [homogeneousLocalHom_val] at hh
    erw [hvC] at hh
    exact hh.trans (hvD.trans (congrArg ((B.obj.sort s).str.dim k).target
      (homogeneousLocalHom_val f n s y)))
  map_comp k x y z hz := by
    let n := max (k + 1) (max (homogeneousCellDimension A s x)
      (max (homogeneousCellDimension A s y) (homogeneousCellDimension A s z)))
    have hn (t : A.obj.carrier s) (ht : homogeneousCellDimension A s t ≤ n) :
        (A.obj.sort s).str.IsCell n t :=
      (A.obj.sort s).str.isCell_mono ht (homogeneousCellDimension_spec A s t)
    let k' : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_left _ _)⟩
    let x' := homogeneousFiniteCell A n s x (hn x (le_trans (le_max_left _ _) (le_max_right _ _)))
    let y' := homogeneousFiniteCell A n s y
      (hn y (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
    let z' := homogeneousFiniteCell A n s z
      (hn z (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
    have hm := ((homogeneousLocalHom f n).sort s).map_comp k' x' y' z'
      ((truncated_comp_mem sig (Nat.le_succ n) (omegaRestrictedAlgebra A.obj (n + 1)) k' s x' y' z').mpr hz)
    have hv := (truncated_comp_mem sig (Nat.le_succ n) (omegaRestrictedAlgebra B.obj (n + 1)) k' s _ _ _).mp hm
    simp only [homogeneousLocalHom_val] at hv
    exact hv
/-- A compatible homogeneous family glues to an algebra homomorphism. -/
noncomputable def homogeneousFamilyHom
    (f : (homogeneousCone sig).obj (Homogeneous.omegaModelFunctor.obj A) ⟶
      (homogeneousCone sig).obj (Homogeneous.omegaModelFunctor.obj B)) :
    Homogeneous.CategorialAlgebra.Hom A.obj B.obj where
  sort := homogeneousFamilyFunctor f
  map_op {a} {s} σ x := by
    classical
    let n := Finset.univ.sup (fun j : Fin a.length => homogeneousCellDimension A (a.get j) (x j))
    let y : Word.Family (omegaTruncatedAlgebra A.obj n).carrier a := fun j =>
      homogeneousFiniteCell A n _ (x j) ((A.obj.sort _).str.isCell_mono
        (Finset.le_sup (f := fun j : Fin a.length => homogeneousCellDimension A (a.get j) (x j))
          (Finset.mem_univ j)) (homogeneousCellDimension_spec A _ (x j)))
    have hh := congrArg Subtype.val ((homogeneousLocalHom f n).map_op σ y)
    rw [homogeneousLocalHom_val] at hh
    change homogeneousFamilyMap f s ((A.obj.op σ).toFun x) =
      (B.obj.op σ).toFun (fun j => (((homogeneousLocalHom f n).sort _).toFun (y j)).val) at hh
    simp only [homogeneousLocalHom_val] at hh
    exact hh

/-- Homogeneous compatible homomorphism families are induced by actual homomorphisms. -/
theorem homogeneousCone_full_proof : (homogeneousCone.{u, v, w} sig).Full where
  map_surjective {A B} f := by
    obtain ⟨C, rfl⟩ := Homogeneous.omegaModelFunctor_bijective.2 A
    obtain ⟨D, rfl⟩ := Homogeneous.omegaModelFunctor_bijective.2 B
    refine ⟨ObjectProperty.homMk (ObjectProperty.homMk
      (ObjectProperty.homMk (homogeneousFamilyHom f).toPartialHom)), ?_⟩
    apply ProjectiveSystem.Family.Hom.ext
    funext n
    apply model_hom_ext
    intro s x
    apply Subtype.ext
    exact homogeneousFamilyMap_at f n s x

end CategorialAlgebras.Limits
