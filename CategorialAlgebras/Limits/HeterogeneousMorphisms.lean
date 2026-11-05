import CategorialAlgebras.Limits.Faithful

/-!
# Gluing heterogeneous homomorphisms

A compatible family acts on a $k$-cell by its component at level $k$.
Compatibility identifies this action with the component at every later level,
where preservation of all operations can be checked.
-/

universe u v w

namespace CategorialAlgebras.Limits

open CategoryTheory Dimensions

variable {S : Type u} {sig : Signature.{u, v} S}
variable {A B : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig}

/-- The raw action of a compatible family on a cell of its given dimension. -/
noncomputable def heterogeneousFamilyMap
    (f : (heterogeneousCone sig).obj A.toModel ⟶ (heterogeneousCone sig).obj B.toModel)
    (p : ℕ × S) (x : A.carrier p) : B.carrier p :=
  ((f.app p.1).hom.hom.toMap (Fin.last p.1, p.2)
    (heterogeneousDimensionCell sig (omegaInclusion (p.1 + 1)).toOrderHom
      A.toPartialAlgebra (Fin.last p.1, p.2) x)).val

/-- The inverse reindexing realization forgets only the cell proof. -/
theorem heterogeneousRealization_inv (n : ℕ)
    (C : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig)
    (p : Fin (n + 1) × S) (x : (heterogeneousOmegaTruncation sig n).Cell C.toPartialAlgebra p) :
    (heterogeneousDimensionRealization sig (omegaInclusion (n + 1)).toOrderHom
      (orderEmbedding_saturating _) C).inv.toMap p x = x.val := by
  let e := heterogeneousDimensionRealization sig (omegaInclusion (n + 1)).toOrderHom
    (orderEmbedding_saturating _) C
  exact congrArg (fun g : (heterogeneousOmegaTruncation sig n).transformed C.toPartialAlgebra ⟶
    (heterogeneousOmegaTruncation sig n).transformed C.toPartialAlgebra => (g.toMap p x).val)
      e.inv_hom_id

/-- A finite family component acts between the explicit restrictions of the algebras. -/
noncomputable def heterogeneousLocalHom
    (f : (heterogeneousCone sig).obj A.toModel ⟶ (heterogeneousCone sig).obj B.toModel) (n : ℕ) :
    Heterogeneous.CategorialAlgebra.Hom
      (reindexedAlgebra A (omegaInclusion (n + 1)).toOrderHom (orderEmbedding_saturating _))
      (reindexedAlgebra B (omegaInclusion (n + 1)).toOrderHom (orderEmbedding_saturating _)) :=
  Heterogeneous.CategorialAlgebra.Hom.ofPartialHom
    ((heterogeneousDimensionRealization sig (omegaInclusion (n + 1)).toOrderHom
      (orderEmbedding_saturating _) A).hom ≫ (f.app n).hom.hom ≫
      (heterogeneousDimensionRealization sig (omegaInclusion (n + 1)).toOrderHom
        (orderEmbedding_saturating _) B).inv)

/-- The explicit finite homomorphism has the same underlying function as the family component. -/
theorem heterogeneousLocalHom_val
    (f : (heterogeneousCone sig).obj A.toModel ⟶ (heterogeneousCone sig).obj B.toModel)
    (n : ℕ) (j : Fin (n + 1)) (s : S) (x : A.carrier (j.val, s)) :
    ((heterogeneousLocalHom f n).sort s).toFun j x =
      ((f.app n).hom.hom.toMap (j, s)
        (heterogeneousDimensionCell sig (omegaInclusion (n + 1)).toOrderHom
          A.toPartialAlgebra (j, s) x)).val :=
  heterogeneousRealization_inv n B (j, s) _

/-- Compatibility identifies each component with the action at the cell's own dimension. -/
theorem heterogeneousFamilyMap_local
    (f : (heterogeneousCone sig).obj A.toModel ⟶ (heterogeneousCone sig).obj B.toModel)
    (n : ℕ) (j : Fin (n + 1)) (s : S) (x : A.carrier (j.val, s)) :
    heterogeneousFamilyMap f (j.val, s) x = ((heterogeneousLocalHom f n).sort s).toFun j x := by
  let h : j.val ≤ n := Nat.le_of_lt_succ j.isLt
  let p : Fin (j.val + 1) × S := (Fin.last j.val, s)
  let z := heterogeneousDimensionCell sig (omegaInclusion (n + 1)).toOrderHom
    A.toPartialAlgebra (j, s) x
  let y : (((heterogeneousTruncationModels sig h).obj
      ((heterogeneousOmegaTruncationModels sig n).obj A.toModel)).obj.obj.carrier p) :=
    heterogeneousDimensionCell sig (cellInclusion h).toOrderHom
      ((heterogeneousOmegaTruncation sig n).transformed A.toPartialAlgebra) p z
  have hy : ((heterogeneousOmegaTruncationModelsComp sig h).hom.app A.toModel).hom.hom.toMap p y =
      heterogeneousDimensionCell sig (omegaInclusion (j.val + 1)).toOrderHom A.toPartialAlgebra p x := by
    apply Subtype.ext
    exact eq_of_heq (heterogeneousCone_heq sig h A.toModel p y)
  have hc := congrArg (fun g => (g.hom.hom.toMap p y).val) (f.comm h)
  change
    (((heterogeneousOmegaTruncationModelsComp sig h).hom.app B.toModel).hom.hom.toMap p
      (((heterogeneousTruncationModels sig h).map (f.app n)).hom.hom.toMap p y)).val =
    ((f.app j.val).hom.hom.toMap p
      (((heterogeneousOmegaTruncationModelsComp sig h).hom.app A.toModel).hom.hom.toMap p y)).val at hc
  rw [hy] at hc
  have hl := eq_of_heq (heterogeneousCone_heq sig h B.toModel p
    (((heterogeneousTruncationModels sig h).map (f.app n)).hom.hom.toMap p y))
  rw [heterogeneousLocalHom_val]
  exact hc.symm.trans hl

/-- Strict finite pairs in a restricted algebra have their original structures. -/
theorem omegaReindexed_dim (C : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig)
    (n : ℕ) (s : S) (j k : Fin (n + 1)) (h : j < k) :
    (((reindexedAlgebra C (omegaInclusion (n + 1)).toOrderHom
      (orderEmbedding_saturating _)).sort s).str.dim j k h) =
      (C.sort s).str.dim j.val k.val h := by
  change dimensionLE (C.sort s).str (show j.val ≤ k.val from h.le) = _
  exact dimensionLE_of_lt (C.sort s).str _ (show j.val < k.val from h)

/-- The glued heterogeneous functor at each original sort. -/
noncomputable def heterogeneousFamilyFunctor
    (f : (heterogeneousCone sig).obj A.toModel ⟶ (heterogeneousCone sig).obj B.toModel)
    (s : S) : Heterogeneous.Functor (A.sort s) (B.sort s) where
  toFun k := heterogeneousFamilyMap f (k, s)
  map_source j k h x := by
    let j' : Fin (k + 1) := ⟨j, Nat.lt_succ_of_lt h⟩
    have hh := ((heterogeneousLocalHom f k).sort s).map_source j' (Fin.last k) h x
    rw [omegaReindexed_dim, omegaReindexed_dim] at hh
    exact (heterogeneousFamilyMap_local f k j' s _).trans
        (hh.trans (congrArg _ (heterogeneousFamilyMap_local f k (Fin.last k) s x).symm))
  map_target j k h x := by
    let j' : Fin (k + 1) := ⟨j, Nat.lt_succ_of_lt h⟩
    have hh := ((heterogeneousLocalHom f k).sort s).map_target j' (Fin.last k) h x
    rw [omegaReindexed_dim, omegaReindexed_dim] at hh
    exact (heterogeneousFamilyMap_local f k j' s _).trans
        (hh.trans (congrArg _ (heterogeneousFamilyMap_local f k (Fin.last k) s x).symm))
  map_identity j k h x := by
    let j' : Fin (k + 1) := ⟨j, Nat.lt_succ_of_lt h⟩
    have hh := ((heterogeneousLocalHom f k).sort s).map_identity j' (Fin.last k) h x
    rw [omegaReindexed_dim, omegaReindexed_dim] at hh
    exact (heterogeneousFamilyMap_local f k (Fin.last k) s _).trans
        (hh.trans (congrArg _ (heterogeneousFamilyMap_local f k j' s x).symm))
  map_comp j k h x y z hz := by
    let j' : Fin (k + 1) := ⟨j, Nat.lt_succ_of_lt h⟩
    have hh := ((heterogeneousLocalHom f k).sort s).map_comp j' (Fin.last k) h x y z
      (by rw [omegaReindexed_dim]; exact hz)
    rw [omegaReindexed_dim] at hh
    simp only [← heterogeneousFamilyMap_local f k (Fin.last k) s] at hh
    exact hh

/-- The compatible heterogeneous family glues to an algebra homomorphism. -/
noncomputable def heterogeneousFamilyHom
    (f : (heterogeneousCone sig).obj A.toModel ⟶ (heterogeneousCone sig).obj B.toModel) :
    Heterogeneous.CategorialAlgebra.Hom A B where
  sort := heterogeneousFamilyFunctor f
  map_op σ k x := by
    have hh := (heterogeneousLocalHom f k).map_op σ (Fin.last k) x
    change ((heterogeneousLocalHom f k).sort _).toFun (Fin.last k) ((A.op σ).toFun k x) =
      (B.op σ).toFun k (fun q => ((heterogeneousLocalHom f k).sort _).toFun (Fin.last k) (x q)) at hh
    change heterogeneousFamilyMap f (k, _) ((A.op σ).toFun k x) = _
    simp only [← heterogeneousFamilyMap_local f k (Fin.last k)] at hh
    exact hh

/-- Heterogeneous compatible homomorphism families are induced by actual homomorphisms. -/
theorem heterogeneousCone_full_proof : (heterogeneousCone.{u, v, w} sig).Full where
  map_surjective {A B} f := by
    obtain ⟨C, rfl⟩ := Heterogeneous.toModel_bijective.2 A
    obtain ⟨D, rfl⟩ := Heterogeneous.toModel_bijective.2 B
    refine ⟨ObjectProperty.homMk (ObjectProperty.homMk (heterogeneousFamilyHom f).toPartialHom), ?_⟩
    apply ProjectiveSystem.Family.Hom.ext
    funext n
    apply model_hom_ext
    intro p x
    apply Subtype.ext
    exact (heterogeneousFamilyMap_local f n p.1 p.2 x.val).trans
      (heterogeneousLocalHom_val f n p.1 p.2 x.val)

end CategorialAlgebras.Limits
