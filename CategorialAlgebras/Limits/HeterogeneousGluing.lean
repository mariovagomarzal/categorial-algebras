import CategorialAlgebras.Limits.HeterogeneousStages

/-!
# Gluing the heterogeneous categorical structures

Each pair structure is transported from the stage of its upper dimension.
The charts into any later stage preserve and reflect its operations. All
compatibility laws are consequently checked in a single finite stage.
-/

universe u v w
namespace CategorialAlgebras.Limits
open CategoryTheory Dimensions Presentations
set_option backward.isDefEq.respectTransparency false
variable {S : Type u} {sig : Signature.{u, v} S}
variable (A : (heterogeneousSystem.{u, v, w} sig).Family)

/-- Pair structure on diagonal carriers, transported from its upper stage. -/
noncomputable def heterogeneousDiagonalDimension {j k : ℕ} (h : j < k) (s : S) :
    Heterogeneous.CategoryStructure (HeterogeneousDiagonal A (j, s)) (HeterogeneousDiagonal A (k, s)) where
  source x := heterogeneousStageDown A h.le s
    ((((heterogeneousStage A k).sort s).str.dim ⟨j, Nat.lt_succ_of_lt h⟩ (Fin.last k) h).source x)
  target x := heterogeneousStageDown A h.le s
    ((((heterogeneousStage A k).sort s).str.dim ⟨j, Nat.lt_succ_of_lt h⟩ (Fin.last k) h).target x)
  identity x := (((heterogeneousStage A k).sort s).str.dim ⟨j, Nat.lt_succ_of_lt h⟩ (Fin.last k) h).identity
    (heterogeneousStageUp A h.le s x)
  comp := (((heterogeneousStage A k).sort s).str.dim ⟨j, Nat.lt_succ_of_lt h⟩ (Fin.last k) h).comp
  source_identity x := by
    rw [Heterogeneous.CategoryStructure.source_identity, heterogeneousStageDown_up]
  target_identity x := by
    rw [Heterogeneous.CategoryStructure.target_identity, heterogeneousStageDown_up]
  comp_dom x y := by
    rw [Heterogeneous.CategoryStructure.comp_dom]
    exact ⟨congrArg _, fun he => by
      have hh := congrArg (heterogeneousStageUp A h.le s) he
      simpa only [heterogeneousStageUp_down] using hh⟩
  source_comp _ _ _ hz := congrArg _ (Heterogeneous.CategoryStructure.source_comp _ _ _ _ hz)
  target_comp _ _ _ hz := congrArg _ (Heterogeneous.CategoryStructure.target_comp _ _ _ _ hz)
  comp_source x := by
    rw [heterogeneousStageUp_down]
    exact Heterogeneous.CategoryStructure.comp_source _ x
  target_comp_self x := by
    rw [heterogeneousStageUp_down]
    exact Heterogeneous.CategoryStructure.target_comp_self _ x
  assoc := Heterogeneous.CategoryStructure.assoc _

/-- Downward diagonal transport followed by a later chart is ordinary stage transport. -/
theorem heterogeneousChart_down {d m n : ℕ} (hd : d ≤ m) (h : m ≤ n) (s : S) (x) :
    heterogeneousStageUp A (le_trans hd h) s (heterogeneousStageDown A hd s x) =
      heterogeneousStageMap A h ⟨d, Nat.lt_succ_of_le hd⟩ s x := by
  have hh := heterogeneousStageUp_trans A hd h s (heterogeneousStageDown A hd s x)
  rw [heterogeneousStageUp_down] at hh
  exact hh.symm

/-- The chart into any later stage preserves a diagonal source. -/
theorem heterogeneousChart_source {j k n : ℕ} (h : j < k) (hn : k ≤ n) (s : S) (x) :
    heterogeneousStageUp A (le_trans h.le hn) s ((heterogeneousDiagonalDimension A h s).source x) =
      (((heterogeneousStage A n).sort s).str.dim
        ⟨j, Nat.lt_succ_of_le (le_trans h.le hn)⟩ ⟨k, Nat.lt_succ_of_le hn⟩ h).source
          (heterogeneousStageUp A hn s x) := by
  change heterogeneousStageUp A _ s (heterogeneousStageDown A h.le s _) = _
  rw [heterogeneousChart_down, heterogeneousStageMap_source]
  rfl

/-- The chart into any later stage preserves a diagonal target. -/
theorem heterogeneousChart_target {j k n : ℕ} (h : j < k) (hn : k ≤ n) (s : S) (x) :
    heterogeneousStageUp A (le_trans h.le hn) s ((heterogeneousDiagonalDimension A h s).target x) =
      (((heterogeneousStage A n).sort s).str.dim
        ⟨j, Nat.lt_succ_of_le (le_trans h.le hn)⟩ ⟨k, Nat.lt_succ_of_le hn⟩ h).target
          (heterogeneousStageUp A hn s x) := by
  change heterogeneousStageUp A _ s (heterogeneousStageDown A h.le s _) = _
  rw [heterogeneousChart_down, heterogeneousStageMap_target]
  rfl

/-- The chart into any later stage preserves a diagonal identity. -/
theorem heterogeneousChart_identity {j k n : ℕ} (h : j < k) (hn : k ≤ n) (s : S) (x) :
    heterogeneousStageUp A hn s ((heterogeneousDiagonalDimension A h s).identity x) =
      (((heterogeneousStage A n).sort s).str.dim
        ⟨j, Nat.lt_succ_of_le (le_trans h.le hn)⟩ ⟨k, Nat.lt_succ_of_le hn⟩ h).identity
          (heterogeneousStageUp A (le_trans h.le hn) s x) := by
  change heterogeneousStageMap A hn (Fin.last k) s
    ((((heterogeneousStage A k).sort s).str.dim ⟨j, Nat.lt_succ_of_lt h⟩ (Fin.last k) h).identity
      (heterogeneousStageUp A h.le s x)) = _
  erw [heterogeneousStageMap_identity, heterogeneousStageUp_trans]
  rfl

/-- The chart into any later stage preserves and reflects diagonal composition. -/
theorem heterogeneousChart_comp {j k n : ℕ} (h : j < k) (hn : k ≤ n) (s : S) (x y z) :
    heterogeneousStageUp A hn s z ∈
      (((heterogeneousStage A n).sort s).str.dim
        ⟨j, Nat.lt_succ_of_le (le_trans h.le hn)⟩ ⟨k, Nat.lt_succ_of_le hn⟩ h).comp
          (heterogeneousStageUp A hn s x) (heterogeneousStageUp A hn s y) ↔
      z ∈ (heterogeneousDiagonalDimension A h s).comp x y :=
  heterogeneousStageMap_comp_iff A hn s ⟨j, Nat.lt_succ_of_lt h⟩ (Fin.last k) h x y z

/-- The chart into any later stage preserves either diagonal boundary. -/
theorem heterogeneousChart_boundary {j k n : ℕ} (h : j < k) (hn : k ≤ n) (s : S) (b : Bool) (x) :
    heterogeneousStageUp A (le_trans h.le hn) s ((heterogeneousDiagonalDimension A h s).boundary b x) =
      (((heterogeneousStage A n).sort s).str.dim
        ⟨j, Nat.lt_succ_of_le (le_trans h.le hn)⟩ ⟨k, Nat.lt_succ_of_le hn⟩ h).boundary b
          (heterogeneousStageUp A hn s x) := by
  cases b
  · exact heterogeneousChart_source A h hn s x
  · exact heterogeneousChart_target A h hn s x

/-- Every diagonal chart is injective. -/
theorem heterogeneousChart_injective {m n : ℕ} (h : m ≤ n) (s : S) :
    Function.Injective (heterogeneousStageUp A h s) :=
  (heterogeneousStageMap_bijective A h (Fin.last m) s).1
/-- The diagonal pair structures satisfy compatibility in every increasing triple. -/
theorem heterogeneousDiagonal_compatible {i j k : ℕ} (h : i < j) (q : j < k) (s : S) :
    Heterogeneous.Compatible (heterogeneousDiagonalDimension A h s)
      (heterogeneousDiagonalDimension A q s) (heterogeneousDiagonalDimension A (lt_trans h q) s) where
  globular b c x := by
    apply heterogeneousChart_injective A (le_trans h.le q.le) s
    erw [heterogeneousChart_boundary A h q.le, heterogeneousChart_boundary A q (le_refl k),
      heterogeneousChart_boundary A (lt_trans h q) (le_refl k)]
    simp only [heterogeneousStageUp_self]
    exact (((heterogeneousStage A k).sort s).str.compatible
      ⟨i, Nat.lt_succ_of_lt (lt_trans h q)⟩ ⟨j, Nat.lt_succ_of_lt q⟩ (Fin.last k) h q).globular b c x
  identity_identity x := by
    apply heterogeneousChart_injective A (le_refl k) s
    erw [heterogeneousChart_identity A q (le_refl k), heterogeneousChart_identity A h q.le,
      heterogeneousChart_identity A (lt_trans h q) (le_refl k)]
    exact (((heterogeneousStage A k).sort s).str.compatible
      ⟨i, Nat.lt_succ_of_lt (lt_trans h q)⟩ ⟨j, Nat.lt_succ_of_lt q⟩ (Fin.last k) h q).identity_identity _
  boundary_comp b x y z hz := by
    apply (heterogeneousChart_comp A h q.le s _ _ _).mp
    erw [heterogeneousChart_boundary A q (le_refl k),
      heterogeneousChart_boundary A q (le_refl k), heterogeneousChart_boundary A q (le_refl k)]
    simp only [heterogeneousStageUp_self]
    exact (((heterogeneousStage A k).sort s).str.compatible
      ⟨i, Nat.lt_succ_of_lt (lt_trans h q)⟩ ⟨j, Nat.lt_succ_of_lt q⟩ (Fin.last k) h q).boundary_comp b x y z hz
  identity_comp x y z hz := by
    apply (heterogeneousChart_comp A (lt_trans h q) (le_refl k) s _ _ _).mp
    erw [heterogeneousChart_identity A q (le_refl k),
      heterogeneousChart_identity A q (le_refl k), heterogeneousChart_identity A q (le_refl k)]
    exact (((heterogeneousStage A k).sort s).str.compatible
      ⟨i, Nat.lt_succ_of_lt (lt_trans h q)⟩ ⟨j, Nat.lt_succ_of_lt q⟩ (Fin.last k) h q).identity_comp _ _ _
        ((heterogeneousChart_comp A h q.le s x y z).mpr hz)
  interchange x y z t xy zt xz yt hxy hzt hxz hyt :=
    (((heterogeneousStage A k).sort s).str.compatible
      ⟨i, Nat.lt_succ_of_lt (lt_trans h q)⟩ ⟨j, Nat.lt_succ_of_lt q⟩ (Fin.last k) h q).interchange
        x y z t xy zt xz yt hxy hzt hxz hyt

/-- The higher category on all diagonal carriers of a sort. -/
noncomputable def heterogeneousDiagonalSort (s : S) : Heterogeneous.HigherCategory ℕ where
  carrier k := HeterogeneousDiagonal A (k, s)
  str.dim _ _ h := heterogeneousDiagonalDimension A h s
  str.compatible _ _ _ h q := heterogeneousDiagonal_compatible A h q s

/-- Original operations on diagonal cells commute with all later charts. -/
theorem heterogeneousChart_op {a s} (σ : sig a s) {k n : ℕ} (h : k ≤ n)
    (x : Word.Family (fun s => HeterogeneousDiagonal A (k, s)) a) :
    heterogeneousStageUp A h s (((heterogeneousStage A k).op σ).toFun (Fin.last k) x) =
      ((heterogeneousStage A n).op σ).toFun ⟨k, Nat.lt_succ_of_le h⟩
        (fun j => heterogeneousStageUp A h _ (x j)) :=
  heterogeneousStageMap_op A h σ (Fin.last k) x

/-- The explicit heterogeneous algebra on diagonal carriers. -/
noncomputable def heterogeneousDiagonalAlgebra : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig where
  sort := heterogeneousDiagonalSort A
  op {a} {s} σ :=
    { toFun k := ((heterogeneousStage A k).op σ).toFun (Fin.last k)
      map_source j k h x := by
        apply heterogeneousChart_injective A h.le s
        change heterogeneousStageUp A h.le s
          (((heterogeneousStage A j).op σ).toFun (Fin.last j)
            (fun r => (heterogeneousDiagonalDimension A h _).source (x r))) =
          heterogeneousStageUp A h.le s ((heterogeneousDiagonalDimension A h s).source _)
        erw [heterogeneousChart_op, heterogeneousChart_source A h (le_refl k)]
        simp only [heterogeneousChart_source A h (le_refl k), heterogeneousStageUp_self]
        exact ((heterogeneousStage A k).op σ).map_source
          ⟨j, Nat.lt_succ_of_lt h⟩ (Fin.last k) h x
      map_target j k h x := by
        apply heterogeneousChart_injective A h.le s
        change heterogeneousStageUp A h.le s
          (((heterogeneousStage A j).op σ).toFun (Fin.last j)
            (fun r => (heterogeneousDiagonalDimension A h _).target (x r))) =
          heterogeneousStageUp A h.le s ((heterogeneousDiagonalDimension A h s).target _)
        erw [heterogeneousChart_op, heterogeneousChart_target A h (le_refl k)]
        simp only [heterogeneousChart_target A h (le_refl k), heterogeneousStageUp_self]
        exact ((heterogeneousStage A k).op σ).map_target
          ⟨j, Nat.lt_succ_of_lt h⟩ (Fin.last k) h x
      map_identity j k h x := by
        have hh := ((heterogeneousStage A k).op σ).map_identity
          ⟨j, Nat.lt_succ_of_lt h⟩ (Fin.last k) h (fun r => heterogeneousStageUp A h.le _ (x r))
        change _ = (heterogeneousDiagonalDimension A h s).identity
          (((heterogeneousStage A j).op σ).toFun (Fin.last j) x)
        change _ = (((heterogeneousStage A k).sort s).str.dim
          ⟨j, Nat.lt_succ_of_lt h⟩ (Fin.last k) h).identity
            (heterogeneousStageUp A h.le s _)
        erw [heterogeneousChart_op]
        exact hh
      map_comp j k h x y z hz :=
        ((heterogeneousStage A k).op σ).map_comp ⟨j, Nat.lt_succ_of_lt h⟩ (Fin.last k) h x y z hz }

/-- Expansion of the diagonal algebra is exactly the explicit partial diagonal algebra. -/
theorem heterogeneousDiagonalAlgebra_expansion :
    (heterogeneousDiagonalAlgebra A).toPartialAlgebra = heterogeneousDiagonalPartial A := by
  apply congrArg (PartialAlgebra.mk (HeterogeneousDiagonal A))
  funext a s σ x
  cases σ <;> rfl

/-- The explicit diagonal partial algebra satisfies all natural-dimensional model laws. -/
theorem heterogeneousDiagonal_isModel :
    (Heterogeneous.specification ℕ sig).IsModel (heterogeneousDiagonalPartial A) := by
  rw [← heterogeneousDiagonalAlgebra_expansion]
  exact ⟨Heterogeneous.equations_isEPAlgebra (heterogeneousDiagonalAlgebra A).satisfiesEquations,
    fun _ ⟨e, he⟩ => he ▸ (heterogeneousDiagonalAlgebra A).satisfiesEquations e⟩

end CategorialAlgebras.Limits
