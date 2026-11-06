import CategorialAlgebras.Omega.Theta

/-!
# Recovering the homogeneous presentation

Unifying graduated cells forgets the fixed-source proofs. Finite-dimensionality
makes this map surjective, and equality in a common dimension makes it injective.
-/

universe u v w
namespace CategorialAlgebras.Omega
open CategoryTheory Dimensions
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Type u} {sig : Signature.{u, v} S}

/-- Identities in the explicit graduation retain the underlying element, also at equal dimensions. -/
@[simp] theorem graduated_inclusion_val
    (A : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig)
    {j k : ℕ} (h : j ≤ k) (s : S) (x : GraduatedCell A j s) :
    (inclusion (graduatedAlgebra A) h s x).val = x.val := by
  rcases h.lt_or_eq with h | rfl
  · simp only [inclusion, dimensionLE_of_lt _ _ h]
    rfl
  · rw [inclusion_self]

/-- Forget the dimension and the fixed-source proof of a graduated representative. -/
noncomputable def zetaMap (A : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig) (s : S) :
    Cell (graduatedAlgebra A) s → A.carrier s :=
  cellDesc (graduatedAlgebra A) (fun _ x => x.val)
    (fun h x => graduated_inclusion_val A h s x)

/-- The homogeneous comparison sends $[x]_k$ to the original element $x$. -/
@[simp] theorem zetaMap_in (A : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig)
    (k : ℕ) (s : S) (x : GraduatedCell A k s) :
    zetaMap A s (cellIn (graduatedAlgebra A) k s x) = x.val := rfl

/-- Forgetting a graduated representative is injective on quotient classes. -/
theorem zetaMap_injective (A : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig) (s : S) :
    Function.Injective (zetaMap A s) := by
  intro x y h
  obtain ⟨j, x, rfl⟩ := cellIn_surjective (graduatedAlgebra A) s x
  obtain ⟨k, y, rfl⟩ := cellIn_surjective (graduatedAlgebra A) s y
  apply (cellIn_eq_iff _ j k s x y).mpr
  refine ⟨max j k, le_max_left _ _, le_max_right _ _, ?_⟩
  apply Subtype.ext
  simpa only [graduated_inclusion_val] using (show x.val = y.val from h)

/-- Every finite-dimensional cell has a graduated representative. -/
theorem zetaMap_bijective (A : Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig) (s : S) :
    Function.Bijective (zetaMap A.obj s) := by
  refine ⟨zetaMap_injective A.obj s, ?_⟩
  intro x
  obtain ⟨k, hk⟩ := A.property s x
  exact ⟨cellIn (graduatedAlgebra A.obj) k s ⟨x, hk⟩, rfl⟩

/-- Forgetting graduated representatives preserves homogeneous operations. -/
noncomputable def zetaHom (A : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig) :
    unifiedAlgebra (graduatedAlgebra A) ⟶ A where
  sort s :=
    { toFun := zetaMap A s
      map_source k x := by
        obtain ⟨p, hp, y, hy⟩ := cell_cover (graduatedAlgebra A) (fun _ : Fin 1 => s) ![x] (k+1)
        have h0 : cellIn (graduatedAlgebra A) p s (y 0) = x := hy 0
        rw [← h0]
        change zetaMap A s (unifiedSource (graduatedAlgebra A) k s _) = _
        rw [unifiedSource_representative _ (lt_of_lt_of_le (Nat.lt_succ_self k) hp)]
        rfl
      map_target k x := by
        obtain ⟨p, hp, y, hy⟩ := cell_cover (graduatedAlgebra A) (fun _ : Fin 1 => s) ![x] (k+1)
        have h0 : cellIn (graduatedAlgebra A) p s (y 0) = x := hy 0
        rw [← h0]
        change zetaMap A s (unifiedTarget (graduatedAlgebra A) k s _) = _
        rw [unifiedTarget_representative _ (lt_of_lt_of_le (Nat.lt_succ_self k) hp)]
        rfl
      map_comp k x y z hz := by
        obtain ⟨p, hp, t, ht⟩ := cell_cover (graduatedAlgebra A) (fun _ : Fin 3 => s) ![x,y,z] (k+1)
        have h0 : cellIn (graduatedAlgebra A) p s (t 0) = x := ht 0
        have h1 : cellIn (graduatedAlgebra A) p s (t 1) = y := ht 1
        have h2 : cellIn (graduatedAlgebra A) p s (t 2) = z := ht 2
        simp only [← h0, ← h1, ← h2] at hz ⊢
        change _ ∈ unifiedComp (graduatedAlgebra A) k s _ _ at hz
        rw [unifiedComp_mem _ ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hp⟩] at hz
        exact (mem_graduatedComp A (lt_of_lt_of_le (Nat.lt_succ_self k) hp) _ _ _).mp hz }
  map_op {a} {s} σ x := by
    obtain ⟨p, _, y, hy⟩ := cell_cover (graduatedAlgebra A) (fun j => a.get j) x 0
    have hx : (fun j => cellIn (graduatedAlgebra A) p _ (y j)) = x := funext hy
    rw [← hx]
    change zetaMap A s (unifiedBase (graduatedAlgebra A) σ
      (fun j => cellIn (graduatedAlgebra A) p _ (y j))) = _
    rw [unifiedBase_representative]
    rfl

/-- Unification after graduation is naturally isomorphic to the homogeneous identity functor. -/
noncomputable def zeta (sig : Signature.{u, v} S) :
    graduationFunctor.{u, v, w} sig ⋙ unificationFunctor sig ≅
      𝟭 (Homogeneous.OmegaCategorialAlgebra sig) :=
  NatIso.ofComponents (fun A => ObjectProperty.isoMk _
    (homogeneousIsoOfBijective (zetaHom A.obj) (zetaMap_bijective A))) (by
      intro A B f
      apply ObjectProperty.hom_ext
      apply Homogeneous.CategorialAlgebra.Hom.ext
      funext s
      apply Homogeneous.Functor.ext
      funext x
      obtain ⟨k, y, rfl⟩ := cellIn_surjective (graduatedAlgebra A.obj) s x
      rfl)

/-- The natural homogeneous comparison forgets the dimension and cell proof. -/
@[simp] theorem zeta_hom_in (A : Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig)
    (k : ℕ) (s : S) (x : GraduatedCell A.obj k s) :
    ((((zeta sig).hom.app A).hom.sort s).toFun (cellIn (graduatedAlgebra A.obj) k s x)) = x.val := rfl

/-- The inverse homogeneous comparison inserts any representative of the given dimension. -/
theorem zeta_inv_cell (A : Homogeneous.OmegaCategorialAlgebra.{u, v, w} sig)
    (k : ℕ) (s : S) (x : GraduatedCell A.obj k s) :
    ((((zeta sig).inv.app A).hom.sort s).toFun x.val) = cellIn (graduatedAlgebra A.obj) k s x := by
  exact congrArg (fun f : _ ⟶ _ => (f.hom.sort s).toFun
    (cellIn (graduatedAlgebra A.obj) k s x)) ((zeta sig).app A).hom_inv_id

end CategorialAlgebras.Omega
