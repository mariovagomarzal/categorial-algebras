import CategorialAlgebras.Omega.Graduation
import CategorialAlgebras.Omega.Unification
import CategorialAlgebras.Omega.Isomorphisms

/-!
# Recovering the heterogeneous presentation

The dimensional injection identifies each original carrier with the cells of
that dimension in the unified algebra. These bijections are natural and
preserve all heterogeneous operations.
-/

universe u v w
namespace CategorialAlgebras.Omega
open CategoryTheory Dimensions
set_option backward.isDefEq.respectTransparency false
variable {S : Type u} {sig : Signature.{u, v} S}

/-- Insert a dimensional cell into the graduation of unification. -/
noncomputable def thetaCell (B : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig)
    (k : ℕ) (s : S) (x : B.carrier (k, s)) : GraduatedCell (unifiedAlgebra B) k s :=
  ⟨cellIn B k s x, cellIn_isCell B k s x⟩

/-- The insertion identifies the original carrier with the corresponding fixed-source subtype. -/
theorem thetaCell_bijective (B : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig)
    (k : ℕ) (s : S) : Function.Bijective (thetaCell B k s) := by
  constructor
  · intro x y h
    exact cellIn_injective B k s (congrArg Subtype.val h)
  · intro x
    obtain ⟨y, hy⟩ := (unified_isCell_iff B k s x.val).mp x.property
    exact ⟨y, Subtype.ext hy⟩

/-- The dimensional injections form a heterogeneous homomorphism. -/
noncomputable def thetaHom (B : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig) :
    B ⟶ graduatedAlgebra (unifiedAlgebra B) where
  sort s :=
    { toFun k := thetaCell B k s
      map_source j k h x := Subtype.ext (unifiedSource_representative B h s x).symm
      map_target j k h x := Subtype.ext (unifiedTarget_representative B h s x).symm
      map_identity j k h x := by
        apply Subtype.ext
        change cellIn B k s (((B.sort s).str.dim j k h).identity x) = cellIn B j s x
        simpa only [inclusion, dimensionLE_of_lt _ _ h] using cellIn_inclusion B h.le s x
      map_comp j k h x y z hz := by
        apply (mem_graduatedComp (unifiedAlgebra B) h _ _ _).mpr
        exact (unifiedComp_mem B ⟨j, h⟩ s x y z).mpr hz }
  map_op σ k x := Subtype.ext (unifiedBase_representative B σ k x).symm

/-- The original heterogeneous algebra is naturally isomorphic to graduation after unification. -/
noncomputable def theta (sig : Signature.{u, v} S) :
    𝟭 (Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig) ≅
      unificationFunctor sig ⋙ graduationFunctor sig :=
  NatIso.ofComponents
    (fun B => heterogeneousIsoOfBijective (thetaHom B) (fun s k => thetaCell_bijective B k s))
    (by
      intro A B f
      apply Heterogeneous.CategorialAlgebra.Hom.ext
      funext s
      apply Heterogeneous.Functor.ext
      funext k x
      apply Subtype.ext
      rfl)

/-- The forward heterogeneous comparison sends $x$ to its class $[x]_k$. -/
@[simp] theorem theta_hom_val (B : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig)
    (k : ℕ) (s : S) (x : B.carrier (k, s)) :
    ((((theta sig).hom.app B).sort s).toFun k x).val = cellIn B k s x := rfl

/-- The inverse heterogeneous comparison recovers every original representative. -/
@[simp] theorem theta_inv_in (B : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig)
    (k : ℕ) (s : S) (x : B.carrier (k, s)) :
    (((theta sig).inv.app B).sort s).toFun k (thetaCell B k s x) = x :=
  congrArg (fun f : B ⟶ B => (f.sort s).toFun k x) ((theta sig).app B).hom_inv_id

end CategorialAlgebras.Omega
