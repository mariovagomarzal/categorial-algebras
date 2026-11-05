import CategorialAlgebras.Limits.Truncations
import Mathlib.Data.Quot

/-!
# The increasing union of homogeneous finite stages

A coherent truncation family has injective maps from each finite stage to
all later stages. Its union is represented by the quotient of the disjoint
union by these identifications. Operations are computed at a common finite
stage, large enough to contain all inputs and their composition dimensions.
-/

universe u v w

namespace CategorialAlgebras.Limits

open CategoryTheory Dimensions

variable {S : Type u} {sig : Signature.{u, v} S}
variable (A : (homogeneousSystem.{u, v, w} sig).Family)

/-- The algebra recovered on the exact carrier of a homogeneous finite stage. -/
noncomputable def homogeneousStage (n : ℕ) : Homogeneous.NCategorialAlgebra.{u, v, w} n sig :=
  recoveredAlgebra (A.obj n).obj.obj ⟨(A.obj n).obj.property, (A.obj n).property⟩

/-- The inclusion of a lower homogeneous stage in a higher stage. -/
noncomputable def homogeneousStageInclusion {m n : ℕ} (h : m ≤ n) (s : S)
    (x : (A.obj m).obj.obj.carrier s) : (A.obj n).obj.obj.carrier s :=
  (((A.transition h).inv).hom.hom.toMap s x).val

/-- Every inclusion of homogeneous stages is injective. -/
theorem homogeneousStageInclusion_injective {m n : ℕ} (h : m ≤ n) (s : S) :
    Function.Injective (homogeneousStageInclusion A h s) := by
  intro x y hxy
  have hh : (A.transition h).inv.hom.hom.toMap s x =
      (A.transition h).inv.hom.hom.toMap s y := Subtype.ext hxy
  have he z : (A.transition h).hom.hom.hom.toMap s
      ((A.transition h).inv.hom.hom.toMap s z) = z :=
    congrArg (fun f : A.obj m ⟶ A.obj m => f.hom.hom.toMap s z) (A.transition h).inv_hom_id
  have hv := congrArg ((A.transition h).hom.hom.hom.toMap s) hh
  simpa only [he] using hv

/-- The relation identifying a finite cell with its inclusion in any later stage. -/
def homogeneousUnionRelation (s : S)
    (x y : Σ n, (A.obj n).obj.obj.carrier s) : Prop :=
  ∃ h : x.1 ≤ y.1, homogeneousStageInclusion A h s x.2 = y.2

/-- The increasing union of the finite carriers at a sort. -/
def HomogeneousUnion (s : S) : Type w := Quot (homogeneousUnionRelation A s)

/-- Insert a finite-stage cell in the union. -/
def homogeneousUnionIn (n : ℕ) (s : S) (x : (A.obj n).obj.obj.carrier s) :
    HomogeneousUnion A s := Quot.mk _ ⟨n, x⟩

/-- Inclusion in the union identifies a cell with every later-stage inclusion. -/
theorem homogeneousUnionIn_inclusion {m n : ℕ} (h : m ≤ n) (s : S)
    (x : (A.obj m).obj.obj.carrier s) :
    homogeneousUnionIn A m s x =
      homogeneousUnionIn A n s (homogeneousStageInclusion A h s x) :=
  Quot.sound ⟨h, rfl⟩

/-- Every union cell is represented by a cell in a finite stage. -/
theorem homogeneousUnionIn_surjective (s : S) (x : HomogeneousUnion A s) :
    ∃ n y, homogeneousUnionIn A n s y = x := by
  exact ⟨(Quot.out x).1, (Quot.out x).2, Quot.out_eq x⟩

/-- A chosen union representative transported to a specified later stage. -/
noncomputable def homogeneousUnionAt (s : S) (x : HomogeneousUnion A s) (n : ℕ)
    (h : (Quot.out x).1 ≤ n) : (homogeneousStage A n).carrier s :=
  homogeneousStageInclusion A h s (Quot.out x).2

/-- A common stage containing the chosen representatives of an input word. -/
noncomputable def homogeneousWordStage {a : List S}
    (x : Word.Family (HomogeneousUnion A) a) : ℕ := by
  classical
  exact Finset.univ.sup (fun j => (Quot.out (x j)).1)

/-- Each chosen input representative lies below the common word stage. -/
theorem homogeneousWordStage_le {a : List S}
    (x : Word.Family (HomogeneousUnion A) a) (j : Fin a.length) :
    (Quot.out (x j)).1 ≤ homogeneousWordStage A x := by
  classical
  exact Finset.le_sup (f := fun j : Fin a.length => (Quot.out (x j)).1) (Finset.mem_univ j)

/-- Interpret an original operation in a common finite stage, also for an empty word. -/
noncomputable def homogeneousUnionBase {a s} (σ : sig a s)
    (x : Word.Family (HomogeneousUnion A) a) : HomogeneousUnion A s :=
  homogeneousUnionIn A (homogeneousWordStage A x) s
    (((homogeneousStage A (homogeneousWordStage A x)).op σ).toFun
      (fun j => homogeneousUnionAt A _ (x j) _ (homogeneousWordStage_le A x j)))

/-- Compute a source in a finite stage containing the representative and its dimension. -/
noncomputable def homogeneousUnionSource (k : ℕ) (s : S) (x : HomogeneousUnion A s) :
    HomogeneousUnion A s :=
  let n := max (k + 1) (Quot.out x).1
  homogeneousUnionIn A n s
    ((((homogeneousStage A n).sort s).str.dim
      ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_left _ _)⟩).source
      (homogeneousUnionAt A s x n (le_max_right _ _)))

/-- Compute a target in a finite stage containing the representative and its dimension. -/
noncomputable def homogeneousUnionTarget (k : ℕ) (s : S) (x : HomogeneousUnion A s) :
    HomogeneousUnion A s :=
  let n := max (k + 1) (Quot.out x).1
  homogeneousUnionIn A n s
    ((((homogeneousStage A n).sort s).str.dim
      ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_left _ _)⟩).target
      (homogeneousUnionAt A s x n (le_max_right _ _)))

/-- Compute partial composition in a common finite stage and insert its value in the union. -/
noncomputable def homogeneousUnionComp (k : ℕ) (s : S) (x y : HomogeneousUnion A s) :
    Part (HomogeneousUnion A s) :=
  let n := max (k + 1) (max (Quot.out x).1 (Quot.out y).1)
  Part.map (homogeneousUnionIn A n s)
    ((((homogeneousStage A n).sort s).str.dim
      ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_left _ _)⟩).comp
      (homogeneousUnionAt A s x n (le_trans (le_max_left _ _) (le_max_right _ _)))
      (homogeneousUnionAt A s y n (le_trans (le_max_right _ _) (le_max_right _ _))))

/-- The explicit partial algebra on the increasing union of the finite carriers. -/
noncomputable def homogeneousUnionPartial :
    PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol ℕ sig) where
  carrier := HomogeneousUnion A
  op
    | .base σ, x => Part.some (homogeneousUnionBase A σ x)
    | .source k s, x => Part.some (homogeneousUnionSource A k s (x 0))
    | .target k s, x => Part.some (homogeneousUnionTarget A k s (x 0))
    | .comp k s, x => homogeneousUnionComp A k s (x 0) (x 1)

end CategorialAlgebras.Limits
