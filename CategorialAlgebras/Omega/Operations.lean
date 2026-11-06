import CategorialAlgebras.Omega.Stages

/-!
# Operations on unified cells

Each operation is evaluated on selected representatives raised to a common
finite dimension. The bounds include the composition dimension and handle
nullary operations as well as empty carriers.
-/

universe u v w
namespace CategorialAlgebras.Omega
variable {S : Type u} {sig : Signature.{u, v} S}
variable (B : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig)

/-- Raising a representative does not change its quotient class. -/
theorem cellIn_raise {j k : ℕ} (h : j ≤ k) (s : S) (x : B.carrier (j, s)) :
    cellIn B j s x = cellIn B k s (inclusion B h s x) :=
  (cellIn_inclusion B h s x).symm

/-- A chosen union representative transported to a specified later stage. -/
noncomputable def cellAt (s : S) (x : Cell B s) (n : ℕ)
    (h : (Quotient.out x).1 ≤ n) : (stageAlgebra B n).carrier s :=
  inclusion B h s (Quotient.out x).2

/-- A common stage containing the chosen representatives of an input word. -/
noncomputable def wordStage {a : List S}
    (x : Word.Family (Cell B) a) : ℕ := by
  classical
  exact Finset.univ.sup (fun j => (Quotient.out (x j)).1)

/-- Each chosen input representative lies below the common word stage. -/
theorem wordStage_le {a : List S}
    (x : Word.Family (Cell B) a) (j : Fin a.length) :
    (Quotient.out (x j)).1 ≤ wordStage B x := by
  classical
  exact Finset.le_sup (f := fun j : Fin a.length => (Quotient.out (x j)).1) (Finset.mem_univ j)

/-- Interpret an original operation in a common finite stage, also for an empty word. -/
noncomputable def unifiedBase {a s} (σ : sig a s)
    (x : Word.Family (Cell B) a) : Cell B s :=
  cellIn B (wordStage B x) s
    (((stageAlgebra B (wordStage B x)).op σ).toFun
      (fun j => cellAt B _ (x j) _ (wordStage_le B x j)))

/-- Compute a source in a finite stage containing the representative and its dimension. -/
noncomputable def unifiedSource (k : ℕ) (s : S) (x : Cell B s) :
    Cell B s :=
  let n := max (k + 1) (Quotient.out x).1
  cellIn B n s
    ((((stageAlgebra B n).sort s).str.dim
      ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_left _ _)⟩).source
      (cellAt B s x n (le_max_right _ _)))

/-- Compute a target in a finite stage containing the representative and its dimension. -/
noncomputable def unifiedTarget (k : ℕ) (s : S) (x : Cell B s) :
    Cell B s :=
  let n := max (k + 1) (Quotient.out x).1
  cellIn B n s
    ((((stageAlgebra B n).sort s).str.dim
      ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_left _ _)⟩).target
      (cellAt B s x n (le_max_right _ _)))

/-- Compute partial composition in a common finite stage and insert its value in the union. -/
noncomputable def unifiedComp (k : ℕ) (s : S) (x y : Cell B s) :
    Part (Cell B s) :=
  let n := max (k + 1) (max (Quotient.out x).1 (Quotient.out y).1)
  Part.map (cellIn B n s)
    ((((stageAlgebra B n).sort s).str.dim
      ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_left _ _)⟩).comp
      (cellAt B s x n (le_trans (le_max_left _ _) (le_max_right _ _)))
      (cellAt B s y n (le_trans (le_max_right _ _) (le_max_right _ _))))

/-- The explicit partial algebra on the increasing union of the finite carriers. -/
noncomputable def unifiedPartial :
    PartialAlgebra.{u, max v u, w} (Homogeneous.Symbol ℕ sig) where
  carrier := Cell B
  op
    | .base σ, x => Part.some (unifiedBase B σ x)
    | .source k s, x => Part.some (unifiedSource B k s (x 0))
    | .target k s, x => Part.some (unifiedTarget B k s (x 0))
    | .comp k s, x => unifiedComp B k s (x 0) (x 1)

end CategorialAlgebras.Omega
