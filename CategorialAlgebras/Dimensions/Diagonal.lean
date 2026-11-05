import CategorialAlgebras.Dimensions.Descriptions

/-!
# A diagonal imposed by domain equations

For an empty original signature in dimension zero, all terms are variables and
all term operations are total. Discretization to dimension one nevertheless
has composition only on the diagonal. Thus its domain is not imposed by a term.
-/

universe w

namespace CategorialAlgebras.Dimensions.Diagonal

/-- A single sort with no original operation symbols. -/
def emptySignature : Signature.{0, 0} Unit := fun _ _ => PEmpty

/-- An arbitrary set as a zero-dimensional algebra over the empty signature. -/
noncomputable def zeroAlgebra (X : Type w) : Homogeneous.NCategorialAlgebra 0 emptySignature where
  sort _ := Homogeneous.HigherCategory.discrete (Fin 0) X
  op σ := PEmpty.elim σ

/-- Every term operation in the zero-dimensional empty signature is total. -/
theorem term_total (X : Type w) {V : Unit → Type*}
    (v : SortedSet.Map V (zeroAlgebra X).carrier) {s}
    (t : Term (Homogeneous.Symbol (Fin 0) emptySignature) V s) :
    (Term.partialEval (A := (zeroAlgebra X).toPartialAlgebra) v t).Dom := by
  cases t with
  | var x => exact Part.some_dom _
  | app σ _ =>
    cases σ with
    | base σ => exact PEmpty.elim σ
    | source k _ => exact Fin.elim0 k
    | target k _ => exact Fin.elim0 k
    | comp k _ => exact Fin.elim0 k

/-- The transformed composition is defined precisely when its two inputs coincide. -/
theorem composition_dom (X : Type w) (x y : X) :
    (((homogeneousDiscretization emptySignature (show 0 ≤ 1 by omega)).transformed
      (zeroAlgebra X).toPartialAlgebra).op (.comp 0 ())
        (Homogeneous.pair
          (discretizationCell emptySignature (show 0 ≤ 1 by omega) (zeroAlgebra X).toPartialAlgebra () x)
          (discretizationCell emptySignature (show 0 ≤ 1 by omega) (zeroAlgebra X).toPartialAlgebra () y))).Dom ↔
      x = y := by
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨z, hz⟩
    have hh := (discretization_comp_diagonal emptySignature (show 0 ≤ 1 by omega)
      (zeroAlgebra X) 0 (le_refl 0) () x y z.val).mp hz
    exact hh.1
  · intro he
    exact ⟨discretizationCell emptySignature (show 0 ≤ 1 by omega) (zeroAlgebra X).toPartialAlgebra () x,
      (discretization_comp_diagonal emptySignature (show 0 ≤ 1 by omega)
        (zeroAlgebra X) 0 (le_refl 0) () x y x).mpr ⟨he, rfl⟩⟩

/-- With two distinct elements no term can have the domain of transformed composition. -/
theorem no_term_domain (X : Type w) (x y : X) (hxy : x ≠ y)
    (t : Term (Homogeneous.Symbol (Fin 0) emptySignature) (Word.Variables [(), ()]) ()) :
    ¬ ((((homogeneousDiscretization emptySignature (show 0 ≤ 1 by omega)).transformed
      (zeroAlgebra X).toPartialAlgebra).op (.comp 0 ())
        (Homogeneous.pair
          (discretizationCell emptySignature (show 0 ≤ 1 by omega) (zeroAlgebra X).toPartialAlgebra () x)
          (discretizationCell emptySignature (show 0 ≤ 1 by omega) (zeroAlgebra X).toPartialAlgebra () y))).Dom ↔
      (Term.partialEval (A := (zeroAlgebra X).toPartialAlgebra)
        (Word.valuation (φ := id) (Homogeneous.pair x y)) t).Dom) := by
  intro he
  exact hxy ((composition_dom X x y).mp (he.mpr (term_total X _ t)))

end CategorialAlgebras.Dimensions.Diagonal
