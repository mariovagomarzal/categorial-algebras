import CategorialAlgebras.Presentations.Graduation

/-!
# Graduation needs the categorical equations

A two-element ep-algebra with fixed-point-free boundaries has no lower cells, while
its top sort is inhabited. Its graduated source therefore cannot be total.
-/

universe u v

namespace CategorialAlgebras.Presentations.GraduationCounterexample

variable (n : ℕ) {S : Type u} (sig : Signature.{u, v} S)

/-- Two cells per sort, transposed boundaries, diagonal composition and constant base operations. -/
def algebra : PartialAlgebra (Homogeneous.Symbol (Fin n) sig) where
  carrier _ := Bool
  op
    | .base _, _ => Part.some false
    | .source _ _, x => Part.some (!(x 0))
    | .target _ _, x => Part.some (!(x 0))
    | .comp _ _, x => ⟨x 0 = x 1, fun _ => x 0⟩

/-- The transposed boundaries give precisely the diagonal composition domains. -/
theorem algebra_isEPAlgebra : (Homogeneous.epSignature (Fin n) sig).IsEPAlgebra
    (algebra n sig) := by
  intro a s σ x
  cases σ with
  | base σ => exact ⟨fun _ _ _ he => he.elim, fun _ => Part.some_dom _⟩
  | source k s => exact ⟨fun _ _ _ he => he.elim, fun _ => Part.some_dom _⟩
  | target k s => exact ⟨fun _ _ _ he => he.elim, fun _ => Part.some_dom _⟩
  | comp k s =>
    constructor
    · intro h t e ⟨ht, he⟩
      cases ht
      cases he
      refine ⟨!(x 0), ?_, ?_⟩
      · change _ ∈ Term.partialEval _ (Homogeneous.unary _ _)
        erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some]
        exact Part.mem_some _
      · change _ ∈ Term.partialEval _ (Homogeneous.unary _ _)
        erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some]
        exact Part.mem_some_iff.mpr (congrArg Bool.not h)
    · intro h
      obtain ⟨q, hq, hr⟩ := h s (Homogeneous.compositionDomain k s) ⟨rfl, rfl⟩
      change q ∈ Term.partialEval _ (Homogeneous.unary _ _) at hq hr
      erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some] at hq hr
      have he : Bool.not (x 0) = Bool.not (x 1) :=
        (Part.mem_some_iff.mp hq).symm.trans (Part.mem_some_iff.mp hr)
      change x 0 = x 1
      cases hx : x 0 <;> cases hy : x 1 <;> simp_all <;> rfl

/-- A lower sort of the graduated ep-algebra is empty. -/
theorem no_lower_cell (k : Fin n) (s : S) (x : Bool) :
    ¬ (graduation n sig).IsCell (algebra n sig) (k.castSucc, s) x := by
  intro h
  have hk : (k.castSucc : Fin (n + 1)).val < n := k.isLt
  have hd : (graduation n sig).domain (k.castSucc, s) =
      Homogeneous.singletonEquation (graduationEquation n sig k s) := by
    change (if h : k.val < n then _ else _) = _
    erw [dite_eq_left hk]
    rfl
  have hh := h s (graduationEquation n sig k s) (by rw [hd]; exact ⟨rfl, rfl⟩)
  obtain ⟨q, hq, hr⟩ := hh
  have hqx : q = x := Part.mem_some_iff.mp hq
  change q ∈ Term.partialEval _ (Homogeneous.unary _ _) at hr
  erw [Homogeneous.partialEval_unary, Term.partialEval_var, Part.bind_some] at hr
  have hqnx : q = !x := Part.mem_some_iff.mp hr
  have he : x = !x := hqx.symm.trans hqnx
  cases x <;> cases he

/-- For positive dimension and a nonempty set of sorts, graduation fails on ep-algebras. -/
theorem graduation_not_isEPAlgebra (hn : 0 < n) [Nonempty S] :
    ¬ (Heterogeneous.epSignature (Fin (n + 1)) sig).IsEPAlgebra
      ((graduation n sig).transformed (algebra n sig)) := by
  intro h
  let s : S := Classical.choice ‹Nonempty S›
  let k : Fin n := ⟨0, hn⟩
  let x : (graduation n sig).Cell (algebra n sig) (Fin.last n, s) :=
    ⟨false, by
      intro t e he
      rw [graduation_domain_last] at he
      exact he.elim⟩
  have hd := (h (.source (castSucc_lt_last k) s) (Heterogeneous.single x)).mpr
    (fun _ _ he => he.elim)
  let y := (((graduation n sig).transformed (algebra n sig)).op
    (.source (castSucc_lt_last k) s) (Heterogeneous.single x)).get hd
  exact no_lower_cell n sig k s y.val y.property

/-- There exists an ep-algebra whose graduation is not an ep-algebra. -/
theorem exists_epAlgebra_graduation_failure (hn : 0 < n) [Nonempty S] :
    ∃ B : PartialAlgebra.{u, max v u, 0} (Homogeneous.Symbol (Fin n) sig),
      (Homogeneous.epSignature (Fin n) sig).IsEPAlgebra B ∧
      ¬ (Heterogeneous.epSignature (Fin (n + 1)) sig).IsEPAlgebra
        ((graduation n sig).transformed B) :=
  ⟨algebra n sig, algebra_isEPAlgebra n sig, graduation_not_isEPAlgebra n sig hn⟩

end CategorialAlgebras.Presentations.GraduationCounterexample
