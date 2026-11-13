import CategorialAlgebras.Heterogeneous.Evaluation
import Mathlib.Data.Fin.VecNotation

/-!
# Recovery from heterogeneous equations

Totality recovers boundaries, identities and original operations without choosing arbitrary
values. The remaining equations recover the categorical structures and their compatibilities.
-/

universe i u v w x

namespace CategorialAlgebras.Heterogeneous

open CategoryTheory

variable {I : Type i} [Preorder I] {S : Type u} {sig : Signature.{u, v} S}

/-! ## Total values and evaluation -/

/-- The total boundary recovered from the equations. -/
def boundaryValue {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)}
    (hA : SatisfiesEquations A) {j k : I} (h : j < k) (b : Bool) {s}
    (x : A.carrier (k, s)) : A.carrier (j, s) :=
  (A.op (.boundary h s b) (single x)).get (boundary_total hA h s b x)

/-- The total identity recovered from the equations. -/
def identityValue {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)}
    (hA : SatisfiesEquations A) {j k : I} (h : j < k) {s}
    (x : A.carrier (j, s)) : A.carrier (k, s) :=
  (A.op (.identity h s) (single x)).get (identity_total hA h s x)

/-- Recovered boundaries give the original partial operation. -/
theorem boundary_op {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)}
    (hA : SatisfiesEquations A) {j k : I} (h : j < k) (b : Bool) {s}
    (x : Word.Family A.carrier [(k, s)]) :
    A.op (.boundary h s b) x = Part.some (boundaryValue hA h b (x 0)) := by
  erw [← single_eta x]
  exact Part.eq_some_iff.mpr (Part.get_mem _)

/-- Recovered identities give the original partial operation. -/
theorem identity_op {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)}
    (hA : SatisfiesEquations A) {j k : I} (h : j < k) {s}
    (x : Word.Family A.carrier [(j, s)]) :
    A.op (.identity h s) x = Part.some (identityValue hA h (x 0)) := by
  erw [← single_eta x]
  exact Part.eq_some_iff.mpr (Part.get_mem _)

/-- The original operation recovered in one dimension. -/
def operationValue {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)}
    (hA : SatisfiesEquations A) (k : I) {a s} (σ : sig a s)
    (x : Word.Family (fun s => A.carrier (k, s)) a) : A.carrier (k, s) :=
  (A.op (.base k σ) ((dimensionFamily k a).symm x)).get (base_total hA k σ _)

/-- Recovered original operations give the original partial values. -/
theorem base_op {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)}
    (hA : SatisfiesEquations A) (k : I) {a s} (σ : sig a s)
    (x : Word.Family A.carrier (dimensionWord k a)) :
    A.op (.base k σ) x = Part.some (operationValue hA k σ (dimensionFamily k a x)) := by
  unfold operationValue
  apply Part.eq_some_iff.mpr
  simpa only [Equiv.symm_apply_apply] using
    (Part.get_mem (base_total hA k σ ((dimensionFamily k a).symm (dimensionFamily k a x))))

/-- Evaluation of a boundary uses its recovered total map. -/
theorem eval_boundary {X : I × S → Type x}
    {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)} (hA : SatisfiesEquations A)
    (v : SortedSet.Map X A.carrier) {j k : I} (h : j < k) (b : Bool) {s}
    (t : Term (Symbol I sig) X (k, s)) :
    Term.partialEval v (boundary h b t) =
      (Term.partialEval v t).bind (fun x => Part.some (boundaryValue hA h b x)) := by
  erw [boundary, partialEval_unary]
  congr 1
  funext x
  exact boundary_op hA h b (single x)

/-- Evaluation of an identity uses its recovered total map. -/
theorem eval_identity {X : I × S → Type x}
    {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)} (hA : SatisfiesEquations A)
    (v : SortedSet.Map X A.carrier) {j k : I} (h : j < k) {s}
    (t : Term (Symbol I sig) X (j, s)) :
    Term.partialEval v (identityTerm h t) =
      (Term.partialEval v t).bind (fun x => Part.some (identityValue hA h x)) := by
  erw [identityTerm, partialEval_unary]
  congr 1
  funext x
  exact identity_op hA h (single x)

/-! ## Pairwise categorical laws -/

/-- The domain of a recovered composition is equality of its two total boundaries. -/
theorem composition_dom {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)}
    (h : SatisfiesEquations A) {j k : I} (hk : j < k) {s} (x y : A.carrier (k, s)) :
    (A.op (.comp hk s) (pair x y)).Dom ↔
      boundaryValue h hk false x = boundaryValue h hk true y := by
  have hf := (uniform_valid_iff A _ _).mp (h (.domainForward hk s)) ![x, y]
  have hb := (uniform_valid_iff A _ _).mp (h (.domainBackward hk s)) ![x, y]
  have hd : EEquation.Satisfies A (uniformValuation ![x, y])
      (defined (binary hk (variableTerm (k, s) 0) (variableTerm (k, s) 1))) ↔
      (A.op (.comp hk s) (pair x y)).Dom := by
    erw [satisfies_defined, partialEval_binary]
    simp only [variableTerm, Term.partialEval, uniformValuation, Part.bind_some,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  have he : EEquation.Satisfies A (uniformValuation ![x, y])
      (boundary hk false (variableTerm (k, s) (m := 2) 0),
        boundary hk true (variableTerm (k, s) 1)) ↔
      boundaryValue h hk false x = boundaryValue h hk true y := by
    unfold EEquation.Satisfies
    erw [eval_boundary h, eval_boundary h]
    simp only [variableTerm, Term.partialEval, uniformValuation, Part.bind_some,
      Matrix.cons_val_zero, Matrix.cons_val_one, Part.mem_some_iff, exists_eq_left]
  exact ⟨fun hd' => he.mp (hf (by intro r; fin_cases r; exact hd.mpr hd')),
    fun he' => hd.mp (hb (by intro r; fin_cases r; exact he.mpr he'))⟩

/-- Recovered boundaries give the two unit composites. -/
theorem boundary_unit {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)}
    (h : SatisfiesEquations A) {j k : I} (hk : j < k) {s} (x : A.carrier (k, s)) :
    x ∈ A.op (.comp hk s) (pair x (identityValue h hk (boundaryValue h hk false x))) ∧
      x ∈ A.op (.comp hk s) (pair (identityValue h hk (boundaryValue h hk true x)) x) := by
  have hh b := (uniform_valid_iff A _ _).mp (h (.unit hk s b)) (fun _ => x)
    (fun j => Fin.elim0 j)
  constructor
  · have hu := hh false
    unfold EEquation.Satisfies at hu
    simpa only [Bool.false_eq_true, ↓reduceIte, partialEval_binary, eval_identity h,
      eval_boundary h, eval_uniform_variable, Part.bind_some,
      Part.mem_some_iff, exists_eq_right] using hu
  · have hu := hh true
    unfold EEquation.Satisfies at hu
    simpa only [↓reduceIte, partialEval_binary, eval_identity h, eval_boundary h,
      eval_uniform_variable, Part.bind_some, Part.mem_some_iff, exists_eq_right] using hu

/-- Recovered boundaries of a composite are its outer boundaries. -/
theorem boundary_composite {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)}
    (h : SatisfiesEquations A) {j k : I} (hk : j < k) (b : Bool) {s} (x y z : A.carrier (k, s))
    (hz : z ∈ A.op (.comp hk s) (pair x y)) :
    boundaryValue h hk b z = boundaryValue h hk b (if b then x else y) := by
  have hh := (uniform_valid_iff A _ _).mp (h (.compositeBoundary hk s b)) ![x, y]
  have hp : EEquation.Satisfies A (uniformValuation ![x, y])
      (defined (binary hk (variableTerm (k, s) 0) (variableTerm (k, s) 1))) := by
    erw [satisfies_defined, partialEval_binary]
    simpa only [eval_uniform_variable, Matrix.cons_val_zero, Matrix.cons_val_one,
      Part.bind_some] using hz.1
  have hc := hh (by intro r; fin_cases r; exact hp)
  unfold EEquation.Satisfies at hc
  cases b <;>
    simp only [Bool.false_eq_true, ↓reduceIte, eval_boundary h, partialEval_binary,
      eval_uniform_variable, Matrix.cons_val_zero, Matrix.cons_val_one, Part.bind_some,
      Part.mem_bind_iff, Part.mem_some_iff] at hc
  all_goals
    obtain ⟨q, ⟨r, hr, hq⟩, hq'⟩ := hc
    have he := Part.mem_unique hr hz
    subst r
    exact hq.symm.trans hq'

/-- The recovered partial compositions associate whenever adjacent pairs exist. -/
theorem composition_assoc {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)}
    (h : SatisfiesEquations A) {j k : I} (hk : j < k) {s} (x y z xy yz : A.carrier (k, s))
    (hxy : xy ∈ A.op (.comp hk s) (pair x y))
    (hyz : yz ∈ A.op (.comp hk s) (pair y z)) :
    ∃ q, q ∈ A.op (.comp hk s) (pair xy z) ∧ q ∈ A.op (.comp hk s) (pair x yz) := by
  have hh := (uniform_valid_iff A _ _).mp (h (.assoc hk s)) ![x, y, z]
  have hp : ∀ j, EEquation.Satisfies A (uniformValuation ![x, y, z])
      (Fin.cases (defined (binary hk (variableTerm (k, s) 0) (variableTerm (k, s) 1)))
        (Fin.cases (defined (binary hk (variableTerm (k, s) 1) (variableTerm (k, s) 2)))
          Fin.elim0) j) := by
    intro j
    fin_cases j
    · erw [satisfies_defined, partialEval_binary]
      simpa only [eval_uniform_variable, Matrix.cons_val_zero, Matrix.cons_val_one,
        Part.bind_some] using hxy.1
    · erw [satisfies_defined, partialEval_binary]
      change ((Part.some y).bind (fun y => (Part.some z).bind
        (fun z => A.op (.comp hk s) (pair y z)))).Dom
      simpa only [Part.bind_some] using hyz.1
  have hc := hh (by intro r; fin_cases r; exact hp 0; exact hp 1)
  unfold EEquation.Satisfies at hc
  simp only [partialEval_binary, eval_uniform_variable, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Part.bind_some, Part.mem_bind_iff] at hc
  obtain ⟨q, ⟨r, hr, hq⟩, r', hr', hq'⟩ := hc
  have he := Part.mem_unique hr hxy
  have he' := Part.mem_unique hr' hyz
  subst r
  subst r'
  exact ⟨q, hq, hq'⟩

/-- Each boundary retracts the recovered identity. -/
theorem boundary_retract {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)}
    (hA : SatisfiesEquations A) {j k : I} (h : j < k) (b : Bool) {s}
    (x : A.carrier (j, s)) : boundaryValue hA h b (identityValue hA h x) = x := by
  have hh := (uniform_valid_iff A _ _).mp (hA (.retract h s b)) (fun _ => x)
    (fun p => Fin.elim0 p)
  unfold EEquation.Satisfies at hh
  simpa only [eval_boundary hA, eval_identity hA, eval_uniform_variable, Part.bind_some,
    Part.mem_some_iff, exists_eq_left] using hh

/-- The category structure recovered for an increasing pair of dimensions. -/
def recoveredDimension {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)}
    (hA : SatisfiesEquations A) {j k : I} (h : j < k) (s : S) :
    CategoryStructure (A.carrier (j, s)) (A.carrier (k, s)) where
  source := boundaryValue hA h false
  target := boundaryValue hA h true
  identity := identityValue hA h
  comp x y := A.op (.comp h s) (pair x y)
  source_identity := boundary_retract hA h false
  target_identity := boundary_retract hA h true
  comp_dom := composition_dom hA h
  source_comp := by simpa only [Bool.false_eq_true, ↓reduceIte] using boundary_composite hA h false
  target_comp := by simpa only [↓reduceIte] using boundary_composite hA h true
  comp_source x := (boundary_unit hA h x).1
  target_comp_self x := (boundary_unit hA h x).2
  assoc := composition_assoc hA h

/-! ## Equationally partial domains -/

/-- Every algebra satisfying the equations has exactly the specified domains. -/
theorem equations_isEPAlgebra
    {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)} (hA : SatisfiesEquations A) :
    (epSignature I sig).IsEPAlgebra A := by
  intro a s σ z
  cases σ with
  | base k σ => exact ⟨fun _ _ _ he => he.elim, fun _ => base_total hA k σ z⟩
  | source h s =>
    exact ⟨fun _ _ _ he => he.elim, fun _ => by
      have hh := boundary_total hA h s false (z 0)
      erw [single_eta] at hh
      exact hh⟩
  | target h s =>
    exact ⟨fun _ _ _ he => he.elim, fun _ => by
      have hh := boundary_total hA h s true (z 0)
      erw [single_eta] at hh
      exact hh⟩
  | identity h s =>
    exact ⟨fun _ _ _ he => he.elim, fun _ => by
      have hh := identity_total hA h s (z 0)
      erw [single_eta] at hh
      exact hh⟩
  | comp h s =>
    have hd := composition_dom hA h (z 0) (z 1)
    erw [pair_eta] at hd
    erw [hd]
    change _ ↔ EEquationSet.Satisfies A (Word.valuation (φ := id) z)
      (singletonEquation (compositionDomain h s))
    have hs : EEquationSet.Satisfies A (Word.valuation (φ := id) z)
        (singletonEquation (compositionDomain h s)) ↔
        EEquation.Satisfies A (Word.valuation (φ := id) z) (compositionDomain h s) := by
      constructor
      · intro hh
        exact hh _ _ ⟨rfl, rfl⟩
      · rintro hh t e ⟨ht, he⟩
        cases ht
        cases he
        exact hh
    rw [hs]
    simp only [compositionDomain, EEquation.Satisfies, eval_boundary hA,
      Term.partialEval, Part.bind_some, Part.mem_some_iff, exists_eq_left]
    rfl

/-- The equations alone characterize models of the ep-specification. -/
theorem isModel_iff_equations (A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)) :
    (specification I sig).IsModel A ↔ SatisfiesEquations A := by
  constructor
  · rintro ⟨_, h⟩ e
    exact h _ ⟨e, rfl⟩
  · intro h
    exact ⟨equations_isEPAlgebra h, fun _ ⟨e, he⟩ => he ▸ h e⟩

/-! ## Compatibility of dimensions -/

/-- Recovered boundaries are globular. -/
theorem globular_boundary {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)}
    (hA : SatisfiesEquations A) {h j k : I} (hj : h < j) (jk : j < k)
    (b c : Bool) {s} (x : A.carrier (k, s)) :
    boundaryValue hA hj b (boundaryValue hA jk c x) =
      boundaryValue hA (lt_trans hj jk) b x := by
  have hh := (uniform_valid_iff A _ _).mp (hA (.globular hj jk s b c)) (fun _ => x)
    (fun p => Fin.elim0 p)
  unfold EEquation.Satisfies at hh
  simpa only [eval_boundary hA, eval_uniform_variable, Part.bind_some,
    Part.mem_some_iff, exists_eq_left] using hh

/-- Successive recovered identities agree with the direct identity. -/
theorem identity_identity {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)}
    (hA : SatisfiesEquations A) {h j k : I} (hj : h < j) (jk : j < k)
    {s} (x : A.carrier (h, s)) :
    identityValue hA jk (identityValue hA hj x) = identityValue hA (lt_trans hj jk) x := by
  have hh := (uniform_valid_iff A _ _).mp (hA (.identityIdentity hj jk s)) (fun _ => x)
    (fun p => Fin.elim0 p)
  unfold EEquation.Satisfies at hh
  simpa only [eval_identity hA, eval_uniform_variable, Part.bind_some,
    Part.mem_some_iff, exists_eq_left] using hh

/-- A recovered higher boundary preserves lower composite values. -/
theorem higher_boundary_composition {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)}
    (h : SatisfiesEquations A) {l j k : I} (hlj : l < j) (hjk : j < k) (b : Bool) {s}
    (x y z : A.carrier (k, s)) (hz : z ∈ A.op (.comp (lt_trans hlj hjk) s) (pair x y)) :
    boundaryValue h hjk b z ∈ A.op (.comp hlj s)
      (pair (boundaryValue h hjk b x) (boundaryValue h hjk b y)) := by
  have hh := (uniform_valid_iff A _ _).mp (h (.boundaryComposition hlj hjk s b)) ![x, y]
  have hp : EEquation.Satisfies A (uniformValuation ![x, y])
      (defined (binary (lt_trans hlj hjk) (variableTerm (k, s) 0) (variableTerm (k, s) 1))) := by
    erw [satisfies_defined, partialEval_binary]
    simp only [eval_uniform_variable, Matrix.cons_val_zero, Matrix.cons_val_one, Part.bind_some]
    exact hz.1
  have hc := hh (by intro r; fin_cases r; exact hp)
  unfold EEquation.Satisfies at hc
  simp only [eval_boundary h, partialEval_binary, eval_uniform_variable,
    Matrix.cons_val_zero, Matrix.cons_val_one, Part.bind_some,
    Part.mem_bind_iff, Part.mem_some_iff] at hc
  obtain ⟨q, ⟨r, hr, hq⟩, hq'⟩ := hc
  have he := Part.mem_unique hr hz
  subst r
  exact hq ▸ hq'

/-- The recovered compositions satisfy interchange on every composable rectangle. -/
theorem composition_interchange {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)}
    (h : SatisfiesEquations A) {l j k : I} (hlj : l < j) (hjk : j < k) {s}
    (x y z t xy zt xz yt : A.carrier (k, s))
    (hxy : xy ∈ A.op (.comp hjk s) (pair x y))
    (hzt : zt ∈ A.op (.comp hjk s) (pair z t))
    (hxz : xz ∈ A.op (.comp (lt_trans hlj hjk) s) (pair x z))
    (hyt : yt ∈ A.op (.comp (lt_trans hlj hjk) s) (pair y t)) :
    ∃ q, q ∈ A.op (.comp (lt_trans hlj hjk) s) (pair xy zt) ∧
      q ∈ A.op (.comp hjk s) (pair xz yt) := by
  have hh := (uniform_valid_iff A _ _).mp (h (.interchange hlj hjk s)) ![x, y, z, t]
  have hp : ∀ j, EEquation.Satisfies A (uniformValuation ![x, y, z, t])
      (Fin.cases (defined (binary hjk (variableTerm (k, s) 0) (variableTerm (k, s) 1)))
        (Fin.cases (defined (binary hjk (variableTerm (k, s) 2) (variableTerm (k, s) 3)))
          (Fin.cases (defined (binary (lt_trans hlj hjk)
            (variableTerm (k, s) 0) (variableTerm (k, s) 2)))
            (Fin.cases (defined (binary (lt_trans hlj hjk)
              (variableTerm (k, s) 1) (variableTerm (k, s) 3))) Fin.elim0))) j) := by
    intro j
    fin_cases j <;> erw [satisfies_defined, partialEval_binary]
    all_goals simp only [eval_uniform_variable, Part.bind_some]
    · exact hxy.1
    · exact hzt.1
    · exact hxz.1
    · exact hyt.1
  have hc := hh (by intro r; fin_cases r; exact hp 0; exact hp 1; exact hp 2; exact hp 3)
  unfold EEquation.Satisfies at hc
  simp only [partialEval_binary, eval_uniform_variable, Part.bind_some,
    Part.mem_bind_iff] at hc
  obtain ⟨q, ⟨r, hr, r', hr', hq⟩, r₂, hr₂, r₃, hr₃, hq'⟩ := hc
  have he := Part.mem_unique hr hxy
  have he' := Part.mem_unique hr' hzt
  have he₂ := Part.mem_unique hr₂ hxz
  have he₃ := Part.mem_unique hr₃ hyt
  subst r
  subst r'
  subst r₂
  subst r₃
  exact ⟨q, hq, hq'⟩

/-- Recovered identities preserve lower composite values. -/
theorem identity_composition {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)}
    (hA : SatisfiesEquations A) {h j k : I} (hj : h < j) (jk : j < k) {s}
    (x y z : A.carrier (j, s)) (hz : z ∈ A.op (.comp hj s) (pair x y)) :
    identityValue hA jk z ∈ A.op (.comp (lt_trans hj jk) s)
      (pair (identityValue hA jk x) (identityValue hA jk y)) := by
  have hh := (uniform_valid_iff A _ _).mp (hA (.identityComposition hj jk s)) ![x, y]
  have hp : EEquation.Satisfies A (uniformValuation ![x, y])
      (defined (binary hj (variableTerm (j, s) 0) (variableTerm (j, s) 1))) := by
    erw [satisfies_defined, partialEval_binary]
    simp only [eval_uniform_variable, Matrix.cons_val_zero, Matrix.cons_val_one, Part.bind_some]
    exact hz.1
  have hc := hh (by intro r; fin_cases r; exact hp)
  unfold EEquation.Satisfies at hc
  simp only [eval_identity hA, partialEval_binary, eval_uniform_variable,
    Matrix.cons_val_zero, Matrix.cons_val_one, Part.bind_some,
    Part.mem_bind_iff, Part.mem_some_iff] at hc
  obtain ⟨q, ⟨r, hr, hq⟩, hq'⟩ := hc
  have he := Part.mem_unique hr hz
  subst r
  exact hq ▸ hq'

/-- Boolean boundaries of recovered pairs are their recovered maps. -/
@[simp] theorem recoveredDimension_boundary
    {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)}
    (hA : SatisfiesEquations A) {j k : I} (h : j < k) (s : S) (b : Bool) :
    (recoveredDimension hA h s).boundary b = boundaryValue hA h b := by
  cases b <;> rfl

/-- Every recovered increasing triple is compatible. -/
theorem recovered_compatible {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)}
    (hA : SatisfiesEquations A) {h j k : I} (hj : h < j) (jk : j < k) (s : S) :
    Compatible (recoveredDimension hA hj s) (recoveredDimension hA jk s)
      (recoveredDimension hA (lt_trans hj jk) s) where
  globular b c x := by simpa using globular_boundary hA hj jk b c x
  identity_identity := identity_identity hA hj jk
  boundary_comp b x y z hz := by
    simp only [recoveredDimension_boundary]
    exact higher_boundary_composition hA hj jk b x y z hz
  identity_comp := identity_composition hA hj jk
  interchange := composition_interchange hA hj jk

/-- Recover the higher category at an original sort. -/
def recoveredSort {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)}
    (hA : SatisfiesEquations A) (s : S) : HigherCategory I where
  carrier k := A.carrier (k, s)
  str.dim _ _ h := recoveredDimension hA h s
  str.compatible _ _ _ hj jk := recovered_compatible hA hj jk s

/-! ## Original operations -/

/-- Original operation evaluation uses the recovered total interpretation. -/
theorem eval_base {X : I × S → Type x}
    {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)} (hA : SatisfiesEquations A)
    (v : SortedSet.Map X A.carrier) (k : I) {a s} (σ : sig a s)
    (t : Word.Family (fun s => Term (Symbol I sig) X (k, s)) a) :
    Term.partialEval v (base k σ t) =
      (partFamily (fun j => Term.partialEval v (t j))).bind
        (fun z => Part.some (operationValue hA k σ z)) := by
  rw [partialEval_base]
  congr 1
  funext z
  simpa using base_op hA k σ ((dimensionFamily k a).symm z)

/-- Original operations recovered from the equations preserve boundaries. -/
theorem operation_boundary {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)}
    (hA : SatisfiesEquations A) {a s} (σ : sig a s) {j k : I} (hk : j < k) (b : Bool)
    (x : Word.Family (fun s => A.carrier (k, s)) a) :
    boundaryValue hA hk b (operationValue hA k σ x) =
      operationValue hA j σ (fun p => boundaryValue hA hk b (x p)) := by
  let x' := (dimensionFamily k a).symm x
  let v := Word.valuation (φ := id) x'
  let t := dimensionFamily k a
    (fun p => Term.var (sig := Symbol I sig) (Word.position (dimensionWord k a) p))
  have ht p : Term.partialEval (A := A) v (t p) = Part.some (x p) := by
    simpa [t, v, x'] using eval_dimension_family v k a _ x' (fun _ => rfl) p
  have hh := hA (.operationBoundary σ hk b) v (fun p => Fin.elim0 p)
  change EEquation.Satisfies A v
    (boundary hk b (base k σ t), base j σ (fun p => boundary hk b (t p))) at hh
  simpa only [EEquation.Satisfies, eval_boundary hA, eval_base hA, ht,
    partFamily_some, Part.bind_some, Part.mem_some_iff, exists_eq_left] using hh

/-- Original operations recovered from the equations preserve identities. -/
theorem operation_identity {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)}
    (hA : SatisfiesEquations A) {a s} (σ : sig a s) {j k : I} (hk : j < k)
    (x : Word.Family (fun s => A.carrier (j, s)) a) :
    identityValue hA hk (operationValue hA j σ x) =
      operationValue hA k σ (fun p => identityValue hA hk (x p)) := by
  let x' := (dimensionFamily j a).symm x
  let v := Word.valuation (φ := id) x'
  let t := dimensionFamily j a
    (fun p => Term.var (sig := Symbol I sig) (Word.position (dimensionWord j a) p))
  have ht p : Term.partialEval (A := A) v (t p) = Part.some (x p) := by
    simpa [t, v, x'] using eval_dimension_family v j a _ x' (fun _ => rfl) p
  have hh := hA (.operationIdentity σ hk) v (fun p => Fin.elim0 p)
  change EEquation.Satisfies A v
    (identityTerm hk (base j σ t), base k σ (fun p => identityTerm hk (t p))) at hh
  simpa only [EEquation.Satisfies, eval_identity hA, eval_base hA, ht,
    partFamily_some, Part.bind_some, Part.mem_some_iff, exists_eq_left] using hh

/-- A valuation of the doubled positional context. -/
def pairValuation {T : Type u} {A : T → Type w} {a : List T} (x y : Word.Family A a) :
    SortedSet.Map (PairVariables a) A :=
  fun s z => if z.2 then Word.valuation (φ := id) y s z.1
    else Word.valuation (φ := id) x s z.1

/-- Recovered original operations preserve defined composite values. -/
theorem operation_composition {A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig)}
    (hA : SatisfiesEquations A) {a s} (σ : sig a s) {j k : I} (hk : j < k)
    (x y z : Word.Family (fun s => A.carrier (k, s)) a)
    (hz : ∀ p, z p ∈ A.op (.comp hk _) (pair (x p) (y p))) :
    operationValue hA k σ z ∈ A.op (.comp hk s)
      (pair (operationValue hA k σ x) (operationValue hA k σ y)) := by
  let a' := dimensionWord k a
  let x' := (dimensionFamily k a).symm x
  let y' := (dimensionFamily k a).symm y
  let v := pairValuation x' y'
  let tx := dimensionFamily k a
    (fun p => Term.var (sig := Symbol I sig) (X := PairVariables a') (Word.position a' p, false))
  let ty := dimensionFamily k a
    (fun p => Term.var (sig := Symbol I sig) (X := PairVariables a') (Word.position a' p, true))
  have hx p : Term.partialEval (A := A) v (tx p) = Part.some (x p) := by
    simpa [tx, v, x', pairValuation] using eval_dimension_family v k a _ x' (fun _ => rfl) p
  have hy p : Term.partialEval (A := A) v (ty p) = Part.some (y p) := by
    simpa [ty, v, y', pairValuation] using eval_dimension_family v k a _ y' (fun _ => rfl) p
  have hp : ∀ p, EEquation.Satisfies A v (defined (binary hk (tx p) (ty p))) := by
    intro p
    rw [satisfies_defined, partialEval_binary, hx, hy, Part.bind_some, Part.bind_some]
    exact (hz p).1
  have hh := hA (.operationComposition σ hk) v
  have hc : EEquation.Satisfies A v
      (base k σ (fun p => binary hk (tx p) (ty p)), binary hk (base k σ tx) (base k σ ty)) := by
    apply hh
    change ∀ p, EEquation.Satisfies A v
      (((dimensionFamily k a).symm (fun p => defined (binary hk (tx p) (ty p)))) p)
    apply (dimensionFamily_all (fun _ e => EEquation.Satisfies A v e) k a _).mpr
    simpa only [Equiv.apply_symm_apply] using hp
  have hf : partFamily (fun p => Term.partialEval (A := A) v (binary hk (tx p) (ty p))) =
      Part.some z := by
    apply Part.eq_some_iff.mpr
    apply (mem_partFamily _ _).mpr
    intro p
    rw [partialEval_binary, hx, hy, Part.bind_some, Part.bind_some]
    exact hz p
  unfold EEquation.Satisfies at hc
  rw [eval_base hA, hf, Part.bind_some, partialEval_binary, eval_base hA, eval_base hA] at hc
  simpa only [hx, hy, partFamily_some, Part.bind_some, Part.mem_some_iff, exists_eq_left] using hc

/-- Recover a categorial algebra on the exact sorted carriers of a model. -/
def ofEquations (A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig))
    (hA : SatisfiesEquations A) : CategorialAlgebra I sig where
  sort := recoveredSort hA
  op σ :=
    { toFun k := operationValue hA k σ
      map_source := fun _ _ hk x => (operation_boundary hA σ hk false x).symm
      map_target := fun _ _ hk x => (operation_boundary hA σ hk true x).symm
      map_identity := fun _ _ hk x => (operation_identity hA σ hk x).symm
      map_comp := fun _ _ hk x y z hz => operation_composition hA σ hk x y z
        ((mem_partFamily _ _).mp hz) }

/-- Expansion after recovery returns the original partial algebra. -/
theorem toPartialAlgebra_ofEquations (A : PartialAlgebra.{max i u, max i v u, w} (Symbol I sig))
    (hA : SatisfiesEquations A) : (ofEquations A hA).toPartialAlgebra = A := by
  cases A with
  | mk C op =>
    apply congrArg (PartialAlgebra.mk C)
    funext a s σ z
    cases σ with
    | base k σ => exact (base_op hA k σ z).symm
    | source hk s => exact (boundary_op hA hk false z).symm
    | target hk s => exact (boundary_op hA hk true z).symm
    | identity hk s => exact (identity_op hA hk z).symm
    | comp hk s => exact congrArg (op (.comp hk s)) (pair_eta z)

/-! ## Homomorphisms -/

/-- Expand a categorial homomorphism on its unchanged dimension-sorted functions. -/
def CategorialAlgebra.Hom.toPartialHom {A B : CategorialAlgebra.{i, u, v, w} I sig}
    (f : CategorialAlgebra.Hom A B) : PartialAlgebra.Hom A.toPartialAlgebra B.toPartialAlgebra where
  toMap s := (f.sort s.2).toFun s.1
  map_op := by
    intro a s σ z y hy
    cases σ with
    | base k σ =>
      change _ ∈ Part.some _
      erw [Part.mem_some_iff] at hy ⊢
      subst y
      simpa only [dimensionFamily_natural (fun s x => (f.sort s.2).toFun s.1 x)] using
        f.map_op σ k (dimensionFamily k _ z)
    | source h s =>
      erw [Part.mem_some_iff] at hy ⊢
      exact hy ▸ (f.sort s).map_source _ _ h (z 0)
    | target h s =>
      erw [Part.mem_some_iff] at hy ⊢
      exact hy ▸ (f.sort s).map_target _ _ h (z 0)
    | identity h s =>
      erw [Part.mem_some_iff] at hy ⊢
      exact hy ▸ (f.sort s).map_identity _ _ h (z 0)
    | comp h s => exact (f.sort s).map_comp _ _ h _ _ _ hy

/-- Every homomorphism between expansions is a categorial homomorphism. -/
def CategorialAlgebra.Hom.ofPartialHom {A B : CategorialAlgebra.{i, u, v, w} I sig}
    (f : PartialAlgebra.Hom A.toPartialAlgebra B.toPartialAlgebra) : CategorialAlgebra.Hom A B where
  sort s :=
    { toFun k := f.toMap (k, s)
      map_source := fun _ _ h x => Part.mem_some_iff.mp
        (f.map_op (.source h s) (single x) (Part.mem_some _))
      map_target := fun _ _ h x => Part.mem_some_iff.mp
        (f.map_op (.target h s) (single x) (Part.mem_some _))
      map_identity := fun _ _ h x => Part.mem_some_iff.mp
        (f.map_op (.identity h s) (single x) (Part.mem_some _))
      map_comp := fun _ _ h x y _ hz => f.map_op (.comp h s) (pair x y) hz }
  map_op σ k x := by
    have hh := Part.mem_some_iff.mp
      (f.map_op (.base k σ) ((dimensionFamily k _).symm x) (Part.mem_some _))
    simpa only [dimensionFamily_natural, Equiv.apply_symm_apply] using hh

/-- Expansion identifies the homomorphisms bijectively. -/
def CategorialAlgebra.homEquiv (A B : CategorialAlgebra.{i, u, v, w} I sig) :
    CategorialAlgebra.Hom A B ≃ PartialAlgebra.Hom A.toPartialAlgebra B.toPartialAlgebra where
  toFun := CategorialAlgebra.Hom.toPartialHom
  invFun := CategorialAlgebra.Hom.ofPartialHom
  left_inv _ := rfl
  right_inv _ := rfl

end CategorialAlgebras.Heterogeneous
