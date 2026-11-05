import CategorialAlgebras.Homogeneous.Evaluation
import Mathlib.Data.Fin.VecNotation

/-!
# Categorial algebras and models

The expanded partial algebra retains the exact carrier of a categorial algebra.
Its homomorphisms are precisely the sorted higher functors commuting with operations.
Conversely, totality and the domain equations recover the categorical operations.
-/

universe i u v w x

namespace CategorialAlgebras
namespace Homogeneous

open CategoryTheory

variable {I : Type i} [LT I] {S : Type u} {sig : Signature.{u, v} S}

/-- The total boundary map recovered from a model of the equations. -/
def boundaryValue {A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)}
    (h : SatisfiesEquations A) (k : I) (b : Bool) {s} (x : A.carrier s) : A.carrier s :=
  (A.op (.boundary k s b) (single x)).get (boundary_total h k s b x)

/-- A recovered boundary gives the original partial unary operation. -/
theorem boundary_op {A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)}
    (h : SatisfiesEquations A) (k : I) (b : Bool) {s} (x : Word.Family A.carrier [s]) :
    A.op (.boundary k s b) x = Part.some (boundaryValue h k b (x 0)) := by
  erw [← single_eta x]
  exact Part.eq_some_iff.mpr (Part.get_mem _)

/-- The total original operation recovered from a model. -/
def operationValue {A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)}
    (h : SatisfiesEquations A) {a s} (σ : sig a s) (x : Word.Family A.carrier a) :
    A.carrier s := (A.op (.base σ) x).get (base_total h σ x)

/-- Recovered original operations have their original partial values. -/
theorem base_op {A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)}
    (h : SatisfiesEquations A) {a s} (σ : sig a s) (x : Word.Family A.carrier a) :
    A.op (.base σ) x = Part.some (operationValue h σ x) :=
  Part.eq_some_iff.mpr (Part.get_mem _)

/-- Evaluation of boundaries in a model uses the recovered total boundary map. -/
theorem eval_boundary {X : S → Type x}
    {A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)} (h : SatisfiesEquations A)
    (v : SortedSet.Map X A.carrier) {s} (k : I) (b : Bool)
    (t : Term (Symbol I sig) X s) :
    Term.partialEval v (boundary k b t) =
      (Term.partialEval v t).bind (fun x => Part.some (boundaryValue h k b x)) := by
  erw [boundary, partialEval_unary]
  congr 1
  funext x
  exact boundary_op h k b (single x)

/-- The domain of a recovered composition is equality of its two total boundaries. -/
theorem composition_dom {A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)}
    (h : SatisfiesEquations A) (k : I) {s} (x y : A.carrier s) :
    (A.op (.comp k s) (pair x y)).Dom ↔ boundaryValue h k false x = boundaryValue h k true y := by
  have hf := (uniform_valid_iff A _ _).mp (h (.domainForward k s)) ![x, y]
  have hb := (uniform_valid_iff A _ _).mp (h (.domainBackward k s)) ![x, y]
  have hd : EEquation.Satisfies A (uniformValuation ![x, y])
      (defined (binary k (variableTerm s 0) (variableTerm s 1))) ↔
      (A.op (.comp k s) (pair x y)).Dom := by
    erw [satisfies_defined, partialEval_binary]
    simp only [variableTerm, Term.partialEval, uniformValuation, Part.bind_some,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  have he : EEquation.Satisfies A (uniformValuation ![x, y])
      (boundary k false (variableTerm s (m := 2) 0), boundary k true (variableTerm s 1)) ↔
      boundaryValue h k false x = boundaryValue h k true y := by
    unfold EEquation.Satisfies
    erw [eval_boundary h, eval_boundary h]
    simp only [variableTerm, Term.partialEval, uniformValuation, Part.bind_some,
      Matrix.cons_val_zero, Matrix.cons_val_one, Part.mem_some_iff, exists_eq_left]
  exact ⟨fun hd' => he.mp (hf (fun _ => hd.mpr hd')),
    fun he' => hd.mp (hb (fun _ => he.mpr he'))⟩

/-- Every partial algebra satisfying the contextual equations is an ep-algebra. -/
theorem equations_isEPAlgebra
    {A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)} (h : SatisfiesEquations A) :
    (epSignature I sig).IsEPAlgebra A := by
  intro a s σ z
  cases σ with
  | base σ => exact ⟨fun _ _ _ he => he.elim, fun _ => base_total h σ z⟩
  | source k s =>
    exact ⟨fun _ _ _ he => he.elim, fun _ => by
      have hh := boundary_total h k s false (z 0)
      erw [single_eta] at hh
      exact hh⟩
  | target k s =>
    exact ⟨fun _ _ _ he => he.elim, fun _ => by
      have hh := boundary_total h k s true (z 0)
      erw [single_eta] at hh
      exact hh⟩
  | comp k s =>
    have hd := composition_dom h k (z 0) (z 1)
    erw [pair_eta] at hd
    erw [hd]
    change _ ↔ EEquationSet.Satisfies A (Word.valuation (φ := id) z)
      (singletonEquation (compositionDomain k s))
    have hs : EEquationSet.Satisfies A (Word.valuation (φ := id) z)
        (singletonEquation (compositionDomain k s)) ↔
        EEquation.Satisfies A (Word.valuation (φ := id) z) (compositionDomain k s) := by
      constructor
      · intro hh
        exact hh s _ ⟨rfl, rfl⟩
      · rintro hh t e ⟨ht, he⟩
        cases ht
        cases he
        exact hh
    rw [hs]
    simp only [compositionDomain, EEquation.Satisfies, eval_boundary h,
      Term.partialEval, Part.bind_some,
      Part.mem_some_iff, exists_eq_left]
    rfl

/-- Models of the ep-specification are exactly the algebras satisfying its equations. -/
theorem isModel_iff_equations (A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)) :
    (specification I sig).IsModel A ↔ SatisfiesEquations A := by
  constructor
  · rintro ⟨_, h⟩ e
    exact h _ ⟨e, rfl⟩
  · intro h
    exact ⟨equations_isEPAlgebra h, fun _ ⟨e, he⟩ => he ▸ h e⟩

/-- Recovered boundaries fix one another in the same dimension. -/
theorem boundary_retract {A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)}
    (h : SatisfiesEquations A) (k : I) (b c : Bool) {s} (x : A.carrier s) :
    boundaryValue h k b (boundaryValue h k c x) = boundaryValue h k c x := by
  have hh := (uniform_valid_iff A _ _).mp (h (.retract k s b c)) (fun _ => x)
    (fun j => Fin.elim0 j)
  unfold EEquation.Satisfies at hh
  simpa only [eval_boundary h, eval_uniform_variable, Part.bind_some,
    Part.mem_some_iff, exists_eq_left] using hh

/-- Recovered boundaries give the two unit composites. -/
theorem boundary_unit {A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)}
    (h : SatisfiesEquations A) (k : I) {s} (x : A.carrier s) :
    x ∈ A.op (.comp k s) (pair x (boundaryValue h k false x)) ∧
      x ∈ A.op (.comp k s) (pair (boundaryValue h k true x) x) := by
  have hh b := (uniform_valid_iff A _ _).mp (h (.unit k s b)) (fun _ => x)
    (fun j => Fin.elim0 j)
  constructor
  · have hu := hh false
    unfold EEquation.Satisfies at hu
    simpa only [Bool.false_eq_true, ↓reduceIte, partialEval_binary,
      eval_boundary h, eval_uniform_variable, Part.bind_some,
      Part.mem_some_iff, exists_eq_right] using hu
  · have hu := hh true
    unfold EEquation.Satisfies at hu
    simpa only [↓reduceIte, partialEval_binary, eval_boundary h,
      eval_uniform_variable, Part.bind_some, Part.mem_some_iff, exists_eq_right] using hu

/-- Recovered boundaries of a composite are its outer boundaries. -/
theorem boundary_composite {A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)}
    (h : SatisfiesEquations A) (k : I) (b : Bool) {s} (x y z : A.carrier s)
    (hz : z ∈ A.op (.comp k s) (pair x y)) :
    boundaryValue h k b z = boundaryValue h k b (if b then x else y) := by
  have hh := (uniform_valid_iff A _ _).mp (h (.compositeBoundary k s b)) ![x, y]
  have hp : EEquation.Satisfies A (uniformValuation ![x, y])
      (defined (binary k (variableTerm s 0) (variableTerm s 1))) := by
    erw [satisfies_defined, partialEval_binary]
    simpa only [eval_uniform_variable, Matrix.cons_val_zero, Matrix.cons_val_one,
      Part.bind_some] using hz.1
  have hc := hh (fun _ => hp)
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
theorem composition_assoc {A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)}
    (h : SatisfiesEquations A) (k : I) {s} (x y z xy yz : A.carrier s)
    (hxy : xy ∈ A.op (.comp k s) (pair x y))
    (hyz : yz ∈ A.op (.comp k s) (pair y z)) :
    ∃ q, q ∈ A.op (.comp k s) (pair xy z) ∧ q ∈ A.op (.comp k s) (pair x yz) := by
  have hh := (uniform_valid_iff A _ _).mp (h (.assoc k s)) ![x, y, z]
  have hp : ∀ j, EEquation.Satisfies A (uniformValuation ![x, y, z])
      (Fin.cases (defined (binary k (variableTerm s 0) (variableTerm s 1)))
        (Fin.cases (defined (binary k (variableTerm s 1) (variableTerm s 2))) Fin.elim0) j) := by
    intro j
    fin_cases j
    · erw [satisfies_defined, partialEval_binary]
      simpa only [eval_uniform_variable, Matrix.cons_val_zero, Matrix.cons_val_one,
        Part.bind_some] using hxy.1
    · erw [satisfies_defined, partialEval_binary]
      change ((Part.some y).bind (fun y => (Part.some z).bind
        (fun z => A.op (.comp k s) (pair y z)))).Dom
      simpa only [Part.bind_some] using hyz.1
  have hc := hh hp
  unfold EEquation.Satisfies at hc
  simp only [partialEval_binary, eval_uniform_variable, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Part.bind_some, Part.mem_bind_iff] at hc
  obtain ⟨q, ⟨r, hr, hq⟩, r', hr', hq'⟩ := hc
  have he := Part.mem_unique hr hxy
  have he' := Part.mem_unique hr' hyz
  subst r
  subst r'
  exact ⟨q, hq, hq'⟩

/-- The category structure in each dimension recovered from contextual equations. -/
def recoveredDimension {A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)}
    (h : SatisfiesEquations A) (k : I) (s : S) : CategoryStructure (A.carrier s) where
  source := boundaryValue h k false
  target := boundaryValue h k true
  comp x y := A.op (.comp k s) (pair x y)
  source_source := boundary_retract h k false false
  source_target := boundary_retract h k false true
  target_source := boundary_retract h k true false
  target_target := boundary_retract h k true true
  comp_dom := composition_dom h k
  source_comp := by simpa only [Bool.false_eq_true, ↓reduceIte] using boundary_composite h k false
  target_comp := by simpa only [↓reduceIte] using boundary_composite h k true
  comp_source x := (boundary_unit h k x).1
  target_comp_self x := (boundary_unit h k x).2
  assoc := composition_assoc h k

/-- A higher boundary fixes the corresponding lower boundary. -/
theorem higher_lower_boundary {A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)}
    (h : SatisfiesEquations A) {l k : I} (hlk : l < k) (b : Bool) {s} (x : A.carrier s) :
    boundaryValue h k b (boundaryValue h l b x) = boundaryValue h l b x := by
  have hh := (uniform_valid_iff A _ _).mp (h (.higherLower l k hlk s b)) (fun _ => x)
    (fun j => Fin.elim0 j)
  unfold EEquation.Satisfies at hh
  simpa only [eval_boundary h, eval_uniform_variable, Part.bind_some,
    Part.mem_some_iff, exists_eq_left] using hh

/-- A lower boundary absorbs either higher boundary. -/
theorem lower_higher_boundary {A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)}
    (h : SatisfiesEquations A) {l k : I} (hlk : l < k) (b c : Bool) {s} (x : A.carrier s) :
    boundaryValue h l b (boundaryValue h k c x) = boundaryValue h l b x := by
  have hh := (uniform_valid_iff A _ _).mp (h (.lowerHigher l k hlk s b c)) (fun _ => x)
    (fun j => Fin.elim0 j)
  unfold EEquation.Satisfies at hh
  simpa only [eval_boundary h, eval_uniform_variable, Part.bind_some,
    Part.mem_some_iff, exists_eq_left] using hh

/-- A recovered higher boundary preserves lower composite values. -/
theorem higher_boundary_composition {A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)}
    (h : SatisfiesEquations A) {l k : I} (hlk : l < k) (b : Bool) {s}
    (x y z : A.carrier s) (hz : z ∈ A.op (.comp l s) (pair x y)) :
    boundaryValue h k b z ∈ A.op (.comp l s)
      (pair (boundaryValue h k b x) (boundaryValue h k b y)) := by
  have hh := (uniform_valid_iff A _ _).mp (h (.boundaryComposition l k hlk s b)) ![x, y]
  have hp : EEquation.Satisfies A (uniformValuation ![x, y])
      (defined (binary l (variableTerm s 0) (variableTerm s 1))) := by
    erw [satisfies_defined, partialEval_binary]
    simp only [eval_uniform_variable, Matrix.cons_val_zero, Matrix.cons_val_one, Part.bind_some]
    exact hz.1
  have hc := hh (fun _ => hp)
  unfold EEquation.Satisfies at hc
  simp only [eval_boundary h, partialEval_binary, eval_uniform_variable,
    Matrix.cons_val_zero, Matrix.cons_val_one, Part.bind_some,
    Part.mem_bind_iff, Part.mem_some_iff] at hc
  obtain ⟨q, ⟨r, hr, hq⟩, hq'⟩ := hc
  have he := Part.mem_unique hr hz
  subst r
  exact hq ▸ hq'

/-- The recovered compositions satisfy interchange on every composable rectangle. -/
theorem composition_interchange {A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)}
    (h : SatisfiesEquations A) {l k : I} (hlk : l < k) {s}
    (x y z t xy zt xz yt : A.carrier s)
    (hxy : xy ∈ A.op (.comp l s) (pair x y))
    (hzt : zt ∈ A.op (.comp l s) (pair z t))
    (hxz : xz ∈ A.op (.comp k s) (pair x z))
    (hyt : yt ∈ A.op (.comp k s) (pair y t)) :
    ∃ q, q ∈ A.op (.comp k s) (pair xy zt) ∧ q ∈ A.op (.comp l s) (pair xz yt) := by
  have hh := (uniform_valid_iff A _ _).mp (h (.interchange l k hlk s)) ![x, y, z, t]
  have hp : ∀ j, EEquation.Satisfies A (uniformValuation ![x, y, z, t])
      (Fin.cases (defined (binary l (variableTerm s 0) (variableTerm s 1)))
        (Fin.cases (defined (binary l (variableTerm s 2) (variableTerm s 3)))
          (Fin.cases (defined (binary k (variableTerm s 0) (variableTerm s 2)))
            (Fin.cases (defined (binary k (variableTerm s 1) (variableTerm s 3))) Fin.elim0))) j) := by
    intro j
    fin_cases j <;> erw [satisfies_defined, partialEval_binary]
    all_goals simp only [eval_uniform_variable, Part.bind_some]
    · exact hxy.1
    · exact hzt.1
    · exact hxz.1
    · exact hyt.1
  have hc := hh hp
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

/-- Every increasing pair of recovered dimensions is compatible. -/
theorem recovered_compatible {A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)}
    (h : SatisfiesEquations A) {l k : I} (hlk : l < k) (s : S) :
    Compatible (recoveredDimension h l s) (recoveredDimension h k s) where
  source_source := higher_lower_boundary h hlk false
  target_target := higher_lower_boundary h hlk true
  source_source_low := lower_higher_boundary h hlk false false
  target_target_low := lower_higher_boundary h hlk true true
  source_target := lower_higher_boundary h hlk false true
  target_source := lower_higher_boundary h hlk true false
  source_comp := higher_boundary_composition h hlk false
  target_comp := higher_boundary_composition h hlk true
  interchange := composition_interchange h hlk

/-- The sorted higher categories recovered from a model of the equations. -/
def recoveredSort {A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)}
    (h : SatisfiesEquations A) (s : S) : HigherCategory I where
  carrier := A.carrier s
  str.dim k := recoveredDimension h k s
  str.compatible _ _ hlk := recovered_compatible h hlk s

/-- Evaluation of an original operation uses its recovered total interpretation. -/
theorem eval_base {X : S → Type x}
    {A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)} (h : SatisfiesEquations A)
    (v : SortedSet.Map X A.carrier) {a s} (σ : sig a s)
    (t : Word.Family (Term (Symbol I sig) X) a) :
    Term.partialEval v (.app (.base σ) t) =
      (partFamily (fun j => Term.partialEval v (t j))).bind
        (fun z => Part.some (operationValue h σ z)) := by
  rw [Term.partialEval_app]
  congr 1
  funext z
  exact base_op h σ z

/-- The recovered original operations preserve boundaries. -/
theorem operation_boundary {A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)}
    (h : SatisfiesEquations A) {a s} (σ : sig a s) (k : I) (b : Bool)
    (x : Word.Family A.carrier a) :
    boundaryValue h k b (operationValue h σ x) =
      operationValue h σ (fun j => boundaryValue h k b (x j)) := by
  have hh := h (.operationBoundary σ k b) (Word.valuation (φ := id) x)
    (fun j => Fin.elim0 j)
  change EEquation.Satisfies A _ (boundary k b (.app (.base σ) _), .app (.base σ) _) at hh
  unfold EEquation.Satisfies at hh
  erw [eval_boundary h, partialEval_variables, base_op h] at hh
  simp only [Part.bind_some] at hh
  erw [eval_base h] at hh
  have ht j : Term.partialEval (Word.valuation (φ := id) x)
      (boundary k b (.var (Word.position a j))) = Part.some (boundaryValue h k b (x j)) := by
    erw [eval_boundary h]
    exact Part.bind_some _ _
  have hf : partFamily (fun j => Term.partialEval (Word.valuation (φ := id) x)
      (boundary k b (.var (Word.position a j)))) =
      Part.some (fun j => boundaryValue h k b (x j)) := by
    simp_rw [ht]
    exact partFamily_some _
  erw [hf, Part.bind_some] at hh
  dsimp only [Word.valuation, Word.position, Word.mappedVariable] at hh
  simpa only [Part.mem_some_iff, exists_eq_left] using hh

/-- A valuation of the doubled context from a pair of input families. -/
def pairValuation {A : S → Type w} {a : List S} (x y : Word.Family A a) :
    SortedSet.Map (PairVariables a) A :=
  fun s z => if z.2 then Word.valuation (φ := id) y s z.1
    else Word.valuation (φ := id) x s z.1

/-- The recovered original operations preserve all defined composites. -/
theorem operation_composition {A : PartialAlgebra.{u, max i v u, w} (Symbol I sig)}
    (h : SatisfiesEquations A) {a s} (σ : sig a s) (k : I)
    (x y z : Word.Family A.carrier a)
    (hz : ∀ j, z j ∈ A.op (.comp k _) (pair (x j) (y j))) :
    operationValue h σ z ∈ A.op (.comp k s)
      (pair (operationValue h σ x) (operationValue h σ y)) := by
  have hh := h (.operationComposition σ k) (pairValuation x y)
  have hp : ∀ j, EEquation.Satisfies A (pairValuation x y)
      (defined (binary k (.var (Word.position a j, false)) (.var (Word.position a j, true)))) := by
    intro j
    erw [satisfies_defined, partialEval_binary]
    simp only [Term.partialEval, pairValuation, Bool.false_eq_true, ↓reduceIte,
      Part.bind_some]
    exact (hz j).1
  have hc := hh hp
  change EEquation.Satisfies A _ (.app (.base σ) _, binary k (.app (.base σ) _) _) at hc
  unfold EEquation.Satisfies at hc
  have hf : (partFamily (fun j => Term.partialEval (pairValuation x y)
      (binary k (.var (Word.position a j, false)) (.var (Word.position a j, true))))) =
      Part.some z := by
    apply Part.eq_some_iff.mpr
    apply (mem_partFamily _ _).mpr
    intro j
    erw [partialEval_binary]
    simp only [Term.partialEval, pairValuation, Bool.false_eq_true, ↓reduceIte,
      Part.bind_some]
    exact hz j
  erw [eval_base h, hf, Part.bind_some, partialEval_binary, eval_base h, eval_base h] at hc
  simp only [Term.partialEval, pairValuation, Bool.false_eq_true, ↓reduceIte,
    partFamily_some, Part.bind_some, Part.mem_some_iff] at hc
  obtain ⟨q, rfl, hq⟩ := hc
  exact hq

/-- Recover a categorial algebra on the unchanged carrier of any model of the equations. -/
def ofEquations (A : PartialAlgebra.{u, max i v u, w} (Symbol I sig))
    (h : SatisfiesEquations A) : CategorialAlgebra I sig where
  sort := recoveredSort h
  op σ :=
    { toFun := operationValue h σ
      map_source := fun k x => (operation_boundary h σ k false x).symm
      map_target := fun k x => (operation_boundary h σ k true x).symm
      map_comp := fun k x y z hz => operation_composition h σ k x y z
        ((mem_partFamily _ _).mp hz) }

/-- Expansion after recovery returns the original partial algebra exactly. -/
theorem toPartialAlgebra_ofEquations (A : PartialAlgebra.{u, max i v u, w} (Symbol I sig))
    (h : SatisfiesEquations A) : (ofEquations A h).toPartialAlgebra = A := by
  cases A with
  | mk C op =>
    apply congrArg (PartialAlgebra.mk C)
    funext a s σ z
    cases σ with
    | base σ => exact (base_op h σ z).symm
    | source k s => exact (boundary_op h k false z).symm
    | target k s => exact (boundary_op h k true z).symm
    | comp k s => exact congrArg (op (.comp k s)) (pair_eta z)

/-- An expanded homomorphism associated to a categorial homomorphism. -/
def CategorialAlgebra.Hom.toPartialHom {A B : CategorialAlgebra.{i, u, v, w} I sig}
    (f : CategorialAlgebra.Hom A B) : PartialAlgebra.Hom A.toPartialAlgebra B.toPartialAlgebra where
  toMap s := (f.sort s).toFun
  map_op := by
    intro a s σ z y hy
    cases σ with
    | base σ =>
      change _ ∈ Part.some _
      erw [Part.mem_some_iff] at hy ⊢
      exact hy ▸ f.map_op σ z
    | source k s =>
      erw [Part.mem_some_iff] at hy ⊢
      exact hy ▸ (f.sort s).map_source k (z 0)
    | target k s =>
      erw [Part.mem_some_iff] at hy ⊢
      exact hy ▸ (f.sort s).map_target k (z 0)
    | comp k s => exact (f.sort s).map_comp k _ _ _ hy

/-- Every expanded partial homomorphism is a categorial homomorphism. -/
def CategorialAlgebra.Hom.ofPartialHom {A B : CategorialAlgebra.{i, u, v, w} I sig}
    (f : PartialAlgebra.Hom A.toPartialAlgebra B.toPartialAlgebra) : CategorialAlgebra.Hom A B where
  sort s :=
    { toFun := f.toMap s
      map_source := fun k x => Part.mem_some_iff.mp
        (f.map_op (.source k s) (single x) (Part.mem_some _))
      map_target := fun k x => Part.mem_some_iff.mp
        (f.map_op (.target k s) (single x) (Part.mem_some _))
      map_comp := fun k x y _ hz => f.map_op (.comp k s) (pair x y) hz }
  map_op σ x := Part.mem_some_iff.mp (f.map_op (.base σ) x (Part.mem_some _))

/-- Expansion and recovery of homomorphisms are mutually inverse. -/
def CategorialAlgebra.homEquiv (A B : CategorialAlgebra.{i, u, v, w} I sig) :
    CategorialAlgebra.Hom A B ≃ PartialAlgebra.Hom A.toPartialAlgebra B.toPartialAlgebra where
  toFun := CategorialAlgebra.Hom.toPartialHom
  invFun := CategorialAlgebra.Hom.ofPartialHom
  left_inv _ := rfl
  right_inv _ := rfl

end Homogeneous
end CategorialAlgebras
