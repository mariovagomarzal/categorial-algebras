import CategorialAlgebras.HepDerivor.Comparison

/-!
# A strict comparison of transformed algebras

A unary operation interpreted by the constant $1$ is removed when the selected
cells consist only of $0$. Its translated term is nevertheless defined. Thus
successive transformation has no cells while composite transformation has one,
and the comparison is not an isomorphism.
-/

namespace CategorialAlgebras

open CategoryTheory

namespace StrictComparison

/-- The empty signature on one sort. -/
abbrev emptySignature : Signature Unit := fun _ _ => PEmpty

/-- A signature with one unary operation. -/
inductive Unary : List Unit → Unit → Type
  /-- The unary operation. -/
  | op : Unary [()] ()

/-- A signature with two constants. -/
inductive Constants : List Unit → Unit → Type
  /-- The constant interpreted by $0$. -/
  | zero : Constants [] ()
  /-- The constant interpreted by $1$. -/
  | one : Constants [] ()

/-- The hierarchical signature with no symbols. -/
abbrev source := HepSignature.ofSignature emptySignature

/-- The hierarchical signature with one unrestricted unary symbol. -/
abbrev middle := HepSignature.ofSignature Unary

/-- The hierarchical signature with two unrestricted constants. -/
abbrev target := HepSignature.ofSignature Constants

/-- The variable in the one-letter context. -/
abbrev singletonVariable : Term Unary (Word.Variables [()]) () :=
  Term.var (Word.position [()] 0)

/-- The existence equation asserting that the unary operation is defined. -/
def unaryEquation : EEquation Unary (Word.Variables [()]) () :=
  (Term.app Unary.op (fun _ => singletonVariable), Term.app Unary.op (fun _ => singletonVariable))

/-- The first derivor selects precisely the domain of the unary operation. -/
def first : GeneralizedHepDerivor source middle where
  sortMap _ := ()
  image σ := σ.elim
  domain _ t := match t with
    | () => {unaryEquation}

/-- The equation selecting the value of the zero constant. -/
def zeroEquation : EEquation Constants (Word.Variables [()]) () :=
  (Term.var (Word.position [()] 0), Term.app Constants.zero (fun j => Fin.elim0 j))

/-- The second derivor selects zero and interprets the unary operation by one. -/
def second : GeneralizedHepDerivor middle target where
  sortMap _ := ()
  image σ := match σ with
    | .op => Term.app Constants.one (fun j => Fin.elim0 j)
  domain _ t := match t with
    | () => {zeroEquation}

/-- The total two-element algebra interpreting the two constants differently. -/
abbrev algebra : PartialAlgebra Constants := PartialAlgebra.ofAlgebra
  { carrier _ := Bool
    op σ _ := match σ with
      | .zero => false
      | .one => true }

/-- The example algebra is an ep-algebra. -/
theorem algebra_isEPAlgebra : target.IsEPAlgebra algebra :=
  EPSignature.ofSignature_ofAlgebra _ _

/-- Evaluation of the zero constant has exactly the value zero. -/
@[simp] theorem mem_eval_zero {X : Unit → Type} (a : SortedSet.Map X algebra.carrier)
    (b : Bool) :
    b ∈ Term.partialEval (A := algebra) a (Term.app Constants.zero (fun j => Fin.elim0 j)) ↔
      b = false := by
  rw [Term.mem_partialEval_app]
  constructor
  · rintro ⟨_, _, h⟩
    exact Part.mem_some_iff.mp h
  · intro h
    exact ⟨(fun j => Fin.elim0 j), fun j => Fin.elim0 j, Part.mem_some_iff.mpr h⟩

/-- Evaluation of the one constant has exactly the value one. -/
@[simp] theorem mem_eval_one {X : Unit → Type} (a : SortedSet.Map X algebra.carrier)
    (b : Bool) :
    b ∈ Term.partialEval (A := algebra) a (Term.app Constants.one (fun j => Fin.elim0 j)) ↔
      b = true := by
  rw [Term.mem_partialEval_app]
  constructor
  · rintro ⟨_, _, h⟩
    exact Part.mem_some_iff.mp h
  · intro h
    exact ⟨(fun j => Fin.elim0 j), fun j => Fin.elim0 j, Part.mem_some_iff.mpr h⟩

/-- The second derivor selects exactly zero. -/
theorem second_isCell_iff (s : Unit) (b : Bool) : second.IsCell algebra s b ↔ b = false := by
  constructor
  · intro h
    obtain ⟨q, hq, hz⟩ := h () zeroEquation
      (by change zeroEquation ∈ {zeroEquation}; exact Set.mem_singleton _)
    have hqb : q = b := Part.mem_some_iff.mp hq
    exact hqb.symm.trans ((mem_eval_zero _ q).mp hz)
  · intro hb t e he
    cases t
    change e ∈ {zeroEquation} at he
    have he' : e = zeroEquation := Set.mem_singleton_iff.mp he
    subst e
    refine ⟨b, ?_, (mem_eval_zero _ b).mpr hb⟩
    exact Part.mem_some _

/-- The transformed unary operation is nowhere defined: its image is not a cell. -/
theorem unary_nowhere (b : Word.Family (second.Cell algebra) [()])
    (q : second.Cell algebra ()) : q ∉ (second.transformed algebra).op Unary.op b := by
  intro hq
  have h := (second.mem_transformed_op algebra Unary.op b q).mp hq |>.2
  have htrue : q.val = true := (mem_eval_one _ q.val).mp h
  have hfalse := (second_isCell_iff () q.val).mp q.property
  exact Bool.noConfusion (hfalse.symm.trans htrue)

/-- The intermediate transformation is weak but fails the ep-algebra condition. -/
theorem intermediate_not_isEPAlgebra : ¬ middle.IsEPAlgebra (second.transformed algebra) := by
  intro h
  let x : second.Cell algebra () := ⟨false, (second_isCell_iff () false).mpr rfl⟩
  have hd := (h Unary.op (fun _ => x)).mpr (fun _ _ he => he.elim)
  exact unary_nowhere (fun _ => x) _ (Part.get_mem hd)

/-- No cell survives the successive transformations. -/
theorem no_iterated_cell (s : Unit) : IsEmpty (first.Cell (second.transformed algebra) s) := by
  constructor
  intro x
  obtain ⟨q, hq, _⟩ := x.property () unaryEquation (Set.mem_singleton _)
  obtain ⟨r, _, hr⟩ := (Term.mem_partialEval_app (A := second.transformed algebra)
    (Word.singletonValuation x.val) Unary.op (fun _ => singletonVariable) q).mp hq
  exact unary_nowhere r q hr

/-- The translated unary term is the one constant. -/
@[simp] theorem translated_unary : second.translateSingleton () unaryEquation.1 =
    Term.app Constants.one (fun j => Fin.elim0 j) := by
  change Term.app Constants.one _ = Term.app Constants.one _
  congr 1
  funext j
  exact Fin.elim0 j

/-- Zero is a cell of the composite transformation. -/
theorem composite_zero : (first.comp second).IsCell algebra () false := by
  intro t e he
  rcases he with he | he
  · exact (second_isCell_iff () false).mpr rfl t e he
  · rcases he with ⟨r, h, p, hp, he⟩
    cases r
    cases t
    have hp' : p = unaryEquation := Set.mem_singleton_iff.mp hp
    subst p
    have he' : e = (Term.app Constants.one (fun j => Fin.elim0 j),
        Term.app Constants.one (fun j => Fin.elim0 j)) := by
      change e = (second.translateSingleton () unaryEquation.1,
        second.translateSingleton () unaryEquation.1) at he
      simpa only [translated_unary] using he
    rw [he']
    exact ⟨true, (mem_eval_one _ true).mpr rfl, (mem_eval_one _ true).mpr rfl⟩

/-- The composite selects exactly zero, whereas successive transformation has no cells. -/
theorem composite_isCell_iff (s : Unit) (b : Bool) :
    (first.comp second).IsCell algebra s b ↔ b = false := by
  cases s
  constructor
  · intro h
    exact (second_isCell_iff () b).mp (fun t e he => h t e (Or.inl he))
  · rintro rfl
    exact composite_zero

/-- The comparison in this finite example is not an isomorphism. -/
theorem comparison_not_isIso : ¬ IsIso (first.comparison second algebra) := by
  intro h
  obtain ⟨x, _⟩ := ((first.comparison second algebra).bijective_of_isIso ()).surjective
    ⟨false, composite_zero⟩
  exact (no_iterated_cell ()).false x

end StrictComparison

/-- Comparisons between successive and composite generalized hep-derivor
transformations need not be invertible, even over an ep-algebra on two elements. -/
theorem exists_noninvertible_comparison :
    ∃ (sig tau ups : HepSignature.{0, 0} Unit)
      (c : GeneralizedHepDerivor sig tau) (d : GeneralizedHepDerivor tau ups)
      (C : PartialAlgebra.{0, 0, 0} ups.symbol),
      ups.IsEPAlgebra C ∧ ¬ IsIso (c.comparison d C) :=
  ⟨StrictComparison.source, StrictComparison.middle, StrictComparison.target,
    StrictComparison.first, StrictComparison.second, StrictComparison.algebra,
    StrictComparison.algebra_isEPAlgebra, StrictComparison.comparison_not_isIso⟩

end CategorialAlgebras
