import CategorialAlgebras.Preliminaries.Term

/-!
# Substitutions

A sorted assignment of terms to variables extends to a homomorphism between free algebras.
Assignments given by a family use the valuation-family equivalence of word positions.
The family API also allows positions whose sorts have been changed by a map.
-/

universe u v w x y z

namespace CategorialAlgebras

namespace Term

/-! ## General substitutions -/

variable {S : Type u} {sig : Signature.{u, v} S}
variable {X : S → Type w} {Y : S → Type x} {Z : S → Type y}

/-- Substitution as a homomorphism of free algebras. -/
def substHom (f : SortedSet.Map X (Term sig Y)) :
    Algebra.Hom (algebra sig X) (algebra sig Y) := lift f

/-- Substitute $f_s(x)$ for every occurrence of the variable $x$. -/
def subst (f : SortedSet.Map X (Term sig Y)) {s} (t : Term sig X s) : Term sig Y s :=
  eval (A := algebra sig Y) f t

/-- Substitution on a variable is the assigned term. -/
@[simp] theorem subst_var (f : SortedSet.Map X (Term sig Y)) {s} (a : X s) :
    subst f (var a) = f s a := rfl

/-- Substitution preserves operation nodes. -/
@[simp] theorem subst_app (f : SortedSet.Map X (Term sig Y)) {a s} (σ : sig a s)
    (t : Word.Family (Term sig X) a) :
    subst f (app σ t) = app σ (fun j => subst f (t j)) := rfl

/-- Substitution of the variables themselves is the identity. -/
@[simp] theorem subst_id {s} (t : Term sig X s) :
    subst (fun _ x => var x) t = t := by
  induction t with
  | var x => rfl
  | app σ t ih => exact congrArg (app σ) (funext ih)

/-- Substitutions compose by substituting in their assigned terms. -/
theorem subst_comp (f : SortedSet.Map X (Term sig Y))
    (g : SortedSet.Map Y (Term sig Z)) {s} (t : Term sig X s) :
    subst g (subst f t) = subst (fun s x => subst g (f s x)) t := by
  induction t with
  | var x => rfl
  | app σ t ih => exact congrArg (app σ) (funext ih)

/-! ## Substitutions specified by families -/

/-- Substitution specified by a family indexed by a word, possibly with changed sorts. -/
def substFamily {R : Type z} {φ : R → S} {a : List R}
    (q : Word.Family (fun r => Term sig X (φ r)) a) {s}
    (t : Term sig (Word.MappedVariables φ a) s) : Term sig X s :=
  subst (Word.valuation q) t

/-- Family substitution sends the variable at position $j$ to the $j$th term. -/
@[simp] theorem subst_family_var {R : Type z} {φ : R → S} {a : List R}
    (q : Word.Family (fun r => Term sig X (φ r)) a) (j : Fin a.length) :
    substFamily q (var (Word.mappedVariable φ a j)) = q j := rfl

/-- Substitution of the positional variables themselves fixes every term. -/
@[simp] theorem subst_family_positions {R : Type z} {φ : R → S} {a : List R}
    {s} (t : Term sig (Word.MappedVariables φ a) s) :
    substFamily (φ := φ) (fun j => var (Word.mappedVariable φ a j)) t = t := by
  unfold substFamily
  have h : Word.valuation (fun j => (var (Word.mappedVariable φ a j) :
      Term sig (Word.MappedVariables φ a) (φ (a.get j)))) =
      fun _ x => var x := by
    funext s ⟨j, h⟩
    cases h
    rfl
  rw [h, subst_id]

/-- Substituting after a family substitution substitutes in each member of the family. -/
theorem subst_subst_family {R : Type z} {φ : R → S} {a : List R}
    (q : Word.Family (fun r => Term sig X (φ r)) a) (g : SortedSet.Map X (Term sig Y))
    {s} (t : Term sig (Word.MappedVariables φ a) s) :
    subst g (substFamily q t) = substFamily (fun j => subst g (q j)) t := by
  unfold substFamily
  rw [subst_comp]
  congr 1
  funext s ⟨j, h⟩
  cases h
  rfl

/-- The composition rule $R^\sharp(Q^\sharp(P))=(R^\sharp(Q_j))_j^\sharp(P)$. -/
theorem subst_family_comp {a b : List S}
    (q : Word.Family (Term sig (Word.Variables b)) a)
    (r : Word.Family (Term sig X) b) {s} (t : Term sig (Word.Variables a) s) :
    substFamily (φ := id) r (substFamily (φ := id) q t) =
      substFamily (φ := id) (fun j => substFamily (φ := id) r (q j)) t :=
  subst_subst_family q (Word.valuation (φ := id) r) t

end Term
end CategorialAlgebras
