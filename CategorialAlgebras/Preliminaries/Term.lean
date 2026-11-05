import CategorialAlgebras.Preliminaries.Algebra
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Terms and free algebras

Terms are inductive trees with sorted variables and operation nodes. Recursion evaluates a
term in any algebra. The resulting extension is the unique homomorphism on the generators.
For the free-forgetful adjunction the carrier universe contains the sort and symbol universes;
this ensures that the free algebra remains in the chosen category of algebras.
-/

universe u v w z

namespace CategorialAlgebras

open CategoryTheory

/-- Terms over $\Sigma$ with variables in $X$, indexed by their output sort. -/
inductive Term {S : Type u} (sig : Signature.{u, v} S) (X : S → Type w) :
    S → Type (max u v w) where
  /-- A generator of the specified sort. -/
  | var {s} : X s → Term sig X s
  /-- Application of a symbol to a family of terms of its input sorts. -/
  | app {a s} : sig a s → Word.Family (Term sig X) a → Term sig X s

namespace Term

/-! ## Evaluation and the universal property -/

variable {S : Type u} {sig : Signature.{u, v} S} {X : S → Type w}

/-- The free algebra on the sorted set $X$. -/
abbrev algebra (sig : Signature.{u, v} S) (X : S → Type w) : Algebra sig where
  carrier := Term sig X
  op := app

/-- Evaluation with a specified valuation of the generators. -/
def eval {A : Algebra.{u, v, z} sig} (f : SortedSet.Map X A.carrier) :
    ∀ {s}, Term sig X s → A.carrier s
  | _, var x => f _ x
  | _, app σ t => A.op σ (fun j => eval f (t j))

/-- Evaluation sends a variable to its assigned value. -/
@[simp] theorem eval_var {A : Algebra.{u, v, z} sig} (f : SortedSet.Map X A.carrier)
    {s} (x : X s) : eval f (var x) = f s x := rfl

/-- Evaluation interprets an operation on the evaluated family of arguments. -/
@[simp] theorem eval_app {A : Algebra.{u, v, z} sig} (f : SortedSet.Map X A.carrier)
    {a s} (σ : sig a s) (t : Word.Family (Term sig X) a) :
    eval f (app σ t) = A.op σ (fun j => eval f (t j)) := rfl

/-- The extension $f^\sharp$ of a valuation to a homomorphism. -/
def lift {A : Algebra.{u, v, z} sig} (f : SortedSet.Map X A.carrier) :
    Algebra.Hom (algebra sig X) A where
  toMap _ := eval f
  map_op _ _ := rfl

/-- Homomorphisms out of a free algebra are determined by their values on variables. -/
theorem hom_ext {A : Algebra.{u, v, z} sig} {f g : Algebra.Hom (algebra sig X) A}
    (h : ∀ s (x : X s), f.toMap s (var x) = g.toMap s (var x)) : f = g := by
  apply Algebra.Hom.ext
  funext s t
  induction t with
  | var x => exact h _ x
  | app σ t ih =>
    change f.toMap _ ((algebra sig X).op σ t) = g.toMap _ ((algebra sig X).op σ t)
    rw [f.map_op, g.map_op]
    exact congrArg _ (funext ih)

/-- The universal property: every valuation extends to exactly one homomorphism. -/
theorem exists_unique_lift {A : Algebra.{u, v, z} sig} (f : SortedSet.Map X A.carrier) :
    ∃! h : Algebra.Hom (algebra sig X) A, ∀ s x, h.toMap s (var x) = f s x := by
  refine ⟨lift f, fun _ _ => rfl, ?_⟩
  intro h hh
  exact hom_ext hh

/-- Extending the insertion of generators gives the identity. -/
@[simp] theorem lift_var :
    lift (fun s (x : X s) => (var x : Term sig X s)) = Algebra.Hom.id (algebra sig X) := by
  apply hom_ext
  intros
  rfl

/-- Extension commutes with postcomposition by a homomorphism. -/
theorem lift_comp {A : Algebra.{u, v, z} sig} {B : Algebra sig}
    (f : SortedSet.Map X A.carrier) (g : Algebra.Hom A B) :
    lift (fun s x => g.toMap s (f s x)) = Algebra.Hom.comp (lift f) g := by
  apply hom_ext
  intros
  rfl

/-- Renaming the generators of a term. -/
def map {Y : S → Type z} (f : SortedSet.Map X Y) :
    Algebra.Hom (algebra sig X) (algebra sig Y) := lift (fun s x => var (f s x))

/-! ## The free-forgetful adjunction -/

/-- The free algebra functor in a universe containing the sorts and operation symbols. -/
def free (sig : Signature.{u, v} S) :
    SortedSet.{u, max u v w} S ⥤ Algebra.{u, v, max u v w} sig where
  obj X := algebra sig X
  map f := map (fun s x => f s x)
  map_id _ := by apply hom_ext; intros; rfl
  map_comp _ _ := by apply hom_ext; intros; rfl

/-- The natural equivalence between homomorphisms from a free algebra and valuations. -/
def homEquiv (X : SortedSet.{u, max u v w} S) (A : Algebra.{u, v, max u v w} sig) :
    (algebra sig X ⟶ A) ≃ (X ⟶ A.carrier) where
  toFun h := SortedSet.homOfMap (fun s x => h.toMap s (var x))
  invFun f := lift (fun s x => f s x)
  left_inv _ := by apply hom_ext; intros; rfl
  right_inv _ := rfl

/-- The free algebra functor is left adjoint to the forgetful functor. -/
def adjunction (sig : Signature.{u, v} S) : free.{u, v, w} sig ⊣ Algebra.forget sig :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv
      homEquiv_naturality_left_symm := by
        intros
        apply hom_ext
        intros
        rfl
      homEquiv_naturality_right := by intros; rfl }

end Term
end CategorialAlgebras
