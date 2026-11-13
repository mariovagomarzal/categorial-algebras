import CategorialAlgebras.Limits.ProjectiveSystem

/-!
# The universal property of a projective system

An equivalence with the category of compatible families is a limit up to
isomorphism. It gives a functor induced by any coherent family of functors,
unique up to a unique compatible isomorphism, and it reconstructs morphisms
and natural transformations from their finite components.
-/

universe u v w x y z

namespace CategorialAlgebras.Limits

open CategoryTheory

variable {C : ℕ → Type u} [∀ n, Category.{v} (C n)] (T : ProjectiveSystem C)
variable (D : Type w) [Category.{x} D]

/-- A projective limit up to isomorphism, represented by compatible families. -/
structure ProjectiveLimit where
  /-- The equivalence sending an object to its compatible restrictions. -/
  equivalence : D ≌ T.Family

namespace ProjectiveLimit

variable {T D} (P : ProjectiveLimit T D)
variable {L : Type y} [Category.{z} L]

/-- The projection to finite level $n$. -/
def projection (n : ℕ) : D ⥤ C n :=
  P.equivalence.functor ⋙ ProjectiveSystem.Family.evaluation T n

/-- The functor induced by a coherent family of finite-level functors. -/
def lift (F : T.FunctorFamily L) : L ⥤ D :=
  F.toFunctor ⋙ P.equivalence.inverse

/-- The induced functor has the given family of restrictions. -/
def factor (F : T.FunctorFamily L) :
    P.lift F ⋙ P.equivalence.functor ≅ F.toFunctor :=
  Functor.isoWhiskerLeft F.toFunctor P.equivalence.counitIso

/-- The restriction of the induced functor to level $n$ is the prescribed functor. -/
def factorLevel (F : T.FunctorFamily L) (n : ℕ) :
    P.lift F ⋙ P.projection n ≅ F.functor n :=
  Functor.isoWhiskerRight (P.factor F) (ProjectiveSystem.Family.evaluation T n)

/-- Compatible homomorphisms are precisely families of finite-level homomorphisms. -/
def homEquiv (A B : D) : (A ⟶ B) ≃
    (P.equivalence.functor.obj A ⟶ P.equivalence.functor.obj B) :=
  P.equivalence.fullyFaithfulFunctor.homEquiv

/-- Compatible natural transformations are precisely transformations of compatible families. -/
def natTransEquiv (F G : L ⥤ D) : (F ⟶ G) ≃
    (F ⋙ P.equivalence.functor ⟶ G ⋙ P.equivalence.functor) :=
  (P.equivalence.fullyFaithfulFunctor.whiskeringRight L).homEquiv

/-- The reconstructed natural transformation has exactly the prescribed finite-level components. -/
theorem natTransEquiv_symm_app (F G : L ⥤ D)
    (α : F ⋙ P.equivalence.functor ⟶ G ⋙ P.equivalence.functor) (X : L) (n : ℕ) :
    ((P.equivalence.functor.map (((P.natTransEquiv F G).symm α).app X)).app n) =
      (α.app X).app n := by
  have h := (P.equivalence.fullyFaithfulFunctor.whiskeringRight L).map_preimage α
  exact congrArg (fun β => (β.app X).app n) h

/-- A compatible transformation is invertible when every finite-level component is invertible. -/
theorem isIso_of_levelwise (F G : L ⥤ D) (α : F ⟶ G)
    (h : ∀ X n, IsIso ((P.equivalence.functor.map (α.app X)).app n)) : IsIso α := by
  have hi (X : L) : IsIso (P.equivalence.functor.map (α.app X)) := by
    let f := P.equivalence.functor.map (α.app X)
    let e := ProjectiveSystem.Family.isoMk T (fun n => asIso (f.app n)) (fun k => f.comm k)
    change IsIso e.hom
    infer_instance
  have : ∀ X, IsIso (α.app X) := fun X => by
    have := hi X
    exact P.equivalence.fullyFaithfulFunctor.isIso_of_isIso_map (α.app X)
  exact NatIso.isIso_of_isIso_app α

/-- A factorization through the limit is unique up to a unique compatible isomorphism. -/
theorem unique_factor (F : T.FunctorFamily L) (G : L ⥤ D)
    (q : G ⋙ P.equivalence.functor ≅ F.toFunctor) :
    ∃! i : G ≅ P.lift F,
      Functor.isoWhiskerRight i P.equivalence.functor ≪≫ P.factor F = q := by
  let H := (Functor.whiskeringRight L D T.Family).obj P.equivalence.functor
  let ff := P.equivalence.fullyFaithfulFunctor.whiskeringRight L
  let i := ff.preimageIso (q ≪≫ (P.factor F).symm)
  have hi : H.mapIso i = q ≪≫ (P.factor F).symm := by
    apply Iso.ext
    exact ff.map_preimage _
  refine ⟨i, ?_, ?_⟩
  · change H.mapIso i ≪≫ P.factor F = q
    rw [hi]
    simp
  · intro j hj
    apply Iso.ext
    apply ff.map_injective
    change (H.mapIso j).hom = (H.mapIso i).hom
    rw [hi]
    have hh := congrArg Iso.hom hj
    have hh' := congrArg (fun f => f ≫ (P.factor F).inv) hh
    simpa only [H, Functor.isoWhiskerRight, Iso.trans_hom, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Iso.symm_hom] using hh'

end ProjectiveLimit

end CategorialAlgebras.Limits
