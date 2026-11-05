import CategorialAlgebras.Presentations.GraduationModels
import CategorialAlgebras.Presentations.UnificationModels
import CategorialAlgebras.Presentations.CompositeDerivors

/-!
# Identity images in the top dimension

Identities into the top dimension identify each heterogeneous carrier with the fixed
points of the corresponding unified source. At the top both maps are identities.
-/

universe u v w

namespace CategorialAlgebras.Presentations

open CategoryTheory

variable {n : ℕ} {S : Type u} {sig : Signature.{u, v} S}

/-- Embed a cell into the top dimension, acting as identity at the top itself. -/
def topIdentity (C : Heterogeneous.NCategory.{w} n) :
    ∀ k, C.carrier k → C.carrier (Fin.last n) :=
  Fin.lastCases id (fun k => (C.str.dim k.castSucc (Fin.last n) (castSucc_lt_last k)).identity)

/-- Retract top cells to their source, acting as identity at the top itself. -/
def topSource (C : Heterogeneous.NCategory.{w} n) :
    ∀ k, C.carrier (Fin.last n) → C.carrier k :=
  Fin.lastCases id (fun k => (C.str.dim k.castSucc (Fin.last n) (castSucc_lt_last k)).source)

/-- At the top dimension the identity embedding does nothing. -/
@[simp] theorem topIdentity_last (C : Heterogeneous.NCategory.{w} n) :
    topIdentity C (Fin.last n) = id := Fin.lastCases_last

/-- Below the top the embedding is the specified heterogeneous identity. -/
@[simp] theorem topIdentity_castSucc (C : Heterogeneous.NCategory.{w} n) (k : Fin n) :
    topIdentity C k.castSucc = (C.str.dim _ _ (castSucc_lt_last k)).identity :=
  Fin.lastCases_castSucc k

/-- At the top dimension the source retraction does nothing. -/
@[simp] theorem topSource_last (C : Heterogeneous.NCategory.{w} n) :
    topSource C (Fin.last n) = id := Fin.lastCases_last

/-- Below the top the retraction is the specified heterogeneous source. -/
@[simp] theorem topSource_castSucc (C : Heterogeneous.NCategory.{w} n) (k : Fin n) :
    topSource C k.castSucc = (C.str.dim _ _ (castSucc_lt_last k)).source :=
  Fin.lastCases_castSucc k

/-- Source is a left inverse to the identity embedding. -/
@[simp] theorem topSource_topIdentity (C : Heterogeneous.NCategory.{w} n) (k) :
    Function.LeftInverse (topSource C k) (topIdentity C k) := by
  refine Fin.lastCases ?_ (fun j => ?_) k
  · intro x
    simp only [topIdentity_last, topSource_last, id_eq]
  · intro x
    simpa only [topIdentity_castSucc, topSource_castSucc] using
      (C.str.dim _ _ (castSucc_lt_last j)).source_identity x

/-- Identity embeddings into the top dimension are injective. -/
theorem topIdentity_injective (C : Heterogeneous.NCategory.{w} n) (k) :
    Function.Injective (topIdentity C k) := (topSource_topIdentity C k).injective

/-- A top identity is fixed by its unified source. -/
theorem topIdentity_isFiniteCell (A : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig)
    (k) (s) (x : (A.sort s).carrier k) :
    IsFiniteCell ((unifiedAlgebra A).sort s).str k (topIdentity (A.sort s) k x) := by
  revert x
  refine Fin.lastCases ?_ (fun j => ?_) k
  · intro x
    exact isFiniteCell_last _ _
  · intro x hj
    rw [topIdentity_castSucc]
    change _ = _
    exact congrArg ((A.sort s).str.dim _ _ (castSucc_lt_last j)).identity
      (((A.sort s).str.dim _ _ (castSucc_lt_last j)).source_identity x)

/-- Fixed points of a unified source are exactly the corresponding identity image. -/
theorem finiteCell_iff_identity_range
    (A : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig) (k) (s)
    (x : (A.sort s).carrier (Fin.last n)) :
    IsFiniteCell ((unifiedAlgebra A).sort s).str k x ↔
      x ∈ Set.range (topIdentity (A.sort s) k) := by
  refine Fin.lastCases ?_ (fun j => ?_) k
  · exact ⟨fun _ => ⟨x, by simp only [topIdentity_last, id_eq]⟩,
      fun _ => isFiniteCell_last _ _⟩
  · constructor
    · intro hx
      refine ⟨((A.sort s).str.dim _ _ (castSucc_lt_last j)).source x, ?_⟩
      rw [topIdentity_castSucc]
      exact hx j.isLt
    · rintro ⟨y, rfl⟩
      exact topIdentity_isFiniteCell A _ s y

/-- Embed a heterogeneous cell into the graduation of the unified top carrier. -/
def identityImageCell (A : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig) (k s)
    (x : (A.sort s).carrier k) : GraduatedCell (unifiedAlgebra A) k s :=
  graduatedCell _ (topIdentity (A.sort s) k x) (topIdentity_isFiniteCell A k s x)

/-- The embedding identifies each original carrier with the selected identity image. -/
theorem identityImageCell_bijective (A : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig)
    (k s) : Function.Bijective (identityImageCell A k s) := by
  constructor
  · intro x y h
    exact topIdentity_injective _ k (congrArg Subtype.val h)
  · intro x
    obtain ⟨y, hy⟩ := (finiteCell_iff_identity_range A k s x.val).mp (x.is_finite_cell _)
    exact ⟨y, Subtype.ext hy⟩

/-- Identity embeddings commute with all sorted higher functors. -/
theorem topIdentity_natural {C D : Heterogeneous.NCategory.{w} n}
    (f : Heterogeneous.Functor C D) (k) (x : C.carrier k) :
    f.toFun (Fin.last n) (topIdentity C k x) = topIdentity D k (f.toFun k x) := by
  revert x
  refine Fin.lastCases ?_ (fun j => ?_) k
  · intro x
    simp only [topIdentity_last, id_eq]
  · intro x
    simpa only [topIdentity_castSucc] using f.map_identity _ _ (castSucc_lt_last j) x

/-- Top identity embeddings preserve an original algebra operation. -/
theorem topIdentity_operation (A : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig)
    {a s} (σ : sig a s) (k) (x : Word.Family (fun s => (A.sort s).carrier k) a) :
    topIdentity (A.sort s) k ((A.op σ).toFun k x) =
      (A.op σ).toFun (Fin.last n) (fun j => topIdentity (A.sort _) k (x j)) := by
  revert x
  refine Fin.lastCases ?_ (fun k => ?_) k
  · intro x
    simp only [topIdentity_last, id_eq]
  · intro x
    simp only [topIdentity_castSucc]
    exact ((A.op σ).map_identity _ _ (castSucc_lt_last k) x).symm

/-- A lower boundary of a top identity is the original boundary. -/
theorem topIdentity_boundary (A : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig)
    {j k : Fin (n + 1)} (h : j < k) (s) (b : Bool) (x : (A.sort s).carrier k) :
    topIdentity (A.sort s) j (A.boundary h b x) =
      (unifiedAlgebra A).boundary (lowerDimension h) b (topIdentity (A.sort s) k x) := by
  revert h x
  refine Fin.lastCases ?_ (fun k => ?_) k
  · intro h x
    rw [show topIdentity (A.sort s) j =
      ((A.sort s).str.dim j (Fin.last n) (castSucc_lt_last (lowerDimension h))).identity from
      topIdentity_castSucc _ (lowerDimension h), topIdentity_last]
    cases b <;> rfl
  · intro h x
    rw [show topIdentity (A.sort s) j =
      ((A.sort s).str.dim j (Fin.last n) (castSucc_lt_last (lowerDimension h))).identity from
      topIdentity_castSucc _ (lowerDimension h), topIdentity_castSucc]
    cases b
    · exact congrArg ((A.sort s).str.dim j (Fin.last n)
        (castSucc_lt_last (lowerDimension h))).identity
        (boundary_identity ((A.sort s).str.compatible j k.castSucc (Fin.last n)
          h (castSucc_lt_last k)) false x).symm
    · exact congrArg ((A.sort s).str.dim j (Fin.last n)
        (castSucc_lt_last (lowerDimension h))).identity
        (boundary_identity ((A.sort s).str.compatible j k.castSucc (Fin.last n)
          h (castSucc_lt_last k)) true x).symm

/-- Top identity embeddings commute with identities between any two dimensions. -/
theorem topIdentity_identity (A : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig)
    {j k : Fin (n + 1)} (h : j < k) (s) (x : (A.sort s).carrier j) :
    topIdentity (A.sort s) k (((A.sort s).str.dim j k h).identity x) =
      topIdentity (A.sort s) j x := by
  revert h
  refine Fin.lastCases ?_ (fun k => ?_) k
  · intro h
    rw [topIdentity_last, show topIdentity (A.sort s) j =
      ((A.sort s).str.dim j (Fin.last n) h).identity from
      topIdentity_castSucc _ (lowerDimension h)]
    rfl
  · intro h
    rw [topIdentity_castSucc, show topIdentity (A.sort s) j =
      ((A.sort s).str.dim j (Fin.last n) (castSucc_lt_last (lowerDimension h))).identity from
      topIdentity_castSucc _ (lowerDimension h)]
    exact ((A.sort s).str.compatible j k.castSucc (Fin.last n) h
      (castSucc_lt_last k)).identity_identity x

/-- Top identities preserve every defined composition. -/
theorem topIdentity_comp (A : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig)
    {j k : Fin (n + 1)} (h : j < k) (s) (x y z : (A.sort s).carrier k)
    (hz : z ∈ ((A.sort s).str.dim j k h).comp x y) :
    topIdentity (A.sort s) k z ∈
      (((unifiedAlgebra A).sort s).str.dim (lowerDimension h)).comp
        (topIdentity (A.sort s) k x) (topIdentity (A.sort s) k y) := by
  revert h x y z
  refine Fin.lastCases ?_ (fun k => ?_) k
  · intro h x y z hz
    simp only [topIdentity_last, id_eq]
    exact hz
  · intro h x y z hz
    simp only [topIdentity_castSucc]
    exact ((A.sort s).str.compatible j k.castSucc (Fin.last n) h
      (castSucc_lt_last k)).identity_comp x y z hz

/-- Embedding each heterogeneous carrier into the graduation of the unified carrier is
an algebra homomorphism. -/
def identityImageHom (A : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig) :
    PartialAlgebra.Hom A.toPartialAlgebra
      (graduatedAlgebra (unifiedAlgebra A)).toPartialAlgebra where
  toMap p := identityImageCell A p.1 p.2
  map_op {a} {s} σ x {q} hq := by
    cases σ with
    | @base k a s σ =>
      apply Part.mem_some_iff.mpr
      apply Subtype.ext
      have hf := Heterogeneous.dimensionFamily_natural
        (fun p z => identityImageCell A p.1 p.2 z) k a x
      have hv : (fun j => ((Heterogeneous.dimensionFamily k a)
          (fun j => identityImageCell A _ _ (x j)) j).val) =
          fun j => topIdentity (A.sort _) k ((Heterogeneous.dimensionFamily k a) x j) := by
        funext j
        exact congrArg Subtype.val (congrFun hf j)
      change topIdentity (A.sort s) k q = (A.op σ).toFun (Fin.last n) _
      erw [hv]
      exact (congrArg (topIdentity (A.sort s) k) (Part.mem_some_iff.mp hq)).trans
        (topIdentity_operation A σ k _)
    | source h s =>
      apply Part.mem_some_iff.mpr
      apply Subtype.ext
      exact (congrArg (topIdentity (A.sort s) _) (Part.mem_some_iff.mp hq)).trans
        (topIdentity_boundary A h s false _)
    | target h s =>
      apply Part.mem_some_iff.mpr
      apply Subtype.ext
      exact (congrArg (topIdentity (A.sort s) _) (Part.mem_some_iff.mp hq)).trans
        (topIdentity_boundary A h s true _)
    | identity h s =>
      apply Part.mem_some_iff.mpr
      apply Subtype.ext
      exact (congrArg (topIdentity (A.sort s) _) (Part.mem_some_iff.mp hq)).trans
        (topIdentity_identity A h s _)
    | comp h s =>
      exact (mem_graduatedComp (unifiedAlgebra A) h _ _ _).mpr
        (topIdentity_comp A h s _ _ _ hq)

/-- Every heterogeneous algebra is isomorphic to the graduation of its unified carrier. -/
noncomputable def identityImageIso (A : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig) :
    A.toPartialAlgebra ≅ (graduatedAlgebra (unifiedAlgebra A)).toPartialAlgebra := by
  let f : A.toPartialAlgebra ⟶ (graduatedAlgebra (unifiedAlgebra A)).toPartialAlgebra :=
    identityImageHom A
  have : CategoryTheory.IsIso f :=
    (Heterogeneous.hepSignature (Fin (n + 1)) sig).isIso_of_bijective
      (Heterogeneous.equations_isEPAlgebra A.satisfiesEquations)
      (EPSignature.IsEPAlgebra.isWeak
        (Heterogeneous.equations_isEPAlgebra
          (graduatedAlgebra (unifiedAlgebra A)).satisfiesEquations))
      (identityImageHom A) (fun p => identityImageCell_bijective A p.1 p.2)
  exact CategoryTheory.asIso f

end CategorialAlgebras.Presentations
