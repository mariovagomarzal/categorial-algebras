import CategorialAlgebras.Dimensions.Indices

/-!
# Heterogeneous dimension derivors

A monotone change of dimensions interprets a strictly increasing image pair
by its corresponding operation. A collapsed pair uses a variable. All cell
domains are empty. Inclusions give truncation and clamping gives discretization.
-/

universe i j u v w

namespace CategorialAlgebras.Dimensions

open CategoryTheory

variable {I : Type i} {J : Type j} [LinearOrder I] [LinearOrder J]
variable {S : Type u} (sig : Signature.{u, v} S)

/-- The map of sorts associated with a change of dimensions. -/
def dimensionSortMap (f : I → J) (p : I × S) : J × S := (f p.1, p.2)

/-- A monotone dimension map interprets strict image pairs by symbols and collapsed
pairs by variables. -/
def heterogeneousDimensionDerivor (f : I →o J) :
    Derivor (Heterogeneous.Symbol I sig) (Heterogeneous.Symbol J sig) where
  sortMap := dimensionSortMap f
  image
    | .base _ σ => .app (.base (f _) σ) (fun q => .var
        ⟨⟨q.val, by simpa only [List.length_map] using q.isLt⟩, by
          simp [dimensionSortMap, Heterogeneous.dimensionWord, List.get_eq_getElem]⟩)
    | @Heterogeneous.Symbol.source _ _ _ _ j k h s =>
      if hh : f j < f k then
        Heterogeneous.boundary hh false
          (.var (Word.mappedVariable (dimensionSortMap f) _ 0))
      else .var ⟨0, Prod.ext (le_antisymm (le_of_not_gt hh) (f.monotone h.le)) rfl⟩
    | @Heterogeneous.Symbol.target _ _ _ _ j k h s =>
      if hh : f j < f k then
        Heterogeneous.boundary hh true
          (.var (Word.mappedVariable (dimensionSortMap f) _ 0))
      else .var ⟨0, Prod.ext (le_antisymm (le_of_not_gt hh) (f.monotone h.le)) rfl⟩
    | @Heterogeneous.Symbol.identity _ _ _ _ j k h s =>
      if hh : f j < f k then
        Heterogeneous.identityTerm hh
          (.var (Word.mappedVariable (dimensionSortMap f) _ 0))
      else .var ⟨0, Prod.ext (le_antisymm (f.monotone h.le) (le_of_not_gt hh)) rfl⟩
    | @Heterogeneous.Symbol.comp _ _ _ _ j k _ _ => if hh : f j < f k then
        Heterogeneous.binary hh
          (.var (Word.mappedVariable (dimensionSortMap f) _ 0))
          (.var (Word.mappedVariable (dimensionSortMap f) _ 1))
      else .var (Word.mappedVariable (dimensionSortMap f) _ 0)

/-- The sort map of a dimension derivor changes only the dimension coordinate. -/
@[simp] theorem heterogeneousDimensionDerivor_sortMap (f : I →o J) :
    (heterogeneousDimensionDerivor sig f).sortMap = dimensionSortMap f := rfl

/-- The image of a source uses its image pair, or a variable if that pair collapses. -/
@[simp] theorem heterogeneousDimensionDerivor_source (f : I →o J)
    {j k : I} (h : j < k) (s : S) :
    (heterogeneousDimensionDerivor sig f).image (.source h s) =
      if hh : f j < f k then Heterogeneous.boundary hh false (.var (Word.mappedVariable (dimensionSortMap f) [(k, s)] 0))
      else .var ⟨0, Prod.ext (le_antisymm (le_of_not_gt hh) (f.monotone h.le)) rfl⟩ := rfl

/-- The image of a target uses its image pair, or a variable if that pair collapses. -/
@[simp] theorem heterogeneousDimensionDerivor_target (f : I →o J)
    {j k : I} (h : j < k) (s : S) :
    (heterogeneousDimensionDerivor sig f).image (.target h s) =
      if hh : f j < f k then Heterogeneous.boundary hh true (.var (Word.mappedVariable (dimensionSortMap f) [(k, s)] 0))
      else .var ⟨0, Prod.ext (le_antisymm (le_of_not_gt hh) (f.monotone h.le)) rfl⟩ := rfl

/-- The image of an identity uses its image pair, or a variable if that pair collapses. -/
@[simp] theorem heterogeneousDimensionDerivor_identity (f : I →o J)
    {j k : I} (h : j < k) (s : S) :
    (heterogeneousDimensionDerivor sig f).image (.identity h s) =
      if hh : f j < f k then Heterogeneous.identityTerm hh (.var (Word.mappedVariable (dimensionSortMap f) [(j, s)] 0))
      else .var ⟨0, Prod.ext (le_antisymm (f.monotone h.le) (le_of_not_gt hh)) rfl⟩ := rfl

/-- The image of a composition uses its image pair, or a variable if that pair collapses. -/
@[simp] theorem heterogeneousDimensionDerivor_comp (f : I →o J)
    {j k : I} (h : j < k) (s : S) :
    (heterogeneousDimensionDerivor sig f).image (.comp h s) =
      if hh : f j < f k then Heterogeneous.binary hh (.var (Word.mappedVariable (dimensionSortMap f) [(k, s), (k, s)] 0)) (.var (Word.mappedVariable (dimensionSortMap f) [(k, s), (k, s)] 1))
      else .var (Word.mappedVariable (dimensionSortMap f) [(k, s), (k, s)] 0) := rfl

/-- A monotone dimension change, with empty cell domains. -/
def heterogeneousDimension (f : I →o J) :
    GeneralizedHepDerivor (Heterogeneous.hepSignature I sig)
      (Heterogeneous.hepSignature J sig) where
  toDerivor := heterogeneousDimensionDerivor sig f
  domain _ := ⊥

/-- Heterogeneous dimension changes impose no cell equations. -/
@[simp] theorem heterogeneousDimension_domain (f : I →o J) (p : I × S) :
    (heterogeneousDimension sig f).domain p = ⊥ := rfl

/-- Every element in the selected sort is a cell of a heterogeneous dimension change. -/
theorem heterogeneousDimension_isCell (f : I →o J)
    (B : PartialAlgebra.{max j u, max j v u, w} (Heterogeneous.Symbol J sig))
    (p : I × S) (x : B.carrier (dimensionSortMap f p)) :
    (heterogeneousDimension sig f).IsCell B p x :=
  (heterogeneousDimension sig f).isCell_of_empty (fun _ => rfl) B p x

/-- The heterogeneous discretization derivor clamps cell dimensions to the cutoff. -/
def heterogeneousDiscretization {m n : ℕ} (_h : m ≤ n) :
    GeneralizedHepDerivor (Heterogeneous.hepSignature (Fin (n + 1)) sig)
      (Heterogeneous.hepSignature (Fin (m + 1)) sig) :=
  heterogeneousDimension sig (clampDimension m)

/-- The heterogeneous truncation derivor includes the retained cell dimensions. -/
def heterogeneousTruncation {m n : ℕ} (h : m ≤ n) :
    GeneralizedHepDerivor (Heterogeneous.hepSignature (Fin (m + 1)) sig)
      (Heterogeneous.hepSignature (Fin (n + 1)) sig) :=
  heterogeneousDimension sig (cellInclusion h).toOrderHom

/-- Heterogeneous discretization on partial algebras is the induced transformation. -/
noncomputable def heterogeneousDiscretizationPartialFunctor {m n : ℕ} (h : m ≤ n) :
    PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol (Fin (m + 1)) sig) ⥤
      PartialAlgebra (Heterogeneous.Symbol (Fin (n + 1)) sig) :=
  (heterogeneousDiscretization sig h).transformedFunctor

/-- Heterogeneous truncation on partial algebras is the induced transformation. -/
noncomputable def heterogeneousTruncationPartialFunctor {m n : ℕ} (h : m ≤ n) :
    PartialAlgebra.{u, max v u, w} (Heterogeneous.Symbol (Fin (n + 1)) sig) ⥤
      PartialAlgebra (Heterogeneous.Symbol (Fin (m + 1)) sig) :=
  (heterogeneousTruncation sig h).transformedFunctor

end CategorialAlgebras.Dimensions
