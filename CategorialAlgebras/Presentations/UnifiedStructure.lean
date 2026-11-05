import CategorialAlgebras.Presentations.Unification

/-!
# The structure on top-dimensional cells

A two-carrier category becomes a one-carrier category by representing each object by
its identity. Compatibility of increasing triples supplies the higher category laws.
-/

universe u v w

namespace CategorialAlgebras.Presentations

/-- Represent objects by their identities, retaining the arrow carrier and composition. -/
def collapseDimension {A B : Type w} (C : Heterogeneous.CategoryStructure A B) :
    Homogeneous.CategoryStructure B where
  source x := C.identity (C.source x)
  target x := C.identity (C.target x)
  comp := C.comp
  source_source x := by rw [C.source_identity]
  source_target x := by rw [C.source_identity]
  target_source x := by rw [C.target_identity]
  target_target x := by rw [C.target_identity]
  comp_dom x y := (C.comp_dom x y).trans
    (Function.LeftInverse.injective C.source_identity).eq_iff.symm
  source_comp x y z hz := congrArg C.identity (C.source_comp x y z hz)
  target_comp x y z hz := congrArg C.identity (C.target_comp x y z hz)
  comp_source := C.comp_source
  target_comp_self := C.target_comp_self
  assoc := C.assoc

/-- A lower boundary of an upper identity agrees with the intermediate boundary. -/
theorem boundary_identity {A B C : Type w}
    {l : Heterogeneous.CategoryStructure A B} {k : Heterogeneous.CategoryStructure B C}
    {m : Heterogeneous.CategoryStructure A C} (h : Heterogeneous.Compatible l k m)
    (b : Bool) (x : B) : m.boundary b (k.identity x) = l.boundary b x := by
  have he := h.globular b false (k.identity x)
  simpa only [Heterogeneous.CategoryStructure.boundary, Bool.false_eq_true,
    ↓reduceIte, k.source_identity] using he.symm

/-- Collapsing the two pairs ending at the top gives compatible homogeneous dimensions. -/
theorem collapse_compatible {A B C : Type w}
    {l : Heterogeneous.CategoryStructure A B} {k : Heterogeneous.CategoryStructure B C}
    {m : Heterogeneous.CategoryStructure A C} (h : Heterogeneous.Compatible l k m) :
    Homogeneous.Compatible (collapseDimension m) (collapseDimension k) where
  source_source x := by
    change k.identity (k.source (m.identity (m.source x))) = m.identity (m.source x)
    rw [← h.identity_identity, k.source_identity, h.identity_identity]
  target_target x := by
    change k.identity (k.target (m.identity (m.target x))) = m.identity (m.target x)
    rw [← h.identity_identity, k.target_identity, h.identity_identity]
  source_source_low x := by
    change m.identity (m.source (k.identity (k.source x))) = m.identity (m.source x)
    rw [show m.source (k.identity (k.source x)) = l.source (k.source x) from
      boundary_identity h false _, show l.source (k.source x) = m.source x from
      h.globular false false x]
  target_target_low x := by
    change m.identity (m.target (k.identity (k.target x))) = m.identity (m.target x)
    rw [show m.target (k.identity (k.target x)) = l.target (k.target x) from
      boundary_identity h true _, show l.target (k.target x) = m.target x from
      h.globular true true x]
  source_target x := by
    change m.identity (m.source (k.identity (k.target x))) = m.identity (m.source x)
    rw [show m.source (k.identity (k.target x)) = l.source (k.target x) from
      boundary_identity h false _, show l.source (k.target x) = m.source x from
      h.globular false true x]
  target_source x := by
    change m.identity (m.target (k.identity (k.source x))) = m.identity (m.target x)
    rw [show m.target (k.identity (k.source x)) = l.target (k.source x) from
      boundary_identity h true _, show l.target (k.source x) = m.target x from
      h.globular true false x]
  source_comp x y z hz := h.identity_comp _ _ _ (h.boundary_comp false x y z hz)
  target_comp x y z hz := h.identity_comp _ _ _ (h.boundary_comp true x y z hz)
  interchange x y z t xy zt xz yt hxy hzt hxz hyt := by
    obtain ⟨q, hq, hq'⟩ := h.interchange x z y t xz yt xy zt hxz hyt hxy hzt
    exact ⟨q, hq', hq⟩

variable {n : ℕ} {S : Type u} {sig : Signature.{u, v} S}
variable (A : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig)

/-- The homogeneous higher category on a heterogeneous sort's top cells. -/
def unifiedSort (s : S) : Homogeneous.NCategory n where
  carrier := (A.sort s).carrier (Fin.last n)
  str.dim k := collapseDimension ((A.sort s).str.dim k.castSucc (Fin.last n) (castSucc_lt_last k))
  str.compatible j k h := collapse_compatible ((A.sort s).str.compatible
    j.castSucc k.castSucc (Fin.last n) h (castSucc_lt_last k))

/-- The explicit unified categorial algebra, before inserting the empty-domain subtype. -/
def unifiedAlgebra : Homogeneous.NCategorialAlgebra.{u, v, w} n sig where
  sort := unifiedSort A
  op {a} {s} σ :=
    { toFun := (A.op σ).toFun (Fin.last n)
      map_source k x := ((A.op σ).map_identity _ _ (castSucc_lt_last k)
        (((Heterogeneous.wordProduct A.sort a).str.dim _ _ (castSucc_lt_last k)).source x)).trans
          (congrArg ((A.sort s).str.dim _ _ (castSucc_lt_last k)).identity
            ((A.op σ).map_source _ _ (castSucc_lt_last k) x))
      map_target k x := ((A.op σ).map_identity _ _ (castSucc_lt_last k)
        (((Heterogeneous.wordProduct A.sort a).str.dim _ _ (castSucc_lt_last k)).target x)).trans
          (congrArg ((A.sort s).str.dim _ _ (castSucc_lt_last k)).identity
            ((A.op σ).map_target _ _ (castSucc_lt_last k) x))
      map_comp k x y z hz := (A.op σ).map_comp _ _ (castSucc_lt_last k) x y z hz }

end CategorialAlgebras.Presentations
