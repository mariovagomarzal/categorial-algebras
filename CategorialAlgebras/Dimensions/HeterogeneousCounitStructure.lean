import CategorialAlgebras.Dimensions.HeterogeneousStructure
import CategorialAlgebras.Presentations.UnifiedStructure

/-!
# Identity inclusions for saturated cell dimensions

Weak-pair identities compose and preserve lower composition. These laws give
the natural inclusion of an initially strict, saturated reindexing into its
original heterogeneous structure.
-/

universe i u v w

namespace CategorialAlgebras.Dimensions

variable {I : Type i} [LinearOrder I] {A : I → Type w}

/-- Weak-pair boundaries retract weak-pair identities. -/
theorem dimensionLE_boundary_identity (C : Heterogeneous.Structure I A) {j k : I}
    (h : j ≤ k) (b : Bool) (x : A j) :
    (dimensionLE C h).boundary b ((dimensionLE C h).identity x) = x := by
  cases b
  · exact (dimensionLE C h).source_identity x
  · exact (dimensionLE C h).target_identity x

/-- Successive weak-pair identities are the direct identity. -/
theorem dimensionLE_identity_trans (C : Heterogeneous.Structure I A) {i j k : I}
    (hij : i ≤ j) (hjk : j ≤ k) (x : A i) :
    (dimensionLE C hjk).identity ((dimensionLE C hij).identity x) =
      (dimensionLE C (le_trans hij hjk)).identity x := by
  rcases hij.lt_or_eq with hij | rfl
  · rcases hjk.lt_or_eq with hjk | rfl
    · simpa only [dimensionLE_of_lt _ _ hij, dimensionLE_of_lt _ _ hjk,
        dimensionLE_of_lt _ _ (lt_trans hij hjk)] using
        (C.compatible i j k hij hjk).identity_identity x
    · simp only [dimensionLE_self]
      rfl
  · simp only [dimensionLE_self]
    rfl

/-- A lower weak-pair boundary of an upper identity is the intermediate boundary. -/
theorem dimensionLE_boundary_upperIdentity (C : Heterogeneous.Structure I A) {i j k : I}
    (hij : i ≤ j) (hjk : j ≤ k) (b : Bool) (x : A j) :
    (dimensionLE C (le_trans hij hjk)).boundary b ((dimensionLE C hjk).identity x) =
      (dimensionLE C hij).boundary b x := by
  rcases hij.lt_or_eq with hij | rfl
  · rcases hjk.lt_or_eq with hjk | rfl
    · simpa only [dimensionLE_of_lt _ _ hij, dimensionLE_of_lt _ _ hjk,
        dimensionLE_of_lt _ _ (lt_trans hij hjk)] using
        Presentations.boundary_identity (C.compatible i j k hij hjk) b x
    · simp only [dimensionLE_self]
      rfl
  · rw [dimensionLE_self]
    cases b <;> exact dimensionLE_boundary_identity C hjk _ x

/-- A boundary of an identity from a lower dimension is the intermediate identity. -/
theorem dimensionLE_boundary_lowerIdentity (C : Heterogeneous.Structure I A) {i j k : I}
    (hij : i ≤ j) (hjk : j ≤ k) (b : Bool) (x : A i) :
    (dimensionLE C hjk).boundary b ((dimensionLE C (le_trans hij hjk)).identity x) =
      (dimensionLE C hij).identity x := by
  rw [← dimensionLE_identity_trans C hij hjk]
  exact dimensionLE_boundary_identity C hjk b _

/-- Weak-pair identities preserve composition, including a collapsed lower pair. -/
theorem dimensionLE_identity_comp (C : Heterogeneous.Structure I A) {i j k : I}
    (hij : i ≤ j) (hjk : j ≤ k) (x y z : A j)
    (hz : z ∈ (dimensionLE C hij).comp x y) :
    (dimensionLE C hjk).identity z ∈ (dimensionLE C (le_trans hij hjk)).comp
      ((dimensionLE C hjk).identity x) ((dimensionLE C hjk).identity y) := by
  rcases hij.lt_or_eq with hij | rfl
  · rcases hjk.lt_or_eq with hjk | rfl
    · simpa only [dimensionLE_of_lt _ _ hij, dimensionLE_of_lt _ _ hjk,
        dimensionLE_of_lt _ _ (lt_trans hij hjk)] using
        (C.compatible i j k hij hjk).identity_comp x y z
          (by simpa only [dimensionLE_of_lt _ _ hij] using hz)
    · simp only [dimensionLE_self]
      exact hz
  · rw [dimensionLE_self, mem_discretePair] at hz
    rcases hz with ⟨rfl, rfl⟩
    have hh := (dimensionLE C hjk).comp_source ((dimensionLE C hjk).identity x)
    rwa [(dimensionLE C hjk).source_identity] at hh

/-- Identity inclusions commute with boundaries when a lower dimension is retained or
both source dimensions collapse. -/
theorem dimensionLE_boundary_square (C : Heterogeneous.Structure I A) {a b j k : I}
    (hab : a ≤ b) (haj : a ≤ j) (hbk : b ≤ k) (hjk : j ≤ k)
    (hs : a = b ∨ a = j) (c : Bool) (x : A b) :
    (dimensionLE C haj).identity ((dimensionLE C hab).boundary c x) =
      (dimensionLE C hjk).boundary c ((dimensionLE C hbk).identity x) := by
  rcases hs with rfl | rfl
  · rw [dimensionLE_self]
    cases c <;> exact (dimensionLE_boundary_lowerIdentity C haj hjk _ x).symm
  · rw [dimensionLE_self]
    exact (dimensionLE_boundary_upperIdentity C hab hbk c x).symm

/-- Identity inclusions commute with composition on retained or collapsed lower pairs. -/
theorem dimensionLE_comp_square (C : Heterogeneous.Structure I A) {a b j k : I}
    (hab : a ≤ b) (haj : a ≤ j) (hbk : b ≤ k) (hjk : j ≤ k)
    (hs : a = b ∨ a = j) (x y z : A b) (hz : z ∈ (dimensionLE C hab).comp x y) :
    (dimensionLE C hbk).identity z ∈ (dimensionLE C hjk).comp
      ((dimensionLE C hbk).identity x) ((dimensionLE C hbk).identity y) := by
  rcases hs with rfl | rfl
  · rw [dimensionLE_self, mem_discretePair] at hz
    rcases hz with ⟨rfl, rfl⟩
    rw [← dimensionLE_identity_trans C haj hjk]
    have hh := (dimensionLE C hjk).comp_source
      ((dimensionLE C hjk).identity ((dimensionLE C haj).identity x))
    rwa [(dimensionLE C hjk).source_identity] at hh
  · exact dimensionLE_identity_comp C hab hbk x y z hz

/-- Identity inclusions from a saturating reindexing form a higher functor. -/
noncomputable def reindexedCounit (C : Heterogeneous.HigherCategory.{i, w} I)
    (f : I →o I) (hf : Saturating f) (hle : ∀ k, f k ≤ k)
    (hs : ∀ j k, j < k → f j = f k ∨ f j = j) :
    Heterogeneous.Functor (reindexedSort C f hf) C where
  toFun k := (dimensionLE C.str (hle k)).identity
  map_source j k h x := by
    have he := dimensionLE_boundary_square C.str (f.monotone h.le) (hle j) (hle k) h.le
      (hs j k h) false x
    erw [dimensionLE_of_lt _ _ h] at he
    exact he
  map_target j k h x := by
    have he := dimensionLE_boundary_square C.str (f.monotone h.le) (hle j) (hle k) h.le
      (hs j k h) true x
    erw [dimensionLE_of_lt _ _ h] at he
    exact he
  map_identity j k h x := by
    have he := (dimensionLE_identity_trans C.str (f.monotone h.le) (hle k) x).trans
      (dimensionLE_identity_trans C.str (hle j) h.le x).symm
    erw [dimensionLE_of_lt _ _ h] at he
    exact he
  map_comp j k h x y z hz := by
    simpa only [dimensionLE_of_lt _ _ h] using
      dimensionLE_comp_square C.str (f.monotone h.le) (hle j) (hle k) h.le (hs j k h) x y z hz

/-- Identity inclusions commute with all original operations, hence form a categorial
algebra homomorphism from the saturated reindexing. -/
noncomputable def reindexedCounitHom {S : Type u} {sig : Signature.{u, v} S}
    (B : Heterogeneous.CategorialAlgebra.{i, u, v, w} I sig)
    (f : I →o I) (hf : Saturating f) (hle : ∀ k, f k ≤ k)
    (hs : ∀ j k, j < k → f j = f k ∨ f j = j) :
    Heterogeneous.CategorialAlgebra.Hom (reindexedAlgebra B f hf) B where
  sort s := reindexedCounit (B.sort s) f hf hle hs
  map_op {a} {_s} σ k x :=
    (map_dimensionLE_identity (B.op σ) (hle k) x).symm.trans
      (congrArg ((B.op σ).toFun k)
        (dimensionLE_product_identity (C := fun q : Fin a.length => B.sort (a.get q)) (hle k) x))

end CategorialAlgebras.Dimensions
