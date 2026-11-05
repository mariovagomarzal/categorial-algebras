import CategorialAlgebras.Dimensions.HeterogeneousDerivors

/-!
# Saturating a family of cell dimensions

An initially strict monotone map may become constant above a cutoff. Pulling
back a heterogeneous structure along such a map repeats the last carrier,
using discrete structures on collapsed pairs.
-/

universe i j u v w

namespace CategorialAlgebras.Dimensions

/-- The heterogeneous discrete category with the same objects and arrows. -/
noncomputable def discretePair (A : Type w) : Heterogeneous.CategoryStructure A A where
  source := id
  target := id
  identity := id
  comp := (Homogeneous.CategoryStructure.discrete A).comp
  source_identity _ := rfl
  target_identity _ := rfl
  comp_dom _ _ := Iff.rfl
  source_comp _ _ _ h := h.2 ▸ h.1
  target_comp _ _ _ h := h.2.symm
  comp_source _ := ⟨rfl, rfl⟩
  target_comp_self _ := ⟨rfl, rfl⟩
  assoc := (Homogeneous.CategoryStructure.discrete A).assoc

/-- Membership in discrete composition is equality of both inputs and the result. -/
@[simp] theorem mem_discretePair {A : Type w} (x y z : A) :
    z ∈ (discretePair A).comp x y ↔ x = y ∧ x = z := by
  exact ⟨fun ⟨h, hz⟩ => ⟨h, hz⟩, fun ⟨h, hz⟩ => ⟨h, hz⟩⟩

/-- Appending a discrete upper pair preserves compatibility. -/
theorem compatible_discretePair {A B : Type w} (C : Heterogeneous.CategoryStructure A B) :
    Heterogeneous.Compatible C (discretePair B) C where
  globular b c x := by cases c <;> rfl
  identity_identity _ := rfl
  boundary_comp b _ _ _ h := by cases b <;> exact h
  identity_comp _ _ _ h := h
  interchange x y z t xy zt xz yt hxy hzt hxz hyt := by
    rcases hxy with ⟨rfl, rfl⟩
    rcases hzt with ⟨rfl, rfl⟩
    have he : xz = yt := Part.mem_unique hxz hyt
    subst yt
    exact ⟨xz, hxz, ⟨rfl, rfl⟩⟩

variable {J : Type j} [LinearOrder J] {A : J → Type w}

/-- Extend the pair structures to weakly increasing dimensions, using discrete
composition when the dimensions coincide. -/
noncomputable def dimensionLE (C : Heterogeneous.Structure J A) {j k : J} (h : j ≤ k) :
    Heterogeneous.CategoryStructure (A j) (A k) :=
  if hh : j < k then C.dim j k hh else by
    have he : j = k := le_antisymm h (le_of_not_gt hh)
    subst k
    exact discretePair (A j)

/-- Strict pairs retain their original structure. -/
@[simp] theorem dimensionLE_of_lt (C : Heterogeneous.Structure J A) {j k : J} (h : j ≤ k) (hh : j < k) :
    dimensionLE C h = C.dim j k hh := by
  simp only [dimensionLE, dite_eq_left hh]

/-- Equal pairs have the discrete structure. -/
@[simp] theorem dimensionLE_self (C : Heterogeneous.Structure J A) (j : J) :
    dimensionLE C (le_refl j) = discretePair (A j) := by
  simp only [dimensionLE, lt_self_iff_false, dite_false]

/-- A collapsed weak-pair source retains its argument up to carrier transport. -/
theorem dimensionLE_source_heq (C : Heterogeneous.Structure J A) {j k : J}
    (h : j ≤ k) (he : j = k) (x : A k) :
    HEq ((dimensionLE C h).source x) x := by
  subst k
  rw [dimensionLE_self]
  rfl

/-- A collapsed weak-pair target retains its argument up to carrier transport. -/
theorem dimensionLE_target_heq (C : Heterogeneous.Structure J A) {j k : J}
    (h : j ≤ k) (he : j = k) (x : A k) :
    HEq ((dimensionLE C h).target x) x := by
  subst k
  rw [dimensionLE_self]
  rfl

/-- A collapsed weak-pair identity retains its argument up to carrier transport. -/
theorem dimensionLE_identity_heq (C : Heterogeneous.Structure J A) {j k : J}
    (h : j ≤ k) (he : j = k) (x : A j) :
    HEq ((dimensionLE C h).identity x) x := by
  subst k
  rw [dimensionLE_self]
  rfl

/-- Composition of a collapsed weak pair is discrete on its arrow carrier. -/
theorem dimensionLE_comp_of_eq (C : Heterogeneous.Structure J A) {j k : J}
    (h : j ≤ k) (he : j = k) (x y : A k) :
    (dimensionLE C h).comp x y = (discretePair (A k)).comp x y := by
  subst k
  rw [dimensionLE_self]

/-- Weakly increasing triples remain compatible provided a collapsed first pair
forces the second pair to collapse. -/
theorem dimensionLE_compatible (C : Heterogeneous.Structure J A) {i j k : J}
    (hij : i ≤ j) (hjk : j ≤ k) (hc : i = j → j = k) :
    Heterogeneous.Compatible (dimensionLE C hij) (dimensionLE C hjk)
      (dimensionLE C (le_trans hij hjk)) := by
  rcases hij.lt_or_eq with hij | rfl
  · rcases hjk.lt_or_eq with hjk | rfl
    · simpa only [dimensionLE_of_lt _ _ hij, dimensionLE_of_lt _ _ hjk,
        dimensionLE_of_lt _ _ (lt_trans hij hjk)] using C.compatible i j k hij hjk
    · simpa only [dimensionLE_of_lt _ _ hij, dimensionLE_self] using
        compatible_discretePair (C.dim i j hij)
  · have he := hc rfl
    subst k
    simpa only [dimensionLE_self] using compatible_discretePair (discretePair (A i))

variable {I : Type i} [LinearOrder I]

/-- Once an initially strict dimension map identifies two dimensions, all subsequent
dimensions have that same image. -/
def Saturating (f : I →o J) : Prop :=
  ∀ i j k, i < j → j < k → f i = f j → f j = f k

/-- Clamping is initially strict and then constant. -/
theorem clampDimension_saturating (m n : ℕ) :
    Saturating (clampDimension m : Fin (n + 1) →o Fin (m + 1)) := by
  intro i j k hij hjk he
  apply Fin.ext
  have hv := congrArg Fin.val he
  change min i.val m = min j.val m at hv
  change min j.val m = min k.val m
  have hi : i.val < j.val := hij
  have hj : j.val < k.val := hjk
  omega

/-- A strictly increasing inclusion is saturating vacuously. -/
theorem orderEmbedding_saturating (f : I ↪o J) : Saturating f.toOrderHom := by
  intro i j _ hij _ he
  exact (ne_of_lt (f.lt_iff_lt.mpr hij) he).elim

/-- Pullback of a heterogeneous structure along a saturating dimension map. -/
noncomputable def reindexedStructure (C : Heterogeneous.Structure J A) (f : I →o J)
    (hf : Saturating f) : Heterogeneous.Structure I (fun k => A (f k)) where
  dim _j _k h := dimensionLE C (f.monotone h.le)
  compatible _i _j _k hij hjk := dimensionLE_compatible C _ _ (hf _ _ _ hij hjk)

/-- Pullback of a heterogeneous higher category along a saturating dimension map. -/
noncomputable def reindexedSort (C : Heterogeneous.HigherCategory.{j, w} J)
    (f : I →o J) (hf : Saturating f) : Heterogeneous.HigherCategory I where
  carrier k := C.carrier (f k)
  str := reindexedStructure C.str f hf

/-- A functor preserves the weak-pair sources. -/
theorem map_dimensionLE_source {C D : Heterogeneous.HigherCategory.{j, w} J}
    (F : Heterogeneous.Functor C D) {j k : J} (h : j ≤ k) (x : C.carrier k) :
    F.toFun j ((dimensionLE C.str h).source x) =
      (dimensionLE D.str h).source (F.toFun k x) := by
  rcases h.lt_or_eq with h | rfl
  · simpa only [dimensionLE_of_lt _ _ h] using F.map_source j k h x
  · simp only [dimensionLE_self, discretePair, id_eq]

/-- A functor preserves the weak-pair targets. -/
theorem map_dimensionLE_target {C D : Heterogeneous.HigherCategory.{j, w} J}
    (F : Heterogeneous.Functor C D) {j k : J} (h : j ≤ k) (x : C.carrier k) :
    F.toFun j ((dimensionLE C.str h).target x) =
      (dimensionLE D.str h).target (F.toFun k x) := by
  rcases h.lt_or_eq with h | rfl
  · simpa only [dimensionLE_of_lt _ _ h] using F.map_target j k h x
  · simp only [dimensionLE_self, discretePair, id_eq]

/-- A functor preserves the weak-pair identities. -/
theorem map_dimensionLE_identity {C D : Heterogeneous.HigherCategory.{j, w} J}
    (F : Heterogeneous.Functor C D) {j k : J} (h : j ≤ k) (x : C.carrier j) :
    F.toFun k ((dimensionLE C.str h).identity x) =
      (dimensionLE D.str h).identity (F.toFun j x) := by
  rcases h.lt_or_eq with h | rfl
  · simpa only [dimensionLE_of_lt _ _ h] using F.map_identity j k h x
  · simp only [dimensionLE_self, discretePair, id_eq]

/-- A functor preserves the weak-pair compositions. -/
theorem map_dimensionLE_comp {C D : Heterogeneous.HigherCategory.{j, w} J}
    (F : Heterogeneous.Functor C D) {j k : J} (h : j ≤ k) (x y z : C.carrier k)
    (hz : z ∈ (dimensionLE C.str h).comp x y) :
    F.toFun k z ∈ (dimensionLE D.str h).comp (F.toFun k x) (F.toFun k y) := by
  rcases h.lt_or_eq with h | rfl
  · simpa only [dimensionLE_of_lt _ _ h] using
      F.map_comp j k h x y z (by simpa only [dimensionLE_of_lt _ _ h] using hz)
  · simp only [dimensionLE_self, mem_discretePair] at hz ⊢
    exact ⟨congrArg (F.toFun j) hz.1, congrArg (F.toFun j) hz.2⟩

/-- Weak-pair sources on a product are pointwise. -/
theorem dimensionLE_product_source {T : Type u} {C : T → Heterogeneous.HigherCategory.{j, w} J}
    {j k : J} (h : j ≤ k) (x : ∀ t, (C t).carrier k) :
    (dimensionLE (Heterogeneous.HigherCategory.product C).str h).source x =
      fun t => (dimensionLE (C t).str h).source (x t) := by
  rcases h.lt_or_eq with hh | rfl
  · simp only [dimensionLE_of_lt _ _ hh]
    rfl
  · simp only [dimensionLE_self]
    rfl

/-- Weak-pair targets on a product are pointwise. -/
theorem dimensionLE_product_target {T : Type u} {C : T → Heterogeneous.HigherCategory.{j, w} J}
    {j k : J} (h : j ≤ k) (x : ∀ t, (C t).carrier k) :
    (dimensionLE (Heterogeneous.HigherCategory.product C).str h).target x =
      fun t => (dimensionLE (C t).str h).target (x t) := by
  rcases h.lt_or_eq with hh | rfl
  · simp only [dimensionLE_of_lt _ _ hh]
    rfl
  · simp only [dimensionLE_self]
    rfl

/-- Weak-pair identities on a product are pointwise. -/
theorem dimensionLE_product_identity {T : Type u} {C : T → Heterogeneous.HigherCategory.{j, w} J}
    {j k : J} (h : j ≤ k) (x : ∀ t, (C t).carrier j) :
    (dimensionLE (Heterogeneous.HigherCategory.product C).str h).identity x =
      fun t => (dimensionLE (C t).str h).identity (x t) := by
  rcases h.lt_or_eq with hh | rfl
  · simp only [dimensionLE_of_lt _ _ hh]
    rfl
  · simp only [dimensionLE_self]
    rfl

/-- Weak-pair composition on a product is componentwise, including discrete pairs. -/
theorem dimensionLE_product_comp {T : Type u} {C : T → Heterogeneous.HigherCategory.{j, w} J}
    {j k : J} (h : j ≤ k) (x y z : ∀ t, (C t).carrier k) :
    z ∈ (dimensionLE (Heterogeneous.HigherCategory.product C).str h).comp x y ↔
      ∀ t, z t ∈ (dimensionLE (C t).str h).comp (x t) (y t) := by
  rcases h.lt_or_eq with hh | rfl
  · simp only [dimensionLE_of_lt _ _ hh]
    exact mem_partFamily _ _
  · simp only [dimensionLE_self, mem_discretePair]
    exact ⟨fun h t => ⟨congrFun h.1 t, congrFun h.2 t⟩,
      fun h => ⟨funext (fun t => (h t).1), funext (fun t => (h t).2)⟩⟩

/-- Original operations on a reindexed algebra use the operation in the image dimension. -/
noncomputable def reindexedAlgebra {S : Type u} {sig : Signature.{u, v} S}
    (B : Heterogeneous.CategorialAlgebra.{j, u, v, w} J sig)
    (f : I →o J) (hf : Saturating f) : Heterogeneous.CategorialAlgebra I sig where
  sort s := reindexedSort (B.sort s) f hf
  op {a} {s} σ :=
    { toFun k := (B.op σ).toFun (f k)
      map_source j k h x := by
        change (B.op σ).toFun (f j)
          (fun q => (dimensionLE (B.sort _).str (f.monotone h.le)).source (x q)) = _
        exact (congrArg ((B.op σ).toFun (f j))
          (dimensionLE_product_source (C := fun q : Fin a.length => B.sort (a.get q))
            (f.monotone h.le) x).symm).trans (map_dimensionLE_source (B.op σ) _ x)
      map_target j k h x := by
        change (B.op σ).toFun (f j)
          (fun q => (dimensionLE (B.sort _).str (f.monotone h.le)).target (x q)) = _
        exact (congrArg ((B.op σ).toFun (f j))
          (dimensionLE_product_target (C := fun q : Fin a.length => B.sort (a.get q))
            (f.monotone h.le) x).symm).trans (map_dimensionLE_target (B.op σ) _ x)
      map_identity j k h x := by
        change (B.op σ).toFun (f k)
          (fun q => (dimensionLE (B.sort _).str (f.monotone h.le)).identity (x q)) = _
        exact (congrArg ((B.op σ).toFun (f k))
          (dimensionLE_product_identity (C := fun q : Fin a.length => B.sort (a.get q))
            (f.monotone h.le) x).symm).trans (map_dimensionLE_identity (B.op σ) _ x)
      map_comp j k h x y z hz := by
        apply map_dimensionLE_comp (B.op σ) (f.monotone h.le)
        have hz' : ∀ q : Fin a.length,
            z q ∈ (dimensionLE (B.sort (a.get q)).str (f.monotone h.le)).comp (x q) (y q) :=
          (mem_partFamily _ _).mp hz
        exact (dimensionLE_product_comp (C := fun q : Fin a.length => B.sort (a.get q))
          _ x y z).mpr hz'  }

end CategorialAlgebras.Dimensions
