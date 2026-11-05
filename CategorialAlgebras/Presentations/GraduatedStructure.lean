import CategorialAlgebras.Presentations.Graduation

/-!
# The structure carried by graduated cells

Boundaries restrict the original boundaries, identities include lower cells, and
composition has precisely the original matching-boundary domain.
-/

universe u v w

namespace CategorialAlgebras.Presentations

variable {n : ℕ} {S : Type u} {sig : Signature.{u, v} S}
variable (B : Homogeneous.NCategorialAlgebra.{u, v, w} n sig)

/-- The selected cells, with the exact subtype used by the induced transformation. -/
abbrev GraduatedCell (k : Fin (n + 1)) (s : S) :=
  (graduation n sig).Cell B.toPartialAlgebra (k, s)

/-- A selected cell satisfies the fixed-source condition in its dimension. -/
theorem GraduatedCell.is_finite_cell {k s} (x : GraduatedCell B k s) :
    IsFiniteCell (B.sort s).str k x.val :=
  (graduation_isCell_iff n sig B k s x.val).mp x.property

/-- Package a finite cell in the carrier selected by graduation. -/
def graduatedCell {k s} (x : B.carrier s) (h : IsFiniteCell (B.sort s).str k x) :
    GraduatedCell B k s := ⟨x, (graduation_isCell_iff n sig B k s x).mpr h⟩

/-- Source of a graduated cell. -/
def graduatedSource {j k : Fin (n + 1)} (h : j < k) {s}
    (x : GraduatedCell B k s) : GraduatedCell B j s :=
  graduatedCell B (((B.sort s).str.dim (lowerDimension h)).source x.val)
    (fun _ => source_isCell _ _ _)

/-- Target of a graduated cell. -/
def graduatedTarget {j k : Fin (n + 1)} (h : j < k) {s}
    (x : GraduatedCell B k s) : GraduatedCell B j s :=
  graduatedCell B (((B.sort s).str.dim (lowerDimension h)).target x.val)
    (fun _ => target_isCell _ _ _)

/-- Identity is the inclusion from lower to higher cells. -/
def graduatedIdentity {j k : Fin (n + 1)} (h : j < k) {s}
    (x : GraduatedCell B j s) : GraduatedCell B k s :=
  graduatedCell B x.val (isFiniteCell_mono _ (le_of_lt h) (x.is_finite_cell B))

/-- Defined lower composites of higher cells remain higher cells. -/
theorem graduated_comp_isCell {j k : Fin (n + 1)} (h : j < k) {s}
    (x y : GraduatedCell B k s) {z : B.carrier s}
    (hz : z ∈ ((B.sort s).str.dim (lowerDimension h)).comp x.val y.val) :
    IsFiniteCell (B.sort s).str k z := by
  intro hk
  exact comp_isCell _ (show lowerDimension h < (⟨k.val, hk⟩ : Fin n) from h)
    (x.is_finite_cell B hk) (y.is_finite_cell B hk) hz

/-- Composition restricts the original partial composition without changing its domain. -/
noncomputable def graduatedComp {j k : Fin (n + 1)} (h : j < k) {s}
    (x y : GraduatedCell B k s) : Part (GraduatedCell B k s) where
  Dom := (((B.sort s).str.dim (lowerDimension h)).comp x.val y.val).Dom
  get hd := graduatedCell B _ (graduated_comp_isCell B h x y (Part.get_mem hd))

/-- A graduated composite has exactly its original underlying value. -/
@[simp] theorem mem_graduatedComp {j k : Fin (n + 1)} (h : j < k) {s}
    (x y z : GraduatedCell B k s) :
    z ∈ graduatedComp B h x y ↔
      z.val ∈ ((B.sort s).str.dim (lowerDimension h)).comp x.val y.val := by
  constructor
  · rintro ⟨hd, hz⟩
    exact ⟨hd, congrArg Subtype.val hz⟩
  · rintro ⟨hd, hz⟩
    exact ⟨hd, Subtype.ext hz⟩

/-- The category structure associated with two dimensions of graduated cells. -/
noncomputable def graduatedDimension {j k : Fin (n + 1)} (h : j < k) (s : S) :
    Heterogeneous.CategoryStructure (GraduatedCell B j s) (GraduatedCell B k s) where
  source := graduatedSource B h
  target := graduatedTarget B h
  identity := graduatedIdentity B h
  comp := graduatedComp B h
  source_identity x := Subtype.ext (x.is_finite_cell B (lowerDimension h).isLt)
  target_identity x := Subtype.ext
    (((B.sort s).str.isCell_iff_target _ _).mp (x.is_finite_cell B (lowerDimension h).isLt))
  comp_dom x y := by
    exact (((B.sort s).str.dim (lowerDimension h)).comp_dom _ _).trans
      ⟨fun he => Subtype.ext he, fun he => congrArg Subtype.val he⟩
  source_comp x y z hz := Subtype.ext
    (((B.sort s).str.dim (lowerDimension h)).source_comp _ _ _
      ((mem_graduatedComp B h x y z).mp hz))
  target_comp x y z hz := Subtype.ext
    (((B.sort s).str.dim (lowerDimension h)).target_comp _ _ _
      ((mem_graduatedComp B h x y z).mp hz))
  comp_source x := (mem_graduatedComp B h _ _ _).mpr
    (((B.sort s).str.dim (lowerDimension h)).comp_source _)
  target_comp_self x := (mem_graduatedComp B h _ _ _).mpr
    (((B.sort s).str.dim (lowerDimension h)).target_comp_self _)
  assoc x y z xy yz hxy hyz := by
    obtain ⟨q, hq, hq'⟩ := ((B.sort s).str.dim (lowerDimension h)).assoc
      _ _ _ _ _ ((mem_graduatedComp B h _ _ _).mp hxy)
      ((mem_graduatedComp B h _ _ _).mp hyz)
    exact ⟨graduatedCell B q (graduated_comp_isCell B h xy z hq),
      (mem_graduatedComp B h _ _ _).mpr hq,
      (mem_graduatedComp B h _ _ _).mpr hq'⟩

/-- The graduated structures satisfy globularity, preservation and interchange. -/
theorem graduated_compatible {i j k : Fin (n + 1)} (ij : i < j) (jk : j < k) (s : S) :
    Heterogeneous.Compatible (graduatedDimension B ij s) (graduatedDimension B jk s)
      (graduatedDimension B (lt_trans ij jk) s) where
  globular b c x := by
    apply Subtype.ext
    have h := (B.sort s).str.compatible (lowerDimension ij) (lowerDimension jk)
      (show lowerDimension ij < lowerDimension jk from ij)
    cases b <;> cases c
    · exact h.source_source_low x.val
    · exact h.source_target x.val
    · exact h.target_source x.val
    · exact h.target_target_low x.val
  identity_identity _ := Subtype.ext rfl
  boundary_comp b x y z hz := by
    have h := (B.sort s).str.compatible (lowerDimension ij) (lowerDimension jk)
      (show lowerDimension ij < lowerDimension jk from ij)
    cases b
    · exact (mem_graduatedComp B ij _ _ _).mpr
        (h.source_comp _ _ _ ((mem_graduatedComp B (lt_trans ij jk) _ _ _).mp hz))
    · exact (mem_graduatedComp B ij _ _ _).mpr
        (h.target_comp _ _ _ ((mem_graduatedComp B (lt_trans ij jk) _ _ _).mp hz))
  identity_comp x y z hz := (mem_graduatedComp B (lt_trans ij jk) _ _ _).mpr
    ((mem_graduatedComp B ij _ _ _).mp hz)
  interchange x y z t xy zt xz yt hxy hzt hxz hyt := by
    have h := (B.sort s).str.compatible (lowerDimension ij) (lowerDimension jk)
      (show lowerDimension ij < lowerDimension jk from ij)
    obtain ⟨q, hq, hq'⟩ := h.interchange x.val z.val y.val t.val xz.val yt.val xy.val zt.val
      ((mem_graduatedComp B (lt_trans ij jk) _ _ _).mp hxz)
      ((mem_graduatedComp B (lt_trans ij jk) _ _ _).mp hyt)
      ((mem_graduatedComp B jk _ _ _).mp hxy)
      ((mem_graduatedComp B jk _ _ _).mp hzt)
    exact ⟨graduatedCell B q (graduated_comp_isCell B jk xz yt hq),
      (mem_graduatedComp B (lt_trans ij jk) _ _ _).mpr hq',
      (mem_graduatedComp B jk _ _ _).mpr hq⟩

/-- A sort of the graduated higher category. -/
noncomputable def graduatedSort (s : S) : Heterogeneous.NCategory n where
  carrier k := GraduatedCell B k s
  str.dim _ _ h := graduatedDimension B h s
  str.compatible _ _ _ ij jk := graduated_compatible B ij jk s

/-- Original operations restrict to cells of any fixed dimension. -/
def graduatedOperation {a s} (σ : sig a s) (k : Fin (n + 1))
    (x : Word.Family (fun s => GraduatedCell B k s) a) : GraduatedCell B k s :=
  graduatedCell B ((B.op σ).toFun (fun j => (x j).val))
    (fun hk => operation_isCell B σ ⟨k.val, hk⟩ _ (fun j => (x j).is_finite_cell B hk))

/-- The explicit graduated categorial algebra, on the exact transformed carriers. -/
noncomputable def graduatedAlgebra : Heterogeneous.NCategorialAlgebra.{u, v, w} n sig where
  sort := graduatedSort B
  op σ :=
    { toFun := graduatedOperation B σ
      map_source _ _ _ x := Subtype.ext ((B.op σ).map_source _ (fun j => (x j).val))
      map_target _ _ _ x := Subtype.ext ((B.op σ).map_target _ (fun j => (x j).val))
      map_identity _ _ _ _ := Subtype.ext rfl
      map_comp _ _ h _x _y _z hz := (mem_graduatedComp B h _ _ _).mpr
        ((B.op σ).map_comp _ _ _ _ ((mem_partFamily _ _).mpr
          (fun j => (mem_graduatedComp B h _ _ _).mp ((mem_partFamily _ _).mp hz j)))) }

end CategorialAlgebras.Presentations
