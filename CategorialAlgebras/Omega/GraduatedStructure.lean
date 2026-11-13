import CategorialAlgebras.Presentations.GraduatedStructure
import CategorialAlgebras.Homogeneous.Omega

/-!
# The structure carried by graduated cells

Boundaries restrict the original boundaries, identities include lower cells, and
composition has precisely the original matching-boundary domain.
-/

universe u v w

namespace CategorialAlgebras.Omega

variable {S : Type u} {sig : Signature.{u, v} S}
variable (B : Homogeneous.CategorialAlgebra.{0, u, v, w} ℕ sig)

/-- The $k$-cells selected by graduation, as fixed-source subtypes. -/
abbrev GraduatedCell (k : ℕ) (s : S) :=
  {x : B.carrier s // (B.sort s).str.IsCell k x}

/-- Package a fixed-source cell as a graduated cell. -/
def graduatedCell {k s} (x : B.carrier s) (h : (B.sort s).str.IsCell k x) :
    GraduatedCell B k s := ⟨x, h⟩

/-- Source of a graduated cell. -/
def graduatedSource {j k : ℕ} (_h : j < k) {s}
    (x : GraduatedCell B k s) : GraduatedCell B j s :=
  graduatedCell B (((B.sort s).str.dim j).source x.val)
    (((B.sort s).str.dim j).source_source _)

/-- Target of a graduated cell. -/
def graduatedTarget {j k : ℕ} (_h : j < k) {s}
    (x : GraduatedCell B k s) : GraduatedCell B j s :=
  graduatedCell B (((B.sort s).str.dim j).target x.val)
    (((B.sort s).str.dim j).source_target _)

/-- Identity is the inclusion from lower to higher cells. -/
def graduatedIdentity {j k : ℕ} (h : j < k) {s}
    (x : GraduatedCell B j s) : GraduatedCell B k s :=
  graduatedCell B x.val ((B.sort s).str.isCell_mono h.le x.property)

/-- Defined lower composites of higher cells remain higher cells. -/
theorem graduated_comp_isCell {j k : ℕ} (h : j < k) {s}
    (x y : GraduatedCell B k s) {z : B.carrier s}
    (hz : z ∈ ((B.sort s).str.dim j).comp x.val y.val) :
    (B.sort s).str.IsCell k z := by
  have hv := ((B.sort s).str.compatible j k h).source_comp x.val y.val z hz
  rw [x.property, y.property] at hv
  exact Part.mem_unique hv hz

/-- Composition restricts the original partial composition without changing its domain. -/
noncomputable def graduatedComp {j k : ℕ} (h : j < k) {s}
    (x y : GraduatedCell B k s) : Part (GraduatedCell B k s) where
  Dom := (((B.sort s).str.dim j).comp x.val y.val).Dom
  get hd := graduatedCell B _ (graduated_comp_isCell B h x y (Part.get_mem hd))

/-- A graduated composite has exactly its original underlying value. -/
@[simp] theorem mem_graduatedComp {j k : ℕ} (h : j < k) {s}
    (x y z : GraduatedCell B k s) :
    z ∈ graduatedComp B h x y ↔
      z.val ∈ ((B.sort s).str.dim j).comp x.val y.val := by
  constructor
  · rintro ⟨hd, hz⟩
    exact ⟨hd, congrArg Subtype.val hz⟩
  · rintro ⟨hd, hz⟩
    exact ⟨hd, Subtype.ext hz⟩

/-- The category structure associated with two dimensions of graduated cells. -/
noncomputable def graduatedDimension {j k : ℕ} (h : j < k) (s : S) :
    Heterogeneous.CategoryStructure (GraduatedCell B j s) (GraduatedCell B k s) where
  source := graduatedSource B h
  target := graduatedTarget B h
  identity := graduatedIdentity B h
  comp := graduatedComp B h
  source_identity x := Subtype.ext x.property
  target_identity x := Subtype.ext
    (((B.sort s).str.isCell_iff_target _ _).mp x.property)
  comp_dom x y := by
    exact (((B.sort s).str.dim j).comp_dom _ _).trans
      ⟨fun he => Subtype.ext he, fun he => congrArg Subtype.val he⟩
  source_comp x y z hz := Subtype.ext
    (((B.sort s).str.dim j).source_comp _ _ _
      ((mem_graduatedComp B h x y z).mp hz))
  target_comp x y z hz := Subtype.ext
    (((B.sort s).str.dim j).target_comp _ _ _
      ((mem_graduatedComp B h x y z).mp hz))
  comp_source x := (mem_graduatedComp B h _ _ _).mpr
    (((B.sort s).str.dim j).comp_source _)
  target_comp_self x := (mem_graduatedComp B h _ _ _).mpr
    (((B.sort s).str.dim j).target_comp_self _)
  assoc x y z xy yz hxy hyz := by
    obtain ⟨q, hq, hq'⟩ := ((B.sort s).str.dim j).assoc
      _ _ _ _ _ ((mem_graduatedComp B h _ _ _).mp hxy)
      ((mem_graduatedComp B h _ _ _).mp hyz)
    exact ⟨graduatedCell B q (graduated_comp_isCell B h xy z hq),
      (mem_graduatedComp B h _ _ _).mpr hq,
      (mem_graduatedComp B h _ _ _).mpr hq'⟩

/-- The graduated structures satisfy globularity, preservation and interchange. -/
theorem graduated_compatible {i j k : ℕ} (ij : i < j) (jk : j < k) (s : S) :
    Heterogeneous.Compatible (graduatedDimension B ij s) (graduatedDimension B jk s)
      (graduatedDimension B (lt_trans ij jk) s) where
  globular b c x := by
    apply Subtype.ext
    have h := (B.sort s).str.compatible i j
      ij
    cases b <;> cases c
    · exact h.source_source_low x.val
    · exact h.source_target x.val
    · exact h.target_source x.val
    · exact h.target_target_low x.val
  identity_identity _ := Subtype.ext rfl
  boundary_comp b x y z hz := by
    have h := (B.sort s).str.compatible i j
      ij
    cases b
    · exact (mem_graduatedComp B ij _ _ _).mpr
        (h.source_comp _ _ _ ((mem_graduatedComp B (lt_trans ij jk) _ _ _).mp hz))
    · exact (mem_graduatedComp B ij _ _ _).mpr
        (h.target_comp _ _ _ ((mem_graduatedComp B (lt_trans ij jk) _ _ _).mp hz))
  identity_comp x y z hz := (mem_graduatedComp B (lt_trans ij jk) _ _ _).mpr
    ((mem_graduatedComp B ij _ _ _).mp hz)
  interchange x y z t xy zt xz yt hxy hzt hxz hyt := by
    have h := (B.sort s).str.compatible i j
      ij
    obtain ⟨q, hq, hq'⟩ := h.interchange x.val z.val y.val t.val xz.val yt.val xy.val zt.val
      ((mem_graduatedComp B (lt_trans ij jk) _ _ _).mp hxz)
      ((mem_graduatedComp B (lt_trans ij jk) _ _ _).mp hyt)
      ((mem_graduatedComp B jk _ _ _).mp hxy)
      ((mem_graduatedComp B jk _ _ _).mp hzt)
    exact ⟨graduatedCell B q (graduated_comp_isCell B jk xz yt hq),
      (mem_graduatedComp B (lt_trans ij jk) _ _ _).mpr hq',
      (mem_graduatedComp B jk _ _ _).mpr hq⟩

/-- A sort of the graduated higher category. -/
noncomputable def graduatedSort (s : S) : Heterogeneous.HigherCategory ℕ where
  carrier k := GraduatedCell B k s
  str.dim _ _ h := graduatedDimension B h s
  str.compatible _ _ _ ij jk := graduated_compatible B ij jk s

/-- Original operations restrict to cells of any fixed dimension. -/
def graduatedOperation {a s} (σ : sig a s) (k : ℕ)
    (x : Word.Family (fun s => GraduatedCell B k s) a) : GraduatedCell B k s :=
  graduatedCell B ((B.op σ).toFun (fun j => (x j).val))
    (((B.op σ).map_source k (fun j => (x j).val)).symm.trans
      (congrArg (B.op σ).toFun (funext (fun j => (x j).property))))

/-- The explicit graduated categorial algebra, on fixed-source subtypes. -/
noncomputable def graduatedAlgebra : Heterogeneous.OmegaCategorialAlgebra.{u, v, w} sig where
  sort := graduatedSort B
  op σ :=
    { toFun := graduatedOperation B σ
      map_source _ _ _ x := Subtype.ext ((B.op σ).map_source _ (fun j => (x j).val))
      map_target _ _ _ x := Subtype.ext ((B.op σ).map_target _ (fun j => (x j).val))
      map_identity _ _ _ _ := Subtype.ext rfl
      map_comp _ _ h _x _y _z hz := (mem_graduatedComp B h _ _ _).mpr
        ((B.op σ).map_comp _ _ _ _ ((mem_partFamily _ _).mpr
          (fun j => (mem_graduatedComp B h _ _ _).mp ((mem_partFamily _ _).mp hz j)))) }

end CategorialAlgebras.Omega
