import CategorialAlgebras.Limits.HomogeneousStages
import Mathlib.Order.DirectedInverseSystem

/-!
# Equality and operations in the increasing union

Two representatives agree precisely when their images agree in a common later
stage. Injectivity then lets any sufficiently large common stage compute all
operations, independently of the representatives selected by the construction.
-/

universe u v w
namespace CategorialAlgebras.Limits
open CategoryTheory Dimensions Presentations
set_option backward.isDefEq.respectTransparency false
variable {S : Type u} {sig : Signature.{u, v} S}
variable (A : (homogeneousSystem.{u, v, w} sig).Family)

/-- The stage inclusions give a directed system of types at every sort. -/
instance homogeneousStageDirected (s : S) : DirectedSystem
    (fun n => (A.obj n).obj.obj.carrier s) (fun {_ _} h => homogeneousStageInclusion A h s) where
  map_self {i} x := homogeneousStageInclusion_self A i s x
  map_map {_ _ _} h q x := homogeneousStageInclusion_trans A h q s x

/-- The injective bundled inclusion of two finite stages. -/
noncomputable def homogeneousStageEmbedding {m n} (h : m ≤ n) (s : S) :
    (A.obj m).obj.obj.carrier s ↪ (A.obj n).obj.obj.carrier s :=
  ⟨homogeneousStageInclusion A h s, homogeneousStageInclusion_injective A h s⟩

/-- Compatibility of the bundled inclusions. -/
instance homogeneousEmbeddingDirected (s : S) : DirectedSystem
    (fun n => (A.obj n).obj.obj.carrier s) (fun {_ _} h => homogeneousStageEmbedding A h s) :=
  homogeneousStageDirected A s


/-- The setoid comparing representatives in a common later stage. -/
noncomputable def homogeneousCommonSetoid (s : S) : Setoid (Σ n, (A.obj n).obj.obj.carrier s) :=
  DirectLimit.setoid (fun _ _ h => homogeneousStageEmbedding A h s)

/-- Equality of union representatives is equality in some common finite stage. -/
theorem homogeneousUnionIn_eq_iff (m n : ℕ) (s : S) (x) (y) :
    homogeneousUnionIn A m s x = homogeneousUnionIn A n s y ↔
      ∃ (p : ℕ) (hm : m ≤ p) (hn : n ≤ p),
        homogeneousStageInclusion A hm s x = homogeneousStageInclusion A hn s y := by
  constructor
  · intro he
    have hcommon : ∀ {x y : Σ n, (A.obj n).obj.obj.carrier s},
        Relation.EqvGen (homogeneousUnionRelation A s) x y → (homogeneousCommonSetoid A s).r x y := by
      intro x y hr
      induction hr with
      | rel x y h =>
        obtain ⟨h, he⟩ := h
        exact ⟨y.1, h, le_refl _, he.trans (homogeneousStageInclusion_self A _ s _).symm⟩
      | refl x => exact (homogeneousCommonSetoid A s).refl x
      | symm x y _ ih => exact (homogeneousCommonSetoid A s).symm ih
      | trans x y z _ _ ih ih' => exact (homogeneousCommonSetoid A s).trans ih ih'
    exact hcommon (Quot.eq.mp he)
  · rintro ⟨p, hm, hn, he⟩
    exact (homogeneousUnionIn_inclusion A hm s x).trans
      ((congrArg (homogeneousUnionIn A p s) he).trans (homogeneousUnionIn_inclusion A hn s y).symm)

/-- The canonical map from each stage to its union is injective. -/
theorem homogeneousUnionIn_injective (n : ℕ) (s : S) :
    Function.Injective (homogeneousUnionIn A n s) := by
  intro x y h
  obtain ⟨p, hp, _, he⟩ := (homogeneousUnionIn_eq_iff A n n s x y).mp h
  exact homogeneousStageInclusion_injective A hp s he

/-- Equal union cells have equal images in every common later stage. -/
theorem homogeneousUnionIn_eq_at {m n p : ℕ} (hm : m ≤ p) (hn : n ≤ p) (s) (x) (y)
    (he : homogeneousUnionIn A m s x = homogeneousUnionIn A n s y) :
    homogeneousStageInclusion A hm s x = homogeneousStageInclusion A hn s y := by
  obtain ⟨q, hmq, hnq, hq⟩ := (homogeneousUnionIn_eq_iff A m n s x y).mp he
  apply homogeneousStageInclusion_injective A (le_max_left p q) s
  rw [homogeneousStageInclusion_trans, homogeneousStageInclusion_trans]
  have hh := congrArg (homogeneousStageInclusion A (le_max_right p q) s) hq
  simpa only [homogeneousStageInclusion_trans] using hh

/-- A chosen representative, raised to a common stage, agrees with every other representative there. -/
theorem homogeneousUnionAt_eq {m n : ℕ} (h : m ≤ n) (s) (x : (A.obj m).obj.obj.carrier s)
    (hn : (Quot.out (homogeneousUnionIn A m s x)).1 ≤ n) :
    homogeneousUnionAt A s (homogeneousUnionIn A m s x) n hn = homogeneousStageInclusion A h s x :=
  homogeneousUnionIn_eq_at A hn h s _ x (Quot.out_eq _)

/-- Moving a representative to a later stage does not change its image in the union. -/
theorem homogeneousUnionIn_comp {m n : ℕ} (h : m ≤ n) (s) :
    (homogeneousUnionIn A n s) ∘ (homogeneousStageInclusion A h s) = homogeneousUnionIn A m s := by
  funext x
  exact (homogeneousUnionIn_inclusion A h s x).symm

/-- Stage inclusions commute with the whole partial composition, including its domain. -/
theorem homogeneousStageInclusion_comp_map {m n : ℕ} (h : m ≤ n) (s) (k : Fin m) (x y) :
    Part.map (homogeneousStageInclusion A h s) ((((homogeneousStage A m).sort s).str.dim k).comp x y) =
      (((homogeneousStage A n).sort s).str.dim (dimensionInclusion h k)).comp
        (homogeneousStageInclusion A h s x) (homogeneousStageInclusion A h s y) := by
  apply Part.ext
  intro z
  constructor
  · intro hz
    obtain ⟨q, hq, rfl⟩ := (Part.mem_map_iff _).mp hz
    exact homogeneousStageInclusion_comp A h s k x y q hq
  · intro hz
    have hd := (((homogeneousStage A n).sort s).str.dim _).comp_dom _ _ |>.mp hz.1
    rw [← homogeneousStageInclusion_source, ← homogeneousStageInclusion_target] at hd
    have hp := (((homogeneousStage A m).sort s).str.dim k).comp_dom x y |>.mpr
      (homogeneousStageInclusion_injective A h s hd)
    have hq := homogeneousStageInclusion_comp A h s k x y _ (Part.get_mem hp)
    exact (Part.mem_map_iff _).mpr ⟨_, Part.get_mem hp, Part.mem_unique hq hz⟩

/-- Raising a chosen representative agrees with its direct raising to the later stage. -/
theorem homogeneousUnionAt_trans {s} (x : HomogeneousUnion A s) {m n}
    (hm : (Quot.out x).1 ≤ m) (hn : m ≤ n) :
    homogeneousStageInclusion A hn s (homogeneousUnionAt A s x m hm) =
      homogeneousUnionAt A s x n (le_trans hm hn) :=
  homogeneousStageInclusion_trans A hm hn s _

/-- A source on the union can be computed in any stage containing its dimension. -/
theorem homogeneousUnionSource_in {n : ℕ} (k : Fin n) (s) (x : (A.obj n).obj.obj.carrier s) :
    homogeneousUnionSource A k.val s (homogeneousUnionIn A n s x) =
      homogeneousUnionIn A n s ((((homogeneousStage A n).sort s).str.dim k).source x) := by
  let z := homogeneousUnionIn A n s x
  let m := max (k.val + 1) (Quot.out z).1
  let p := max m n
  have hm : m ≤ p := le_max_left _ _
  have hn : n ≤ p := le_max_right _ _
  have hk : k.val < m := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  change homogeneousUnionIn A m s ((((homogeneousStage A m).sort s).str.dim ⟨k.val, hk⟩).source
    (homogeneousUnionAt A s z m (le_max_right _ _))) = _
  calc
    _ = homogeneousUnionIn A p s (homogeneousStageInclusion A hm s
        ((((homogeneousStage A m).sort s).str.dim ⟨k.val, hk⟩).source
          (homogeneousUnionAt A s z m (le_max_right _ _)))) := homogeneousUnionIn_inclusion A hm s _
    _ = homogeneousUnionIn A p s (homogeneousStageInclusion A hn s
        ((((homogeneousStage A n).sort s).str.dim k).source x)) := by
      rw [homogeneousStageInclusion_source, homogeneousStageInclusion_source]
      congr 2
      exact (homogeneousUnionAt_trans A z (le_max_right _ _) hm).trans
        (homogeneousUnionAt_eq A hn s x _)
    _ = _ := (homogeneousUnionIn_inclusion A hn s _).symm

/-- A target on the union can be computed in any stage containing its dimension. -/
theorem homogeneousUnionTarget_in {n : ℕ} (k : Fin n) (s) (x : (A.obj n).obj.obj.carrier s) :
    homogeneousUnionTarget A k.val s (homogeneousUnionIn A n s x) =
      homogeneousUnionIn A n s ((((homogeneousStage A n).sort s).str.dim k).target x) := by
  let z := homogeneousUnionIn A n s x
  let m := max (k.val + 1) (Quot.out z).1
  let p := max m n
  have hm : m ≤ p := le_max_left _ _
  have hn : n ≤ p := le_max_right _ _
  have hk : k.val < m := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  change homogeneousUnionIn A m s ((((homogeneousStage A m).sort s).str.dim ⟨k.val, hk⟩).target
    (homogeneousUnionAt A s z m (le_max_right _ _))) = _
  calc
    _ = homogeneousUnionIn A p s (homogeneousStageInclusion A hm s
        ((((homogeneousStage A m).sort s).str.dim ⟨k.val, hk⟩).target
          (homogeneousUnionAt A s z m (le_max_right _ _)))) := homogeneousUnionIn_inclusion A hm s _
    _ = homogeneousUnionIn A p s (homogeneousStageInclusion A hn s
        ((((homogeneousStage A n).sort s).str.dim k).target x)) := by
      rw [homogeneousStageInclusion_target, homogeneousStageInclusion_target]
      congr 2
      exact (homogeneousUnionAt_trans A z (le_max_right _ _) hm).trans
        (homogeneousUnionAt_eq A hn s x _)
    _ = _ := (homogeneousUnionIn_inclusion A hn s _).symm
/-- Computing a partial composition and inserting its value commutes with moving to a later stage. -/
theorem homogeneousUnionComp_move {m n : ℕ} (h : m ≤ n) (s) (k : Fin m) (x y) :
    Part.map (homogeneousUnionIn A m s) ((((homogeneousStage A m).sort s).str.dim k).comp x y) =
      Part.map (homogeneousUnionIn A n s)
        ((((homogeneousStage A n).sort s).str.dim (dimensionInclusion h k)).comp
          (homogeneousStageInclusion A h s x) (homogeneousStageInclusion A h s y)) := by
  rw [← homogeneousStageInclusion_comp_map, Part.map_map]
  exact congrArg (fun f => Part.map f _) (homogeneousUnionIn_comp A h s).symm

/-- Partial composition on the union is computed in any sufficiently large common stage. -/
theorem homogeneousUnionComp_in {n : ℕ} (k : Fin n) (s) (x y : (A.obj n).obj.obj.carrier s) :
    homogeneousUnionComp A k.val s (homogeneousUnionIn A n s x) (homogeneousUnionIn A n s y) =
      Part.map (homogeneousUnionIn A n s) ((((homogeneousStage A n).sort s).str.dim k).comp x y) := by
  let z := homogeneousUnionIn A n s x
  let t := homogeneousUnionIn A n s y
  let m := max (k.val + 1) (max (Quot.out z).1 (Quot.out t).1)
  let p := max m n
  have hm : m ≤ p := le_max_left _ _
  have hn : n ≤ p := le_max_right _ _
  have hk : k.val < m := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  have hx : (Quot.out z).1 ≤ m := le_trans (le_max_left _ _) (le_max_right _ _)
  have hy : (Quot.out t).1 ≤ m := le_trans (le_max_right _ _) (le_max_right _ _)
  change Part.map (homogeneousUnionIn A m s)
    ((((homogeneousStage A m).sort s).str.dim ⟨k.val, hk⟩).comp
      (homogeneousUnionAt A s z m hx) (homogeneousUnionAt A s t m hy)) = _
  calc
    _ = Part.map (homogeneousUnionIn A p s)
        ((((homogeneousStage A p).sort s).str.dim (dimensionInclusion hm ⟨k.val, hk⟩)).comp
          (homogeneousStageInclusion A hm s (homogeneousUnionAt A s z m hx))
          (homogeneousStageInclusion A hm s (homogeneousUnionAt A s t m hy))) :=
      homogeneousUnionComp_move A hm s ⟨k.val, hk⟩ _ _
    _ = Part.map (homogeneousUnionIn A p s)
        ((((homogeneousStage A p).sort s).str.dim (dimensionInclusion hn k)).comp
          (homogeneousStageInclusion A hn s x) (homogeneousStageInclusion A hn s y)) := by
      rw [homogeneousUnionAt_trans, homogeneousUnionAt_trans,
        homogeneousUnionAt_eq A hn s x, homogeneousUnionAt_eq A hn s y]
      rfl
    _ = _ := (homogeneousUnionComp_move A hn s k x y).symm

/-- All values of partial composition can be checked in a common finite stage. -/
theorem homogeneousUnionComp_mem {n : ℕ} (k : Fin n) (s) (x y z : (A.obj n).obj.obj.carrier s) :
    homogeneousUnionIn A n s z ∈
      homogeneousUnionComp A k.val s (homogeneousUnionIn A n s x) (homogeneousUnionIn A n s y) ↔
        z ∈ (((homogeneousStage A n).sort s).str.dim k).comp x y := by
  rw [homogeneousUnionComp_in, Part.mem_map_iff]
  exact ⟨fun ⟨q, hq, he⟩ => (homogeneousUnionIn_injective A n s he) ▸ hq,
    fun hz => ⟨z, hz, rfl⟩⟩

/-- Original operations on the union are computed at every common finite stage. -/
theorem homogeneousUnionBase_in {n : ℕ} {a s} (σ : sig a s)
    (x : Word.Family ((homogeneousStage A n).carrier) a) :
    homogeneousUnionBase A σ (fun j => homogeneousUnionIn A n _ (x j)) =
      homogeneousUnionIn A n s (((homogeneousStage A n).op σ).toFun x) := by
  let z : Word.Family (HomogeneousUnion A) a := fun j => homogeneousUnionIn A n _ (x j)
  let m := homogeneousWordStage A z
  let p := max m n
  have hm : m ≤ p := le_max_left _ _
  have hn : n ≤ p := le_max_right _ _
  change homogeneousUnionIn A m s (((homogeneousStage A m).op σ).toFun
    (fun j => homogeneousUnionAt A _ (z j) m (homogeneousWordStage_le A z j))) = _
  calc
    _ = homogeneousUnionIn A p s (homogeneousStageInclusion A hm s
        (((homogeneousStage A m).op σ).toFun
          (fun j => homogeneousUnionAt A _ (z j) m (homogeneousWordStage_le A z j)))) :=
      homogeneousUnionIn_inclusion A hm s _
    _ = homogeneousUnionIn A p s (homogeneousStageInclusion A hn s
        (((homogeneousStage A n).op σ).toFun x)) := by
      rw [homogeneousStageInclusion_op, homogeneousStageInclusion_op]
      congr 2
      funext j
      exact (homogeneousUnionAt_trans A (z j) (homogeneousWordStage_le A z j) hm).trans
        (homogeneousUnionAt_eq A hn _ (x j) _)
    _ = _ := (homogeneousUnionIn_inclusion A hn s _).symm

/-- Every finite sorted tuple of union cells has representatives in a common stage above any bound. -/
theorem homogeneousUnion_cover {r : ℕ} (sorts : Fin r → S)
    (x : ∀ j, HomogeneousUnion A (sorts j)) (bound : ℕ) :
    ∃ n, bound ≤ n ∧ ∃ y : ∀ j, (homogeneousStage A n).carrier (sorts j),
      ∀ j, homogeneousUnionIn A n (sorts j) (y j) = x j := by
  classical
  let n := max bound (Finset.univ.sup (fun j => (Quot.out (x j)).1))
  have hn j : (Quot.out (x j)).1 ≤ n :=
    le_trans (Finset.le_sup (f := fun j => (Quot.out (x j)).1) (Finset.mem_univ j)) (le_max_right _ _)
  refine ⟨n, le_max_left _ _, (fun j => homogeneousUnionAt A _ (x j) n (hn j)), ?_⟩
  intro j
  exact (homogeneousUnionIn_inclusion A (hn j) _ (Quot.out (x j)).2).symm.trans (Quot.out_eq (x j))

/-- A tuple indexed by any finite type has common representatives above every bound. -/
theorem homogeneousUnion_cover_finite {ι : Type*} [Fintype ι] (sorts : ι → S)
    (x : ∀ j, HomogeneousUnion A (sorts j)) (bound : ℕ) :
    ∃ n, bound ≤ n ∧ ∃ y : ∀ j, (homogeneousStage A n).carrier (sorts j),
      ∀ j, homogeneousUnionIn A n (sorts j) (y j) = x j := by
  classical
  let n := max bound (Finset.univ.sup (fun j => (Quot.out (x j)).1))
  have hn j : (Quot.out (x j)).1 ≤ n :=
    le_trans (Finset.le_sup (f := fun j => (Quot.out (x j)).1) (Finset.mem_univ j)) (le_max_right _ _)
  refine ⟨n, le_max_left _ _, (fun j => homogeneousUnionAt A _ (x j) n (hn j)), ?_⟩
  intro j
  exact (homogeneousUnionIn_inclusion A (hn j) _ (Quot.out (x j)).2).symm.trans (Quot.out_eq (x j))

end CategorialAlgebras.Limits
