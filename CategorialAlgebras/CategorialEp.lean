import Stemma
import CategorialAlgebras.EpSignature
import CategorialAlgebras.Compact.Identification
import CategorialAlgebras.Extended.Model

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "Categorial specifications as ep-specifications" =>

In the compact and in the extended presentation, a higher-order categorial algebra is a partial
algebra in which the operations of $`\Sigma`, the sources, the targets and the identities are
total, and a composition is defined exactly when the source of its first argument is the target of
its second one. These are the domain conditions of an ep-signature (Remark `RCompactEp` and the
first part of Proposition `PExtendedIdent` of the draft): with them, the compact and the extended
specifications become ep-specifications whose models are those of the $`\mathrm{QE}`-specifications
$`\mathcal{C}^{\Sigma^{(n)}}` and $`\mathcal{C}^{\Sigma^{\mathrm{ext}(n)}}`. The functors of
graduation and unification are induced by generalized ep-derivors between these ep-specifications.

As the specifications, the ep-signatures are written once for every preordered set of dimensions
$`I`.

```lean
universe u v w

namespace CategorialAlgebras

open Signature Term

variable {S : Type u} (Sig : Signature.{u, v} S) (Index : Type) [Preorder Index]
```

```lean
section
variable {S : Type u} {Sig : Signature.{u, v} S} {A : PartialAlgebra.{u, v, w} Sig}
  {ws : List S} {s : S} {σ : Sig ws s}

lemma op_dom_congr {a b : Arity A ws} (e : a = b) : (A.op σ a).Dom ↔ (A.op σ b).Dom := by
  rw [e]

lemma op_eq_some_get {a b : Arity A ws} (e : b = a) (h : (A.op σ b).Dom) :
    A.op σ a = Part.some ((A.op σ b).get h) := by
  subst e; exact (Part.some_get h).symm
end
```

# The compact ep-signature

:::definition (label := "compact.ep-signature") (central := false) (title := "The compact ep-signature")
The compact categorial signature with dimensions in $`I` is an ep-signature in which the operation
symbols of $`\Sigma`, the $`k`-sources and the $`k`-targets have no domain conditions, and
$`\circ^{k}_{s}` has the single domain condition
$`\mathrm{sc}^{k}_{s}(v_0) \overset{\mathrm{e}}{=} \mathrm{tg}^{k}_{s}(v_1)`. The relation
$`\lhd` is well-founded: only the compositions have domain conditions, and only sources and
targets occur in them.

```lean
/-- The domain conditions of the compact signature. -/
def compactDefn : ∀ {ws : List S} {s : S}, Compact.CompactSignature Sig Index ws s →
    Set (EEq (Compact.CompactSignature Sig Index) (Vars ws.get))
  | _, _, .comp k s => {EEq.mk' (app₁ (.sc k s) (.var (Vars.mk (κ := [s, s].get) ⟨0, by simp⟩)))
      (app₁ (.tg k s) (.var (Vars.mk (κ := [s, s].get) ⟨1, by simp⟩)))}
  | _, _, .op _ => ∅
  | _, _, .sc _ _ => ∅
  | _, _, .tg _ _ => ∅

/-- The rank of an operation symbol: `1` for the compositions, `0` otherwise. -/
def compactRank : Op (Compact.CompactSignature Sig Index) → ℕ
  | ⟨_, _, .comp _ _⟩ => 1
  | _ => 0

/-- The compact ep-signature `𝚺⁽ⁿ⁾`. -/
def compactEpSig : EpSignature.{u, max u v} S where
  sig := Compact.CompactSignature Sig Index
  defn := compactDefn Sig Index
  wf := by
    refine Subrelation.wf (r := InvImage (· < ·) (compactRank Sig Index)) ?_
      (InvImage.wf _ wellFounded_lt)
    rintro τ ⟨ws, s, σ⟩ ⟨e, he, hτ⟩
    cases σ with
    | op _ => exact he.elim
    | sc _ _ => exact he.elim
    | tg _ _ => exact he.elim
    | comp k s =>
      obtain rfl := he
      simp only [EEq.ops, EEq.mk', app₁, Term.ops, Set.mem_union, Set.mem_singleton_iff] at hτ
      rcases hτ with (rfl | hτ) | (rfl | hτ)
      · simp [InvImage, compactRank]
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hτ
        match j, hj with
        | ⟨0, _⟩, hj => simp [Term.args₁, Term.ops] at hj
      · simp [InvImage, compactRank]
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hτ
        match j, hj with
        | ⟨0, _⟩, hj => simp [Term.args₁, Term.ops] at hj
```
:::

:::proof (of := "compact.ep-signature")
Every operation symbol other than a composition has rank $`0`, and every composition rank $`1`.
If $`\tau \lhd \sigma`, then $`\sigma` has a domain condition, so it is a composition
$`\circ^{k}_{s}`, and $`\tau` occurs in $`\mathrm{sc}^{k}_{s}(v_0)` or in
$`\mathrm{tg}^{k}_{s}(v_1)`, so it is $`\mathrm{sc}^{k}_{s}` or $`\mathrm{tg}^{k}_{s}`. Hence
$`\lhd` decreases the rank, and it is well-founded.
:::

:::definition (label := "compact.ep-specification") (central := false) (title := "The compact ep-specification")
The compact ep-specification $`(\mathbf{\Sigma}^{(n)}, \mathcal{C}^{\Sigma^{(n)}})` is the
compact ep-signature together with the specification $`\mathcal{C}^{\Sigma^{(n)}}`.

```lean
/-- The compact ep-specification `(𝚺⁽ⁿ⁾, 𝒞^{Σ⁽ⁿ⁾})`. -/
def compactEpSpec : EpSpec.{u, max u v} S (Compact.Var S) :=
  ⟨compactEpSig Sig Index, Compact.compactSpec Sig Index⟩
```
:::

:::proposition (label := "compact.ep-models") (central := false) (title := "The models of the compact ep-specification")
A partial $`\Sigma^{(n)}`-algebra is a model of the compact ep-specification if and only if it is a
model of $`\mathcal{C}^{\Sigma^{(n)}}`. Hence
$`\mathsf{PAlg}(\mathcal{C}^{\Sigma^{(n)}}) = \mathsf{epAlg}(\mathbf{\Sigma}^{(n)}, \mathcal{C}^{\Sigma^{(n)}})`.

```lean
theorem compactEpSpec_isModel_iff (A : PartialAlgebra.{u, max u v, w} (Compact.CompactSignature Sig Index)) :
    (compactEpSpec Sig Index).IsModel A ↔ ∀ q ∈ Compact.compactSpec Sig Index, q.Holds A := by
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  let M : Compact.CompactPAlg.{u, v, w} Sig Index := ⟨A, h⟩
  intro ws s σ a
  cases σ with
  | op σ => exact ⟨fun _ => EEq.holdsAll_empty, fun _ => Compact.op_dom (M := M) σ a⟩
  | sc k s =>
    exact ⟨fun _ => EEq.holdsAll_empty, fun _ => (op_dom_congr (by
      funext i; match i with | ⟨0, _⟩ => rfl)).mp (Compact.sc_dom (M := M) k (a ⟨0, by simp⟩))⟩
  | tg k s =>
    exact ⟨fun _ => EEq.holdsAll_empty, fun _ => (op_dom_congr (by
      funext i; match i with | ⟨0, _⟩ => rfl)).mp (Compact.tg_dom (M := M) k (a ⟨0, by simp⟩))⟩
  | comp k s =>
    have h0 : (app₁ (.sc k s) (.var (Vars.mk (κ := [s, s].get) ⟨0, by simp⟩)) :
        Term (Compact.CompactSignature Sig Index) (Vars [s, s].get) s).eval A (famVal a) =
        Part.some (Compact.msc M k (a ⟨0, by simp⟩)) := by
      rw [eval_app₁_of_eq_some _ _ _ rfl]
      exact op_eq_some_get (by funext i; match i with | ⟨0, _⟩ => rfl) _
    have h1 : (app₁ (.tg k s) (.var (Vars.mk (κ := [s, s].get) ⟨1, by simp⟩)) :
        Term (Compact.CompactSignature Sig Index) (Vars [s, s].get) s).eval A (famVal a) =
        Part.some (Compact.mtg M k (a ⟨1, by simp⟩)) := by
      rw [eval_app₁_of_eq_some _ _ _ rfl]
      exact op_eq_some_get (by funext i; match i with | ⟨0, _⟩ => rfl) _
    change _ ↔ EEq.HoldsAll A (famVal a) {_}
    rw [EEq.holdsAll_singleton, EEq.holds_mk'_iff h0 h1]
    letI := Compact.modelStruct (M := M) s
    refine (op_dom_congr ?_).trans
      (Compact.CategoryStruct.pcomp_dom (C := M.1 s) (k := k) (g := a ⟨0, by simp⟩)
        (f := a ⟨1, by simp⟩))
    funext i; match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl
```
:::

:::proof (of := "compact.ep-models")
A model of the ep-specification is a model of $`\mathcal{C}^{\Sigma^{(n)}}`. Conversely, in a model
of $`\mathcal{C}^{\Sigma^{(n)}}` the operations without domain conditions are total, by (A0) and
(A$`^{k}`1), and $`x \circ^{k}_{s} y` is defined if and only if
$`\mathrm{sc}^{k}_{s}(x) = \mathrm{tg}^{k}_{s}(y)`, by (A$`^{k}`3), which is its domain condition.
:::

:::construction (label := "compact.ep-alg-equiv") (central := false) (title := "PAlg(C^Σ⁽ⁿ⁾) = epAlg(Σ⁽ⁿ⁾, C^Σ⁽ⁿ⁾)")
By Proposition `compact.ep-models`, the category of models of $`\mathcal{C}^{\Sigma^{(n)}}` and the
category of models of the compact ep-specification have the same objects and the same morphisms;
the identity is an equivalence between them.

```lean
open CategoryTheory in
/-- `PAlg(𝒞^{Σ⁽ⁿ⁾}) ≌ epAlg(𝚺⁽ⁿ⁾, 𝒞^{Σ⁽ⁿ⁾})`. -/
def compactEpAlgEquiv :
    Compact.CompactPAlg.{u, v, w} Sig Index ≌ EpSpec.EpAlg.{u, max u v, w} (compactEpSpec Sig Index) :=
  CategoryTheory.Equivalence.mk
    { obj M := ⟨M.1, (compactEpSpec_isModel_iff Sig Index M.1).mpr M.2⟩, map f := f
      map_id _ := rfl, map_comp _ _ := rfl }
    { obj A := ⟨A.1, A.2.2⟩, map f := f, map_id _ := rfl, map_comp _ _ := rfl }
    (NatIso.ofComponents (fun _ => Iso.refl _))
    (NatIso.ofComponents (fun _ => Iso.refl _))
```
:::

# The extended ep-signature

:::definition (label := "extended.ep-signature") (central := false) (title := "The extended ep-signature")
The extended categorial signature with dimensions in $`I` is an ep-signature in which only the
compositions have domain conditions: $`\circ^{(j,k)}_{s}` has the single domain condition
$`\mathrm{sc}^{(j,k)}_{s}(v_0) \overset{\mathrm{e}}{=} \mathrm{tg}^{(j,k)}_{s}(v_1)`.

```lean
/-- The domain conditions of the extended signature. -/
def extendedDefn : ∀ {ws : List (Index × S)} {t : Index × S},
    Extended.ExtendedSignature Sig Index ws t →
    Set (EEq (Extended.ExtendedSignature Sig Index) (Vars ws.get))
  | _, _, @Extended.ExtendedSignature.comp _ _ _ _ j k h s =>
      {EEq.mk' (app₁ (.sc h s) (.var (Vars.mk (κ := [(k, s), (k, s)].get) ⟨0, by simp⟩)))
        (app₁ (.tg h s) (.var (Vars.mk (κ := [(k, s), (k, s)].get) ⟨1, by simp⟩)))}
  | _, _, .op _ _ => ∅
  | _, _, .sc _ _ => ∅
  | _, _, .tg _ _ => ∅
  | _, _, .idm _ _ => ∅

/-- The rank of an operation symbol: `1` for the compositions, `0` otherwise. -/
def extendedRank : Op (Extended.ExtendedSignature Sig Index) → ℕ
  | ⟨_, _, .comp _ _⟩ => 1
  | _ => 0

/-- The extended ep-signature `𝚺^{ext(n)}`. -/
def extendedEpSig : EpSignature.{u, max u v} (Index × S) where
  sig := Extended.ExtendedSignature Sig Index
  defn := extendedDefn Sig Index
  wf := by
    refine Subrelation.wf (r := InvImage (· < ·) (extendedRank Sig Index)) ?_
      (InvImage.wf _ wellFounded_lt)
    rintro τ ⟨ws, t, σ⟩ ⟨e, he, hτ⟩
    cases σ with
    | op _ _ => exact he.elim
    | sc _ _ => exact he.elim
    | tg _ _ => exact he.elim
    | idm _ _ => exact he.elim
    | comp h s =>
      obtain rfl := he
      simp only [EEq.ops, EEq.mk', app₁, Term.ops, Set.mem_union, Set.mem_singleton_iff] at hτ
      rcases hτ with (rfl | hτ) | (rfl | hτ)
      · simp [InvImage, extendedRank]
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hτ
        match j, hj with
        | ⟨0, _⟩, hj => simp [Term.args₁, Term.ops] at hj
      · simp [InvImage, extendedRank]
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hτ
        match j, hj with
        | ⟨0, _⟩, hj => simp [Term.args₁, Term.ops] at hj
```
:::

:::proof (of := "extended.ep-signature")
As for the compact ep-signature: $`\lhd` decreases the rank, which is $`1` for the compositions and
$`0` for the other operation symbols.
:::

:::definition (label := "extended.ep-specification") (central := false) (title := "The extended ep-specification")
The extended ep-specification $`(\mathbf{\Sigma}^{\mathrm{ext}(n)}, \mathcal{C}^{\Sigma^{\mathrm{ext}(n)}})`
is the extended ep-signature together with the specification
$`\mathcal{C}^{\Sigma^{\mathrm{ext}(n)}}`.

```lean
/-- The extended ep-specification `(𝚺^{ext(n)}, 𝒞^{Σ^{ext(n)}})`. -/
def extendedEpSpec : EpSpec.{u, max u v} (Index × S) (Extended.EVar S Index) :=
  ⟨extendedEpSig Sig Index, Extended.extendedSpec Sig Index⟩
```
:::

:::proposition (label := "extended.ep-models") (central := false) (title := "The models of the extended ep-specification")
A partial $`\Sigma^{\mathrm{ext}(n)}`-algebra is a model of the extended ep-specification if and
only if it is a model of $`\mathcal{C}^{\Sigma^{\mathrm{ext}(n)}}`. Hence
$`\mathsf{PAlg}(\mathcal{C}^{\Sigma^{\mathrm{ext}(n)}}) = \mathsf{epAlg}(\mathbf{\Sigma}^{\mathrm{ext}(n)}, \mathcal{C}^{\Sigma^{\mathrm{ext}(n)}})`.

```lean
theorem extendedEpSpec_isModel_iff
    (A : PartialAlgebra.{u, max u v, w} (Extended.ExtendedSignature Sig Index)) :
    (extendedEpSpec Sig Index).IsModel A ↔ ∀ q ∈ Extended.extendedSpec Sig Index, q.Holds A := by
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  let M : Extended.ExtendedPAlg.{u, v, w} Sig Index := ⟨A, h⟩
  intro ws t σ a
  cases σ with
  | op k σ => exact ⟨fun _ => EEq.holdsAll_empty, fun _ => Extended.Model.op_dom' (M := M) k σ a⟩
  | sc h s =>
    exact ⟨fun _ => EEq.holdsAll_empty, fun _ => (op_dom_congr (by
      funext i; match i with | ⟨0, _⟩ => rfl)).mp
        (Extended.Model.sc_dom (M := M) h (a ⟨0, by simp⟩))⟩
  | tg h s =>
    exact ⟨fun _ => EEq.holdsAll_empty, fun _ => (op_dom_congr (by
      funext i; match i with | ⟨0, _⟩ => rfl)).mp
        (Extended.Model.tg_dom (M := M) h (a ⟨0, by simp⟩))⟩
  | idm h s =>
    exact ⟨fun _ => EEq.holdsAll_empty, fun _ => (op_dom_congr (by
      funext i; match i with | ⟨0, _⟩ => rfl)).mp
        (Extended.Model.idm_dom (M := M) h (a ⟨0, by simp⟩))⟩
  | @comp j k h s =>
    have h0 : (app₁ (.sc h s) (.var (Vars.mk (κ := [(k, s), (k, s)].get) ⟨0, by simp⟩)) :
        Term (Extended.ExtendedSignature Sig Index) (Vars [(k, s), (k, s)].get) (j, s)).eval A
          (famVal a) = Part.some (Extended.Model.sc M h (a ⟨0, by simp⟩)) := by
      rw [eval_app₁_of_eq_some _ _ _ rfl]
      exact op_eq_some_get (by funext i; match i with | ⟨0, _⟩ => rfl) _
    have h1 : (app₁ (.tg h s) (.var (Vars.mk (κ := [(k, s), (k, s)].get) ⟨1, by simp⟩)) :
        Term (Extended.ExtendedSignature Sig Index) (Vars [(k, s), (k, s)].get) (j, s)).eval A
          (famVal a) = Part.some (Extended.Model.tg M h (a ⟨1, by simp⟩)) := by
      rw [eval_app₁_of_eq_some _ _ _ rfl]
      exact op_eq_some_get (by funext i; match i with | ⟨0, _⟩ => rfl) _
    change _ ↔ EEq.HoldsAll A (famVal a) {_}
    rw [EEq.holdsAll_singleton, EEq.holds_mk'_iff h0 h1]
    refine (op_dom_congr ?_).trans (Extended.Model.pcomp_dom_iff (M := M))
    funext i; match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl
```
:::

:::proof (of := "extended.ep-models")
As for the compact ep-specification: the operations without domain conditions are total by (EA0)
and (EA$`^{j,k}`1), and the domain condition of $`\circ^{(j,k)}_{s}` is (EA$`^{j,k}`3).
:::

:::construction (label := "extended.ep-alg-equiv") (central := false) (title := "PAlg(C^Σᵉˣᵗ⁽ⁿ⁾) = epAlg(Σᵉˣᵗ⁽ⁿ⁾, C^Σᵉˣᵗ⁽ⁿ⁾)")
By Proposition `extended.ep-models`, the identity is an equivalence between the category of models
of $`\mathcal{C}^{\Sigma^{\mathrm{ext}(n)}}` and that of the extended ep-specification.

```lean
open CategoryTheory in
/-- `epAlg(𝚺^{ext(n)}, 𝒞^{Σ^{ext(n)}}) ≌ PAlg(𝒞^{Σ^{ext(n)}})`. -/
def extendedEpAlgEquiv :
    EpSpec.EpAlg.{u, max u v, w} (extendedEpSpec Sig Index) ≌
      Extended.ExtendedPAlg.{u, v, w} Sig Index :=
  CategoryTheory.Equivalence.mk
    { obj A := ⟨A.1, A.2.2⟩, map f := f, map_id _ := rfl, map_comp _ _ := rfl }
    { obj M := ⟨M.1, (extendedEpSpec_isModel_iff Sig Index M.1).mpr M.2⟩, map f := f
      map_id _ := rfl, map_comp _ _ := rfl }
    (NatIso.ofComponents (fun _ => Iso.refl _))
    (NatIso.ofComponents (fun _ => Iso.refl _))
```
:::

```lean
end CategorialAlgebras
```
