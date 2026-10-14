import Stemma
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Fintype.EquivFin
import CategorialAlgebras.EpSignature

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "Generalized ep-derivors" =>

The general derivors of {cite}`LG18` are morphisms between order-sorted signatures with
predicates that send every sort to a formula delimiting, inside the interpretation of the image
sort, the elements that interpret it, and every operation symbol to a formula. The equationally
partial signatures of {cite}`Rei87` carry, for every operation symbol, a set of existence
equations that describes its domain. A *generalized ep-derivor* (Section `SGenEpDerivors` of the
draft) combines both ideas, with existence equations in place of formulas: it sends every sort to
a set of existence equations in one variable, which delimits the elements that interpret the sort,
and every operation symbol to a term; the domain of the operation symbol in the transformed
algebras is given by its domain conditions. This document defines them, the partial algebras they
derive, and when they send the models of one ep-specification to those of another.

```lean
universe u v u' v' w

namespace CategorialAlgebras

open Signature CategoryTheory

variable {S : Type u} {T : Type u'}

/-- The valuation of the single variable of the word `(t)` at `b`. -/
def val₁ {A : T → Type w} {t : T} (b : A t) : ∀ t', Vars (fun _ : Unit => t) t' → Part (A t') :=
  famVal (κ := fun _ : Unit => t) fun _ => b

lemma eq_val₁ {A : T → Type w} {t₀ : T} {f : ∀ t, Vars (fun _ : Unit => t₀) t → Part (A t)}
    {b : A t₀} (h : f t₀ ⟨(), rfl⟩ = Part.some b) : f = val₁ b := by
  funext t x; obtain ⟨⟨⟩, rfl⟩ := x; exact h
```

# Generalized ep-derivors

:::definition (label := "gen-ep-derivor") (central := false) (title := "Generalized ep-derivors")
Let $`\mathbf{\Sigma} = (S, \Sigma, \mathrm{def}^{\mathbf{\Sigma}})` and
$`\mathbf{\Lambda} = (T, \Lambda, \mathrm{def}^{\mathbf{\Lambda}})` be ep-signatures. A
*generalized ep-derivor* from $`\mathbf{\Sigma}` to $`\mathbf{\Lambda}` is a triple
$`\mathbf{d} = (\varphi, D, d)` where

1. $`\varphi` is a mapping from $`S` to $`T`;
2. $`D` assigns to every sort $`s \in S` a set $`D_s` of existence equations of $`\Lambda` in
   the single variable of $`\downarrow(\varphi(s))`, the *domain* of $`s`; and
3. $`(\varphi, d)` is a derivor from $`(S, \Sigma)` to $`(T, \Lambda)`.

For a mapping $`\kappa \colon I \to S`, $`D_{\kappa}` is the set of the domains of the
$`\kappa(i)`, each stated for the variable $`i` of $`\downarrow(\varphi \circ \kappa)`:
$`D_\kappa = \bigcup_{i \in I} (\iota_i)^{\sharp}[D_{\kappa(i)}]`, where $`\iota_i` renames the
variable of $`\downarrow(\varphi(\kappa(i)))` to $`i`. For a word $`\mathbf{s}` this is the set
$`D_{\mathbf{s}}` of the draft.

```lean
structure GenEpDerivor (Sg : EpSignature.{u, v} S) (Lg : EpSignature.{u', v'} T) where
  /-- The mapping of sorts `φ`. -/
  sortMap : S → T
  /-- The domain `D_s` of each sort. -/
  sortDom : ∀ s : S, Set (EEq Lg.sig (Vars fun _ : Unit => sortMap s))
  /-- The term `d(σ)` of each operation symbol. -/
  op : ∀ {ws : List S} {s : S}, Sg.sig ws s → Term Lg.sig (Vars (sortMap ∘ ws.get)) (sortMap s)

namespace GenEpDerivor

variable {Sg : EpSignature.{u, v} S} {Lg : EpSignature.{u', v'} T} (δ : GenEpDerivor Sg Lg)

/-- The derivor `(φ, d)`. -/
def toDerivor : Derivor Sg.sig Lg.sig := ⟨δ.sortMap, δ.op⟩

/-- The renaming `ιᵢ` of the variable of `↓(φ(κ i))` to the variable `i` of `↓(φ ∘ κ)`. -/
def famDomRen {I : Type} (κ : I → S) (i : I) :
    ∀ t, Vars (fun _ : Unit => δ.sortMap (κ i)) t → Term Lg.sig (Vars (δ.sortMap ∘ κ)) t :=
  fun _ x => .var ⟨i, x.2⟩

/-- The domains `D_κ` of a family of sorts. -/
def famDom {I : Type} (κ : I → S) : Set (EEq Lg.sig (Vars (δ.sortMap ∘ κ))) :=
  ⋃ i, EEq.substSet (δ.famDomRen κ i) (δ.sortDom (κ i))

end GenEpDerivor
```
:::

# The underlying sets of the derived algebras

```lean
/-- The forgetful functor from partial algebras to sorted sets. -/
def PartialAlgebra.forget {Sig : Signature.{u, v} S} :
    PartialAlgebra.{u, v, w} Sig ⥤ (S → Type w) where
  obj A := A.carrier
  map f s := TypeCat.ofHom (f.map s)

namespace GenEpDerivor

variable {Sg : EpSignature.{u, v} S} {Lg : EpSignature.{u', v'} T} (δ : GenEpDerivor Sg Lg)
```

:::proposition (label := "gen-ep-delta") (central := false) (title := "The functor Δ_(φ,D)")
Let $`\mathbf{d} = (\varphi, D, d)` be a generalized ep-derivor. There is a functor
$`\Delta_{(\varphi, D)}` from $`\mathsf{PAlg}(\Lambda)` to $`\mathsf{Set}^{S}` that sends a partial
$`\Lambda`-algebra $`\mathbf{B}` to the $`S`-sorted set $`B_{(\varphi, D)}` with
$`(B_{(\varphi, D)})_s = \{b \in B_{\varphi(s)} \mid \mathbf{B} \models D_s[b]\}`, and a
homomorphism $`f` to the family of the restrictions of the $`f_{\varphi(s)}`. Moreover, a family
$`\mathbf{b}` with $`b_i \in B_{\varphi(\kappa(i))}` is in $`(B_{(\varphi, D)})_{\kappa}` if and
only if $`\mathbf{B} \models D_{\kappa}[\mathbf{b}]`.

```lean
/-- The cells `(B_(φ,D))_s`. -/
def cells (B : PartialAlgebra.{u', v', w} Lg.sig) (s : S) : Type w :=
  {b : B (δ.sortMap s) // EEq.HoldsAll B (val₁ b) (δ.sortDom s)}

lemma cells_map {B B' : PartialAlgebra.{u', v', w} Lg.sig} (f : B ⟶ B') {s : S} (b : δ.cells B s) :
    EEq.HoldsAll B' (val₁ (f.map _ b.1)) (δ.sortDom s) := by
  have key : (fun t x => (val₁ b.1 t x).map (f.map t)) = val₁ (f.map _ b.1) := famVal_map _ _
  rw [← key]
  exact EEq.holdsAll_hom f (val₁ b.1) b.2

/-- The functor `Δ_(φ,D)`. -/
def delta : PartialAlgebra.{u', v', w} Lg.sig ⥤ (S → Type w) where
  obj B := δ.cells B
  map f s := TypeCat.ofHom fun b => ⟨f.map _ b.1, δ.cells_map f b⟩

theorem holdsAll_famDom_iff {B : PartialAlgebra.{u', v', w} Lg.sig} {I : Type} {κ : I → S}
    (b : ∀ i, B (δ.sortMap (κ i))) :
    EEq.HoldsAll B (famVal b) (δ.famDom κ) ↔ ∀ i, EEq.HoldsAll B (val₁ (b i)) (δ.sortDom (κ i)) := by
  rw [famDom, EEq.holdsAll_iUnion]
  refine forall_congr' fun i => ?_
  rw [EEq.holdsAll_substSet]
  have : (fun t x => (δ.famDomRen κ i t x).eval B (famVal b)) = val₁ (b i) :=
    eq_val₁ (by simp only [famDomRen, Term.eval_var]; rfl)
  rw [this]
```
:::

:::proof (of := "gen-ep-delta")
If $`\mathbf{B} \models D_s[b]`, then $`\mathbf{B}' \models D_s[f(b)]` by Proposition `hom-eval`, so the
restrictions are well defined; they preserve identities and composites because restrictions do.
For a family, $`(\iota_i)^{\sharp}` only renames a variable, so, by Proposition `subst-eval`,
$`\mathbf{B} \models (\iota_i)^{\sharp}[D_{\kappa(i)}][\mathbf{b}]` if and only if
$`\mathbf{B} \models D_{\kappa(i)}[b_i]`.
:::

# Domains, definedness conditions and translations

To translate an existence equation it does not suffice to translate both members: if $`d(\sigma)`
does not contain the variable $`j`, then $`d^{\sharp}(\sigma((P_i)_i))` can be defined although
$`P_j` is not. The translation therefore also states that all the subterms are defined, which
requires the domains of the operation symbols, which in turn are given by the translations of
their domain conditions. Both are defined at once by recursion along the well-founded relation
$`\lhd` of the ep-signature.

In the Lean, the definedness conditions and the translations are first defined for an arbitrary
assignment `dm` of domains to the operation symbols; the domains are then the fixed point of the
recursion along $`\lhd`, which only uses `dm` at the symbols that precede the one being defined.

```lean
/-- The definedness conditions `dfd(R)`, for an assignment `dm` of domains to the operation
symbols. -/
def dfdWith (dm : ∀ τ : Op Sg.sig, Set (EEq Lg.sig (Vars (δ.sortMap ∘ τ.ws.get))))
    {I : Type} {κ : I → S} : {t : S} → Term Sg.sig (Vars κ) t → Set (EEq Lg.sig (Vars (δ.sortMap ∘ κ)))
  | _, .var _ => ∅
  | _, .app τ ts => (⋃ j, dfdWith dm (ts j)) ∪
      EEq.substSet (famSubst fun j => δ.toDerivor.lift (ts j)) (dm ⟨_, _, τ⟩)

/-- The translation `tr(P, Q)` of an existence equation, for an assignment `dm` of domains. -/
def trWith (dm : ∀ τ : Op Sg.sig, Set (EEq Lg.sig (Vars (δ.sortMap ∘ τ.ws.get))))
    {I : Type} {κ : I → S} (e : EEq Sg.sig (Vars κ)) : Set (EEq Lg.sig (Vars (δ.sortMap ∘ κ))) :=
  insert ⟨δ.sortMap e.sort, δ.toDerivor.lift e.lhs, δ.toDerivor.lift e.rhs⟩
    (δ.dfdWith dm e.lhs ∪ δ.dfdWith dm e.rhs)

/-- The translation `tr[ℋ]` of a set of existence equations. -/
def trSetWith (dm : ∀ τ : Op Sg.sig, Set (EEq Lg.sig (Vars (δ.sortMap ∘ τ.ws.get))))
    {I : Type} {κ : I → S} (H : Set (EEq Sg.sig (Vars κ))) : Set (EEq Lg.sig (Vars (δ.sortMap ∘ κ))) :=
  ⋃ e ∈ H, δ.trWith dm e

/-- The substitution `d(σ)♯` that sends the variable of `↓(φ(s))` to `d(σ)`. -/
def resultSubst (σ : Op Sg.sig) :
    ∀ t, Vars (fun _ : Unit => δ.sortMap σ.s) t → Term Lg.sig (Vars (δ.sortMap ∘ σ.ws.get)) t :=
  fun _ x => x.2 ▸ δ.op σ.σ

/-- One step of the recursion that defines the domains. -/
def domStep (σ : Op Sg.sig) (dm : ∀ τ : Op Sg.sig, Set (EEq Lg.sig (Vars (δ.sortMap ∘ τ.ws.get)))) :
    Set (EEq Lg.sig (Vars (δ.sortMap ∘ σ.ws.get))) :=
  δ.famDom σ.ws.get ∪ δ.trSetWith dm (Sg.defn σ.σ) ∪ {⟨_, δ.op σ.σ, δ.op σ.σ⟩} ∪
    EEq.substSet (δ.resultSubst σ) (δ.sortDom σ.s)

lemma dfdWith_congr {dm dm' : ∀ τ : Op Sg.sig, Set (EEq Lg.sig (Vars (δ.sortMap ∘ τ.ws.get)))}
    {I : Type} {κ : I → S} : ∀ {t : S} (R : Term Sg.sig (Vars κ) t), (∀ τ ∈ R.ops, dm τ = dm' τ) →
      δ.dfdWith dm R = δ.dfdWith dm' R
  | _, .var _, _ => rfl
  | _, .app τ ts, h => by
    simp only [dfdWith]
    rw [h ⟨_, _, τ⟩ (Or.inl rfl)]
    exact congrArg₂ (· ∪ ·) (congrArg Set.iUnion (funext fun j =>
      dfdWith_congr (ts j) fun τ' hτ' => h τ' (Or.inr (Set.mem_iUnion.mpr ⟨j, hτ'⟩)))) rfl

lemma trSetWith_congr {dm dm' : ∀ τ : Op Sg.sig, Set (EEq Lg.sig (Vars (δ.sortMap ∘ τ.ws.get)))}
    {I : Type} {κ : I → S} (H : Set (EEq Sg.sig (Vars κ)))
    (h : ∀ e ∈ H, ∀ τ ∈ e.ops, dm τ = dm' τ) : δ.trSetWith dm H = δ.trSetWith dm' H := by
  unfold trSetWith trWith
  refine congrArg Set.iUnion (funext fun e => congrArg Set.iUnion (funext fun he => ?_))
  rw [δ.dfdWith_congr e.lhs fun τ hτ => h e he τ (Or.inl hτ),
    δ.dfdWith_congr e.rhs fun τ hτ => h e he τ (Or.inr hτ)]

lemma domStep_congr (σ : Op Sg.sig)
    {dm dm' : ∀ τ : Op Sg.sig, Set (EEq Lg.sig (Vars (δ.sortMap ∘ τ.ws.get)))}
    (h : ∀ τ, Sg.Prec τ σ → dm τ = dm' τ) : δ.domStep σ dm = δ.domStep σ dm' := by
  unfold domStep
  rw [δ.trSetWith_congr _ fun e he τ hτ => h τ ⟨e, he, hτ⟩]
```

:::definition (label := "gen-ep-domains") (central := false) (title := "Domains, definedness conditions and translations")
Let $`\mathbf{d} = (\varphi, D, d)` be a generalized ep-derivor from $`\mathbf{\Sigma}` to
$`\mathbf{\Lambda}`. By recursion along $`\lhd`, the *domain of* $`\sigma` *along*
$`\mathbf{d}`, $`\mathrm{Dom}_{\mathbf{d}}(\sigma)`, for $`\sigma \in \Sigma_{\mathbf{s}, s}`, the
*definedness conditions* $`\mathrm{dfd}_{\mathbf{d}}(R)` of a term $`R`, and the *translations*
of the existence equations are defined as follows:

1. $`\mathrm{dfd}_{\mathbf{d}}(i) = \varnothing` for a variable, and
   $`\mathrm{dfd}_{\mathbf{d}}(\tau((R_j)_j)) = \bigcup_j \mathrm{dfd}_{\mathbf{d}}(R_j) \cup (d^{\sharp}(R_j))^{\sharp}_j[\mathrm{Dom}_{\mathbf{d}}(\tau)]`;
2. $`\mathrm{tr}_{\mathbf{d}}(P, Q) = \{(d^{\sharp}(P), d^{\sharp}(Q))\} \cup \mathrm{dfd}_{\mathbf{d}}(P) \cup \mathrm{dfd}_{\mathbf{d}}(Q)`,
   and $`\mathrm{tr}_{\mathbf{d}}[\mathcal{H}]` is the union of the translations of the equations
   of $`\mathcal{H}`;
3. $`\mathrm{Dom}_{\mathbf{d}}(\sigma) = D_{\mathbf{s}} \cup \mathrm{tr}_{\mathbf{d}}[\mathrm{def}^{\mathbf{\Sigma}}(\sigma)] \cup \{(d(\sigma), d(\sigma))\} \cup d(\sigma)^{\sharp}[D_s]`.

The four parts of $`\mathrm{Dom}_{\mathbf{d}}(\sigma)` state that the arguments are in the domains
of their sorts, that the domain conditions of $`\sigma` hold in the derived algebra, that
$`d(\sigma)` is defined, and that its value is in the domain of $`s`.

```lean
open Classical in
/-- The domains `Dom_𝐝(σ)`, by recursion along `◁`. -/
noncomputable def opDom : ∀ σ : Op Sg.sig, Set (EEq Lg.sig (Vars (δ.sortMap ∘ σ.ws.get))) :=
  Sg.wf.fix fun σ IH => δ.domStep σ fun τ => if h : Sg.Prec τ σ then IH τ h else ∅

/-- The definedness conditions `dfd_𝐝(R)`. -/
noncomputable def dfd {I : Type} {κ : I → S} {t : S} (R : Term Sg.sig (Vars κ) t) :
    Set (EEq Lg.sig (Vars (δ.sortMap ∘ κ))) :=
  δ.dfdWith δ.opDom R

/-- The translation `tr_𝐝(P, Q)`. -/
noncomputable def tr {I : Type} {κ : I → S} (e : EEq Sg.sig (Vars κ)) :
    Set (EEq Lg.sig (Vars (δ.sortMap ∘ κ))) :=
  δ.trWith δ.opDom e

/-- The translation `tr_𝐝[ℋ]`. -/
noncomputable def trSet {I : Type} {κ : I → S} (H : Set (EEq Sg.sig (Vars κ))) :
    Set (EEq Lg.sig (Vars (δ.sortMap ∘ κ))) :=
  δ.trSetWith δ.opDom H

theorem opDom_eq (σ : Op Sg.sig) : δ.opDom σ = δ.domStep σ δ.opDom := by
  unfold opDom
  rw [WellFounded.fix_eq]
  apply domStep_congr
  intro τ h
  simp only [dif_pos h]
```
:::

:::proof (of := "gen-ep-domains")
The recursion is well-founded because the operation symbols that occur in
$`\mathrm{def}^{\mathbf{\Sigma}}(\sigma)` precede $`\sigma` in $`\lhd`: the definedness
conditions of a term only depend on the domains of the operation symbols that occur in it, so the
step that defines $`\mathrm{Dom}_{\mathbf{d}}(\sigma)` only uses the domains of the symbols that
precede $`\sigma`.
:::

```lean
lemma holdsAll_opDom_iff {B : PartialAlgebra.{u', v', w} Lg.sig} {ws : List S} {s : S}
    (σ : Sg.sig ws s) (b : ∀ j, B (δ.sortMap (ws.get j))) :
    EEq.HoldsAll B (famVal b) (δ.opDom ⟨ws, s, σ⟩) ↔
      EEq.HoldsAll B (famVal b) (δ.famDom ws.get) ∧
        EEq.HoldsAll B (famVal b) (δ.trSet (Sg.defn σ)) ∧
        ∃ h : ((δ.op σ).eval B (famVal b)).Dom,
          EEq.HoldsAll B (val₁ (((δ.op σ).eval B (famVal b)).get h)) (δ.sortDom s) := by
  rw [δ.opDom_eq]
  simp only [domStep, EEq.holdsAll_union, EEq.holdsAll_singleton, EEq.holdsAll_substSet]
  have hv : ∀ h : ((δ.op σ).eval B (famVal b)).Dom,
      (fun t x => (δ.resultSubst ⟨ws, s, σ⟩ t x).eval B (famVal b)) =
        val₁ (((δ.op σ).eval B (famVal b)).get h) :=
    fun h => eq_val₁ (Part.some_get h).symm
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, ⟨hd, -, -⟩⟩, h4⟩
    exact ⟨h1, h2, hd, by rw [← hv hd]; exact h4⟩
  · rintro ⟨h1, h2, hd, h4⟩
    exact ⟨⟨⟨h1, h2⟩, ⟨hd, hd, rfl⟩⟩, by rw [hv hd]; exact h4⟩
```

# The derived algebra

:::definition (label := "gen-ep-derived") (central := false) (title := "The derived partial algebra")
Let $`\mathbf{d} = (\varphi, D, d)` be a generalized ep-derivor from $`\mathbf{\Sigma}` to
$`\mathbf{\Lambda}` and $`\mathbf{B} = (B, G)` a partial $`\Lambda`-algebra.
$`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})` is the partial $`\Sigma`-algebra
$`(B_{(\varphi, D)}, G^{\mathbf{d}})` in which $`G^{\mathbf{d}}_\sigma` is defined at the families
$`\mathbf{b}` with $`\mathbf{B} \models \mathrm{Dom}_{\mathbf{d}}(\sigma)[\mathbf{b}]` and sends
$`\mathbf{b}` to $`d(\sigma)^{\mathbf{B}}[\mathbf{b}]`.

This is a partial $`\Sigma`-algebra: if $`\mathbf{B} \models \mathrm{Dom}_{\mathbf{d}}(\sigma)[\mathbf{b}]`,
then $`d(\sigma)^{\mathbf{B}}[\mathbf{b}]` is defined and, by Proposition `subst-eval`,
$`\mathbf{B} \models D_s[d(\sigma)^{\mathbf{B}}[\mathbf{b}]]`.

```lean
variable {B : PartialAlgebra.{u', v', w} Lg.sig}

lemma op_dom_of_holds {ws : List S} {s : S} {σ : Sg.sig ws s} {b : ∀ j, B (δ.sortMap (ws.get j))}
    (h : EEq.HoldsAll B (famVal b) (δ.opDom ⟨ws, s, σ⟩)) : ((δ.op σ).eval B (famVal b)).Dom := by
  obtain ⟨-, -, hd, -⟩ := (δ.holdsAll_opDom_iff σ b).mp h
  exact hd

lemma op_mem_of_holds {ws : List S} {s : S} {σ : Sg.sig ws s} {b : ∀ j, B (δ.sortMap (ws.get j))}
    (h : EEq.HoldsAll B (famVal b) (δ.opDom ⟨ws, s, σ⟩)) :
    EEq.HoldsAll B (val₁ (((δ.op σ).eval B (famVal b)).get (δ.op_dom_of_holds h))) (δ.sortDom s) := by
  obtain ⟨-, -, hd, h4⟩ := (δ.holdsAll_opDom_iff σ b).mp h
  exact h4

/-- The derived partial algebra `𝐝*_𝔤𝔡(𝐁)`. -/
noncomputable def derived (B : PartialAlgebra.{u', v', w} Lg.sig) : PartialAlgebra.{u, v, w} Sg.sig where
  carrier := δ.cells B
  op {ws s} σ a :=
    ⟨EEq.HoldsAll B (famVal fun j => (a j).1) (δ.opDom ⟨ws, s, σ⟩), fun h =>
      ⟨((δ.op σ).eval B (famVal fun j => (a j).1)).get (δ.op_dom_of_holds h),
        δ.op_mem_of_holds h⟩⟩
```
:::

```lean
theorem eval_derived {I : Type} {κ : I → S} (b : ∀ i, δ.derived B (κ i)) :
    ∀ {t : S} (R : Term Sg.sig (Vars κ) t),
      ((R.eval (δ.derived B) (famVal b)).Dom ↔
        EEq.HoldsAll B (famVal fun i => (b i).1) (δ.dfd R)) ∧
      ∀ c, R.eval (δ.derived B) (famVal b) = Part.some c →
        (δ.toDerivor.lift R).eval B (famVal fun i => (b i).1) = Part.some c.1
  | _, .var x => by
    obtain ⟨i, rfl⟩ := x
    refine ⟨⟨fun _ => EEq.holdsAll_empty, fun _ => trivial⟩, fun c hc => ?_⟩
    have : b i = c := Part.some_inj.mp hc
    subst this
    rfl
  | _, .app τ ts => by
    have ih := fun j => eval_derived b (ts j)
    have hdfd : δ.dfd (Term.app τ ts) = (⋃ j, δ.dfd (ts j)) ∪
        EEq.substSet (famSubst fun j => δ.toDerivor.lift (ts j)) (δ.opDom ⟨_, _, τ⟩) := rfl
    have hlift : δ.toDerivor.lift (Term.app τ ts) =
        (δ.op τ).subst (famSubst fun j => δ.toDerivor.lift (ts j)) := rfl
    have hval : ∀ a : Arity (δ.derived B) _,
        (∀ j, (ts j).eval (δ.derived B) (famVal b) = Part.some (a j)) →
        (fun s x => (famSubst (fun j => δ.toDerivor.lift (ts j)) s x).eval B
          (famVal fun i => (b i).1)) = famVal fun j => (a j).1 :=
      fun a ha => famSubst_eval fun j => (ih j).2 (a j) (ha j)
    refine ⟨⟨fun hD => ?_, fun hH => ?_⟩, fun c hc => ?_⟩
    · obtain ⟨a, ha, hA⟩ := Term.eval_app_dom _ _ τ hD
      have hop : ((δ.derived B).op τ a).Dom := hA ▸ hD
      rw [hdfd, EEq.holdsAll_union, EEq.holdsAll_iUnion]
      erw [EEq.holdsAll_substSet, hval a ha]
      exact ⟨fun j => (ih j).1.mp (by rw [ha j]; trivial), hop⟩
    · rw [hdfd, EEq.holdsAll_union, EEq.holdsAll_iUnion] at hH
      obtain ⟨hj, hsub⟩ := hH
      have hd : ∀ j, ((ts j).eval (δ.derived B) (famVal b)).Dom := fun j => (ih j).1.mpr (hj j)
      let a : Arity (δ.derived B) _ := fun j => ((ts j).eval (δ.derived B) (famVal b)).get (hd j)
      have ha : ∀ j, (ts j).eval (δ.derived B) (famVal b) = Part.some (a j) :=
        fun j => (Part.some_get _).symm
      erw [EEq.holdsAll_substSet, hval a ha] at hsub
      rw [Term.eval_app_of_eq_some _ _ τ ha]
      exact hsub
    · have hD : ((Term.app τ ts).eval (δ.derived B) (famVal b)).Dom := by rw [hc]; trivial
      obtain ⟨a, ha, hA⟩ := Term.eval_app_dom _ _ τ hD
      rw [hlift]
      erw [Term.eval_subst, hval a ha]
      rw [hA] at hc
      obtain ⟨hop, rfl⟩ := Part.eq_some_iff.mp hc
      exact (Part.some_get _).symm
```

:::Stemma.lemma (label := "gen-ep-translation") (central := false) (title := "Values in the derived algebra")
Let $`\mathbf{d}` be a generalized ep-derivor from $`\mathbf{\Sigma}` to $`\mathbf{\Lambda}`,
$`\mathbf{B}` a partial $`\Lambda`-algebra and $`\mathbf{b}` a family in
$`(B_{(\varphi, D)})_{\kappa}`. For every term $`R` with variables in $`\downarrow\kappa`,
$`R^{\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})}[\mathbf{b}]` is defined if and only if
$`\mathbf{B} \models \mathrm{dfd}_{\mathbf{d}}(R)[\mathbf{b}]`, and then it is
$`d^{\sharp}(R)^{\mathbf{B}}[\mathbf{b}]`. Consequently, for every set $`\mathcal{H}` of
existence equations, $`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B}) \models \mathcal{H}[\mathbf{b}]`
if and only if $`\mathbf{B} \models \mathrm{tr}_{\mathbf{d}}[\mathcal{H}][\mathbf{b}]`.

```lean
theorem eval_derived_dom_iff {I : Type} {κ : I → S} (b : ∀ i, δ.derived B (κ i)) {t : S}
    (R : Term Sg.sig (Vars κ) t) :
    (R.eval (δ.derived B) (famVal b)).Dom ↔ EEq.HoldsAll B (famVal fun i => (b i).1) (δ.dfd R) :=
  (δ.eval_derived b R).1

theorem eval_derived_get {I : Type} {κ : I → S} (b : ∀ i, δ.derived B (κ i)) {t : S}
    (R : Term Sg.sig (Vars κ) t) (h : (R.eval (δ.derived B) (famVal b)).Dom) :
    (δ.toDerivor.lift R).eval B (famVal fun i => (b i).1) =
      Part.some ((R.eval (δ.derived B) (famVal b)).get h).1 :=
  (δ.eval_derived b R).2 _ (Part.some_get h).symm

theorem holdsAll_derived_iff {I : Type} {κ : I → S} (b : ∀ i, δ.derived B (κ i))
    (H : Set (EEq Sg.sig (Vars κ))) :
    EEq.HoldsAll (δ.derived B) (famVal b) H ↔ EEq.HoldsAll B (famVal fun i => (b i).1) (δ.trSet H) := by
  have hg : ∀ {t : S} (R : Term Sg.sig (Vars κ) t) (h : (R.eval (δ.derived B) (famVal b)).Dom)
      (g : ((δ.toDerivor.lift R).eval B (famVal fun i => (b i).1)).Dom),
      ((δ.toDerivor.lift R).eval B (famVal fun i => (b i).1)).get g =
        ((R.eval (δ.derived B) (famVal b)).get h).1 :=
    fun R h g => Part.get_eq_of_mem (by rw [δ.eval_derived_get b R h]; exact Part.mem_some _) g
  unfold trSet trSetWith
  rw [EEq.holdsAll_biUnion]
  refine forall₂_congr fun e _ => ?_
  rw [trWith, EEq.holdsAll_insert, EEq.holdsAll_union]
  constructor
  · rintro ⟨h1, h2, heq⟩
    have e1 := δ.eval_derived_get b e.lhs h1
    have e2 := δ.eval_derived_get b e.rhs h2
    refine ⟨⟨?_, ?_, ?_⟩,
      (δ.eval_derived_dom_iff b e.lhs).mp h1, (δ.eval_derived_dom_iff b e.rhs).mp h2⟩
    · show ((δ.toDerivor.lift e.lhs).eval B (famVal fun i => (b i).1)).Dom
      rw [e1]; trivial
    · show ((δ.toDerivor.lift e.rhs).eval B (famVal fun i => (b i).1)).Dom
      rw [e2]; trivial
    · show ((δ.toDerivor.lift e.lhs).eval B (famVal fun i => (b i).1)).get _ =
        ((δ.toDerivor.lift e.rhs).eval B (famVal fun i => (b i).1)).get _
      exact (hg e.lhs h1 _).trans ((congrArg Subtype.val heq).trans (hg e.rhs h2 _).symm)
  · rintro ⟨⟨g1, g2, heq⟩, d1, d2⟩
    have h1 := (δ.eval_derived_dom_iff b e.lhs).mpr d1
    have h2 := (δ.eval_derived_dom_iff b e.rhs).mpr d2
    have heq' : ((δ.toDerivor.lift e.lhs).eval B (famVal fun i => (b i).1)).get g1 =
        ((δ.toDerivor.lift e.rhs).eval B (famVal fun i => (b i).1)).get g2 := heq
    exact ⟨h1, h2, Subtype.ext ((hg e.lhs h1 g1).symm.trans (heq'.trans (hg e.rhs h2 g2)))⟩
```
:::

:::proof (of := "gen-ep-translation")
By induction on $`R`. For a variable, both values are $`b_i`. Let $`R = \sigma((R_j)_j)`; by
(H2), $`d^{\sharp}(R) = (d^{\sharp}(R_j))^{\sharp}_j(d(\sigma))`. The term $`R` is defined in
$`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})` if and only if every $`R_j` is defined, i.e., by the
induction hypothesis, $`\mathbf{B} \models \mathrm{dfd}_{\mathbf{d}}(R_j)[\mathbf{b}]`, and the
family $`\mathbf{c}` of their values $`c_j = d^{\sharp}(R_j)^{\mathbf{B}}[\mathbf{b}]` satisfies
$`\mathrm{Dom}_{\mathbf{d}}(\sigma)`. By Proposition `subst-eval`, the latter holds if and only if
$`\mathbf{B} \models (d^{\sharp}(R_j))^{\sharp}_j[\mathrm{Dom}_{\mathbf{d}}(\sigma)][\mathbf{b}]`, and,
again by Proposition `subst-eval`, the value $`d(\sigma)^{\mathbf{B}}[\mathbf{c}]` is
$`d^{\sharp}(R)^{\mathbf{B}}[\mathbf{b}]`. An existence equation holds in
$`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})` if and only if both members are defined and their
values, the values of their translations in $`\mathbf{B}`, are equal.
:::

:::proposition (label := "gen-ep-domain-def") (central := false) (title := "The domains in the derived algebra")
A family $`\mathbf{b} \in (B_{(\varphi, D)})_{\mathbf{s}}` is in the domain of $`\sigma` in
$`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})` if and only if
$`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B}) \models \mathrm{def}^{\mathbf{\Sigma}}(\sigma)[\mathbf{b}]`,
$`d(\sigma)^{\mathbf{B}}[\mathbf{b}]` is defined and it is in $`(B_{(\varphi, D)})_s`.
Consequently, $`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})` is a $`\mathbf{\Sigma}`-algebra if and
only if, for every $`\sigma` and every $`\mathbf{b}` such that
$`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B}) \models \mathrm{def}^{\mathbf{\Sigma}}(\sigma)[\mathbf{b}]`,
$`d(\sigma)^{\mathbf{B}}[\mathbf{b}]` is defined and is in $`(B_{(\varphi, D)})_s`.

```lean
theorem op_derived_dom_iff {ws : List S} {s : S} (σ : Sg.sig ws s) (a : Arity (δ.derived B) ws) :
    ((δ.derived B).op σ a).Dom ↔ EEq.HoldsAll (δ.derived B) (famVal a) (Sg.defn σ) ∧
      ∃ h : ((δ.op σ).eval B (famVal fun j => (a j).1)).Dom,
        EEq.HoldsAll B (val₁ (((δ.op σ).eval B (famVal fun j => (a j).1)).get h)) (δ.sortDom s) := by
  change EEq.HoldsAll B (famVal fun j => (a j).1) (δ.opDom ⟨ws, s, σ⟩) ↔ _
  rw [δ.holdsAll_opDom_iff σ, ← δ.holdsAll_derived_iff a]
  have hfam : EEq.HoldsAll B (famVal fun j => (a j).1) (δ.famDom ws.get) :=
    (δ.holdsAll_famDom_iff _).mpr fun j => (a j).2
  exact ⟨fun ⟨_, h2, h3⟩ => ⟨h2, h3⟩, fun ⟨h2, h3⟩ => ⟨hfam, h2, h3⟩⟩

theorem derived_isAlgebra_iff : Sg.IsAlgebra (δ.derived B) ↔
    ∀ {ws : List S} {s : S} (σ : Sg.sig ws s) (a : Arity (δ.derived B) ws),
      EEq.HoldsAll (δ.derived B) (famVal a) (Sg.defn σ) →
        ∃ h : ((δ.op σ).eval B (famVal fun j => (a j).1)).Dom,
          EEq.HoldsAll B (val₁ (((δ.op σ).eval B (famVal fun j => (a j).1)).get h))
            (δ.sortDom s) := by
  constructor
  · intro h ws s σ a hdef
    exact ((δ.op_derived_dom_iff σ a).mp ((h σ a).mpr hdef)).2
  · intro h ws s σ a
    rw [δ.op_derived_dom_iff σ a]
    exact ⟨fun h' => h'.1, fun hdef => ⟨hdef, h σ a hdef⟩⟩
```
:::

:::proof (of := "gen-ep-domain-def")
By Lemma `gen-ep-translation`, $`\mathbf{B} \models \mathrm{tr}_{\mathbf{d}}[\mathrm{def}^{\mathbf{\Sigma}}(\sigma)][\mathbf{b}]`
if and only if $`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B}) \models \mathrm{def}^{\mathbf{\Sigma}}(\sigma)[\mathbf{b}]`,
and, by Proposition `subst-eval`, if $`d(\sigma)^{\mathbf{B}}[\mathbf{b}]` is defined,
$`\mathbf{B} \models d(\sigma)^{\sharp}[D_s][\mathbf{b}]` if and only if its value is in
$`(B_{(\varphi, D)})_s`; the family itself satisfies $`D_{\mathbf{s}}` by Proposition
`gen-ep-delta`. The first statement follows from the definition of
$`\mathrm{Dom}_{\mathbf{d}}(\sigma)`, and the second one from the first.
:::

:::proposition (label := "gen-ep-functor") (central := false) (title := "The functor of a generalized ep-derivor")
Let $`\mathbf{d}` be a generalized ep-derivor from $`\mathbf{\Sigma}` to $`\mathbf{\Lambda}`.
There is a functor $`\mathbf{d}^{\ast}_{\mathfrak{gd}}` from $`\mathsf{PAlg}(\Lambda)` to
$`\mathsf{PAlg}(\Sigma)` that sends $`\mathbf{B}` to $`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})`
and a homomorphism $`f` to $`\Delta_{(\varphi, D)}(f)`, and its composite with the forgetful functor
$`\mathsf{PAlg}(\Sigma) \to \mathsf{Set}^{S}` is $`\Delta_{(\varphi, D)}`.

```lean
/-- `Δ_(φ,D)(f)`, as a homomorphism of derived algebras. -/
noncomputable def derivedMap {B B' : PartialAlgebra.{u', v', w} Lg.sig} (f : B ⟶ B') :
    δ.derived B ⟶ δ.derived B' where
  map s b := ⟨f.map _ b.1, δ.cells_map f b⟩
  map_dom σ a h := by
    have h' := EEq.holdsAll_hom f (famVal fun j => (a j).1) h
    erw [famVal_map] at h'
    exact h'
  map_op σ a h := by
    apply Subtype.ext
    have := Term.eval_hom f (famVal fun j => (a j).1) (δ.op σ) (δ.op_dom_of_holds h)
    erw [famVal_map] at this
    exact (Part.get_eq_of_mem (Part.eq_some_iff.mp this) _).symm

/-- The functor `𝐝*_𝔤𝔡`. -/
noncomputable def derivedFunctor :
    PartialAlgebra.{u', v', w} Lg.sig ⥤ PartialAlgebra.{u, v, w} Sg.sig where
  obj B := δ.derived B
  map f := δ.derivedMap f

theorem derivedFunctor_comp_forget : δ.derivedFunctor ⋙ PartialAlgebra.forget = δ.delta :=
  rfl
```
:::

:::proof (of := "gen-ep-functor")
Let $`f \colon \mathbf{B} \to \mathbf{B}'` and $`\mathbf{b}` in the domain of
$`G^{\mathbf{d}}_\sigma`, i.e., $`\mathbf{B} \models \mathrm{Dom}_{\mathbf{d}}(\sigma)[\mathbf{b}]`. By
Proposition `hom-eval`, $`\mathbf{B}' \models \mathrm{Dom}_{\mathbf{d}}(\sigma)[f \circ \mathbf{b}]`
and $`d(\sigma)^{\mathbf{B}'}[f \circ \mathbf{b}] = f(d(\sigma)^{\mathbf{B}}[\mathbf{b}])`. The rest
follows from Proposition `gen-ep-delta`.
:::

# Closed subsets and congruences

A *closed subset* of a partial algebra is a sorted subset closed under the operations wherever
they are defined, and a *congruence* is a sorted equivalence compatible with the operations
wherever they are defined.

```lean
end GenEpDerivor

/-- `Y` is a closed subset of `𝐀`. -/
def PartialAlgebra.IsClosedSubset {Sig : Signature.{u, v} S} (A : PartialAlgebra.{u, v, w} Sig)
    (Y : ∀ s, Set (A s)) : Prop :=
  ∀ {ws : List S} {s : S} (σ : Sig ws s) (a : Arity A ws), (∀ j, a j ∈ Y _) →
    ∀ h : (A.op σ a).Dom, (A.op σ a).get h ∈ Y s

/-- `Φ` is a congruence on `𝐀`. -/
def PartialAlgebra.IsCongruence {Sig : Signature.{u, v} S} (A : PartialAlgebra.{u, v, w} Sig)
    (Φ : ∀ s, A s → A s → Prop) : Prop :=
  (∀ s, Equivalence (Φ s)) ∧
    ∀ {ws : List S} {s : S} (σ : Sig ws s) (a b : Arity A ws) (ha : (A.op σ a).Dom)
      (hb : (A.op σ b).Dom), (∀ j, Φ _ (a j) (b j)) → Φ s ((A.op σ a).get ha) ((A.op σ b).get hb)

/-- The defined values of a term under a valuation in a closed subset are in it. -/
theorem Term.eval_mem_of_isClosedSubset {Sig : Signature.{u, v} S} {A : PartialAlgebra.{u, v, w} Sig}
    {Y : ∀ s, Set (A s)} (hY : A.IsClosedSubset Y) {X : S → Type} {val : ∀ s, X s → Part (A s)}
    (hv : ∀ s x (h : (val s x).Dom), (val s x).get h ∈ Y s) :
    ∀ {t : S} (R : Term Sig X t) (h : (R.eval A val).Dom), (R.eval A val).get h ∈ Y t
  | _, .var x, h => hv _ x h
  | _, .app σ ts, h => by
    obtain ⟨a, ha, hA⟩ := Term.eval_app_dom A val σ h
    have hd : (A.op σ a).Dom := hA ▸ h
    rw [Part.get_eq_get_of_eq _ _ hA]
    refine hY σ a (fun j => ?_) hd
    have hj := Term.eval_mem_of_isClosedSubset hY hv (ts j) (by rw [ha j]; trivial)
    rwa [Part.get_eq_of_mem (Part.eq_some_iff.mp (ha j))] at hj

/-- The defined values of a term under two related valuations are related by a congruence. -/
theorem Term.eval_rel_of_isCongruence {Sig : Signature.{u, v} S} {A : PartialAlgebra.{u, v, w} Sig}
    {Φ : ∀ s, A s → A s → Prop} (hΦ : A.IsCongruence Φ) {X : S → Type}
    {val val' : ∀ s, X s → Part (A s)}
    (hv : ∀ s x (h : (val s x).Dom) (h' : (val' s x).Dom), Φ s ((val s x).get h) ((val' s x).get h')) :
    ∀ {t : S} (R : Term Sig X t) (h : (R.eval A val).Dom) (h' : (R.eval A val').Dom),
      Φ t ((R.eval A val).get h) ((R.eval A val').get h')
  | _, .var x, h, h' => hv _ x h h'
  | _, .app σ ts, h, h' => by
    obtain ⟨a, ha, hA⟩ := Term.eval_app_dom A val σ h
    obtain ⟨b, hb, hB⟩ := Term.eval_app_dom A val' σ h'
    have hd : (A.op σ a).Dom := hA ▸ h
    have hd' : (A.op σ b).Dom := hB ▸ h'
    rw [Part.get_eq_get_of_eq _ _ hA, Part.get_eq_get_of_eq _ _ hB]
    refine hΦ.2 σ a b hd hd' fun j => ?_
    have hj := Term.eval_rel_of_isCongruence hΦ hv (ts j) (by rw [ha j]; trivial)
      (by rw [hb j]; trivial)
    rwa [Part.get_eq_of_mem (Part.eq_some_iff.mp (ha j)),
      Part.get_eq_of_mem (Part.eq_some_iff.mp (hb j))] at hj

namespace GenEpDerivor

variable {Sg : EpSignature.{u, v} S} {Lg : EpSignature.{u', v'} T} (δ : GenEpDerivor Sg Lg)
  {B : PartialAlgebra.{u', v', w} Lg.sig}
```

:::proposition (label := "gen-ep-closed-congruence") (central := false) (title := "Closed subsets and congruences of derived algebras")
Let $`\mathbf{d}` be a generalized ep-derivor from $`\mathbf{\Sigma}` to $`\mathbf{\Lambda}` and
$`\mathbf{B}` a partial $`\Lambda`-algebra.

1. If $`Y` is a closed subset of $`\mathbf{B}`, then
   $`(Y_{\varphi(s)} \cap (B_{(\varphi, D)})_s)_{s \in S}` is a closed subset of
   $`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})`.
2. If $`\Phi` is a congruence on $`\mathbf{B}`, then
   $`(\Phi_{\varphi(s)} \cap (B_{(\varphi, D)})_s^2)_{s \in S}` is a congruence on
   $`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})`.

```lean
theorem isClosedSubset_derived {Y : ∀ t, Set (B t)} (hY : B.IsClosedSubset Y) :
    (δ.derived B).IsClosedSubset fun s => {b | b.1 ∈ Y (δ.sortMap s)} := by
  intro ws s σ a ha h
  exact Term.eval_mem_of_isClosedSubset hY (fun t x hx => by obtain ⟨j, rfl⟩ := x; exact ha j)
    (δ.op σ) _

theorem isCongruence_derived {Φ : ∀ t, B t → B t → Prop} (hΦ : B.IsCongruence Φ) :
    (δ.derived B).IsCongruence fun s b b' => Φ (δ.sortMap s) b.1 b'.1 := by
  refine ⟨fun s => ⟨fun x => (hΦ.1 _).refl x.1, fun h => (hΦ.1 _).symm h,
    fun h h' => (hΦ.1 _).trans h h'⟩, ?_⟩
  intro ws s σ a b _ _ hab
  exact Term.eval_rel_of_isCongruence hΦ
    (fun t x h h' => by obtain ⟨j, rfl⟩ := x; exact hab j) (δ.op σ) _ _
```
:::

:::proof (of := "gen-ep-closed-congruence")
By induction on terms, the defined values of a term under a valuation in a closed subset are in
it, and the defined values of a term under two $`\Phi`-related valuations are $`\Phi`-related.
The operations of $`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})` are restrictions of the derived
operations $`d(\sigma)^{\mathbf{B}}`.
:::

```lean
end GenEpDerivor
```

# Sending models to models

The draft states the condition on the $`\mathrm{QE}`-equations of the source specification after
renaming their variables to those of a word. A $`\mathrm{QE}`-equation has finitely many
variables; numbering them by a bijection $`e` from $`n = \{0, \ldots, n-1\}` turns it into a
$`\mathrm{QE}`-equation with variables in $`\downarrow\kappa_e`, where $`\kappa_e(i)` is the sort
of the $`i`-th variable.

```lean
/-- Renames the variables of a term, all of which are in `D`. -/
def Term.renameOn {Sig : Signature.{u, v} S} {X Y : S → Type} {D : Set (Σ s, X s)}
    (f : ∀ p ∈ D, Y p.1) : {s : S} → (t : Term Sig X s) → t.vars ⊆ D → Term Sig Y s
  | _, .var x, h => .var (f ⟨_, x⟩ (h rfl))
  | _, .app σ ts, h => .app σ fun j =>
      Term.renameOn f (ts j) fun _ hp => h (Set.mem_iUnion.mpr ⟨j, hp⟩)

namespace QEEq

variable {Sig : Signature.{u, v} S} {V : S → Type} (q : QEEq Sig V) {n : ℕ} (e : Fin n ≃ q.vars)

/-- The sort `κ_e(i)` of the `i`-th variable. -/
def wordSort (i : Fin n) : S := (e i).1.1

/-- The renaming of the variables of `q` along `e`. -/
def renameVar (p : Σ s, V s) (hp : p ∈ q.vars) : Vars (q.wordSort e) p.1 :=
  ⟨e.symm ⟨p, hp⟩, by simp [wordSort]⟩

/-- An existence equation with variables in those of `q`, renamed along `e`. -/
def renameEEq (c : EEq Sig V) (hc : c.vars ⊆ q.vars) : EEq Sig (Vars (q.wordSort e)) :=
  ⟨c.sort, c.lhs.renameOn (q.renameVar e) fun _ hp => hc (Or.inl hp),
    c.rhs.renameOn (q.renameVar e) fun _ hp => hc (Or.inr hp)⟩

/-- The conclusion of `q`, renamed along `e`. -/
def wordConclusion : EEq Sig (Vars (q.wordSort e)) :=
  q.renameEEq e q.conclusion fun _ hp => Or.inl hp

/-- The premises of `q`, renamed along `e`. -/
def wordPremises : Set (EEq Sig (Vars (q.wordSort e))) :=
  {c' | ∃ c, ∃ hc : c ∈ q.premises,
    c' = q.renameEEq e c fun _ hp => Or.inr (Set.mem_iUnion₂_of_mem hc hp)}

open Classical in
lemma Term.eval_renameOn {X Y : S → Type} {D : Set (Σ s, X s)} (f : ∀ p ∈ D, Y p.1)
    {A : PartialAlgebra.{u, v, w} Sig} (val : ∀ s, Y s → Part (A s)) :
    ∀ {t : S} (R : Term Sig X t) (h : R.vars ⊆ D),
      (R.renameOn f h).eval A val =
        R.eval A fun s x => if hx : ⟨s, x⟩ ∈ D then val s (f ⟨s, x⟩ hx) else Part.none
  | _, .var x, h => by simp [Term.renameOn, dif_pos (h rfl)]
  | _, .app σ ts, h => Term.eval_app_congr σ fun j => Term.eval_renameOn f val (ts j) _

lemma Term.vars_finite {X : S → Type} : ∀ {t : S} (R : Term Sig X t), R.vars.Finite
  | _, .var _ => Set.finite_singleton _
  | _, .app _ ts => Set.finite_iUnion fun j => Term.vars_finite (ts j)

lemma vars_finite : q.vars.Finite := by
  refine ((Term.vars_finite q.conclusion.lhs).union (Term.vars_finite q.conclusion.rhs)).union ?_
  refine Set.Finite.subset (Set.Finite.biUnion (List.finite_toSet q.premises) fun c _ =>
    ((Term.vars_finite c.lhs).union (Term.vars_finite c.rhs))) ?_
  intro p hp
  simp only [Set.mem_iUnion] at hp ⊢
  obtain ⟨c, hc, hp⟩ := hp
  exact ⟨c, hc, hp⟩

open Classical in
/-- The valuation of the variables of `q` given by a family indexed by their numbering. -/
noncomputable def wordVal {A : S → Type w} (b : ∀ i, A (q.wordSort e i)) : ∀ s, V s → Part (A s) :=
  fun s x => if hx : ⟨s, x⟩ ∈ q.vars then famVal b s (q.renameVar e ⟨s, x⟩ hx) else Part.none

lemma holds_renameEEq {A : PartialAlgebra.{u, v, w} Sig} (b : ∀ i, A (q.wordSort e i))
    (c : EEq Sig V) (hc : c.vars ⊆ q.vars) :
    (q.renameEEq e c hc).Holds A (famVal b) ↔ c.Holds A (q.wordVal e b) := by
  have h1 := Term.eval_renameOn (q.renameVar e) (famVal b) c.lhs fun _ hp => hc (Or.inl hp)
  have h2 := Term.eval_renameOn (q.renameVar e) (famVal b) c.rhs fun _ hp => hc (Or.inr hp)
  unfold EEq.Holds renameEEq
  dsimp only
  rw [h1, h2]
  rfl

/-- A `QE`-equation holds exactly when its renaming along a numbering of its variables holds
for every family. -/
theorem holds_iff_word (A : PartialAlgebra.{u, v, w} Sig) :
    q.Holds A ↔ ∀ b : ∀ i, A (q.wordSort e i),
      EEq.HoldsAll A (famVal b) (q.wordPremises e) → (q.wordConclusion e).Holds A (famVal b) := by
  constructor
  · intro h b hb
    refine (q.holds_renameEEq e b q.conclusion _).mpr (h _ (fun p hp => ?_) fun c hc => ?_)
    · unfold wordVal; rw [dif_pos hp]; trivial
    · exact (q.holds_renameEEq e b c _).mp (hb _ ⟨c, hc, rfl⟩)
  · intro h val hval hprem
    let b : ∀ i, A (q.wordSort e i) := fun i => (val (e i).1.1 (e i).1.2).get (hval _ (e i).2)
    have hagree : ∀ p ∈ q.vars, q.wordVal e b p.1 p.2 = val p.1 p.2 := by
      intro p hp
      obtain ⟨i, hi⟩ : ∃ i, e i = ⟨p, hp⟩ := ⟨e.symm ⟨p, hp⟩, e.apply_symm_apply _⟩
      have hpi : (e i).1 = p := congrArg Subtype.val hi
      subst hpi
      have hmem : (⟨(e i).1.1, (e i).1.2⟩ : Σ s, V s) ∈ q.vars := (e i).2
      have hr : q.renameVar e ⟨(e i).1.1, (e i).1.2⟩ hmem = ⟨i, rfl⟩ := by
        apply Subtype.ext
        simp [renameVar]
      unfold wordVal
      rw [dif_pos hmem, hr]
      exact Part.some_get _
    have hc : ∀ c : EEq Sig V, c.vars ⊆ q.vars →
        (c.Holds A (q.wordVal e b) ↔ c.Holds A val) := by
      intro c hcv
      have h1 := Term.eval_congr_vars (A := A) c.lhs fun p hp => hagree p (hcv (Or.inl hp))
      have h2 := Term.eval_congr_vars (A := A) c.rhs fun p hp => hagree p (hcv (Or.inr hp))
      simp only [EEq.Holds, h1, h2]
    have := h b fun c' hc' => by
      obtain ⟨c, hcm, rfl⟩ := hc'
      exact (q.holds_renameEEq e b c _).mpr
        ((hc c fun _ hp => Or.inr (Set.mem_iUnion₂_of_mem hcm hp)).mpr (hprem c hcm))
    exact (hc _ fun _ hp => Or.inl hp).mp ((q.holds_renameEEq e b _ _).mp this)

end QEEq
```

:::definition (label := "gen-ep-sends-models") (central := false) (title := "Sending models to models")
Let $`\mathbf{d}` be a generalized ep-derivor from $`\mathbf{\Sigma}` to $`\mathbf{\Lambda}`, and
$`(\mathbf{\Sigma}, \mathcal{E})` and $`(\mathbf{\Lambda}, \mathcal{F})` ep-specifications.
$`\mathbf{d}^{\ast}_{\mathfrak{gd}}` *sends models of* $`(\mathbf{\Lambda}, \mathcal{F})` *to models
of* $`(\mathbf{\Sigma}, \mathcal{E})` if $`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})` is a model of
$`(\mathbf{\Sigma}, \mathcal{E})` for every model $`\mathbf{B}` of $`(\mathbf{\Lambda}, \mathcal{F})`.
In this case $`\mathbf{d}^{\ast}_{\mathfrak{gd}}` birestricts to a functor from
$`\mathsf{epAlg}(\mathbf{\Lambda}, \mathcal{F})` to $`\mathsf{epAlg}(\mathbf{\Sigma}, \mathcal{E})`.

```lean
namespace GenEpDerivor

variable {Sg : EpSignature.{u, v} S} {Lg : EpSignature.{u', v'} T} (δ : GenEpDerivor Sg Lg)
  {V : S → Type} {V' : T → Type}

/-- `𝐝*_𝔤𝔡` sends models of `(𝚲, ℱ)` to models of `(𝚺, ℰ)`. -/
def SendsModels (E : Set (QEEq Sg.sig V)) (F : Set (QEEq Lg.sig V')) : Prop :=
  ∀ B : PartialAlgebra.{u', v', w} Lg.sig, (EpSpec.mk Lg F).IsModel B →
    (EpSpec.mk Sg E).IsModel (δ.derived B)

/-- The birestriction of `𝐝*_𝔤𝔡` to the categories of models. -/
noncomputable def restrict {E : Set (QEEq Sg.sig V)} {F : Set (QEEq Lg.sig V')}
    (h : δ.SendsModels.{u, v, u', v', w} E F) :
    EpSpec.EpAlg.{u', v', w} (EpSpec.mk Lg F) ⥤ EpSpec.EpAlg.{u, v, w} (EpSpec.mk Sg E) where
  obj B := ⟨δ.derived B.1, h B.1 B.2⟩
  map f := δ.derivedMap (B := _) (B' := _) f
  map_id _ := PartialAlgebra.Hom.ext fun _ _ => rfl
  map_comp _ _ := PartialAlgebra.Hom.ext fun _ _ => rfl
```
:::

:::proposition (label := "gen-ep-sends-models-iff") (central := false) (title := "When a generalized ep-derivor sends models to models")
Let $`\mathbf{d} = (\varphi, D, d)` be a generalized ep-derivor from $`\mathbf{\Sigma}` to
$`\mathbf{\Lambda}`, and $`(\mathbf{\Sigma}, \mathcal{E})` and $`(\mathbf{\Lambda}, \mathcal{F})`
ep-specifications. Then $`\mathbf{d}^{\ast}_{\mathfrak{gd}}` sends models of
$`(\mathbf{\Lambda}, \mathcal{F})` to models of $`(\mathbf{\Sigma}, \mathcal{E})` if and only if the
following conditions hold, where $`\mathrm{Cn}` is $`\mathrm{Cn}^{\mathbf{\Lambda}, \mathcal{F}}`:

1. (GEP1) for every $`\sigma \in \Sigma_{\mathbf{s}, s}`, the translated domain conditions of
   $`\sigma` guarantee that $`d(\sigma)` is defined and takes its values in the domain of $`s`:
   $`\{(d(\sigma), d(\sigma))\} \cup d(\sigma)^{\sharp}[D_s] \subseteq \mathrm{Cn}(D_{\mathbf{s}} \cup \mathrm{tr}_{\mathbf{d}}[\mathrm{def}^{\mathbf{\Sigma}}(\sigma)])`;
2. (GEP2) for every $`\mathrm{QE}`-equation $`\bigwedge_{i} e_i \longrightarrow e` of
   $`\mathcal{E}` and every numbering of its variables, with
   $`\kappa` the sorts of the numbered variables,
   $`\mathrm{tr}_{\mathbf{d}}(e) \subseteq \mathrm{Cn}(D_{\kappa} \cup \bigcup_i \mathrm{tr}_{\mathbf{d}}(e_i))`.

More precisely, (GEP1) holds if and only if $`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})` is a
$`\mathbf{\Sigma}`-algebra for every model $`\mathbf{B}` of $`(\mathbf{\Lambda}, \mathcal{F})`, and
(GEP2) holds if and only if every equation of $`\mathcal{E}` holds in
$`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})` for every model $`\mathbf{B}` of
$`(\mathbf{\Lambda}, \mathcal{F})`.

The draft asks (GEP2) after renaming the variables once; asking it for every numbering is
equivalent, by the second part of the statement, and avoids a choice.

```lean
/-- The condition (GEP1). -/
def GEP1 (F : Set (QEEq Lg.sig V')) : Prop :=
  ∀ {ws : List S} {s : S} (σ : Sg.sig ws s),
    insert ⟨_, δ.op σ, δ.op σ⟩ (EEq.substSet (δ.resultSubst ⟨ws, s, σ⟩) (δ.sortDom s)) ⊆
      EpSpec.Cn.{u', v', w} (EpSpec.mk Lg F) (δ.sortMap ∘ ws.get)
        (δ.famDom ws.get ∪ δ.trSet (Sg.defn σ))

/-- The condition (GEP2). -/
def GEP2 (E : Set (QEEq Sg.sig V)) (F : Set (QEEq Lg.sig V')) : Prop :=
  ∀ q ∈ E, ∀ (n : ℕ) (e : Fin n ≃ q.vars),
    δ.tr (q.wordConclusion e) ⊆
      EpSpec.Cn.{u', v', w} (EpSpec.mk Lg F) (δ.sortMap ∘ q.wordSort e)
        (δ.famDom (q.wordSort e) ∪ δ.trSet (q.wordPremises e))

lemma trSet_singleton {I : Type} {κ : I → S} (e : EEq Sg.sig (Vars κ)) : δ.trSet {e} = δ.tr e := by
  simp [trSet, trSetWith, tr]

/-- (GEP2) for one numbering of the variables of one equation. -/
lemma gep2_word_iff {F : Set (QEEq Lg.sig V')} (q : QEEq Sg.sig V) {n : ℕ} (e : Fin n ≃ q.vars) :
    δ.tr (q.wordConclusion e) ⊆
      EpSpec.Cn.{u', v', w} (EpSpec.mk Lg F) (δ.sortMap ∘ q.wordSort e)
        (δ.famDom (q.wordSort e) ∪ δ.trSet (q.wordPremises e)) ↔
    ∀ B : PartialAlgebra.{u', v', w} Lg.sig, (EpSpec.mk Lg F).IsModel B →
      ∀ b : ∀ i, δ.derived B (q.wordSort e i),
        EEq.HoldsAll (δ.derived B) (famVal b) (q.wordPremises e) →
          (q.wordConclusion e).Holds (δ.derived B) (famVal b) := by
  constructor
  · intro h B hB b hb
    have hfam : EEq.HoldsAll B (famVal fun i => (b i).1) (δ.famDom (q.wordSort e)) :=
      (δ.holdsAll_famDom_iff _).mpr fun i => (b i).2
    have htr := (δ.holdsAll_derived_iff b _).mp hb
    have hconc : EEq.HoldsAll B (famVal fun i => (b i).1) (δ.trSet {q.wordConclusion e}) := by
      rw [trSet_singleton]
      exact fun c hc => (EpSpec.mem_cn_iff _ _).mp (h hc) B hB _ (EEq.holdsAll_union.mpr ⟨hfam, htr⟩)
    exact EEq.holdsAll_singleton.mp ((δ.holdsAll_derived_iff b _).mpr hconc)
  · intro h c hc
    refine (EpSpec.mem_cn_iff _ _).mpr fun B hB a ha => ?_
    obtain ⟨hfam, htr⟩ := EEq.holdsAll_union.mp ha
    have hcells := (δ.holdsAll_famDom_iff a).mp hfam
    let b : ∀ i, δ.derived B (q.wordSort e i) := fun i => ⟨a i, hcells i⟩
    have hb : EEq.HoldsAll (δ.derived B) (famVal b) (q.wordPremises e) :=
      (δ.holdsAll_derived_iff b _).mpr htr
    have hconc := (δ.holdsAll_derived_iff b {q.wordConclusion e}).mp
      (EEq.holdsAll_singleton.mpr (h B hB b hb))
    rw [trSet_singleton] at hconc
    exact hconc c hc

theorem gep1_iff {F : Set (QEEq Lg.sig V')} :
    δ.GEP1.{u, v, u', v', w} F ↔ ∀ B : PartialAlgebra.{u', v', w} Lg.sig,
      (EpSpec.mk Lg F).IsModel B → Sg.IsAlgebra (δ.derived B) := by
  constructor
  · intro h B hB
    rw [derived_isAlgebra_iff]
    intro ws s σ a hdef
    have hfam : EEq.HoldsAll B (famVal fun j => (a j).1) (δ.famDom ws.get) :=
      (δ.holdsAll_famDom_iff _).mpr fun j => (a j).2
    have htr := (δ.holdsAll_derived_iff a _).mp hdef
    have hall : EEq.HoldsAll B (famVal fun j => (a j).1)
        (insert ⟨_, δ.op σ, δ.op σ⟩ (EEq.substSet (δ.resultSubst ⟨ws, s, σ⟩) (δ.sortDom s))) :=
      fun c hc => (EpSpec.mem_cn_iff _ _).mp (h σ hc) B hB _ (EEq.holdsAll_union.mpr ⟨hfam, htr⟩)
    obtain ⟨⟨hd, -, -⟩, hD⟩ := EEq.holdsAll_insert.mp hall
    refine ⟨hd, ?_⟩
    have hv : (fun t x => (δ.resultSubst ⟨ws, s, σ⟩ t x).eval B (famVal fun j => (a j).1)) =
        val₁ (((δ.op σ).eval B (famVal fun j => (a j).1)).get hd) :=
      eq_val₁ (Part.some_get hd).symm
    erw [EEq.holdsAll_substSet, hv] at hD
    exact hD
  · intro h ws s σ c hc
    refine (EpSpec.mem_cn_iff _ _).mpr fun B hB a ha => ?_
    obtain ⟨hfam, htr⟩ := EEq.holdsAll_union.mp ha
    have hcells := (δ.holdsAll_famDom_iff a).mp hfam
    let b : Arity (δ.derived B) ws := fun j => ⟨a j, hcells j⟩
    have hdef : EEq.HoldsAll (δ.derived B) (famVal b) (Sg.defn σ) :=
      (δ.holdsAll_derived_iff b _).mpr htr
    obtain ⟨hd, hD⟩ := (δ.derived_isAlgebra_iff.mp (h B hB)) σ b hdef
    have hv : (fun t x => (δ.resultSubst ⟨ws, s, σ⟩ t x).eval B (famVal a)) =
        val₁ (((δ.op σ).eval B (famVal a)).get hd) :=
      eq_val₁ (Part.some_get hd).symm
    rcases hc with rfl | hc
    · exact ⟨hd, hd, rfl⟩
    · have hsub : EEq.HoldsAll B (famVal a)
          (EEq.substSet (δ.resultSubst ⟨ws, s, σ⟩) (δ.sortDom s)) := by
        erw [EEq.holdsAll_substSet, hv]
        exact hD
      exact hsub c hc

theorem gep2_iff {E : Set (QEEq Sg.sig V)} {F : Set (QEEq Lg.sig V')} :
    δ.GEP2.{u, v, u', v', w} E F ↔ ∀ B : PartialAlgebra.{u', v', w} Lg.sig,
      (EpSpec.mk Lg F).IsModel B → ∀ q ∈ E, q.Holds (δ.derived B) := by
  constructor
  · intro h B hB q hq
    letI := q.vars_finite.fintype
    let e := (Fintype.equivFin q.vars).symm
    exact (q.holds_iff_word e _).mpr ((δ.gep2_word_iff q e).mp (h q hq _ e) B hB)
  · intro h q hq n e
    exact (δ.gep2_word_iff q e).mpr fun B hB => (q.holds_iff_word e _).mp (h B hB q hq)

theorem sendsModels_iff {E : Set (QEEq Sg.sig V)} {F : Set (QEEq Lg.sig V')} :
    δ.SendsModels.{u, v, u', v', w} E F ↔ δ.GEP1.{u, v, u', v', w} F ∧ δ.GEP2.{u, v, u', v', w} E F := by
  constructor
  · intro h
    exact ⟨δ.gep1_iff.mpr fun B hB => (h B hB).1, δ.gep2_iff.mpr fun B hB => (h B hB).2⟩
  · rintro ⟨h1, h2⟩ B hB
    exact ⟨δ.gep1_iff.mp h1 B hB, δ.gep2_iff.mp h2 B hB⟩

end GenEpDerivor
```
:::

:::proof (of := "gen-ep-sends-models-iff")
Let $`\mathbf{B}` be a model of $`(\mathbf{\Lambda}, \mathcal{F})`. The families $`\mathbf{b}` with
$`\mathbf{B} \models D_{\kappa}[\mathbf{b}]` are, by Proposition `gen-ep-delta`, the families of
cells of $`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})`. For such a family, by Lemma
`gen-ep-translation`, $`\mathbf{B} \models \mathrm{tr}_{\mathbf{d}}[\mathrm{def}^{\mathbf{\Sigma}}(\sigma)][\mathbf{b}]`
if and only if $`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B}) \models \mathrm{def}^{\mathbf{\Sigma}}(\sigma)[\mathbf{b}]`,
and, by Proposition `subst-eval`,
$`\mathbf{B} \models \{(d(\sigma), d(\sigma))\} \cup d(\sigma)^{\sharp}[D_s][\mathbf{b}]` if and only if
$`d(\sigma)^{\mathbf{B}}[\mathbf{b}]` is defined and is a cell of sort $`s`. Hence (GEP1) states the
condition of Proposition `gen-ep-domain-def` for every model. Similarly, by Lemma
`gen-ep-translation`, (GEP2) states that, for every model $`\mathbf{B}` and every family of cells
of $`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})`, if the renamed premises hold, so does the renamed
conclusion; and a valuation of the variables of a $`\mathrm{QE}`-equation is the same as a family
indexed by their numbering.
:::

:::remark (title := "On generalized ep-derivors")
1. The domain of an operation symbol $`\sigma` in $`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})` is
   not part of the data: it is the translation of its domain conditions, which, by (GEP1), are
   only required to guarantee that the derived operation is defined. It may therefore be smaller
   than the domain of $`d(\sigma)^{\mathbf{B}}`, as in the discretization functors. In
   {cite}`Rei87` the morphisms of ep-signatures are required, moreover, to translate the domain
   conditions of $`\sigma` into a set of equations equivalent to the definedness of $`d(\sigma)`.
2. If $`\mathbf{\Sigma}` and $`\mathbf{\Lambda}` are many-sorted signatures, regarded as
   ep-signatures with empty sets of domain conditions, then for every derivor $`(\varphi, d)` the
   generalized ep-derivor $`(\varphi, \varnothing, d)` sends total $`\Lambda`-algebras to
   $`\Sigma`-algebras, in which every $`\sigma` is interpreted as the derived operation
   $`d(\sigma)^{\mathbf{B}}` {cite}`CVST10b`.
3. The functor $`\mathbf{d}^{\ast}_{\mathfrak{gd}}` is defined on all the partial
   $`\Lambda`-algebras, but it may only send the models of some ep-specification to models of
   another one: the domains of the sorts of the graduation derivor, for instance, are only
   preserved by the derived operations in the models of the axioms of $`n`-categories.
:::

```lean
end CategorialAlgebras
```
