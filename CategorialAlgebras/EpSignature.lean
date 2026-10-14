import Stemma
import Mathlib.Order.Closure
import CategorialAlgebras.Derivor

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "ep-signatures and ep-specifications" =>

An *equationally partial signature* (Subsection `SEpSignatures` of the draft, after
{cite}`Rei87`) is a many-sorted signature in which every operation symbol carries a set of
existence equations, its *domain conditions*, that describes where the operation is defined. Its
algebras are the partial algebras in which every operation is defined exactly where its domain
conditions hold. This document defines them, the ep-specifications, and the semantic consequence
operator that the generalized ep-derivors use to compare sets of existence equations.

```lean
universe u v w

namespace CategorialAlgebras

open Signature

variable {S : Type u}
```

# Partial algebras form a category

```lean
namespace PartialAlgebra

variable {Sig : Signature.{u, v} S}

instance category : CategoryTheory.Category.{max u w} (PartialAlgebra.{u, v, w} Sig) where
  Hom A B := Hom A B
  id A := Hom.id A
  comp H K := Hom.comp K H
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] lemma id_map (A : PartialAlgebra.{u, v, w} Sig) (s : S) (x : A s) :
    (CategoryTheory.CategoryStruct.id A : Hom A A).map s x = x := rfl

@[simp] lemma comp_map {A B C : PartialAlgebra.{u, v, w} Sig} (H : A ⟶ B) (K : B ⟶ C) (s : S)
    (x : A s) :
    (CategoryTheory.CategoryStruct.comp H K : Hom A C).map s x = K.map s (H.map s x) := rfl

end PartialAlgebra
```

# Operation symbols occurring in terms

```lean
/-- An operation symbol of `Σ`, together with its rank. -/
structure Op (Sig : Signature.{u, v} S) where
  /-- The arity. -/
  ws : List S
  /-- The sort. -/
  s : S
  /-- The operation symbol. -/
  σ : Sig ws s

variable {Sig : Signature.{u, v} S}

/-- The operation symbols that occur in a term. -/
def Term.ops {X : S → Type} : {t : S} → Term Sig X t → Set (Op Sig)
  | _, .var _ => ∅
  | _, .app σ ts => {⟨_, _, σ⟩} ∪ ⋃ j, (ts j).ops

/-- The operation symbols that occur in an existence equation. -/
def EEq.ops {X : S → Type} (e : EEq Sig X) : Set (Op Sig) := e.lhs.ops ∪ e.rhs.ops
```

# ep-signatures

:::definition (label := "ep-signature") (central := false) (title := "ep-signatures and their algebras")
An *ep-signature* $`\mathbf{\Sigma} = (S, \Sigma, \mathrm{def}^{\mathbf{\Sigma}})` is a many-sorted
signature $`(S, \Sigma)` together with, for every $`\sigma \in \Sigma_{\mathbf{s}, s}`, a set
$`\mathrm{def}^{\mathbf{\Sigma}}(\sigma)` of existence equations with variables in
$`\downarrow\mathbf{s}`, the *domain conditions* of $`\sigma`, such that the relation
$`\tau \lhd \sigma`, "$`\tau` occurs in some equation of $`\mathrm{def}^{\mathbf{\Sigma}}(\sigma)`",
is well-founded.

A partial $`\Sigma`-algebra $`\mathbf{A} = (A, F)` is an *ep-algebra of type* $`\mathbf{\Sigma}`,
or a $`\mathbf{\Sigma}`-*algebra*, if, for every $`\sigma \in \Sigma_{\mathbf{s}, s}`,
$`\mathrm{Dom}(F_\sigma) = A_{\mathrm{def}^{\mathbf{\Sigma}}(\sigma)}`, the set of the families
$`\mathbf{a} \in A_{\mathbf{s}}` with $`\mathbf{A} \models \mathrm{def}^{\mathbf{\Sigma}}(\sigma)[\mathbf{a}]`.
The $`\mathbf{\Sigma}`-algebras form the full subcategory $`\mathsf{epAlg}(\mathbf{\Sigma})` of the
category $`\mathsf{PAlg}(\Sigma)` of partial $`\Sigma`-algebras.

```lean
structure EpSignature (S : Type u) where
  /-- The many-sorted signature. -/
  sig : Signature.{u, v} S
  /-- The domain conditions of each operation symbol. -/
  defn : ∀ {ws : List S} {s : S}, sig ws s → Set (EEq sig (Vars ws.get))
  /-- The relation "occurs in the domain conditions of" is well-founded. -/
  wf : WellFounded fun τ σ : Op sig => ∃ e ∈ defn σ.σ, τ ∈ e.ops

namespace EpSignature

variable (Sg : EpSignature.{u, v} S)

/-- The relation `τ ◁ σ`: `τ` occurs in the domain conditions of `σ`. -/
def Prec (τ σ : Op Sg.sig) : Prop := ∃ e ∈ Sg.defn σ.σ, τ ∈ e.ops

/-- `𝐀` is a `𝚺`-algebra: every operation is defined exactly where its domain conditions
hold. -/
def IsAlgebra (A : PartialAlgebra.{u, v, w} Sg.sig) : Prop :=
  ∀ {ws : List S} {s : S} (σ : Sg.sig ws s) (a : Arity A ws),
    (A.op σ a).Dom ↔ EEq.HoldsAll A (famVal a) (Sg.defn σ)

/-- The category `epAlg(𝚺)`. -/
def EpAlg : Type (max u v (w + 1)) := {A : PartialAlgebra.{u, v, w} Sg.sig // Sg.IsAlgebra A}

instance : CategoryTheory.Category.{max u w} (EpAlg.{u, v, w} Sg) where
  Hom A B := PartialAlgebra.Hom A.1 B.1
  id A := PartialAlgebra.Hom.id A.1
  comp H K := PartialAlgebra.Hom.comp K H

end EpSignature
```
:::

:::definition (label := "ep-signature-of-sig") (central := false) (title := "A signature as an ep-signature")
A many-sorted signature $`(S, \Sigma)` is identified with the ep-signature
$`(S, \Sigma, \varnothing)` in which no operation symbol has domain conditions. Its ep-algebras are
the total $`\Sigma`-algebras.

```lean
/-- The ep-signature `(S, Σ, ∅)`. -/
def EpSignature.ofSig (Sig : Signature.{u, v} S) : EpSignature.{u, v} S where
  sig := Sig
  defn _ := ∅
  wf := ⟨fun _ => ⟨_, fun _ ⟨_, he, _⟩ => he.elim⟩⟩

theorem EpSignature.ofSig_isAlgebra_iff (Sig : Signature.{u, v} S)
    (A : PartialAlgebra.{u, v, w} Sig) :
    (EpSignature.ofSig Sig).IsAlgebra A ↔
      ∀ {ws : List S} {s : S} (σ : Sig ws s) (a : Arity A ws), (A.op σ a).Dom := by
  constructor
  · intro h ws s σ a
    exact (h σ a).mpr fun _ he => he.elim
  · intro h ws s σ a
    exact ⟨fun _ _ he => he.elim, fun _ => h σ a⟩
```
:::

:::proof (of := "ep-signature-of-sig")
The empty set of domain conditions holds for every family.
:::

# ep-specifications

The draft takes the $`\mathrm{QE}`-equations of an ep-specification with variables in a fixed
$`S`-sorted set $`V^{S}`; the library allows any $`S`-sorted set of variables $`V`.

:::definition (label := "ep-specification") (central := false) (title := "ep-specifications and their models")
An *ep-specification* $`(\mathbf{\Sigma}, \mathcal{E})` is an ep-signature together with a set
$`\mathcal{E}` of $`\mathrm{QE}`-equations. Its *models* are the $`\mathbf{\Sigma}`-algebras in which
every equation of $`\mathcal{E}` holds; they form the full subcategory
$`\mathsf{epAlg}(\mathbf{\Sigma}, \mathcal{E})` of $`\mathsf{epAlg}(\mathbf{\Sigma})`.

```lean
/-- An ep-specification `(𝚺, ℰ)`. -/
structure EpSpec (S : Type u) (V : S → Type) where
  /-- The ep-signature. -/
  sg : EpSignature.{u, v} S
  /-- The `QE`-equations. -/
  eqs : Set (QEEq sg.sig V)

namespace EpSpec

variable {V : S → Type} (Sp : EpSpec.{u, v} S V)

/-- `𝐀` is a model of `(𝚺, ℰ)`. -/
def IsModel (A : PartialAlgebra.{u, v, w} Sp.sg.sig) : Prop :=
  Sp.sg.IsAlgebra A ∧ ∀ q ∈ Sp.eqs, q.Holds A

/-- The category `epAlg(𝚺, ℰ)`. -/
def EpAlg : Type (max u v (w + 1)) := {A : PartialAlgebra.{u, v, w} Sp.sg.sig // Sp.IsModel A}

instance : CategoryTheory.Category.{max u w} (EpAlg.{u, v, w} Sp) where
  Hom A B := PartialAlgebra.Hom A.1 B.1
  id A := PartialAlgebra.Hom.id A.1
  comp H K := PartialAlgebra.Hom.comp K H

end EpSpec
```
:::

# The semantic consequence operator

:::definition (label := "ep-consequence") (central := false) (title := "The semantic consequence operator")
Let $`(\mathbf{\Sigma}, \mathcal{E})` be an ep-specification and $`\kappa \colon I \to S`. For a set
$`\mathcal{H}` of existence equations with variables in $`\downarrow\kappa`,
$`\mathrm{Cn}^{\mathbf{\Sigma}, \mathcal{E}}_{\kappa}(\mathcal{H})` is the set of the existence
equations $`e` such that, for every model $`\mathbf{A}` of $`(\mathbf{\Sigma}, \mathcal{E})` and
every family $`\mathbf{a}` with $`\mathbf{A} \models \mathcal{H}[\mathbf{a}]`,
$`\mathbf{A} \models e[\mathbf{a}]`. The set $`\mathcal{H}` is *closed* if
$`\mathrm{Cn}^{\mathbf{\Sigma}, \mathcal{E}}_{\kappa}(\mathcal{H}) = \mathcal{H}`.

The models range over the partial algebras whose sorts are sets of a fixed universe, the
universe `w` of the Lean.

```lean
namespace EpSpec

variable {V : S → Type} (Sp : EpSpec.{u, v} S V) {I : Type} (κ : I → S)

/-- The semantic consequence operator `Cn^{𝚺,ℰ}_κ`. -/
def Cn (H : Set (EEq Sp.sg.sig (Vars κ))) : Set (EEq Sp.sg.sig (Vars κ)) :=
  {e | ∀ A : PartialAlgebra.{u, v, w} Sp.sg.sig, Sp.IsModel A → ∀ a : ∀ i, A (κ i),
    EEq.HoldsAll A (famVal a) H → e.Holds A (famVal a)}

/-- `ℋ` is closed. -/
def IsClosed (H : Set (EEq Sp.sg.sig (Vars κ))) : Prop := Cn.{u, v, w} Sp κ H = H

end EpSpec
```
:::

:::proposition (label := "ep-consequence-closure") (central := false) (title := "Cn is a closure operator")
$`\mathrm{Cn}^{\mathbf{\Sigma}, \mathcal{E}}_{\kappa}` is a closure operator, and
$`\mathcal{H}` and $`\mathrm{Cn}^{\mathbf{\Sigma}, \mathcal{E}}_{\kappa}(\mathcal{H})` hold under the
same families in the models. Consequently,
$`\mathcal{H}' \subseteq \mathrm{Cn}^{\mathbf{\Sigma}, \mathcal{E}}_{\kappa}(\mathcal{H})` if and
only if every family of a model that satisfies $`\mathcal{H}` satisfies $`\mathcal{H}'`, and two
closed sets of existence equations are equal if and only if they hold under the same families in
the models.

```lean
namespace EpSpec

variable {V : S → Type} (Sp : EpSpec.{u, v} S V) {I : Type} (κ : I → S)

/-- `Cn` as a closure operator. -/
def cnClosure : ClosureOperator (Set (EEq Sp.sg.sig (Vars κ))) :=
  ClosureOperator.mk' (Cn.{u, v, w} Sp κ)
    (fun _ _ hHH' _ he A hA a ha => he A hA a fun e' he' => ha e' (hHH' he'))
    (fun _ e he A _ a ha => ha e he)
    (fun _ _ he A hA a ha => he A hA a fun _ he' => he' A hA a ha)

theorem holdsAll_cn_iff {H : Set (EEq Sp.sg.sig (Vars κ))} {A : PartialAlgebra.{u, v, w} Sp.sg.sig}
    (hA : Sp.IsModel A) (a : ∀ i, A (κ i)) :
    EEq.HoldsAll A (famVal a) (Cn.{u, v, w} Sp κ H) ↔ EEq.HoldsAll A (famVal a) H :=
  ⟨fun h e he => h e fun _ _ _ ha => ha e he, fun h _ he => he A hA a h⟩

theorem subset_cn_iff {H H' : Set (EEq Sp.sg.sig (Vars κ))} :
    H' ⊆ Cn.{u, v, w} Sp κ H ↔
      ∀ A : PartialAlgebra.{u, v, w} Sp.sg.sig, Sp.IsModel A → ∀ a : ∀ i, A (κ i),
        EEq.HoldsAll A (famVal a) H → EEq.HoldsAll A (famVal a) H' :=
  ⟨fun h A hA a ha e he => h he A hA a ha, fun h e he A hA a ha => h A hA a ha e he⟩

theorem eq_of_isClosed {H H' : Set (EEq Sp.sg.sig (Vars κ))} (hH : IsClosed.{u, v, w} Sp κ H)
    (hH' : IsClosed.{u, v, w} Sp κ H')
    (h : ∀ A : PartialAlgebra.{u, v, w} Sp.sg.sig, Sp.IsModel A → ∀ a : ∀ i, A (κ i),
      EEq.HoldsAll A (famVal a) H ↔ EEq.HoldsAll A (famVal a) H') :
    H = H' := by
  rw [← hH, ← hH']
  ext e
  exact ⟨fun he A hA a ha => he A hA a ((h A hA a).mpr ha),
    fun he A hA a ha => he A hA a ((h A hA a).mp ha)⟩

end EpSpec
```
:::

:::proof (of := "ep-consequence-closure")
Every equation of $`\mathcal{H}` holds wherever $`\mathcal{H}` does, so
$`\mathcal{H} \subseteq \mathrm{Cn}(\mathcal{H})`; a larger set holds under fewer families, so
$`\mathrm{Cn}` is monotone; and, by definition, $`\mathrm{Cn}(\mathcal{H})` holds wherever
$`\mathcal{H}` does, so it holds under the same families as $`\mathcal{H}`, and
$`\mathrm{Cn}(\mathrm{Cn}(\mathcal{H})) \subseteq \mathrm{Cn}(\mathcal{H})`. The inclusion
$`\mathcal{H}' \subseteq \mathrm{Cn}(\mathcal{H})` says, by definition, that every equation of
$`\mathcal{H}'` holds wherever $`\mathcal{H}` does. If closed sets $`\mathcal{H}` and
$`\mathcal{H}'` hold under the same families, then each is contained in the closure of the other,
which is the other.
:::

```lean
end CategorialAlgebras
```
