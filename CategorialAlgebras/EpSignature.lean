import Stemma
import Mathlib.Order.Closure
import CategorialAlgebras.Derivor

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "ep-signatures and ep-specifications" =>

An *equationally partial signature*, as in Reichel's equationally partial algebras, is a
many-sorted signature in which every operation symbol carries a set of existence equations, its
*domain conditions*: in an algebra of this type, an operation is defined exactly on the families
that satisfy them. This document follows Subsection `SEpSignatures` of the draft: ep-signatures,
their algebras, ep-specifications, and the semantic consequence operator.

```lean
universe u v w

namespace CategorialAlgebras

open Signature

variable {S : Type u}
```

# Operation symbols occurring in a term

```lean
/-- An operation symbol of a signature, together with its rank. -/
abbrev Signature.Symbol (Sig : Signature.{u, v} S) : Type (max u v) :=
  (ws : List S) × (s : S) × Sig ws s
```

:::definition (label := "term.symbols") (central := false) (title := "Operation symbols of a term")
The set of the operation symbols that *occur* in a term is defined by recursion: no symbol
occurs in a variable, and the symbols of $`\sigma((P_j)_j)` are $`\sigma` and those of the
$`P_j`. The symbols of an existence equation are those of its two sides.

```lean
def Term.symbols {Sig : Signature.{u, v} S} {X : S → Type} :
    {s : S} → Term Sig X s → Set Sig.Symbol
  | _, .var _ => ∅
  | _, .app σ ts => insert ⟨_, _, σ⟩ (⋃ j, Term.symbols (ts j))

def EEq.symbols {Sig : Signature.{u, v} S} {X : S → Type} (e : EEq Sig X) : Set Sig.Symbol :=
  e.lhs.symbols ∪ e.rhs.symbols
```
:::

# ep-signatures and their algebras

:::definition (label := "ep-signature") (central := false) (title := "ep-signature")
An *equationally partial signature*, or *ep-signature*, on the set of sorts $`S` is a pair
$`\mathbf{\Sigma} = (\Sigma, \mathrm{def}^{\mathbf{\Sigma}})` where $`\Sigma` is an
$`S`-sorted signature and $`\mathrm{def}^{\mathbf{\Sigma}}` assigns to every
$`\sigma \in \Sigma_{\mathbf{s}, s}` a set
$`\mathrm{def}^{\mathbf{\Sigma}}(\sigma) \subseteq \mathrm{Eq}_{\Sigma}(\downarrow\mathbf{s})` of
existence equations, the *domain conditions* of $`\sigma`, such that the relation $`\lhd` on
the operation symbols, $`\tau \lhd \sigma` if $`\tau` occurs in some equation of
$`\mathrm{def}^{\mathbf{\Sigma}}(\sigma)`, is well-founded (Definition `DEpSignature` of the
draft, where the set of sorts is part of the ep-signature).

```lean
/-- The relation `τ ◁ σ`: `τ` occurs in a domain condition of `σ`. -/
def Signature.DefPrec {Sig : Signature.{u, v} S}
    (defn : ∀ {ws : List S} {s : S}, Sig ws s → Set (EEq Sig (WordVar id ws)))
    (τ σ : Sig.Symbol) : Prop :=
  ∃ e ∈ defn σ.2.2, τ ∈ e.symbols

structure EpSignature (S : Type u) where
  /-- The underlying signature. -/
  sig : Signature.{u, v} S
  /-- The domain conditions of each operation symbol. -/
  defn : ∀ {ws : List S} {s : S}, sig ws s → Set (EEq sig (WordVar id ws))
  /-- The relation `◁` is well-founded. -/
  wf : WellFounded (Signature.DefPrec defn)
```
:::

The well-foundedness of $`\lhd` forbids, in particular, an operation symbol to occur in its own
domain conditions; it is what allows the domains of the operation symbols along a generalized
ep-derivor to be defined by recursion. It holds in all the ep-signatures of the draft, whose
domain conditions only involve operation symbols with no domain conditions.

A family $`\mathbf{a} \in A_{\mathbf{s}}` is a valuation of the variables of
$`\downarrow\mathbf{s}` (see {name}`WordVar`).

```lean
/-- A family `𝐚 ∈ A_𝐬`, as a valuation of `↓𝐬`. -/
abbrev Signature.Arity.val {A : S → Type w} {ws : List S} (a : Arity A ws) :
    ∀ s, WordVar id ws s → A s :=
  WordVar.val (φ := id) (B := A) a
```

:::definition (label := "ep-algebra") (central := false) (title := "ep-algebra")
Let $`\mathbf{\Sigma}` be an ep-signature. A partial $`\Sigma`-algebra $`\mathbf{A} = (A, F)` is
an *ep-algebra of type* $`\mathbf{\Sigma}`, or a $`\mathbf{\Sigma}`-*algebra*, if, for every
$`\sigma \in \Sigma_{\mathbf{s}, s}`, the domain of $`F_\sigma` is the set of the families
$`\mathbf{a} \in A_{\mathbf{s}}` with $`\mathbf{A} \models \mathrm{def}^{\mathbf{\Sigma}}(\sigma)[\mathbf{a}]`.
The domain conditions are evaluated in $`\mathbf{A}` itself, so they may involve its other
partial operations.

```lean
def EpSignature.IsAlgebra (Sg : EpSignature.{u, v} S) (A : PartialAlgebra.{u, v, w} Sg.sig) :
    Prop :=
  ∀ {ws : List S} {s : S} (σ : Sg.sig ws s) (a : Arity A ws),
    (A.op σ a).Dom ↔ EEq.HoldsAll A a.val (Sg.defn σ)
```
:::

:::definition (label := "ep-signature.of-signature") (central := false) (title := "A signature as an ep-signature")
A many-sorted signature $`\Sigma` is identified with the ep-signature $`(\Sigma, \varnothing)`
in which no operation symbol has domain conditions.

```lean
def EpSignature.ofSignature (Sig : Signature.{u, v} S) : EpSignature.{u, v} S where
  sig := Sig
  defn _ := ∅
  wf := ⟨fun _ => ⟨_, fun _ ⟨_, he, _⟩ => he.elim⟩⟩
```
:::

:::proposition (label := "ep-signature.of-signature-algebra") (central := false) (title := "The algebras of a signature")
The ep-algebras of type $`(\Sigma, \varnothing)` are the (total) $`\Sigma`-algebras: the
partial $`\Sigma`-algebras in which every operation is defined everywhere.

```lean
theorem EpSignature.isAlgebra_ofSignature_iff (Sig : Signature.{u, v} S)
    (A : PartialAlgebra.{u, v, w} Sig) :
    (EpSignature.ofSignature Sig).IsAlgebra A ↔
      ∀ {ws : List S} {s : S} (σ : Sig ws s) (a : Arity A ws), (A.op σ a).Dom := by
  constructor
  · intro h ws s σ a
    exact (h σ a).2 fun _ he => he.elim
  · intro h ws s σ a
    exact ⟨fun _ _ he => he.elim, fun _ => h σ a⟩
```
:::

:::proof (of := "ep-signature.of-signature-algebra")
With no domain conditions, every family satisfies them, so an ep-algebra of type
$`(\Sigma, \varnothing)` has all its operations defined everywhere, and conversely.
:::

# ep-specifications and their models

:::definition (label := "ep-specification") (central := false) (title := "ep-specification")
An *ep-specification* is a pair $`(\mathbf{\Sigma}, \mathcal{E})` of an ep-signature
$`\mathbf{\Sigma}` and a set $`\mathcal{E}` of $`\mathrm{QE}`$-equations of $`\Sigma`. Its
*models* are the $`\mathbf{\Sigma}`-algebras in which every equation of $`\mathcal{E}` holds;
with the homomorphisms of partial algebras they form the category
$`\mathsf{epAlg}(\mathbf{\Sigma}, \mathcal{E})`, a full subcategory of $`\mathsf{PAlg}(\Sigma)`.
An ep-signature $`\mathbf{\Sigma}` is identified with the ep-specification
$`(\mathbf{\Sigma}, \varnothing)`, whose models are the $`\mathbf{\Sigma}`-algebras, and
$`\mathsf{epAlg}(\mathbf{\Sigma}) = \mathsf{epAlg}(\mathbf{\Sigma}, \varnothing)`.

```lean
def EpSignature.IsModel (Sg : EpSignature.{u, v} S) {V : S → Type}
    (E : Set (QEEq Sg.sig V)) (A : PartialAlgebra.{u, v, w} Sg.sig) : Prop :=
  Sg.IsAlgebra A ∧ ∀ q ∈ E, q.Holds A

def EpAlg (Sg : EpSignature.{u, v} S) {V : S → Type} (E : Set (QEEq Sg.sig V)) :
    Type (max u v (w + 1)) :=
  {A : PartialAlgebra.{u, v, w} Sg.sig // Sg.IsModel E A}

instance (Sg : EpSignature.{u, v} S) {V : S → Type} (E : Set (QEEq Sg.sig V)) :
    CategoryTheory.Category.{max u w} (EpAlg.{u, v, w} Sg E) where
  Hom A B := PartialAlgebra.Hom A.1 B.1
  id A := PartialAlgebra.Hom.id A.1
  comp H K := PartialAlgebra.Hom.comp K H
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
```
:::

# Semantic consequence

:::definition (label := "ep-specification.cn") (central := false) (title := "Semantic consequence operator")
Let $`(\mathbf{\Sigma}, \mathcal{E})` be an ep-specification and $`X` an $`S`-sorted set. For
$`\mathcal{H} \subseteq \mathrm{Eq}_{\Sigma}(X)`, $`\mathrm{Cn}^{\mathbf{\Sigma}, \mathcal{E}}_X(\mathcal{H})`
is the set of the existence equations $`e` such that, for every model $`\mathbf{A}` of
$`(\mathbf{\Sigma}, \mathcal{E})` and every valuation $`a \colon X \to A` with
$`\mathbf{A} \models \mathcal{H}[a]`, $`e` holds in $`\mathbf{A}` under $`a`; that is, every
pair $`(\mathbf{A}, a)` in $`\mathrm{Mod}(\mathcal{H})` is in $`\mathrm{Mod}(\{e\})`. A set
$`\mathcal{H}` is *closed* if $`\mathrm{Cn}^{\mathbf{\Sigma}, \mathcal{E}}_X(\mathcal{H}) = \mathcal{H}`.

The models range over the partial algebras whose carriers lie in a fixed universe, an argument
of the Lean definition that the draft does not see; the library always takes the universe of
the algebras under consideration.

```lean
def EpSignature.Cn (Sg : EpSignature.{u, v} S) {V : S → Type} (E : Set (QEEq Sg.sig V))
    (X : S → Type) (H : Set (EEq Sg.sig X)) : Set (EEq Sg.sig X) :=
  {e | ∀ A : PartialAlgebra.{u, v, w} Sg.sig, Sg.IsModel E A →
    ∀ a : ∀ s, X s → A s, EEq.HoldsAll A a H → e.Holds A a}
```
:::

:::proposition (label := "ep-specification.cn-closure") (central := false) (title := "Cn is a closure operator")
$`\mathrm{Cn}^{\mathbf{\Sigma}, \mathcal{E}}_X` is a closure operator on the subsets of
$`\mathrm{Eq}_{\Sigma}(X)`, whose closed sets are those with
$`\mathrm{Cn}^{\mathbf{\Sigma}, \mathcal{E}}_X(\mathcal{H}) = \mathcal{H}`.

```lean
def EpSignature.cnClosure (Sg : EpSignature.{u, v} S) {V : S → Type}
    (E : Set (QEEq Sg.sig V)) (X : S → Type) : ClosureOperator (Set (EEq Sg.sig X)) :=
  ClosureOperator.mk₂ (Sg.Cn.{u, v, w} E X)
    (fun _ e he _ _ _ hH => hH e he)
    (fun _ _ hle e he A hA a hH' => he A hA a fun e' he' => hle he' A hA a hH')
```
:::

:::proof (of := "ep-specification.cn-closure")
Every equation of $`\mathcal{H}` holds wherever $`\mathcal{H}` does, so
$`\mathcal{H} \subseteq \mathrm{Cn}(\mathcal{H})`. If $`\mathcal{H} \subseteq \mathrm{Cn}(\mathcal{H}')`,
then every pair in $`\mathrm{Mod}(\mathcal{H}')` is in $`\mathrm{Mod}(\mathcal{H})`, and hence
$`\mathrm{Cn}(\mathcal{H}) \subseteq \mathrm{Cn}(\mathcal{H}')`. These two properties
characterize closure operators.
:::

:::proposition (label := "ep-specification.cn-models") (central := false) (title := "Cn does not change the models")
For every $`\mathcal{H} \subseteq \mathrm{Eq}_{\Sigma}(X)`:

1. $`\mathrm{Mod}(\mathrm{Cn}(\mathcal{H})) = \mathrm{Mod}(\mathcal{H})`;
2. $`\mathcal{H}' \subseteq \mathrm{Cn}(\mathcal{H})` if and only if
   $`\mathrm{Mod}(\mathcal{H}) \subseteq \mathrm{Mod}(\mathcal{H}')`;
3. two closed sets of existence equations are equal if and only if they have the same models.

```lean
namespace EpSignature

variable (Sg : EpSignature.{u, v} S) {V : S → Type} (E : Set (QEEq Sg.sig V)) {X : S → Type}

theorem holdsAll_cn_iff {H : Set (EEq Sg.sig X)} {A : PartialAlgebra.{u, v, w} Sg.sig}
    (hA : Sg.IsModel E A) (a : ∀ s, X s → A s) :
    EEq.HoldsAll A a (Sg.Cn.{u, v, w} E X H) ↔ EEq.HoldsAll A a H :=
  ⟨fun h e he => h e fun _ _ _ hH => hH e he, fun h _ he => he A hA a h⟩

theorem subset_cn_iff {H H' : Set (EEq Sg.sig X)} :
    H' ⊆ Sg.Cn.{u, v, w} E X H ↔
      ∀ A : PartialAlgebra.{u, v, w} Sg.sig, Sg.IsModel E A →
        ∀ a : ∀ s, X s → A s, EEq.HoldsAll A a H → EEq.HoldsAll A a H' :=
  ⟨fun h A hA a hH e he => h he A hA a hH, fun h e he A hA a hH => h A hA a hH e he⟩

theorem eq_of_closed {H H' : Set (EEq Sg.sig X)} (hH : Sg.Cn.{u, v, w} E X H = H)
    (hH' : Sg.Cn.{u, v, w} E X H' = H') :
    H = H' ↔ ∀ A : PartialAlgebra.{u, v, w} Sg.sig, Sg.IsModel E A →
      ∀ a : ∀ s, X s → A s, (EEq.HoldsAll A a H ↔ EEq.HoldsAll A a H') := by
  refine ⟨fun h _ _ _ => h ▸ Iff.rfl, fun h => ?_⟩
  apply Set.Subset.antisymm
  · rw [← hH']
    exact (subset_cn_iff Sg E).2 fun A hA a hH'' => (h A hA a).2 hH''
  · rw [← hH]
    exact (subset_cn_iff Sg E).2 fun A hA a hH'' => (h A hA a).1 hH''

end EpSignature
```
:::

:::proof (of := "ep-specification.cn-models")
(1) A pair in $`\mathrm{Mod}(\mathrm{Cn}(\mathcal{H}))` is in $`\mathrm{Mod}(\mathcal{H})`, since
$`\mathcal{H} \subseteq \mathrm{Cn}(\mathcal{H})`, and conversely by the definition of
$`\mathrm{Cn}`. (2) Both sides say that every pair in $`\mathrm{Mod}(\mathcal{H})` satisfies every
equation of $`\mathcal{H}'`. (3) If $`\mathcal{H}` and $`\mathcal{H}'` are closed and have the
same models, then, by (2), each is contained in the closure of the other, which is the other.
:::

```lean
end CategorialAlgebras
```
