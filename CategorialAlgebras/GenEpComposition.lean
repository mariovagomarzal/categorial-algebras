import Stemma
import Mathlib.CategoryTheory.Bicategory.Grothendieck
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import CategorialAlgebras.GenEpDerivor

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "Composition of generalized ep-derivors" =>

Generalized ep-derivors compose (Subsection `SEpSiggd` of the draft): the composite translates the
domains of the first one along the second, and keeps the closure of the result under the semantic
consequence operator, which makes the composition associative. The functor of a composite is the
composite of the functors on the models. In the draft both are equal; here the cells of
$`(\mathbf{e} \circ \mathbf{d})^{\ast}_{\mathfrak{gd}}(\mathbf{C})` are the elements of $`C` that satisfy
the domains of the composite, while those of
$`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{e}^{\ast}_{\mathfrak{gd}}(\mathbf{C}))` are the cells of
$`\mathbf{e}^{\ast}_{\mathfrak{gd}}(\mathbf{C})` that satisfy the domains of $`\mathbf{d}`: they are the
same elements of $`C`, but not the same set. The equalities of the draft are therefore stated as
isomorphisms that send every cell to itself, and the functor $`\mathrm{Alg}_{\mathfrak{gd}}` of the
draft becomes a pseudofunctor; its Grothendieck construction is the category
$`\mathsf{epAlg}_{\mathfrak{gd}}`.

The composite depends on the universe of the algebras over which the semantic consequence operator
ranges, the universe `w` of the Lean. All the signatures of this document have their sorts and
operation symbols in the same universes.

```lean
universe u v w

namespace CategorialAlgebras

open Signature CategoryTheory

variable {S T U : Type u}

/-- The ep-specification `(𝚺, ∅)`. -/
def EpSignature.toSpec (Sg : EpSignature.{u, v} S) : EpSpec.{u, v} S fun _ => Empty := ⟨Sg, ∅⟩

/-- The semantic consequence operator `Cn^𝚺_κ` of an ep-signature. -/
def EpSignature.Cn (Sg : EpSignature.{u, v} S) {I : Type} (κ : I → S)
    (H : Set (EEq Sg.sig (Vars κ))) : Set (EEq Sg.sig (Vars κ)) :=
  EpSpec.Cn.{u, v, w} Sg.toSpec κ H
```

# Composites and identities

:::definition (label := "gen-ep-comp") (central := false) (title := "Composite and identity generalized ep-derivors")
Let $`\mathbf{d} = (\varphi, D, d)` be a generalized ep-derivor from $`\mathbf{\Sigma}` to
$`\mathbf{\Lambda}` and $`\mathbf{e} = (\psi, E, e)` one from $`\mathbf{\Lambda}` to $`\mathbf{\Omega}`.
The *composite* $`\mathbf{e} \circ \mathbf{d}` is
$`(\psi \circ \varphi, D^{\mathbf{e} \circ \mathbf{d}}, e^{\sharp} \circ d)`, where
$`(\psi \circ \varphi, e^{\sharp} \circ d)` is the composite derivor and
$`D^{\mathbf{e} \circ \mathbf{d}}_s = \mathrm{Cn}^{\mathbf{\Omega}}(E_{\varphi(s)} \cup \mathrm{tr}_{\mathbf{e}}[D_s])`.
The *identity* at $`\mathbf{\Sigma}` is
$`\mathrm{id}_{\mathbf{\Sigma}} = (\mathrm{id}_S, (\mathrm{Cn}^{\mathbf{\Sigma}}(\varnothing))_{s \in S}, \eta^{\Sigma})`.

```lean
namespace GenEpDerivor

variable {Sg : EpSignature.{u, v} S} {Lg : EpSignature.{u, v} T} {Og : EpSignature.{u, v} U}

/-- The composite `𝐞 ∘ 𝐝`. -/
noncomputable def comp (ε : GenEpDerivor Lg Og) (δ : GenEpDerivor Sg Lg) : GenEpDerivor Sg Og where
  sortMap := ε.sortMap ∘ δ.sortMap
  sortDom s := EpSignature.Cn.{u, v, w} Og (fun _ : Unit => ε.sortMap (δ.sortMap s))
    (ε.sortDom (δ.sortMap s) ∪ ε.trSet (δ.sortDom s))
  op σ := ε.toDerivor.lift (δ.op σ)

/-- The identity `id_𝚺`. -/
noncomputable def id (Sg : EpSignature.{u, v} S) : GenEpDerivor Sg Sg where
  sortMap := _root_.id
  sortDom s := EpSignature.Cn.{u, v, w} Sg (fun _ : Unit => s) ∅
  op σ := (Derivor.id Sg.sig).op σ

end GenEpDerivor
```
:::

:::Stemma.lemma (label := "gen-ep-comp-models") (central := false) (title := "The functor of a composite")
Let $`\mathbf{d}` be a generalized ep-derivor from $`\mathbf{\Sigma}` to $`\mathbf{\Lambda}`,
$`\mathbf{e}` one from $`\mathbf{\Lambda}` to $`\mathbf{\Omega}`, and $`(\mathbf{\Sigma}, \mathcal{E})`,
$`(\mathbf{\Lambda}, \mathcal{F})` and $`(\mathbf{\Omega}, \mathcal{G})` ep-specifications such that
$`\mathbf{e}^{\ast}_{\mathfrak{gd}}` sends models of $`(\mathbf{\Omega}, \mathcal{G})` to models of
$`(\mathbf{\Lambda}, \mathcal{F})` and $`\mathbf{d}^{\ast}_{\mathfrak{gd}}` sends models of
$`(\mathbf{\Lambda}, \mathcal{F})` to models of $`(\mathbf{\Sigma}, \mathcal{E})`. Then
$`(\mathbf{e} \circ \mathbf{d})^{\ast}_{\mathfrak{gd}}` sends models of $`(\mathbf{\Omega}, \mathcal{G})`
to models of $`(\mathbf{\Sigma}, \mathcal{E})`, and it is isomorphic, on these models, to
$`\mathbf{d}^{\ast}_{\mathfrak{gd}} \circ \mathbf{e}^{\ast}_{\mathfrak{gd}}`, by isomorphisms that send
every cell to itself. Moreover, $`(\mathrm{id}_{\mathbf{\Sigma}})^{\ast}_{\mathfrak{gd}}` sends models
of $`(\mathbf{\Sigma}, \mathcal{E})` to models of $`(\mathbf{\Sigma}, \mathcal{E})`, and it is
isomorphic on them to the identity functor, by isomorphisms that send every cell to itself.

```lean
namespace GenEpDerivor

variable {Sg : EpSignature.{u, v} S} {Lg : EpSignature.{u, v} T} {Og : EpSignature.{u, v} U}
  {V : S → Type} {V' : T → Type} {V'' : U → Type}
  {E : Set (QEEq Sg.sig V)} {F : Set (QEEq Lg.sig V')} {G : Set (QEEq Og.sig V'')}
  {ε : GenEpDerivor Lg Og} {δ : GenEpDerivor Sg Lg}

theorem comp_sendsModels (hε : ε.SendsModels.{u, v, u, v, w} F G)
    (hδ : δ.SendsModels.{u, v, u, v, w} E F) :
    (ε.comp.{u, v, w} δ).SendsModels.{u, v, u, v, w} E G := by
  sorry

/-- The homomorphism `(𝐞 ∘ 𝐝)*(𝐂) → 𝐝*(𝐞*(𝐂))` that sends every cell to itself. -/
noncomputable def compHom (C : EpSpec.EpAlg.{u, v, w} (EpSpec.mk Og G)) :
    PartialAlgebra.Hom ((ε.comp.{u, v, w} δ).derived C.1) (δ.derived (ε.derived C.1)) where
  map _ x := ⟨⟨x.1, by sorry⟩, by sorry⟩
  map_dom := by sorry
  map_op := by sorry

/-- The homomorphism `𝐝*(𝐞*(𝐂)) → (𝐞 ∘ 𝐝)*(𝐂)` that sends every cell to itself. -/
noncomputable def compInv (C : EpSpec.EpAlg.{u, v, w} (EpSpec.mk Og G)) :
    PartialAlgebra.Hom (δ.derived (ε.derived C.1)) ((ε.comp.{u, v, w} δ).derived C.1) where
  map _ x := ⟨x.1.1, by sorry⟩
  map_dom := by sorry
  map_op := by sorry

/-- `(𝐞 ∘ 𝐝)*_𝔤𝔡 ≅ 𝐝*_𝔤𝔡 ∘ 𝐞*_𝔤𝔡` on the models. -/
noncomputable def compIso (hε : ε.SendsModels.{u, v, u, v, w} F G)
    (hδ : δ.SendsModels.{u, v, u, v, w} E F) :
    (ε.comp.{u, v, w} δ).restrict (comp_sendsModels hε hδ) ≅ ε.restrict hε ⋙ δ.restrict hδ :=
  NatIso.ofComponents
    (fun C => { hom := compHom C, inv := compInv C, hom_inv_id := by sorry, inv_hom_id := by sorry })
    (by sorry)

theorem compIso_hom_map (hε : ε.SendsModels.{u, v, u, v, w} F G)
    (hδ : δ.SendsModels.{u, v, u, v, w} E F) (C : EpSpec.EpAlg.{u, v, w} (EpSpec.mk Og G)) (s : S)
    (x : (ε.comp.{u, v, w} δ).derived C.1 s) :
    (PartialAlgebra.Hom.map ((compIso hε hδ).hom.app C) s x).1.1 = x.1 := by
  sorry

theorem id_sendsModels : (GenEpDerivor.id.{u, v, w} Sg).SendsModels.{u, v, u, v, w} E E := by
  sorry

/-- `(id_𝚺)*_𝔤𝔡 ≅ Id` on the models. -/
noncomputable def idIso :
    (GenEpDerivor.id.{u, v, w} Sg).restrict (id_sendsModels (E := E)) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun A =>
      { hom := (⟨fun _ x => x.1, by sorry, by sorry⟩ :
          PartialAlgebra.Hom ((GenEpDerivor.id.{u, v, w} Sg).derived A.1) A.1)
        inv := (⟨fun _ a => ⟨a, by sorry⟩, by sorry, by sorry⟩ :
          PartialAlgebra.Hom A.1 ((GenEpDerivor.id.{u, v, w} Sg).derived A.1))
        hom_inv_id := by sorry
        inv_hom_id := by sorry })
    (by sorry)

theorem idIso_hom_map (A : EpSpec.EpAlg.{u, v, w} (EpSpec.mk Sg E)) (s : S)
    (x : (GenEpDerivor.id.{u, v, w} Sg).derived A.1 s) :
    PartialAlgebra.Hom.map ((idIso (E := E)).hom.app A) s x = x.1 := by
  sorry

end GenEpDerivor
```
:::

:::proof (of := "gen-ep-comp-models")
Let $`\mathbf{C}` be a model of $`(\mathbf{\Omega}, \mathcal{G})`,
$`\mathbf{B} = \mathbf{e}^{\ast}_{\mathfrak{gd}}(\mathbf{C})`,
$`\mathbf{A} = \mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})` and
$`\mathbf{A}' = (\mathbf{e} \circ \mathbf{d})^{\ast}_{\mathfrak{gd}}(\mathbf{C})`. Since $`\mathbf{C}` is a
$`\mathbf{\Omega}`-algebra, $`D^{\mathbf{e} \circ \mathbf{d}}_s` and
$`E_{\varphi(s)} \cup \mathrm{tr}_{\mathbf{e}}[D_s]` hold for the same elements of $`\mathbf{C}`, so
that, by Lemma `gen-ep-translation` applied to $`\mathbf{e}`, an element of $`C_{\psi(\varphi(s))}`
is a cell of sort $`s` of $`\mathbf{A}'` if and only if it is a cell of sort $`s` of $`\mathbf{A}`.

By well-founded induction along $`\lhd`, every $`\sigma` has the same interpretation in
$`\mathbf{A}` and in $`\mathbf{A}'`. Assume it for every $`\tau \lhd \sigma`; then the domain
conditions of $`\sigma` hold for the same families in both algebras. Since $`\mathbf{A}` is a
$`\mathbf{\Sigma}`-algebra, by Proposition `gen-ep-domain-def` the domain of $`\sigma` in
$`\mathbf{A}` is the set of the families that satisfy its domain conditions, and for them
$`d(\sigma)^{\mathbf{B}}` is defined and is a cell of sort $`s`; by Lemma `gen-ep-translation`
applied to $`\mathbf{e}`, $`e^{\sharp}(d(\sigma))^{\mathbf{C}}` is then defined and equal to it.
Hence, by Proposition `gen-ep-domain-def` applied to $`\mathbf{e} \circ \mathbf{d}`, both domains
and both values agree. So $`\mathbf{A}'` is $`\mathbf{A}` up to the identification of the cells, and
it is a model of $`(\mathbf{\Sigma}, \mathcal{E})`. On homomorphisms both functors take
restrictions.

For the identity, every element of a $`\mathbf{\Sigma}`-algebra satisfies
$`\mathrm{Cn}^{\mathbf{\Sigma}}(\varnothing)`, and $`\sigma((j)_j)^{\mathbf{A}}` is $`\sigma^{\mathbf{A}}`,
whose domain is the set of the families that satisfy $`\mathrm{def}^{\mathbf{\Sigma}}(\sigma)`.
:::

:::remark (label := "gen-ep-same-functor") (title := "Changing the domains")
Two generalized ep-derivors $`(\varphi, D, d)` and $`(\varphi, D', d)` that differ only in their
domains derive the same algebra from every partial $`\Lambda`-algebra $`\mathbf{B}` in which $`D` and
$`D'` hold for the same elements, up to the identification of the cells: by Proposition
`gen-ep-domain-def` and induction along $`\lhd`, every $`\sigma` has the same domain in both
algebras, and the values are given by the same derived operations.

```lean
namespace GenEpDerivor

variable {Sg : EpSignature.{u, v} S} {Lg : EpSignature.{u, v} T} (δ : GenEpDerivor Sg Lg)

/-- The generalized ep-derivor `(φ, D', d)`. -/
def withDom (D' : ∀ s, Set (EEq Lg.sig (Vars fun _ : Unit => δ.sortMap s))) : GenEpDerivor Sg Lg :=
  { δ with sortDom := D' }

/-- `(φ, D, d)*(𝐁) ≅ (φ, D', d)*(𝐁)` when `D` and `D'` hold for the same elements of `𝐁`. -/
noncomputable def withDomIso (D' : ∀ s, Set (EEq Lg.sig (Vars fun _ : Unit => δ.sortMap s)))
    (B : PartialAlgebra.{u, v, w} Lg.sig)
    (h : ∀ s (b : B (δ.sortMap s)),
      EEq.HoldsAll B (val₁ b) (δ.sortDom s) ↔ EEq.HoldsAll B (val₁ b) (D' s)) :
    δ.derived B ≅ (δ.withDom D').derived B where
  hom := ⟨fun s x => ⟨x.1, (h s x.1).mp x.2⟩, by sorry, by sorry⟩
  inv := ⟨fun s x => ⟨x.1, (h s x.1).mpr x.2⟩, by sorry, by sorry⟩
  hom_inv_id := by sorry
  inv_hom_id := by sorry

end GenEpDerivor
```
:::

# The category of ep-signatures and generalized ep-derivors

:::definition (label := "gen-ep-closed") (central := false) (title := "Closed generalized ep-derivors")
A generalized ep-derivor $`\mathbf{d} = (\varphi, D, d)` from $`\mathbf{\Sigma}` to $`\mathbf{\Lambda}` is
*closed* if every $`D_s` is closed: $`\mathrm{Cn}^{\mathbf{\Lambda}}(D_s) = D_s`. Composites and
identities are closed, by definition.

```lean
namespace GenEpDerivor

variable {Sg : EpSignature.{u, v} S} {Lg : EpSignature.{u, v} T} (δ : GenEpDerivor Sg Lg)

/-- `𝐝` is closed. -/
def IsClosed : Prop :=
  ∀ s, EpSignature.Cn.{u, v, w} Lg (fun _ : Unit => δ.sortMap s) (δ.sortDom s) = δ.sortDom s

end GenEpDerivor
```
:::

:::proposition (label := "ep-sig-gd") (central := false) (title := "The category epSig_𝔤𝔡")
The ep-signatures, as objects, and the closed generalized ep-derivors that send algebras to
algebras, as morphisms, with the composites and identities of Definition `gen-ep-comp`, form a
category $`\mathsf{epSig}_{\mathfrak{gd}}`.

The objects record the universe `w` of the algebras, on which the morphisms depend.

```lean
/-- The ep-signatures, as objects of `epSig_𝔤𝔡`. -/
structure EpSigGd where
  /-- The set of sorts. -/
  sorts : Type u
  /-- The ep-signature. -/
  sg : EpSignature.{u, v} sorts
  /-- The universe of the algebras. -/
  univ : PUnit.{w + 1} := ⟨⟩

namespace EpSigGd

/-- The morphisms of `epSig_𝔤𝔡`. -/
structure Hom (X Y : EpSigGd.{u, v, w}) where
  /-- The generalized ep-derivor. -/
  der : GenEpDerivor X.sg Y.sg
  /-- It is closed. -/
  closed : der.IsClosed.{u, v, w}
  /-- It sends algebras to algebras. -/
  sends : der.SendsModels.{u, v, u, v, w} X.sg.toSpec.eqs Y.sg.toSpec.eqs

noncomputable instance category : Category.{max u v} EpSigGd.{u, v, w} where
  Hom := Hom
  id X := ⟨GenEpDerivor.id.{u, v, w} X.sg, by sorry, GenEpDerivor.id_sendsModels⟩
  comp f g := ⟨g.der.comp.{u, v, w} f.der, by sorry, GenEpDerivor.comp_sendsModels g.sends f.sends⟩
  id_comp := by sorry
  comp_id := by sorry
  assoc := by sorry

end EpSigGd
```
:::

:::proof (of := "ep-sig-gd")
By Lemma `gen-ep-comp-models`, with empty sets of $`\mathrm{QE}`-equations, composites and
identities send algebras to algebras, and they are closed by definition. The first components of
$`(\mathbf{f} \circ \mathbf{e}) \circ \mathbf{d}` and $`\mathbf{f} \circ (\mathbf{e} \circ \mathbf{d})`
are equal, and so are their third ones, by Proposition `derivor-lift-id-comp`. Their second
components are closed, so, by Proposition `ep-consequence-closure`, it suffices that they hold for
the same elements of every $`\mathbf{\Theta}`-algebra $`\mathbf{X}`: by the first part of the proof of
Lemma `gen-ep-comp-models`, these are, in both cases, the cells of
$`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{e}^{\ast}_{\mathfrak{gd}}(\mathbf{f}^{\ast}_{\mathfrak{gd}}(\mathbf{X})))`.
In the same way, $`\mathbf{d} \circ \mathrm{id} = \mathbf{d} = \mathrm{id} \circ \mathbf{d}`.
:::

# Algebras along generalized ep-derivors

:::proposition (label := "alg-gd") (central := false) (title := "The pseudofunctor Alg_𝔤𝔡")
There is a contravariant pseudofunctor $`\mathrm{Alg}_{\mathfrak{gd}}` from $`\mathsf{epSig}_{\mathfrak{gd}}`
to $`\mathsf{Cat}` that sends an ep-signature $`\mathbf{\Sigma}` to $`\mathsf{epAlg}(\mathbf{\Sigma})`, a
morphism $`\mathbf{d}` to the birestriction $`\mathbf{d}^{\ast}_{\mathfrak{gd}}`, and whose structural
isomorphisms are those of Lemma `gen-ep-comp-models`.

The draft states $`\mathrm{Alg}_{\mathfrak{gd}}` as a functor, with
$`\mathrm{Alg}_{\mathfrak{gd}}(\mathbf{e} \circ \mathbf{d}) = \mathrm{Alg}_{\mathfrak{gd}}(\mathbf{d}) \circ \mathrm{Alg}_{\mathfrak{gd}}(\mathbf{e})`;
these equalities hold up to the isomorphisms of Lemma `gen-ep-comp-models`, which send every cell
to itself and therefore satisfy the coherence conditions of a pseudofunctor.

```lean
namespace EpSigGd

/-- The pseudofunctor `Alg_𝔤𝔡`. -/
noncomputable def algGd :
    Pseudofunctor (LocallyDiscrete EpSigGd.{u, v, w}ᵒᵖ) Cat.{max u w, max u v (w + 1)} :=
  LocallyDiscrete.mkPseudofunctor
    (fun X => Cat.of (EpSpec.EpAlg.{u, v, w} X.unop.sg.toSpec))
    (fun f => (f.unop.der.restrict f.unop.sends).toCatHom)
    (fun X => Cat.Hom.isoMk GenEpDerivor.idIso)
    (fun f g => Cat.Hom.isoMk (GenEpDerivor.compIso f.unop.sends g.unop.sends))
    (by sorry) (by sorry) (by sorry)

end EpSigGd
```
:::

:::proof (of := "alg-gd")
The isomorphisms of Lemma `gen-ep-comp-models` send every cell to itself, and so do their
composites and whiskerings; two such isomorphisms between the same functors are equal, since a
homomorphism is determined by its values. The coherence conditions are equations between such
isomorphisms.
:::

:::definition (label := "ep-alg-gd") (central := false) (title := "The category epAlg_𝔤𝔡")
The category $`\mathsf{epAlg}_{\mathfrak{gd}}` is the Grothendieck construction of the contravariant
pseudofunctor $`\mathrm{Alg}_{\mathfrak{gd}}`. Its objects are the pairs
$`(\mathbf{\Sigma}, \mathbf{A})`, with $`\mathbf{\Sigma}` an ep-signature and $`\mathbf{A}` a
$`\mathbf{\Sigma}`-algebra, and its morphisms from $`(\mathbf{\Sigma}, \mathbf{A})` to
$`(\mathbf{\Lambda}, \mathbf{B})` are the pairs $`(\mathbf{d}, h)`, with $`\mathbf{d}` a morphism of
$`\mathsf{epSig}_{\mathfrak{gd}}` from $`\mathbf{\Sigma}` to $`\mathbf{\Lambda}` and $`h` a homomorphism
from $`\mathbf{A}` to $`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})`.

```lean
/-- The category `epAlg_𝔤𝔡`. -/
abbrev EpAlgGd := Pseudofunctor.CoGrothendieck EpSigGd.algGd.{u, v, w}
```
:::

The category $`\mathsf{Sig}_{\mathfrak{d}}` of many-sorted signatures and derivors is mapped into
$`\mathsf{epSig}_{\mathfrak{gd}}` by sending $`(S, \Sigma)` to $`(S, \Sigma, \varnothing)` and a
derivor $`(\varphi, d)` to the closed generalized ep-derivor
$`(\varphi, (\mathrm{Cn}^{\mathbf{\Lambda}}(\varnothing))_{s \in S}, d)`, and
$`\mathrm{Alg}_{\mathfrak{gd}}` extends the contravariant functor that sends a many-sorted signature
$`(S, \Sigma)` to $`\mathsf{Alg}(\Sigma)` {cite}`CVST10b`.

```lean
end CategorialAlgebras
```
