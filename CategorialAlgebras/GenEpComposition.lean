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

```lean
section Agree

variable {Sig : Signature.{u, v} S} {A A' : PartialAlgebra.{u, v, w} Sig} (f : ∀ s, A s → A' s)

/-- Values of terms along a mapping that commutes with the operations of the symbols in `O`. -/
lemma Term.eval_map_of_agree (O : Set (Op Sig))
    (hO : ∀ τ ∈ O, ∀ a : Arity A τ.ws,
      A'.op τ.σ (fun j => f _ (a j)) = (A.op τ.σ a).map (f τ.s))
    {X : S → Type} (val : ∀ s, X s → Part (A s)) :
    ∀ {t : S} (R : Term Sig X t), R.ops ⊆ O →
      R.eval A' (fun s x => (val s x).map (f s)) = (R.eval A val).map (f t)
  | _, .var x, _ => by simp
  | _, .app σ ts, hR => by
    have hσ : (⟨_, _, σ⟩ : Op Sig) ∈ O := hR (Or.inl rfl)
    have ih : ∀ j, (ts j).eval A' (fun s x => (val s x).map (f s)) =
        ((ts j).eval A val).map (f _) := fun j =>
      Term.eval_map_of_agree O hO val (ts j)
        fun τ hτ => hR (Or.inr (Set.mem_iUnion.mpr ⟨j, hτ⟩))
    by_cases hall : ∀ j, ((ts j).eval A val).Dom
    · let a : Arity A _ := fun j => ((ts j).eval A val).get (hall j)
      have ha : ∀ j, (ts j).eval A val = Part.some (a j) := fun j => (Part.some_get _).symm
      have ha' : ∀ j, (ts j).eval A' (fun s x => (val s x).map (f s)) = Part.some (f _ (a j)) :=
        fun j => by rw [ih j, ha j, Part.map_some]
      rw [Term.eval_app_of_eq_some A' _ σ ha', Term.eval_app_of_eq_some A val σ ha]
      exact hO _ hσ a
    · push_neg at hall
      obtain ⟨j, hj⟩ := hall
      have h1 : ¬ ((Term.app σ ts).eval A' (fun s x => (val s x).map (f s))).Dom := fun h => by
        obtain ⟨c, hc, -⟩ := Term.eval_app_dom A' _ σ h
        have : ((ts j).eval A' (fun s x => (val s x).map (f s))).Dom := by rw [hc j]; trivial
        rw [ih j] at this
        exact hj this
      have h2 : ¬ ((Term.app σ ts).eval A val).Dom := fun h => by
        obtain ⟨c, hc, -⟩ := Term.eval_app_dom A val σ h
        exact hj (by rw [hc j]; trivial)
      rw [Part.eq_none_iff'.mpr h1, Part.eq_none_iff'.mpr h2, Part.map_none]

lemma EEq.holds_map_of_agree (hf : ∀ s, Function.Injective (f s)) (O : Set (Op Sig))
    (hO : ∀ τ ∈ O, ∀ a : Arity A τ.ws,
      A'.op τ.σ (fun j => f _ (a j)) = (A.op τ.σ a).map (f τ.s))
    {X : S → Type} (val : ∀ s, X s → Part (A s)) (e : EEq Sig X) (he : e.ops ⊆ O) :
    e.Holds A' (fun s x => (val s x).map (f s)) ↔ e.Holds A val := by
  unfold EEq.Holds
  rw [Term.eval_map_of_agree f O hO val e.lhs fun τ h => he (Or.inl h),
    Term.eval_map_of_agree f O hO val e.rhs fun τ h => he (Or.inr h)]
  constructor
  · rintro ⟨h1, h2, heq⟩
    exact ⟨h1, h2, hf _ heq⟩
  · rintro ⟨h1, h2, heq⟩
    exact ⟨h1, h2, congrArg (f _) heq⟩

lemma EEq.holdsAll_famVal_map_of_agree (hf : ∀ s, Function.Injective (f s))
    (hO : ∀ τ : Op Sig, ∀ a : Arity A τ.ws,
      A'.op τ.σ (fun j => f _ (a j)) = (A.op τ.σ a).map (f τ.s))
    {I : Type} {κ : I → S} (a : ∀ i, A (κ i)) (H : Set (EEq Sig (Vars κ))) :
    EEq.HoldsAll A' (famVal fun i => f _ (a i)) H ↔ EEq.HoldsAll A (famVal a) H := by
  rw [← famVal_map]
  exact ⟨fun h e he => (EEq.holds_map_of_agree f hf Set.univ (fun τ _ => hO τ) _ e
      (Set.subset_univ _)).mp (h e he),
    fun h e he => (EEq.holds_map_of_agree f hf Set.univ (fun τ _ => hO τ) _ e
      (Set.subset_univ _)).mpr (h e he)⟩

end Agree

/-- Two partial algebras of an ep-signature, related by injective mappings, have the same
operations if they do for every operation symbol whose domain conditions they satisfy alike. -/
theorem EpSignature.op_agree (Sg : EpSignature.{u, v} S) {A A' : PartialAlgebra.{u, v, w} Sg.sig}
    (f : ∀ s, A s → A' s) (hf : ∀ s, Function.Injective (f s))
    (step : ∀ {ws : List S} {s : S} (σ : Sg.sig ws s) (a : Arity A ws),
      (EEq.HoldsAll A' (famVal fun j => f _ (a j)) (Sg.defn σ) ↔
        EEq.HoldsAll A (famVal a) (Sg.defn σ)) →
      A'.op σ (fun j => f _ (a j)) = (A.op σ a).map (f s)) :
    ∀ (σ : Op Sg.sig) (a : Arity A σ.ws),
      A'.op σ.σ (fun j => f _ (a j)) = (A.op σ.σ a).map (f σ.s) := by
  intro σ
  induction σ using Sg.wf.induction with
  | h σ ih =>
    intro a
    apply step
    rw [← famVal_map]
    exact ⟨fun h e he => (EEq.holds_map_of_agree f hf {τ | Sg.Prec τ σ} (fun τ hτ => ih τ hτ) _ e
        fun τ hτ => ⟨e, he, hτ⟩).mp (h e he),
      fun h e he => (EEq.holds_map_of_agree f hf {τ | Sg.Prec τ σ} (fun τ hτ => ih τ hτ) _ e
        fun τ hτ => ⟨e, he, hτ⟩).mpr (h e he)⟩

/-- A partial algebra isomorphic to a model is a model. -/
theorem EpSpec.isModel_of_iso {V : S → Type} (Sp : EpSpec.{u, v} S V)
    {A B : PartialAlgebra.{u, v, w} Sp.sg.sig} (H : PartialAlgebra.Hom A B)
    (K : PartialAlgebra.Hom B A) (hHK : ∀ s x, H.map s (K.map s x) = x) (hA : Sp.IsModel A) :
    Sp.IsModel B := by
  have hval : ∀ {X : S → Type} (val : ∀ s, X s → Part (B s)),
      (fun s x => ((val s x).map (K.map s)).map (H.map s)) = val := by
    intro X val
    funext s x
    rw [Part.map_map]
    exact Part.map_id' (fun y => hHK s y) _
  refine ⟨fun σ b => ?_, fun q hq val hdom hprem => ?_⟩
  · have hb : (fun j => H.map _ (K.map _ (b j))) = b := funext fun j => hHK _ _
    constructor
    · intro hd
      have h := EEq.holdsAll_hom H _ ((hA.1 σ _).mp (K.map_dom σ b hd))
      rwa [famVal_map, hb] at h
    · intro hdef
      have h1 := EEq.holdsAll_hom K _ hdef
      rw [famVal_map] at h1
      have hd := H.map_dom σ _ ((hA.1 σ _).mpr h1)
      rwa [hb] at hd
  · have h := hA.2 q hq (fun s x => (val s x).map (K.map s)) (fun x hx => hdom x hx)
      fun e he => EEq.holdsAll_singleton.mp
        (EEq.holdsAll_hom K val (EEq.holdsAll_singleton.mpr (hprem e he)))
    have := EEq.holdsAll_singleton.mp (EEq.holdsAll_hom H _ (EEq.holdsAll_singleton.mpr h))
    rwa [hval] at this

namespace GenEpDerivor

variable {Sg : EpSignature.{u, v} S} {Lg : EpSignature.{u, v} T} {Og : EpSignature.{u, v} U}
  {ε : GenEpDerivor Lg Og} {δ : GenEpDerivor Sg Lg}

/-- The cells of `(𝐞 ∘ 𝐝)*(𝐂)` are those of `𝐝*(𝐞*(𝐂))`. -/
lemma comp_cells_iff {C : PartialAlgebra.{u, v, w} Og.sig} (hC : Og.IsAlgebra C) {s : S}
    (x : C (ε.sortMap (δ.sortMap s))) :
    EEq.HoldsAll C (val₁ x) ((ε.comp.{u, v, w} δ).sortDom s) ↔
      ∃ hE : EEq.HoldsAll C (val₁ x) (ε.sortDom (δ.sortMap s)),
        EEq.HoldsAll (ε.derived C) (val₁ (⟨x, hE⟩ : ε.cells C (δ.sortMap s))) (δ.sortDom s) := by
  have hm : Og.toSpec.IsModel C := ⟨hC, fun _ hq => hq.elim⟩
  refine (EpSpec.holdsAll_cn_iff (H := ε.sortDom (δ.sortMap s) ∪ ε.trSet (δ.sortDom s))
    Og.toSpec (fun _ : Unit => ε.sortMap (δ.sortMap s)) hm (fun _ => x)).trans
    (EEq.holdsAll_union.trans ?_)
  constructor
  · rintro ⟨hE, htr⟩
    exact ⟨hE, (ε.holdsAll_derived_iff (B := C)
      (fun _ : Unit => (⟨x, hE⟩ : ε.cells C (δ.sortMap s))) _).mpr htr⟩
  · rintro ⟨hE, hD⟩
    exact ⟨hE, (ε.holdsAll_derived_iff (B := C)
      (fun _ : Unit => (⟨x, hE⟩ : ε.cells C (δ.sortMap s))) _).mp hD⟩

/-- A cell of `𝐝*(𝐞*(𝐂))` as a cell of `(𝐞 ∘ 𝐝)*(𝐂)`. -/
def toComp {C : PartialAlgebra.{u, v, w} Og.sig} (hC : Og.IsAlgebra C) (s : S)
    (y : δ.derived (ε.derived C) s) : (ε.comp.{u, v, w} δ).derived C s :=
  ⟨y.1.1, (comp_cells_iff hC y.1.1).mpr ⟨y.1.2, y.2⟩⟩

/-- A cell of `(𝐞 ∘ 𝐝)*(𝐂)` as a cell of `𝐝*(𝐞*(𝐂))`. -/
def ofComp {C : PartialAlgebra.{u, v, w} Og.sig} (hC : Og.IsAlgebra C) (s : S)
    (x : (ε.comp.{u, v, w} δ).derived C s) : δ.derived (ε.derived C) s :=
  ⟨⟨x.1, ((comp_cells_iff hC x.1).mp x.2).fst⟩, ((comp_cells_iff hC x.1).mp x.2).snd⟩

lemma toComp_injective {C : PartialAlgebra.{u, v, w} Og.sig} (hC : Og.IsAlgebra C) (s : S) :
    Function.Injective (toComp (ε := ε) (δ := δ) hC s) := by
  intro y y' h
  have h1 := congrArg (fun z : (ε.comp.{u, v, w} δ).derived C s => z.1) h
  exact Subtype.ext (Subtype.ext h1)

theorem comp_op_agree {C : PartialAlgebra.{u, v, w} Og.sig} (hC : Og.IsAlgebra C)
    (hA : Sg.IsAlgebra (δ.derived (ε.derived C))) (σ : Op Sg.sig)
    (a : Arity (δ.derived (ε.derived C)) σ.ws) :
    ((ε.comp.{u, v, w} δ).derived C).op σ.σ (fun j => toComp hC _ (a j)) =
      ((δ.derived (ε.derived C)).op σ.σ a).map (toComp hC σ.s) := by
  refine Sg.op_agree (toComp hC) (toComp_injective hC) (fun {ws s} σ a hdef => ?_) σ a
  have hev : ∀ hδd : ((δ.op σ).eval (ε.derived C) (famVal fun j => (a j).1)).Dom,
      ((ε.comp.{u, v, w} δ).op σ).eval C (famVal fun j => (toComp hC _ (a j)).1) =
        Part.some (((δ.op σ).eval (ε.derived C) (famVal fun j => (a j).1)).get hδd).1 :=
    fun hδd => ε.eval_derived_get (B := C) (fun j => (a j).1) (δ.op σ) hδd
  apply Part.ext'
  · rw [(ε.comp.{u, v, w} δ).op_derived_dom_iff σ, hdef]
    show _ ↔ ((δ.derived (ε.derived C)).op σ a).Dom
    rw [hA σ a]
    refine ⟨fun h => h.1, fun hd => ⟨hd, ?_⟩⟩
    obtain ⟨hδd, hD⟩ := ((δ.op_derived_dom_iff σ a).mp ((hA σ a).mpr hd)).2
    refine ⟨by rw [hev hδd]; trivial, ?_⟩
    rw [Part.get_eq_of_mem (by rw [hev hδd]; exact Part.mem_some _)]
    exact (comp_cells_iff hC _).mpr ⟨_, hD⟩
  · intro h1 h2
    apply Subtype.ext
    exact Part.get_eq_of_mem (by rw [hev (δ.op_dom_of_holds h2)]; exact Part.mem_some _) _

/-- The cells of `(id_𝚺)*(𝐀)` are all the elements of a `𝚺`-algebra `𝐀`. -/
lemma id_cells {A : PartialAlgebra.{u, v, w} Sg.sig} (hA : Sg.IsAlgebra A) {s : S} (a : A s) :
    EEq.HoldsAll A (val₁ a) ((GenEpDerivor.id.{u, v, w} Sg).sortDom s) := by
  have hm : Sg.toSpec.IsModel A := ⟨hA, fun _ hq => hq.elim⟩
  exact (EpSpec.holdsAll_cn_iff Sg.toSpec (fun _ : Unit => s) hm (fun _ => a)).mpr
    EEq.holdsAll_empty

theorem id_op_agree {A : PartialAlgebra.{u, v, w} Sg.sig} (hA : Sg.IsAlgebra A) (σ : Op Sg.sig)
    (a : Arity ((GenEpDerivor.id.{u, v, w} Sg).derived A) σ.ws) :
    A.op σ.σ (fun j => (a j).1) =
      (((GenEpDerivor.id.{u, v, w} Sg).derived A).op σ.σ a).map fun x => x.1 := by
  refine Sg.op_agree (A := (GenEpDerivor.id.{u, v, w} Sg).derived A) (fun _ x => x.1)
    (fun _ _ _ h => Subtype.ext h) (fun {ws s} σ a hdef => ?_) σ a
  have hev : ((GenEpDerivor.id.{u, v, w} Sg).op σ).eval A (famVal fun j => (a j).1) =
      A.op σ fun j => (a j).1 :=
    Term.eval_app_of_eq_some A _ σ fun j => rfl
  apply Part.ext'
  · show (A.op σ fun j => (a j).1).Dom ↔ (((GenEpDerivor.id.{u, v, w} Sg).derived A).op σ a).Dom
    rw [GenEpDerivor.op_derived_dom_iff]
    constructor
    · intro hd
      exact ⟨hdef.mp ((hA σ _).mp hd), by rw [hev]; exact hd, id_cells hA _⟩
    · rintro ⟨h, -⟩
      exact (hA σ _).mpr (hdef.mpr h)
  · intro h1 h2
    exact (Part.get_eq_get_of_eq _ _ hev.symm).symm.trans rfl

end GenEpDerivor
```

:::Stemma.lemma (label := "gen-ep-comp-models") (central := true) (title := "The functor of a composite")
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

/-- The homomorphism `(𝐞 ∘ 𝐝)*(𝐂) → 𝐝*(𝐞*(𝐂))` that sends every cell to itself. -/
noncomputable def compHom (hε : ε.SendsModels.{u, v, u, v, w} F G)
    (hδ : δ.SendsModels.{u, v, u, v, w} E F) (C : EpSpec.EpAlg.{u, v, w} (EpSpec.mk Og G)) :
    PartialAlgebra.Hom ((ε.comp.{u, v, w} δ).derived C.1) (δ.derived (ε.derived C.1)) where
  map := ofComp C.2.1
  map_dom σ a' h := by
    have := comp_op_agree C.2.1 (hδ _ (hε C.1 C.2)).1 ⟨_, _, σ⟩ fun j => ofComp C.2.1 _ (a' j)
    have h' : (((ε.comp.{u, v, w} δ).derived C.1).op σ
        fun j => toComp C.2.1 _ (ofComp C.2.1 _ (a' j))).Dom := h
    rw [this] at h'
    exact h'
  map_op σ a' h := by
    have := comp_op_agree C.2.1 (hδ _ (hε C.1 C.2)).1 ⟨_, _, σ⟩ fun j => ofComp C.2.1 _ (a' j)
    exact congrArg (ofComp C.2.1 _) (Part.get_eq_get_of_eq _ h this)

/-- The homomorphism `𝐝*(𝐞*(𝐂)) → (𝐞 ∘ 𝐝)*(𝐂)` that sends every cell to itself. -/
noncomputable def compInv (hε : ε.SendsModels.{u, v, u, v, w} F G)
    (hδ : δ.SendsModels.{u, v, u, v, w} E F) (C : EpSpec.EpAlg.{u, v, w} (EpSpec.mk Og G)) :
    PartialAlgebra.Hom (δ.derived (ε.derived C.1)) ((ε.comp.{u, v, w} δ).derived C.1) where
  map := toComp C.2.1
  map_dom σ a h := by
    rw [comp_op_agree C.2.1 (hδ _ (hε C.1 C.2)).1 ⟨_, _, σ⟩ a]
    exact h
  map_op σ a h :=
    (Part.get_eq_get_of_eq _ _ (comp_op_agree C.2.1 (hδ _ (hε C.1 C.2)).1 ⟨_, _, σ⟩ a)).symm

theorem comp_sendsModels (hε : ε.SendsModels.{u, v, u, v, w} F G)
    (hδ : δ.SendsModels.{u, v, u, v, w} E F) :
    (ε.comp.{u, v, w} δ).SendsModels.{u, v, u, v, w} E G := fun C hC =>
  EpSpec.isModel_of_iso _ (compInv hε hδ ⟨C, hC⟩) (compHom hε hδ ⟨C, hC⟩) (fun _ _ => rfl)
    (hδ _ (hε C hC))

/-- `(𝐞 ∘ 𝐝)*_𝔤𝔡 ≅ 𝐝*_𝔤𝔡 ∘ 𝐞*_𝔤𝔡` on the models. -/
noncomputable def compIso (hε : ε.SendsModels.{u, v, u, v, w} F G)
    (hδ : δ.SendsModels.{u, v, u, v, w} E F) :
    (ε.comp.{u, v, w} δ).restrict (comp_sendsModels hε hδ) ≅ ε.restrict hε ⋙ δ.restrict hδ :=
  NatIso.ofComponents
    (fun C =>
      { hom := compHom hε hδ C
        inv := compInv hε hδ C
        hom_inv_id := PartialAlgebra.Hom.ext fun _ _ => rfl
        inv_hom_id := PartialAlgebra.Hom.ext fun _ _ => rfl })
    (fun _ => PartialAlgebra.Hom.ext fun _ _ => rfl)

theorem compIso_hom_map (hε : ε.SendsModels.{u, v, u, v, w} F G)
    (hδ : δ.SendsModels.{u, v, u, v, w} E F) (C : EpSpec.EpAlg.{u, v, w} (EpSpec.mk Og G)) (s : S)
    (x : (ε.comp.{u, v, w} δ).derived C.1 s) :
    (PartialAlgebra.Hom.map ((compIso hε hδ).hom.app C) s x).1.1 = x.1 :=
  rfl

/-- The homomorphism `(id_𝚺)*(𝐀) → 𝐀`. -/
noncomputable def idHom (A : EpSpec.EpAlg.{u, v, w} (EpSpec.mk Sg E)) :
    PartialAlgebra.Hom ((GenEpDerivor.id.{u, v, w} Sg).derived A.1) A.1 where
  map _ x := x.1
  map_dom σ a h := by
    rw [id_op_agree A.2.1 ⟨_, _, σ⟩ a]
    exact h
  map_op σ a h := (Part.get_eq_get_of_eq _ _ (id_op_agree A.2.1 ⟨_, _, σ⟩ a)).symm

/-- The homomorphism `𝐀 → (id_𝚺)*(𝐀)`. -/
noncomputable def idInv (A : EpSpec.EpAlg.{u, v, w} (EpSpec.mk Sg E)) :
    PartialAlgebra.Hom A.1 ((GenEpDerivor.id.{u, v, w} Sg).derived A.1) where
  map _ a := ⟨a, id_cells A.2.1 a⟩
  map_dom σ a h := by
    have := id_op_agree A.2.1 ⟨_, _, σ⟩ fun j => ⟨a j, id_cells A.2.1 (a j)⟩
    have h' : (A.1.op σ fun j => a j).Dom := h
    rw [this] at h'
    exact h'
  map_op σ a h := by
    have := id_op_agree A.2.1 ⟨_, _, σ⟩ fun j => ⟨a j, id_cells A.2.1 (a j)⟩
    exact Subtype.ext (Part.get_eq_get_of_eq _ h this)

theorem id_sendsModels : (GenEpDerivor.id.{u, v, w} Sg).SendsModels.{u, v, u, v, w} E E :=
  fun A hA => EpSpec.isModel_of_iso _ (idInv ⟨A, hA⟩) (idHom ⟨A, hA⟩) (fun _ _ => rfl) hA

/-- `(id_𝚺)*_𝔤𝔡 ≅ Id` on the models. -/
noncomputable def idIso :
    (GenEpDerivor.id.{u, v, w} Sg).restrict (id_sendsModels (E := E)) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun A =>
      { hom := idHom A
        inv := idInv A
        hom_inv_id := PartialAlgebra.Hom.ext fun _ _ => rfl
        inv_hom_id := PartialAlgebra.Hom.ext fun _ _ => rfl })
    (fun _ => PartialAlgebra.Hom.ext fun _ _ => rfl)

theorem idIso_hom_map (A : EpSpec.EpAlg.{u, v, w} (EpSpec.mk Sg E)) (s : S)
    (x : (GenEpDerivor.id.{u, v, w} Sg).derived A.1 s) :
    PartialAlgebra.Hom.map ((idIso (E := E)).hom.app A) s x = x.1 :=
  rfl

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

/-- A cell of `(φ, D, d)*(𝐁)` as a cell of `(φ, D', d)*(𝐁)`. -/
def toWithDom {D' : ∀ s, Set (EEq Lg.sig (Vars fun _ : Unit => δ.sortMap s))}
    {B : PartialAlgebra.{u, v, w} Lg.sig}
    (h : ∀ s (b : B (δ.sortMap s)),
      EEq.HoldsAll B (val₁ b) (δ.sortDom s) ↔ EEq.HoldsAll B (val₁ b) (D' s))
    (s : S) (x : δ.derived B s) : (δ.withDom D').derived B s :=
  ⟨x.1, (h s x.1).mp x.2⟩

theorem withDom_op_agree {D' : ∀ s, Set (EEq Lg.sig (Vars fun _ : Unit => δ.sortMap s))}
    {B : PartialAlgebra.{u, v, w} Lg.sig}
    (h : ∀ s (b : B (δ.sortMap s)),
      EEq.HoldsAll B (val₁ b) (δ.sortDom s) ↔ EEq.HoldsAll B (val₁ b) (D' s))
    (σ : Op Sg.sig) (a : Arity (δ.derived B) σ.ws) :
    ((δ.withDom D').derived B).op σ.σ (fun j => δ.toWithDom h _ (a j)) =
      ((δ.derived B).op σ.σ a).map (δ.toWithDom h σ.s) := by
  refine Sg.op_agree (δ.toWithDom h)
    (fun s x y hxy => Subtype.ext (congrArg (fun z : (δ.withDom D').derived B s => z.1) hxy))
    (fun {ws s} σ a hdef => ?_) σ a
  apply Part.ext'
  · show _ ↔ ((δ.derived B).op σ a).Dom
    rw [op_derived_dom_iff, op_derived_dom_iff, hdef]
    constructor
    · rintro ⟨hdf, hd, hc⟩
      exact ⟨hdf, hd, (h s _).mpr hc⟩
    · rintro ⟨hdf, hd, hc⟩
      exact ⟨hdf, hd, (h s _).mp hc⟩
  · intro _ _
    rfl

/-- `(φ, D, d)*(𝐁) ≅ (φ, D', d)*(𝐁)` when `D` and `D'` hold for the same elements of `𝐁`. -/
noncomputable def withDomIso (D' : ∀ s, Set (EEq Lg.sig (Vars fun _ : Unit => δ.sortMap s)))
    (B : PartialAlgebra.{u, v, w} Lg.sig)
    (h : ∀ s (b : B (δ.sortMap s)),
      EEq.HoldsAll B (val₁ b) (δ.sortDom s) ↔ EEq.HoldsAll B (val₁ b) (D' s)) :
    δ.derived B ≅ (δ.withDom D').derived B where
  hom :=
    { map := δ.toWithDom h
      map_dom := fun σ a hd => by
        rw [δ.withDom_op_agree h ⟨_, _, σ⟩ a]
        exact hd
      map_op := fun σ a hd =>
        (Part.get_eq_get_of_eq _ _ (δ.withDom_op_agree h ⟨_, _, σ⟩ a)).symm }
  inv :=
    { map := fun s x => ⟨x.1, (h s x.1).mpr x.2⟩
      map_dom := fun σ a hd => by
        have := δ.withDom_op_agree h ⟨_, _, σ⟩ fun j => ⟨(a j).1, (h _ (a j).1).mpr (a j).2⟩
        have hd' : (((δ.withDom D').derived B).op σ
            fun j => δ.toWithDom h _ ⟨(a j).1, (h _ (a j).1).mpr (a j).2⟩).Dom := hd
        rw [this] at hd'
        exact hd'
      map_op := fun {_ s} σ a hd => by
        have := δ.withDom_op_agree h ⟨_, _, σ⟩ fun j => ⟨(a j).1, (h _ (a j).1).mpr (a j).2⟩
        exact Subtype.ext (congrArg (fun z : (δ.withDom D').derived B s => z.1)
          (Part.get_eq_get_of_eq _ hd this)) }
  hom_inv_id := PartialAlgebra.Hom.ext fun _ _ => rfl
  inv_hom_id := PartialAlgebra.Hom.ext fun _ _ => rfl

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

```lean
namespace GenEpDerivor

variable {Sg : EpSignature.{u, v} S} {Lg : EpSignature.{u, v} T} {Og : EpSignature.{u, v} U}

lemma mk_eq {φ : S → T} {D D' : ∀ s, Set (EEq Lg.sig (Vars fun _ : Unit => φ s))}
    {d d' : ∀ {ws : List S} {s : S}, Sg.sig ws s → Term Lg.sig (Vars (φ ∘ ws.get)) (φ s)}
    (hD : D = D') (hd : ∀ {ws : List S} {s : S} (σ : Sg.sig ws s), d σ = d' σ) :
    (⟨φ, D, d⟩ : GenEpDerivor Sg Lg) = ⟨φ, D', d'⟩ := by
  subst hD
  have : @d = @d' := by funext ws s σ; exact hd σ
  subst this
  rfl

lemma comp_isClosed (ε : GenEpDerivor Lg Og) (δ : GenEpDerivor Sg Lg) :
    (ε.comp.{u, v, w} δ).IsClosed.{u, v, w} :=
  fun _ => EpSpec.cn_cn.{u, v, w} Og.toSpec _ _

lemma id_isClosed : (GenEpDerivor.id.{u, v, w} Sg).IsClosed.{u, v, w} :=
  fun _ => EpSpec.cn_cn.{u, v, w} Sg.toSpec _ _

/-- `(𝐞 ∘ 𝐝)*(𝐂)` and `𝐝*(𝐞*(𝐂))` satisfy the same existence equations. -/
lemma holdsAll_comp_derived_iff {ε : GenEpDerivor Lg Og} {δ : GenEpDerivor Sg Lg}
    {C : PartialAlgebra.{u, v, w} Og.sig} (hC : Og.IsAlgebra C)
    (hA : Sg.IsAlgebra (δ.derived (ε.derived C))) {I : Type} {κ : I → S}
    (z : ∀ i, δ.derived (ε.derived C) (κ i)) (H : Set (EEq Sg.sig (Vars κ))) :
    EEq.HoldsAll ((ε.comp.{u, v, w} δ).derived C) (famVal fun i => toComp hC _ (z i)) H ↔
      EEq.HoldsAll (δ.derived (ε.derived C)) (famVal z) H :=
  EEq.holdsAll_famVal_map_of_agree (toComp hC) (toComp_injective hC)
    (fun τ a => comp_op_agree hC hA τ a) z H

/-- `(id_𝚺)*(𝐀)` and `𝐀` satisfy the same existence equations. -/
lemma holdsAll_id_derived_iff {A : PartialAlgebra.{u, v, w} Sg.sig} (hA : Sg.IsAlgebra A)
    {I : Type} {κ : I → S} (z : ∀ i, (GenEpDerivor.id.{u, v, w} Sg).derived A (κ i))
    (H : Set (EEq Sg.sig (Vars κ))) :
    EEq.HoldsAll A (famVal fun i => (z i).1) H ↔
      EEq.HoldsAll ((GenEpDerivor.id.{u, v, w} Sg).derived A) (famVal z) H :=
  EEq.holdsAll_famVal_map_of_agree (A := (GenEpDerivor.id.{u, v, w} Sg).derived A)
    (fun _ x => x.1) (fun _ _ _ hxy => Subtype.ext hxy) (fun τ a => id_op_agree hA τ a) z H

end GenEpDerivor
```

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

lemma Hom.ext {X Y : EpSigGd.{u, v, w}} {f g : Hom X Y} (h : f.der = g.der) : f = g := by
  cases f; cases g; cases h; rfl

noncomputable instance category : Category.{max u v} EpSigGd.{u, v, w} where
  Hom := Hom
  id X := ⟨GenEpDerivor.id.{u, v, w} X.sg, GenEpDerivor.id_isClosed, GenEpDerivor.id_sendsModels⟩
  comp f g := ⟨g.der.comp.{u, v, w} f.der, GenEpDerivor.comp_isClosed _ _,
    GenEpDerivor.comp_sendsModels g.sends f.sends⟩
  id_comp {X Y} f := by
    apply Hom.ext
    obtain ⟨⟨φ, D, d⟩, hcl, hs⟩ := f
    show GenEpDerivor.comp.{u, v, w} ⟨φ, D, d⟩ (GenEpDerivor.id.{u, v, w} X.sg) = ⟨φ, D, d⟩
    refine GenEpDerivor.mk_eq ?_ fun σ => Derivor.lift_app_vars ⟨φ, d⟩ σ
    funext s
    refine EpSpec.eq_of_isClosed.{u, v, w} Y.sg.toSpec (fun _ : Unit => φ s)
      (EpSpec.cn_cn _ _ _) (hcl s) fun C hC a => ?_
    refine (EpSpec.holdsAll_cn_iff _ _ hC _).trans (EEq.holdsAll_union.trans ?_)
    refine ⟨fun h => h.1, fun hD => ⟨hD, ?_⟩⟩
    have hX := hs C hC
    exact (GenEpDerivor.holdsAll_derived_iff (δ := (⟨φ, D, d⟩ : GenEpDerivor X.sg Y.sg)) (B := C)
      (fun _ : Unit => ⟨a (), hD⟩) _).mp
      ((EpSpec.holdsAll_cn_iff X.sg.toSpec _ hX _).mpr EEq.holdsAll_empty)
  comp_id {X Y} f := by
    apply Hom.ext
    obtain ⟨⟨φ, D, d⟩, hcl, hs⟩ := f
    show GenEpDerivor.comp.{u, v, w} (GenEpDerivor.id.{u, v, w} Y.sg) ⟨φ, D, d⟩ = ⟨φ, D, d⟩
    refine GenEpDerivor.mk_eq ?_ fun σ => Derivor.lift_id (d σ)
    funext s
    refine EpSpec.eq_of_isClosed.{u, v, w} Y.sg.toSpec (fun _ : Unit => φ s)
      (EpSpec.cn_cn _ _ _) (hcl s) fun C hC a => ?_
    refine (EpSpec.holdsAll_cn_iff _ _ hC _).trans (EEq.holdsAll_union.trans ?_)
    have hcell := GenEpDerivor.id_cells hC.1 (a ())
    have key := (GenEpDerivor.holdsAll_id_derived_iff hC.1
      (fun _ : Unit => (⟨a (), hcell⟩ : (GenEpDerivor.id.{u, v, w} Y.sg).derived C (φ s))) (D s)).trans
      (GenEpDerivor.holdsAll_derived_iff (δ := GenEpDerivor.id.{u, v, w} Y.sg) (B := C)
        (fun _ : Unit => (⟨a (), hcell⟩ : (GenEpDerivor.id.{u, v, w} Y.sg).derived C (φ s))) (D s))
    exact ⟨fun h => key.mpr h.2, fun h => ⟨hcell, key.mp h⟩⟩
  assoc {X Y Z W} f g h := by
    apply Hom.ext
    show GenEpDerivor.comp.{u, v, w} h.der (GenEpDerivor.comp.{u, v, w} g.der f.der) =
      GenEpDerivor.comp.{u, v, w} (GenEpDerivor.comp.{u, v, w} h.der g.der) f.der
    refine GenEpDerivor.mk_eq ?_ fun σ =>
      (Derivor.lift_comp h.der.toDerivor g.der.toDerivor (f.der.op σ)).symm
    funext s
    refine EpSpec.eq_of_isClosed.{u, v, w} W.sg.toSpec _ (EpSpec.cn_cn _ _ _)
      (EpSpec.cn_cn _ _ _) fun C hC a => ?_
    have hZ := h.sends C hC
    have hY := g.sends _ hZ
    refine (GenEpDerivor.comp_cells_iff (ε := h.der) (δ := g.der.comp.{u, v, w} f.der)
      hC.1 (a ())).trans (Iff.trans ?_ (GenEpDerivor.comp_cells_iff
        (ε := h.der.comp.{u, v, w} g.der) (δ := f.der) hC.1 (a ())).symm)
    constructor
    · rintro ⟨hζ, hεδ⟩
      obtain ⟨hε, hδ⟩ := (GenEpDerivor.comp_cells_iff hZ.1 _).mp hεδ
      exact ⟨(GenEpDerivor.comp_cells_iff (ε := h.der) (δ := g.der) (s := f.der.sortMap s)
          hC.1 _).mpr ⟨hζ, hε⟩,
        (GenEpDerivor.holdsAll_comp_derived_iff hC.1 hY.1
          (fun _ : Unit => ⟨⟨a (), hζ⟩, hε⟩) _).mpr hδ⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨hζ, hε⟩ := (GenEpDerivor.comp_cells_iff (ε := h.der) (δ := g.der)
        (s := f.der.sortMap s) hC.1 _).mp h1
      exact ⟨hζ, (GenEpDerivor.comp_cells_iff hZ.1 _).mpr ⟨hε,
        (GenEpDerivor.holdsAll_comp_derived_iff hC.1 hY.1
          (fun _ : Unit => ⟨⟨a (), hζ⟩, hε⟩) _).mp h2⟩⟩

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

/-- The functor `Alg_𝔤𝔡(𝐝)`, as a morphism of `Cat`. -/
noncomputable def algGdMap {b b' : EpSigGd.{u, v, w}ᵒᵖ} (f : b ⟶ b') :
    Cat.of (EpSpec.EpAlg.{u, v, w} b.unop.sg.toSpec) ⟶ Cat.of (EpSpec.EpAlg.{u, v, w} b'.unop.sg.toSpec) :=
  (f.unop.der.restrict f.unop.sends).toCatHom

/-- The isomorphisms between the functors of equal morphisms send every cell to itself. -/
lemma algGdMap_eqToHom_val {b b' : EpSigGd.{u, v, w}ᵒᵖ} {k k' : b ⟶ b'} (hk : k = k')
    (p : algGdMap k = algGdMap k') (X : EpSpec.EpAlg.{u, v, w} b.unop.sg.toSpec) (s : b'.unop.sorts)
    (x : ((algGdMap k).toFunctor.obj X).1 s) :
    HEq (PartialAlgebra.Hom.map ((eqToHom p).toNatTrans.app X) s x).1 x.1 := by
  subst hk
  rfl

/-- The pseudofunctor `Alg_𝔤𝔡`. -/
noncomputable def algGd :
    Pseudofunctor (LocallyDiscrete EpSigGd.{u, v, w}ᵒᵖ) Cat.{max u w, max u v (w + 1)} :=
  LocallyDiscrete.mkPseudofunctor
    (fun X => Cat.of (EpSpec.EpAlg.{u, v, w} X.unop.sg.toSpec))
    (fun f => algGdMap f)
    (fun X => Cat.Hom.isoMk GenEpDerivor.idIso)
    (fun f g => Cat.Hom.isoMk (GenEpDerivor.compIso f.unop.sends g.unop.sends))
    (by
      intro _ _ _ _ f g h
      ext X
      apply EpSpec.EpAlg.hom_ext
      intro s x
      apply Subtype.ext
      exact (eq_of_heq (algGdMap_eqToHom_val (Category.assoc f g h) _ X s x)).symm)
    (by
      intro _ _ f
      ext X
      apply EpSpec.EpAlg.hom_ext
      intro s x
      apply Subtype.ext
      exact (eq_of_heq (algGdMap_eqToHom_val (Category.id_comp f) _ X s x)).symm)
    (by
      intro _ _ f
      ext X
      apply EpSpec.EpAlg.hom_ext
      intro s x
      apply Subtype.ext
      exact (eq_of_heq (algGdMap_eqToHom_val (Category.comp_id f) _ X s x)).symm)

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
