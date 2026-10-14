import Stemma
import CategorialAlgebras.GenEpDerivor

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "Sending models to models" =>

A generalized ep-derivor $`\mathbf{d}` from $`\mathbf{\Sigma}` to $`\mathbf{\Lambda}` determines a
functor $`\mathbf{d}^{\ast}_{\mathfrak{gd}}` on all the partial $`\Lambda`-algebras. Whether it
sends the models of an ep-specification $`(\mathbf{\Lambda}, \mathcal{F})` to models of an
ep-specification $`(\mathbf{\Sigma}, \mathcal{E})` is a property of $`\mathbf{d}`, which this
document characterizes syntactically, by the conditions (GEP1) and (GEP2). It follows
Subsection `SEpModels` of the draft.

```lean
universe u v w u' v' z z'

namespace CategorialAlgebras

open CategoryTheory Signature

variable {S : Type u} {T : Type u'}

namespace GenEpDerivor

variable {Sg : EpSignature.{u, v} S} {Lg : EpSignature.{u', v'} T}
```

# Sending models to models

:::definition (label := "gen-ep-derivor.sends-models") (central := false) (title := "Sending models to models")
Let $`\mathbf{d}` be a generalized ep-derivor from $`\mathbf{\Sigma}` to $`\mathbf{\Lambda}`, and
$`(\mathbf{\Sigma}, \mathcal{E})` and $`(\mathbf{\Lambda}, \mathcal{F})` ep-specifications.
$`\mathbf{d}^{\ast}_{\mathfrak{gd}}` *sends models of* $`(\mathbf{\Lambda}, \mathcal{F})` *to
models of* $`(\mathbf{\Sigma}, \mathcal{E})` if, for every model $`\mathbf{B}` of
$`(\mathbf{\Lambda}, \mathcal{F})`, $`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})` is a model of
$`(\mathbf{\Sigma}, \mathcal{E})`. In this case, $`\mathbf{d}^{\ast}_{\mathfrak{gd}}` birestricts to
a functor from $`\mathsf{epAlg}(\mathbf{\Lambda}, \mathcal{F})` to
$`\mathsf{epAlg}(\mathbf{\Sigma}, \mathcal{E})`. For $`\mathcal{E} = \mathcal{F} = \varnothing`, we
say that $`\mathbf{d}^{\ast}_{\mathfrak{gd}}` *sends* $`\mathbf{\Lambda}`*-algebras to*
$`\mathbf{\Sigma}`*-algebras*. The models range over the partial algebras with carriers in a
fixed universe.

```lean
def SendsModels (d : GenEpDerivor Sg Lg) {V : S → Type z} (E : Set (QEEq Sg.sig V))
    {W : T → Type z'} (F : Set (QEEq Lg.sig W)) : Prop :=
  ∀ B : PartialAlgebra.{u', v', w} Lg.sig, Lg.IsModel F B → Sg.IsModel E (d.derived B)

def restrict (d : GenEpDerivor Sg Lg) {V : S → Type z} {E : Set (QEEq Sg.sig V)}
    {W : T → Type z'} {F : Set (QEEq Lg.sig W)} (h : d.SendsModels.{u, v, w} E F) :
    EpAlg.{u', v', w} Lg F ⥤ EpAlg.{u, v, w} Sg E where
  obj B := ⟨d.derived B.1, h B.1 B.2⟩
  map f := d.derivedMap f
  map_id _ := rfl
  map_comp _ _ := rfl
```
:::

# The conditions (GEP1) and (GEP2)

The condition (GEP1) says that the translated domain conditions of every operation symbol
$`\sigma \in \Sigma_{\mathbf{s}, s}` guarantee, in the models of $`(\mathbf{\Lambda}, \mathcal{F})`,
that $`d(\sigma)` is defined and takes its values in the domain of $`s`. The consequence
operator $`\mathrm{Cn}` is that of $`(\mathbf{\Lambda}, \mathcal{F})` (see
{name}`EpSignature.Cn`).

```lean
/-- A valuation of the variables of `↓φ*(𝐬)` as a family. -/
lemma val_eq {φ : S → T} {ws : List S} {B : T → Type w} (c : ∀ t, WordVar φ ws t → B t) :
    WordVar.val (φ := φ) (B := B) (fun j => c _ ⟨j, rfl⟩) = c := by
  funext t v
  obtain ⟨j, h⟩ := v
  subst h
  rfl

/-- The family of `𝐝*(B)` determined by a valuation of `↓φ*(𝐬)` that satisfies `D_𝐬`. -/
def ofVal (d : GenEpDerivor Sg Lg) {B : PartialAlgebra.{u', v', w} Lg.sig} {ws : List S}
    (c : ∀ t, WordVar d.sortMap ws t → B t) (hc : EEq.HoldsAll B c (d.domWord ws)) :
    Arity (d.derived B) ws :=
  fun j => ⟨c _ ⟨j, rfl⟩, (d.holdsAll_domWord B _).1 ((val_eq c).symm ▸ hc) j⟩

lemma famVal_ofVal (d : GenEpDerivor Sg Lg) {B : PartialAlgebra.{u', v', w} Lg.sig}
    {ws : List S} (c : ∀ t, WordVar d.sortMap ws t → B t) (hc : EEq.HoldsAll B c (d.domWord ws)) :
    d.famVal (d.ofVal c hc) = c :=
  val_eq c
```

:::definition (label := "gen-ep-derivor.gep1") (central := false) (title := "The condition (GEP1)")
A generalized ep-derivor $`\mathbf{d} = (\varphi, D, d)` satisfies (GEP1) for
$`(\mathbf{\Lambda}, \mathcal{F})` if, for every $`\sigma \in \Sigma_{\mathbf{s}, s}`,
$$`\{(d(\sigma), d(\sigma))\} \cup d(\sigma)^{\sharp}[D_s] \subseteq \mathrm{Cn}^{\mathbf{\Lambda}, \mathcal{F}}_{\downarrow\varphi^{\star}(\mathbf{s})}\left(D_{\mathbf{s}} \cup \mathrm{tr}_{\mathbf{d}}[\mathrm{def}^{\mathbf{\Sigma}}(\sigma)]\right).`

```lean
/-- The conditions (GEP1). -/
def GEP1 (d : GenEpDerivor Sg Lg) {W : T → Type z'} (F : Set (QEEq Lg.sig W)) : Prop :=
  ∀ {ws : List S} {s : S} (σ : Sg.sig ws s),
    insert (EEq.defined (d.op σ))
        (EEq.subst (WordVar.single (F := fun t => Term Lg.sig (WordVar d.sortMap ws) t) (d.op σ))
          '' d.dom s) ⊆
      Lg.Cn.{u', v', w} F (WordVar d.sortMap ws)
        (d.domWord ws ∪ d.trSet d.Dom d.wordVar (Sg.defn σ))
```
:::

The condition (GEP2) translates the $`\mathrm{QE}`$-equations of $`\mathcal{E}`. The draft renames
the variables of each equation to those of a word $`\mathbf{s}` and translates them along
$`d^{\sharp}`. The library keeps the variables $`V` of the equations and translates each
$`x \in V_s` to a variable of sort $`\varphi(s)`: the variables of $`V` *read through*
$`\varphi` are the pairs $`(s, x)` with $`\varphi(s) = t`, and $`D_V` states, for each of them,
the domain of $`s`. This avoids the renaming, which may change the algebras in which a
$`\mathrm{QE}`$-equation holds when some carrier is empty: a valuation of all the variables of
$`V` need not exist although one of the variables that occur does.

:::definition (label := "gen-ep-derivor.pull-var") (central := false) (title := "Variables read through a mapping of sorts")
Let $`\mathbf{d} = (\varphi, D, d)` be a generalized ep-derivor and $`X` an $`S`-sorted set.
The $`T`-sorted set of the variables of $`X` read through $`\varphi` has, as variables of sort
$`t`, the pairs $`(s, x)` with $`x \in X_s` and $`\varphi(s) = t`. The variable $`x \in X_s` is
translated to the variable $`(s, x)`, and $`D_X` is the set of the equations of $`D_s`,
stated for $`(s, x)`, for all $`s` and $`x \in X_s`.

```lean
/-- The variables of `X` read through `φ`: the pairs `(s, x)` with `x ∈ X_s` and `φ(s) = t`. -/
def PullVar (φ : S → T) (X : S → Type z) (t : T) : Type (max u z) :=
  {p : (s : S) × X s // φ p.1 = t}

/-- The variable `(s, x)` of `X` read through `φ`. -/
def pullVar (d : GenEpDerivor Sg Lg) (X : S → Type z) :
    ∀ s, X s → Term Lg.sig (PullVar d.sortMap X) (d.sortMap s) :=
  fun s x => .var ⟨⟨s, x⟩, rfl⟩

/-- `D_X`: the domains of the sorts of the variables of `X`. -/
def domVar (d : GenEpDerivor Sg Lg) (X : S → Type z) : Set (EEq Lg.sig (PullVar d.sortMap X)) :=
  ⋃ s, ⋃ x : X s,
    EEq.subst (WordVar.single (F := fun t => Term Lg.sig (PullVar d.sortMap X) t)
      (d.pullVar X s x)) '' d.dom s
```
:::

```lean
lemma holdsAll_domVar (d : GenEpDerivor Sg Lg) {B : PartialAlgebra.{u', v', w} Lg.sig}
    {X : S → Type z} (c : ∀ t, PullVar d.sortMap X t → B t) :
    EEq.HoldsAll B c (d.domVar X) ↔
      ∀ s x, EEq.HoldsAll B (WordVar.single (F := fun t => B t) (c _ ⟨⟨s, x⟩, rfl⟩))
        (d.dom s) := by
  simp only [domVar, holdsAll_iUnion]
  refine forall_congr' fun s => forall_congr' fun x => ?_
  have hx : ((d.pullVar X s x).eval B c).Dom := trivial
  rw [EEq.holdsAll_subst B _ c (eval_single B c _ hx), eval_single_get B c _ hx]
  rfl

/-- The valuation of `X` in `𝐝*(B)` determined by a valuation of `X` read through `φ`. -/
def ofPull (d : GenEpDerivor Sg Lg) {B : PartialAlgebra.{u', v', w} Lg.sig} {X : S → Type z}
    (c : ∀ t, PullVar d.sortMap X t → B t) (hc : EEq.HoldsAll B c (d.domVar X)) :
    ∀ s, X s → d.derived B s :=
  fun s x => ⟨c _ ⟨⟨s, x⟩, rfl⟩, (d.holdsAll_domVar c).1 hc s x⟩

/-- The valuation of `X` read through `φ` determined by a valuation of `X` in `𝐝*(B)`. -/
def toPull (d : GenEpDerivor Sg Lg) {B : PartialAlgebra.{u', v', w} Lg.sig} {X : S → Type z}
    (a : ∀ s, X s → d.derived B s) : ∀ t, PullVar d.sortMap X t → B t :=
  fun _ p => p.2 ▸ (a p.1.1 p.1.2).1

lemma holdsAll_toPull (d : GenEpDerivor Sg Lg) {B : PartialAlgebra.{u', v', w} Lg.sig}
    {X : S → Type z} (a : ∀ s, X s → d.derived B s) :
    EEq.HoldsAll B (d.toPull a) (d.domVar X) :=
  (d.holdsAll_domVar _).2 fun s x => (a s x).2

lemma pullVar_mem (d : GenEpDerivor Sg Lg) {B : PartialAlgebra.{u', v', w} Lg.sig}
    {X : S → Type z} (a : ∀ s, X s → d.derived B s) :
    ∀ s x, (a s x).1 ∈ (d.pullVar X s x).eval B (d.toPull a) :=
  fun _ _ => Part.mem_some _

lemma pullVar_mem_ofPull (d : GenEpDerivor Sg Lg) {B : PartialAlgebra.{u', v', w} Lg.sig}
    {X : S → Type z} (c : ∀ t, PullVar d.sortMap X t → B t) (hc : EEq.HoldsAll B c (d.domVar X)) :
    ∀ s x, (d.ofPull c hc s x).1 ∈ (d.pullVar X s x).eval B c :=
  fun _ _ => Part.mem_some _

lemma holdsAll_singleton {Sig : Signature.{u', v'} T} {Y : T → Type z}
    {A : PartialAlgebra.{u', v', w} Sig} {c : ∀ t, Y t → A t} {e : EEq Sig Y} :
    EEq.HoldsAll A c {e} ↔ e.Holds A c :=
  ⟨fun h => h _ rfl, fun h _ he => he ▸ h⟩
```

:::definition (label := "gen-ep-derivor.gep2") (central := false) (title := "The condition (GEP2)")
A generalized ep-derivor $`\mathbf{d}` satisfies (GEP2) for $`(\mathbf{\Sigma}, \mathcal{E})` and
$`(\mathbf{\Lambda}, \mathcal{F})` if, for every $`\mathrm{QE}`$-equation
$`\bigwedge_{i \in m} e_i \longrightarrow e` of $`\mathcal{E}`, with variables in $`V`,
$$`\mathrm{tr}_{\mathbf{d}}(e) \subseteq \mathrm{Cn}^{\mathbf{\Lambda}, \mathcal{F}}\left(D_V \cup \textstyle\bigcup_{i \in m} \mathrm{tr}_{\mathbf{d}}(e_i)\right),`
where the translations are taken along the variables of $`V` read through $`\varphi`.

```lean
/-- The conditions (GEP2). -/
def GEP2 (d : GenEpDerivor Sg Lg) {V : S → Type z} (E : Set (QEEq Sg.sig V)) {W : T → Type z'}
    (F : Set (QEEq Lg.sig W)) : Prop :=
  ∀ q ∈ E, d.trSet d.Dom (d.pullVar V) {q.conclusion} ⊆
    Lg.Cn.{u', v', w} F (PullVar d.sortMap V)
      (d.domVar V ∪ d.trSet d.Dom (d.pullVar V) {e | e ∈ q.premises})
```
:::

:::proposition (label := "gen-ep-derivor.sends-models-iff") (central := false) (title := "Syntactic criterion")
Let $`\mathbf{d}` be a generalized ep-derivor from $`\mathbf{\Sigma}` to $`\mathbf{\Lambda}`, and
$`(\mathbf{\Sigma}, \mathcal{E})` and $`(\mathbf{\Lambda}, \mathcal{F})` ep-specifications. Then:

1. (GEP1) holds if and only if $`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})` is a
   $`\mathbf{\Sigma}`-algebra for every model $`\mathbf{B}` of $`(\mathbf{\Lambda}, \mathcal{F})`;
2. (GEP2) holds if and only if every equation of $`\mathcal{E}` holds in
   $`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})` for every model $`\mathbf{B}` of
   $`(\mathbf{\Lambda}, \mathcal{F})`;
3. consequently, $`\mathbf{d}^{\ast}_{\mathfrak{gd}}` sends models of $`(\mathbf{\Lambda}, \mathcal{F})`
   to models of $`(\mathbf{\Sigma}, \mathcal{E})` if and only if (GEP1) and (GEP2) hold.

```lean
theorem gep1_iff (d : GenEpDerivor Sg Lg) {W : T → Type z'} (F : Set (QEEq Lg.sig W)) :
    d.GEP1.{u, v, w} F ↔
      ∀ B : PartialAlgebra.{u', v', w} Lg.sig, Lg.IsModel F B → Sg.IsAlgebra (d.derived B) := by
  constructor
  · intro h B hB
    rw [isAlgebra_derived_iff]
    intro ws s σ b hb
    have hc : EEq.HoldsAll B (d.famVal b) (d.domWord ws ∪ d.trSet d.Dom d.wordVar (Sg.defn σ)) :=
      holdsAll_union.2 ⟨(d.holdsAll_domWord B _).2 fun j => (b j).2,
        (d.holdsAll_translation B b _).1 hb⟩
    have hd : ((d.op σ).eval B (d.famVal b)).Dom :=
      (h σ (Set.mem_insert _ _) B hB _ hc).1
    refine ⟨hd, ?_⟩
    have := (EEq.holdsAll_subst B _ _ (eval_single B _ (d.op σ) hd) (d.dom s)).1
      fun e he => h σ (Set.mem_insert_of_mem _ he) B hB _ hc
    rwa [eval_single_get] at this
  · intro h ws s σ e he A hA c hc
    obtain ⟨hw, ht⟩ := holdsAll_union.1 hc
    have hb := (d.holdsAll_translation A (d.ofVal c hw) (Sg.defn σ)).2
      ((d.famVal_ofVal c hw).symm ▸ ht)
    obtain ⟨hd, hD⟩ := (isAlgebra_derived_iff d A).1 (h A hA) σ _ hb
    revert hd hD
    rw [famVal_ofVal]
    intro hd hD
    rcases he with rfl | he
    · exact ⟨hd, hd, rfl⟩
    · rw [← eval_single_get A c (d.op σ) hd, ← EEq.holdsAll_subst] at hD
      exact hD e he

theorem gep2_iff (d : GenEpDerivor Sg Lg) {V : S → Type z} (E : Set (QEEq Sg.sig V))
    {W : T → Type z'} (F : Set (QEEq Lg.sig W)) :
    d.GEP2.{u, v, w} E F ↔
      ∀ B : PartialAlgebra.{u', v', w} Lg.sig, Lg.IsModel F B →
        ∀ q ∈ E, q.Holds (d.derived B) := by
  constructor
  · intro h B hB q hq a ha
    have hc : EEq.HoldsAll B (d.toPull a)
        (d.domVar V ∪ d.trSet d.Dom (d.pullVar V) {e | e ∈ q.premises}) :=
      holdsAll_union.2 ⟨d.holdsAll_toPull a,
        (d.holdsAll_derived B _ _ a (d.pullVar_mem a) _).1 ha⟩
    have := (d.holdsAll_derived B _ _ a (d.pullVar_mem a) {q.conclusion}).2
      fun e he => h q hq he B hB _ hc
    exact holdsAll_singleton.1 this
  · intro h q hq e he A hA c hc
    obtain ⟨hw, hp⟩ := holdsAll_union.1 hc
    have hprem := (d.holdsAll_derived A _ _ _ (d.pullVar_mem_ofPull c hw) _).2 hp
    have hcon := h A hA q hq (d.ofPull c hw) hprem
    exact (d.holdsAll_derived A _ _ _ (d.pullVar_mem_ofPull c hw) {q.conclusion}).1
      (holdsAll_singleton.2 hcon) e he

theorem sendsModels_iff (d : GenEpDerivor Sg Lg) {V : S → Type z} (E : Set (QEEq Sg.sig V))
    {W : T → Type z'} (F : Set (QEEq Lg.sig W)) :
    d.SendsModels.{u, v, w} E F ↔ d.GEP1.{u, v, w} F ∧ d.GEP2.{u, v, w} E F := by
  rw [gep1_iff, gep2_iff]
  exact ⟨fun h => ⟨fun B hB => (h B hB).1, fun B hB => (h B hB).2⟩,
    fun h B hB => ⟨h.1 B hB, h.2 B hB⟩⟩
```
:::

:::proof (of := "gen-ep-derivor.sends-models-iff")
Let $`\mathbf{B}` be a model of $`(\mathbf{\Lambda}, \mathcal{F})`. The valuations $`c` of
$`\downarrow\varphi^{\star}(\mathbf{s})` in $`\mathbf{B}` with $`\mathbf{B} \models D_{\mathbf{s}}[c]` are,
by Proposition {name}`GenEpDerivor.holdsAll_domWord_iff`, the families of
$`(B_{(\varphi, D)})_{\mathbf{s}}`. For such a family, by Lemma {name}`GenEpDerivor.translation`,
$`\mathbf{B} \models \mathrm{tr}_{\mathbf{d}}[\mathrm{def}^{\mathbf{\Sigma}}(\sigma)][c]` if and only if
$`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B}) \models \mathrm{def}^{\mathbf{\Sigma}}(\sigma)[c]`, and, by
Corollary {name}`EEq.holdsAll_subst`, $`\mathbf{B}` satisfies
$`\{(d(\sigma), d(\sigma))\} \cup d(\sigma)^{\sharp}[D_s]` under $`c` if and only if
$`d(\sigma)^{\mathbf{B}}[c]` is defined and in $`(B_{(\varphi, D)})_s`. Hence (GEP1) says that the
condition of Proposition {name}`GenEpDerivor.isAlgebra_derived_iff` holds for every model. In the
same way, the valuations of $`V` read through $`\varphi` that satisfy $`D_V` are the valuations
of $`V` in $`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})`, and, by
Lemma {name}`GenEpDerivor.holdsAll_derived`, (GEP2) says that, under each of them, if the
premises of an equation of $`\mathcal{E}` hold in $`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})`,
then so does its conclusion. The third statement combines the first two.
:::

# Remarks

The domain of $`\sigma` in $`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})` is not part of the data: it
is the translation of its domain conditions, which, by (GEP1), are only required to guarantee
that the derived operation is defined. It may therefore be smaller than the domain of
$`d(\sigma)^{\mathbf{B}}`, as for the discretization functors. Moreover,
$`\mathbf{d}^{\ast}_{\mathfrak{gd}}` may only send the models of some ep-specification to models
of another: the domains of the sorts of the graduation derivor are only preserved by the derived
operations in the models of the axioms of $`n`-categories.

When $`\mathbf{\Sigma}` and $`\mathbf{\Lambda}` are many-sorted signatures, regarded as
ep-signatures with no domain conditions, every derivor is a generalized ep-derivor with empty
domains, which sends (total) $`\Lambda`-algebras to $`\Sigma`-algebras: in
$`\mathbf{d}^{\ast}_{\mathfrak{gd}}(\mathbf{B})`, which has carriers $`B_{\varphi}`, every
$`\sigma` is interpreted as the derived operation $`d(\sigma)^{\mathbf{B}}`.

```lean
lemma eval_dom_of_total {Sig : Signature.{u, v} S} {X : S → Type z}
    {A : PartialAlgebra.{u, v, w} Sig} (hA : ∀ {ws : List S} {s : S} (σ : Sig ws s) a, (A.op σ a).Dom)
    (c : ∀ s, X s → A s) {s : S} (P : Term Sig X s) : (P.eval A c).Dom := by
  induction P with
  | var x => trivial
  | app σ ts ih => exact ⟨ih, hA σ _⟩
```

:::definition (label := "gen-ep-derivor.of-derivor") (central := false) (title := "A derivor as a generalized ep-derivor")
A derivor $`(\varphi, d)` from $`(S, \Sigma)` to $`(T, \Lambda)` is the generalized ep-derivor
$`(\varphi, \varnothing, d)` between the ep-signatures $`(S, \Sigma, \varnothing)` and
$`(T, \Lambda, \varnothing)`.

```lean
/-- A derivor as a generalized ep-derivor between signatures, with empty domains. -/
def ofDerivor {Sig : Signature.{u, v} S} {Lam : Signature.{u', v'} T} (d : Derivor Sig Lam) :
    GenEpDerivor (EpSignature.ofSignature Sig) (EpSignature.ofSignature Lam) where
  toDerivor := d
  dom _ := ∅
```
:::

:::proposition (label := "gen-ep-derivor.of-derivor-algebra") (central := false) (title := "Derivors send algebras to algebras")
For every derivor $`(\varphi, d)` and every (total) $`\Lambda`-algebra $`\mathbf{B}`,
$`(\varphi, \varnothing, d)^{\ast}_{\mathfrak{gd}}(\mathbf{B})` is a (total) $`\Sigma`-algebra.

```lean
theorem ofDerivor_isAlgebra {Sig : Signature.{u, v} S} {Lam : Signature.{u', v'} T}
    (d : Derivor Sig Lam) {B : PartialAlgebra.{u', v', w} Lam}
    (hB : (EpSignature.ofSignature Lam).IsAlgebra B) :
    (EpSignature.ofSignature Sig).IsAlgebra ((ofDerivor d).derived B) := by
  refine (isAlgebra_derived_iff (ofDerivor d) B).2 fun σ b _ => ?_
  have htot : ∀ {ws : List T} {s : T} (σ : Lam ws s) (a : Arity B ws), (B.op σ a).Dom :=
    (EpSignature.isAlgebra_ofSignature_iff Lam B).1 hB
  exact ⟨eval_dom_of_total htot _ _, fun _ he => he.elim⟩
```
:::

:::proof (of := "gen-ep-derivor.of-derivor-algebra")
By Proposition {name}`GenEpDerivor.isAlgebra_derived_iff`, it suffices that $`d(\sigma)` is
defined at every family of $`\mathbf{B}` and that its value is in the domain of $`s`. The first
holds because every term is defined in a total algebra, and the second because the domains are
empty.
:::

```lean
end GenEpDerivor

end CategorialAlgebras
```
