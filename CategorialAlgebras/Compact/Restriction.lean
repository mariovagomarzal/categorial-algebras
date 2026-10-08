import Stemma
import CategorialAlgebras.Compact.Product

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "Restriction of compact categories" =>

In the compact presentation all the cells live in one set, so truncating a compact category
at some level means keeping a *subset* of its cells: those whose dimension is low enough, that
is, those that are $`u`-cells for every dimension $`u` that is forgotten. On these cells the
sources, targets and compositions of the remaining dimensions are again a compact category.

As for extended categories, the construction is done once, for a strictly monotone mapping
$`e \colon J \to I` that says which dimension of $`I` each dimension of $`J` becomes, and a set
$`U \subseteq I` of forgotten dimensions, each of them above every dimension $`e(j)`.

```lean
universe u u₁ u₂

namespace CategorialAlgebras.Compact

variable {I J : Type} [Preorder I] [Preorder J]

open CategoryStruct
```

# Lemmas on cells

```lean
section Cells

variable {C : Type u} [Category I C]

lemma sc_tg_of_lt {j k : I} (h : j < k) (f : C) : sc k (tg j f) = tg j f := by
  calc sc k (tg j f)
    _ = sc k (sc j (tg j f)) := by rw [PreCategory.sck_tgk_eq_tgk]
    _ = sc j (tg j f) := Category.sck_scj_eq_scj _ h
    _ = tg j f := PreCategory.sck_tgk_eq_tgk j f

lemma cell_of_le {K : Type} [PartialOrder K] {D : Type u} [Category K D] {j k : K} {f : D}
    (hf : cell j f) (h : j ≤ k) : cell k f := by
  rcases h.lt_or_eq with h | h
  · change sc k f = f
    calc sc k f
      _ = sc k (sc j f) := by rw [hf]
      _ = sc j f := Category.sck_scj_eq_scj f h
      _ = f := hf
  · exact h ▸ hf

lemma tg_eq_of_cell {k : I} {f : C} (hf : cell k f) : tg k f = f := by
  calc tg k f
    _ = tg k (sc k f) := by rw [hf]
    _ = sc k f := PreCategory.tgk_sck_eq_sck k f
    _ = f := hf

end Cells
```

# The restriction

:::construction (label := "compact.restrict-category") (central := false) (title := "Restriction to the cells of low dimension")
Let $`C` be a compact category with dimensions in $`I`, let $`e \colon J \to I` be strictly
monotone and let $`U \subseteq I` be a set of dimensions with $`e(j) < u` for every $`j \in J`
and $`u \in U`. The *restriction* of $`C` along $`e` and $`U` is the set
$$`C|_{e,U} = \{ f \in C \mid \mathrm{sc}^{u}(f) = f \text{ for every } u \in U \}`
of the cells that are $`u`-cells for every $`u \in U`, with the compact categorial structure
with dimensions in $`J` given, for $`j \in J`, by $`\mathrm{sc}^{e(j)}`, $`\mathrm{tg}^{e(j)}`
and $`\#^{e(j)}`. These operations do not leave $`C|_{e,U}`: for $`u \in U`, the $`e(j)`-source
and $`e(j)`-target of any cell are $`u`-cells by (2C1), since $`e(j) < u`, and
$`\mathrm{sc}^{u}(g \#^{e(j)} f) = \mathrm{sc}^{u} g \#^{e(j)} \mathrm{sc}^{u} f = g \#^{e(j)} f`
by (2C2). Every axiom of the restriction is an axiom of $`C`.

```lean
/-- The cells of `C` that are `u`-cells for every `u ∈ U`. -/
def Restr (U : Set I) (C : Type u) [CategoryStruct I C] : Type u :=
  {f : C // ∀ u ∈ U, sc u f = f}

variable {e : J → I} {U : Set I}

@[reducible]
def CategoryStruct.restrict (hU : ∀ j, ∀ u ∈ U, e j < u) (C : Type u) [Category I C] :
    CategoryStruct J (Restr U C) where
  sc k x := ⟨sc (e k) x.1, fun u hu => Category.sck_scj_eq_scj x.1 (hU k u hu)⟩
  tg k x := ⟨tg (e k) x.1, fun u hu => sc_tg_of_lt (hU k u hu) x.1⟩
  pcomp k g f := ⟨sc (e k) g.1 = tg (e k) f.1, fun p => ⟨g.1 ♯[e k] f.1 ← p, fun u hu => by
    rw [Category.sck_compj_eq_compj_sck (hU k u hu) p]
    exact congr_comp₁ (f.2 u hu) (g.2 u hu) _⟩⟩
  pcomp_dom := ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

section

variable (hU : ∀ j, ∀ u ∈ U, e j < u) {C : Type u} [Category I C]

lemma restrict_sc_is_tg {k : J} {g f : Restr U C}
    (p : @sc_is_tg J (Restr U C) (CategoryStruct.restrict hU C) k g f) :
    sc_is_tg (e k) g.1 f.1 :=
  congrArg Subtype.val p

end

@[reducible]
def PreCategory.restrict (hU : ∀ j, ∀ u ∈ U, e j < u) (C : Type u) [Category I C] :
    PreCategory J (Restr U C) where
  toCategoryStruct := CategoryStruct.restrict hU C
  sck_sck_eq_sck k f := Subtype.ext (PreCategory.sck_sck_eq_sck (e k) f.1)
  tgk_sck_eq_sck k f := Subtype.ext (PreCategory.tgk_sck_eq_sck (e k) f.1)
  sck_tgk_eq_tgk k f := Subtype.ext (PreCategory.sck_tgk_eq_tgk (e k) f.1)
  tgk_tgk_eq_tgk k f := Subtype.ext (PreCategory.tgk_tgk_eq_tgk (e k) f.1)
  sck_compk_eq_sck p := Subtype.ext (PreCategory.sck_compk_eq_sck (restrict_sc_is_tg hU p))
  tgk_compk_eq_tgk p := Subtype.ext (PreCategory.tgk_compk_eq_tgk (restrict_sc_is_tg hU p))
  compk_sck_eq_id k f := Subtype.ext (PreCategory.compk_sck_eq_id (e k) f.1)
  compk_tgk_eq_id k f := Subtype.ext (PreCategory.compk_tgk_eq_id (e k) f.1)
  assoc p₁ p₂ :=
    Subtype.ext (PreCategory.assoc (restrict_sc_is_tg hU p₁) (restrict_sc_is_tg hU p₂))

@[reducible]
def Category.restrict (he : StrictMono e) (hU : ∀ j, ∀ u ∈ U, e j < u) (C : Type u)
    [Category I C] : Category J (Restr U C) where
  toPreCategory := PreCategory.restrict hU C
  sck_scj_eq_scj f h := Subtype.ext (Category.sck_scj_eq_scj f.1 (he h))
  scj_sck_eq_scj f h := Subtype.ext (Category.scj_sck_eq_scj f.1 (he h))
  scj_tgk_eq_scj f h := Subtype.ext (Category.scj_tgk_eq_scj f.1 (he h))
  tgk_tgj_eq_tgj f h := Subtype.ext (Category.tgk_tgj_eq_tgj f.1 (he h))
  tgj_tgk_eq_tgj f h := Subtype.ext (Category.tgj_tgk_eq_tgj f.1 (he h))
  tgj_sck_eq_tgj f h := Subtype.ext (Category.tgj_sck_eq_tgj f.1 (he h))
  sck_compj_eq_compj_sck h p :=
    Subtype.ext (Category.sck_compj_eq_compj_sck (he h) (restrict_sc_is_tg hU p))
  tgk_compj_eq_compj_tgk h p :=
    Subtype.ext (Category.tgk_compj_eq_compj_tgk (he h) (restrict_sc_is_tg hU p))
  interchange h p₁ p₂ p₃ p₄ :=
    Subtype.ext (Category.interchange (he h) (restrict_sc_is_tg hU p₁)
      (restrict_sc_is_tg hU p₂) (restrict_sc_is_tg hU p₃) (restrict_sc_is_tg hU p₄))
```
:::

:::construction (label := "compact.restrict-functor") (central := false) (title := "Restriction of compact functors")
A compact functor $`F \colon C \to D` sends $`C|_{e,U}` into $`D|_{e,U}`, since it preserves
$`u`-sources, and restricts to a compact functor between the restrictions. More generally, a
compact functor $`F \colon \prod_{l \in L} C_l \to D` restricts to a compact functor
$`\prod_{l \in L} C_l|_{e,U} \to D|_{e,U}`; this is the form needed for the operations of an
algebra.

```lean
variable {e : J → I} {U : Set I}

def Functor.restrict (he : StrictMono e) (hU : ∀ j, ∀ u ∈ U, e j < u)
    {C : Type u₁} [Category I C] {D : Type u₂} [Category I D] (F : Functor I C D) :
    @Functor J _ (Restr U C) (Category.restrict he hU C) (Restr U D)
      (Category.restrict he hU D) :=
  letI := Category.restrict he hU C
  letI := Category.restrict he hU D
  { map := fun x => ⟨F x.1, fun u hu => by rw [← F.map_sc_eq_sc_map, x.2 u hu]⟩
    map_sc_eq_sc_map := fun k x => Subtype.ext (F.map_sc_eq_sc_map (e k) x.1)
    map_tg_eq_tg_map := fun k x => Subtype.ext (F.map_tg_eq_tg_map (e k) x.1)
    map_comp_eq_comp_map := fun p =>
      Subtype.ext (F.map_comp_eq_comp_map (restrict_sc_is_tg hU p)) }

def Functor.restrictPi (he : StrictMono e) (hU : ∀ j, ∀ u ∈ U, e j < u)
    {L : Type} {C : L → Type u₁} [∀ l, Category I (C l)] {D : Type u₂} [Category I D]
    (F : Functor I ((l : L) → C l) D) :
    @Functor J _ ((l : L) → Restr U (C l))
      (@Category.pi J L (fun l => Restr U (C l)) _ fun l => Category.restrict he hU (C l))
      (Restr U D) (Category.restrict he hU D) :=
  letI := fun l => Category.restrict he hU (C l)
  letI := Category.restrict he hU D
  { map := fun x => ⟨F (fun l => (x l).1), fun u hu => by
      rw [← F.map_sc_eq_sc_map]
      exact congrArg F (funext fun l => (x l).2 u hu)⟩
    map_sc_eq_sc_map := fun k x => Subtype.ext (F.map_sc_eq_sc_map (e k) (fun l => (x l).1))
    map_tg_eq_tg_map := fun k x => Subtype.ext (F.map_tg_eq_tg_map (e k) (fun l => (x l).1))
    map_comp_eq_comp_map := fun {k f g} p =>
      Subtype.ext (F.map_comp_eq_comp_map (k := e k) (f := fun l => (f l).1)
        (g := fun l => (g l).1)
        (funext fun l => restrict_sc_is_tg hU (pi_sc_is_tg.mp p l))) }
```
:::

```lean
end CategorialAlgebras.Compact
```
