import CategorialAlgebras.HepDerivor.Category
import CategorialAlgebras.Homogeneous.Signature
import CategorialAlgebras.Heterogeneous.Signature

/-!
# The generalized hep-derivors of a change of signature

A derivor $\mathbf{c}=(\varphi,c)$ from $\Sigma$ to $\Lambda$ determines, in every type of
dimensions, a generalized hep-derivor $\mathbf{c}^{(n)}$ between the homogeneous categorial
signatures and a generalized hep-derivor $\mathbf{c}^{\mathrm{htg}(n)}$ between the
heterogeneous ones. Both have empty domains, translate the original operation symbols by
means of $c$ and leave the categorial structure unchanged.

The terms of $\Lambda$ are regarded as terms of the categorial signatures by the inclusion
derivors $\boldsymbol{\iota}$ and $\boldsymbol{\iota}_k$; the latter sends $P$ to $P_k$,
replacing every operation symbol $\tau$ by its copy $\tau_k$. Translations along a derivor
commute with these inclusions, and hence the assignments $\mathbf{c}\mapsto\mathbf{c}^{(n)}$
and $\mathbf{c}\mapsto\mathbf{c}^{\mathrm{htg}(n)}$ preserve compositions and identities:
they are functors from many-sorted signatures and derivors to hierarchical signatures and
generalized hep-derivors.
-/

universe i u u' u'' v v' v'' w x y

namespace CategorialAlgebras

open CategoryTheory

namespace Derivor

variable {S : Type u} {T : Type u'} {sig : Signature.{u, v} S} {tau : Signature.{u', v'} T}

/-- Translations along equal derivors, with corresponding assignments of the variables,
are equal. The equality is heterogeneous since the sort maps need not be definitionally
equal. -/
theorem translate_heq {c c' : Derivor sig tau} (h : c = c') {X : S → Type w}
    {Y : T → Type x} (f : ∀ s, X s → Term tau Y (c.sortMap s))
    (f' : ∀ s, X s → Term tau Y (c'.sortMap s)) (hf : HEq f f') {s} (P : Term sig X s) :
    HEq (c.translate f P) (c'.translate f' P) := by
  subst h
  cases hf
  rfl

end Derivor

namespace ChangeOfSignature

variable {S : Type u} {T : Type u'} {U : Type u''}
variable {sig : Signature.{u, v} S} {tau : Signature.{u', v'} T} {ups : Signature.{u'', v''} U}

/-! ## The inclusions of the original terms -/

/-- The homogeneous inclusion derivor, which regards every operation symbol of $\Lambda$ as
an operation symbol of the homogeneous categorial signature. -/
def homogeneousInclusion (I : Type i) (tau : Signature.{u', v'} T) :
    Derivor tau (Homogeneous.Symbol I tau) where
  sortMap := id
  image τ := .app (.base τ) (fun j => .var (Word.position _ j))

/-- The variable at a position of a word, regarded as the variable at the same position of
the word placed in dimension $k$. -/
def dimensionPosition {I : Type i} (k : I) {R : Type u} (φ : R → T) (a : List R) :
    ∀ t, Word.MappedVariables φ a t →
      Word.MappedVariables (fun p : I × R => (p.1, φ p.2)) (Heterogeneous.dimensionWord k a)
        (k, t) :=
  fun _ x => ⟨⟨x.val.val, by
    simpa only [Heterogeneous.dimensionWord, List.length_map] using x.val.isLt⟩, by
      obtain ⟨j, h⟩ := x
      subst h
      simp [Heterogeneous.dimensionWord, List.get_eq_getElem]⟩

/-- The heterogeneous inclusion derivor at dimension $k$, which sends every operation
symbol $\tau$ of $\Lambda$ to its copy $\tau_k$. -/
def heterogeneousInclusion (I : Type i) [Preorder I] (k : I) (tau : Signature.{u', v'} T) :
    Derivor tau (Heterogeneous.Symbol I tau) where
  sortMap t := (k, t)
  image {a _} τ := .app (.base k τ) (fun q => .var ⟨⟨q.val, by
      simpa only [Heterogeneous.dimensionWord, List.length_map] using q.isLt⟩, by
    simp [Heterogeneous.dimensionWord, List.get_eq_getElem]⟩)

/-- The term $P$ of $\Lambda$ regarded as a term of the homogeneous categorial signature. -/
abbrev homogeneousTerm (I : Type i) {R : Type u} {φ : R → T} {a : List R} {t}
    (P : Term tau (Word.MappedVariables φ a) t) :
    Term (Homogeneous.Symbol I tau) (Word.MappedVariables φ a) t :=
  (homogeneousInclusion I tau).translate ((homogeneousInclusion I tau).positionMap φ a) P

/-- The term $P_k$ of the heterogeneous categorial signature, obtained from a term $P$ of
$\Lambda$ by replacing every operation symbol $\tau$ by $\tau_k$. -/
abbrev heterogeneousTerm (I : Type i) [Preorder I] (k : I) {R : Type u} {φ : R → T}
    {a : List R} {t} (P : Term tau (Word.MappedVariables φ a) t) :
    Term (Heterogeneous.Symbol I tau)
      (Word.MappedVariables (fun p : I × R => (p.1, φ p.2)) (Heterogeneous.dimensionWord k a))
      (k, t) :=
  (heterogeneousInclusion I k tau).translate
    (fun t x => .var (dimensionPosition k φ a t x)) P

/-! ## The derivors of a change of signature -/

/-- The derivor underlying $\mathbf{c}^{(n)}$: original symbols are translated by $c$, and
sources, targets and compositions are sent to those of the translated sort. -/
def homogeneousDerivor (I : Type i) (c : Derivor sig tau) :
    Derivor (Homogeneous.Symbol I sig) (Homogeneous.Symbol I tau) where
  sortMap := c.sortMap
  image
    | .base σ => homogeneousTerm I (c.image σ)
    | .source k s => Homogeneous.unary (.source k (c.sortMap s))
        (.var (Word.mappedVariable c.sortMap _ 0))
    | .target k s => Homogeneous.unary (.target k (c.sortMap s))
        (.var (Word.mappedVariable c.sortMap _ 0))
    | .comp k s => Homogeneous.binary k (.var (Word.mappedVariable c.sortMap [s, s] 0))
        (.var (Word.mappedVariable c.sortMap [s, s] 1))

/-- The homogeneous categorial derivor $\mathbf{c}^{(n)}=(\varphi,c^{(n)},\varnothing)$
determined by a derivor, with empty domains. -/
def homogeneous (I : Type i) (c : Derivor sig tau) :
    GeneralizedHepDerivor (Homogeneous.hepSignature I sig) (Homogeneous.hepSignature I tau) where
  toDerivor := homogeneousDerivor I c
  domain _ := ⊥

/-- The map of sorts $(k,s)\mapsto(k,\varphi(s))$ of the heterogeneous derivor. -/
def heterogeneousSortMap {I : Type i} (c : Derivor sig tau) (p : I × S) : I × T :=
  (p.1, c.sortMap p.2)

/-- The derivor underlying $\mathbf{c}^{\mathrm{htg}(n)}$: every $\sigma_k$ is sent to
$c(\sigma)_k$, and sources, targets, identities and compositions are sent to those of the
translated sort. -/
def heterogeneousDerivor (I : Type i) [Preorder I] (c : Derivor sig tau) :
    Derivor (Heterogeneous.Symbol I sig) (Heterogeneous.Symbol I tau) where
  sortMap := heterogeneousSortMap c
  image
    | .base k σ => heterogeneousTerm I k (c.image σ)
    | .source h s => Heterogeneous.unary (.source h (c.sortMap s))
        (.var (Word.mappedVariable (heterogeneousSortMap c) _ 0))
    | .target h s => Heterogeneous.unary (.target h (c.sortMap s))
        (.var (Word.mappedVariable (heterogeneousSortMap c) _ 0))
    | .identity h s => Heterogeneous.unary (.identity h (c.sortMap s))
        (.var (Word.mappedVariable (heterogeneousSortMap c) _ 0))
    | @Heterogeneous.Symbol.comp _ _ _ _ _ k h s =>
        Heterogeneous.binary h
          (.var (Word.mappedVariable (heterogeneousSortMap c) [(k, s), (k, s)] 0))
          (.var (Word.mappedVariable (heterogeneousSortMap c) [(k, s), (k, s)] 1))

/-- The heterogeneous categorial derivor
$\mathbf{c}^{\mathrm{htg}(n)}=(\varphi^{\mathrm{htg}(n)},c^{\mathrm{htg}(n)},\varnothing)$
determined by a derivor, with empty domains. -/
def heterogeneous (I : Type i) [Preorder I] (c : Derivor sig tau) :
    GeneralizedHepDerivor (Heterogeneous.hepSignature I sig)
      (Heterogeneous.hepSignature I tau) where
  toDerivor := heterogeneousDerivor I c
  domain _ := ⊥

/-- The homogeneous derivor of a change of signature has empty domains. -/
@[simp] theorem homogeneous_domain (I : Type i) (c : Derivor sig tau) (s : S) :
    (homogeneous I c).domain s = ⊥ := rfl

/-- The heterogeneous derivor of a change of signature has empty domains. -/
@[simp] theorem heterogeneous_domain (I : Type i) [Preorder I] (c : Derivor sig tau)
    (p : I × S) : (heterogeneous I c).domain p = ⊥ := rfl

/-- The sort map of the homogeneous derivor of a change of signature. -/
@[simp] theorem homogeneous_sortMap (I : Type i) (c : Derivor sig tau) :
    (homogeneous I c).sortMap = c.sortMap := rfl

/-- The sort map of the heterogeneous derivor of a change of signature. -/
@[simp] theorem heterogeneous_sortMap (I : Type i) [Preorder I] (c : Derivor sig tau) :
    (heterogeneous I c).sortMap = heterogeneousSortMap c := rfl

/-! ## Translation commutes with the inclusions -/

/-- Translating the generic application of an original symbol along a composite with an
inclusion gives the image of its copy. -/
theorem homogeneousInclusion_comp_image {I : Type i} {V : Type x} {sig' : Signature.{x, w} V}
    (X : Derivor (Homogeneous.Symbol I tau) sig') {a t} (τ : tau a t) :
    ((homogeneousInclusion I tau).comp X).image τ = X.image (.base τ) :=
  X.translate_symbol (.base τ)

/-- The homogeneous inclusion commutes with the homogeneous derivor of a change of
signature: translating $P$ along $\mathbf{d}^{(n)}$ is translating it along $\mathbf{d}$. -/
theorem homogeneousInclusion_comp (I : Type i) (d : Derivor tau ups) :
    (homogeneousInclusion I tau).comp (homogeneousDerivor I d) =
      d.comp (homogeneousInclusion I ups) := by
  apply Derivor.ext (c := (homogeneousInclusion I tau).comp (homogeneousDerivor I d))
    (d := d.comp (homogeneousInclusion I ups)) rfl
  apply heq_of_eq
  funext a t τ
  exact homogeneousInclusion_comp_image (homogeneousDerivor I d) τ

/-! ## Compositions and identities -/

/-- The homogeneous derivor of a composite is the composite of the homogeneous derivors. -/
theorem homogeneous_comp (I : Type i) (c : Derivor sig tau) (d : Derivor tau ups) :
    (homogeneous I c).comp (homogeneous I d) = homogeneous I (c.comp d) := by
  apply GeneralizedHepDerivor.ext
  · apply Derivor.ext (c := (homogeneousDerivor I c).comp (homogeneousDerivor I d))
      (d := homogeneousDerivor I (c.comp d)) rfl
    apply heq_of_eq
    funext a s σ
    cases σ with
    | base σ =>
      have h1 := Derivor.translate_comp (homogeneousInclusion I tau) (homogeneousDerivor I d)
        ((homogeneousInclusion I tau).positionMap c.sortMap a)
        ((homogeneousDerivor I d).positionMap c.sortMap a) (c.image σ)
      have h2 := Derivor.translate_comp d (homogeneousInclusion I ups)
        (d.positionMap c.sortMap a)
        ((homogeneousInclusion I ups).positionMap (d.sortMap ∘ c.sortMap) a) (c.image σ)
      refine h1.symm.trans (Eq.trans ?_ h2)
      apply eq_of_heq
      apply Derivor.translate_heq (homogeneousInclusion_comp I d)
      apply heq_of_eq
      funext t x
      obtain ⟨j, h⟩ := x
      cases h
      rfl
    | source k s =>
      apply congrArg (Term.app (sig := Homogeneous.Symbol I ups) (.source k _))
      funext j
      fin_cases j
      rfl
    | target k s =>
      apply congrArg (Term.app (sig := Homogeneous.Symbol I ups) (.target k _))
      funext j
      fin_cases j
      rfl
    | comp k s =>
      apply congrArg (Term.app (sig := Homogeneous.Symbol I ups) (.comp k _))
      funext j
      fin_cases j <;> rfl
  · apply heq_of_eq
    funext s
    change ⊥ ⊔ (homogeneousDerivor I d).translateSingletonSet _ ⊥ = ⊥
    rw [Derivor.translateSingletonSet_empty]
    exact bot_sup_eq _

/-- The homogeneous derivor of an identity derivor is the identity. -/
theorem homogeneous_identity (I : Type i) (sig : Signature.{u, v} S) :
    homogeneous I (Derivor.identity sig) =
      GeneralizedHepDerivor.identity (Homogeneous.hepSignature I sig) := by
  apply GeneralizedHepDerivor.ext
  · apply Derivor.ext (c := homogeneousDerivor I (Derivor.identity sig))
      (d := Derivor.identity _) rfl
    apply heq_of_eq
    funext a s σ
    cases σ with
    | base σ => exact (homogeneousInclusion I sig).translate_symbol σ
    | source k s =>
      apply congrArg (Term.app (sig := Homogeneous.Symbol I sig) (.source k s))
      funext j
      fin_cases j
      rfl
    | target k s =>
      apply congrArg (Term.app (sig := Homogeneous.Symbol I sig) (.target k s))
      funext j
      fin_cases j
      rfl
    | comp k s =>
      apply congrArg (Term.app (sig := Homogeneous.Symbol I sig) (.comp k s))
      funext j
      fin_cases j <;> rfl
  · rfl

/-- The positions of a word placed in dimension $k$, regarded back as positions of the word. -/
def dimensionUnposition {I : Type i} (k : I) {R : Type u} {V : Type x} (ψ : I × R → V)
    (a : List R) (p : V) :
    Word.MappedVariables ψ (Heterogeneous.dimensionWord k a) p →
      Word.MappedVariables (fun r => ψ (k, r)) a p :=
  fun x => ⟨⟨x.val.val, by
    simpa only [Heterogeneous.dimensionWord, List.length_map] using x.val.isLt⟩, by
      obtain ⟨j, h⟩ := x
      subst h
      simp [Heterogeneous.dimensionWord, List.get_eq_getElem]⟩

/-- Translating the generic application of an original symbol along a composite with a
heterogeneous inclusion gives the image of its copy, with the positions of the dimensional
word regarded as positions of the original word. -/
theorem heterogeneousInclusion_comp_image {I : Type i} [Preorder I] (k : I) {V : Type x}
    {sig' : Signature.{x, w} V} (X : Derivor (Heterogeneous.Symbol I tau) sig') {a t}
    (τ : tau a t) :
    ((heterogeneousInclusion I k tau).comp X).image τ =
      Term.subst (fun p y => .var (dimensionUnposition k X.sortMap a p y))
        (X.image (.base k τ)) := by
  change Term.subst _ (X.image (.base k τ)) = _
  congr 1
  funext p y
  obtain ⟨j, h⟩ := y
  cases h
  rfl

/-- The heterogeneous inclusion at dimension $k$ commutes with the heterogeneous derivor
of a change of signature: translating $P_k$ along $\mathbf{d}^{\mathrm{htg}(n)}$ gives
$d^\sharp(P)_k$. -/
theorem heterogeneousInclusion_comp (I : Type i) [Preorder I] (k : I) (d : Derivor tau ups) :
    (heterogeneousInclusion I k tau).comp (heterogeneousDerivor I d) =
      d.comp (heterogeneousInclusion I k ups) := by
  apply Derivor.ext (c := (heterogeneousInclusion I k tau).comp (heterogeneousDerivor I d))
    (d := d.comp (heterogeneousInclusion I k ups)) rfl
  apply heq_of_eq
  funext a t τ
  rw [heterogeneousInclusion_comp_image]
  refine (Derivor.subst_translate (heterogeneousInclusion I k ups)
    (fun t x => .var (dimensionPosition k d.sortMap a t x)) _ (d.image τ)).trans ?_
  congr 1

/-- The heterogeneous derivor of a composite is the composite of the heterogeneous
derivors. -/
theorem heterogeneous_comp (I : Type i) [Preorder I] (c : Derivor sig tau)
    (d : Derivor tau ups) :
    (heterogeneous I c).comp (heterogeneous I d) = heterogeneous I (c.comp d) := by
  apply GeneralizedHepDerivor.ext
  · apply Derivor.ext (c := (heterogeneousDerivor I c).comp (heterogeneousDerivor I d))
      (d := heterogeneousDerivor I (c.comp d)) rfl
    apply heq_of_eq
    funext a s σ
    cases σ with
    | base k σ =>
      have h1 := Derivor.translate_comp (heterogeneousInclusion I k tau)
        (heterogeneousDerivor I d) (fun t x => .var (dimensionPosition k c.sortMap _ t x))
        ((heterogeneousDerivor I d).positionMap (heterogeneousSortMap c)
          (Heterogeneous.dimensionWord k _)) (c.image σ)
      have h2 := Derivor.translate_comp d (heterogeneousInclusion I k ups)
        (d.positionMap c.sortMap _)
        (fun t x => .var (dimensionPosition k (d.sortMap ∘ c.sortMap) _ t x)) (c.image σ)
      refine h1.symm.trans (Eq.trans ?_ h2)
      apply eq_of_heq
      apply Derivor.translate_heq (heterogeneousInclusion_comp I k d)
      apply heq_of_eq
      funext t x
      obtain ⟨j, h⟩ := x
      cases h
      rfl
    | source h s =>
      apply congrArg (Term.app (sig := Heterogeneous.Symbol I ups) (.source h _))
      funext j
      fin_cases j
      rfl
    | target h s =>
      apply congrArg (Term.app (sig := Heterogeneous.Symbol I ups) (.target h _))
      funext j
      fin_cases j
      rfl
    | identity h s =>
      apply congrArg (Term.app (sig := Heterogeneous.Symbol I ups) (.identity h _))
      funext j
      fin_cases j
      rfl
    | comp h s =>
      apply congrArg (Term.app (sig := Heterogeneous.Symbol I ups) (.comp h _))
      funext j
      fin_cases j <;> rfl
  · apply heq_of_eq
    funext s
    change ⊥ ⊔ (heterogeneousDerivor I d).translateSingletonSet _ ⊥ = ⊥
    rw [Derivor.translateSingletonSet_empty]
    exact bot_sup_eq _

/-- Variables of possibly different sorts are heterogeneously equal when their generators
are. -/
theorem var_heq {V : Type x} {sig' : Signature.{x, w} V} {X : V → Type y}
    {t t' : V} (h : t = t') {y : X t} {y' : X t'} (hy : HEq y y') :
    HEq (Term.var (sig := sig') y) (Term.var (sig := sig') y') := by
  subst h
  cases hy
  rfl

/-- Positions of possibly different sorts are heterogeneously equal when they are the same
position. -/
theorem position_heq {V : Type x} {R : Type u} {φ : R → V} {a : List R}
    {t t' : V} (h : t = t') (y : Word.MappedVariables φ a t)
    (y' : Word.MappedVariables φ a t') (hv : y.val = y'.val) : HEq y y' := by
  subst h
  obtain ⟨j, hj⟩ := y
  obtain ⟨j', hj'⟩ := y'
  change j = j' at hv
  subst hv
  rfl

/-- The heterogeneous derivor of an identity derivor is the identity. -/
theorem heterogeneous_identity (I : Type i) [Preorder I] (sig : Signature.{u, v} S) :
    heterogeneous I (Derivor.identity sig) =
      GeneralizedHepDerivor.identity (Heterogeneous.hepSignature I sig) := by
  apply GeneralizedHepDerivor.ext
  · apply Derivor.ext (c := heterogeneousDerivor I (Derivor.identity sig))
      (d := Derivor.identity _) rfl
    apply heq_of_eq
    funext a s σ
    cases σ with
    | base k σ =>
      apply congrArg (Term.app (sig := Heterogeneous.Symbol I sig) (.base k σ))
      funext q
      change Word.valuation _ _ _ = _
      simp only [Word.valuation]
      apply eq_of_heq
      refine (eqRec_heq _ _).trans ?_
      change HEq (Term.var (dimensionPosition k id _ _ (Word.position _ _)) :
        Term (Heterogeneous.Symbol I sig) _ _) _
      refine var_heq (by simp [Heterogeneous.dimensionWord, List.get_eq_getElem]) ?_
      exact position_heq (by simp [Heterogeneous.dimensionWord, List.get_eq_getElem]) _ _ rfl
    | source h s =>
      apply congrArg (Term.app (sig := Heterogeneous.Symbol I sig) (.source h s))
      funext j
      fin_cases j
      rfl
    | target h s =>
      apply congrArg (Term.app (sig := Heterogeneous.Symbol I sig) (.target h s))
      funext j
      fin_cases j
      rfl
    | identity h s =>
      apply congrArg (Term.app (sig := Heterogeneous.Symbol I sig) (.identity h s))
      funext j
      fin_cases j
      rfl
    | comp h s =>
      apply congrArg (Term.app (sig := Heterogeneous.Symbol I sig) (.comp h s))
      funext j
      fin_cases j <;> rfl
  · rfl

/-! ## Functoriality -/

/-- The assignment $\mathbf{c}\mapsto\mathbf{c}^{(n)}$ is a functor from many-sorted
signatures and derivors to hierarchical signatures and generalized hep-derivors. -/
def homogeneousSignatureFunctor (I : Type i) :
    ManySortedSignature.{u, v} ⥤ BundledHepSignature.{u, max i v u} where
  obj sig := ⟨sig.sort, Homogeneous.hepSignature I sig.symbol⟩
  map c := homogeneous I c
  map_id sig := homogeneous_identity I sig.symbol
  map_comp c d := (homogeneous_comp I c d).symm

/-- The assignment $\mathbf{c}\mapsto\mathbf{c}^{\mathrm{htg}(n)}$ is a functor from
many-sorted signatures and derivors to hierarchical signatures and generalized
hep-derivors. -/
def heterogeneousSignatureFunctor (I : Type i) [Preorder I] :
    ManySortedSignature.{u, v} ⥤ BundledHepSignature.{max i u, max i v u} where
  obj sig := ⟨I × sig.sort, Heterogeneous.hepSignature I sig.symbol⟩
  map c := heterogeneous I c
  map_id sig := heterogeneous_identity I sig.symbol
  map_comp c d := (heterogeneous_comp I c d).symm

end ChangeOfSignature
end CategorialAlgebras
