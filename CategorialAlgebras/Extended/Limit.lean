import Stemma
import Mathlib.CategoryTheory.EqToHom
import CategorialAlgebras.Extended.Truncation

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "Extended ω-categorial algebras as a projective limit" =>

This document proves Proposition 10.2 of the draft: the category
$`\omega\mathsf{Cat}^{\mathrm{ext}}\mathsf{Alg}(\Sigma)`, with the truncation functors
$`T^{\mathrm{ext}(n,\omega)}_{\Sigma}`, is the projective limit of the projective system of the
categories $`\mathsf{nCat}^{\mathrm{ext}}\mathsf{Alg}(\Sigma)` and the truncation functors
$`T^{\mathrm{ext}(m,n)}_{\Sigma}`.

The proof rests on one construction: a family $`(\boldsymbol{\mathsf{A}}_n)_{n \in \mathbb{N}}`
of extended $`n`-categorial algebras that is *compatible*, in the sense that
$`T^{\mathrm{ext}(m,n)}_{\Sigma}(\boldsymbol{\mathsf{A}}_n) = \boldsymbol{\mathsf{A}}_m` for
$`m \leq n`, is the family of truncations of a single extended $`\omega`-categorial algebra.

```lean
universe u v w

namespace CategorialAlgebras.Extended

open CategoryTheory

variable {S : Type u} {Sig : Signature.{u, v} S}
```

# Transport along a compatibility

If $`T^{\mathrm{ext}(m,n)}_{\Sigma}(\boldsymbol{\mathsf{B}}) = \boldsymbol{\mathsf{B}}'`, the
$`i`-cells of sort $`s` of $`\boldsymbol{\mathsf{B}}'` are the $`i`-cells of sort $`s` of
$`\boldsymbol{\mathsf{B}}`, for $`i \leq m`. In the Lean this identification is a transport
along an equality of types, `tr`, with inverse `trInv`, and the lemmas below say that it
commutes with all the structure.

```lean
namespace CatAlgebra

variable {m n : ℕ} {h : m ≤ n} {B : CatAlgebra.{u, v, w} Sig n} {B' : CatAlgebra.{u, v, w} Sig m}

/-- The `i`-cells of `B'` are the `i`-cells of `B`, when `B'` is a truncation of `B`. -/
def tr (E : B.truncate h = B') (s : S) (i : FinSucc m) (x : B s (dimIncl h i)) : B' s i :=
  cast (by subst E; rfl) x

/-- The inverse of `tr`. -/
def trInv (E : B.truncate h = B') (s : S) (i : FinSucc m) (y : B' s i) : B s (dimIncl h i) :=
  cast (by subst E; rfl) y

@[simp] lemma tr_trInv (E : B.truncate h = B') (s : S) (i : FinSucc m) (y : B' s i) :
    tr E s i (trInv E s i y) = y := by
  subst E; rfl

@[simp] lemma trInv_tr (E : B.truncate h = B') (s : S) (i : FinSucc m) (x : B s (dimIncl h i)) :
    trInv E s i (tr E s i x) = x := by
  subst E; rfl

lemma tr_heq (E : B.truncate h = B') (s : S) (i : FinSucc m) (x : B s (dimIncl h i)) :
    tr E s i x ≍ x := by
  subst E; rfl

lemma trInv_heq (E : B.truncate h = B') (s : S) (i : FinSucc m) (y : B' s i) :
    trInv E s i y ≍ y := by
  subst E; rfl

lemma tr_inj (E : B.truncate h = B') (s : S) (i : FinSucc m) {x y : B s (dimIncl h i)} :
    tr E s i x = tr E s i y ↔ x = y := by
  subst E; rfl

lemma tr_tr {l : ℕ} {h₁ : l ≤ m} {B'' : CatAlgebra.{u, v, w} Sig l}
    (E₂ : B.truncate h = B') (E₁ : B'.truncate h₁ = B'') (E₃ : B.truncate (h₁.trans h) = B'')
    (s : S) (i : FinSucc l) (x : B s (dimIncl (h₁.trans h) i)) :
    tr E₁ s i (tr E₂ s (dimIncl h₁ i) x) = tr E₃ s i x := by
  subst E₂ E₁; rfl

lemma trInv_trInv {l : ℕ} {h₁ : l ≤ m} {B'' : CatAlgebra.{u, v, w} Sig l}
    (E₂ : B.truncate h = B') (E₁ : B'.truncate h₁ = B'') (E₃ : B.truncate (h₁.trans h) = B'')
    (s : S) (i : FinSucc l) (x : B'' s i) :
    trInv E₂ s (dimIncl h₁ i) (trInv E₁ s i x) = trInv E₃ s i x := by
  subst E₂ E₁; rfl

lemma sc_tr (E : B.truncate h = B') (s : S) {a b : FinSucc m} (hab : a < b)
    (y : B s (dimIncl h b)) :
    sc hab (tr E s b y) = tr E s a (sc (dimIncl_strictMono h hab) y) := by
  subst E; rfl

lemma tg_tr (E : B.truncate h = B') (s : S) {a b : FinSucc m} (hab : a < b)
    (y : B s (dimIncl h b)) :
    tg hab (tr E s b y) = tr E s a (tg (dimIncl_strictMono h hab) y) := by
  subst E; rfl

lemma trInv_idm (E : B.truncate h = B') (s : S) {a b : FinSucc m} (hab : a < b)
    (u : B' s a) :
    trInv E s b (idm hab u) = idm (dimIncl_strictMono h hab) (trInv E s a u) := by
  subst E; rfl

lemma idm_trInv (E : B.truncate h = B') (s : S) {a b : FinSucc m} (hab : a < b)
    (u : B s (dimIncl h a)) :
    idm hab (tr E s a u) = tr E s b (idm (dimIncl_strictMono h hab) u) := by
  subst E; rfl

lemma comp_tr (E : B.truncate h = B') (s : S) {a b : FinSucc m} (hab : a < b)
    (g f : B s (dimIncl h b)) (p : sc_is_tg (dimIncl_strictMono h hab) g f)
    (p' : sc_is_tg hab (tr E s b g) (tr E s b f)) :
    CategoryStruct.comp hab (tr E s b g) (tr E s b f) p' =
      tr E s b (CategoryStruct.comp (dimIncl_strictMono h hab) g f p) := by
  subst E; rfl

lemma trInv_comp (E : B.truncate h = B') (s : S) {a b : FinSucc m} (hab : a < b)
    (g f : B' s b) (p : sc_is_tg hab g f)
    (p' : sc_is_tg (dimIncl_strictMono h hab) (trInv E s b g) (trInv E s b f)) :
    trInv E s b (CategoryStruct.comp hab g f p) =
      CategoryStruct.comp (dimIncl_strictMono h hab) (trInv E s b g) (trInv E s b f) p' := by
  subst E; rfl

lemma trInv_sc_is_tg (E : B.truncate h = B') (s : S) {a b : FinSucc m} (hab : a < b)
    {g f : B' s b} (p : sc_is_tg hab g f) :
    sc_is_tg (dimIncl_strictMono h hab) (trInv E s b g) (trInv E s b f) := by
  subst E; exact p

lemma op_tr (E : B.truncate h = B') {ws : List S} {s : S} (σ : Sig ws s) (a : FinSucc m)
    (x : ExtArity B.carrier ws (dimIncl h a)) :
    B'.op σ a (fun l => tr E (ws.get l) a (x l)) = tr E s a (B.op σ (dimIncl h a) x) := by
  subst E; rfl

lemma trInv_op (E : B.truncate h = B') {ws : List S} {s : S} (σ : Sig ws s) (a : FinSucc m)
    (y : ExtArity B'.carrier ws a) :
    trInv E s a (B'.op σ a y) = B.op σ (dimIncl h a) (fun l => trInv E (ws.get l) a (y l)) := by
  subst E; rfl

lemma sc_heq (E : B.truncate h = B') (s : S) {a b : FinSucc m} (hab : a < b)
    {x : B' s b} {y : B s (dimIncl h b)} (hxy : x ≍ y) :
    sc hab x ≍ sc (dimIncl_strictMono h hab) y := by
  subst E; obtain rfl := eq_of_heq hxy; rfl

lemma tg_heq (E : B.truncate h = B') (s : S) {a b : FinSucc m} (hab : a < b)
    {x : B' s b} {y : B s (dimIncl h b)} (hxy : x ≍ y) :
    tg hab x ≍ tg (dimIncl_strictMono h hab) y := by
  subst E; obtain rfl := eq_of_heq hxy; rfl

lemma idm_heq (E : B.truncate h = B') (s : S) {a b : FinSucc m} (hab : a < b)
    {x : B' s a} {y : B s (dimIncl h a)} (hxy : x ≍ y) :
    idm hab x ≍ idm (dimIncl_strictMono h hab) y := by
  subst E; obtain rfl := eq_of_heq hxy; rfl

lemma pcomp_heq (E : B.truncate h = B') (s : S) {a b : FinSucc m} (hab : a < b)
    {g f : B' s b} {g' f' : B s (dimIncl h b)} (hg : g ≍ g') (hf : f ≍ f') :
    CategoryStruct.pcomp hab g f ≍ CategoryStruct.pcomp (dimIncl_strictMono h hab) g' f' := by
  subst E; obtain rfl := eq_of_heq hg; obtain rfl := eq_of_heq hf; rfl

lemma op_heq (E : B.truncate h = B') {ws : List S} {s : S} (σ : Sig ws s) (a : FinSucc m)
    {x : ExtArity B'.carrier ws a} {y : ExtArity B.carrier ws (dimIncl h a)} (hxy : x ≍ y) :
    B'.op σ a x ≍ B.op σ (dimIncl h a) y := by
  subst E; obtain rfl := eq_of_heq hxy; rfl

section Hom

variable {C : CatAlgebra.{u, v, w} Sig n} {C' : CatAlgebra.{u, v, w} Sig m}

lemma map_tr (E : B.truncate h = B') (E' : C.truncate h = C') {K : Hom B C} {K' : Hom B' C'}
    (hK : K.truncate h ≍ K') (s : S) (a : FinSucc m) (x : B s (dimIncl h a)) :
    K'.map s a (tr E s a x) = tr E' s a (K.map s (dimIncl h a) x) := by
  subst E E'; obtain rfl := eq_of_heq hK; rfl

lemma trInv_map (E : B.truncate h = B') (E' : C.truncate h = C') {K : Hom B C} {K' : Hom B' C'}
    (hK : K.truncate h ≍ K') (s : S) (a : FinSucc m) (y : B' s a) :
    trInv E' s a (K'.map s a y) = K.map s (dimIncl h a) (trInv E s a y) := by
  subst E E'; obtain rfl := eq_of_heq hK; rfl

lemma map_heq (E : B.truncate h = B') (E' : C.truncate h = C') {K : Hom B C} {K' : Hom B' C'}
    (hK : K.truncate h ≍ K') (s : S) (a : FinSucc m) {x : B' s a} {y : B s (dimIncl h a)}
    (hxy : x ≍ y) : K'.map s a x ≍ K.map s (dimIncl h a) y := by
  subst E E'; obtain rfl := eq_of_heq hK; obtain rfl := eq_of_heq hxy; rfl

end Hom

end CatAlgebra

theorem CategoryStruct.ext_of {I : Type} [Preorder I] {C : TypeFamily.{w} I}
    {X Y : CategoryStruct I C}
    (hsc : ∀ {k j : I} (h : j < k) (x : C k), X.sc h x = Y.sc h x)
    (htg : ∀ {k j : I} (h : j < k) (x : C k), X.tg h x = Y.tg h x)
    (hidm : ∀ {k j : I} (h : j < k) (x : C j), X.idm h x = Y.idm h x)
    (hpcomp : ∀ {k j : I} (h : j < k) (g f : C k), X.pcomp h g f = Y.pcomp h g f) :
    X = Y := by
  cases X with | mk sc₁ tg₁ idm₁ pcomp₁ =>
  cases Y with | mk sc₂ tg₂ idm₂ pcomp₂ =>
  have e₁ : @sc₁ = @sc₂ := by funext k j h x; exact hsc h x
  have e₂ : @tg₁ = @tg₂ := by funext k j h x; exact htg h x
  have e₃ : @idm₁ = @idm₂ := by funext k j h x; exact hidm h x
  have e₄ : @pcomp₁ = @pcomp₂ := by funext k j h g f; exact hpcomp h g f
  subst e₁ e₂ e₃ e₄; rfl

theorem Category.ext_of {I : Type} [Preorder I] {C : TypeFamily.{w} I} {X Y : Category I C}
    (h : X.toCategoryStruct = Y.toCategoryStruct) : X = Y := by
  cases X with | @mk P₁ =>
  cases P₁ with | @mk S₁ =>
  cases Y with | @mk P₂ =>
  cases P₂ with | @mk S₂ =>
  subst h
  rfl

namespace CatAlgebra

theorem ext_of_heq {A B : CatAlgebra.{u, v, w} Sig n} (hc : A.carrier = B.carrier)
    (hsc : ∀ s {a b : FinSucc n} (h : a < b) (x : A s b) (y : B s b), x ≍ y → sc h x ≍ sc h y)
    (htg : ∀ s {a b : FinSucc n} (h : a < b) (x : A s b) (y : B s b), x ≍ y → tg h x ≍ tg h y)
    (hidm : ∀ s {a b : FinSucc n} (h : a < b) (x : A s a) (y : B s a), x ≍ y →
      idm h x ≍ idm h y)
    (hpcomp : ∀ s {a b : FinSucc n} (h : a < b) (g f : A s b) (g' f' : B s b), g ≍ g' → f ≍ f' →
      CategoryStruct.pcomp h g f ≍ CategoryStruct.pcomp h g' f')
    (hop : ∀ {ws : List S} {s : S} (σ : Sig ws s) (a : FinSucc n) (x : ExtArity A.carrier ws a)
      (y : ExtArity B.carrier ws a), x ≍ y → A.op σ a x ≍ B.op σ a y) :
    A = B := by
  cases A with | @mk C strA opA =>
  cases B with | @mk D strB opB =>
  dsimp only at hc
  subst hc
  have hstr : strA = strB := by
    funext s
    exact Category.ext_of (CategoryStruct.ext_of
      (fun h x => eq_of_heq (hsc s h x x HEq.rfl))
      (fun h x => eq_of_heq (htg s h x x HEq.rfl))
      (fun h x => eq_of_heq (hidm s h x x HEq.rfl))
      (fun h g f => eq_of_heq (hpcomp s h g f g f HEq.rfl HEq.rfl)))
  subst hstr
  have hop' : @opA = @opB := by
    funext ws s σ
    exact Functor.ext fun a x => eq_of_heq (hop σ a x x HEq.rfl)
  subst hop'
  rfl

theorem Hom.heq_of {A₁ A₂ B₁ B₂ : CatAlgebra.{u, v, w} Sig n} (E₁ : A₁ = A₂) (E₂ : B₁ = B₂)
    {K : Hom A₁ B₁} {K' : Hom A₂ B₂}
    (h : ∀ s a (x : A₁ s a) (y : A₂ s a), x ≍ y → K.map s a x ≍ K'.map s a y) : K ≍ K' := by
  subst E₁ E₂
  exact heq_of_eq (Hom.ext fun s => Functor.ext fun a x => eq_of_heq (h s a x x HEq.rfl))

end CatAlgebra
```


# The ω-categorial algebra of a compatible family

```lean
lemma comp_eq_comp {I : Type} [Preorder I] {C : TypeFamily.{w} I} [CategoryStruct I C]
    {k j : I} {h : j < k} {g₁ g₂ f₁ f₂ : C k} (eg : g₁ = g₂) (ef : f₁ = f₂)
    (p₁ : sc_is_tg h g₁ f₁) (p₂ : sc_is_tg h g₂ f₂) :
    CategoryStruct.comp h g₁ f₁ p₁ = CategoryStruct.comp h g₂ f₂ p₂ := by
  subst eg ef; rfl

lemma last_lt {j k : ℕ} (h : j < k) : dimIncl h.le (Fin.last j) < Fin.last k := h

section Limit

open CatAlgebra

variable (A : ∀ n, CatAlgebra.{u, v, w} Sig n)
  (hA : ∀ m n (h : m ≤ n), (A n).truncate h = A m)

/-- The `k`-cells of sort `s` of the limit are the `k`-cells of sort `s` of `A k`. -/
abbrev limCarrier (s : S) : OmegaTypeFamily.{w} := fun k => A k s (Fin.last k)

@[reducible]
def limStruct (s : S) : CategoryStruct ℕ (limCarrier A s) where
  sc {k j} h x := tr (hA j k h.le) s (Fin.last j) (sc (C := (A k).carrier s) (last_lt h) x)
  tg {k j} h x := tr (hA j k h.le) s (Fin.last j) (tg (C := (A k).carrier s) (last_lt h) x)
  idm {k j} h u := idm (C := (A k).carrier s) (last_lt h) (trInv (hA j k h.le) s (Fin.last j) u)
  pcomp {k j} h g f := CategoryStruct.pcomp (C := (A k).carrier s) (last_lt h) g f
  pcomp_dom := by
    intro k j h f g
    rw [CategoryStruct.pcomp_dom]
    exact (tr_inj _ _ _).symm

variable {A} {s : S}

lemma lim_sc_is_tg {k j : ℕ} (h : j < k) {g f : A k s (Fin.last k)}
    (p : tr (hA j k h.le) s (Fin.last j) (sc (last_lt h) g) =
      tr (hA j k h.le) s (Fin.last j) (tg (last_lt h) f)) :
    sc_is_tg (last_lt h) g f :=
  (tr_inj _ _ _).mp p

lemma lim_sckj_idmkj {k j : ℕ} (h : j < k) (u : A j s (Fin.last j)) :
    tr (hA j k h.le) s (Fin.last j)
      (sc (last_lt h) (idm (last_lt h) (trInv (hA j k h.le) s (Fin.last j) u))) = u := by
  rw [PreCategory.sckj_idmkj, tr_trInv]

lemma lim_tgkj_idmkj {k j : ℕ} (h : j < k) (u : A j s (Fin.last j)) :
    tr (hA j k h.le) s (Fin.last j)
      (tg (last_lt h) (idm (last_lt h) (trInv (hA j k h.le) s (Fin.last j) u))) = u := by
  rw [PreCategory.tgkj_idmkj, tr_trInv]

lemma lim_idm_sc {k j : ℕ} (h : j < k) (f : A k s (Fin.last k)) :
    idm (last_lt h) (trInv (hA j k h.le) s (Fin.last j)
      (tr (hA j k h.le) s (Fin.last j) (sc (last_lt h) f))) = idm (last_lt h) (sc (last_lt h) f) := by
  rw [trInv_tr]

lemma lim_idm_tg {k j : ℕ} (h : j < k) (f : A k s (Fin.last k)) :
    idm (last_lt h) (trInv (hA j k h.le) s (Fin.last j)
      (tr (hA j k h.le) s (Fin.last j) (tg (last_lt h) f))) = idm (last_lt h) (tg (last_lt h) f) := by
  rw [trInv_tr]

lemma lim_scji_sckj {k j i : ℕ} (h₁ : j < k) (h₂ : i < j) (f : A k s (Fin.last k)) :
    tr (hA i j h₂.le) s (Fin.last i)
      (sc (last_lt h₂) (tr (hA j k h₁.le) s (Fin.last j) (sc (last_lt h₁) f))) =
    tr (hA i k (h₂.trans h₁).le) s (Fin.last i) (sc (last_lt (h₂.trans h₁)) f) := by
  rw [sc_tr, tr_tr (E₃ := hA i k (h₂.le.trans h₁.le))]
  exact congrArg _ (Category.scji_sckj_eq_scki _ _ f)

lemma lim_scji_tgkj {k j i : ℕ} (h₁ : j < k) (h₂ : i < j) (f : A k s (Fin.last k)) :
    tr (hA i j h₂.le) s (Fin.last i)
      (sc (last_lt h₂) (tr (hA j k h₁.le) s (Fin.last j) (tg (last_lt h₁) f))) =
    tr (hA i k (h₂.trans h₁).le) s (Fin.last i) (sc (last_lt (h₂.trans h₁)) f) := by
  rw [sc_tr, tr_tr (E₃ := hA i k (h₂.le.trans h₁.le))]
  exact congrArg _ (Category.scji_tgkj_eq_scki _ _ f)

lemma lim_tgji_tgkj {k j i : ℕ} (h₁ : j < k) (h₂ : i < j) (f : A k s (Fin.last k)) :
    tr (hA i j h₂.le) s (Fin.last i)
      (tg (last_lt h₂) (tr (hA j k h₁.le) s (Fin.last j) (tg (last_lt h₁) f))) =
    tr (hA i k (h₂.trans h₁).le) s (Fin.last i) (tg (last_lt (h₂.trans h₁)) f) := by
  rw [tg_tr, tr_tr (E₃ := hA i k (h₂.le.trans h₁.le))]
  exact congrArg _ (Category.tgji_tgkj_eq_tgki _ _ f)

lemma lim_tgji_sckj {k j i : ℕ} (h₁ : j < k) (h₂ : i < j) (f : A k s (Fin.last k)) :
    tr (hA i j h₂.le) s (Fin.last i)
      (tg (last_lt h₂) (tr (hA j k h₁.le) s (Fin.last j) (sc (last_lt h₁) f))) =
    tr (hA i k (h₂.trans h₁).le) s (Fin.last i) (tg (last_lt (h₂.trans h₁)) f) := by
  rw [tg_tr, tr_tr (E₃ := hA i k (h₂.le.trans h₁.le))]
  exact congrArg _ (Category.tgji_sckj_eq_tgki _ _ f)

lemma lim_idm_idm {k j i : ℕ} (h₁ : j < k) (h₂ : i < j) (u : A i s (Fin.last i)) :
    idm (last_lt h₁) (trInv (hA j k h₁.le) s (Fin.last j)
      (idm (last_lt h₂) (trInv (hA i j h₂.le) s (Fin.last i) u))) =
    idm (last_lt (h₂.trans h₁)) (trInv (hA i k (h₂.trans h₁).le) s (Fin.last i) u) := by
  rw [trInv_idm, trInv_trInv (E₃ := hA i k (h₂.le.trans h₁.le))]
  exact Category.idmkj_idmji_eq_idmki _ _ _

lemma lim_comp_idm_sc {k j : ℕ} (h : j < k) (f : A k s (Fin.last k))
    (p : sc_is_tg (last_lt h) f (idm (last_lt h) (trInv (hA j k h.le) s (Fin.last j)
      (tr (hA j k h.le) s (Fin.last j) (sc (last_lt h) f))))) :
    CategoryStruct.comp (last_lt h) f (idm (last_lt h) (trInv (hA j k h.le) s (Fin.last j)
      (tr (hA j k h.le) s (Fin.last j) (sc (last_lt h) f)))) p = f :=
  (comp_eq_comp rfl (lim_idm_sc hA h f) _ _).trans (PreCategory.compkj_idmkj_sckj_eq_id _ f)

lemma lim_comp_tg_idm {k j : ℕ} (h : j < k) (f : A k s (Fin.last k))
    (p : sc_is_tg (last_lt h) (idm (last_lt h) (trInv (hA j k h.le) s (Fin.last j)
      (tr (hA j k h.le) s (Fin.last j) (tg (last_lt h) f)))) f) :
    CategoryStruct.comp (last_lt h) (idm (last_lt h) (trInv (hA j k h.le) s (Fin.last j)
      (tr (hA j k h.le) s (Fin.last j) (tg (last_lt h) f)))) f p = f :=
  (comp_eq_comp (lim_idm_tg hA h f) rfl _ _).trans (PreCategory.compkj_tgkj_idmkj_eq_id _ f)

lemma lim_sc_comp {k j i : ℕ} (h₁ : j < k) (h₂ : i < j) {g f : A k s (Fin.last k)}
    (p : sc_is_tg (last_lt (h₂.trans h₁)) g f)
    (q : sc_is_tg (last_lt h₂) (tr (hA j k h₁.le) s (Fin.last j) (sc (last_lt h₁) g))
      (tr (hA j k h₁.le) s (Fin.last j) (sc (last_lt h₁) f))) :
    tr (hA j k h₁.le) s (Fin.last j)
      (sc (last_lt h₁) (CategoryStruct.comp (last_lt (h₂.trans h₁)) g f p)) =
    CategoryStruct.comp (last_lt h₂) (tr (hA j k h₁.le) s (Fin.last j) (sc (last_lt h₁) g))
      (tr (hA j k h₁.le) s (Fin.last j) (sc (last_lt h₁) f)) q := by
  rw [comp_tr _ s _ _ _ (Category.sc_tg_ji_sc (j_lt_k := last_lt h₁)
    (i_lt_j := dimIncl_strictMono _ (last_lt h₂)) p)]
  exact congrArg _ (Category.sckj_compki_eq_compji_sckj p)

lemma lim_tg_comp {k j i : ℕ} (h₁ : j < k) (h₂ : i < j) {g f : A k s (Fin.last k)}
    (p : sc_is_tg (last_lt (h₂.trans h₁)) g f)
    (q : sc_is_tg (last_lt h₂) (tr (hA j k h₁.le) s (Fin.last j) (tg (last_lt h₁) g))
      (tr (hA j k h₁.le) s (Fin.last j) (tg (last_lt h₁) f))) :
    tr (hA j k h₁.le) s (Fin.last j)
      (tg (last_lt h₁) (CategoryStruct.comp (last_lt (h₂.trans h₁)) g f p)) =
    CategoryStruct.comp (last_lt h₂) (tr (hA j k h₁.le) s (Fin.last j) (tg (last_lt h₁) g))
      (tr (hA j k h₁.le) s (Fin.last j) (tg (last_lt h₁) f)) q := by
  rw [comp_tr _ s _ _ _ (Category.sc_tg_ji_tg (j_lt_k := last_lt h₁)
    (i_lt_j := dimIncl_strictMono _ (last_lt h₂)) p)]
  exact congrArg _ (Category.tgkj_compki_eq_compji_tgkj p)

lemma lim_idm_comp {k j i : ℕ} (h₁ : j < k) (h₂ : i < j) {g f : A j s (Fin.last j)}
    (p : sc_is_tg (last_lt h₂) g f)
    (q : sc_is_tg (last_lt (h₂.trans h₁))
      (idm (last_lt h₁) (trInv (hA j k h₁.le) s (Fin.last j) g))
      (idm (last_lt h₁) (trInv (hA j k h₁.le) s (Fin.last j) f))) :
    idm (last_lt h₁) (trInv (hA j k h₁.le) s (Fin.last j)
      (CategoryStruct.comp (last_lt h₂) g f p)) =
    CategoryStruct.comp (last_lt (h₂.trans h₁))
      (idm (last_lt h₁) (trInv (hA j k h₁.le) s (Fin.last j) g))
      (idm (last_lt h₁) (trInv (hA j k h₁.le) s (Fin.last j) f)) q := by
  rw [trInv_comp _ s _ _ _ p (trInv_sc_is_tg _ s _ p)]
  exact Category.idmkj_compji_eq_compki_idmkj _

lemma lim_sckj_compkj {k j : ℕ} (h : j < k) {g f : A k s (Fin.last k)}
    (p : sc_is_tg (last_lt h) g f) :
    tr (hA j k h.le) s (Fin.last j) (sc (last_lt h) (CategoryStruct.comp (last_lt h) g f p)) =
    tr (hA j k h.le) s (Fin.last j) (sc (last_lt h) f) := by
  rw [PreCategory.sckj_compkj_eq_sckj]

lemma lim_tgkj_compkj {k j : ℕ} (h : j < k) {g f : A k s (Fin.last k)}
    (p : sc_is_tg (last_lt h) g f) :
    tr (hA j k h.le) s (Fin.last j) (tg (last_lt h) (CategoryStruct.comp (last_lt h) g f p)) =
    tr (hA j k h.le) s (Fin.last j) (tg (last_lt h) g) := by
  rw [PreCategory.tgkj_compkj_eq_tgkj]

variable (A) in
@[reducible]
def limCategory (s : S) : OmegaCategory (limCarrier A s) where
  toCategoryStruct := limStruct A hA s
  sckj_compkj_eq_sckj {_ _ h _ _} p := lim_sckj_compkj hA h (lim_sc_is_tg hA h p)
  tgkj_compkj_eq_tgkj {_ _ h _ _} p := lim_tgkj_compkj hA h (lim_sc_is_tg hA h p)
  sckj_idmkj h u := lim_sckj_idmkj hA h u
  tgkj_idmkj h u := lim_tgkj_idmkj hA h u
  compkj_idmkj_sckj_eq_id h f := lim_comp_idm_sc hA h f (by simp)
  compkj_tgkj_idmkj_eq_id h f := lim_comp_tg_idm hA h f (by simp)
  assoc {_ _ h _ _ _} p₁ p₂ := PreCategory.assoc (lim_sc_is_tg hA h p₁) (lim_sc_is_tg hA h p₂)
  scji_sckj_eq_scki h₁ h₂ f := lim_scji_sckj hA h₁ h₂ f
  scji_tgkj_eq_scki h₁ h₂ f := lim_scji_tgkj hA h₁ h₂ f
  tgji_tgkj_eq_tgki h₁ h₂ f := lim_tgji_tgkj hA h₁ h₂ f
  tgji_sckj_eq_tgki h₁ h₂ f := lim_tgji_sckj hA h₁ h₂ f
  sckj_compki_eq_compji_sckj {_ _ _ h₁ h₂ _ _} p :=
    lim_sc_comp hA h₁ h₂ (lim_sc_is_tg hA (h₂.trans h₁) p)
      (by unfold sc_is_tg; rw [sc_tr, tg_tr, tr_inj]
          exact Category.sc_tg_ji_sc (j_lt_k := last_lt h₁)
            (i_lt_j := dimIncl_strictMono _ (last_lt h₂)) (lim_sc_is_tg hA (h₂.trans h₁) p))
  tgkj_compki_eq_compji_tgkj {_ _ _ h₁ h₂ _ _} p :=
    lim_tg_comp hA h₁ h₂ (lim_sc_is_tg hA (h₂.trans h₁) p)
      (by unfold sc_is_tg; rw [sc_tr, tg_tr, tr_inj]
          exact Category.sc_tg_ji_tg (j_lt_k := last_lt h₁)
            (i_lt_j := dimIncl_strictMono _ (last_lt h₂)) (lim_sc_is_tg hA (h₂.trans h₁) p))
  idmkj_idmji_eq_idmki h₁ h₂ u := lim_idm_idm hA h₁ h₂ u
  idmkj_compji_eq_compki_idmkj {_ _ _ h₁ h₂ _ _} p :=
    lim_idm_comp hA h₁ h₂ (lim_sc_is_tg hA h₂ p)
      (Category.sc_tg_ki_idmkj (j_lt_k := last_lt h₁)
        (trInv_sc_is_tg _ s _ (lim_sc_is_tg hA h₂ p)))
  interchange := by
    intro k j i j_lt_k i_lt_j f₁ f₂ g₁ g₂ p₁ p₂ p₃ p₄
    exact Category.interchange (i_lt_j := dimIncl_strictMono j_lt_k.le (last_lt i_lt_j))
      (lim_sc_is_tg hA j_lt_k p₁) (lim_sc_is_tg hA j_lt_k p₂)
      (lim_sc_is_tg hA (i_lt_j.trans j_lt_k) p₃) (lim_sc_is_tg hA (i_lt_j.trans j_lt_k) p₄)

lemma lim_op_sc {ws : List S} (σ : Sig ws s) {k j : ℕ} (h : j < k)
    (a : ExtArity (A k).carrier ws (Fin.last k)) :
    (A j).op σ (Fin.last j)
      (fun l => tr (hA j k h.le) (ws.get l) (Fin.last j) (sc (last_lt h) (a l))) =
    tr (hA j k h.le) s (Fin.last j) (sc (last_lt h) ((A k).op σ (Fin.last k) a)) := by
  rw [op_tr]
  exact congrArg _ (((A k).op σ).map_sc_eq_sc_map (last_lt h) a)

lemma lim_op_tg {ws : List S} (σ : Sig ws s) {k j : ℕ} (h : j < k)
    (a : ExtArity (A k).carrier ws (Fin.last k)) :
    (A j).op σ (Fin.last j)
      (fun l => tr (hA j k h.le) (ws.get l) (Fin.last j) (tg (last_lt h) (a l))) =
    tr (hA j k h.le) s (Fin.last j) (tg (last_lt h) ((A k).op σ (Fin.last k) a)) := by
  rw [op_tr]
  exact congrArg _ (((A k).op σ).map_tg_eq_tg_map (last_lt h) a)

lemma lim_op_idm {ws : List S} (σ : Sig ws s) {k j : ℕ} (h : j < k)
    (u : ExtArity (A j).carrier ws (Fin.last j)) :
    (A k).op σ (Fin.last k)
      (fun l => idm (last_lt h) (trInv (hA j k h.le) (ws.get l) (Fin.last j) (u l))) =
    idm (last_lt h) (trInv (hA j k h.le) s (Fin.last j) ((A j).op σ (Fin.last j) u)) := by
  rw [trInv_op]
  exact ((A k).op σ).map_idm_eq_idm_map (last_lt h) _

```

:::construction (label := "extended.limit-algebra") (central := false) (title := "The ω-categorial algebra of a compatible family")
Let $`(\boldsymbol{\mathsf{A}}_n)_{n \in \mathbb{N}}` be a compatible family of extended
$`n`-categorial $`\Sigma`-algebras. Its *limit* $`\varprojlim_n \boldsymbol{\mathsf{A}}_n` is the
extended $`\omega`-categorial $`\Sigma`-algebra whose $`k`-cells of sort $`s` are the $`k`-cells of
sort $`s` of $`\boldsymbol{\mathsf{A}}_k`, its cells of top dimension. For $`j < k`, the
$`(j,k)`-source of a $`k`-cell $`x` is its $`(j,k)`-source in $`\boldsymbol{\mathsf{A}}_k`,
which is a $`j`-cell of $`\boldsymbol{\mathsf{A}}_k` and so, by compatibility, a $`j`-cell of
$`\boldsymbol{\mathsf{A}}_j`; targets, identities and compositions are defined in the same way,
and an operation symbol acts on $`k`-cells as it does in $`\boldsymbol{\mathsf{A}}_k`. Every
axiom involves finitely many dimensions $`i < j < k`, and holds because it holds in
$`\boldsymbol{\mathsf{A}}_k`.

```lean
variable (A) in
/-- The extended `ω`-categorial algebra of a compatible family: its `k`-cells, and the action
of the operations on them, are those of the `k`-th member of the family. -/
def lim : OmegaCatAlgebra.{u, v, w} Sig :=
  letI := limCategory A hA
  { carrier := limCarrier A
    str := limCategory A hA
    op := fun {ws s} σ =>
    { map := fun k a => (A k).op σ (Fin.last k) a
      map_sc_eq_sc_map := fun h a => lim_op_sc hA σ h a
      map_tg_eq_tg_map := fun h a => lim_op_tg hA σ h a
      map_idm_eq_idm_map := fun h u => lim_op_idm hA σ h u
      map_comp_eq_comp_map := by
        intro k j h f g p
        exact ((A k).op σ).map_comp_eq_comp_map (j_lt_k := last_lt h)
          (funext fun l => lim_sc_is_tg hA h (congrFun p l)) } }

```
:::

```lean
end Limit
```

```lean
section LimitProps

open CatAlgebra

variable {A : ∀ n, CatAlgebra.{u, v, w} Sig n} (hA : ∀ m n (h : m ≤ n), (A n).truncate h = A m)

theorem lim_truncate (n : ℕ) : (lim A hA).truncate n = A n := by
  apply CatAlgebra.ext_of_heq
  · funext s i
    exact (congrFun (congrFun (congrArg CatAlgebra.carrier
      (hA i n (Nat.lt_succ_iff.mp i.isLt))) s) (Fin.last i)).symm
  · intro s a b h x y hxy
    exact (tr_heq _ _ _ _).trans (sc_heq (hA b n (Nat.lt_succ_iff.mp b.isLt)) s (last_lt h) hxy)
  · intro s a b h x y hxy
    exact (tr_heq _ _ _ _).trans (tg_heq (hA b n (Nat.lt_succ_iff.mp b.isLt)) s (last_lt h) hxy)
  · intro s a b h x y hxy
    exact idm_heq (hA b n (Nat.lt_succ_iff.mp b.isLt)) s (last_lt h)
      ((trInv_heq _ _ _ _).trans hxy)
  · intro s a b h g f g' f' hg hf
    exact pcomp_heq (hA b n (Nat.lt_succ_iff.mp b.isLt)) s (last_lt h) hg hf
  · intro ws s σ a x y hxy
    exact op_heq (hA a n (Nat.lt_succ_iff.mp a.isLt)) σ (Fin.last a) hxy

theorem lim_self (B : OmegaCatAlgebra.{u, v, w} Sig) :
    lim (fun n => B.truncate n) (fun _ _ _ => rfl) = B :=
  rfl

theorem lim_congr {A' : ∀ n, CatAlgebra.{u, v, w} Sig n}
    (hA' : ∀ m n (h : m ≤ n), (A' n).truncate h = A' m) (e : A = A') :
    lim A hA = lim A' hA' := by
  subst e; rfl

end LimitProps
```

# Homomorphisms between limits

```lean
section LimitHom

open CatAlgebra

variable {A A' : ∀ n, CatAlgebra.{u, v, w} Sig n}
  {hA : ∀ m n (h : m ≤ n), (A n).truncate h = A m}
  {hA' : ∀ m n (h : m ≤ n), (A' n).truncate h = A' m}
  (H : ∀ n, CatAlgebra.Hom (A n) (A' n))
  (hH : ∀ m n (h : m ≤ n), (H n).truncate h ≍ H m)

```

:::construction (label := "extended.limit-hom") (central := false) (title := "The homomorphism of a compatible family")
Let $`(\boldsymbol{\mathsf{A}}_n)_n` and $`(\boldsymbol{\mathsf{A}}'_n)_n` be compatible families
and $`(H_n \colon \boldsymbol{\mathsf{A}}_n \to \boldsymbol{\mathsf{A}}'_n)_n` a family of
homomorphisms such that $`T^{\mathrm{ext}(m,n)}_{\Sigma}(H_n) = H_m` for $`m \leq n`. Then the
mappings $`H_{k,s,k}`, which send the $`k`-cells of $`\boldsymbol{\mathsf{A}}_k` to those of
$`\boldsymbol{\mathsf{A}}'_k`, form a homomorphism
$`\varprojlim_n H_n \colon \varprojlim_n \boldsymbol{\mathsf{A}}_n \to \varprojlim_n \boldsymbol{\mathsf{A}}'_n`.

```lean
/-- The homomorphism between the limits of two compatible families determined by a compatible
family of homomorphisms: on `k`-cells it is the `k`-th homomorphism of the family. -/
def limHom : OmegaCatAlgebra.Hom (lim A hA) (lim A' hA') where
  map s :=
    { map := fun k x => (H k).map s (Fin.last k) x
      map_sc_eq_sc_map := by
        intro k j h x
        change (H j).map s (Fin.last j) (tr (hA j k h.le) s (Fin.last j) (sc (last_lt h) x)) =
          tr (hA' j k h.le) s (Fin.last j) (sc (last_lt h) ((H k).map s (Fin.last k) x))
        rw [map_tr (hA j k h.le) (hA' j k h.le) (hH j k h.le)]
        exact congrArg _ (((H k).map s).map_sc_eq_sc_map (last_lt h) x)
      map_tg_eq_tg_map := by
        intro k j h x
        change (H j).map s (Fin.last j) (tr (hA j k h.le) s (Fin.last j) (tg (last_lt h) x)) =
          tr (hA' j k h.le) s (Fin.last j) (tg (last_lt h) ((H k).map s (Fin.last k) x))
        rw [map_tr (hA j k h.le) (hA' j k h.le) (hH j k h.le)]
        exact congrArg _ (((H k).map s).map_tg_eq_tg_map (last_lt h) x)
      map_idm_eq_idm_map := by
        intro k j h u
        exact (((H k).map s).map_idm_eq_idm_map (last_lt h) _).trans
          (congrArg (idm (last_lt h))
            (trInv_map (hA j k h.le) (hA' j k h.le) (hH j k h.le) s (Fin.last j) u).symm)
      map_comp_eq_comp_map := by
        intro k j h f g p
        exact ((H k).map s).map_comp_eq_comp_map (j_lt_k := last_lt h) (lim_sc_is_tg hA h p) }
  map_op σ k a := (H k).map_op σ (Fin.last k) a

```
:::

Truncating the limit gives back the family, and every extended $`\omega`-categorial algebra,
or homomorphism, is the limit of its truncations.

```lean
theorem limHom_truncate (n : ℕ) :
    (limHom (hA := hA) (hA' := hA') H hH).truncate n ≍ H n := by
  refine Hom.heq_of (lim_truncate hA n) (lim_truncate hA' n) ?_
  intro s a x y hxy
  exact map_heq (hA a n (Nat.lt_succ_iff.mp a.isLt)) (hA' a n (Nat.lt_succ_iff.mp a.isLt))
    (hH a n (Nat.lt_succ_iff.mp a.isLt)) s (Fin.last a) hxy

end LimitHom

theorem limHom_self {B B' : OmegaCatAlgebra.{u, v, w} Sig} (K : OmegaCatAlgebra.Hom B B') :
    limHom (hA := fun _ _ _ => rfl) (hA' := fun _ _ _ => rfl) (fun n => K.truncate n)
      (fun _ _ _ => HEq.rfl) = K :=
  rfl

theorem limHom_congr {A₁ A₂ A₁' A₂' : ∀ n, CatAlgebra.{u, v, w} Sig n}
    {hA₁ : ∀ m n (h : m ≤ n), (A₁ n).truncate h = A₁ m}
    {hA₂ : ∀ m n (h : m ≤ n), (A₂ n).truncate h = A₂ m}
    {hA₁' : ∀ m n (h : m ≤ n), (A₁' n).truncate h = A₁' m}
    {hA₂' : ∀ m n (h : m ≤ n), (A₂' n).truncate h = A₂' m}
    {H₁ : ∀ n, CatAlgebra.Hom (A₁ n) (A₁' n)} {H₂ : ∀ n, CatAlgebra.Hom (A₂ n) (A₂' n)}
    (hH₁ : ∀ m n (h : m ≤ n), (H₁ n).truncate h ≍ H₁ m)
    (hH₂ : ∀ m n (h : m ≤ n), (H₂ n).truncate h ≍ H₂ m)
    (e : A₁ = A₂) (e' : A₁' = A₂') (eH : H₁ ≍ H₂) :
    limHom (hA := hA₁) (hA' := hA₁') H₁ hH₁ ≍ limHom (hA := hA₂) (hA' := hA₂') H₂ hH₂ := by
  subst e e'
  obtain rfl := eq_of_heq eH
  rfl
```

# The universal property

:::proposition (label := "extended.omega-cat-alg-limit") (central := true) (title := "Proposition 10.2")
Let $`\mathsf{L}` be a category and, for every $`n \in \mathbb{N}`, let
$`F_n \colon \mathsf{L} \to \mathsf{nCat}^{\mathrm{ext}}\mathsf{Alg}(\Sigma)` be a functor. If
$`F_m = T^{\mathrm{ext}(m,n)}_{\Sigma} \circ F_n` for all $`m \leq n`, then there exists a
unique functor
$`\langle F_k \rangle_{k \in \mathbb{N}} \colon \mathsf{L} \to \omega\mathsf{Cat}^{\mathrm{ext}}\mathsf{Alg}(\Sigma)`
such that $`F_n = T^{\mathrm{ext}(n,\omega)}_{\Sigma} \circ \langle F_k \rangle_{k \in \mathbb{N}}`
for every $`n \in \mathbb{N}`.

Together with Remark 10.1, this says that
$`(\omega\mathsf{Cat}^{\mathrm{ext}}\mathsf{Alg}(\Sigma), T^{\mathrm{ext}(\cdot,\omega)}_{\Sigma})`
is the projective limit of the projective system
$`((\cdot)\mathsf{Cat}^{\mathrm{ext}}\mathsf{Alg}(\Sigma), T^{\mathrm{ext}(\cdot)}_{\Sigma})` in
$`\mathsf{Cat}`.

```lean
theorem omegaCatAlg_isLimit {L : Type*} [CategoryTheory.Category L] (F : ∀ n, L ⥤ CatAlgebra.{u, v, w} Sig n)
    (hF : ∀ m n (h : m ≤ n), F n ⋙ truncation Sig h = F m) :
    ∃! G : L ⥤ OmegaCatAlgebra.{u, v, w} Sig, ∀ n, G ⋙ truncationω Sig n = F n := by
  let G : L ⥤ OmegaCatAlgebra.{u, v, w} Sig :=
    { obj := fun X => lim (fun n => (F n).obj X) (fun m n h => Functor.congr_obj (hF m n h) X)
      map := fun f => limHom (fun n => (F n).map f) (fun m n h => Functor.hcongr_hom (hF m n h) f)
      map_id := by
        intro X
        refine OmegaCatAlgebra.Hom.ext fun s => CategorialAlgebras.Extended.Functor.ext ?_
        intro k x
        change ((F k).map (𝟙 X)).map s (Fin.last k) x = x
        rw [(F k).map_id]
        rfl
      map_comp := by
        intro X Y Z f g
        refine OmegaCatAlgebra.Hom.ext fun s => CategorialAlgebras.Extended.Functor.ext ?_
        intro k x
        change ((F k).map (f ≫ g)).map s (Fin.last k) x =
          ((F k).map g).map s (Fin.last k) (((F k).map f).map s (Fin.last k) x)
        rw [(F k).map_comp]
        rfl }
  refine ⟨G, fun n => ?_, fun G' hG' => ?_⟩
  · exact Functor.hext (fun X => lim_truncate _ n)
      (fun X Y f => limHom_truncate _ (fun m n h => Functor.hcongr_hom (hF m n h) f) n)
  · refine Functor.hext (fun X => ?_) (fun X Y f => ?_)
    · exact (lim_self (G'.obj X)).symm.trans
        (lim_congr _ _ (funext fun n => Functor.congr_obj (hG' n) X))
    · exact (heq_of_eq (limHom_self (G'.map f)).symm).trans
        (limHom_congr _ (fun m n h => Functor.hcongr_hom (hF m n h) f)
          (funext fun n => Functor.congr_obj (hG' n) X)
          (funext fun n => Functor.congr_obj (hG' n) Y)
          (Function.hfunext rfl fun n n' hn => by
            cases hn
            exact Functor.hcongr_hom (hG' n) f))
```
:::

:::proof (of := "extended.omega-cat-alg-limit")
For an object $`X` of $`\mathsf{L}`, the family $`(F_n(X))_{n}` is compatible, and
$`\langle F_k \rangle_k(X)` is its limit; for a morphism $`f`, the family $`(F_n(f))_n` is
compatible, and $`\langle F_k \rangle_k(f)` is its limit. This is a functor because each
$`F_k` is, and $`T^{\mathrm{ext}(n,\omega)}_{\Sigma}` sends it to $`F_n`, since truncating the
limit of a compatible family gives back the family.

For uniqueness, let $`G` be another functor with
$`T^{\mathrm{ext}(n,\omega)}_{\Sigma} \circ G = F_n` for every $`n`. An extended
$`\omega`-categorial algebra is the limit of its truncations, so
$`G(X) = \varprojlim_n T^{\mathrm{ext}(n,\omega)}_{\Sigma}(G(X)) = \varprojlim_n F_n(X)`, and in
the same way $`G(f) = \varprojlim_n F_n(f)`.
:::

```lean
end CategorialAlgebras.Extended
```
