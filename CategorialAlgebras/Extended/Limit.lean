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

end Limit
```

```lean
end CategorialAlgebras.Extended
```
