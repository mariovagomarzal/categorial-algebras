import Mathlib.Data.Fin.VecNotation
import CategorialAlgebras.Compact.Truncation

/-!
# Towers of compact categories and their limits

A tower is a sequence of compact categories `X n`, with dimensions in `n`, in which `X n` embeds
into `X (n + 1)` as the set of its `n`-cells, preserving the structure of the dimensions below
`n`. Its limit is the union of the chain: the cells of all levels, each cell identified with its
images at the levels above. The sources, targets and compositions of dimension `k` are computed
at any level above `k` that contains the cells involved, and the limit is a compact
`ω`-category. This is the construction behind the limit of a compatible family of compact
categorial algebras, in the proof of the universal property of `ωCatAlg(Σ)`.
-/

universe w

namespace CategorialAlgebras.Compact

open CategoryStruct

/-- A tower of compact categories: `X n` has dimensions in `n`, and `X n` embeds into `X (n+1)`
as the set of `n`-cells, preserving the structure of the dimensions below `n`. -/
structure Tower where
  X : ℕ → Type w
  str : ∀ n, Category (Fin n) (X n)
  e : ∀ n, X n → X (n + 1)
  e_injective : ∀ n, Function.Injective (e n)
  e_sc : ∀ n (k : Fin n) a, e n (sc k a) = sc k.castSucc (e n a)
  e_tg : ∀ n (k : Fin n) a, e n (tg k a) = tg k.castSucc (e n a)
  e_comp : ∀ n (k : Fin n) g f (h : sc_is_tg k g f),
    e n (g ♯[k] f ← h) = (e n g ♯.[k.castSucc] e n f).get (dom_of_sc_is_tg (by
      change sc k.castSucc (e n g) = tg k.castSucc (e n f)
      rw [← e_sc, ← e_tg, h]))
  e_cell : ∀ n a, sc (Fin.last n) (e n a) = e n a
  e_surj : ∀ n x, sc (Fin.last n) x = x → ∃ a, e n a = x

attribute [instance] Tower.str

namespace Tower

variable (T : Tower.{w})

/-- The iterated embedding from level `n` to level `m ≥ n`. -/
def up {n m : ℕ} (h : n ≤ m) (a : T.X n) : T.X m := Nat.leRecOn h (fun {k} => T.e k) a

@[simp] lemma up_self {n : ℕ} (a : T.X n) : T.up le_rfl a = a := Nat.leRecOn_self _

lemma up_succ {n m : ℕ} (h : n ≤ m) (a : T.X n) :
    T.up (Nat.le_succ_of_le h) a = T.e m (T.up h a) := Nat.leRecOn_succ h _

lemma up_trans {n m p : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ p) (a : T.X n) :
    T.up (h₁.trans h₂) a = T.up h₂ (T.up h₁ a) := Nat.leRecOn_trans h₁ h₂ _

lemma up_injective {n m : ℕ} (h : n ≤ m) : Function.Injective (T.up h : T.X n → T.X m) := by
  induction m, h using Nat.le_induction with
  | base => intro a b hab; simpa using hab
  | succ m hm ih =>
    intro a b hab
    rw [up_succ T hm, up_succ T hm] at hab
    exact ih (T.e_injective m hab)

lemma up_sc {n m : ℕ} (h : n ≤ m) (k : ℕ) (hk : k < n) (a : T.X n) :
    T.up h (sc (⟨k, hk⟩ : Fin n) a) = sc (⟨k, by omega⟩ : Fin m) (T.up h a) := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m hm ih => rw [up_succ T hm, up_succ T hm, ih, e_sc]; rfl

lemma up_tg {n m : ℕ} (h : n ≤ m) (k : ℕ) (hk : k < n) (a : T.X n) :
    T.up h (tg (⟨k, hk⟩ : Fin n) a) = tg (⟨k, by omega⟩ : Fin m) (T.up h a) := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m hm ih => rw [up_succ T hm, up_succ T hm, ih, e_tg]; rfl

lemma up_sc_is_tg {n m : ℕ} (h : n ≤ m) (k : ℕ) (hk : k < n) {g f : T.X n}
    (hgf : sc_is_tg (⟨k, hk⟩ : Fin n) g f) :
    sc_is_tg (⟨k, by omega⟩ : Fin m) (T.up h g) (T.up h f) := by
  change sc _ _ = tg _ _
  rw [← up_sc T h k hk, ← up_tg T h k hk, hgf]

lemma up_comp {n m : ℕ} (h : n ≤ m) (k : ℕ) (hk : k < n) {g f : T.X n}
    (hgf : sc_is_tg (⟨k, hk⟩ : Fin n) g f) :
    T.up h (g ♯[(⟨k, hk⟩ : Fin n)] f ← hgf) =
      T.up h g ♯[(⟨k, by omega⟩ : Fin m)] T.up h f ← T.up_sc_is_tg h k hk hgf := by
  induction m, h using Nat.le_induction with
  | base => simp only [up_self]
  | succ m hm ih =>
    rw [up_succ T hm, ih, e_comp]
    exact congr_comp₂ (T.up_succ hm f).symm (T.up_succ hm g).symm _

/-- The image of level `n` in level `m` consists of `u`-cells for `n ≤ u < m`. -/
lemma up_cell {n m : ℕ} (h : n ≤ m) (a : T.X n) (u : ℕ) (hu : n ≤ u) (hum : u < m) :
    sc (⟨u, hum⟩ : Fin m) (T.up h a) = T.up h a := by
  induction m, h using Nat.le_induction with
  | base => omega
  | succ m hm ih =>
    rw [up_succ T hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hum with hu' | rfl
    · have := T.e_sc m ⟨u, hu'⟩ (T.up hm a)
      rw [ih hu'] at this
      exact this.symm
    · exact T.e_cell _ _

/-- A cell of level `m` that is a `u`-cell for `n ≤ u < m` comes from level `n`. -/
lemma up_surj {n m : ℕ} (h : n ≤ m) (x : T.X m)
    (hx : ∀ u (_ : n ≤ u) (hum : u < m), sc (⟨u, hum⟩ : Fin m) x = x) :
    ∃ a, T.up h a = x := by
  induction m, h using Nat.le_induction with
  | base => exact ⟨x, by simp⟩
  | succ m hm ih =>
    obtain ⟨y, rfl⟩ := T.e_surj m x (hx m hm (Nat.lt_succ_self m))
    obtain ⟨a, rfl⟩ := ih y fun u hu hum => T.e_injective m (by
      rw [T.e_sc]; exact hx u hu (by omega))
    exact ⟨a, (T.up_succ hm a)⟩

/-- Pairs of a level and a cell of that level. -/
abbrev Pre := Σ n, T.X n

/-- Two pairs are equivalent when they agree at a common level. -/
def Rel (p q : T.Pre) : Prop :=
  T.up (le_max_left p.1 q.1) p.2 = T.up (le_max_right p.1 q.1) q.2

lemma rel_iff_le {p q : T.Pre} {N : ℕ} (hp : p.1 ≤ N) (hq : q.1 ≤ N) :
    T.Rel p q ↔ T.up hp p.2 = T.up hq q.2 := by
  unfold Rel
  rw [← (T.up_injective (max_le hp hq)).eq_iff, ← up_trans, ← up_trans]

instance setoid : Setoid T.Pre where
  r := T.Rel
  iseqv :=
    { refl := fun p => by simp [Rel]
      symm := fun {p q} h => by
        rw [T.rel_iff_le (le_max_left p.1 q.1) (le_max_right p.1 q.1)] at h
        rw [T.rel_iff_le (le_max_right p.1 q.1) (le_max_left p.1 q.1)]
        exact h.symm
      trans := fun {p q r} h₁ h₂ => by
        let N := max p.1 (max q.1 r.1)
        have hp : p.1 ≤ N := le_max_left _ _
        have hq : q.1 ≤ N := le_trans (le_max_left _ _) (le_max_right _ _)
        have hr : r.1 ≤ N := le_trans (le_max_right _ _) (le_max_right _ _)
        rw [T.rel_iff_le hp hq] at h₁
        rw [T.rel_iff_le hq hr] at h₂
        rw [T.rel_iff_le hp hr]
        exact h₁.trans h₂ }

/-- The limit of the tower: its cells, at all levels, with each cell identified with its
images. -/
def Lim := Quotient T.setoid

/-- The cell of the limit given by a cell of level `n`. -/
def cls (n : ℕ) (a : T.X n) : T.Lim := Quotient.mk _ ⟨n, a⟩

lemma cls_up {n m : ℕ} (h : n ≤ m) (a : T.X n) : T.cls m (T.up h a) = T.cls n a := by
  apply Quotient.sound
  change T.Rel _ _
  rw [T.rel_iff_le (le_refl m) h]
  simp

lemma cls_inj {n : ℕ} {a b : T.X n} : T.cls n a = T.cls n b ↔ a = b := by
  constructor
  · intro hab
    have := Quotient.exact hab
    change T.Rel _ _ at this
    rwa [T.rel_iff_le (le_refl n) (le_refl n), up_self, up_self] at this
  · rintro rfl; rfl

/-- Every cell of the limit comes from every level above some level. -/
lemma exists_cls (z : T.Lim) : ∃ n, ∀ m, n ≤ m → ∃ a, T.cls m a = z := by
  induction z using Quotient.inductionOn with
  | h p => exact ⟨p.1, fun m hm => ⟨T.up hm p.2, T.cls_up hm p.2⟩⟩

lemma cls_eq_iff {n m M : ℕ} (hn : n ≤ M) (hm : m ≤ M) {a : T.X n} {b : T.X m} :
    T.cls n a = T.cls m b ↔ T.up hn a = T.up hm b := by
  rw [← T.cls_up hn a, ← T.cls_up hm b, cls_inj]

/-- A level from which a cell of the limit comes. -/
noncomputable def lvl (z : T.Lim) : ℕ := Classical.choose (T.exists_cls z)

/-- A representative of a cell of the limit at a level above `lvl`. -/
noncomputable def rep (z : T.Lim) (N : ℕ) (h : T.lvl z ≤ N) : T.X N :=
  Classical.choose (Classical.choose_spec (T.exists_cls z) N h)

@[simp] lemma cls_rep (z : T.Lim) (N : ℕ) (h : T.lvl z ≤ N) : T.cls N (T.rep z N h) = z :=
  Classical.choose_spec (Classical.choose_spec (T.exists_cls z) N h)

lemma exists_rep (z : T.Lim) {N : ℕ} (h : T.lvl z ≤ N) : ∃ a, T.cls N a = z :=
  ⟨_, T.cls_rep z N h⟩

/-- The `k`-source in the limit, computed at a level above `k`. -/
noncomputable def scL (k : ℕ) (z : T.Lim) : T.Lim :=
  T.cls (max (T.lvl z) (k + 1))
    (sc (⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_right _ _)⟩ : Fin (max (T.lvl z) (k + 1)))
      (T.rep z _ (le_max_left _ _)))

noncomputable def tgL (k : ℕ) (z : T.Lim) : T.Lim :=
  T.cls (max (T.lvl z) (k + 1))
    (tg (⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_right _ _)⟩ : Fin (max (T.lvl z) (k + 1)))
      (T.rep z _ (le_max_left _ _)))

lemma scL_cls {k n : ℕ} (hk : k < n) (a : T.X n) :
    T.scL k (T.cls n a) = T.cls n (sc (⟨k, hk⟩ : Fin n) a) := by
  unfold scL
  have hb := T.cls_rep (T.cls n a) (max (T.lvl (T.cls n a)) (k + 1)) (le_max_left _ _)
  generalize T.rep (T.cls n a) _ (le_max_left _ _) = b at hb ⊢
  let N := max (T.lvl (T.cls n a)) (k + 1)
  rw [T.cls_eq_iff (le_max_left N n) (le_max_right N n)] at hb
  rw [T.cls_eq_iff (le_max_left N n) (le_max_right N n), up_sc, up_sc, hb]

lemma tgL_cls {k n : ℕ} (hk : k < n) (a : T.X n) :
    T.tgL k (T.cls n a) = T.cls n (tg (⟨k, hk⟩ : Fin n) a) := by
  unfold tgL
  have hb := T.cls_rep (T.cls n a) (max (T.lvl (T.cls n a)) (k + 1)) (le_max_left _ _)
  generalize T.rep (T.cls n a) _ (le_max_left _ _) = b at hb ⊢
  let N := max (T.lvl (T.cls n a)) (k + 1)
  rw [T.cls_eq_iff (le_max_left N n) (le_max_right N n)] at hb
  rw [T.cls_eq_iff (le_max_left N n) (le_max_right N n), up_tg, up_tg, hb]

lemma up_sc_is_tg_iff {n m : ℕ} (h : n ≤ m) (k : ℕ) (hk : k < n) {g f : T.X n} :
    sc_is_tg (⟨k, by omega⟩ : Fin m) (T.up h g) (T.up h f) ↔ sc_is_tg (⟨k, hk⟩ : Fin n) g f := by
  change sc _ _ = tg _ _ ↔ sc _ _ = tg _ _
  rw [← up_sc T h k hk, ← up_tg T h k hk, (T.up_injective h).eq_iff]

/-- The `k`-composite of the cells of two cells of level `N`, in the limit. -/
def compAt (k N : ℕ) (hk : k < N) (g f : T.X N) : Part T.Lim :=
  ⟨sc_is_tg (⟨k, hk⟩ : Fin N) g f, fun h => T.cls N (g ♯[(⟨k, hk⟩ : Fin N)] f ← h)⟩

lemma compAt_eq {k N n : ℕ} (hN : k < N) (hn : k < n) {g' f' : T.X N} {g f : T.X n}
    (hg : T.cls N g' = T.cls n g) (hf : T.cls N f' = T.cls n f) :
    T.compAt k N hN g' f' = T.compAt k n hn g f := by
  rw [T.cls_eq_iff (le_max_left N n) (le_max_right N n)] at hg hf
  have hdom : sc_is_tg (⟨k, hN⟩ : Fin N) g' f' ↔ sc_is_tg (⟨k, hn⟩ : Fin n) g f := by
    rw [← T.up_sc_is_tg_iff (le_max_left N n) k hN, ← T.up_sc_is_tg_iff (le_max_right N n) k hn,
      hg, hf]
  refine Part.ext' hdom fun h₁ h₂ => ?_
  have h₁' : sc_is_tg (⟨k, hN⟩ : Fin N) g' f' := h₁
  have h₂' : sc_is_tg (⟨k, hn⟩ : Fin n) g f := h₂
  show T.cls N (g' ♯[(⟨k, hN⟩ : Fin N)] f' ← h₁') = T.cls n (g ♯[(⟨k, hn⟩ : Fin n)] f ← h₂')
  rw [T.cls_eq_iff (le_max_left N n) (le_max_right N n), up_comp, up_comp]
  exact congr_comp₂ hf hg _

/-- The `k`-composition in the limit, computed at a level above `k`. -/
noncomputable def pcompL (k : ℕ) (g f : T.Lim) : Part T.Lim :=
  T.compAt k (max (max (T.lvl g) (T.lvl f)) (k + 1))
    (lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_right _ _))
    (T.rep g _ (le_trans (le_max_left _ _) (le_max_left _ _)))
    (T.rep f _ (le_trans (le_max_right _ _) (le_max_left _ _)))

lemma pcompL_cls {k n : ℕ} (hk : k < n) (g f : T.X n) :
    T.pcompL k (T.cls n g) (T.cls n f) = T.compAt k n hk g f :=
  T.compAt_eq _ hk (T.cls_rep _ _ _) (T.cls_rep _ _ _)

/-- Finitely many cells of the limit come from a common level above any bound. -/
lemma exists_cls_fam {r : ℕ} (z : Fin r → T.Lim) (b : ℕ) :
    ∃ N, b < N ∧ ∃ a : Fin r → T.X N, ∀ i, T.cls N (a i) = z i := by
  classical
  let N := max (Finset.univ.sup fun i => T.lvl (z i)) b + 1
  refine ⟨N, by omega, fun i => T.rep (z i) N ?_, fun i => T.cls_rep _ _ _⟩
  exact le_trans (Finset.le_sup (f := fun i => T.lvl (z i)) (Finset.mem_univ i)) (by omega)

lemma exists_cls₁ (z : T.Lim) (b : ℕ) : ∃ N, b < N ∧ ∃ a, T.cls N a = z := by
  obtain ⟨N, hN, a, ha⟩ := T.exists_cls_fam ![z] b
  exact ⟨N, hN, a 0, ha 0⟩

lemma exists_cls₂ (z₁ z₂ : T.Lim) (b : ℕ) :
    ∃ N, b < N ∧ ∃ a₁ a₂, T.cls N a₁ = z₁ ∧ T.cls N a₂ = z₂ := by
  obtain ⟨N, hN, a, ha⟩ := T.exists_cls_fam ![z₁, z₂] b
  exact ⟨N, hN, a 0, a 1, ha 0, ha 1⟩

lemma exists_cls₃ (z₁ z₂ z₃ : T.Lim) (b : ℕ) :
    ∃ N, b < N ∧ ∃ a₁ a₂ a₃, T.cls N a₁ = z₁ ∧ T.cls N a₂ = z₂ ∧ T.cls N a₃ = z₃ := by
  obtain ⟨N, hN, a, ha⟩ := T.exists_cls_fam ![z₁, z₂, z₃] b
  exact ⟨N, hN, a 0, a 1, a 2, ha 0, ha 1, ha 2⟩

lemma exists_cls₄ (z₁ z₂ z₃ z₄ : T.Lim) (b : ℕ) :
    ∃ N, b < N ∧ ∃ a₁ a₂ a₃ a₄, T.cls N a₁ = z₁ ∧ T.cls N a₂ = z₂ ∧ T.cls N a₃ = z₃ ∧
      T.cls N a₄ = z₄ := by
  obtain ⟨N, hN, a, ha⟩ := T.exists_cls_fam ![z₁, z₂, z₃, z₄] b
  exact ⟨N, hN, a 0, a 1, a 2, a 3, ha 0, ha 1, ha 2, ha 3⟩

/-- The compact categorial structure of the limit, with dimensions in `ℕ`. -/
noncomputable instance limStruct : CategoryStruct ℕ T.Lim where
  sc := T.scL
  tg := T.tgL
  pcomp := T.pcompL
  pcomp_dom := by
    intro k f g
    obtain ⟨N, hN, g', f', rfl, rfl⟩ := T.exists_cls₂ g f k
    rw [T.pcompL_cls hN, T.scL_cls hN, T.tgL_cls hN, cls_inj]
    rfl

lemma sc_cls {k n : ℕ} (hk : k < n) (a : T.X n) :
    sc k (T.cls n a) = T.cls n (sc (⟨k, hk⟩ : Fin n) a) := T.scL_cls hk a

lemma tg_cls {k n : ℕ} (hk : k < n) (a : T.X n) :
    tg k (T.cls n a) = T.cls n (tg (⟨k, hk⟩ : Fin n) a) := T.tgL_cls hk a

lemma sc_is_tg_cls {k n : ℕ} (hk : k < n) {g f : T.X n} :
    sc_is_tg k (T.cls n g) (T.cls n f) ↔ sc_is_tg (⟨k, hk⟩ : Fin n) g f := by
  change sc _ _ = tg _ _ ↔ _
  rw [T.sc_cls hk, T.tg_cls hk, cls_inj]; rfl

lemma comp_eq {k N : ℕ} (hk : k < N) {x y : T.Lim} {x' y' : T.X N} (hx : x = T.cls N x')
    (hy : y = T.cls N y') (h : sc_is_tg k x y) :
    x ♯[k] y ← h = T.cls N (x' ♯[(⟨k, hk⟩ : Fin N)] y' ←
      (T.sc_is_tg_cls hk).mp (hx ▸ hy ▸ h)) := by
  subst hx hy
  apply Part.get_eq_of_mem
  change _ ∈ T.pcompL k _ _
  rw [T.pcompL_cls hk]
  exact ⟨(T.sc_is_tg_cls hk).mp h, rfl⟩

section Laws

variable {k j : ℕ}

lemma lim_sc_sc (f : T.Lim) : sc k (sc k f) = sc k f := by
  obtain ⟨N, hN, a, rfl⟩ := T.exists_cls₁ f k
  simp only [T.sc_cls hN]; exact congrArg _ (PreCategory.sck_sck_eq_sck _ a)

lemma lim_tg_sc (f : T.Lim) : tg k (sc k f) = sc k f := by
  obtain ⟨N, hN, a, rfl⟩ := T.exists_cls₁ f k
  simp only [T.sc_cls hN, T.tg_cls hN]; exact congrArg _ (PreCategory.tgk_sck_eq_sck _ a)

lemma lim_sc_tg (f : T.Lim) : sc k (tg k f) = tg k f := by
  obtain ⟨N, hN, a, rfl⟩ := T.exists_cls₁ f k
  simp only [T.sc_cls hN, T.tg_cls hN]; exact congrArg _ (PreCategory.sck_tgk_eq_tgk _ a)

lemma lim_tg_tg (f : T.Lim) : tg k (tg k f) = tg k f := by
  obtain ⟨N, hN, a, rfl⟩ := T.exists_cls₁ f k
  simp only [T.tg_cls hN]; exact congrArg _ (PreCategory.tgk_tgk_eq_tgk _ a)

lemma lim_sc_comp {f g : T.Lim} (h : sc_is_tg k g f) : sc k (g ♯[k] f ← h) = sc k f := by
  obtain ⟨N, hN, g', f', rfl, rfl⟩ := T.exists_cls₂ g f k
  rw [T.comp_eq hN rfl rfl h]
  simp only [T.sc_cls hN]; exact congrArg _ (PreCategory.sck_compk_eq_sck _)

lemma lim_tg_comp {f g : T.Lim} (h : sc_is_tg k g f) : tg k (g ♯[k] f ← h) = tg k g := by
  obtain ⟨N, hN, g', f', rfl, rfl⟩ := T.exists_cls₂ g f k
  rw [T.comp_eq hN rfl rfl h]
  simp only [T.tg_cls hN]; exact congrArg _ (PreCategory.tgk_compk_eq_tgk _)

lemma lim_comp_sc (f : T.Lim) : f ♯[k] (sc k f) ← (T.lim_tg_sc f).symm = f := by
  obtain ⟨N, hN, a, rfl⟩ := T.exists_cls₁ f k
  exact (T.comp_eq hN rfl (T.sc_cls hN a) _).trans (congrArg _ (PreCategory.compk_sck_eq_id _ a))

lemma lim_tg_comp_self (f : T.Lim) : (tg k f) ♯[k] f ← (T.lim_sc_tg f) = f := by
  obtain ⟨N, hN, a, rfl⟩ := T.exists_cls₁ f k
  exact (T.comp_eq hN (T.tg_cls hN a) rfl _).trans (congrArg _ (PreCategory.compk_tgk_eq_id _ a))

lemma lim_assoc {f g h : T.Lim} (hgf : sc_is_tg k g f) (hhg : sc_is_tg k h g) :
    ((h ♯[k] g ← hhg) ♯[k] f ← ((T.lim_sc_comp hhg).trans hgf)) =
      (h ♯[k] (g ♯[k] f ← hgf) ← (hhg.trans (T.lim_tg_comp hgf).symm)) := by
  obtain ⟨N, hN, h', g', f', rfl, rfl, rfl⟩ := T.exists_cls₃ h g f k
  exact (T.comp_eq hN (T.comp_eq hN rfl rfl hhg) rfl _).trans
    ((congrArg _ (PreCategory.assoc _ _)).trans
    (T.comp_eq hN rfl (T.comp_eq hN rfl rfl hgf) _).symm)

end Laws

noncomputable instance limPreCategory : PreCategory ℕ T.Lim where
  sck_sck_eq_sck _ := T.lim_sc_sc
  tgk_sck_eq_sck _ := T.lim_tg_sc
  sck_tgk_eq_tgk _ := T.lim_sc_tg
  tgk_tgk_eq_tgk _ := T.lim_tg_tg
  sck_compk_eq_sck := T.lim_sc_comp
  tgk_compk_eq_tgk := T.lim_tg_comp
  compk_sck_eq_id _ := T.lim_comp_sc
  compk_tgk_eq_id _ := T.lim_tg_comp_self
  assoc := T.lim_assoc

section Laws

variable {k j : ℕ}

lemma lim_two (f : T.Lim) (h : j < k) :
    sc k (sc j f) = sc j f ∧ sc j (sc k f) = sc j f ∧ sc j (tg k f) = sc j f ∧
      tg k (tg j f) = tg j f ∧ tg j (tg k f) = tg j f ∧ tg j (sc k f) = tg j f := by
  obtain ⟨N, hN, a, rfl⟩ := T.exists_cls₁ f k
  have hj : j < N := by omega
  have hjk : (⟨j, hj⟩ : Fin N) < ⟨k, hN⟩ := h
  simp only [T.sc_cls hN, T.tg_cls hN, T.sc_cls hj, T.tg_cls hj]
  exact ⟨congrArg _ (Category.sck_scj_eq_scj a hjk), congrArg _ (Category.scj_sck_eq_scj a hjk),
    congrArg _ (Category.scj_tgk_eq_scj a hjk), congrArg _ (Category.tgk_tgj_eq_tgj a hjk),
    congrArg _ (Category.tgj_tgk_eq_tgj a hjk), congrArg _ (Category.tgj_sck_eq_tgj a hjk)⟩

lemma lim_sc_comp_j {f g : T.Lim} (h : j < k) (hgf : sc_is_tg j g f) (hd) :
    sc k (g ♯[j] f ← hgf) = (sc k g ♯.[j] sc k f).get hd := by
  obtain ⟨N, hN, g', f', rfl, rfl⟩ := T.exists_cls₂ g f k
  have hj : j < N := by omega
  have hjk : (⟨j, hj⟩ : Fin N) < ⟨k, hN⟩ := h
  rw [T.comp_eq hj rfl rfl hgf, T.sc_cls hN]
  exact (congrArg _ (Category.sck_compj_eq_compj_sck hjk _)).trans
    (T.comp_eq hj (T.sc_cls hN g') (T.sc_cls hN f') (sc_is_tg_of_dom hd)).symm

lemma lim_tg_comp_j {f g : T.Lim} (h : j < k) (hgf : sc_is_tg j g f) (hd) :
    tg k (g ♯[j] f ← hgf) = (tg k g ♯.[j] tg k f).get hd := by
  obtain ⟨N, hN, g', f', rfl, rfl⟩ := T.exists_cls₂ g f k
  have hj : j < N := by omega
  have hjk : (⟨j, hj⟩ : Fin N) < ⟨k, hN⟩ := h
  rw [T.comp_eq hj rfl rfl hgf, T.tg_cls hN]
  exact (congrArg _ (Category.tgk_compj_eq_compj_tgk hjk _)).trans
    (T.comp_eq hj (T.tg_cls hN g') (T.tg_cls hN f') (sc_is_tg_of_dom hd)).symm

lemma lim_interchange {f₁ f₂ g₁ g₂ : T.Lim} (h : j < k)
    (hg : sc_is_tg k g₂ g₁) (hf : sc_is_tg k f₂ f₁)
    (h₂ : sc_is_tg j g₂ f₂) (h₁ : sc_is_tg j g₁ f₁) (hd) (hd') :
    ((g₂ ♯[j] f₂ ← h₂) ♯.[k] (g₁ ♯[j] f₁ ← h₁)).get hd =
      ((g₂ ♯[k] g₁ ← hg) ♯.[j] (f₂ ♯[k] f₁ ← hf)).get hd' := by
  obtain ⟨N, hN, a₁, a₂, b₁, b₂, rfl, rfl, rfl, rfl⟩ := T.exists_cls₄ f₁ f₂ g₁ g₂ k
  have hj : j < N := by omega
  have hjk : (⟨j, hj⟩ : Fin N) < ⟨k, hN⟩ := h
  exact (T.comp_eq hN (T.comp_eq hj rfl rfl h₂) (T.comp_eq hj rfl rfl h₁)
    (sc_is_tg_of_dom hd)).trans
    ((congrArg _ (Category.interchange hjk _ _ _ _)).trans
      (T.comp_eq hj (T.comp_eq hN rfl rfl hg) (T.comp_eq hN rfl rfl hf) (sc_is_tg_of_dom hd')).symm)

end Laws

/-- The limit of a tower is a compact `ω`-category. -/
noncomputable instance limOmegaCategory : OmegaCategory T.Lim where
  sck_scj_eq_scj f h := (T.lim_two f h).1
  scj_sck_eq_scj f h := (T.lim_two f h).2.1
  scj_tgk_eq_scj f h := (T.lim_two f h).2.2.1
  tgk_tgj_eq_tgj f h := (T.lim_two f h).2.2.2.1
  tgj_tgk_eq_tgj f h := (T.lim_two f h).2.2.2.2.1
  tgj_sck_eq_tgj f h := (T.lim_two f h).2.2.2.2.2
  sck_compj_eq_compj_sck h hgf := T.lim_sc_comp_j h hgf _
  tgk_compj_eq_compj_tgk h hgf := T.lim_tg_comp_j h hgf _
  interchange h hg hf h₂ h₁ := T.lim_interchange h hg hf h₂ h₁ _ _
  is_cell z := by
    obtain ⟨N, -, a, rfl⟩ := T.exists_cls₁ z 0
    refine ⟨N, ?_⟩
    change sc N (T.cls N a) = T.cls N a
    rw [← T.cls_up (Nat.le_succ N) a, T.sc_cls (Nat.lt_succ_self N)]
    congr 1
    rw [T.up_succ le_rfl, up_self]
    exact T.e_cell N a

end Tower

end CategorialAlgebras.Compact
