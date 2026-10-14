import Stemma
import CategorialAlgebras.Evaluation
import CategorialAlgebras.Compact.Specification
import CategorialAlgebras.Compact.OmegaAlgebra

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "Compact categorial algebras as models" =>

```lean
universe u v w

namespace CategorialAlgebras.Compact

open Signature Term CTerm CategoryStruct

variable {S : Type u} {Sig : Signature.{u, v} S} {Index : Type} [Preorder Index]
```

# The partial algebra of cells

```lean
/-- The operations of the partial algebra of cells. -/
def cellOp (C : S → Type w) [∀ s, Category Index (C s)]
    (F : ∀ {ws : List S} {s : S}, Sig ws s → Functor Index (Arity C ws) (C s)) :
    (ws : List S) → (s : S) → CompactSignature Sig Index ws s → Arity C ws →. C s
  | _, _, .op σ, a => Part.some (F σ a)
  | _, _, .sc k _, a => Part.some (sc k (a ⟨0, by simp⟩))
  | _, _, .tg k _, a => Part.some (tg k (a ⟨0, by simp⟩))
  | _, _, .comp k _, a => a ⟨0, by simp⟩ ♯.[k] a ⟨1, by simp⟩

/-- The partial algebra of cells of an `S`-sorted compact category with operations. -/
abbrev cellAlgebra (C : S → Type w) [∀ s, Category Index (C s)]
    (F : ∀ {ws : List S} {s : S}, Sig ws s → Functor Index (Arity C ws) (C s)) :
    PartialAlgebra.{u, max u v, w} (CompactSignature Sig Index) where
  carrier := C
  op {ws s} σ := cellOp C F ws s σ

section CellAlgebra

variable {C : S → Type w} [∀ s, Category Index (C s)]
  {F : ∀ {ws : List S} {s : S}, Sig ws s → Functor Index (Arity C ws) (C s)}
  {val : ∀ s, Var S s → Part (C s)}

local notation "M" => cellAlgebra C F

lemma cell_eval_scT {k : Index} {s : S} {t : CTerm Sig Index s} {a : C s}
    (h : t.eval M val = Part.some a) : (scT k t).eval M val = Part.some (sc k a) := by
  rw [scT, eval_app₁_of_eq_some _ _ _ h]; rfl

lemma cell_eval_tgT {k : Index} {s : S} {t : CTerm Sig Index s} {a : C s}
    (h : t.eval M val = Part.some a) : (tgT k t).eval M val = Part.some (tg k a) := by
  rw [tgT, eval_app₁_of_eq_some _ _ _ h]; rfl

lemma cell_eval_compT {k : Index} {s : S} {t t' : CTerm Sig Index s} {a b : C s}
    (h : t.eval M val = Part.some a) (h' : t'.eval M val = Part.some b) :
    (compT k t t').eval M val = a ♯.[k] b := by
  rw [compT, eval_app₂_of_eq_some _ _ _ h h']; rfl

lemma cell_eval_compT_some {k : Index} {s : S} {t t' : CTerm Sig Index s} {a b : C s}
    (h : t.eval M val = Part.some a) (h' : t'.eval M val = Part.some b)
    (hab : sc_is_tg k a b) :
    (compT k t t').eval M val = Part.some (a ♯[k] b ← hab) := by
  rw [cell_eval_compT h h']; exact (Part.some_get _).symm

lemma cell_eval_opT {ws : List S} {s : S} (σ : Sig ws s)
    {ts : (j : Fin ws.length) → CTerm Sig Index (ws.get j)} {a : Arity C ws}
    (h : ∀ j, (ts j).eval M val = Part.some (a j)) :
    (opT σ ts).eval M val = Part.some (F σ a) := by
  rw [opT, eval_app_of_eq_some _ _ _ h]; rfl

lemma cell_eval_x {s : S} {i : ℕ} (h : (val s i).Dom) :
    (x (Sig := Sig) (Index := Index) (s := s) i).eval M val = Part.some ((val s i).get h) := by
  simp only [CTerm.x]; exact (Part.some_get h).symm

/-- The value of a composite that is defined. -/
lemma cell_comp_dom {k : Index} {s : S} {t t' : CTerm Sig Index s} {a b : C s}
    (h : t.eval M val = Part.some a) (h' : t'.eval M val = Part.some b)
    (hd : (EEq.defined (compT k t t')).Holds M val) : sc_is_tg k a b := by
  rw [EEq.holds_defined_iff, cell_eval_compT h h'] at hd
  exact sc_is_tg_of_dom hd

open PreCategory Category in
/-- The partial algebra of cells is a model of the compact specification. -/
theorem cellAlgebra_holds : ∀ q ∈ compactSpec Sig Index, q.Holds (cellAlgebra C F) := by
  intro q hq val hvars hprem
  have var : ∀ {s : S} (i : ℕ), (⟨s, i⟩ : Σ t, Var S t) ∈ q.vars →
      ∃ a, (x (Sig := Sig) (Index := Index) (s := s) i).eval M val = Part.some a :=
    fun i hi => ⟨_, cell_eval_x (hvars _ hi)⟩
  cases hq with
  | @A0 ws s σ xs =>
    choose a ha using fun j => var (s := ws.get j) (xs j) (by simp [QEEq.vars, EEq.vars, EEq.defined, opT, x]; try exact ⟨j, rfl, rfl⟩)
    rw [EEq.holds_defined_iff, cell_eval_opT σ ha]; trivial
  | A1_sc k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.defined, scT, x])
    rw [EEq.holds_defined_iff, cell_eval_scT ha]; trivial
  | A1_tg k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.defined, tgT, x])
    rw [EEq.holds_defined_iff, cell_eval_tgT ha]; trivial
  | A2_sc_sc k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', scT, x])
    rw [EEq.holds_mk'_iff (cell_eval_scT (cell_eval_scT ha)) (cell_eval_scT ha)]
    exact sck_sck_eq_sck k a
  | A2_sc_tg k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', scT, tgT, x])
    rw [EEq.holds_mk'_iff (cell_eval_scT (cell_eval_tgT ha)) (cell_eval_tgT ha)]
    exact sck_tgk_eq_tgk k a
  | A2_tg_sc k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', scT, tgT, x])
    rw [EEq.holds_mk'_iff (cell_eval_tgT (cell_eval_scT ha)) (cell_eval_scT ha)]
    exact tgk_sck_eq_sck k a
  | A2_tg_tg k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', tgT, x])
    rw [EEq.holds_mk'_iff (cell_eval_tgT (cell_eval_tgT ha)) (cell_eval_tgT ha)]
    exact tgk_tgk_eq_tgk k a
  | A3_dom k s i j =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    obtain ⟨b, hb⟩ := var (s := s) j (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    have hab := cell_comp_dom (k := k) ha hb (hprem _ (by simp))
    rw [EEq.holds_mk'_iff (cell_eval_scT ha) (cell_eval_tgT hb)]
    exact hab
  | A3_def k s i j =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    obtain ⟨b, hb⟩ := var (s := s) j (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    have hab := (EEq.holds_mk'_iff (cell_eval_scT (k := k) ha) (cell_eval_tgT (k := k) hb)).mp (hprem _ (by simp))
    rw [EEq.holds_defined_iff, cell_eval_compT ha hb]
    exact dom_of_sc_is_tg hab
  | A4_sc k s i j =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    obtain ⟨b, hb⟩ := var (s := s) j (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    have hab := cell_comp_dom (k := k) ha hb (hprem _ (by simp))
    rw [EEq.holds_mk'_iff (cell_eval_scT (cell_eval_compT_some ha hb hab)) (cell_eval_scT hb)]
    exact sck_compk_eq_sck hab
  | A4_tg k s i j =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    obtain ⟨b, hb⟩ := var (s := s) j (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    have hab := cell_comp_dom (k := k) ha hb (hprem _ (by simp))
    rw [EEq.holds_mk'_iff (cell_eval_tgT (cell_eval_compT_some ha hb hab)) (cell_eval_tgT ha)]
    exact tgk_compk_eq_tgk hab
  | A5_sc k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', compT, scT, x])
    rw [EEq.holds_mk'_iff
      (cell_eval_compT_some ha (cell_eval_scT ha) (tgk_sck_eq_sck k a).symm) ha]
    exact compk_sck_eq_id k a
  | A5_tg k s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', compT, tgT, x])
    rw [EEq.holds_mk'_iff (cell_eval_compT_some (cell_eval_tgT ha) ha (sck_tgk_eq_tgk k a)) ha]
    exact compk_tgk_eq_id k a
  | A6 k s i j l =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    obtain ⟨b, hb⟩ := var (s := s) j (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    obtain ⟨c, hc⟩ := var (s := s) l (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    have hab := cell_comp_dom (k := k) ha hb (hprem _ (by simp))
    have hbc := cell_comp_dom (k := k) hb hc (hprem _ (by simp))
    rw [EEq.holds_mk'_iff
      (cell_eval_compT_some (cell_eval_compT_some ha hb hab) hc (PreCategory.compl_assoc hbc hab))
      (cell_eval_compT_some ha (cell_eval_compT_some hb hc hbc) (PreCategory.compr_assoc hbc hab))]
    exact assoc hbc hab
  | @A7_sc k ws s σ xs =>
    choose a ha using fun j => var (s := ws.get j) (xs j) (by simp [QEEq.vars, EEq.vars, EEq.mk', opT, scT, x]; try exact ⟨j, rfl, rfl⟩)
    rw [EEq.holds_mk'_iff (cell_eval_scT (cell_eval_opT σ ha))
      (cell_eval_opT σ fun j => cell_eval_scT (ha j))]
    exact ((F σ).map_sc_eq_sc_map k a).symm
  | @A7_tg k ws s σ xs =>
    choose a ha using fun j => var (s := ws.get j) (xs j) (by simp [QEEq.vars, EEq.vars, EEq.mk', opT, tgT, x]; try exact ⟨j, rfl, rfl⟩)
    rw [EEq.holds_mk'_iff (cell_eval_tgT (cell_eval_opT σ ha))
      (cell_eval_opT σ fun j => cell_eval_tgT (ha j))]
    exact ((F σ).map_tg_eq_tg_map k a).symm
  | @A8 k ws s σ xs ys =>
    choose a ha using fun j => var (s := ws.get j) (xs j)
      (by simp [QEEq.vars, EEq.vars, EEq.mk', opT, compT, x]
          exact Or.inl (Or.inr (Or.inl ⟨j, rfl, rfl⟩)))
    choose b hb using fun j => var (s := ws.get j) (ys j)
      (by simp [QEEq.vars, EEq.vars, EEq.mk', opT, compT, x]
          exact Or.inl (Or.inr (Or.inr ⟨j, rfl, rfl⟩)))
    have hab : ∀ j, sc_is_tg k (a j) (b j) := fun j =>
      cell_comp_dom (ha j) (hb j) (hprem _ (List.mem_ofFn.mpr ⟨j, rfl⟩))
    have hF : sc_is_tg k (F σ a) (F σ b) := (F σ).comp_map (pi_sc_is_tg.mpr hab)
    rw [EEq.holds_mk'_iff
      (cell_eval_opT σ fun j => cell_eval_compT_some (ha j) (hb j) (hab j))
      (cell_eval_compT_some (cell_eval_opT σ ha) (cell_eval_opT σ hb) hF)]
    exact (F σ).map_comp_eq_comp_map (pi_sc_is_tg.mpr hab)
  | AB1_sc_sc l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', scT, x])
    rw [EEq.holds_mk'_iff (cell_eval_scT (cell_eval_scT ha)) (cell_eval_scT ha)]
    exact sck_scj_eq_scj a h
  | AB1_tg_tg l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', tgT, x])
    rw [EEq.holds_mk'_iff (cell_eval_tgT (cell_eval_tgT ha)) (cell_eval_tgT ha)]
    exact tgk_tgj_eq_tgj a h
  | AB1_sc_sck l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', scT, x])
    rw [EEq.holds_mk'_iff (cell_eval_scT (cell_eval_scT ha)) (cell_eval_scT ha)]
    exact scj_sck_eq_scj a h
  | AB1_tg_tgk l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', tgT, x])
    rw [EEq.holds_mk'_iff (cell_eval_tgT (cell_eval_tgT ha)) (cell_eval_tgT ha)]
    exact tgj_tgk_eq_tgj a h
  | AB1_sc_tgk l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', scT, tgT, x])
    rw [EEq.holds_mk'_iff (cell_eval_scT (cell_eval_tgT ha)) (cell_eval_scT ha)]
    exact scj_tgk_eq_scj a h
  | AB1_tg_sck l k h s i =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', scT, tgT, x])
    rw [EEq.holds_mk'_iff (cell_eval_tgT (cell_eval_scT ha)) (cell_eval_tgT ha)]
    exact tgj_sck_eq_tgj a h
  | AB2_sc l k h s i j =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    obtain ⟨b, hb⟩ := var (s := s) j (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    have hab := cell_comp_dom (k := l) ha hb (hprem _ (by simp))
    rw [EEq.holds_mk'_iff (cell_eval_scT (cell_eval_compT_some ha hb hab))
      (cell_eval_compT_some (cell_eval_scT ha) (cell_eval_scT hb) (Category.sc_tg_j_sc h hab))]
    exact sck_compj_eq_compj_sck h hab
  | AB2_tg l k h s i j =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    obtain ⟨b, hb⟩ := var (s := s) j (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    have hab := cell_comp_dom (k := l) ha hb (hprem _ (by simp))
    rw [EEq.holds_mk'_iff (cell_eval_tgT (cell_eval_compT_some ha hb hab))
      (cell_eval_compT_some (cell_eval_tgT ha) (cell_eval_tgT hb) (Category.sc_tg_j_tg h hab))]
    exact tgk_compj_eq_compj_tgk h hab
  | AB3 l k h s i j p q =>
    obtain ⟨a, ha⟩ := var (s := s) i (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    obtain ⟨b, hb⟩ := var (s := s) j (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    obtain ⟨c, hc⟩ := var (s := s) p (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    obtain ⟨d, hd⟩ := var (s := s) q (by simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, compT, x])
    have h₁ := cell_comp_dom (k := l) ha hb (hprem _ (by simp))
    have h₂ := cell_comp_dom (k := l) hc hd (hprem _ (by simp))
    have h₃ := cell_comp_dom (k := k) ha hc (hprem _ (by simp))
    have h₄ := cell_comp_dom (k := k) hb hd (hprem _ (by simp))
    rw [EEq.holds_mk'_iff
      (cell_eval_compT_some (cell_eval_compT_some ha hb h₁) (cell_eval_compT_some hc hd h₂)
        (Category.sc_tg_k_interchange h h₃ h₄ h₁ h₂))
      (cell_eval_compT_some (cell_eval_compT_some ha hc h₃) (cell_eval_compT_some hb hd h₄)
        (Category.sc_tg_j_interchange h h₃ h₄ h₁))]
    exact interchange h h₃ h₄ h₁ h₂

end CellAlgebra
```
