import CategorialAlgebras.PartialAlgebra

/-!
# Evaluation

Lemmas to compute the value of a term in a partial algebra and to decide whether an existence
equation holds, and valuations that assign given values to finitely many variables. They are
used to show that the categorial algebras are the models of their specifications.
-/

universe u v w

namespace CategorialAlgebras

open Signature

variable {S : Type u} {Sig : Signature.{u, v} S} {V : S → Type}

namespace Term

variable (A : PartialAlgebra.{u, v, w} Sig) (val : ∀ s, V s → Part (A s))

@[simp] lemma eval_var {s : S} (x : V s) : (Term.var x : Term Sig V s).eval A val = val s x := by
  simp [Term.eval]

/-- An operation symbol applied to terms with known values. -/
lemma eval_app_of_eq_some {ws : List S} {s : S} (σ : Sig ws s)
    {ts : (j : Fin ws.length) → Term Sig V (ws.get j)} {a : Arity A ws}
    (h : ∀ j, (ts j).eval A val = Part.some (a j)) :
    (Term.app σ ts).eval A val = A.op σ a := by
  have hd : ∀ j, ((ts j).eval A val).Dom := fun j => by rw [h j]; trivial
  have hf : ∀ hd' : ∀ j, ((ts j).eval A val).Dom,
      (fun j => ((ts j).eval A val).get (hd' j)) = a := by
    intro hd'; funext j; exact Part.get_eq_of_mem (by rw [h j]; exact Part.mem_some _) _
  apply Part.ext'
  · change (∃ h : ∀ j, _, (A.op σ _).Dom) ↔ _
    constructor
    · rintro ⟨h₁, h₂⟩; rwa [hf h₁] at h₂
    · intro h₂; exact ⟨hd, by rwa [hf hd]⟩
  · rintro ⟨h₁, h₂⟩ h₃
    exact Part.get_eq_get_of_eq _ _ (congrArg (A.op σ) (hf h₁))

lemma eval_app₁_of_eq_some {s t : S} (σ : Sig [s] t) {x : Term Sig V s} {a : A s}
    (h : x.eval A val = Part.some a) :
    (app₁ σ x).eval A val = A.op σ (fun | ⟨0, _⟩ => a) :=
  eval_app_of_eq_some A val σ fun | ⟨0, _⟩ => h

lemma eval_app₂_of_eq_some {s₀ s₁ t : S} (σ : Sig [s₀, s₁] t) {x : Term Sig V s₀}
    {y : Term Sig V s₁} {a : A s₀} {b : A s₁}
    (hx : x.eval A val = Part.some a) (hy : y.eval A val = Part.some b) :
    (app₂ σ x y).eval A val = A.op σ (fun | ⟨0, _⟩ => a | ⟨1, _⟩ => b) :=
  eval_app_of_eq_some A val σ fun | ⟨0, _⟩ => hx | ⟨1, _⟩ => hy

/-- If the value of `σ((t_j)_j)` is defined, so are the values of the `t_j`, and it is the value
of `σ` on them. -/
lemma eval_app_dom {ws : List S} {s : S} (σ : Sig ws s)
    {ts : (j : Fin ws.length) → Term Sig V (ws.get j)} (h : ((Term.app σ ts).eval A val).Dom) :
    ∃ a : Arity A ws, (∀ j, (ts j).eval A val = Part.some (a j)) ∧
      (Term.app σ ts).eval A val = A.op σ a := by
  obtain ⟨h₁, -⟩ := h
  refine ⟨fun j => ((ts j).eval A val).get (h₁ j), fun j => (Part.some_get _).symm, ?_⟩
  exact eval_app_of_eq_some A val σ fun j => (Part.some_get _).symm

/-- The variables of a term with a defined value are defined. -/
lemma vars_dom_of_eval_dom : ∀ {s : S} (t : Term Sig V s), (t.eval A val).Dom →
    ∀ x ∈ t.vars, (val x.1 x.2).Dom
  | _, .var y, h, x, hx => by
    simp only [Term.vars, Set.mem_singleton_iff] at hx; subst hx; simpa using h
  | _, .app σ ts, h, x, hx => by
    simp only [Term.vars, Set.mem_iUnion] at hx
    obtain ⟨j, hj⟩ := hx
    obtain ⟨a, ha, -⟩ := eval_app_dom A val σ h
    exact vars_dom_of_eval_dom (ts j) (by rw [ha j]; trivial) x hj

@[simp] lemma vars_var {s : S} (x : V s) : (Term.var x : Term Sig V s).vars = {⟨s, x⟩} := by
  simp [Term.vars]

@[simp] lemma vars_app {ws : List S} {s : S} (σ : Sig ws s)
    (ts : (j : Fin ws.length) → Term Sig V (ws.get j)) :
    (Term.app σ ts).vars = ⋃ j, (ts j).vars := by
  simp [Term.vars]

@[simp] lemma vars_app₁ {s t : S} (σ : Sig [s] t) (x : Term Sig V s) :
    (app₁ σ x).vars = x.vars := by
  ext y; simp only [app₁, vars_app, Set.mem_iUnion]
  exact ⟨fun ⟨⟨0, _⟩, h⟩ => h, fun h => ⟨⟨0, by simp⟩, h⟩⟩

@[simp] lemma vars_app₂ {s₀ s₁ t : S} (σ : Sig [s₀, s₁] t) (x : Term Sig V s₀)
    (y : Term Sig V s₁) : (app₂ σ x y).vars = x.vars ∪ y.vars := by
  ext z; simp only [app₂, vars_app, Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨⟨j, hj⟩, h⟩
    match j, hj with
    | 0, _ => exact Or.inl h
    | 1, _ => exact Or.inr h
  · rintro (h | h)
    · exact ⟨⟨0, by simp⟩, h⟩
    · exact ⟨⟨1, by simp⟩, h⟩

end Term

/-- An existence equation between terms with known values holds exactly when the values are
equal. -/
lemma EEq.holds_mk'_iff {A : PartialAlgebra.{u, v, w} Sig} {val : ∀ s, V s → Part (A s)}
    {s : S} {t t' : Term Sig V s} {a b : A s}
    (ht : t.eval A val = Part.some a) (ht' : t'.eval A val = Part.some b) :
    (EEq.mk' t t').Holds A val ↔ a = b := by
  simp only [EEq.Holds, EEq.mk', ht, ht']
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨trivial, trivial, h⟩⟩

lemma EEq.holds_defined_iff {A : PartialAlgebra.{u, v, w} Sig} {val : ∀ s, V s → Part (A s)}
    {s : S} {t : Term Sig V s} :
    (EEq.defined t).Holds A val ↔ (t.eval A val).Dom := by
  simp only [EEq.Holds, EEq.defined]
  exact ⟨fun ⟨h, _, _⟩ => h, fun h => ⟨h, h, by trivial⟩⟩

/-- An existence equation holds when both sides have the same value. -/
lemma EEq.holds_mk' {A : PartialAlgebra.{u, v, w} Sig} {val : ∀ s, V s → Part (A s)}
    {s : S} {t t' : Term Sig V s} {a : Part (A s)} (ha : a.Dom)
    (ht : t.eval A val = a) (ht' : t'.eval A val = a) : (EEq.mk' t t').Holds A val := by
  simp only [EEq.Holds, EEq.mk', ht, ht']
  exact ⟨ha, ha, by trivial⟩

/-- If both sides of an existence equation are defined, its variables are defined. -/
lemma EEq.vars_dom_of_holds {A : PartialAlgebra.{u, v, w} Sig} {val : ∀ s, V s → Part (A s)}
    {e : EEq Sig V} (h : e.Holds A val) : ∀ x ∈ e.vars, (val x.1 x.2).Dom := by
  obtain ⟨h₁, h₂, -⟩ := h
  rintro x (hx | hx)
  · exact Term.vars_dom_of_eval_dom A val _ h₁ x hx
  · exact Term.vars_dom_of_eval_dom A val _ h₂ x hx

/-! ## Valuations of finitely many variables -/

section Assign

open Classical in
/-- The valuation that sends the variable `pts i` to `a i`, and is undefined elsewhere. -/
noncomputable def assign {ι : Type} {A : S → Type w} (pts : ι → Σ t, V t)
    (a : ∀ i, A (pts i).1) : ∀ s, V s → Part (A s) :=
  fun s x => if h : ∃ i, pts i = ⟨s, x⟩ then
    Part.some ((show (pts h.choose).1 = s from congrArg Sigma.fst h.choose_spec) ▸ a h.choose)
  else Part.none

variable {ι : Type} {A : S → Type w} {pts : ι → Σ t, V t} (a : ∀ i, A (pts i).1)

lemma assign_apply (hpts : Function.Injective pts) (i : ι) :
    assign pts a (pts i).1 (pts i).2 = Part.some (a i) := by
  have h : ∃ c, pts c = ⟨(pts i).1, (pts i).2⟩ := ⟨i, rfl⟩
  simp only [assign, h, ↓reduceDIte, Part.some_inj]
  have key : ∀ c (hc : (pts c).1 = (pts i).1), c = i → (hc ▸ a c : A (pts i).1) = a i := by
    rintro c hc rfl; rfl
  exact key _ _ (hpts h.choose_spec)

lemma assign_dom {s : S} {x : V s} : (assign pts a s x).Dom ↔ ⟨s, x⟩ ∈ Set.range pts := by
  unfold assign
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => trivial⟩
  · exact ⟨fun h' => h'.elim, fun h' => h h'⟩

end Assign

end CategorialAlgebras
