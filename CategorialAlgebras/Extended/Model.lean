import Mathlib.Data.Fin.VecNotation
import CategorialAlgebras.Evaluation
import CategorialAlgebras.Extended.Specification

/-!
# The structure of a model of the extended specification

The operations of a model of the extended specification `C^{Σ^{ext(n)}}` and the laws they satisfy,
read off its axioms: the `(j,k)`-sources, `(j,k)`-targets and `(k,j)`-identities are total, the
`j`-composition of `k`-cells is defined exactly on the pairs whose `(j,k)`-source and
`(j,k)`-target agree, and the axioms (EA…) become equations between these operations. They are
used to show that unification sends models to models, and that graduation after unification is
isomorphic to the identity.
-/

universe u v w

namespace CategorialAlgebras.Extended

open Signature Term ETerm

variable {S : Type u} {Sig : Signature.{u, v} S} {Index : Type} [Preorder Index]

/-! ## The copies of the operation symbols on families -/

/-- A family of elements of sorts `(k, s_p)`, seen as a family of the arity of `σ_k`. -/
def liftFam {A : Index × S → Type w} (k : Index) {ws : List S} (a : ∀ p : Fin ws.length, A (k, ws.get p)) :
    Arity A (ws.map fun t => (k, t)) :=
  fun q => cast (congrArg A (by simp)) (a (Fin.cast (by simp) q))

omit [Preorder Index] in
/-- Every family of the arity of `σ_k` is a lifted family. -/
lemma liftFam_unlift {A : Index × S → Type w} (k : Index) {ws : List S}
    (a : Arity A (ws.map fun t => (k, t))) :
    liftFam k (fun p => cast (congrArg A (by simp)) (a (Fin.cast (by simp) p))) = a := by
  funext q
  simp only [liftFam, cast_cast]
  have key : ∀ q' (e : q' = q) (h : A ((ws.map fun t => (k, t)).get q') =
      A ((ws.map fun t => (k, t)).get q)), cast h (a q') = a q := by
    rintro _ rfl _; rfl
  exact key _ (Fin.ext rfl) _

lemma eval_cast {A : PartialAlgebra.{u, max u v, w} (ExtendedSignature Sig Index)}
    {val : ∀ t, EVar S Index t → Part (A t)} {t t' : Index × S} (e : t = t')
    (r : ETerm Sig Index t) (b : A t) (h : r.eval A val = Part.some b) :
    (cast (congrArg (ETerm Sig Index) e) r).eval A val = Part.some (cast (congrArg A e) b) := by
  subst e; exact h

/-- The value of `σ_k((t_p)_p)`, when the values of the `t_p` are known. -/
lemma eval_opT {A : PartialAlgebra.{u, max u v, w} (ExtendedSignature Sig Index)}
    {val : ∀ t, EVar S Index t → Part (A t)} (k : Index) {ws : List S} {s : S} (σ : Sig ws s)
    {ts : (p : Fin ws.length) → ETerm Sig Index (k, ws.get p)} {a : ∀ p, A (k, ws.get p)}
    (h : ∀ p, (ts p).eval A val = Part.some (a p)) :
    (opT k σ ts).eval A val = A.op (.op k σ) (liftFam k a) :=
  eval_app_of_eq_some A val _ fun _ => eval_cast (by simp) _ _ (h _)

lemma vars_cast {t t' : Index × S} (h : ETerm Sig Index t = ETerm Sig Index t') (e : t = t')
    (r : ETerm Sig Index t) : (cast h r).vars = r.vars := by
  subst e; rfl

lemma vars_opT (k : Index) {ws : List S} {s : S} (σ : Sig ws s)
    (ts : (p : Fin ws.length) → ETerm Sig Index (k, ws.get p)) :
    (opT k σ ts).vars = ⋃ p, (ts p).vars := by
  ext y
  simp only [opT, vars_app, Set.mem_iUnion, liftArgs]
  constructor
  · rintro ⟨q, hq⟩
    rw [vars_cast _ ?e] at hq
    · exact ⟨_, hq⟩
    · simp
  · rintro ⟨p, hp⟩
    refine ⟨Fin.cast (by simp) p, ?_⟩
    rw [vars_cast _ ?e']
    · simpa using hp
    · simp

/-- The argument of a unary operation symbol. -/
def arg₁ {A : Index × S → Type w} {t : Index × S} (a : A t) : Arity A [t] := fun | ⟨0, _⟩ => a

/-- The arguments of a binary operation symbol. -/
def arg₂ {A : Index × S → Type w} {t t' : Index × S} (a : A t) (b : A t') : Arity A [t, t'] :=
  fun | ⟨0, _⟩ => a | ⟨1, _⟩ => b

lemma eval_app₁ {A : PartialAlgebra.{u, max u v, w} (ExtendedSignature Sig Index)}
    {val : ∀ t, EVar S Index t → Part (A t)} {t t' : Index × S} (σ : ExtendedSignature Sig Index [t] t')
    {r : ETerm Sig Index t} {a : A t} (h : r.eval A val = Part.some a) :
    (app₁ σ r).eval A val = A.op σ (arg₁ a) := by
  rw [eval_app₁_of_eq_some _ _ _ h]
  congr 1; funext i
  match i with
  | ⟨0, _⟩ => rfl

lemma eval_app₂ {A : PartialAlgebra.{u, max u v, w} (ExtendedSignature Sig Index)}
    {val : ∀ t, EVar S Index t → Part (A t)} {t₀ t₁ t' : Index × S}
    (σ : ExtendedSignature Sig Index [t₀, t₁] t') {r : ETerm Sig Index t₀} {r' : ETerm Sig Index t₁}
    {a : A t₀} {b : A t₁} (h : r.eval A val = Part.some a) (h' : r'.eval A val = Part.some b) :
    (app₂ σ r r').eval A val = A.op σ (arg₂ a b) := by
  rw [eval_app₂_of_eq_some _ _ _ h h']
  congr 1; funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

namespace Model

variable (M : ExtendedPAlg.{u, v, w} Sig Index)

/-- Every axiom of the specification holds in a model, under a valuation of finitely many
variables that covers its variables. -/
lemma holds {q : QEEq (ExtendedSignature Sig Index) (EVar S Index)} (hq : ExtendedAxiom Sig Index q)
    {ι : Type} {pts : ι → Σ t, EVar S Index t} (a : ∀ i, M.1 (pts i).1)
    (hvars : q.vars ⊆ Set.range pts)
    (hprem : ∀ e ∈ q.premises, e.Holds M.1 (assign pts a)) :
    q.conclusion.Holds M.1 (assign pts a) :=
  M.2 q hq _ (fun _ hx => (assign_dom a).mpr (hvars hx)) hprem

omit [Preorder Index] in
lemma injective_of_snd {ι : Type} {pts : ι → Σ t, EVar S Index t}
    (h : Function.Injective fun i => ((pts i).2 : ℕ)) : Function.Injective pts :=
  fun _ _ e => h (congrArg (fun y : Σ t, EVar S Index t => (y.2 : ℕ)) e)

/-- The variables `x_0, …, x_{m-1}` of sort `t`. -/
def ptsOf (t : Index × S) (m : ℕ) : Fin m → Σ t, EVar S Index t := fun i => ⟨t, i.val⟩

omit [Preorder Index] in
lemma ptsOf_injective (t : Index × S) (m : ℕ) :
    Function.Injective (ptsOf (S := S) (Index := Index) t m) :=
  injective_of_snd fun _ _ h => Fin.ext h

omit [Preorder Index] in
lemma mem_range_ptsOf {t : Index × S} {m : ℕ} {y : Σ t, EVar S Index t} :
    y ∈ Set.range (ptsOf t m) ↔ y.1 = t ∧ (y.2 : ℕ) < m := by
  obtain ⟨t', i⟩ := y
  constructor
  · rintro ⟨j, hj⟩; cases hj; exact ⟨rfl, j.2⟩
  · rintro ⟨rfl, h⟩; exact ⟨⟨i, h⟩, rfl⟩

lemma eval_ptsOf {t : Index × S} {m : ℕ} (a : Fin m → M.1 t) (i : ℕ) (h : i < m) {b : M.1 t}
    (hb : a ⟨i, h⟩ = b) :
    (x (Sig := Sig) (t := t) i).eval M.1 (assign (ptsOf t m) a) = Part.some b := by
  subst hb; simp only [x, eval_var]; exact assign_apply a (ptsOf_injective t m) ⟨i, h⟩

/-- The variables `x_p` of sort `(k, s_p)`, for a word `s`. -/
def ptsFam (k : Index) (ws : List S) : Fin ws.length → Σ t, EVar S Index t :=
  fun p => ⟨(k, ws.get p), p.val⟩

omit [Preorder Index] in
lemma ptsFam_injective (k : Index) (ws : List S) :
    Function.Injective (ptsFam (S := S) k ws) :=
  injective_of_snd fun _ _ h => Fin.ext h

lemma eval_ptsFam {k : Index} {ws : List S} (a : ∀ p, M.1 (ptsFam k ws p).1) (p : Fin ws.length) :
    (x (Sig := Sig) (t := (k, ws.get p)) p.val).eval M.1 (assign (ptsFam k ws) a) =
      Part.some (a p) := by
  simp only [x, eval_var]; exact assign_apply a (ptsFam_injective k ws) p

/-- The variables `x_{2p}` and `x_{2p+1}` of sort `(k, s_p)`, for a word `s`. -/
def ptsFam₂ (k : Index) (ws : List S) : Fin ws.length ⊕ Fin ws.length → Σ t, EVar S Index t :=
  Sum.elim (fun p => ⟨(k, ws.get p), 2 * p.val⟩) (fun p => ⟨(k, ws.get p), 2 * p.val + 1⟩)

omit [Preorder Index] in
lemma ptsFam₂_injective (k : Index) (ws : List S) :
    Function.Injective (ptsFam₂ (S := S) k ws) := by
  refine injective_of_snd ?_
  rintro (i | i) (j | j) h <;> simp only [ptsFam₂, Sum.elim_inl, Sum.elim_inr] at h
  · exact congrArg Sum.inl (Fin.ext (by omega))
  · omega
  · omega
  · exact congrArg Sum.inr (Fin.ext (by omega))

/-- The families `a` and `b` as values of `x_{2p}` and `x_{2p+1}`. -/
def vals₂ {k : Index} {ws : List S} (a b : ∀ p : Fin ws.length, M.1 (k, ws.get p)) :
    ∀ i, M.1 (ptsFam₂ k ws i).1
  | .inl p => a p
  | .inr p => b p

lemma eval_ptsFam₂_inl {k : Index} {ws : List S} (a b : ∀ p : Fin ws.length, M.1 (k, ws.get p))
    (p : Fin ws.length) :
    (x (Sig := Sig) (t := (k, ws.get p)) (2 * p.val)).eval M.1 (assign (ptsFam₂ k ws) (vals₂ M a b)) =
      Part.some (a p) := by
  simp only [x, eval_var]; exact assign_apply (vals₂ M a b) (ptsFam₂_injective k ws) (.inl p)

lemma eval_ptsFam₂_inr {k : Index} {ws : List S} (a b : ∀ p : Fin ws.length, M.1 (k, ws.get p))
    (p : Fin ws.length) :
    (x (Sig := Sig) (t := (k, ws.get p)) (2 * p.val + 1)).eval M.1
        (assign (ptsFam₂ k ws) (vals₂ M a b)) = Part.some (b p) := by
  simp only [x, eval_var]; exact assign_apply (vals₂ M a b) (ptsFam₂_injective k ws) (.inr p)

end Model

/-- The variables of an axiom with variables `x_0, …, x_{m-1}` of one sort. -/
local macro "model_vars" : tactic => `(tactic| (
  rintro ⟨t, i⟩ hy
  rw [Model.mem_range_ptsOf]
  simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, scT, tgT, idmT, compT, x] at hy
  aesop))

namespace Model

variable {M : ExtendedPAlg.{u, v, w} Sig Index}

/-! ## Totality -/

lemma sc_dom {j k : Index} (h : j < k) {s : S} (a : M.1 (k, s)) :
    (M.1.op (.sc h s) (arg₁ a)).Dom := by
  have := holds M (.EA1_sc h s 0) (pts := ptsOf (k, s) 1) (fun _ => a) (by model_vars) (by simp)
  rwa [EEq.holds_defined_iff, scT, eval_app₁ _ (eval_ptsOf M _ 0 (by omega) rfl)] at this

lemma tg_dom {j k : Index} (h : j < k) {s : S} (a : M.1 (k, s)) :
    (M.1.op (.tg h s) (arg₁ a)).Dom := by
  have := holds M (.EA1_tg h s 0) (pts := ptsOf (k, s) 1) (fun _ => a) (by model_vars) (by simp)
  rwa [EEq.holds_defined_iff, tgT, eval_app₁ _ (eval_ptsOf M _ 0 (by omega) rfl)] at this

lemma idm_dom {j k : Index} (h : j < k) {s : S} (a : M.1 (j, s)) :
    (M.1.op (.idm h s) (arg₁ a)).Dom := by
  have := holds M (.EA1_idm h s 0) (pts := ptsOf (j, s) 1) (fun _ => a) (by model_vars) (by simp)
  rwa [EEq.holds_defined_iff, idmT, eval_app₁ _ (eval_ptsOf M _ 0 (by omega) rfl)] at this

lemma op_dom (k : Index) {ws : List S} {s : S} (σ : Sig ws s) (a : ∀ p, M.1 (k, ws.get p)) :
    (M.1.op (.op k σ) (liftFam k a)).Dom := by
  have := holds M (.EA0 k σ fun p => p.val) (pts := ptsFam k ws) a
    (by
      rintro y hy
      simp [QEEq.vars, EEq.vars, EEq.defined, vars_opT, x] at hy
      obtain ⟨p, rfl⟩ := hy
      exact ⟨p, rfl⟩)
    (by simp)
  rwa [EEq.holds_defined_iff, eval_opT k σ (eval_ptsFam M a)] at this

/-- (EA0) for any family of the arity of `σ_k`. -/
lemma op_dom' (k : Index) {ws : List S} {s : S} (σ : Sig ws s)
    (a : Arity M.1 (ws.map fun t => (k, t))) : (M.1.op (.op k σ) a).Dom := by
  rw [← liftFam_unlift k a]; exact op_dom k σ _

/-! ## The operations -/

variable (M) in
/-- The `(j,k)`-source of a model. -/
def sc {j k : Index} (h : j < k) {s : S} (a : M.1 (k, s)) : M.1 (j, s) :=
  (M.1.op (.sc h s) (arg₁ a)).get (sc_dom h a)

variable (M) in
/-- The `(j,k)`-target of a model. -/
def tg {j k : Index} (h : j < k) {s : S} (a : M.1 (k, s)) : M.1 (j, s) :=
  (M.1.op (.tg h s) (arg₁ a)).get (tg_dom h a)

variable (M) in
/-- The `(k,j)`-identity of a model. -/
def idm {j k : Index} (h : j < k) {s : S} (a : M.1 (j, s)) : M.1 (k, s) :=
  (M.1.op (.idm h s) (arg₁ a)).get (idm_dom h a)

variable (M) in
/-- The `j`-composition of `k`-cells of a model, a partial operation. -/
def pcomp {j k : Index} (h : j < k) {s : S} (a b : M.1 (k, s)) : Part (M.1 (k, s)) :=
  M.1.op (.comp h s) (arg₂ a b)

variable (M) in
/-- The copy `σ_k` of an operation symbol, on families of `k`-cells. -/
def op (k : Index) {ws : List S} {s : S} (σ : Sig ws s) (a : ∀ p, M.1 (k, ws.get p)) : M.1 (k, s) :=
  (M.1.op (.op k σ) (liftFam k a)).get (op_dom k σ a)

variable {val : ∀ t, EVar S Index t → Part (M.1 t)}

lemma eval_scT {j k : Index} {h : j < k} {s : S} {t : ETerm Sig Index (k, s)} {a : M.1 (k, s)}
    (ht : t.eval M.1 val = Part.some a) : (scT h t).eval M.1 val = Part.some (sc M h a) := by
  rw [scT, eval_app₁ _ ht]; exact (Part.some_get _).symm

lemma eval_tgT {j k : Index} {h : j < k} {s : S} {t : ETerm Sig Index (k, s)} {a : M.1 (k, s)}
    (ht : t.eval M.1 val = Part.some a) : (tgT h t).eval M.1 val = Part.some (tg M h a) := by
  rw [tgT, eval_app₁ _ ht]; exact (Part.some_get _).symm

lemma eval_idmT {j k : Index} {h : j < k} {s : S} {t : ETerm Sig Index (j, s)} {a : M.1 (j, s)}
    (ht : t.eval M.1 val = Part.some a) : (idmT h t).eval M.1 val = Part.some (idm M h a) := by
  rw [idmT, eval_app₁ _ ht]; exact (Part.some_get _).symm

lemma eval_compT {j k : Index} {h : j < k} {s : S} {t t' : ETerm Sig Index (k, s)}
    {a b : M.1 (k, s)} (ht : t.eval M.1 val = Part.some a) (ht' : t'.eval M.1 val = Part.some b) :
    (compT h t t').eval M.1 val = pcomp M h a b := by
  rw [compT, eval_app₂ _ ht ht', pcomp]

lemma eval_opT' (k : Index) {ws : List S} {s : S} (σ : Sig ws s)
    {ts : (p : Fin ws.length) → ETerm Sig Index (k, ws.get p)} {a : ∀ p, M.1 (k, ws.get p)}
    (h : ∀ p, (ts p).eval M.1 val = Part.some (a p)) :
    (opT k σ ts).eval M.1 val = Part.some (op M k σ a) := by
  rw [eval_opT k σ h]; exact (Part.some_get _).symm

lemma holds_mk'_of_eval {t : Index × S} {r r' : ETerm Sig Index t} {p p' : Part (M.1 t)}
    (hr : r.eval M.1 val = p) (hr' : r'.eval M.1 val = p') :
    (EEq.mk' r r').Holds M.1 val ↔ ∃ (h₁ : p.Dom) (h₂ : p'.Dom), p.get h₁ = p'.get h₂ := by
  subst hr hr'; rfl

end Model

set_option hygiene false in
/-- The value of the variable `x_i` under a valuation of `x_0, …, x_{m-1}`. -/
local macro "ev" i:num : term => `(Model.eval_ptsOf M _ $i (by omega) (by rfl))

set_option hygiene false in
/-- Read an equation off an axiom of the specification, for variables of one sort. -/
local macro "law" ax:term:max m:num vals:term:max l:term:max r:term:max prem:term:max :
    tactic =>
  `(tactic| (
    obtain ⟨_, _, e⟩ := (Model.holds_mk'_of_eval $l $r).mp
      (Model.holds M $ax (pts := Model.ptsOf _ $m) $vals (by model_vars) $prem)
    exact e))

/-- Premises stating that composites are defined, one term for each premise. -/
local syntax "prems" term,* : term

set_option hygiene false in
macro_rules
  | `(prems $h) => `(by
      intro e he
      obtain rfl := List.mem_singleton.mp he
      exact $h)
  | `(prems $h₁, $h₂) => `(by
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      exacts [$h₁, $h₂])
  | `(prems $h₁, $h₂, $h₃, $h₄) => `(by
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      exacts [$h₁, $h₂, $h₃, $h₄])

namespace Model

variable {M : ExtendedPAlg.{u, v, w} Sig Index}

/-! ## Composition -/

lemma holds_defined_of_dom {t : Index × S} {val : ∀ t, EVar S Index t → Part (M.1 t)}
    {r : ETerm Sig Index t} {p : Part (M.1 t)} (hr : r.eval M.1 val = p) (hp : p.Dom) :
    (EEq.defined r).Holds M.1 val := by
  rw [EEq.holds_defined_iff, hr]; exact hp

/-- (EA3): `x ∘^{(j,k)} y` is defined exactly when the `(j,k)`-source of `x` is the
`(j,k)`-target of `y`. -/
lemma pcomp_dom_iff {j k : Index} {h : j < k} {s : S} {a b : M.1 (k, s)} :
    (pcomp M h a b).Dom ↔ sc M h a = tg M h b := by
  constructor
  · intro hd
    have := holds M (.EA3_dom h s 0 1) (pts := ptsOf (k, s) 2) ![a, b] (by model_vars)
      (prems holds_defined_of_dom (eval_compT (ev 0) (ev 1)) hd)
    rwa [EEq.holds_mk'_iff (eval_scT (ev 0)) (eval_tgT (ev 1))] at this
  · intro hab
    have := holds M (.EA3_def h s 0 1) (pts := ptsOf (k, s) 2) ![a, b] (by model_vars)
      (prems (EEq.holds_mk'_iff (eval_scT (ev 0)) (eval_tgT (ev 1))).mpr hab)
    rwa [EEq.holds_defined_iff, eval_compT (ev 0) (ev 1)] at this

variable (M) in
/-- The `j`-composite of two `k`-cells whose `(j,k)`-source and target agree. -/
def comp {j k : Index} (h : j < k) {s : S} (a b : M.1 (k, s)) (hab : sc M h a = tg M h b) :
    M.1 (k, s) :=
  (pcomp M h a b).get (pcomp_dom_iff.mpr hab)

lemma pcomp_eq {j k : Index} {h : j < k} {s : S} {a b : M.1 (k, s)} (hab : sc M h a = tg M h b) :
    pcomp M h a b = Part.some (comp M h a b hab) :=
  (Part.some_get _).symm

lemma comp_congr {j k : Index} {h : j < k} {s : S} {a a' b b' : M.1 (k, s)}
    (ha : a = a') (hb : b = b') (hab : sc M h a = tg M h b) (hab' : sc M h a' = tg M h b') :
    comp M h a b hab = comp M h a' b' hab' := by
  subst ha hb; rfl

variable {val : ∀ t, EVar S Index t → Part (M.1 t)}

lemma eval_compT_some {j k : Index} {h : j < k} {s : S} {t t' : ETerm Sig Index (k, s)}
    {a b : M.1 (k, s)} (ht : t.eval M.1 val = Part.some a) (ht' : t'.eval M.1 val = Part.some b)
    (hab : sc M h a = tg M h b) : (compT h t t').eval M.1 val = Part.some (comp M h a b hab) := by
  rw [eval_compT ht ht']; exact pcomp_eq hab

lemma holds_defined_compT {j k : Index} {h : j < k} {s : S} {t t' : ETerm Sig Index (k, s)}
    {a b : M.1 (k, s)} (ht : t.eval M.1 val = Part.some a) (ht' : t'.eval M.1 val = Part.some b)
    (hab : sc M h a = tg M h b) : (EEq.defined (compT h t t')).Holds M.1 val :=
  holds_defined_of_dom (eval_compT_some ht ht' hab) trivial

/-! ## The laws (EA^{j,k}) -/

section Laws

variable {j k : Index} {h : j < k} {s : S}

lemma sc_idm (u : M.1 (j, s)) : sc M h (idm M h u) = u := by
  law (.EA2_sc h s 0) 1 ![u] (eval_scT (eval_idmT (ev 0))) (ev 0) (by simp)

lemma tg_idm (u : M.1 (j, s)) : tg M h (idm M h u) = u := by
  law (.EA2_tg h s 0) 1 ![u] (eval_tgT (eval_idmT (ev 0))) (ev 0) (by simp)

lemma sc_comp {a b : M.1 (k, s)} (hab : sc M h a = tg M h b) :
    sc M h (comp M h a b hab) = sc M h b := by
  law (.EA4_sc h s 0 1) 2 ![a, b] (eval_scT (eval_compT_some (ev 0) (ev 1) hab)) (eval_scT (ev 1))
    (prems holds_defined_compT (ev 0) (ev 1) hab)

lemma tg_comp {a b : M.1 (k, s)} (hab : sc M h a = tg M h b) :
    tg M h (comp M h a b hab) = tg M h a := by
  law (.EA4_tg h s 0 1) 2 ![a, b] (eval_tgT (eval_compT_some (ev 0) (ev 1) hab)) (eval_tgT (ev 0))
    (prems holds_defined_compT (ev 0) (ev 1) hab)

lemma comp_idm_sc (a : M.1 (k, s)) :
    comp M h a (idm M h (sc M h a)) (tg_idm _).symm = a := by
  law (.EA5_sc h s 0) 1 ![a] (eval_compT_some (ev 0) (eval_idmT (eval_scT (ev 0))) (tg_idm _).symm)
    (ev 0) (by simp)

lemma idm_tg_comp (a : M.1 (k, s)) :
    comp M h (idm M h (tg M h a)) a (sc_idm _) = a := by
  law (.EA5_tg h s 0) 1 ![a] (eval_compT_some (eval_idmT (eval_tgT (ev 0))) (ev 0) (sc_idm _))
    (ev 0) (by simp)

lemma comp_assoc {a b c : M.1 (k, s)} (hab : sc M h a = tg M h b) (hbc : sc M h b = tg M h c) :
    comp M h (comp M h a b hab) c ((sc_comp hab).trans hbc) =
      comp M h a (comp M h b c hbc) (hab.trans (tg_comp hbc).symm) := by
  law (.EA6 h s 0 1 2) 3 ![a, b, c]
    (eval_compT_some (eval_compT_some (ev 0) (ev 1) hab) (ev 2) ((sc_comp hab).trans hbc))
    (eval_compT_some (ev 0) (eval_compT_some (ev 1) (ev 2) hbc) (hab.trans (tg_comp hbc).symm))
    (prems holds_defined_compT (ev 0) (ev 1) hab, holds_defined_compT (ev 1) (ev 2) hbc)

end Laws

/-! ## The laws (EA^{h,j,k}) -/

section Laws'

variable {a b c : Index} {h₁ : a < b} {h₂ : b < c} {s : S}

lemma sc_sc (x : M.1 (c, s)) : sc M h₁ (sc M h₂ x) = sc M (h₁.trans h₂) x := by
  law (.EA1'_sc_sc h₁ h₂ s 0) 1 ![x] (eval_scT (eval_scT (ev 0))) (eval_scT (ev 0)) (by simp)

lemma tg_tg (x : M.1 (c, s)) : tg M h₁ (tg M h₂ x) = tg M (h₁.trans h₂) x := by
  law (.EA1'_tg_tg h₁ h₂ s 0) 1 ![x] (eval_tgT (eval_tgT (ev 0))) (eval_tgT (ev 0)) (by simp)

lemma sc_tg (x : M.1 (c, s)) : sc M h₁ (tg M h₂ x) = sc M (h₁.trans h₂) x := by
  law (.EA1'_sc_tg h₁ h₂ s 0) 1 ![x] (eval_scT (eval_tgT (ev 0))) (eval_scT (ev 0)) (by simp)

lemma tg_sc (x : M.1 (c, s)) : tg M h₁ (sc M h₂ x) = tg M (h₁.trans h₂) x := by
  law (.EA1'_tg_sc h₁ h₂ s 0) 1 ![x] (eval_tgT (eval_scT (ev 0))) (eval_tgT (ev 0)) (by simp)

lemma idm_idm (u : M.1 (a, s)) : idm M h₂ (idm M h₁ u) = idm M (h₁.trans h₂) u := by
  law (.EA2' h₁ h₂ s 0) 1 ![u] (eval_idmT (eval_idmT (ev 0))) (eval_idmT (ev 0)) (by simp)

lemma sc_comp' {x y : M.1 (c, s)} (hxy : sc M (h₁.trans h₂) x = tg M (h₁.trans h₂) y) :
    sc M h₂ (comp M (h₁.trans h₂) x y hxy) =
      comp M h₁ (sc M h₂ x) (sc M h₂ y) (by rw [sc_sc (h₁ := h₁) (h₂ := h₂), tg_sc (h₁ := h₁) (h₂ := h₂)]; exact hxy) := by
  law (.EA3'_sc h₁ h₂ s 0 1) 2 ![x, y] (eval_scT (eval_compT_some (ev 0) (ev 1) hxy))
    (eval_compT_some (eval_scT (ev 0)) (eval_scT (ev 1)) (by rw [sc_sc (h₁ := h₁) (h₂ := h₂), tg_sc (h₁ := h₁) (h₂ := h₂)]; exact hxy))
    (prems holds_defined_compT (ev 0) (ev 1) hxy)

lemma tg_comp' {x y : M.1 (c, s)} (hxy : sc M (h₁.trans h₂) x = tg M (h₁.trans h₂) y) :
    tg M h₂ (comp M (h₁.trans h₂) x y hxy) =
      comp M h₁ (tg M h₂ x) (tg M h₂ y) (by rw [sc_tg (h₁ := h₁) (h₂ := h₂), tg_tg (h₁ := h₁) (h₂ := h₂)]; exact hxy) := by
  law (.EA3'_tg h₁ h₂ s 0 1) 2 ![x, y] (eval_tgT (eval_compT_some (ev 0) (ev 1) hxy))
    (eval_compT_some (eval_tgT (ev 0)) (eval_tgT (ev 1)) (by rw [sc_tg (h₁ := h₁) (h₂ := h₂), tg_tg (h₁ := h₁) (h₂ := h₂)]; exact hxy))
    (prems holds_defined_compT (ev 0) (ev 1) hxy)

/-- The `(a,c)`-source of a `b`-composite of `c`-cells. -/
lemma sc_comp_low {x y : M.1 (c, s)} (hxy : sc M h₂ x = tg M h₂ y) :
    sc M (h₁.trans h₂) (comp M h₂ x y hxy) = sc M (h₁.trans h₂) y := by
  rw [← sc_sc (h₁ := h₁) (h₂ := h₂), sc_comp, sc_sc]

lemma tg_comp_low {x y : M.1 (c, s)} (hxy : sc M h₂ x = tg M h₂ y) :
    tg M (h₁.trans h₂) (comp M h₂ x y hxy) = tg M (h₁.trans h₂) x := by
  rw [← tg_tg (h₁ := h₁) (h₂ := h₂), tg_comp, tg_tg]

/-- The `(a,c)`-sources of two `b`-composable `c`-cells agree. -/
lemma sc_eq_sc_of_comp {x y : M.1 (c, s)} (hxy : sc M h₂ x = tg M h₂ y) :
    sc M (h₁.trans h₂) x = sc M (h₁.trans h₂) y := by
  rw [← sc_sc (h₁ := h₁) (h₂ := h₂), hxy, sc_tg]

lemma tg_eq_tg_of_comp {x y : M.1 (c, s)} (hxy : sc M h₂ x = tg M h₂ y) :
    tg M (h₁.trans h₂) x = tg M (h₁.trans h₂) y := by
  rw [← tg_sc (h₁ := h₁) (h₂ := h₂), hxy, tg_tg]

lemma interchange {x y z t : M.1 (c, s)} (hxy : sc M h₂ x = tg M h₂ y)
    (hzt : sc M h₂ z = tg M h₂ t) (hxz : sc M (h₁.trans h₂) x = tg M (h₁.trans h₂) z)
    (hyt : sc M (h₁.trans h₂) y = tg M (h₁.trans h₂) t) :
    comp M (h₁.trans h₂) (comp M h₂ x y hxy) (comp M h₂ z t hzt)
        (by rw [sc_comp_low (h₁ := h₁), tg_comp_low (h₁ := h₁), ← sc_eq_sc_of_comp (h₁ := h₁) hxy]; exact hxz) =
      comp M h₂ (comp M (h₁.trans h₂) x z hxz) (comp M (h₁.trans h₂) y t hyt)
        (by rw [sc_comp' (h₁ := h₁) (h₂ := h₂), tg_comp' (h₁ := h₁) (h₂ := h₂)]; exact comp_congr hxy hzt _ _) := by
  law (.EA4' h₁ h₂ s 0 1 2 3) 4 ![x, y, z, t]
    (eval_compT_some (eval_compT_some (ev 0) (ev 1) hxy) (eval_compT_some (ev 2) (ev 3) hzt)
      (by rw [sc_comp_low (h₁ := h₁), tg_comp_low (h₁ := h₁), ← sc_eq_sc_of_comp (h₁ := h₁) hxy]; exact hxz))
    (eval_compT_some (eval_compT_some (ev 0) (ev 2) hxz) (eval_compT_some (ev 1) (ev 3) hyt)
      (by rw [sc_comp' (h₁ := h₁) (h₂ := h₂), tg_comp' (h₁ := h₁) (h₂ := h₂)]; exact comp_congr hxy hzt _ _))
    (prems holds_defined_compT (ev 0) (ev 1) hxy, holds_defined_compT (ev 2) (ev 3) hzt,
      holds_defined_compT (ev 0) (ev 2) hxz, holds_defined_compT (ev 1) (ev 3) hyt)

lemma sc_idm_low (u : M.1 (b, s)) : sc M (h₁.trans h₂) (idm M h₂ u) = sc M h₁ u := by
  rw [← sc_sc (h₁ := h₁) (h₂ := h₂), sc_idm]

lemma tg_idm_low (u : M.1 (b, s)) : tg M (h₁.trans h₂) (idm M h₂ u) = tg M h₁ u := by
  rw [← tg_tg (h₁ := h₁) (h₂ := h₂), tg_idm]

lemma idm_comp {u v : M.1 (b, s)} (huv : sc M h₁ u = tg M h₁ v) :
    idm M h₂ (comp M h₁ u v huv) =
      comp M (h₁.trans h₂) (idm M h₂ u) (idm M h₂ v) (by rw [sc_idm_low (h₁ := h₁) (h₂ := h₂), tg_idm_low (h₁ := h₁) (h₂ := h₂)]; exact huv) := by
  law (.EA5' h₁ h₂ s 0 1) 2 ![u, v] (eval_idmT (eval_compT_some (ev 0) (ev 1) huv))
    (eval_compT_some (eval_idmT (ev 0)) (eval_idmT (ev 1)) (by rw [sc_idm_low (h₁ := h₁) (h₂ := h₂), tg_idm_low (h₁ := h₁) (h₂ := h₂)]; exact huv))
    (prems holds_defined_compT (ev 0) (ev 1) huv)

end Laws'

/-! ## The laws of the copies of the operation symbols -/

/-- The variables of an axiom with variables `x_p` of sort `(k, s_p)`. -/
local macro "fam_vars" : tactic => `(tactic| (
  rintro y hy
  simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, vars_opT, scT, tgT, idmT, compT, x] at hy
  obtain ⟨p, hp⟩ := hy
  exact ⟨p, hp.symm⟩))

section Ops

variable {j k : Index} (h : j < k) {ws : List S} {s : S} (σ : Sig ws s)

lemma sc_op (a : ∀ p, M.1 (k, ws.get p)) :
    sc M h (op M k σ a) = op M j σ (fun p => sc M h (a p)) := by
  obtain ⟨_, _, e⟩ := (holds_mk'_of_eval (eval_scT (eval_opT' k σ (eval_ptsFam M a)))
    (eval_opT' j σ fun p => eval_scT (eval_ptsFam M a p))).mp
    (holds M (.EA7_sc h σ fun p => p.val) (pts := ptsFam k ws) a (by fam_vars) (by simp))
  exact e

lemma tg_op (a : ∀ p, M.1 (k, ws.get p)) :
    tg M h (op M k σ a) = op M j σ (fun p => tg M h (a p)) := by
  obtain ⟨_, _, e⟩ := (holds_mk'_of_eval (eval_tgT (eval_opT' k σ (eval_ptsFam M a)))
    (eval_opT' j σ fun p => eval_tgT (eval_ptsFam M a p))).mp
    (holds M (.EA7_tg h σ fun p => p.val) (pts := ptsFam k ws) a (by fam_vars) (by simp))
  exact e

lemma idm_op (u : ∀ p, M.1 (j, ws.get p)) :
    idm M h (op M j σ u) = op M k σ (fun p => idm M h (u p)) := by
  obtain ⟨_, _, e⟩ := (holds_mk'_of_eval (eval_idmT (eval_opT' j σ (eval_ptsFam M u)))
    (eval_opT' k σ fun p => eval_idmT (eval_ptsFam M u p))).mp
    (holds M (.EA7_idm h σ fun p => p.val) (pts := ptsFam j ws) u (by fam_vars) (by simp))
  exact e

lemma op_comp (a b : ∀ p, M.1 (k, ws.get p)) (hab : ∀ p, sc M h (a p) = tg M h (b p)) :
    op M k σ (fun p => comp M h (a p) (b p) (hab p)) =
      comp M h (op M k σ a) (op M k σ b)
        (by rw [sc_op, tg_op]; exact congrArg (op M j σ) (funext hab)) := by
  obtain ⟨_, _, e⟩ := (holds_mk'_of_eval
    (eval_opT' k σ fun p =>
      eval_compT_some (eval_ptsFam₂_inl M a b p) (eval_ptsFam₂_inr M a b p) (hab p))
    (eval_compT_some (eval_opT' k σ (eval_ptsFam₂_inl M a b))
      (eval_opT' k σ (eval_ptsFam₂_inr M a b))
      (by rw [sc_op, tg_op]; exact congrArg (op M j σ) (funext hab)))).mp
    (holds M (.EA8 h σ (fun p => 2 * p.val) (fun p => 2 * p.val + 1)) (pts := ptsFam₂ k ws)
      (vals₂ M a b)
      (by
        rintro y hy
        simp [QEEq.vars, EEq.vars, EEq.mk', EEq.defined, vars_opT, compT, x] at hy
        rcases hy with ((⟨p, hp | hp⟩ | ⟨p, hp⟩ | ⟨p, hp⟩) | ⟨p, hp | hp⟩) <;>
          first | exact ⟨.inl p, hp.symm⟩ | exact ⟨.inr p, hp.symm⟩)
      (by
        intro e he
        obtain ⟨p, rfl⟩ := List.mem_ofFn.mp he
        exact holds_defined_compT (eval_ptsFam₂_inl M a b p) (eval_ptsFam₂_inr M a b p) (hab p)))
  exact e

end Ops

end Model

end CategorialAlgebras.Extended
