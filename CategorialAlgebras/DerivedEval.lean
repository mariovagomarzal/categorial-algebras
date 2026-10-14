import CategorialAlgebras.GenEpDerivor
import CategorialAlgebras.Compact.Identification
import CategorialAlgebras.EpSignature

/-!
# Values in derived algebras and in compact models

The value of an operation of the algebra derived along a generalized ep-derivor, from the value of
its term, and the values of terms built with the operations of a model of the compact
specification, for any set of variables. They are used to compute the functors of graduation and
unification.
-/

universe u v w

namespace CategorialAlgebras

open Signature Term CategoryTheory

/-- The argument of a unary operation symbol. -/
def arityOne {S : Type u} {A : S → Type w} {t : S} (a : A t) : Arity A [t] := fun | ⟨0, _⟩ => a

/-- The arguments of a binary operation symbol. -/
def arityTwo {S : Type u} {A : S → Type w} {t t' : S} (a : A t) (b : A t') : Arity A [t, t'] :=
  fun | ⟨0, _⟩ => a | ⟨1, _⟩ => b

section
variable {S : Type u} {Sig : Signature.{u, v} S} {A : PartialAlgebra.{u, v, w} Sig} {V : S → Type}
  {val : ∀ s, V s → Part (A s)}

lemma eval_app₁_arity {t t' : S} (σ : Sig [t] t') {r : Term Sig V t} {a : A t}
    (h : r.eval A val = Part.some a) : (app₁ σ r).eval A val = A.op σ (arityOne a) := by
  rw [eval_app₁_of_eq_some _ _ _ h]; rfl

lemma eval_app₂_arity {t₀ t₁ t' : S} (σ : Sig [t₀, t₁] t') {r : Term Sig V t₀} {r' : Term Sig V t₁}
    {a : A t₀} {b : A t₁} (h : r.eval A val = Part.some a) (h' : r'.eval A val = Part.some b) :
    (app₂ σ r r').eval A val = A.op σ (arityTwo a b) := by
  rw [eval_app₂_of_eq_some _ _ _ h h']; rfl
end

namespace PartialAlgebra

variable {S : Type u} {Sig : Signature.{u, v} S} {A B : PartialAlgebra.{u, v, w} Sig}
  (e : ∀ s, A s ≃ B s)
  (he : ∀ {ws : List S} {s : S} (σ : Sig ws s) (a : Arity A ws),
    B.op σ (fun j => e _ (a j)) = (A.op σ a).map (e s))

include he in
lemma op_symm {ws : List S} {s : S} (σ : Sig ws s) (b : Arity B ws) :
    B.op σ b = (A.op σ fun j => (e _).symm (b j)).map (e s) := by
  have := he σ fun j => (e _).symm (b j)
  simp only [Equiv.apply_symm_apply] at this
  exact this

include e he in
/-- A family of bijections that commutes with the operations is a homomorphism. -/
def homOfEquiv : Hom A B where
  map s := e s
  map_dom σ a ha := by rw [he]; exact ha
  map_op σ a ha := (Part.get_eq_of_mem (show e _ ((A.op σ a).get ha) ∈ B.op σ (fun j => e _ (a j))
    by rw [he]; exact Part.mem_map _ (Part.get_mem ha)) _).symm

include e he in
/-- The inverse of a family of bijections that commutes with the operations is a homomorphism. -/
def homOfEquivSymm : Hom B A where
  map s := (e s).symm
  map_dom σ b hb := by rw [op_symm e he σ b] at hb; exact hb
  map_op σ b hb := by
    have hm : (A.op σ fun j => (e _).symm (b j)).Dom := by
      have := hb; rw [op_symm e he σ b] at this; exact this
    have : (B.op σ b).get hb = e _ ((A.op σ fun j => (e _).symm (b j)).get hm) :=
      Part.get_eq_of_mem (show e _ ((A.op σ fun j => (e _).symm (b j)).get hm) ∈ B.op σ b
        by rw [op_symm e he σ b]; exact Part.mem_map _ (Part.get_mem hm)) _
    rw [this, Equiv.symm_apply_apply]

end PartialAlgebra

/-- A family of bijections that commutes with the operations is an isomorphism of models. -/
def EpSpec.isoOfEquiv {S : Type u} {V : S → Type} {Sp : EpSpec.{u, v} S V}
    {A B : EpSpec.EpAlg.{u, v, w} Sp} (e : ∀ s, A.1 s ≃ B.1 s)
    (he : ∀ {ws : List S} {s : S} (σ : Sp.sg.sig ws s) (a : Arity A.1 ws),
      B.1.op σ (fun j => e _ (a j)) = (A.1.op σ a).map (e s)) : A ≅ B where
  hom := PartialAlgebra.homOfEquiv e he
  inv := PartialAlgebra.homOfEquivSymm e he
  hom_inv_id := PartialAlgebra.Hom.ext fun s x => (e s).symm_apply_apply x
  inv_hom_id := PartialAlgebra.Hom.ext fun s x => (e s).apply_symm_apply x

namespace GenEpDerivor

variable {S T : Type u} {Sg : EpSignature.{u, v} S} {Lg : EpSignature.{u, v} T}
  (δ : GenEpDerivor Sg Lg) {B : PartialAlgebra.{u, v, w} Lg.sig}

/-- The value of an operation of the derived algebra, from the value of its term. -/
lemma derived_op_eq_some {ws : List S} {s : S} {σ : Sg.sig ws s} {a : Arity (δ.derived B) ws}
    {c : B (δ.sortMap s)} (hdef : EEq.HoldsAll (δ.derived B) (famVal a) (Sg.defn σ))
    (hc : (δ.op σ).eval B (famVal fun j => (a j).1) = Part.some c)
    (hcD : EEq.HoldsAll B (val₁ c) (δ.sortDom s)) :
    (δ.derived B).op σ a = Part.some ⟨c, hcD⟩ := by
  have hD : ((δ.op σ).eval B (famVal fun j => (a j).1)).Dom := by rw [hc]; trivial
  have hg : ((δ.op σ).eval B (famVal fun j => (a j).1)).get hD = c :=
    Part.get_eq_of_mem (by rw [hc]; exact Part.mem_some c) hD
  exact Part.eq_some_iff.mpr ⟨(δ.op_derived_dom_iff σ a).mpr ⟨hdef, hD, hg ▸ hcD⟩, Subtype.ext hg⟩

end GenEpDerivor

namespace Compact

variable {S : Type u} {Sig : Signature.{u, v} S} {Index : Type} [Preorder Index]
  {M : CompactPAlg.{u, v, w} Sig Index} {V : S → Type} {val : ∀ s, V s → Part (M.1 s)}

lemma op_get_eq {ws : List S} {s : S} {σ : CompactSignature Sig Index ws s} {a b : Arity M.1 ws}
    (e : a = b) (h : (M.1.op σ b).Dom) : M.1.op σ a = Part.some ((M.1.op σ b).get h) := by
  subst e; exact (Part.some_get h).symm

lemma eval_sc {k : Index} {s : S} {r : Term (CompactSignature Sig Index) V s} {a : M.1 s}
    (h : r.eval M.1 val = Part.some a) :
    (app₁ (.sc k s) r).eval M.1 val = Part.some (msc M k a) := by
  rw [eval_app₁_of_eq_some _ _ _ h]
  exact op_get_eq (by funext i; match i with | ⟨0, _⟩ => rfl) _

lemma eval_tg {k : Index} {s : S} {r : Term (CompactSignature Sig Index) V s} {a : M.1 s}
    (h : r.eval M.1 val = Part.some a) :
    (app₁ (.tg k s) r).eval M.1 val = Part.some (mtg M k a) := by
  rw [eval_app₁_of_eq_some _ _ _ h]
  exact op_get_eq (by funext i; match i with | ⟨0, _⟩ => rfl) _

lemma eval_comp {k : Index} {s : S} {r r' : Term (CompactSignature Sig Index) V s} {a b : M.1 s}
    (h : r.eval M.1 val = Part.some a) (h' : r'.eval M.1 val = Part.some b)
    (hab : CategoryStruct.sc_is_tg k a b) :
    (app₂ (.comp k s) r r').eval M.1 val = Part.some (CategoryStruct.comp k a b hab) := by
  rw [eval_app₂_of_eq_some _ _ _ h h']
  exact op_get_eq (by funext i; match i with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl) _

lemma eval_op {ws : List S} {s : S} (σ : Sig ws s)
    {ts : (j : Fin ws.length) → Term (CompactSignature Sig Index) V (ws.get j)} {a : Arity M.1 ws}
    (h : ∀ j, (ts j).eval M.1 val = Part.some (a j)) :
    (Term.app (.op σ) ts).eval M.1 val = Part.some (mop M σ a) := by
  rw [eval_app_of_eq_some _ _ _ h]; exact (Part.some_get _).symm

end Compact

end CategorialAlgebras
