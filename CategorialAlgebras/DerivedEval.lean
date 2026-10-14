import CategorialAlgebras.GenEpDerivor
import CategorialAlgebras.Compact.Identification

/-!
# Values in derived algebras and in compact models

The value of an operation of the algebra derived along a generalized ep-derivor, from the value of
its term, and the values of terms built with the operations of a model of the compact
specification, for any set of variables. They are used to compute the functors of graduation and
unification.
-/

universe u v w

namespace CategorialAlgebras

open Signature Term

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
