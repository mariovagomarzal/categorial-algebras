import CategorialAlgebras.Preliminaries.Substitution

/-!
# Derivors

A derivor changes sorts and interprets each operation as a term in the translated positions
of its input word. It transforms free algebras, translates terms, and commutes with
substitution. Many-sorted signatures of fixed sort and symbol universes form a category.
-/

universe u u' u'' u''' v v' v'' v''' w x y

namespace CategorialAlgebras

open CategoryTheory

/-- A derivor sends sorts to sorts and symbols to terms in the corresponding positions. -/
structure Derivor {S : Type u} {T : Type u'} (sig : Signature.{u, v} S)
    (tau : Signature.{u', v'} T) where
  /-- The map of sorts. -/
  sortMap : S → T
  /-- The term interpreting each symbol, with one variable for each input position. -/
  image : ∀ {a s}, sig a s → Term tau (Word.MappedVariables sortMap a) (sortMap s)

namespace Derivor

variable {S : Type u} {T : Type u'} {U : Type u''} {V : Type u'''}
variable {sig : Signature.{u, v} S} {tau : Signature.{u', v'} T}
variable {ups : Signature.{u'', v''} U} {xi : Signature.{u''', v'''} V}

/-! ## Transformed algebras and translation -/

/-- Equality of derivors is equality of the sort maps and of their dependent symbol images. -/
theorem ext {c d : Derivor sig tau} (h : c.sortMap = d.sortMap)
    (hi : HEq @c.image @d.image) : c = d := by
  cases c
  cases d
  cases h
  cases hi
  rfl

/-- The transformed free algebra interprets symbols by substituting into their images. -/
def transformed (c : Derivor sig tau) (X : T → Type w) : Algebra sig where
  carrier s := Term tau X (c.sortMap s)
  op σ q := Term.substFamily q (c.image σ)

/-- Substitution is a homomorphism between the transformed free algebras.

**Formally stronger** than the informal statement. Informally, it is stated for the substitution of
a family of terms for the positional variables of a word; here it holds for every substitution
between sorted sets of variables. -/
def substHom (c : Derivor sig tau) {X : T → Type w} {Y : T → Type x}
    (f : SortedSet.Map X (Term tau Y)) :
    Algebra.Hom (c.transformed X) (c.transformed Y) where
  toMap _ := Term.subst f
  map_op σ q := Term.subst_subst_family q f (c.image σ)

/-- Algebraic extension of an assignment of translated terms to the source variables. -/
def translateHom (c : Derivor sig tau) {X : S → Type w} {Y : T → Type x}
    (f : ∀ s, X s → Term tau Y (c.sortMap s)) :
    Algebra.Hom (Term.algebra sig X) (c.transformed Y) := Term.lift f

/-- Translation of a term with an arbitrary assignment for its variables. -/
def translate (c : Derivor sig tau) {X : S → Type w} {Y : T → Type x}
    (f : ∀ s, X s → Term tau Y (c.sortMap s)) {s} (t : Term sig X s) :
    Term tau Y (c.sortMap s) := (c.translateHom f).toMap s t

/-- Translation sends a variable to its assigned translated term. -/
@[simp] theorem translate_var (c : Derivor sig tau) {X : S → Type w} {Y : T → Type x}
    (f : ∀ s, X s → Term tau Y (c.sortMap s)) {s} (a : X s) :
    c.translate f (Term.var a) = f s a := rfl

/-- Translation substitutes the translated arguments in the image of an operation. -/
@[simp] theorem translate_app (c : Derivor sig tau) {X : S → Type w} {Y : T → Type x}
    (f : ∀ s, X s → Term tau Y (c.sortMap s)) {a s} (σ : sig a s)
    (t : Word.Family (Term sig X) a) :
    c.translate f (Term.app σ t) =
      Term.substFamily (fun j => c.translate f (t j)) (c.image σ) := rfl

/-- Target substitutions commute with translation by substituting in its variable assignment. -/
theorem subst_translate (c : Derivor sig tau) {X : S → Type w}
    {Y : T → Type x} {Z : T → Type y}
    (f : ∀ s, X s → Term tau Y (c.sortMap s)) (g : SortedSet.Map Y (Term tau Z))
    {s} (t : Term sig X s) :
    Term.subst g (c.translate f t) = c.translate (fun s x => Term.subst g (f s x)) t := by
  induction t with
  | var x => rfl
  | app σ t ih =>
    simp only [translate_app, Term.subst_subst_family]
    exact congrArg (fun q => Term.substFamily q (c.image σ)) (funext ih)

/-- Translating a source substitution translates all the terms assigned to variables. -/
theorem translate_subst (c : Derivor sig tau) {X : S → Type w}
    {Y : S → Type x} {Z : T → Type y}
    (f : SortedSet.Map X (Term sig Y)) (g : ∀ s, Y s → Term tau Z (c.sortMap s))
    {s} (t : Term sig X s) :
    c.translate g (Term.subst f t) = c.translate (fun s x => c.translate g (f s x)) t := by
  induction t with
  | var x => rfl
  | app σ t ih =>
    simp only [Term.subst_app, translate_app]
    exact congrArg (fun q => Term.substFamily q (c.image σ)) (funext ih)

/-- Translate a context of positions along the sort map, preserving each position. -/
def positionMap (c : Derivor sig tau) {R : Type y} (φ : R → S) (a : List R) :
    ∀ s, Word.MappedVariables φ a s →
      Term tau (Word.MappedVariables (c.sortMap ∘ φ) a) (c.sortMap s) :=
  fun _ ⟨j, h⟩ => Term.var ⟨j, congrArg c.sortMap h⟩

/-- Translation $c^\sharp$ on the positional variables of a word. -/
def translateWord (c : Derivor sig tau) (a : List S) {s}
    (t : Term sig (Word.Variables a) s) :
    Term tau (Word.MappedVariables c.sortMap a) (c.sortMap s) :=
  c.translate (c.positionMap id a) t

/-- Word translation preserves the variable at each position. -/
@[simp] theorem translate_word_var (c : Derivor sig tau) (a : List S) (j : Fin a.length) :
    c.translateWord a (Term.var (Word.position a j)) =
      Term.var (Word.mappedVariable c.sortMap a j) := rfl

/-- Word translation has the operation equation specified by substitution in symbol images. -/
theorem translate_word_app (c : Derivor sig tau) (a : List S) {b s} (σ : sig b s)
    (t : Word.Family (Term sig (Word.Variables a)) b) :
    c.translateWord a (Term.app σ t) =
      Term.substFamily (fun j => c.translateWord a (t j)) (c.image σ) := rfl

/-- The identity derivor interprets a symbol by applying it to its positional variables. -/
abbrev identity (sig : Signature.{u, v} S) : Derivor sig sig where
  sortMap := id
  image {a} {_} σ := Term.app σ (fun j => Term.var (Word.position a j))

/-- The composite interprets each source symbol by translating its first image. -/
abbrev comp (c : Derivor sig tau) (d : Derivor tau ups) : Derivor sig ups where
  sortMap := d.sortMap ∘ c.sortMap
  image {a} {_} σ := d.translate (d.positionMap c.sortMap a) (c.image σ)

/-! ## Substitution and composition laws -/

/-- Translation commutes with a substitution specified by a family of terms. -/
theorem translate_subst_family (c : Derivor sig tau) {R : Type y} {φ : R → S}
    {a : List R} {X : S → Type w} {Y : T → Type x}
    (q : Word.Family (fun r => Term sig X (φ r)) a)
    (f : ∀ s, X s → Term tau Y (c.sortMap s)) {s}
    (t : Term sig (Word.MappedVariables φ a) s) :
    c.translate f (Term.substFamily (φ := φ) q t) =
      Term.substFamily (φ := c.sortMap ∘ φ) (fun j => c.translate f (q j))
        (c.translate (c.positionMap φ a) t) := by
  unfold Term.substFamily
  rw [translate_subst, subst_translate]
  apply congrArg (fun f => c.translate f t)
  funext s ⟨j, h⟩
  cases h
  rfl

/-- Translation on word variables commutes with substitutions specified by families. -/
theorem translate_word_subst_family (c : Derivor sig tau) {a b : List S}
    (q : Word.Family (Term sig (Word.Variables b)) a) {s}
    (t : Term sig (Word.Variables a) s) :
    c.translateWord b (Term.substFamily (φ := id) q t) =
      Term.substFamily (φ := c.sortMap) (fun j => c.translateWord b (q j))
        (c.translateWord a t) :=
  c.translate_subst_family q (c.positionMap id b) t

/-- Translation by a composite is successive translation by its two derivors. -/
theorem translate_comp (c : Derivor sig tau) (d : Derivor tau ups)
    {X : S → Type w} {Y : T → Type x} {Z : U → Type y}
    (f : ∀ s, X s → Term tau Y (c.sortMap s))
    (g : ∀ t, Y t → Term ups Z (d.sortMap t)) {s} (t : Term sig X s) :
    (c.comp d).translate (fun s x => d.translate g (f s x)) t =
      d.translate g (c.translate f t) := by
  induction t with
  | var x => rfl
  | app σ t ih =>
    simp only [translate_app, translate_subst_family]
    exact congrArg (fun q => Term.substFamily q ((c.comp d).image σ)) (funext ih)

/-- Translation by the identity derivor is ordinary substitution of its variable assignment. -/
theorem translate_identity {X : S → Type w} {Y : S → Type x}
    (f : SortedSet.Map X (Term sig Y)) {s} (t : Term sig X s) :
    (identity sig).translate f t = Term.subst f t := by
  induction t with
  | var x => rfl
  | app σ t ih =>
    change Term.app σ (fun j => (identity sig).translate f (t j)) =
      Term.app σ (fun j => Term.subst f (t j))
    exact congrArg (Term.app σ) (funext ih)

/-- The identity derivor fixes all terms in positional variables. -/
@[simp] theorem translate_word_identity (a : List S) {s}
    (t : Term sig (Word.Variables a) s) : (identity sig).translateWord a t = t := by
  unfold translateWord
  rw [translate_identity]
  exact Term.subst_id t

/-- Translating the generic application of a symbol gives its image under the derivor. -/
theorem translate_symbol (c : Derivor sig tau) {a s} (σ : sig a s) :
    c.translateWord a (Term.app σ (fun j => Term.var (Word.position a j))) = c.image σ := by
  change Term.substFamily (φ := c.sortMap)
    (fun j => Term.var (Word.mappedVariable c.sortMap a j)) (c.image σ) = _
  exact Term.subst_family_positions _

/-- The identity derivor is a left identity for composition. -/
@[simp] theorem identity_comp (c : Derivor sig tau) : (identity sig).comp c = c := by
  apply ext (c := (identity sig).comp c) (d := c) rfl
  apply heq_of_eq
  funext a s σ
  exact translate_symbol c σ

/-- The identity derivor is a right identity for composition. -/
@[simp] theorem comp_identity (c : Derivor sig tau) : c.comp (identity tau) = c := by
  apply ext (c := c.comp (identity tau)) (d := c) rfl
  apply heq_of_eq
  funext a s σ
  change (identity tau).translate _ (c.image σ) = c.image σ
  rw [translate_identity]
  exact Term.subst_id _

/-- Composition of derivors is associative. -/
theorem comp_assoc (c : Derivor sig tau) (d : Derivor tau ups) (e : Derivor ups xi) :
    (c.comp d).comp e = c.comp (d.comp e) := by
  apply ext (c := (c.comp d).comp e) (d := c.comp (d.comp e)) rfl
  apply heq_of_eq
  funext a s σ
  exact (translate_comp d e (d.positionMap c.sortMap a)
    (e.positionMap (d.sortMap ∘ c.sortMap) a) (c.image σ)).symm

end Derivor

/-- Many-sorted signatures and derivors form a category at fixed sort and symbol universes. -/
instance : Category (ManySortedSignature.{u, v}) where
  Hom A B := Derivor A.symbol B.symbol
  id A := Derivor.identity A.symbol
  comp := Derivor.comp
  id_comp := Derivor.identity_comp
  comp_id := Derivor.comp_identity
  assoc := Derivor.comp_assoc

end CategorialAlgebras
