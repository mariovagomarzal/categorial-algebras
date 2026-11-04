import Mathlib.Data.PFun
import Mathlib.CategoryTheory.Category.Basic
import CategorialAlgebras.Signature

/-!
# Partial algebras and QE-equations

Definitions `DVarCompact` and `DVarExtended` of the draft present categorial algebras as a $\mathrm{QE}$-variety of
partial algebras: models of a set of quasi-existence equations. The notions of partial
algebra, term, existence equation and $\mathrm{QE}$-equation are those of the preliminaries
of the draft (Definitions `DPartialAlg` and `DQEEq`), the usual ones for
many-sorted partial algebras: an
*existence equation* $t \overset{\mathrm{e}}{=} t'$ holds when both sides are defined and
equal, and a $\mathrm{QE}$-*equation* is an implication from a finite conjunction of
existence equations to an existence equation.
-/

universe u v w

namespace CategorialAlgebras

open Signature

variable {S : Type u}

/-!
## Terms
-/

/-- Let $\Sigma$ be an $S$-sorted signature and $V$ an $S$-sorted set of *variables*. The
$S$-sorted set $\mathrm{T}_{\Sigma}(V)$ of *terms* is the least one that contains the
variables, $x \in \mathrm{T}_{\Sigma}(V)_s$ for $x \in V_s$, and is closed under the operation
symbols: $\sigma((t_j)_{j \in |\mathbf{s}|}) \in \mathrm{T}_{\Sigma}(V)_s$ for
$\sigma \in \Sigma_{\mathbf{s}, s}$ and $t_j \in \mathrm{T}_{\Sigma}(V)_{s_j}$.
-/
inductive Term (Sig : Signature.{u, v} S) (V : S → Type) : S → Type (max u v)
  /-- A variable. -/
  | var {s : S} (x : V s) : Term Sig V s
  /-- An operation symbol applied to a family of terms. -/
  | app {ws : List S} {s : S} (σ : Sig ws s) (ts : (j : Fin ws.length) → Term Sig V (ws.get j)) :
      Term Sig V s

/-!
## Partial algebras
-/

/-- A *partial* $\Sigma$-*algebra* is a pair $\mathbf{A} = (A, F)$ where $A$ is an $S$-sorted set
and $F$ assigns to every $\sigma \in \Sigma_{\mathbf{s}, s}$ a partial mapping
$F_\sigma \colon A_{\mathbf{s}} \rightharpoonup A_s$.
-/
structure PartialAlgebra (Sig : Signature.{u, v} S) where
  /-- The underlying `S`-sorted set. -/
  carrier : S → Type w
  /-- The partial operation of each operation symbol. -/
  op : ∀ {ws : List S} {s : S}, Sig ws s → Arity carrier ws →. carrier s

namespace PartialAlgebra

variable {Sig : Signature.{u, v} S}

instance : CoeFun (PartialAlgebra.{u, v, w} Sig) fun _ ↦ S → Type w := ⟨PartialAlgebra.carrier⟩

attribute [coe] PartialAlgebra.carrier

/-- A *homomorphism* from $\mathbf{A}$ to $\mathbf{B}$ is an $S$-sorted mapping
$h = (h_s)_{s \in S}$ such that, whenever $F_\sigma((a_j)_j)$ is defined, so is
$G_\sigma((h_{s_j}(a_j))_j)$, and $h_s(F_\sigma((a_j)_j)) = G_\sigma((h_{s_j}(a_j))_j)$. These
are the homomorphisms the draft uses: they need not reflect definedness.
-/
structure Hom (A B : PartialAlgebra.{u, v, w} Sig) where
  /-- The mapping at each sort. -/
  map : ∀ s, A s → B s
  /-- Defined operations are sent to defined operations. -/
  map_dom : ∀ {ws : List S} {s : S} (σ : Sig ws s) (a : Arity A ws),
    (A.op σ a).Dom → (B.op σ (fun j => map (ws.get j) (a j))).Dom
  /-- The mapping commutes with the operations, where they are defined. -/
  map_op : ∀ {ws : List S} {s : S} (σ : Sig ws s) (a : Arity A ws) (h : (A.op σ a).Dom),
    map s ((A.op σ a).get h) = (B.op σ (fun j => map (ws.get j) (a j))).get (map_dom σ a h)

namespace Hom

@[ext]
lemma ext {A B : PartialAlgebra.{u, v, w} Sig} {H K : Hom A B} (h : ∀ s x, H.map s x = K.map s x) :
    H = K := by
  cases H; cases K; congr; funext s x; exact h s x

/-- The identity homomorphism. -/
def id (A : PartialAlgebra.{u, v, w} Sig) : Hom A A where
  map _ x := x
  map_dom _ _ h := h
  map_op _ _ _ := rfl

/-- The composite of two homomorphisms. -/
def comp {A B C : PartialAlgebra.{u, v, w} Sig} (K : Hom B C) (H : Hom A B) : Hom A C where
  map s x := K.map s (H.map s x)
  map_dom σ a h := K.map_dom σ _ (H.map_dom σ a h)
  map_op σ a h := by
    change K.map _ (H.map _ ((A.op σ a).get h)) = _
    rw [H.map_op σ a h, K.map_op]

end Hom

end PartialAlgebra

/-!
## Evaluation of terms
-/

/-- Let $\mathbf{A}$ be a partial $\Sigma$-algebra and $v \colon V \rightharpoonup A$ an
$S$-sorted partial mapping, a *valuation*. The value $t^{\mathbf{A}}[v]$ of a term $t$ is
partial: $x^{\mathbf{A}}[v] = v(x)$ for a variable, defined when $v$ is defined at $x$, and
$\sigma((t_j)_j)^{\mathbf{A}}[v]$ is defined exactly when every $t_j^{\mathbf{A}}[v]$ is
defined and $F_\sigma$ is defined on their family, and then is
$F_\sigma((t_j^{\mathbf{A}}[v])_j)$.

The draft takes total valuations $v \colon V \to A$. Valuations are partial here so that an
equation can be evaluated with values for its own variables only; see the definition of
$\mathrm{QE}$-equations below.
-/
def Term.eval {Sig : Signature.{u, v} S} {V : S → Type} (A : PartialAlgebra.{u, v, w} Sig)
    (val : ∀ s, V s → Part (A s)) : {s : S} → Term Sig V s → Part (A s)
  | _, .var x => val _ x
  | _, .app σ ts =>
    ⟨∃ h : ∀ j, (Term.eval A val (ts j)).Dom,
        (A.op σ fun j => (Term.eval A val (ts j)).get (h j)).Dom,
      fun h => (A.op σ fun j => (Term.eval A val (ts j)).get (h.1 j)).get h.2⟩

/-- The set $\mathrm{Var}(t)$ of the variables that occur in a term $t$, as pairs of a sort and a
variable of that sort: $\mathrm{Var}(x) = \{x\}$ and
$\mathrm{Var}(\sigma((t_j)_j)) = \bigcup_j \mathrm{Var}(t_j)$.
-/
def Term.vars {Sig : Signature.{u, v} S} {V : S → Type} :
    {s : S} → Term Sig V s → Set (Σ t, V t)
  | _, .var x => {⟨_, x⟩}
  | _, .app _ ts => ⋃ j, (ts j).vars

/-!
## QE-equations and their models
-/

/-!
### Existence equations and QE-equations

An *existence equation* $t \overset{\mathrm{e}}{=} t'$ is a pair of terms of the same sort; it
*holds* in $\mathbf{A}$ under a valuation $v$ when $t^{\mathbf{A}}[v]$ and
$t'^{\mathbf{A}}[v]$ are both defined and are equal. In particular
$t \overset{\mathrm{e}}{=} t$ says that $t$ is defined. A $\mathrm{QE}$-*equation*
$\bigwedge_{i} (t_i \overset{\mathrm{e}}{=} t'_i) \longrightarrow t \overset{\mathrm{e}}{=} t'$
is a finite list of existence equations, its *premises*, and an existence equation, its
*conclusion*; its *variables* are those that occur in its premises or in its conclusion. It
*holds* in $\mathbf{A}$ when, for every valuation defined at its variables under which all the
premises hold, the conclusion holds. A $\mathrm{QE}$-equation without premises is an
existence equation.

Definition `DQEEq` of the draft asks the conclusion for every total valuation
$v \colon V \to A$. When $A$ has an empty sort there are no such valuations, and every
equation holds in $\mathbf{A}$, whatever the other sorts are: for $S = \{a, b\}$, a partial
algebra with $A_a = \varnothing$ would be a model of every specification. Asking it only for the
valuations of the variables of the equation, as is usual in many-sorted equational logic, makes
the satisfaction of an equation depend only on the sorts of its variables. The two notions agree
on partial algebras whose sorts are all nonempty.
-/

structure EEq (Sig : Signature.{u, v} S) (V : S → Type) where
  /-- The sort of both sides. -/
  sort : S
  /-- The left-hand side. -/
  lhs : Term Sig V sort
  /-- The right-hand side. -/
  rhs : Term Sig V sort

structure QEEq (Sig : Signature.{u, v} S) (V : S → Type) where
  /-- The premises. -/
  premises : List (EEq Sig V)
  /-- The conclusion. -/
  conclusion : EEq Sig V

variable {Sig : Signature.{u, v} S} {V : S → Type}

def EEq.vars (e : EEq Sig V) : Set (Σ t, V t) := e.lhs.vars ∪ e.rhs.vars

def QEEq.vars (q : QEEq Sig V) : Set (Σ t, V t) :=
  q.conclusion.vars ∪ ⋃ e ∈ q.premises, e.vars

def EEq.Holds (A : PartialAlgebra.{u, v, w} Sig) (val : ∀ s, V s → Part (A s)) (e : EEq Sig V) :
    Prop :=
  ∃ (h₁ : (e.lhs.eval A val).Dom) (h₂ : (e.rhs.eval A val).Dom),
    (e.lhs.eval A val).get h₁ = (e.rhs.eval A val).get h₂

def QEEq.Holds (A : PartialAlgebra.{u, v, w} Sig) (q : QEEq Sig V) : Prop :=
  ∀ val : ∀ s, V s → Part (A s), (∀ x ∈ q.vars, (val x.1 x.2).Dom) →
    (∀ e ∈ q.premises, e.Holds A val) → q.conclusion.Holds A val

/-!
### The category of models of a QE-specification

A $\mathrm{QE}$-*specification* is a set $\mathcal{E}$ of $\mathrm{QE}$-equations. Its
*models* are the partial $\Sigma$-algebras in which every equation of $\mathcal{E}$ holds;
they form the $\mathrm{QE}$-variety $\mathcal{V}(\mathcal{E})$, and, with the homomorphisms of
partial algebras, the category $\mathsf{PAlg}(\mathcal{E})$.
-/

def PAlg (E : Set (QEEq Sig V)) : Type (max u v (w + 1)) :=
  {A : PartialAlgebra.{u, v, w} Sig // ∀ q ∈ E, q.Holds A}

instance (E : Set (QEEq Sig V)) : CategoryTheory.Category.{max u w} (PAlg.{u, v, w} E) where
  Hom A B := PartialAlgebra.Hom A.1 B.1
  id A := PartialAlgebra.Hom.id A.1
  comp H K := PartialAlgebra.Hom.comp K H
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-!
## Notation for equations

The specifications of the draft are written with a few kinds of terms: an operation symbol
applied to one, two or a family of terms. The helpers below build them.
-/

namespace Term

variable {Sig : Signature.{u, v} S} {V : S → Type}

/-- The family of arguments of a unary operation symbol. -/
def args₁ {s : S} (t : Term Sig V s) : (j : Fin [s].length) → Term Sig V ([s].get j)
  | ⟨0, _⟩ => t

/-- The family of arguments of a binary operation symbol. -/
def args₂ {s₀ s₁ : S} (t₀ : Term Sig V s₀) (t₁ : Term Sig V s₁) :
    (j : Fin [s₀, s₁].length) → Term Sig V ([s₀, s₁].get j)
  | ⟨0, _⟩ => t₀
  | ⟨1, _⟩ => t₁

/-- A unary operation symbol applied to a term. -/
def app₁ {s t : S} (σ : Sig [s] t) (x : Term Sig V s) : Term Sig V t := .app σ (args₁ x)

/-- A binary operation symbol applied to two terms. -/
def app₂ {s₀ s₁ t : S} (σ : Sig [s₀, s₁] t) (x : Term Sig V s₀) (y : Term Sig V s₁) :
    Term Sig V t :=
  .app σ (args₂ x y)

end Term

/-- The existence equation `t ≐ t'`. -/
def EEq.mk' {Sig : Signature.{u, v} S} {V : S → Type} {s : S} (t t' : Term Sig V s) :
    EEq Sig V :=
  ⟨s, t, t'⟩

/-- The existence equation `t ≐ t`, saying that `t` is defined. -/
def EEq.defined {Sig : Signature.{u, v} S} {V : S → Type} {s : S} (t : Term Sig V s) :
    EEq Sig V :=
  ⟨s, t, t⟩

end CategorialAlgebras
