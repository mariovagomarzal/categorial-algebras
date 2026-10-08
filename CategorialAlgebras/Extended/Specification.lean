import Stemma
import CategorialAlgebras.PartialAlgebra
import CategorialAlgebras.Extended.Algebra

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "The extended QE-specification" =>

Definition 8.5 of the draft presents the extended $`n`-categorial $`\Sigma`-algebras as a
$`\mathrm{QE}`$-variety of partial $`\Sigma^{\mathrm{ext}(n)}`-algebras, where
$`\Sigma^{\mathrm{ext}(n)}` is the extended $`n`-categorial signature of Definition 8.4, with
sorts $`(n+1) \times S`. This document writes down the specification
$`\mathcal{C}^{\Sigma^{\mathrm{ext}(n)}}` and the category of its models.

```lean
universe u v w

namespace CategorialAlgebras.Extended

open Term

variable {S : Type u}
```

# Terms of the extended signature

The variables are countably many of each sort $`(k, s)`. In the Lean, `x i` is the variable
number `i`, and `scT h`, `tgT h`, `idmT h` and `compT h`, for `h : j < k`, build the terms
$`\mathrm{sc}^{(j,k)}(t)`, $`\mathrm{tg}^{(j,k)}(t)`, $`\mathrm{i}^{(k,j)}(t)` and
$`t \circ^{(j,k)} t'`; `opT k σ` applies the copy $`\sigma_k` of $`\sigma` to a family of terms
of sorts $`(k, s_p)`.

```lean
/-- The variables: countably many of each sort. -/
abbrev EVar (S : Type u) (n : ℕ) : FinSucc n × S → Type := fun _ => ℕ

/-- Terms of the extended `n`-categorial signature. -/
abbrev ETerm (Sig : Signature.{u, v} S) (n : ℕ) := Term (ExtendedSignature Sig n) (EVar S n)

namespace ETerm

variable {Sig : Signature.{u, v} S} {n : ℕ}

/-- A family of terms of sorts `(k, s_p)`, seen as the arguments of the copy `σ_k`. -/
def liftArgs (k : FinSucc n) (ws : List S)
    (ts : (p : Fin ws.length) → ETerm Sig n (k, ws.get p)) :
    (p : Fin (ws.map fun t => (k, t)).length) → ETerm Sig n ((ws.map fun t => (k, t)).get p) :=
  fun p => cast (congrArg (ETerm Sig n) (by simp)) (ts (Fin.cast (by simp) p))

def x {t : FinSucc n × S} (i : ℕ) : ETerm Sig n t := .var (s := t) i

def scT {j k : FinSucc n} (h : j < k) {s : S} (t : ETerm Sig n (k, s)) : ETerm Sig n (j, s) :=
  app₁ (ExtendedSignature.sc h s) t

def tgT {j k : FinSucc n} (h : j < k) {s : S} (t : ETerm Sig n (k, s)) : ETerm Sig n (j, s) :=
  app₁ (ExtendedSignature.tg h s) t

def idmT {j k : FinSucc n} (h : j < k) {s : S} (t : ETerm Sig n (j, s)) : ETerm Sig n (k, s) :=
  app₁ (ExtendedSignature.idm h s) t

def compT {j k : FinSucc n} (h : j < k) {s : S} (t t' : ETerm Sig n (k, s)) :
    ETerm Sig n (k, s) :=
  app₂ (ExtendedSignature.comp h s) t t'

def opT (k : FinSucc n) {ws : List S} {s : S} (σ : Sig ws s)
    (ts : (p : Fin ws.length) → ETerm Sig n (k, ws.get p)) : ETerm Sig n (k, s) :=
  .app (ExtendedSignature.op k σ) (liftArgs k ws ts)

end ETerm
```

# The specification

:::definition (label := "extended.qe-specification") (central := false) (title := "The specification C^Σᵉˣᵗ⁽ⁿ⁾")
Let $`\Sigma` be an $`S`-sorted signature and $`n \in \mathbb{N}`. The specification
$`\mathcal{C}^{\Sigma^{\mathrm{ext}(n)}}` is the set of the following $`\mathrm{QE}`$-equations,
for all sorts, operation symbols, dimensions and variables (Definition 8.5 of the draft):

1. (EA0) $`\sigma_k((x_p)_p)` is defined, for every $`k \in n + 1`;
2. for all $`j < k` in $`n + 1`:
   (EA$`^{j,k}`1) $`\mathrm{sc}^{(j,k)}(x)`, $`\mathrm{tg}^{(j,k)}(x)` and $`\mathrm{i}^{(k,j)}(u)`
   are defined;
   (EA$`^{j,k}`2) $`\mathrm{sc}^{(j,k)}\mathrm{i}^{(k,j)}(u) \overset{\mathrm{e}}{=} u` and
   $`\mathrm{tg}^{(j,k)}\mathrm{i}^{(k,j)}(u) \overset{\mathrm{e}}{=} u`;
   (EA$`^{j,k}`3) $`x \circ^{(j,k)} y` is defined if and only if
   $`\mathrm{sc}^{(j,k)}(x) \overset{\mathrm{e}}{=} \mathrm{tg}^{(j,k)}(y)`;
   (EA$`^{j,k}`4) if $`x \circ^{(j,k)} y` is defined, its $`(j,k)`-source is
   $`\mathrm{sc}^{(j,k)}(y)` and its $`(j,k)`-target is $`\mathrm{tg}^{(j,k)}(x)`;
   (EA$`^{j,k}`5) $`x \circ^{(j,k)} \mathrm{i}^{(k,j)}\mathrm{sc}^{(j,k)}(x) \overset{\mathrm{e}}{=} x`
   and $`\mathrm{i}^{(k,j)}\mathrm{tg}^{(j,k)}(x) \circ^{(j,k)} x \overset{\mathrm{e}}{=} x`;
   (EA$`^{j,k}`6) associativity of $`\circ^{(j,k)}` where defined;
   (EA$`^{j,k}`7) $`\mathrm{sc}^{(j,k)}(\sigma_k((x_p)_p)) \overset{\mathrm{e}}{=} \sigma_j((\mathrm{sc}^{(j,k)}(x_p))_p)`,
   likewise for $`\mathrm{tg}^{(j,k)}`, and
   $`\mathrm{i}^{(k,j)}(\sigma_j((u_p)_p)) \overset{\mathrm{e}}{=} \sigma_k((\mathrm{i}^{(k,j)}(u_p))_p)`;
   (EA$`^{j,k}`8) if every $`x_p \circ^{(j,k)} y_p` is defined, then
   $`\sigma_k((x_p \circ^{(j,k)} y_p)_p) \overset{\mathrm{e}}{=} \sigma_k((x_p)_p) \circ^{(j,k)} \sigma_k((y_p)_p)`;
3. for all $`h < j < k` in $`n + 1`:
   (EA$`^{h,j,k}`1) $`\mathrm{sc}^{(h,j)}\mathrm{sc}^{(j,k)}(x)` and
   $`\mathrm{sc}^{(h,j)}\mathrm{tg}^{(j,k)}(x)` are equal to $`\mathrm{sc}^{(h,k)}(x)`, and
   $`\mathrm{tg}^{(h,j)}\mathrm{tg}^{(j,k)}(x)` and $`\mathrm{tg}^{(h,j)}\mathrm{sc}^{(j,k)}(x)`
   to $`\mathrm{tg}^{(h,k)}(x)`;
   (EA$`^{h,j,k}`2) $`\mathrm{i}^{(k,j)}\mathrm{i}^{(j,h)}(u) \overset{\mathrm{e}}{=} \mathrm{i}^{(k,h)}(u)`;
   (EA$`^{h,j,k}`3) if $`x \circ^{(h,k)} y` is defined, then
   $`\mathrm{sc}^{(j,k)}(x \circ^{(h,k)} y) \overset{\mathrm{e}}{=} \mathrm{sc}^{(j,k)}(x) \circ^{(h,j)} \mathrm{sc}^{(j,k)}(y)`,
   and likewise for targets;
   (EA$`^{h,j,k}`4) if $`x \circ^{(j,k)} y`, $`z \circ^{(j,k)} t`, $`x \circ^{(h,k)} z` and
   $`y \circ^{(h,k)} t` are defined, then
   $`(x \circ^{(j,k)} y) \circ^{(h,k)} (z \circ^{(j,k)} t) \overset{\mathrm{e}}{=} (x \circ^{(h,k)} z) \circ^{(j,k)} (y \circ^{(h,k)} t)`;
   (EA$`^{h,j,k}`5) if $`u \circ^{(h,j)} v` is defined, then
   $`\mathrm{i}^{(k,j)}(u \circ^{(h,j)} v) \overset{\mathrm{e}}{=} \mathrm{i}^{(k,j)}(u) \circ^{(h,k)} \mathrm{i}^{(k,j)}(v)`.

The axioms (EA$`^{h,j,k}`1)–(EA$`^{h,j,k}`5) are the counterparts of the conditions (MS1),
(MS4), (MS3), (MS9) and (MS8) of Definition 8.1, so that the models of the specification are,
as the draft says, the extended $`n`-categories with operations that are extended
$`n`-functors.

```lean
open ETerm in
inductive ExtendedAxiom (Sig : Signature.{u, v} S) (n : ℕ) :
    QEEq (ExtendedSignature Sig n) (EVar S n) → Prop
  | EA0 (k : FinSucc n) {ws : List S} {s : S} (σ : Sig ws s) (xs : Fin ws.length → ℕ) :
      ExtendedAxiom Sig n ⟨[], .defined (opT k σ fun p => x (xs p))⟩
  | EA1_sc {j k : FinSucc n} (h : j < k) (s : S) (i : ℕ) :
      ExtendedAxiom Sig n ⟨[], .defined (scT h (x (t := (k, s)) i))⟩
  | EA1_tg {j k : FinSucc n} (h : j < k) (s : S) (i : ℕ) :
      ExtendedAxiom Sig n ⟨[], .defined (tgT h (x (t := (k, s)) i))⟩
  | EA1_idm {j k : FinSucc n} (h : j < k) (s : S) (i : ℕ) :
      ExtendedAxiom Sig n ⟨[], .defined (idmT h (x (t := (j, s)) i))⟩
  | EA2_sc {j k : FinSucc n} (h : j < k) (s : S) (i : ℕ) :
      ExtendedAxiom Sig n ⟨[], .mk' (scT h (idmT h (x (t := (j, s)) i))) (x i)⟩
  | EA2_tg {j k : FinSucc n} (h : j < k) (s : S) (i : ℕ) :
      ExtendedAxiom Sig n ⟨[], .mk' (tgT h (idmT h (x (t := (j, s)) i))) (x i)⟩
  | EA3_dom {j k : FinSucc n} (h : j < k) (s : S) (i i' : ℕ) :
      ExtendedAxiom Sig n ⟨[.defined (compT h (x (t := (k, s)) i) (x i'))],
        .mk' (scT h (x (t := (k, s)) i)) (tgT h (x i'))⟩
  | EA3_def {j k : FinSucc n} (h : j < k) (s : S) (i i' : ℕ) :
      ExtendedAxiom Sig n ⟨[.mk' (scT h (x (t := (k, s)) i)) (tgT h (x i'))],
        .defined (compT h (x (t := (k, s)) i) (x i'))⟩
  | EA4_sc {j k : FinSucc n} (h : j < k) (s : S) (i i' : ℕ) :
      ExtendedAxiom Sig n ⟨[.defined (compT h (x (t := (k, s)) i) (x i'))],
        .mk' (scT h (compT h (x (t := (k, s)) i) (x i'))) (scT h (x i'))⟩
  | EA4_tg {j k : FinSucc n} (h : j < k) (s : S) (i i' : ℕ) :
      ExtendedAxiom Sig n ⟨[.defined (compT h (x (t := (k, s)) i) (x i'))],
        .mk' (tgT h (compT h (x (t := (k, s)) i) (x i'))) (tgT h (x i))⟩
  | EA5_sc {j k : FinSucc n} (h : j < k) (s : S) (i : ℕ) :
      ExtendedAxiom Sig n
        ⟨[], .mk' (compT h (x (t := (k, s)) i) (idmT h (scT h (x i)))) (x i)⟩
  | EA5_tg {j k : FinSucc n} (h : j < k) (s : S) (i : ℕ) :
      ExtendedAxiom Sig n
        ⟨[], .mk' (compT h (idmT h (tgT h (x (t := (k, s)) i))) (x i)) (x i)⟩
  | EA6 {j k : FinSucc n} (h : j < k) (s : S) (i i' i'' : ℕ) :
      ExtendedAxiom Sig n
        ⟨[.defined (compT h (x (t := (k, s)) i) (x i')),
            .defined (compT h (x (t := (k, s)) i') (x i''))],
          .mk' (compT h (compT h (x (t := (k, s)) i) (x i')) (x i''))
            (compT h (x i) (compT h (x i') (x i'')))⟩
  | EA7_sc {j k : FinSucc n} (h : j < k) {ws : List S} {s : S} (σ : Sig ws s)
      (xs : Fin ws.length → ℕ) :
      ExtendedAxiom Sig n
        ⟨[], .mk' (scT h (opT k σ fun p => x (xs p))) (opT j σ fun p => scT h (x (xs p)))⟩
  | EA7_tg {j k : FinSucc n} (h : j < k) {ws : List S} {s : S} (σ : Sig ws s)
      (xs : Fin ws.length → ℕ) :
      ExtendedAxiom Sig n
        ⟨[], .mk' (tgT h (opT k σ fun p => x (xs p))) (opT j σ fun p => tgT h (x (xs p)))⟩
  | EA7_idm {j k : FinSucc n} (h : j < k) {ws : List S} {s : S} (σ : Sig ws s)
      (us : Fin ws.length → ℕ) :
      ExtendedAxiom Sig n
        ⟨[], .mk' (idmT h (opT j σ fun p => x (us p))) (opT k σ fun p => idmT h (x (us p)))⟩
  | EA8 {j k : FinSucc n} (h : j < k) {ws : List S} {s : S} (σ : Sig ws s)
      (xs ys : Fin ws.length → ℕ) :
      ExtendedAxiom Sig n
        ⟨List.ofFn fun p => .defined (compT h (x (t := (k, ws.get p)) (xs p)) (x (ys p))),
          .mk' (opT k σ fun p => compT h (x (xs p)) (x (ys p)))
            (compT h (opT k σ fun p => x (xs p)) (opT k σ fun p => x (ys p)))⟩
  | EA1'_sc_sc {a b c : FinSucc n} (h₁ : a < b) (h₂ : b < c) (s : S) (i : ℕ) :
      ExtendedAxiom Sig n
        ⟨[], .mk' (scT h₁ (scT h₂ (x (t := (c, s)) i))) (scT (h₁.trans h₂) (x i))⟩
  | EA1'_tg_tg {a b c : FinSucc n} (h₁ : a < b) (h₂ : b < c) (s : S) (i : ℕ) :
      ExtendedAxiom Sig n
        ⟨[], .mk' (tgT h₁ (tgT h₂ (x (t := (c, s)) i))) (tgT (h₁.trans h₂) (x i))⟩
  | EA1'_sc_tg {a b c : FinSucc n} (h₁ : a < b) (h₂ : b < c) (s : S) (i : ℕ) :
      ExtendedAxiom Sig n
        ⟨[], .mk' (scT h₁ (tgT h₂ (x (t := (c, s)) i))) (scT (h₁.trans h₂) (x i))⟩
  | EA1'_tg_sc {a b c : FinSucc n} (h₁ : a < b) (h₂ : b < c) (s : S) (i : ℕ) :
      ExtendedAxiom Sig n
        ⟨[], .mk' (tgT h₁ (scT h₂ (x (t := (c, s)) i))) (tgT (h₁.trans h₂) (x i))⟩
  | EA2' {a b c : FinSucc n} (h₁ : a < b) (h₂ : b < c) (s : S) (i : ℕ) :
      ExtendedAxiom Sig n
        ⟨[], .mk' (idmT h₂ (idmT h₁ (x (t := (a, s)) i))) (idmT (h₁.trans h₂) (x i))⟩
  | EA3'_sc {a b c : FinSucc n} (h₁ : a < b) (h₂ : b < c) (s : S) (i i' : ℕ) :
      ExtendedAxiom Sig n ⟨[.defined (compT (h₁.trans h₂) (x (t := (c, s)) i) (x i'))],
        .mk' (scT h₂ (compT (h₁.trans h₂) (x (t := (c, s)) i) (x i')))
          (compT h₁ (scT h₂ (x i)) (scT h₂ (x i')))⟩
  | EA3'_tg {a b c : FinSucc n} (h₁ : a < b) (h₂ : b < c) (s : S) (i i' : ℕ) :
      ExtendedAxiom Sig n ⟨[.defined (compT (h₁.trans h₂) (x (t := (c, s)) i) (x i'))],
        .mk' (tgT h₂ (compT (h₁.trans h₂) (x (t := (c, s)) i) (x i')))
          (compT h₁ (tgT h₂ (x i)) (tgT h₂ (x i')))⟩
  | EA4' {a b c : FinSucc n} (h₁ : a < b) (h₂ : b < c) (s : S) (i i' p q : ℕ) :
      ExtendedAxiom Sig n
        ⟨[.defined (compT h₂ (x (t := (c, s)) i) (x i')),
            .defined (compT h₂ (x (t := (c, s)) p) (x q)),
            .defined (compT (h₁.trans h₂) (x (t := (c, s)) i) (x p)),
            .defined (compT (h₁.trans h₂) (x (t := (c, s)) i') (x q))],
          .mk' (compT (h₁.trans h₂) (compT h₂ (x (t := (c, s)) i) (x i'))
              (compT h₂ (x p) (x q)))
            (compT h₂ (compT (h₁.trans h₂) (x i) (x p)) (compT (h₁.trans h₂) (x i') (x q)))⟩
  | EA5' {a b c : FinSucc n} (h₁ : a < b) (h₂ : b < c) (s : S) (i i' : ℕ) :
      ExtendedAxiom Sig n ⟨[.defined (compT h₁ (x (t := (b, s)) i) (x i'))],
        .mk' (idmT h₂ (compT h₁ (x (t := (b, s)) i) (x i')))
          (compT (h₁.trans h₂) (idmT h₂ (x i)) (idmT h₂ (x i')))⟩

/-- The specification `C^{Σ^{ext(n)}}`. -/
def extendedSpec (Sig : Signature.{u, v} S) (n : ℕ) :
    Set (QEEq (ExtendedSignature Sig n) (EVar S n)) :=
  {q | ExtendedAxiom Sig n q}

/-- The category `PAlg(C^{Σ^{ext(n)}})` of models of the extended specification. -/
abbrev ExtendedPAlg (Sig : Signature.{u, v} S) (n : ℕ) :=
  PAlg.{u, max u v, w} (extendedSpec Sig n)
```
:::

```lean
end CategorialAlgebras.Extended
```
