import Stemma
import CategorialAlgebras.PartialAlgebra
import CategorialAlgebras.Compact.Algebra

open Verso.Genre Manual InlineLean Stemma

#doc (Stemma) "The compact QE-specification" =>

Definition `DVarCompact` of the draft presents the compact $`n`-categorial $`\Sigma`-algebras as a
$`\mathrm{QE}`$-variety of partial $`\Sigma^{(n)}`-algebras, where $`\Sigma^{(n)}` is the
compact $`n`-categorial signature of Definition `DSigmaCatCompact`. This document writes down the
specification $`\mathcal{C}^{\Sigma^{(n)}}` and the category
$`\mathsf{PAlg}(\mathcal{C}^{\Sigma^{(n)}})` of its models.

```lean
universe u v w

namespace CategorialAlgebras.Compact

open Term

variable {S : Type u}
```

# Terms of the compact signature

The variables $`V^{S}` are a fixed $`S`-sorted set with countably many variables of each sort;
we take $`V^{S}_s = \mathbb{N}`. We write $`\mathrm{sc}^{k}(t)`, $`\mathrm{tg}^{k}(t)` and
$`t \circ^{k} t'` for the terms built with the symbols of Definition `DSigmaCatCompact`, and
$`\sigma((t_j)_j)` for an operation symbol of $`\Sigma`; in the Lean they are `scT`, `tgT`,
`compT` and `opT`, and `x i` is the variable number `i`.

```lean
/-- The variables: countably many of each sort. -/
abbrev Var (S : Type u) : S → Type := fun _ => ℕ

/-- Terms of the compact `n`-categorial signature, with variables in `Var S`. -/
abbrev CTerm (Sig : Signature.{u, v} S) (n : ℕ) := Term (CompactSignature Sig n) (Var S)

namespace CTerm

variable {Sig : Signature.{u, v} S} {n : ℕ}

def x {s : S} (i : ℕ) : CTerm Sig n s := .var (s := s) i

def scT (k : Fin n) {s : S} (t : CTerm Sig n s) : CTerm Sig n s :=
  app₁ (CompactSignature.sc k s) t

def tgT (k : Fin n) {s : S} (t : CTerm Sig n s) : CTerm Sig n s :=
  app₁ (CompactSignature.tg k s) t

def compT (k : Fin n) {s : S} (t t' : CTerm Sig n s) : CTerm Sig n s :=
  app₂ (CompactSignature.comp k s) t t'

def opT {ws : List S} {s : S} (σ : Sig ws s) (ts : (j : Fin ws.length) → CTerm Sig n (ws.get j)) :
    CTerm Sig n s :=
  .app (CompactSignature.op σ) ts

end CTerm
```

# The specification

:::definition (label := "compact.qe-specification") (central := false) (title := "The specification C^Σ⁽ⁿ⁾")
Let $`\Sigma` be an $`S`-sorted signature and $`n \in \mathbb{N}`. The specification
$`\mathcal{C}^{\Sigma^{(n)}}` is the set of the following $`\mathrm{QE}`$-equations of
$`\Sigma^{(n)}` with variables in $`V^{S}`, for all sorts, operation symbols, dimensions and
variables (Definition `DVarCompact` of the draft):

1. (A0) $`\sigma((x_j)_j) \overset{\mathrm{e}}{=} \sigma((x_j)_j)`;
2. for every $`k \in n`:
   (A$`^k`1) $`\mathrm{sc}^{k}(x)` and $`\mathrm{tg}^{k}(x)` are defined;
   (A$`^k`2) $`\mathrm{sc}^{k}\mathrm{sc}^{k}(x) \overset{\mathrm{e}}{=} \mathrm{sc}^{k}(x)`,
   $`\mathrm{sc}^{k}\mathrm{tg}^{k}(x) \overset{\mathrm{e}}{=} \mathrm{tg}^{k}(x)`,
   $`\mathrm{tg}^{k}\mathrm{sc}^{k}(x) \overset{\mathrm{e}}{=} \mathrm{sc}^{k}(x)`,
   $`\mathrm{tg}^{k}\mathrm{tg}^{k}(x) \overset{\mathrm{e}}{=} \mathrm{tg}^{k}(x)`;
   (A$`^k`3) $`x \circ^{k} y` is defined if and only if
   $`\mathrm{sc}^{k}(x) \overset{\mathrm{e}}{=} \mathrm{tg}^{k}(y)`;
   (A$`^k`4) if $`x \circ^{k} y` is defined, its $`k`-source is $`\mathrm{sc}^{k}(y)` and its
   $`k`-target is $`\mathrm{tg}^{k}(x)`;
   (A$`^k`5) $`x \circ^{k} \mathrm{sc}^{k}(x) \overset{\mathrm{e}}{=} x` and
   $`\mathrm{tg}^{k}(x) \circ^{k} x \overset{\mathrm{e}}{=} x`;
   (A$`^k`6) if $`x \circ^{k} y` and $`y \circ^{k} z` are defined, then
   $`(x \circ^{k} y) \circ^{k} z \overset{\mathrm{e}}{=} x \circ^{k} (y \circ^{k} z)`;
   (A$`^k`7) $`\mathrm{sc}^{k}(\sigma((x_j)_j)) \overset{\mathrm{e}}{=} \sigma((\mathrm{sc}^{k}(x_j))_j)`
   and likewise for $`\mathrm{tg}^{k}`;
   (A$`^k`8) if every $`x_j \circ^{k} y_j` is defined, then
   $`\sigma((x_j \circ^{k} y_j)_j) \overset{\mathrm{e}}{=} \sigma((x_j)_j) \circ^{k} \sigma((y_j)_j)`;
3. for all $`l < k` in $`n`:
   (AB$`^{l,k}`1) $`\mathrm{sc}^{k}\mathrm{sc}^{l}(x)`, $`\mathrm{sc}^{l}\mathrm{sc}^{k}(x)` and
   $`\mathrm{sc}^{l}\mathrm{tg}^{k}(x)` are equal to $`\mathrm{sc}^{l}(x)`, and
   $`\mathrm{tg}^{k}\mathrm{tg}^{l}(x)`, $`\mathrm{tg}^{l}\mathrm{tg}^{k}(x)` and
   $`\mathrm{tg}^{l}\mathrm{sc}^{k}(x)` are equal to $`\mathrm{tg}^{l}(x)`;
   (AB$`^{l,k}`2) if $`x \circ^{l} y` is defined, then
   $`\mathrm{sc}^{k}(x \circ^{l} y) \overset{\mathrm{e}}{=} \mathrm{sc}^{k}(x) \circ^{l} \mathrm{sc}^{k}(y)`,
   and likewise for $`\mathrm{tg}^{k}`;
   (AB$`^{l,k}`3) if $`x \circ^{l} y`, $`z \circ^{l} t`, $`x \circ^{k} z` and $`y \circ^{k} t` are
   defined, then
   $`(x \circ^{l} y) \circ^{k} (z \circ^{l} t) \overset{\mathrm{e}}{=} (x \circ^{k} z) \circ^{l} (y \circ^{k} t)`.

The variables $`x, y, z, t` are $`x_0, x_1, x_2, x_3` of the relevant sort, and the families
$`(x_j)_j`, $`(y_j)_j` are any families of variables.

```lean
open CTerm in
inductive CompactAxiom (Sig : Signature.{u, v} S) (n : ℕ) :
    QEEq (CompactSignature Sig n) (Var S) → Prop
  | A0 {ws : List S} {s : S} (σ : Sig ws s) (xs : Fin ws.length → ℕ) :
      CompactAxiom Sig n ⟨[], .defined (opT σ fun j => x (xs j))⟩
  | A1_sc (k : Fin n) (s : S) (i : ℕ) :
      CompactAxiom Sig n ⟨[], .defined (scT k (x (s := s) i))⟩
  | A1_tg (k : Fin n) (s : S) (i : ℕ) :
      CompactAxiom Sig n ⟨[], .defined (tgT k (x (s := s) i))⟩
  | A2_sc_sc (k : Fin n) (s : S) (i : ℕ) :
      CompactAxiom Sig n ⟨[], .mk' (scT k (scT k (x (s := s) i))) (scT k (x i))⟩
  | A2_sc_tg (k : Fin n) (s : S) (i : ℕ) :
      CompactAxiom Sig n ⟨[], .mk' (scT k (tgT k (x (s := s) i))) (tgT k (x i))⟩
  | A2_tg_sc (k : Fin n) (s : S) (i : ℕ) :
      CompactAxiom Sig n ⟨[], .mk' (tgT k (scT k (x (s := s) i))) (scT k (x i))⟩
  | A2_tg_tg (k : Fin n) (s : S) (i : ℕ) :
      CompactAxiom Sig n ⟨[], .mk' (tgT k (tgT k (x (s := s) i))) (tgT k (x i))⟩
  | A3_dom (k : Fin n) (s : S) (i j : ℕ) :
      CompactAxiom Sig n
        ⟨[.defined (compT k (x (s := s) i) (x j))], .mk' (scT k (x (s := s) i)) (tgT k (x j))⟩
  | A3_def (k : Fin n) (s : S) (i j : ℕ) :
      CompactAxiom Sig n
        ⟨[.mk' (scT k (x (s := s) i)) (tgT k (x j))], .defined (compT k (x (s := s) i) (x j))⟩
  | A4_sc (k : Fin n) (s : S) (i j : ℕ) :
      CompactAxiom Sig n ⟨[.defined (compT k (x (s := s) i) (x j))],
        .mk' (scT k (compT k (x (s := s) i) (x j))) (scT k (x j))⟩
  | A4_tg (k : Fin n) (s : S) (i j : ℕ) :
      CompactAxiom Sig n ⟨[.defined (compT k (x (s := s) i) (x j))],
        .mk' (tgT k (compT k (x (s := s) i) (x j))) (tgT k (x i))⟩
  | A5_sc (k : Fin n) (s : S) (i : ℕ) :
      CompactAxiom Sig n ⟨[], .mk' (compT k (x (s := s) i) (scT k (x i))) (x i)⟩
  | A5_tg (k : Fin n) (s : S) (i : ℕ) :
      CompactAxiom Sig n ⟨[], .mk' (compT k (tgT k (x (s := s) i)) (x i)) (x i)⟩
  | A6 (k : Fin n) (s : S) (i j l : ℕ) :
      CompactAxiom Sig n
        ⟨[.defined (compT k (x (s := s) i) (x j)), .defined (compT k (x (s := s) j) (x l))],
          .mk' (compT k (compT k (x (s := s) i) (x j)) (x l))
            (compT k (x i) (compT k (x j) (x l)))⟩
  | A7_sc (k : Fin n) {ws : List S} {s : S} (σ : Sig ws s) (xs : Fin ws.length → ℕ) :
      CompactAxiom Sig n
        ⟨[], .mk' (scT k (opT σ fun j => x (xs j))) (opT σ fun j => scT k (x (xs j)))⟩
  | A7_tg (k : Fin n) {ws : List S} {s : S} (σ : Sig ws s) (xs : Fin ws.length → ℕ) :
      CompactAxiom Sig n
        ⟨[], .mk' (tgT k (opT σ fun j => x (xs j))) (opT σ fun j => tgT k (x (xs j)))⟩
  | A8 (k : Fin n) {ws : List S} {s : S} (σ : Sig ws s) (xs ys : Fin ws.length → ℕ) :
      CompactAxiom Sig n
        ⟨List.ofFn fun j => .defined (compT k (x (s := ws.get j) (xs j)) (x (ys j))),
          .mk' (opT σ fun j => compT k (x (xs j)) (x (ys j)))
            (compT k (opT σ fun j => x (xs j)) (opT σ fun j => x (ys j)))⟩
  | AB1_sc_sc (l k : Fin n) (h : l < k) (s : S) (i : ℕ) :
      CompactAxiom Sig n ⟨[], .mk' (scT k (scT l (x (s := s) i))) (scT l (x i))⟩
  | AB1_tg_tg (l k : Fin n) (h : l < k) (s : S) (i : ℕ) :
      CompactAxiom Sig n ⟨[], .mk' (tgT k (tgT l (x (s := s) i))) (tgT l (x i))⟩
  | AB1_sc_sck (l k : Fin n) (h : l < k) (s : S) (i : ℕ) :
      CompactAxiom Sig n ⟨[], .mk' (scT l (scT k (x (s := s) i))) (scT l (x i))⟩
  | AB1_tg_tgk (l k : Fin n) (h : l < k) (s : S) (i : ℕ) :
      CompactAxiom Sig n ⟨[], .mk' (tgT l (tgT k (x (s := s) i))) (tgT l (x i))⟩
  | AB1_sc_tgk (l k : Fin n) (h : l < k) (s : S) (i : ℕ) :
      CompactAxiom Sig n ⟨[], .mk' (scT l (tgT k (x (s := s) i))) (scT l (x i))⟩
  | AB1_tg_sck (l k : Fin n) (h : l < k) (s : S) (i : ℕ) :
      CompactAxiom Sig n ⟨[], .mk' (tgT l (scT k (x (s := s) i))) (tgT l (x i))⟩
  | AB2_sc (l k : Fin n) (h : l < k) (s : S) (i j : ℕ) :
      CompactAxiom Sig n ⟨[.defined (compT l (x (s := s) i) (x j))],
        .mk' (scT k (compT l (x (s := s) i) (x j))) (compT l (scT k (x i)) (scT k (x j)))⟩
  | AB2_tg (l k : Fin n) (h : l < k) (s : S) (i j : ℕ) :
      CompactAxiom Sig n ⟨[.defined (compT l (x (s := s) i) (x j))],
        .mk' (tgT k (compT l (x (s := s) i) (x j))) (compT l (tgT k (x i)) (tgT k (x j)))⟩
  | AB3 (l k : Fin n) (h : l < k) (s : S) (i j p q : ℕ) :
      CompactAxiom Sig n
        ⟨[.defined (compT l (x (s := s) i) (x j)), .defined (compT l (x (s := s) p) (x q)),
            .defined (compT k (x (s := s) i) (x p)), .defined (compT k (x (s := s) j) (x q))],
          .mk' (compT k (compT l (x (s := s) i) (x j)) (compT l (x p) (x q)))
            (compT l (compT k (x i) (x p)) (compT k (x j) (x q)))⟩

/-- The specification `C^{Σ^{(n)}}`. -/
def compactSpec (Sig : Signature.{u, v} S) (n : ℕ) :
    Set (QEEq (CompactSignature Sig n) (Var S)) :=
  {q | CompactAxiom Sig n q}

/-- The category `PAlg(C^{Σ^{(n)}})` of models of the compact specification. -/
abbrev CompactPAlg (Sig : Signature.{u, v} S) (n : ℕ) := PAlg.{u, max u v, w} (compactSpec Sig n)
```
:::

```lean
end CategorialAlgebras.Compact
```
