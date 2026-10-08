/-
Ported from https://github.com/mariovagomarzal/higher_category_theory
(`HigherCategoryTheory/Tactic.lean`).
Copyright (c) 2025 Mario Vago Marzal. Released under Apache 2.0 license.
Authors: Enric Cosme Llópez, Raúl Ruiz Mora, Mario Vago Marzal
-/
import CategorialAlgebras.Init
import Mathlib.Tactic.TryThis

/-!
# Proof automation for higher category theory

This file provides the `hcat_disch` tactic, a proof automation tool for discharging common goals in
higher category theory proofs. It is used extensively as the default proof method for most of the
definitions of the library.

The `hcat_disch` tactic first tries a simple set of tactics and if those fail, it falls back to
`aesop_hcat`, a wrapper around Aesop with the `HigherCategoryTheory` rule set.
-/

namespace CategorialAlgebras

open Lean Meta Elab Tactic in
/--
Core implementation for the `aesop_hcat` family of tactics. Calls Aesop with the
`HigherCategoryTheory` rule set and appropriate configuration.

The `suggest` argument controls whether to use `aesop?` (producing a "Try this" suggestion) or plain
`aesop`. The `clauses` argument allows passing additional Aesop tactic clauses.
-/
private meta def evalAesop (suggest : Bool) (clauses : TSyntaxArray `Aesop.tactic_clause) :
    TacticM Unit := do
  let suggest := suggest || hcat.tactic.suggest.get (← getOptions)
  let nonterminal := hcat.tactic.nonterminal.get (← getOptions)
  let configClause ← `(Aesop.tactic_clause| (config := { terminal := $(quote !nonterminal) }))
  let rsClause ← `(Aesop.tactic_clause| (rule_sets := [$(mkIdent `HigherCategoryTheory):ident]))
  let clauses := clauses |>.push configClause |>.push rsClause
  evalTactic (← if suggest
    then `(tactic| aesop? $clauses*)
    else `(tactic| aesop $clauses*))

/-- A wrapper around Aesop for the `HigherCategoryTheory` rule set. -/
elab (name := aesop_hcat) "aesop_hcat" clauses:Aesop.tactic_clause* : tactic =>
  evalAesop false clauses

/-- A suggestive version of `aesop_hcat` that produces a "Try this" suggestion on success. -/
elab (name := aesop_hcat?) "aesop_hcat?" clauses:Aesop.tactic_clause* : tactic =>
  evalAesop true clauses

open Lean Meta Elab Tactic in
/--
Core implementation for the `hcat_disch` family of tactics. Tries a sequence of tactics to discharge
common higher category theory goals, and falls back to Aesop if those tactics fail.

The `suggest` argument controls whether to produce "Try this" suggestions on success. When `true`,
simple tactics are wrapped with `try_this` and `aesop_hcat` is replaced by `aesop_hcat?`.
-/
private meta def higherCategoryTheoryDischarger (suggest : Bool) : TacticM Unit := do
  let suggest := suggest || hcat.tactic.suggest.get (← getOptions)
  let wrap (tac : TSyntax `tactic) : TacticM (TSyntax `tactic) :=
    if suggest then `(tactic| try_this $tac) else pure tac
  let mut tactics : Array (TSyntax `tactic) := #[]
  tactics := tactics.push (← wrap (← `(tactic| (intros; rfl))))
  if hcat.tactic.omega.get (← getOptions) then
    tactics := tactics.push (← wrap (← `(tactic| (intros; omega))))
  tactics := tactics.push (← if suggest then `(tactic| aesop_hcat?) else `(tactic| aesop_hcat))
  evalTactic (← `(tactic| first $[| $tactics:tactic]*))

/-- A tactic for discharging common goals in higher category theory proofs. -/
elab (name := hcat_disch) "hcat_disch" : tactic =>
  higherCategoryTheoryDischarger false

/-- A suggestive version of `hcat_disch` that produces a "Try this" suggestion on success. -/
elab (name := hcat_disch?) "hcat_disch?" : tactic =>
  higherCategoryTheoryDischarger true

end CategorialAlgebras
