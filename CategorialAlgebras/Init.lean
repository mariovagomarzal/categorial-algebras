/-
Ported from https://github.com/mariovagomarzal/higher_category_theory
(`HigherCategoryTheory/Init.lean`).
Copyright (c) 2025 Mario Vago Marzal. Released under Apache 2.0 license.
Authors: Enric Cosme Llópez, Raúl Ruiz Mora, Mario Vago Marzal
-/
import Aesop

/-!
# Init

The `HigherCategoryTheory` rule set for Aesop and the options that control the `hcat_disch`
tactic of `CategorialAlgebras.Tactic`.
-/

declare_aesop_rule_sets [HigherCategoryTheory]

/-- Option to override the suggestive behavior of `hcat_disch` and `aesop_hcat`. -/
register_option hcat.tactic.suggest : Bool := {
  defValue := false
  descr := "The `hcat_disch` and `aesop_hcat` tactics produce \"Try this\" suggestions."
}

/-- Option to control whether `aesop_hcat` runs in non-terminal mode. -/
register_option hcat.tactic.nonterminal : Bool := {
  defValue := false
  descr := "The `aesop_hcat` tactic runs in non-terminal mode."
}

/-- Option to control whether a wrapped `omega` is tried as part of `hcat_disch`. -/
register_option hcat.tactic.omega : Bool := {
  defValue := false
  descr := "A wrapped version of `omega` is tried as part of the `hcat_disch` tactic."
}
