/-
  LeanVerify/Semantics.lean
  Propositional semantics matching CH-SEM of the lean text.

  A valuation v : ℕ → Bool assigns truth values to atoms.
  eval v φ computes the truth value of φ under v.
-/

import LeanVerify.Syntax

namespace PropLogic

/-- A valuation assigns a truth value to each propositional variable. -/
abbrev Valuation := ℕ → Bool

/-- Truth-value evaluation of a formula under a valuation (DEF-SEM001). -/
def Formula.eval (v : Valuation) : Formula → Bool
  | .var n    => v n
  | .fls      => false
  | .tru      => true
  | .neg φ    => !(φ.eval v)
  | .conj φ ψ => (φ.eval v) && (ψ.eval v)
  | .disj φ ψ => (φ.eval v) || (ψ.eval v)
  | .impl φ ψ => !(φ.eval v) || (ψ.eval v)

/-- A formula is a tautology if it evaluates to true under every valuation. -/
def Formula.isTautology (φ : Formula) : Prop :=
  ∀ v : Valuation, φ.eval v = true

/-- Semantic consequence: Γ ⊨ φ iff every valuation making all of Γ true
    also makes φ true. -/
def SemConseq (Γ : Set Formula) (φ : Formula) : Prop :=
  ∀ v : Valuation, (∀ ψ ∈ Γ, ψ.eval v = true) → φ.eval v = true

scoped notation:30 Γ " ⊨ₚ " φ => SemConseq Γ φ

end PropLogic
