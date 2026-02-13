/-
  LeanVerify/Syntax.lean
  Propositional formulas matching CH-SYN of the lean text.

  We use a simple inductive type with atoms indexed by ℕ.
  Connectives: ⊥, ⊤, ¬, ∧, ∨, →
-/

import Mathlib.Tactic

namespace PropLogic

/-- Propositional formulas (DEF-SYN001 / DEF-SYN002). -/
inductive Formula where
  | var  : ℕ → Formula
  | fls  : Formula          -- ⊥
  | tru  : Formula          -- ⊤
  | neg  : Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | impl : Formula → Formula → Formula
  deriving DecidableEq, Repr

namespace Formula

-- Notation
scoped notation:max "#" n => Formula.var n
scoped notation "⊥ₚ" => Formula.fls
scoped notation "⊤ₚ" => Formula.tru
scoped prefix:75 "∼" => Formula.neg
scoped infixl:65 " ⋀ " => Formula.conj
scoped infixl:60 " ⋁ " => Formula.disj
scoped infixr:55 " ⟹ " => Formula.impl

end Formula

end PropLogic
