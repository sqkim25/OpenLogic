/-
  LeanVerify/Hilbert.lean
  Hilbert-style axiomatic proof system matching DED.2 of the lean text.

  Axioms A1-A14 (AX-DED003) + Modus Ponens (AX-DED001).
  This is the propositional fragment only (no quantifier axioms/rules).
-/

import LeanVerify.Syntax

namespace PropLogic

open Formula

/-- Hilbert-style derivability: Γ ⊢ φ.
    Axioms A1-A14 from AX-DED003, Modus Ponens from AX-DED001. -/
inductive Hilbert (Γ : Set Formula) : Formula → Prop where
  -- Hypothesis
  | hyp    : φ ∈ Γ → Hilbert Γ φ
  -- A1: (A ∧ B) → A
  | ax1    : Hilbert Γ ((φ ⋀ ψ) ⟹ φ)
  -- A2: (A ∧ B) → B
  | ax2    : Hilbert Γ ((φ ⋀ ψ) ⟹ ψ)
  -- A3: A → (B → (A ∧ B))
  | ax3    : Hilbert Γ (φ ⟹ (ψ ⟹ (φ ⋀ ψ)))
  -- A4: A → (A ∨ B)
  | ax4    : Hilbert Γ (φ ⟹ (φ ⋁ ψ))
  -- A5: A → (B ∨ A)
  | ax5    : Hilbert Γ (φ ⟹ (ψ ⋁ φ))
  -- A6: (A → C) → ((B → C) → ((A ∨ B) → C))
  | ax6    : Hilbert Γ ((φ ⟹ χ) ⟹ ((ψ ⟹ χ) ⟹ ((φ ⋁ ψ) ⟹ χ)))
  -- A7: A → (B → A)  [K combinator]
  | ax7    : Hilbert Γ (φ ⟹ (ψ ⟹ φ))
  -- A8: (A → (B → C)) → ((A → B) → (A → C))  [S combinator]
  | ax8    : Hilbert Γ ((φ ⟹ (ψ ⟹ χ)) ⟹ ((φ ⟹ ψ) ⟹ (φ ⟹ χ)))
  -- A9: (A → B) → ((A → ¬B) → ¬A)  [contraposition]
  | ax9    : Hilbert Γ ((φ ⟹ ψ) ⟹ ((φ ⟹ ∼ψ) ⟹ ∼φ))
  -- A10: ¬A → (A → B)  [ex falso from negation]
  | ax10   : Hilbert Γ (∼φ ⟹ (φ ⟹ ψ))
  -- A11: ⊤
  | ax11   : Hilbert Γ ⊤ₚ
  -- A12: ⊥ → A
  | ax12   : Hilbert Γ (⊥ₚ ⟹ φ)
  -- A13: (A → ⊥) → ¬A
  | ax13   : Hilbert Γ ((φ ⟹ ⊥ₚ) ⟹ ∼φ)
  -- A14: ¬¬A → A  [double negation elimination]
  | ax14   : Hilbert Γ (∼(∼φ) ⟹ φ)
  -- Modus Ponens (AX-DED001)
  | mp     : Hilbert Γ (φ ⟹ ψ) → Hilbert Γ φ → Hilbert Γ ψ

scoped notation:30 Γ " ⊢ₕ " φ => Hilbert Γ φ

/-- Monotonicity: if Γ ⊆ Δ and Γ ⊢ φ, then Δ ⊢ φ. -/
theorem Hilbert.monotone {Γ Δ : Set Formula} {φ : Formula}
    (hsub : Γ ⊆ Δ) (h : Γ ⊢ₕ φ) : Δ ⊢ₕ φ := by
  induction h with
  | hyp hmem => exact .hyp (hsub hmem)
  | mp _ _ ih1 ih2 => exact .mp ih1 ih2
  | ax1 => exact .ax1
  | ax2 => exact .ax2
  | ax3 => exact .ax3
  | ax4 => exact .ax4
  | ax5 => exact .ax5
  | ax6 => exact .ax6
  | ax7 => exact .ax7
  | ax8 => exact .ax8
  | ax9 => exact .ax9
  | ax10 => exact .ax10
  | ax11 => exact .ax11
  | ax12 => exact .ax12
  | ax13 => exact .ax13
  | ax14 => exact .ax14

end PropLogic
