/-
  LeanVerify/Deduction.lean
  The Deduction Theorem for the propositional Hilbert system:
    Γ ∪ {A} ⊢ B  ↔  Γ ⊢ A → B

  This corresponds to THM-DED001 in the lean text (DED.2.3).
  The proof follows the book's induction on derivation length.
-/

import LeanVerify.Hilbert

namespace PropLogic

open Formula

/-- A → A is provable from any Γ, using axioms A7 and A8.
    This is the base case where B ≡ A in the deduction theorem. -/
theorem Hilbert.impl_self (Γ : Set Formula) (φ : Formula) :
    Γ ⊢ₕ (φ ⟹ φ) := by
  -- φ → ((φ → φ) → φ)          by A7
  -- (φ → ((φ→φ) → φ)) → ((φ → (φ→φ)) → (φ → φ))  by A8
  -- φ → (φ → φ)                by A7
  -- (φ → (φ → φ)) → (φ → φ)   by MP on A8
  -- φ → φ                       by MP on A7
  have h1 : Γ ⊢ₕ (φ ⟹ ((φ ⟹ φ) ⟹ φ)) := .ax7
  have h2 : Γ ⊢ₕ ((φ ⟹ ((φ ⟹ φ) ⟹ φ)) ⟹ ((φ ⟹ (φ ⟹ φ)) ⟹ (φ ⟹ φ))) := .ax8
  have h3 : Γ ⊢ₕ ((φ ⟹ (φ ⟹ φ)) ⟹ (φ ⟹ φ)) := .mp h2 h1
  have h4 : Γ ⊢ₕ (φ ⟹ (φ ⟹ φ)) := .ax7
  exact .mp h3 h4

/-- Deduction theorem, "only if" direction:
    If Γ ∪ {A} ⊢ B then Γ ⊢ A → B.
    Proof by induction on the derivation. -/
theorem Hilbert.deduction_imp {Γ : Set Formula} {A B : Formula}
    (h : (Γ ∪ {A}) ⊢ₕ B) : Γ ⊢ₕ (A ⟹ B) := by
  induction h with
  | hyp hmem =>
    cases hmem with
    | inl hΓ =>
      -- B ∈ Γ: derive Γ ⊢ B, then use A7 to get Γ ⊢ A → B
      exact .mp .ax7 (.hyp hΓ)
    | inr hA =>
      -- B = A: derive Γ ⊢ A → A
      rw [Set.mem_singleton_iff] at hA
      rw [hA]
      exact Hilbert.impl_self Γ A
  | ax1 => exact .mp .ax7 .ax1
  | ax2 => exact .mp .ax7 .ax2
  | ax3 => exact .mp .ax7 .ax3
  | ax4 => exact .mp .ax7 .ax4
  | ax5 => exact .mp .ax7 .ax5
  | ax6 => exact .mp .ax7 .ax6
  | ax7 => exact .mp .ax7 .ax7
  | ax8 => exact .mp .ax7 .ax8
  | ax9 => exact .mp .ax7 .ax9
  | ax10 => exact .mp .ax7 .ax10
  | ax11 => exact .mp .ax7 .ax11
  | ax12 => exact .mp .ax7 .ax12
  | ax13 => exact .mp .ax7 .ax13
  | ax14 => exact .mp .ax7 .ax14
  | mp _ _ ih1 ih2 =>
    -- ih1 : Γ ⊢ A → (C → B)
    -- ih2 : Γ ⊢ A → C
    -- Need: Γ ⊢ A → B
    -- Use A8: (A → (C → B)) → ((A → C) → (A → B))
    exact .mp (.mp .ax8 ih1) ih2

/-- Deduction theorem, "if" direction:
    If Γ ⊢ A → B then Γ ∪ {A} ⊢ B.
    Uses monotonicity + modus ponens. -/
theorem Hilbert.deduction_of_imp {Γ : Set Formula} {A B : Formula}
    (h : Γ ⊢ₕ (A ⟹ B)) : (Γ ∪ {A}) ⊢ₕ B := by
  have hAB : (Γ ∪ {A}) ⊢ₕ (A ⟹ B) :=
    h.monotone Set.subset_union_left
  have hA : (Γ ∪ {A}) ⊢ₕ A :=
    .hyp (Set.mem_union_right Γ (Set.mem_singleton A))
  exact .mp hAB hA

/-- The Deduction Theorem (THM-DED001):
    Γ ∪ {φ} ⊢ ψ  ↔  Γ ⊢ φ → ψ -/
theorem deduction_theorem (Γ : Set Formula) (φ ψ : Formula) :
    ((Γ ∪ {φ}) ⊢ₕ ψ) ↔ (Γ ⊢ₕ (φ ⟹ ψ)) :=
  ⟨Hilbert.deduction_imp, Hilbert.deduction_of_imp⟩

end PropLogic
