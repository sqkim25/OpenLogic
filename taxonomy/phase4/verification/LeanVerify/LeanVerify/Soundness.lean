/-
  LeanVerify/Soundness.lean
  Soundness theorem for the propositional Hilbert system:
    If Γ ⊢ φ then Γ ⊨ φ

  This corresponds to THM-META001 (Soundness) in the lean text.
-/

import LeanVerify.Hilbert
import LeanVerify.Semantics

namespace PropLogic

open Formula

/-- Soundness: if Γ ⊢ φ then Γ ⊨ φ (THM-META001). -/
theorem soundness {Γ : Set Formula} {φ : Formula}
    (h : Γ ⊢ₕ φ) : Γ ⊨ₚ φ := by
  induction h with
  | hyp hmem =>
    intro v hΓ; exact hΓ _ hmem
  | ax1 =>
    intro v _; simp [eval]; cases eval v _ <;> cases eval v _ <;> simp
  | ax2 =>
    intro v _; simp [eval]; cases eval v _ <;> cases eval v _ <;> simp
  | ax3 =>
    intro v _; simp [eval]; cases eval v _ <;> cases eval v _ <;> simp
  | ax4 =>
    intro v _; simp [eval]; cases eval v _ <;> simp
  | ax5 =>
    intro v _; simp [eval]; cases eval v _ <;> simp
  | ax6 =>
    intro v _; simp [eval]
    cases eval v _ <;> cases eval v _ <;> cases eval v _ <;> simp
  | ax7 =>
    intro v _; simp [eval]; cases eval v _ <;> simp
  | ax8 =>
    intro v _; simp [eval]
    cases eval v _ <;> cases eval v _ <;> cases eval v _ <;> simp
  | ax9 =>
    intro v _; simp [eval]; cases eval v _ <;> cases eval v _ <;> simp
  | ax10 =>
    intro v _; simp [eval]; cases eval v _ <;> simp
  | ax11 =>
    intro v _; simp [eval]
  | ax12 =>
    intro v _; simp [eval]
  | ax13 =>
    intro v _; simp [eval]
  | ax14 =>
    intro v _; simp [eval]
  | mp _ _ ih1 ih2 =>
    intro v hΓ
    have h1 := ih1 v hΓ  -- eval v (φ ⟹ ψ) = true
    have h2 := ih2 v hΓ  -- eval v φ = true
    -- h1 : !(eval v φ) || (eval v ψ) = true
    -- h2 : eval v φ = true
    -- Goal: eval v ψ = true
    simp [eval] at h1
    -- h1 : eval v φ = false ∨ eval v ψ = true
    rcases h1 with h1f | h1t
    · -- eval v φ = false contradicts h2
      simp [h1f] at h2
    · exact h1t

end PropLogic
