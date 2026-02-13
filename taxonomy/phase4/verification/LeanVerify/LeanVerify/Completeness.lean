/-
  LeanVerify/Completeness.lean
  Propositional completeness for the Hilbert system:
    If Γ ⊨ φ then Γ ⊢ φ

  Strategy: Kalmár's lemma approach.
  1. Define φ^v (signed formula under valuation v)
  2. Prove Kalmár's lemma: {p₁^v, ..., pₙ^v} ⊢ φ^v for each connective case
  3. Derive completeness via case splitting on atoms

  This corresponds to THM-META002 (Completeness) in the lean text.

  STATUS: The overall structure is set up and the key helper lemmas
  (exfalso, contradiction, dne, impl_self) are fully proved. The
  Kalmár induction and elimination steps use `sorry` — completing
  these requires ~300-500 lines of set-manipulation infrastructure
  typical for this style of proof in Lean.
-/

import LeanVerify.Hilbert
import LeanVerify.Semantics
import LeanVerify.Deduction

namespace PropLogic

open Formula

/-! ### Helper derivations needed for completeness -/

/-- If Γ ⊢ A and Γ ⊢ ¬A, then Γ ⊢ B (ex falso quodlibet). -/
theorem Hilbert.exfalso {Γ : Set Formula} {φ ψ : Formula}
    (h1 : Γ ⊢ₕ φ) (h2 : Γ ⊢ₕ ∼φ) : Γ ⊢ₕ ψ :=
  .mp (.mp .ax10 h2) h1

/-- If Γ ⊢ A → B and Γ ⊢ A → ¬B, then Γ ⊢ ¬A. -/
theorem Hilbert.contradiction {Γ : Set Formula} {φ ψ : Formula}
    (h1 : Γ ⊢ₕ (φ ⟹ ψ)) (h2 : Γ ⊢ₕ (φ ⟹ ∼ψ)) : Γ ⊢ₕ ∼φ :=
  .mp (.mp .ax9 h1) h2

/-- Transitivity of ⊢: if Γ ⊢ A → B and Γ ⊢ B → C then Γ ⊢ A → C. -/
theorem Hilbert.impl_trans {Γ : Set Formula} {φ ψ χ : Formula}
    (h1 : Γ ⊢ₕ (φ ⟹ ψ)) (h2 : Γ ⊢ₕ (ψ ⟹ χ)) : Γ ⊢ₕ (φ ⟹ χ) := by
  -- Use deduction theorem: suffices to show Γ ∪ {φ} ⊢ χ
  apply Hilbert.deduction_imp
  have hφ : (Γ ∪ {φ}) ⊢ₕ φ := .hyp (Set.mem_union_right _ (Set.mem_singleton _))
  have hsub : Γ ⊆ Γ ∪ {φ} := Set.subset_union_left
  have h1' := h1.monotone hsub
  have h2' := h2.monotone hsub
  exact .mp h2' (.mp h1' hφ)

/-- Γ ⊢ A → B → A∧B  (from A3, curried) -/
theorem Hilbert.conj_intro {Γ : Set Formula} {φ ψ : Formula}
    (h1 : Γ ⊢ₕ φ) (h2 : Γ ⊢ₕ ψ) : Γ ⊢ₕ (φ ⋀ ψ) :=
  .mp (.mp .ax3 h1) h2

/-! ### Signed formula -/

/-- φ^v: if v makes φ true, return φ; if false, return ¬φ. -/
def signedFormula (v : Valuation) (φ : Formula) : Formula :=
  if φ.eval v = true then φ else ∼φ

/-- Collect all atom indices occurring in a formula. -/
def atoms : Formula → Finset ℕ
  | .var n => {n}
  | .fls => ∅
  | .tru => ∅
  | .neg φ => atoms φ
  | .conj φ ψ => atoms φ ∪ atoms ψ
  | .disj φ ψ => atoms φ ∪ atoms ψ
  | .impl φ ψ => atoms φ ∪ atoms ψ

/-- The set of signed atoms as hypotheses. -/
def signedAtoms (v : Valuation) (φ : Formula) : Set Formula :=
  { signedFormula v (.var n) | n ∈ atoms φ }

/-! ### Kalmár's Lemma -/

/-- Kalmár's lemma: from the signed atoms of φ under v, we can derive φ^v.
    This is the core technical lemma for completeness.

    The proof proceeds by structural induction on φ, case-splitting on
    the truth value of each subformula under v. Each connective case
    uses the corresponding axioms (A1-A14) to build the derivation.

    SORRY: Full formalization requires extensive Finset/Set manipulation
    for monotonicity across signedAtoms of subformulas. -/
theorem kalmar_lemma (v : Valuation) (φ : Formula) :
    (signedAtoms v φ) ⊢ₕ (signedFormula v φ) := by
  sorry

/-! ### Completeness theorems -/

/-- Weak completeness for propositional logic:
    If φ is a tautology, then ∅ ⊢ φ.

    Proof sketch: Apply Kalmár's lemma for each valuation, then
    use the deduction theorem to eliminate signed atoms one by one.
    For each atom p, both the p-branch and ¬p-branch yield φ,
    so p can be eliminated. After eliminating all atoms, ∅ ⊢ φ. -/
theorem weak_completeness {φ : Formula}
    (htaut : φ.isTautology) : (∅ : Set Formula) ⊢ₕ φ := by
  sorry

/-- Strong completeness for propositional logic:
    If Γ ⊨ φ then Γ ⊢ φ (THM-META002).

    Follows from weak completeness applied to the finite conjunction
    of the relevant hypotheses, plus the deduction theorem. -/
theorem completeness {Γ : Set Formula} {φ : Formula}
    (h : Γ ⊨ₚ φ) : Γ ⊢ₕ φ := by
  sorry

end PropLogic
