/-
  LeanVerify/Completeness.lean
  Propositional completeness for the Hilbert system:
    If Γ ⊨ φ then Γ ⊢ φ

  Strategy: Kalmár's lemma approach.
  1. Define φ^v (signed formula under valuation v)
  2. Prove Kalmár's lemma: {p₁^v, ..., pₙ^v} ⊢ φ^v for each connective case
  3. Derive completeness via case splitting on atoms

  This corresponds to THM-META002 (Completeness) in the lean text.
-/

import LeanVerify.Hilbert
import LeanVerify.Semantics
import LeanVerify.Deduction
import Mathlib.Order.Zorn

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
  apply Hilbert.deduction_imp
  have hφ : (Γ ∪ {φ}) ⊢ₕ φ := .hyp (Set.mem_union_right _ (Set.mem_singleton _))
  have hsub : Γ ⊆ Γ ∪ {φ} := Set.subset_union_left
  exact .mp (h2.monotone hsub) (.mp (h1.monotone hsub) hφ)

/-- Γ ⊢ A ∧ B from Γ ⊢ A and Γ ⊢ B. -/
theorem Hilbert.conj_intro {Γ : Set Formula} {φ ψ : Formula}
    (h1 : Γ ⊢ₕ φ) (h2 : Γ ⊢ₕ ψ) : Γ ⊢ₕ (φ ⋀ ψ) :=
  .mp (.mp .ax3 h1) h2

/-- Double negation introduction: if Γ ⊢ φ then Γ ⊢ ¬¬φ. -/
theorem Hilbert.double_neg_intro {Γ : Set Formula} {φ : Formula}
    (h : Γ ⊢ₕ φ) : Γ ⊢ₕ ∼(∼φ) :=
  .mp (.mp .ax9 (.mp .ax7 h)) (Hilbert.impl_self Γ (∼φ))

/-- Contraposition: if Γ ⊢ φ → ψ then Γ ⊢ ¬ψ → ¬φ. -/
theorem Hilbert.contrapos {Γ : Set Formula} {φ ψ : Formula}
    (h : Γ ⊢ₕ (φ ⟹ ψ)) : Γ ⊢ₕ (∼ψ ⟹ ∼φ) := by
  apply Hilbert.deduction_imp
  have hsub : Γ ⊆ Γ ∪ {∼ψ} := Set.subset_union_left
  have hns : (Γ ∪ {∼ψ}) ⊢ₕ ∼ψ := .hyp (Set.mem_union_right _ (Set.mem_singleton _))
  exact .mp (.mp .ax9 (h.monotone hsub)) (.mp .ax7 hns)

/-- Case elimination: from p → φ and ¬p → φ, derive φ. -/
theorem Hilbert.case_elim {Γ : Set Formula} {p φ : Formula}
    (h1 : Γ ⊢ₕ (p ⟹ φ)) (h2 : Γ ⊢ₕ (∼p ⟹ φ)) : Γ ⊢ₕ φ :=
  .mp .ax14 (.mp (.mp .ax9 (Hilbert.contrapos h1)) (Hilbert.contrapos h2))

/-- ¬(φ ∧ ψ) from ¬φ. -/
theorem Hilbert.neg_conj_left {Γ : Set Formula} {φ ψ : Formula}
    (h : Γ ⊢ₕ ∼φ) : Γ ⊢ₕ ∼(φ ⋀ ψ) :=
  Hilbert.contradiction .ax1 (.mp .ax7 h)

/-- ¬(φ ∧ ψ) from ¬ψ. -/
theorem Hilbert.neg_conj_right {Γ : Set Formula} {φ ψ : Formula}
    (h : Γ ⊢ₕ ∼ψ) : Γ ⊢ₕ ∼(φ ⋀ ψ) :=
  Hilbert.contradiction .ax2 (.mp .ax7 h)

/-- ¬(φ ∨ ψ) from ¬φ and ¬ψ. -/
theorem Hilbert.neg_disj {Γ : Set Formula} {φ ψ : Formula}
    (h1 : Γ ⊢ₕ ∼φ) (h2 : Γ ⊢ₕ ∼ψ) : Γ ⊢ₕ ∼(φ ⋁ ψ) :=
  .mp .ax13 (.mp (.mp .ax6 (.mp .ax10 h1)) (.mp .ax10 h2))

/-- ¬(φ → ψ) from φ and ¬ψ. -/
theorem Hilbert.neg_impl {Γ : Set Formula} {φ ψ : Formula}
    (h1 : Γ ⊢ₕ φ) (h2 : Γ ⊢ₕ ∼ψ) : Γ ⊢ₕ ∼(φ ⟹ ψ) := by
  have himpl : Γ ⊢ₕ ((φ ⟹ ψ) ⟹ ψ) := by
    apply Hilbert.deduction_imp
    have hsub : Γ ⊆ Γ ∪ {φ ⟹ ψ} := Set.subset_union_left
    exact .mp (.hyp (Set.mem_union_right _ (Set.mem_singleton _))) (h1.monotone hsub)
  exact Hilbert.contradiction himpl (.mp .ax7 h2)

/-- ¬⊥ is provable. -/
theorem Hilbert.neg_bot (Γ : Set Formula) : Γ ⊢ₕ ∼⊥ₚ :=
  .mp .ax13 (Hilbert.impl_self Γ ⊥ₚ)

/-! ### Signed formula and atoms -/

def signedFormula (v : Valuation) (φ : Formula) : Formula :=
  if φ.eval v = true then φ else ∼φ

def atoms : Formula → Finset ℕ
  | .var n => {n}
  | .fls => ∅
  | .tru => ∅
  | .neg φ => atoms φ
  | .conj φ ψ => atoms φ ∪ atoms ψ
  | .disj φ ψ => atoms φ ∪ atoms ψ
  | .impl φ ψ => atoms φ ∪ atoms ψ

def signedAtoms (v : Valuation) (φ : Formula) : Set Formula :=
  { signedFormula v (.var n) | n ∈ atoms φ }

theorem signedFormula_true {v : Valuation} {φ : Formula} (h : φ.eval v = true) :
    signedFormula v φ = φ := by simp [signedFormula, h]

theorem signedFormula_false {v : Valuation} {φ : Formula} (h : φ.eval v = false) :
    signedFormula v φ = ∼φ := by simp [signedFormula, h]

/-! ### Kalmár's Lemma -/

theorem kalmar_core (v : Valuation) : (φ : Formula) → ∀ Γ : Set Formula,
    (∀ n ∈ atoms φ, signedFormula v (.var n) ∈ Γ) →
    Γ ⊢ₕ (signedFormula v φ)
  | .var n, Γ, h => .hyp (h n (Finset.mem_singleton.mpr rfl))
  | .fls, Γ, _ => by
    have : eval v .fls = false := rfl
    rw [signedFormula_false this]; exact Hilbert.neg_bot Γ
  | .tru, Γ, _ => by
    have : eval v .tru = true := rfl
    rw [signedFormula_true this]; exact .ax11
  | .neg φ, Γ, h => by
    simp only [atoms] at h
    have ih := kalmar_core v φ Γ h
    cases hev : φ.eval v
    · -- φ false → neg φ true → need ∼φ
      have hne : eval v (.neg φ) = true := by simp [eval, hev]
      rw [signedFormula_true hne]; rw [signedFormula_false hev] at ih; exact ih
    · -- φ true → neg φ false → need ∼∼φ
      have hne : eval v (.neg φ) = false := by simp [eval, hev]
      rw [signedFormula_false hne]; rw [signedFormula_true hev] at ih
      exact Hilbert.double_neg_intro ih
  | .conj φ ψ, Γ, h => by
    simp only [atoms] at h
    have ihφ := kalmar_core v φ Γ (fun n hn => h n (Finset.mem_union_left _ hn))
    have ihψ := kalmar_core v ψ Γ (fun n hn => h n (Finset.mem_union_right _ hn))
    cases hφv : φ.eval v <;> cases hψv : ψ.eval v
    · rw [signedFormula_false (by simp [eval, hφv, hψv] : eval v (.conj φ ψ) = false)]
      rw [signedFormula_false hφv] at ihφ; exact Hilbert.neg_conj_left ihφ
    · rw [signedFormula_false (by simp [eval, hφv, hψv] : eval v (.conj φ ψ) = false)]
      rw [signedFormula_false hφv] at ihφ; exact Hilbert.neg_conj_left ihφ
    · rw [signedFormula_false (by simp [eval, hφv, hψv] : eval v (.conj φ ψ) = false)]
      rw [signedFormula_false hψv] at ihψ; exact Hilbert.neg_conj_right ihψ
    · rw [signedFormula_true (by simp [eval, hφv, hψv] : eval v (.conj φ ψ) = true)]
      rw [signedFormula_true hφv] at ihφ; rw [signedFormula_true hψv] at ihψ
      exact Hilbert.conj_intro ihφ ihψ
  | .disj φ ψ, Γ, h => by
    simp only [atoms] at h
    have ihφ := kalmar_core v φ Γ (fun n hn => h n (Finset.mem_union_left _ hn))
    have ihψ := kalmar_core v ψ Γ (fun n hn => h n (Finset.mem_union_right _ hn))
    cases hφv : φ.eval v <;> cases hψv : ψ.eval v
    · rw [signedFormula_false (by simp [eval, hφv, hψv] : eval v (.disj φ ψ) = false)]
      rw [signedFormula_false hφv] at ihφ; rw [signedFormula_false hψv] at ihψ
      exact Hilbert.neg_disj ihφ ihψ
    · rw [signedFormula_true (by simp [eval, hφv, hψv] : eval v (.disj φ ψ) = true)]
      rw [signedFormula_true hψv] at ihψ; exact .mp .ax5 ihψ
    · rw [signedFormula_true (by simp [eval, hφv, hψv] : eval v (.disj φ ψ) = true)]
      rw [signedFormula_true hφv] at ihφ; exact .mp .ax4 ihφ
    · rw [signedFormula_true (by simp [eval, hφv, hψv] : eval v (.disj φ ψ) = true)]
      rw [signedFormula_true hφv] at ihφ; exact .mp .ax4 ihφ
  | .impl φ ψ, Γ, h => by
    simp only [atoms] at h
    have ihφ := kalmar_core v φ Γ (fun n hn => h n (Finset.mem_union_left _ hn))
    have ihψ := kalmar_core v ψ Γ (fun n hn => h n (Finset.mem_union_right _ hn))
    cases hφv : φ.eval v <;> cases hψv : ψ.eval v
    · rw [signedFormula_true (by simp [eval, hφv, hψv] : eval v (.impl φ ψ) = true)]
      rw [signedFormula_false hφv] at ihφ; exact .mp .ax10 ihφ
    · rw [signedFormula_true (by simp [eval, hφv, hψv] : eval v (.impl φ ψ) = true)]
      rw [signedFormula_false hφv] at ihφ; exact .mp .ax10 ihφ
    · rw [signedFormula_false (by simp [eval, hφv, hψv] : eval v (.impl φ ψ) = false)]
      rw [signedFormula_true hφv] at ihφ; rw [signedFormula_false hψv] at ihψ
      exact Hilbert.neg_impl ihφ ihψ
    · rw [signedFormula_true (by simp [eval, hφv, hψv] : eval v (.impl φ ψ) = true)]
      rw [signedFormula_true hψv] at ihψ; exact .mp .ax7 ihψ

theorem kalmar_lemma (v : Valuation) (φ : Formula) :
    (signedAtoms v φ) ⊢ₕ (signedFormula v φ) :=
  kalmar_core v φ (signedAtoms v φ) (fun n hn => ⟨n, hn, rfl⟩)

/-! ### Weak completeness via atom elimination -/

/-- Evaluation depends only on the atoms in the formula. -/
theorem eval_eq_of_agree_on_atoms {v w : Valuation} :
    (φ : Formula) → (∀ n ∈ atoms φ, v n = w n) → φ.eval v = φ.eval w
  | .var n, h => h n (Finset.mem_singleton.mpr rfl)
  | .fls, _ => rfl
  | .tru, _ => rfl
  | .neg φ, h => by simp [eval, eval_eq_of_agree_on_atoms φ h]
  | .conj φ ψ, h => by
    simp only [eval]
    rw [eval_eq_of_agree_on_atoms φ (fun n hn => h n (Finset.mem_union_left _ hn)),
        eval_eq_of_agree_on_atoms ψ (fun n hn => h n (Finset.mem_union_right _ hn))]
  | .disj φ ψ, h => by
    simp only [eval]
    rw [eval_eq_of_agree_on_atoms φ (fun n hn => h n (Finset.mem_union_left _ hn)),
        eval_eq_of_agree_on_atoms ψ (fun n hn => h n (Finset.mem_union_right _ hn))]
  | .impl φ ψ, h => by
    simp only [eval]
    rw [eval_eq_of_agree_on_atoms φ (fun n hn => h n (Finset.mem_union_left _ hn)),
        eval_eq_of_agree_on_atoms ψ (fun n hn => h n (Finset.mem_union_right _ hn))]

/-- Helper: signedFormula with Function.update on the same atom. -/
theorem signedFormula_update_same (v : Valuation) (k : ℕ) (b : Bool) :
    signedFormula (Function.update v k b) (.var k) =
      if b then .var k else ∼(.var k) := by
  simp [signedFormula, eval, Function.update]

/-- Helper: signedFormula with Function.update on a different atom. -/
theorem signedFormula_update_noteq (v : Valuation) (k n : ℕ) (b : Bool) (h : n ≠ k) :
    signedFormula (Function.update v k b) (.var n) = signedFormula v (.var n) := by
  simp [signedFormula, eval, Function.update, h]

/-- Atom elimination: if for all v, the signed atoms from a list L
    together with Γ suffice to prove φ, we can remove L one at a time. -/
theorem weak_completeness_aux (φ : Formula) (htaut : φ.isTautology) :
    ∀ (L : List ℕ) (v : Valuation) (Γ : Set Formula),
    (∀ n ∈ atoms φ, n ∉ L → signedFormula v (.var n) ∈ Γ) →
    Γ ⊢ₕ φ := by
  intro L
  induction L with
  | nil =>
    intro v Γ hΓ
    have hΓ' : ∀ n ∈ atoms φ, signedFormula v (.var n) ∈ Γ :=
      fun n hn => hΓ n hn (by simp)
    have := kalmar_core v φ Γ hΓ'
    rwa [signedFormula_true (htaut v)] at this
  | cons k L ih =>
    intro v Γ hΓ
    apply Hilbert.case_elim (p := .var k)
    · -- Branch 1: Γ ⊢ (var k) → φ, i.e., Γ ∪ {var k} ⊢ φ
      apply Hilbert.deduction_imp
      apply ih (Function.update v k true) (Γ ∪ {.var k})
      intro n hn hnL
      by_cases hnk : n = k
      · subst hnk
        rw [signedFormula_update_same, if_pos rfl]
        exact Set.mem_union_right _ (Set.mem_singleton _)
      · rw [signedFormula_update_noteq v k n true hnk]
        have hnkL : n ∉ k :: L := by
          simp only [List.mem_cons, not_or]
          exact ⟨hnk, hnL⟩
        exact Set.mem_union_left _ (hΓ n hn hnkL)
    · -- Branch 2: Γ ⊢ ¬(var k) → φ, i.e., Γ ∪ {∼(var k)} ⊢ φ
      apply Hilbert.deduction_imp
      apply ih (Function.update v k false) (Γ ∪ {∼(.var k)})
      intro n hn hnL
      by_cases hnk : n = k
      · subst hnk
        rw [signedFormula_update_same, if_neg Bool.false_ne_true]
        exact Set.mem_union_right _ (Set.mem_singleton _)
      · rw [signedFormula_update_noteq v k n false hnk]
        have hnkL : n ∉ k :: L := by
          simp only [List.mem_cons, not_or]
          exact ⟨hnk, hnL⟩
        exact Set.mem_union_left _ (hΓ n hn hnkL)

/-- Weak completeness: if φ is a tautology, then ∅ ⊢ₕ φ. -/
theorem weak_completeness {φ : Formula}
    (htaut : φ.isTautology) : (∅ : Set Formula) ⊢ₕ φ :=
  weak_completeness_aux φ htaut (atoms φ).toList (fun _ => true) ∅
    (fun _ hn hnL => absurd ((atoms φ).mem_toList.mpr hn) hnL)

/-! ### Strong completeness via Lindenbaum's lemma -/

section StrongCompleteness

open Classical

/-- Finite support: any derivation uses only finitely many hypotheses. -/
theorem Hilbert.finite_support {Γ : Set Formula} {φ : Formula} (h : Γ ⊢ₕ φ) :
    ∃ Γ₀ : Finset Formula, (↑Γ₀ ⊆ Γ) ∧ ((↑Γ₀ : Set Formula) ⊢ₕ φ) := by
  induction h with
  | hyp hmem =>
    exact ⟨{_}, by simpa using hmem, .hyp (by simp)⟩
  | mp _ _ ih1 ih2 =>
    obtain ⟨Γ₁, h1s, h1p⟩ := ih1
    obtain ⟨Γ₂, h2s, h2p⟩ := ih2
    refine ⟨Γ₁ ∪ Γ₂, ?_, ?_⟩
    · simp only [Finset.coe_union]; exact Set.union_subset h1s h2s
    · exact .mp (h1p.monotone (by simp [Finset.coe_union]))
               (h2p.monotone (by simp [Finset.coe_union]))
  | ax1 => exact ⟨∅, by simp, .ax1⟩
  | ax2 => exact ⟨∅, by simp, .ax2⟩
  | ax3 => exact ⟨∅, by simp, .ax3⟩
  | ax4 => exact ⟨∅, by simp, .ax4⟩
  | ax5 => exact ⟨∅, by simp, .ax5⟩
  | ax6 => exact ⟨∅, by simp, .ax6⟩
  | ax7 => exact ⟨∅, by simp, .ax7⟩
  | ax8 => exact ⟨∅, by simp, .ax8⟩
  | ax9 => exact ⟨∅, by simp, .ax9⟩
  | ax10 => exact ⟨∅, by simp, .ax10⟩
  | ax11 => exact ⟨∅, by simp, .ax11⟩
  | ax12 => exact ⟨∅, by simp, .ax12⟩
  | ax13 => exact ⟨∅, by simp, .ax13⟩
  | ax14 => exact ⟨∅, by simp, .ax14⟩

/-- A finite subset of ⋃₀c is contained in some single member of a chain. -/
private theorem finset_chain_witness
    {c : Set (Set Formula)} (hchain : IsChain (· ⊆ ·) c) (hne : c.Nonempty)
    (F : Finset Formula) (h : (↑F : Set Formula) ⊆ ⋃₀ c) :
    ∃ s ∈ c, (↑F : Set Formula) ⊆ s := by
  induction F using Finset.induction with
  | empty => obtain ⟨s, hs⟩ := hne; exact ⟨s, hs, by simp⟩
  | @insert a t _ ih =>
    have ht : (↑t : Set Formula) ⊆ ⋃₀ c :=
      (Finset.coe_subset.mpr (Finset.subset_insert a t)).trans h
    obtain ⟨s₁, hs₁, hsub₁⟩ := ih ht
    have ha : a ∈ ⋃₀ c := h (by simp)
    obtain ⟨s₂, hs₂, ha₂⟩ := Set.mem_sUnion.mp ha
    rcases hchain.total hs₁ hs₂ with h12 | h21
    · exact ⟨s₂, hs₂, by
        intro y hy
        simp only [Finset.coe_insert, Set.mem_insert_iff] at hy
        rcases hy with rfl | hy
        · exact ha₂
        · exact h12 (hsub₁ hy)⟩
    · exact ⟨s₁, hs₁, by
        intro y hy
        simp only [Finset.coe_insert, Set.mem_insert_iff] at hy
        rcases hy with rfl | hy
        · exact h21 ha₂
        · exact hsub₁ hy⟩

/-- Lindenbaum's lemma: any consistent set extends to a maximal consistent set. -/
theorem lindenbaum {S : Set Formula} (hcon : ¬(S ⊢ₕ ⊥ₚ)) :
    ∃ Δ, S ⊆ Δ ∧ ¬(Δ ⊢ₕ ⊥ₚ) ∧
      ∀ Δ', Δ ⊆ Δ' → ¬(Δ' ⊢ₕ ⊥ₚ) → Δ' ⊆ Δ := by
  have hS : ∃ m, Maximal (· ∈ {Δ | S ⊆ Δ ∧ ¬(Δ ⊢ₕ ⊥ₚ)}) m := by
    apply zorn_subset
    intro c hcS hchain
    by_cases hne : c.Nonempty
    · refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
      · obtain ⟨s, hs⟩ := hne; exact (hcS hs).1.trans (Set.subset_sUnion_of_mem hs)
      · intro hbot
        obtain ⟨F, hFsub, hFprf⟩ := Hilbert.finite_support hbot
        obtain ⟨s, hs, hsub⟩ := finset_chain_witness hchain hne F hFsub
        exact (hcS hs).2 (hFprf.monotone hsub)
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      exact ⟨S, ⟨Set.Subset.rfl, hcon⟩, by simp [hne]⟩
  obtain ⟨Δ, hΔmem, hΔmax⟩ := hS
  exact ⟨Δ, hΔmem.1, hΔmem.2, fun Δ' hsub hcon' =>
    hΔmax ⟨hΔmem.1.trans hsub, hcon'⟩ hsub⟩

/-- A maximal consistent set is deductively closed. -/
private theorem mc_closed {Δ : Set Formula}
    (hΔcon : ¬(Δ ⊢ₕ ⊥ₚ))
    (hΔmax : ∀ Δ', Δ ⊆ Δ' → ¬(Δ' ⊢ₕ ⊥ₚ) → Δ' ⊆ Δ)
    {ψ : Formula} (h : Δ ⊢ₕ ψ) : ψ ∈ Δ := by
  by_contra habs
  have hinconsist : (Δ ∪ {ψ}) ⊢ₕ ⊥ₚ := by
    by_contra hnot
    exact habs (hΔmax (Δ ∪ {ψ}) Set.subset_union_left hnot
      (Set.mem_union_right Δ rfl))
  exact hΔcon (.mp (Hilbert.deduction_imp hinconsist) h)

/-- A maximal consistent set decides every formula. -/
private theorem mc_decides {Δ : Set Formula}
    (hΔcon : ¬(Δ ⊢ₕ ⊥ₚ))
    (hΔmax : ∀ Δ', Δ ⊆ Δ' → ¬(Δ' ⊢ₕ ⊥ₚ) → Δ' ⊆ Δ)
    (ψ : Formula) : ψ ∈ Δ ∨ ∼ψ ∈ Δ := by
  by_contra h
  push_neg at h
  obtain ⟨hψ, hnψ⟩ := h
  have : (Δ ∪ {ψ}) ⊢ₕ ⊥ₚ := by
    by_contra hnot
    exact hψ (hΔmax (Δ ∪ {ψ}) Set.subset_union_left hnot
      (Set.mem_union_right Δ rfl))
  exact hnψ (mc_closed hΔcon hΔmax (.mp .ax13 (Hilbert.deduction_imp this)))

/-- In a maximal consistent set, ¬ψ ∈ Δ ↔ ψ ∉ Δ. -/
private theorem mc_neg_iff {Δ : Set Formula}
    (hΔcon : ¬(Δ ⊢ₕ ⊥ₚ))
    (hΔmax : ∀ Δ', Δ ⊆ Δ' → ¬(Δ' ⊢ₕ ⊥ₚ) → Δ' ⊆ Δ)
    (ψ : Formula) : ∼ψ ∈ Δ ↔ ψ ∉ Δ := by
  constructor
  · intro hneg hψ; exact hΔcon (Hilbert.exfalso (.hyp hψ) (.hyp hneg))
  · intro hψ; exact (mc_decides hΔcon hΔmax ψ).resolve_left hψ

/-- Canonical valuation from a maximal consistent set. -/
noncomputable def canonicalVal (Δ : Set Formula) : Valuation :=
  fun n => if (.var n : Formula) ∈ Δ then true else false

/-- Truth lemma: eval under canonical valuation ↔ membership in Δ. -/
private theorem truth_lemma {Δ : Set Formula}
    (hΔcon : ¬(Δ ⊢ₕ ⊥ₚ))
    (hΔmax : ∀ Δ', Δ ⊆ Δ' → ¬(Δ' ⊢ₕ ⊥ₚ) → Δ' ⊆ Δ) :
    ∀ ψ : Formula, ψ.eval (canonicalVal Δ) = true ↔ ψ ∈ Δ := by
  intro ψ
  induction ψ with
  | var n =>
    constructor
    · intro h
      simp only [eval, canonicalVal] at h
      by_contra hm; rw [if_neg hm] at h; exact absurd h (by decide)
    · intro h
      simp only [eval, canonicalVal, if_pos h]
  | fls =>
    constructor
    · simp [eval]
    · intro hmem; exact absurd (.hyp hmem : Δ ⊢ₕ ⊥ₚ) hΔcon
  | tru =>
    constructor
    · intro _; exact mc_closed hΔcon hΔmax .ax11
    · intro _; rfl
  | neg φ ih =>
    constructor
    · intro h
      have hφf : φ.eval (canonicalVal Δ) = false := by
        cases hc : φ.eval (canonicalVal Δ) with
        | false => rfl
        | true => simp [eval, hc] at h
      exact (mc_neg_iff hΔcon hΔmax φ).mpr (mt ih.mpr (by simp [hφf]))
    · intro hmem
      have hφnΔ : φ ∉ Δ := (mc_neg_iff hΔcon hΔmax φ).mp hmem
      have hφf : φ.eval (canonicalVal Δ) = false := by
        cases hc : φ.eval (canonicalVal Δ) with
        | false => rfl
        | true => exact absurd (ih.mp hc) hφnΔ
      simp [eval, hφf]
  | conj φ ψ ihφ ihψ =>
    constructor
    · intro h
      simp only [eval, Bool.and_eq_true] at h
      exact mc_closed hΔcon hΔmax
        (Hilbert.conj_intro (.hyp (ihφ.mp h.1)) (.hyp (ihψ.mp h.2)))
    · intro hmem
      simp only [eval, Bool.and_eq_true]
      exact ⟨ihφ.mpr (mc_closed hΔcon hΔmax (.mp .ax1 (.hyp hmem))),
             ihψ.mpr (mc_closed hΔcon hΔmax (.mp .ax2 (.hyp hmem)))⟩
  | disj φ ψ ihφ ihψ =>
    constructor
    · intro h
      simp only [eval, Bool.or_eq_true] at h
      rcases h with hφ | hψ
      · exact mc_closed hΔcon hΔmax (.mp .ax4 (.hyp (ihφ.mp hφ)))
      · exact mc_closed hΔcon hΔmax (.mp .ax5 (.hyp (ihψ.mp hψ)))
    · intro hmem
      simp only [eval, Bool.or_eq_true]
      rcases mc_decides hΔcon hΔmax φ with hφ | hnφ
      · exact Or.inl (ihφ.mpr hφ)
      · rcases mc_decides hΔcon hΔmax ψ with hψ | hnψ
        · exact Or.inr (ihψ.mpr hψ)
        · exfalso
          exact hΔcon (Hilbert.exfalso (.hyp hmem)
            (.hyp (mc_closed hΔcon hΔmax
              (Hilbert.neg_disj (.hyp hnφ) (.hyp hnψ)))))
  | impl φ ψ ihφ ihψ =>
    constructor
    · intro h
      cases hφ : φ.eval (canonicalVal Δ) with
      | false =>
        have : φ ∉ Δ := mt ihφ.mpr (by simp [hφ])
        exact mc_closed hΔcon hΔmax (.mp .ax10
          (.hyp ((mc_neg_iff hΔcon hΔmax φ).mpr this)))
      | true =>
        have hψt : ψ.eval (canonicalVal Δ) = true := by simp [eval, hφ] at h; exact h
        exact mc_closed hΔcon hΔmax (.mp .ax7 (.hyp (ihψ.mp hψt)))
    · intro hmem
      cases hφ : φ.eval (canonicalVal Δ) with
      | false => simp [eval, hφ]
      | true =>
        have hψΔ : ψ ∈ Δ :=
          mc_closed hΔcon hΔmax (.mp (.hyp hmem) (.hyp (ihφ.mp hφ)))
        simp [eval, hφ, ihψ.mpr hψΔ]

/-- Strong completeness for propositional logic (THM-META002):
    If Γ ⊨ φ then Γ ⊢ φ. -/
theorem completeness {Γ : Set Formula} {φ : Formula}
    (h : Γ ⊨ₚ φ) : Γ ⊢ₕ φ := by
  by_contra habs
  have hcon : ¬((Γ ∪ {∼φ}) ⊢ₕ ⊥ₚ) :=
    fun hbot => habs (.mp .ax14 (.mp .ax13 (Hilbert.deduction_imp hbot)))
  obtain ⟨Δ, hΔsub, hΔcon, hΔmax⟩ := lindenbaum hcon
  have hv := h (canonicalVal Δ) (fun γ hγ =>
    (truth_lemma hΔcon hΔmax γ).mpr (hΔsub (Set.mem_union_left _ hγ)))
  have hnφ : ∼φ ∈ Δ := hΔsub (Set.mem_union_right _ rfl)
  have hφ_false : φ ∉ Δ := (mc_neg_iff hΔcon hΔmax φ).mp hnφ
  exact hφ_false ((truth_lemma hΔcon hΔmax φ).mp hv)

end StrongCompleteness

end PropLogic
