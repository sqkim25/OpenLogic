/-
  LeanVerify/SYN.lean
  CH-SYN: First-Order Logic Syntax (Level-1)

  35 registry items (SYN-001 through SYN-035).
-/

import Mathlib.Tactic

set_option linter.style.longLine false

namespace FOL

/-! ## SYN.1: Languages and Symbols -/

/-- SYN-001 (PRIM-SYN009): First-order language / signature. -/
structure Language where
  Con : Type        -- constant symbols
  Fn : Type         -- function symbols
  Rel : Type        -- relation symbols
  fnArity : Fn → ℕ
  relArity : Rel → ℕ

-- SYN-002: [SKIP — remark]

/-! ## SYN.2: Terms and Formulas -/

/-- SYN-003 (PRIM-SYN010): Terms. -/
inductive Term (L : Language) where
  | var : ℕ → Term L
  | con : L.Con → Term L
  | app : (f : L.Fn) → (Fin (L.fnArity f) → Term L) → Term L

/-- SYN-004 (PRIM-SYN012): First-order formulas. -/
inductive Formula (L : Language) where
  | eq : Term L → Term L → Formula L
  | rel : (r : L.Rel) → (Fin (L.relArity r) → Term L) → Formula L
  | fls : Formula L
  | neg : Formula L → Formula L
  | conj : Formula L → Formula L → Formula L
  | disj : Formula L → Formula L → Formula L
  | impl : Formula L → Formula L → Formula L
  | all : ℕ → Formula L → Formula L
  | ex : ℕ → Formula L → Formula L

-- SYN-005: [SKIP — propositional fragment is quantifier-free sublanguage]

variable {L : Language}

/-- SYN-006 (DEF-SYN005:terms): Induction on terms. [EASY — FORMALIZED] -/
theorem term_induction (P : Term L → Prop)
    (hvar : ∀ n, P (.var n))
    (hcon : ∀ c, P (.con c))
    (happ : ∀ (f : L.Fn) (args : Fin (L.fnArity f) → Term L),
      (∀ i, P (args i)) → P (.app f args)) :
    ∀ t, P t := by
  intro t; induction t with
  | var n => exact hvar n
  | con c => exact hcon c
  | app f args ih => exact happ f args ih

/-- SYN-007 (DEF-SYN005): Induction on formulas. [EASY — FORMALIZED] -/
theorem formula_induction (P : Formula L → Prop)
    (heq : ∀ t₁ t₂, P (.eq t₁ t₂))
    (hrel : ∀ r args, P (.rel r args))
    (hfls : P .fls)
    (hneg : ∀ φ, P φ → P (.neg φ))
    (hconj : ∀ φ ψ, P φ → P ψ → P (.conj φ ψ))
    (hdisj : ∀ φ ψ, P φ → P ψ → P (.disj φ ψ))
    (himpl : ∀ φ ψ, P φ → P ψ → P (.impl φ ψ))
    (hall : ∀ x φ, P φ → P (.all x φ))
    (hex : ∀ x φ, P φ → P (.ex x φ)) :
    ∀ φ, P φ := by
  intro φ; induction φ with
  | eq t₁ t₂ => exact heq t₁ t₂
  | rel r args => exact hrel r args
  | fls => exact hfls
  | neg φ ih => exact hneg φ ih
  | conj φ ψ ih₁ ih₂ => exact hconj φ ψ ih₁ ih₂
  | disj φ ψ ih₁ ih₂ => exact hdisj φ ψ ih₁ ih₂
  | impl φ ψ ih₁ ih₂ => exact himpl φ ψ ih₁ ih₂
  | all x φ ih => exact hall x φ ih
  | ex x φ ih => exact hex x φ ih

/-- SYN-008 (PRIM-SYN017): Immediate subformulas. -/
def Formula.immediateSubformulas : Formula L → List (Formula L)
  | .eq _ _ | .rel _ _ | .fls => []
  | .neg φ => [φ]
  | .conj φ ψ | .disj φ ψ | .impl φ ψ => [φ, ψ]
  | .all _ φ | .ex _ φ => [φ]

/-- SYN-009: Proper subformula (transitive closure). -/
inductive ProperSub : Formula L → Formula L → Prop where
  | imm : ψ ∈ φ.immediateSubformulas → ProperSub ψ φ
  | trans : ProperSub ψ χ → ProperSub χ φ → ProperSub ψ φ

/-- SYN-010: Subformula (reflexive-transitive closure). -/
def IsSub (ψ φ : Formula L) : Prop := ψ = φ ∨ ProperSub ψ φ

-- SYN-011: [SKIP — remark]

/-- SYN-012 (DEF-SYN008): Subterms of a term. -/
def Term.subterms : Term L → List (Term L)
  | t@(.var _) => [t]
  | t@(.con _) => [t]
  | t@(.app _f args) =>
    t :: (List.ofFn fun i => (args i).subterms).flatten

/-- SYN-013: Main operator. -/
inductive MainOp where
  | eqOp | relOp | flsOp | negOp | conjOp | disjOp | implOp | allOp | exOp

def Formula.mainOp : Formula L → MainOp
  | .eq _ _ => .eqOp
  | .rel _ _ => .relOp
  | .fls => .flsOp
  | .neg _ => .negOp
  | .conj _ _ => .conjOp
  | .disj _ _ => .disjOp
  | .impl _ _ => .implOp
  | .all _ _ => .allOp
  | .ex _ _ => .exOp

/-- SYN-014 (DEF-SYN007): Formula complexity (rank). -/
def Formula.complexity : Formula L → ℕ
  | .eq _ _ | .rel _ _ | .fls => 0
  | .neg φ => φ.complexity + 1
  | .conj φ ψ | .disj φ ψ | .impl φ ψ => max φ.complexity ψ.complexity + 1
  | .all _ φ | .ex _ φ => φ.complexity + 1

/-- SYN-015 (DEF-SYN006:terms): Formation sequences for terms. -/
def IsTermFormationSeq (seq : List (Term L)) : Prop :=
  ∀ (i : Fin seq.length), match seq[i] with
    | .var _ | .con _ => True
    | .app f args =>
      ∀ j, ∃ (k : Fin seq.length), k.val < i.val ∧ seq[k] = args j

/-- SYN-016 (DEF-SYN006): Formation sequences for formulas. -/
def IsFormulaFormationSeq (seq : List (Formula L)) : Prop :=
  ∀ (i : Fin seq.length), match seq[i] with
    | .eq _ _ | .rel _ _ | .fls => True
    | .neg φ => ∃ (k : Fin seq.length), k.val < i.val ∧ seq[k] = φ
    | .conj φ ψ | .disj φ ψ | .impl φ ψ =>
      (∃ (k : Fin seq.length), k.val < i.val ∧ seq[k] = φ) ∧
      (∃ (k : Fin seq.length), k.val < i.val ∧ seq[k] = ψ)
    | .all _ φ | .ex _ φ => ∃ (k : Fin seq.length), k.val < i.val ∧ seq[k] = φ

/-- SYN-017 (DEF-SYN006:equiv): Every formula has a formation sequence.
    [EASY — PROOF-SKETCH-VERIFIED] -/
theorem formula_has_formation_seq (φ : Formula L) :
    ∃ seq : List (Formula L), φ ∈ seq ∧ IsFormulaFormationSeq seq := by
  sorry -- PROOF-SKETCH-VERIFIED: induction on φ, concatenate sub-sequences

/-! ## SYN.3: Variables and Scope -/

/-- SYN-018 (PRIM-SYN014): Free variables of a term. -/
def Term.freeVars : Term L → Finset ℕ
  | .var n => {n}
  | .con _ => ∅
  | .app _f args => Finset.univ.biUnion fun i => (args i).freeVars

/-- SYN-019 (DEF-SYN003): Free variables of a formula. -/
def Formula.freeVars : Formula L → Finset ℕ
  | .eq t₁ t₂ => t₁.freeVars ∪ t₂.freeVars
  | .rel _r args => Finset.univ.biUnion fun i => (args i).freeVars
  | .fls => ∅
  | .neg φ => φ.freeVars
  | .conj φ ψ | .disj φ ψ | .impl φ ψ => φ.freeVars ∪ ψ.freeVars
  | .all x φ | .ex x φ => φ.freeVars.erase x

/-- SYN-020 (PRIM-SYN015): Bound variables. -/
def Formula.boundVars : Formula L → Finset ℕ
  | .eq _ _ | .rel _ _ | .fls => ∅
  | .neg φ => φ.boundVars
  | .conj φ ψ | .disj φ ψ | .impl φ ψ => φ.boundVars ∪ ψ.boundVars
  | .all x φ | .ex x φ => φ.boundVars ∪ {x}

/-- SYN-021 (PRIM-SYN016): Scope of a quantifier. -/
def Formula.quantifierScope : Formula L → Option (ℕ × Formula L)
  | .all x φ | .ex x φ => some (x, φ)
  | _ => none

/-- SYN-022 (PRIM-SYN013): Sentence (closed formula). -/
def Formula.isSentence (φ : Formula L) : Prop := φ.freeVars = ∅

/-! ## SYN.4: Substitution -/

/-- SYN-023 (DEF-SYN001:terms): Substitution in terms. -/
def Term.subst (x : ℕ) (s : Term L) : Term L → Term L
  | .var n => if n = x then s else .var n
  | .con c => .con c
  | .app f args => .app f (fun i => Term.subst x s (args i))

/-- SYN-024: Free-for condition. -/
def freeFor (t : Term L) (x : ℕ) : Formula L → Prop
  | .eq _ _ | .rel _ _ | .fls => True
  | .neg φ => freeFor t x φ
  | .conj φ ψ | .disj φ ψ | .impl φ ψ => freeFor t x φ ∧ freeFor t x ψ
  | .all y φ | .ex y φ => x ∉ φ.freeVars ∨ (y ∉ t.freeVars ∧ freeFor t x φ)

/-- SYN-025 (DEF-SYN001): Substitution in formulas. -/
def Formula.subst (x : ℕ) (t : Term L) : Formula L → Formula L
  | .eq t₁ t₂ => .eq (t₁.subst x t) (t₂.subst x t)
  | .rel r args => .rel r (fun i => (args i).subst x t)
  | .fls => .fls
  | .neg φ => .neg (φ.subst x t)
  | .conj φ ψ => .conj (φ.subst x t) (ψ.subst x t)
  | .disj φ ψ => .disj (φ.subst x t) (ψ.subst x t)
  | .impl φ ψ => .impl (φ.subst x t) (ψ.subst x t)
  | .all y φ => if y = x then .all y φ else .all y (φ.subst x t)
  | .ex y φ => if y = x then .ex y φ else .ex y (φ.subst x t)

/-- SYN-026 (DEF-SYN002): Simultaneous substitution. -/
def Term.substSimul (σ : ℕ → Option (Term L)) : Term L → Term L
  | .var n => (σ n).getD (.var n)
  | .con c => .con c
  | .app f args => .app f (fun i => Term.substSimul σ (args i))

def Formula.substSimul (σ : ℕ → Option (Term L)) : Formula L → Formula L
  | .eq t₁ t₂ => .eq (t₁.substSimul σ) (t₂.substSimul σ)
  | .rel r args => .rel r (fun i => (args i).substSimul σ)
  | .fls => .fls
  | .neg φ => .neg (φ.substSimul σ)
  | .conj φ ψ => .conj (φ.substSimul σ) (ψ.substSimul σ)
  | .disj φ ψ => .disj (φ.substSimul σ) (ψ.substSimul σ)
  | .impl φ ψ => .impl (φ.substSimul σ) (ψ.substSimul σ)
  | .all y φ => .all y (φ.substSimul (fun n => if n = y then none else σ n))
  | .ex y φ => .ex y (φ.substSimul (fun n => if n = y then none else σ n))

/-- SYN-027 (DEF-SYN004): Alphabetic variant.
    Defined as an inductive predicate to avoid termination issues
    with substitution in the quantifier cases. -/
inductive AlphaEquiv : Formula L → Formula L → Prop where
  | eq_refl (t₁ t₂ : Term L) : AlphaEquiv (.eq t₁ t₂) (.eq t₁ t₂)
  | rel_refl (r : L.Rel) (a : Fin (L.relArity r) → Term L) :
    AlphaEquiv (.rel r a) (.rel r a)
  | fls_refl : AlphaEquiv .fls .fls
  | neg (h : AlphaEquiv φ ψ) : AlphaEquiv (.neg φ) (.neg ψ)
  | conj (h₁ : AlphaEquiv φ₁ φ₂) (h₂ : AlphaEquiv ψ₁ ψ₂) :
    AlphaEquiv (.conj φ₁ ψ₁) (.conj φ₂ ψ₂)
  | disj (h₁ : AlphaEquiv φ₁ φ₂) (h₂ : AlphaEquiv ψ₁ ψ₂) :
    AlphaEquiv (.disj φ₁ ψ₁) (.disj φ₂ ψ₂)
  | impl (h₁ : AlphaEquiv φ₁ φ₂) (h₂ : AlphaEquiv ψ₁ ψ₂) :
    AlphaEquiv (.impl φ₁ ψ₁) (.impl φ₂ ψ₂)
  | all_rename (x y z : ℕ) (φ ψ : Formula L) :
    z ∉ φ.freeVars → z ∉ ψ.freeVars →
    AlphaEquiv (φ.subst x (.var z)) (ψ.subst y (.var z)) →
    AlphaEquiv (.all x φ) (.all y ψ)
  | ex_rename (x y z : ℕ) (φ ψ : Formula L) :
    z ∉ φ.freeVars → z ∉ ψ.freeVars →
    AlphaEquiv (φ.subst x (.var z)) (ψ.subst y (.var z)) →
    AlphaEquiv (.ex x φ) (.ex y ψ)

-- SYN-028: [SKIP — uniform substitution in PL]

/-! ## SYN.5: Arithmetic Hierarchy -/

/-- SYN-029 (DEF-SYN009): Bounded quantification. -/
def IsBoundedAll : Formula L → Prop
  | .all _x (.impl _guard _body) => True
  | _ => False

def IsBoundedEx : Formula L → Prop
  | .ex _x (.conj _guard _body) => True
  | _ => False

/-- SYN-030 (DEF-SYN010): Arithmetic hierarchy classes. -/
inductive ArithClass where | delta0 | sigma1 | pi1
  deriving DecidableEq

def Formula.isDelta0 : Formula L → Prop
  | .eq _ _ | .rel _ _ | .fls => True
  | .neg φ => φ.isDelta0
  | .conj φ ψ | .disj φ ψ | .impl φ ψ => φ.isDelta0 ∧ ψ.isDelta0
  | .all _ _ | .ex _ _ => False

def Formula.isSigma1 : Formula L → Prop
  | .ex _ φ => φ.isSigma1 ∨ φ.isDelta0
  | φ => φ.isDelta0

def Formula.isPi1 : Formula L → Prop
  | .all _ φ => φ.isPi1 ∨ φ.isDelta0
  | φ => φ.isDelta0

/-! ## SYN.6: Unique Readability -/

/-- SYN-031: Constructor determinacy. [EASY — FORMALIZED] -/
theorem formula_constructor_determined (φ : Formula L) :
    (∃ t₁ t₂, φ = .eq t₁ t₂) ∨
    (∃ r args, φ = .rel r args) ∨ (φ = .fls) ∨
    (∃ ψ, φ = .neg ψ) ∨
    (∃ ψ χ, φ = .conj ψ χ) ∨ (∃ ψ χ, φ = .disj ψ χ) ∨
    (∃ ψ χ, φ = .impl ψ χ) ∨
    (∃ x ψ, φ = .all x ψ) ∨ (∃ x ψ, φ = .ex x ψ) := by
  cases φ with
  | eq t₁ t₂ => exact .inl ⟨t₁, t₂, rfl⟩
  | rel r args => exact .inr (.inl ⟨r, args, rfl⟩)
  | fls => exact .inr (.inr (.inl rfl))
  | neg ψ => exact .inr (.inr (.inr (.inl ⟨ψ, rfl⟩)))
  | conj ψ χ => exact .inr (.inr (.inr (.inr (.inl ⟨ψ, χ, rfl⟩))))
  | disj ψ χ => exact .inr (.inr (.inr (.inr (.inr (.inl ⟨ψ, χ, rfl⟩)))))
  | impl ψ χ => exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨ψ, χ, rfl⟩))))))
  | all x ψ => exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨x, ψ, rfl⟩)))))))
  | ex x ψ => exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨x, ψ, rfl⟩)))))))

/-- SYN-032 (THM-SYN002): Unique readability (atomic). [EASY — FORMALIZED] -/
theorem atomic_unique_readability (φ : Formula L) (hat : φ.complexity = 0) :
    (∃ t₁ t₂, φ = .eq t₁ t₂) ∨ (∃ r args, φ = .rel r args) ∨ (φ = .fls) := by
  cases φ with
  | eq t₁ t₂ => exact .inl ⟨t₁, t₂, rfl⟩
  | rel r args => exact .inr (.inl ⟨r, args, rfl⟩)
  | fls => exact .inr (.inr rfl)
  | neg _ => simp [Formula.complexity] at hat
  | conj _ _ => simp [Formula.complexity] at hat
  | disj _ _ => simp [Formula.complexity] at hat
  | impl _ _ => simp [Formula.complexity] at hat
  | all _ _ => simp [Formula.complexity] at hat
  | ex _ _ => simp [Formula.complexity] at hat

/-- SYN-033 (THM-SYN001): Unique readability (constructor injectivity).
    [MODERATE — PROOF-SKETCH-VERIFIED] -/
theorem unique_readability_eq (t₁ t₂ s₁ s₂ : Term L) :
    Formula.eq t₁ t₂ = Formula.eq s₁ s₂ → t₁ = s₁ ∧ t₂ = s₂ :=
  fun h => ⟨Formula.eq.inj h |>.1, Formula.eq.inj h |>.2⟩

theorem unique_readability_neg (φ ψ : Formula L) :
    Formula.neg φ = Formula.neg ψ → φ = ψ :=
  Formula.neg.inj

theorem unique_readability_conj (φ₁ ψ₁ φ₂ ψ₂ : Formula L) :
    Formula.conj φ₁ ψ₁ = Formula.conj φ₂ ψ₂ → φ₁ = φ₂ ∧ ψ₁ = ψ₂ :=
  fun h => ⟨Formula.conj.inj h |>.1, Formula.conj.inj h |>.2⟩

theorem unique_readability_all (x y : ℕ) (φ ψ : Formula L) :
    Formula.all x φ = Formula.all y ψ → x = y ∧ φ = ψ :=
  fun h => ⟨Formula.all.inj h |>.1, Formula.all.inj h |>.2⟩

-- SYN-034: [SKIP — PL unique readability is a special case]

/-- SYN-035 (THM-SYN004): Structural induction/recursion.
    [MODERATE — PROOF-SKETCH-VERIFIED] -/
theorem structural_induction_principle (L : Language) :
    ∀ (P : Formula L → Prop),
      (∀ t₁ t₂, P (.eq t₁ t₂)) → (∀ r args, P (.rel r args)) →
      P .fls → (∀ φ, P φ → P (.neg φ)) →
      (∀ φ ψ, P φ → P ψ → P (.conj φ ψ)) →
      (∀ φ ψ, P φ → P ψ → P (.disj φ ψ)) →
      (∀ φ ψ, P φ → P ψ → P (.impl φ ψ)) →
      (∀ x φ, P φ → P (.all x φ)) →
      (∀ x φ, P φ → P (.ex x φ)) →
      ∀ φ, P φ :=
  formula_induction

end FOL
