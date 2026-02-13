/-
  LeanVerify/BST.lean
  CH-BST: Set-Theoretic Background (Level-0)

  64 registry items (BST-001 through BST-064).
  Strategy: TRIVIAL items map to mathlib definitions via abbrev/alias;
  EASY/MODERATE items get full proofs; REFERENCE items cite mathlib theorems.

  Follows REGISTRY.md classification:
    50 TRIVIAL (DEFINITION-CHECKED)
     6 EASY (FORMALIZED / PROOF-SKETCH-VERIFIED)
     3 MODERATE (FORMALIZED / PROOF-SKETCH-VERIFIED)
     4 REFERENCE (mathlib correspondence)
     1 SKIP (remark, no formal content)
-/

import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Data.Nat.Pairing
import Mathlib.SetTheory.Cardinal.SchroederBernstein
import Mathlib.Data.Set.Countable

namespace BST

/-! ## BST.1: Sets and Membership -/

/-- BST-001 (PRIM-BST001): Extensionality.
    Two sets are equal iff they have the same elements.
    mathlib: `Set.ext_iff`. -/
theorem extensionality {α : Type*} (A B : Set α) :
    A = B ↔ ∀ x, x ∈ A ↔ x ∈ B :=
  Set.ext_iff

/-- BST-002 (PRIM-BST003): Subset.
    A ⊆ B iff every element of A is in B.
    mathlib: `Set.Subset`. -/
abbrev Subset {α : Type*} (A B : Set α) : Prop := A ⊆ B

/-- BST-003 (PRIM-BST001:subset-char): Subset characterization.
    A ⊆ B iff A ∩ B = A.   [EASY — FORMALIZED] -/
theorem subset_iff_inter_eq {α : Type*} (A B : Set α) :
    A ⊆ B ↔ A ∩ B = A := by
  constructor
  · intro h; ext x; exact ⟨fun ⟨ha, _⟩ => ha, fun ha => ⟨ha, h ha⟩⟩
  · intro h x hx
    have hmem : x ∈ A ∩ B := by rw [h]; exact hx
    exact hmem.2

/-- BST-004 (PRIM-BST015): Power set.
    𝒫(A) = {B | B ⊆ A}.
    mathlib: `Set.powerset`. -/
abbrev PowerSet {α : Type*} (A : Set α) : Set (Set α) := 𝒫 A

/-- BST-005 (PRIM-BST005): Union.
    A ∪ B = {x | x ∈ A ∨ x ∈ B}.
    mathlib: `Set.union`. -/
abbrev Union {α : Type*} (A B : Set α) : Set α := A ∪ B

/-- BST-006: Intersection.
    A ∩ B = {x | x ∈ A ∧ x ∈ B}.
    mathlib: `Set.inter`. -/
abbrev Inter {α : Type*} (A B : Set α) : Set α := A ∩ B

/-- BST-007: General union.
    ⋃₀ 𝒜 = {x | ∃ A ∈ 𝒜, x ∈ A}.
    mathlib: `Set.sUnion`. -/
abbrev GeneralUnion {α : Type*} (𝒜 : Set (Set α)) : Set α := ⋃₀ 𝒜

/-- BST-008: General intersection.
    ⋂₀ 𝒜 = {x | ∀ A ∈ 𝒜, x ∈ A}.
    mathlib: `Set.sInter`. -/
abbrev GeneralInter {α : Type*} (𝒜 : Set (Set α)) : Set α := ⋂₀ 𝒜

/-- BST-009 (PRIM-BST006): Ordered pair.
    mathlib: `Prod`. -/
abbrev OrderedPair (α β : Type*) := α × β

/-- BST-010 (PRIM-BST007): Cartesian product of sets.
    A ×ˢ B = {(a,b) | a ∈ A ∧ b ∈ B}.
    mathlib: `Set.prod`. -/
abbrev CartesianProd {α β : Type*} (A : Set α) (B : Set β) : Set (α × β) := A ×ˢ B

/-- BST-011 (PRIM-BST012): Natural numbers.
    mathlib: `ℕ`. -/
abbrev NatNumbers := ℕ

/-! ## BST.2: Relations -/

/-- BST-012 (PRIM-BST008): Binary relation on α.
    A binary relation on α is a subset of α × α, or equivalently α → α → Prop. -/
abbrev BinRel (α : Type*) := α → α → Prop

/-- BST-013: Reflexive relation.
    mathlib: `Reflexive`. -/
abbrev IsReflexive {α : Type*} (R : BinRel α) : Prop := Reflexive R

/-- BST-014: Transitive relation.
    mathlib: `Transitive`. -/
abbrev IsTransitive {α : Type*} (R : BinRel α) : Prop := Transitive R

/-- BST-015: Symmetric relation.
    mathlib: `Symmetric`. -/
abbrev IsSymmetric {α : Type*} (R : BinRel α) : Prop := Symmetric R

/-- BST-016: Anti-symmetric relation.
    R is anti-symmetric iff R(a,b) ∧ R(b,a) → a = b. -/
abbrev IsAntiSymm {α : Type*} (R : BinRel α) : Prop := ∀ a b, R a b → R b a → a = b

/-- BST-017: Connected (total) relation.
    For all a b, R(a,b) ∨ R(b,a). -/
def IsConnected {α : Type*} (R : BinRel α) : Prop := ∀ a b, R a b ∨ R b a

/-- BST-018: Irreflexive relation.
    mathlib: `Irreflexive`. -/
abbrev IsIrrefl {α : Type*} (R : BinRel α) : Prop := Irreflexive R

/-- BST-019: Asymmetric relation.
    R is asymmetric iff R(a,b) → ¬R(b,a). -/
def IsAsymmetric {α : Type*} (R : BinRel α) : Prop := ∀ a b, R a b → ¬ R b a

/-- BST-020 (DEF-BST004): Equivalence relation.
    Reflexive, symmetric, transitive.
    mathlib: `Equivalence`. -/
abbrev EquivRel {α : Type*} (R : BinRel α) : Prop := Equivalence R

/-- BST-021: Equivalence class.
    [a]_R = {b | R(a,b)}.
    mathlib: `Quotient`, `Setoid.classes`. -/
def EquivClass {α : Type*} (R : BinRel α) (a : α) : Set α := {b | R a b}

/-- BST-022 (DEF-BST004:partition): Equivalence classes partition the domain.
    [MODERATE — FORMALIZED]
    If R is an equivalence relation on α, then:
    (1) Every element belongs to its own class,
    (2) Two classes are either equal or disjoint,
    (3) The union of all classes is the whole type. -/
theorem equiv_classes_partition {α : Type*} {R : BinRel α} (hR : Equivalence R) :
    (∀ a, a ∈ EquivClass R a) ∧
    (∀ a b, EquivClass R a = EquivClass R b ∨
            EquivClass R a ∩ EquivClass R b = ∅) ∧
    (∀ x, ∃ a, x ∈ EquivClass R a) := by
  refine ⟨fun a => hR.1 a, fun a b => ?_, fun x => ⟨x, hR.1 x⟩⟩
  by_cases h : ∃ c, c ∈ EquivClass R a ∧ c ∈ EquivClass R b
  · left; obtain ⟨c, hca, hcb⟩ := h
    -- hca : c ∈ EquivClass R a, i.e., R a c
    -- hcb : c ∈ EquivClass R b, i.e., R b c
    ext x; simp only [EquivClass, Set.mem_setOf_eq]; constructor
    · -- R a x → R b x
      intro hxa
      exact hR.3 (hR.3 (show R b c from hcb) (hR.2 (show R a c from hca))) hxa
    · -- R b x → R a x
      intro hxb
      exact hR.3 (hR.3 (show R a c from hca) (hR.2 (show R b c from hcb))) hxb
  · right
    push_neg at h
    ext x; simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    exact fun ⟨ha, hb⟩ => h x ha hb

/-- BST-023: Preorder.
    Reflexive + transitive.
    mathlib: `Preorder`. -/
def IsPreorder' {α : Type*} (R : BinRel α) : Prop := Reflexive R ∧ Transitive R

/-- BST-024 (DEF-BST005): Partial order.
    Reflexive + anti-symmetric + transitive.
    mathlib: `PartialOrder`. -/
example : PartialOrder ℕ := inferInstance

/-- BST-025: Linear (total) order.
    Partial order with totality.
    mathlib: `LinearOrder`. -/
example : LinearOrder ℕ := inferInstance

/-- BST-026: Strict order.
    Irreflexive + transitive.
    mathlib: `IsStrictOrder`. -/
example : IsStrictOrder ℕ (· < ·) := inferInstance

/-- BST-027: Strict linear order.
    Strict order + trichotomy.
    mathlib: `IsStrictTotalOrder`. -/
example : IsStrictTotalOrder ℕ (· < ·) := inferInstance

/-- BST-028 (prop:stricttopartial): Every strict order induces a partial order.
    [EASY — PROOF-SKETCH-VERIFIED]
    Given strict order <, define a ≤ b ↔ a < b ∨ a = b. -/
theorem strict_order_induces_partial {α : Type*} {R : BinRel α}
    (hirr : Irreflexive R) (htrans : Transitive R) :
    let R' := fun a b => R a b ∨ a = b
    (Reflexive R') ∧ (∀ a b, R' a b → R' b a → a = b) ∧ (Transitive R') := by
  refine ⟨fun a => Or.inr rfl, fun a b hab hba => ?_, fun a b c hab hbc => ?_⟩
  · rcases hab with h | h
    · rcases hba with h' | h'
      · exact absurd (htrans h h') (hirr a)
      · exact h'.symm
    · exact h
  · rcases hab with h | h <;> rcases hbc with h' | h'
    · exact Or.inl (htrans h h')
    · exact h' ▸ Or.inl h
    · exact h ▸ Or.inl h'
    · exact Or.inr (h.trans h')

/-- BST-029: Tree (as a prefix-closed set of finite sequences).
    We model trees as sets of lists closed under prefix. -/
def IsTree {α : Type*} (T : Set (List α)) : Prop :=
  ∀ s, s ∈ T → ∀ t, t <+: s → t ∈ T

/-- BST-030: Successors in a tree.
    The successors of node s are {s ++ [a] | s ++ [a] ∈ T}. -/
def Successors {α : Type*} (T : Set (List α)) (s : List α) : Set α :=
  {a | s ++ [a] ∈ T}

/-- BST-031: Branch (maximal path) in a tree.
    A branch is a maximal chain through the tree. -/
def IsBranch {α : Type*} (T : Set (List α)) (f : ℕ → List α) : Prop :=
  (∀ n, f n ∈ T) ∧ (∀ n, f n <+: f (n + 1)) ∧
  (∀ n, (f (n + 1)).length = (f n).length + 1)

/-- BST-032: Operations on relations (composition, inverse).
    mathlib: `Relation.Comp`, `Function.swap`. -/
def RelComp {α : Type*} (R S : BinRel α) : BinRel α :=
  fun a c => ∃ b, R a b ∧ S b c

def RelInverse {α : Type*} (R : BinRel α) : BinRel α :=
  fun a b => R b a

/-- BST-033: Transitive closure.
    mathlib: `Relation.TransGen`. -/
abbrev TransClosure {α : Type*} (R : BinRel α) := Relation.TransGen R

/-! ## BST.3: Functions -/

-- BST-034 (PRIM-BST009): Function.
-- Functions are primitive in Lean's type theory (α → β).

/-- BST-035 (DEF-BST002): Surjective function.
    mathlib: `Function.Surjective`. -/
abbrev Surjective {α β : Type*} (f : α → β) : Prop := Function.Surjective f

/-- BST-036 (DEF-BST001): Injective function.
    mathlib: `Function.Injective`. -/
abbrev Injective {α β : Type*} (f : α → β) : Prop := Function.Injective f

/-- BST-037 (DEF-BST003): Bijection.
    mathlib: `Function.Bijective`. -/
abbrev Bijective {α β : Type*} (f : α → β) : Prop := Function.Bijective f

/-- BST-038: Inverse function.
    mathlib: `Function.invFun`. -/
noncomputable abbrev InverseFunc {α β : Type*} [Nonempty α] (f : α → β) : β → α :=
  Function.invFun f

/-- BST-039 (prop:inj-left-inv): Injective ⟹ has left inverse.
    [EASY — PROOF-SKETCH-VERIFIED] -/
theorem inj_has_left_inverse {α β : Type*} [Nonempty α] {f : α → β}
    (hinj : Function.Injective f) :
    ∃ g : β → α, g ∘ f = id :=
  ⟨Function.invFun f, funext fun x => hinj (Function.invFun_eq ⟨x, rfl⟩)⟩

/-- BST-040 (prop:surj-right-inv): Surjective ⟹ has right inverse (requires choice).
    [EASY — FORMALIZED] -/
theorem surj_has_right_inverse {α β : Type*} {f : α → β}
    (hsurj : Function.Surjective f) :
    ∃ g : β → α, f ∘ g = id :=
  ⟨Function.surjInv hsurj, funext fun y => Function.surjInv_eq hsurj y⟩

/-- BST-041 (prop:bijection-inverse): Bijection has a two-sided inverse.
    [EASY — PROOF-SKETCH-VERIFIED] -/
theorem bij_has_inverse {α β : Type*} [Nonempty α] {f : α → β}
    (hbij : Function.Bijective f) :
    ∃ g : β → α, (g ∘ f = id) ∧ (f ∘ g = id) := by
  refine ⟨Function.invFun f, ?_, ?_⟩
  · exact funext fun x => hbij.1 (Function.invFun_eq ⟨x, rfl⟩)
  · exact funext fun y => Function.invFun_eq (hbij.2 y)

/-- BST-042: Composition.
    mathlib: `Function.comp`. -/
abbrev Comp {α β γ : Type*} (g : β → γ) (f : α → β) : α → γ := g ∘ f

/-- BST-043: Graph of a function.
    Graph(f) = {(x, f(x)) | x ∈ α}. -/
def Graph {α β : Type*} (f : α → β) : Set (α × β) := {p | p.2 = f p.1}

/-! ## BST.4: Sequences and Numbers -/

/-- BST-044 (PRIM-BST010): Finite sequences (words).
    We model as `List α`.
    mathlib: `List`. -/
abbrev FinSeq (α : Type*) := List α

/-- BST-045 (PRIM-BST011): Infinite sequences.
    ℕ → α.
    mathlib: built-in function type. -/
abbrev InfSeq (α : Type*) := ℕ → α

/-! ## BST.5: Induction and Recursion -/

/-- BST-046 (PRIM-BST013): Mathematical induction.
    mathlib: `Nat.rec`. The principle is built into Lean's type theory. -/
theorem nat_induction (P : ℕ → Prop) (h0 : P 0) (hs : ∀ n, P n → P (n + 1)) :
    ∀ n, P n :=
  Nat.rec h0 hs

-- BST-047: Set-theoretic justification of induction. [SKIP — remark, no formal content]

-- BST-048 (PRIM-BST014): Structural induction on formulas.
-- Built into Lean's inductive type mechanism.
-- The induction principle is automatically generated for any `inductive` type.
-- Formalized concretely in Syntax.lean for PropLogic.Formula.

/-- BST-049 (DEF-BST006): Closure of a set under operations.
    Cl_F(A) is the smallest set containing A and closed under operations in F. -/
def Closure {α : Type*} (A : Set α) (F : Set (α → α)) : Set α :=
  ⋂₀ {S | A ⊆ S ∧ ∀ f ∈ F, ∀ x ∈ S, f x ∈ S}

theorem closure_contains_base {α : Type*} (A : Set α) (F : Set (α → α)) :
    A ⊆ Closure A F :=
  fun _ hx => Set.mem_sInter.mpr (fun _ hS => hS.1 hx)

theorem closure_closed {α : Type*} (A : Set α) (F : Set (α → α))
    (f : α → α) (hf : f ∈ F) (x : α) (hx : x ∈ Closure A F) :
    f x ∈ Closure A F :=
  Set.mem_sInter.mpr (fun _ hS => hS.2 f hf x (Set.mem_sInter.mp hx _ hS))

/-- BST-050 (DEF-BST007): Dedekind algebra.
    A triple (N, 0, S) where N is a set, 0 ∈ N, S : N → N is injective,
    0 ∉ range(S), and N is the closure of {0} under S.
    mathlib models this via ℕ directly. -/
structure DedekindAlgebra where
  carrier : Type*
  zero : carrier
  succ : carrier → carrier
  succ_inj : Function.Injective succ
  zero_not_succ : ∀ n, succ n ≠ zero
  induction : ∀ (P : carrier → Prop), P zero → (∀ n, P n → P (succ n)) → ∀ n, P n

/-- ℕ is a Dedekind algebra. -/
noncomputable def natDedekind : DedekindAlgebra where
  carrier := ℕ
  zero := 0
  succ := Nat.succ
  succ_inj := Nat.succ_injective
  zero_not_succ := fun n => Nat.succ_ne_zero n
  induction := fun _P h0 hs => Nat.rec h0 hs

/-! ## BST.6: Cardinality -/

/-- BST-051: Enumeration.
    An enumeration of A is a surjection ℕ → A (or a listing a₀, a₁, ...). -/
def IsEnumeration {α : Type*} (f : ℕ → α) (A : Set α) : Prop :=
  ∀ a ∈ A, ∃ n, f n = a

/-- BST-052 (PRIM-BST016): Enumerable (countable) set.
    mathlib: `Set.Countable`. -/
abbrev Enumerable {α : Type*} (A : Set α) : Prop := A.Countable

/-- BST-053 (THM-BST002): ℕ is enumerable.
    [REFERENCE — `Set.countable_univ` in mathlib] -/
theorem nat_enumerable : (Set.univ : Set ℕ).Countable :=
  Set.countable_univ

/-- BST-054 (THM-BST003): ℕ × ℕ is enumerable.
    [REFERENCE — `Set.countable_univ` for `ℕ × ℕ`] -/
theorem nat_prod_enumerable : (Set.univ : Set (ℕ × ℕ)).Countable :=
  Set.countable_univ

/-- BST-055: A subset of an enumerable set is enumerable.
    [EASY — FORMALIZED] -/
theorem subset_of_enumerable {α : Type*} {A B : Set α}
    (hAB : A ⊆ B) (hB : B.Countable) : A.Countable :=
  hB.mono hAB

/-- BST-056: Pairing function.
    mathlib: `Nat.pair`. -/
abbrev PairingFun := Nat.pair

/-- BST-057 (thm:nonenum-bin-omega): {0,1}^ℕ is non-enumerable.
    [MODERATE — FORMALIZED]
    Cantor diagonalization: no surjection ℕ → (ℕ → Bool). -/
theorem bin_omega_non_enumerable :
    ¬ ∃ f : ℕ → (ℕ → Bool), Function.Surjective f := by
  intro ⟨f, hsurj⟩
  let g : ℕ → Bool := fun n => !(f n n)
  obtain ⟨m, hm⟩ := hsurj g
  have h1 : f m m = g m := congr_fun hm m
  have h2 : g m = !(f m m) := rfl
  rw [h2] at h1
  cases f m m <;> simp at h1

/-- BST-058 (thm:nonenum-pownat): 𝒫(ℕ) is non-enumerable.
    [MODERATE — PROOF-SKETCH-VERIFIED]
    Cantor diagonalization: no surjection ℕ → Set ℕ. -/
theorem pow_nat_non_enumerable :
    ¬ ∃ f : ℕ → Set ℕ, Function.Surjective f := by
  intro ⟨f, hsurj⟩
  exact Function.cantor_surjective f hsurj

/-- BST-059 (DEF-BST009): Equinumerosity.
    A ≈ B iff there exists a bijection A → B.
    mathlib: `Cardinal.mk`. -/
def Equinumerous (α β : Type*) : Prop := Nonempty (α ≃ β)

/-- BST-060 (DEF-BST008): Dedekind infinite.
    A set is Dedekind infinite iff there is an injection from it to a proper subset,
    i.e., it is equinumerous with a proper subset of itself. -/
def DedekindInfinite (α : Type*) : Prop :=
  ∃ f : α → α, Function.Injective f ∧ ¬ Function.Surjective f

/-- BST-061: Size comparison by injection.
    |A| ≤ |B| iff there exists an injection A → B.
    mathlib: `Cardinal.mk_le_mk_iff_exists_injective` (approximately). -/
def SizeLE (α β : Type*) : Prop := Nonempty (α ↪ β)

/-- BST-062: Strict size comparison.
    |A| < |B| iff |A| ≤ |B| and ¬|B| ≤ |A|. -/
def SizeLT (α β : Type*) : Prop := SizeLE α β ∧ ¬ SizeLE β α

/-- BST-063 (THM-BST001): Cantor's Theorem.
    |A| < |𝒫(A)| — no surjection from A to its power set.
    [REFERENCE — `Function.cantor_surjective` in mathlib] -/
theorem cantor {α : Type*} (f : α → Set α) : ¬ Function.Surjective f :=
  Function.cantor_surjective f

/-- BST-064 (thm:schroder-bernstein): Schröder-Bernstein theorem.
    If |A| ≤ |B| and |B| ≤ |A| then |A| = |B|.
    [REFERENCE — `Function.Embedding.antisymm` in mathlib] -/
theorem schroder_bernstein {α β : Type*}
    (f : α ↪ β) (g : β ↪ α) : Nonempty (α ≃ β) :=
  f.antisymm g

end BST
