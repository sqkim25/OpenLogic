## CH-DED: Deduction

---

### Chapter: proof-systems

### fol/prf/int — Introduction
- **Action**: CUT
- **Lean Chapter**: CH-DED
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. No formal definitions or theorems introduced. Purely motivational narrative explaining the goals of derivation systems and the soundness/completeness connection. The lean text's DED.1 generic section will provide a one-paragraph framing replacing this.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: N/A (no formal items)
  - Prose: cut all -- replaced by DED.1 intro paragraph
  - Examples: cut all
  - Proofs: N/A

---

### fol/prf/axd — Axiomatic Derivation (proof-systems overview)
- **Action**: CONDENSE
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.2: Axiomatic (Hilbert) Systems
- **Rationale**: Signal is CORE-DEF for Hilbert systems, but content is a discursive survey rather than formal specification. The formal definitions of DEF-DED005, AX-DED001, AX-DED003 live in fol/axd/prp and fol/axd/rul. This section contributes a useful high-level framing paragraph and one worked derivation example for DED.2.
- **Content Directives**:
  - Formal items to preserve: one-paragraph characterization of Hilbert systems (linear sequence, axiom schemas + few rules)
  - Formal items to drop: worked derivation example (redundant with fol/axd/pro examples, but keep one sentence summarizing it)
  - Prose: compress to 2-3 sentence overview for DED.2 preamble; cut historical notes (Frege, Russell, Hilbert)
  - Examples: cut all -- pedagogical illustration
  - Proofs: N/A

---

### fol/prf/ntd — Natural Deduction (proof-systems overview)
- **Action**: CONDENSE
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.3: Natural Deduction
- **Rationale**: Signal is CORE-DEF for ND systems, but content is a discursive survey. Formal definitions of DEF-DED006, PRIM-DED009 live in fol/ntd/rul, fol/ntd/prl. This section contributes a useful high-level framing paragraph for DED.3.
- **Content Directives**:
  - Formal items to preserve: one-paragraph characterization of ND (tree-structured, intro/elim rules, assumption discharge)
  - Formal items to drop: worked derivation example (redundant)
  - Prose: compress to 2-3 sentence overview for DED.3 preamble; cut historical notes (Gentzen, Jaskowski, Prawitz, Fitch)
  - Examples: cut all
  - Proofs: N/A

---

### fol/prf/seq — The Sequent Calculus (proof-systems overview)
- **Action**: CUT
- **Lean Chapter**: CH-DED
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL (REDUNDANT-WITH: fol/seq chapter). Everything here is covered more formally in fol/seq/rul, fol/seq/prl, fol/seq/srl. The DED.4 preamble will be sourced from the condensed fol/prf/ntd-style overview, but actually fol/seq/rul already has a clean sequent definition. No unique content.
- **Content Directives**:
  - Formal items to preserve: none -- all covered in fol/seq/*
  - Formal items to drop: all explain blocks -- redundant
  - Prose: cut all
  - Examples: cut all -- worked derivation example redundant with fol/seq/pro
  - Proofs: N/A

---

### fol/prf/tab — Tableaux (proof-systems overview)
- **Action**: CUT
- **Lean Chapter**: CH-DED
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL (REDUNDANT-WITH: fol/tab chapter). Everything here is covered more formally in fol/tab/rul, fol/tab/prl. No unique formal content.
- **Content Directives**:
  - Formal items to preserve: none -- all covered in fol/tab/*
  - Formal items to drop: all explain blocks -- redundant
  - Prose: cut all
  - Examples: cut all
  - Proofs: N/A

---

### Chapter: axiomatic-deduction

### fol/axd/rul — Rules and Derivation
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (authoritative for PRIM-DED001, PRIM-DED002)
- **Rationale**: Signal is CORE-DEF. Authoritative defining occurrence of PRIM-DED001 (Rule of Inference) and PRIM-DED005 (Derivation) at the generic level. Contains two defn blocks (derivation, rule of inference) plus the derived definitions of derivability and theorem. By A1 decision, the generic definitions from this section become DED.1 content; the axiomatic-specific instantiation (sequence-based derivation) goes to DED.2.
- **Content Directives**:
  - Formal items to preserve: `defn[Derivability]` (generic derivation definition -- PRIM-DED005); `defn[Rule of inference]` (PRIM-DED001); second `defn[Derivability]` (provability relation Gamma |- A); `defn[Theorems]` (PRIM-DED010)
  - Formal items to drop: modus ponens informal example in explain block -- moves to DED.2 as instantiation
  - Prose: split into two: (a) DED.1 gets the abstract framing (derivation as structured object, rule of inference as pattern); (b) DED.2 gets the Hilbert instantiation (derivation as finite sequence)
  - Examples: cut all -- the modus ponens example is pedagogical
  - Proofs: N/A

---

### fol/axd/prp — Axioms and Rules for Propositional Connectives
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.2: Axiomatic (Hilbert) Systems
- **Rationale**: Signal is CORE-DEF. Sole defining occurrence of AX-DED003 (Logical Axiom Schemas, propositional part), AX-DED001 (Modus Ponens), and DEF-DED005 (Hilbert-Style Proof System). Specifies the 14 propositional axiom schemas and the MP rule. Essential system specification for DED.2.
- **Content Directives**:
  - Formal items to preserve: all 14 axiom schema definitions (AX-DED003 propositional fragment); `defn[Modus ponens]` (AX-DED001)
  - Formal items to drop: none -- all are essential system specification
  - Prose: compress to intro + definitions only
  - Examples: cut all
  - Proofs: N/A

---

### fol/axd/qua — Axioms and Rules for Quantifiers
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.2: Axiomatic (Hilbert) Systems
- **Rationale**: Signal is CORE-DEF. Sole defining occurrence of AX-DED003 (quantifier axiom schemas) and AX-DED002 (Universal Generalization / QR rule). Completes the specification of the Hilbert system for FOL.
- **Content Directives**:
  - Formal items to preserve: quantifier axiom schemas (Q1, Q2); `defn[Rules for quantifiers]` (QR / AX-DED002)
  - Formal items to drop: none
  - Prose: compress to intro + definitions only
  - Examples: cut all
  - Proofs: N/A

---

### fol/axd/ptn — Proof-Theoretic Notions (Axiomatic)
- **Action**: ABSORB:fol/ntd/ptn,fol/seq/ptn,fol/tab/ptn
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (authoritative for PRIM-DED003, PRIM-DED004, DEF-DED001)
- **Rationale**: Signal is CORE-DEF. By A1 decision, this section becomes the authoritative home for the generic proof-theoretic notions: Provability (PRIM-DED003/006), Theorem (PRIM-DED010), Consistency (DEF-DED001), and the 5 structural properties (reflexivity, monotonicity, transitivity, inconsistency characterization, compactness). The 3 parallel ptn sections (NTD, SC, Tab) all define identical concepts with system-specific proof details. This section absorbs them: the generic definitions go to DED.1; system-specific proof sketches are noted as remarks in DED.2-5.
- **Content Directives**:
  - Formal items to preserve: `defn[Derivability]` (PRIM-DED006); `defn[Theorems]` (PRIM-DED010); `defn[Consistency]` (DEF-DED001); `prop[Reflexivity]` with proof; `prop[Monotonicity]` with proof; `prop[Transitivity]` with proof; `prop[incons]` (statement); `prop[Compactness]` with proof
  - Formal items to drop: exercises (prob blocks) -- pedagogical
  - Prose: generalize away from axiomatic-specific language; replace "derivation" with proof-system-neutral language where needed; add remark noting that each proof system instantiates these properties (the proof of transitivity differs: AXD uses sequence concatenation, NTD uses implication-intro + elim, SC uses cut, Tab uses cut rule)
  - Examples: cut all
  - Proofs: preserve full for reflexivity, monotonicity (trivial); preserve full for transitivity (using the AXD proof as template, noting variants); preserve full for compactness; cut inconsistency characterization proof (exercise)

---

### fol/axd/ded — Deduction Theorem
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.2: Axiomatic (Hilbert) Systems
- **Rationale**: Signal is CORE-THM. Sole defining occurrence of THM-DED001 (Deduction Theorem) and CP-009 (Deduction Theorem as composition pattern). Central metatheorem for the Hilbert system. This is specific to DED.2 (ND and SC do not need a separate deduction theorem -- it is built into the system design).
- **Content Directives**:
  - Formal items to preserve: `prop[mp]` (meta-MP -- AX-DED001 at meta-level); `thm[deduction-thm]` (THM-DED001 / CP-009) with full proof
  - Formal items to drop: `prop[derivfacts]` -- OL-ONLY derived facts (contraposition, explosion, DNE); these are exercises and not taxonomy items
  - Prose: compress intro; preserve the remark about why axioms lif1 and lif2 were chosen to make the Deduction Theorem work
  - Examples: cut all
  - Proofs: preserve full -- the induction on derivation length is the canonical proof of THM-DED001

---

### fol/axd/ddq — Deduction Theorem with Quantifiers
- **Action**: MERGE-INTO:fol/axd/ded
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.2: Axiomatic (Hilbert) Systems
- **Rationale**: Signal is STEPPING-STONE. Extends THM-DED001 to handle the QR rule. The lean text should present the full FOL version of the Deduction Theorem in one place. The additional QR case is a straightforward extension of the inductive proof.
- **Content Directives**:
  - Formal items to preserve: `thm[deduction-thm-q]` -- statement of the FOL extension (merge as additional case in fol/axd/ded's proof)
  - Formal items to drop: none
  - Prose: replace with cross-ref to extended proof in fol/axd/ded
  - Examples: cut all
  - Proofs: merge the QR case into fol/axd/ded's proof as an additional inductive case

---

### fol/axd/prv — Derivability and Consistency (Axiomatic)
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (authoritative for consistency properties)
- **Rationale**: Signal is STEPPING-STONE. Contains 4 propositions about the derivability/consistency relationship needed for completeness. By A1, these are generic results (they hold for all 4 proof systems). This section is authoritative; the 3 parallel prv sections (NTD, SC, Tab) merge into it.
- **Content Directives**:
  - Formal items to preserve: `prop[provability-contr]` with proof; `prop[prov-incons]` with proof; `prop[explicit-inc]` with proof; `prop[provability-exhaustive]` (statement)
  - Formal items to drop: exercises (prob blocks)
  - Prose: generalize language to be proof-system-neutral; note that proofs use the Deduction Theorem (which in ND is built-in, in SC uses cut)
  - Examples: cut all
  - Proofs: preserve full for provability-contr, prov-incons, explicit-inc; cut exhaustive (exercise)

---

### fol/axd/ppr — Derivability and Propositional Connectives (Axiomatic)
- **Action**: CONDENSE
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.2: Axiomatic (Hilbert) Systems
- **Rationale**: Signal is STEPPING-STONE. Establishes derivability facts for connectives needed for completeness. These are system-specific technical results (they use the specific Hilbert axioms). The generic results (that each system can derive these) follow from equivalence of proof systems. Keep statements, condense proofs to sketches.
- **Content Directives**:
  - Formal items to preserve: `prop[provability-land]` (statement); `prop[provability-lor]` (statement); `prop[provability-lif]` (statement)
  - Formal items to drop: none
  - Prose: compress to statements + one-line proof sketch each
  - Examples: cut all
  - Proofs: preserve sketch only -- each uses axiom schemas + Deduction Theorem + meta-MP

---

### fol/axd/qpr — Derivability and Quantifiers (Axiomatic)
- **Action**: CONDENSE
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.2: Axiomatic (Hilbert) Systems
- **Rationale**: Signal is STEPPING-STONE. Establishes quantifier derivability facts needed for completeness. FOL-only. System-specific proofs using QR and quantifier axioms.
- **Content Directives**:
  - Formal items to preserve: `thm[strong-generalization]` (statement); `prop[provability-quantifiers]` (statement)
  - Formal items to drop: none
  - Prose: compress to statements + one-line proof sketch each
  - Examples: cut all
  - Proofs: preserve sketch only

---

### fol/axd/sou — Soundness (Axiomatic)
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.2: Axiomatic (Hilbert) Systems
- **Rationale**: Signal is CORE-THM. Introduces CP-001 (Soundness Theorem) for the Hilbert system. Per architectural decision, each proof system's soundness proof stays in its own DED.2-5 section. The Hilbert soundness proof is the simplest (induction on derivation length with only MP and QR cases).
- **Content Directives**:
  - Formal items to preserve: `prop` (axioms are valid -- stepping stone); `thm[soundness]` (CP-001: Gamma |- A implies Gamma |= A) with full proof; `cor[weak-soundness]`; `cor[consistency-soundness]` with proof
  - Formal items to drop: exercises (prob block for QR case)
  - Prose: preserve explain block (it motivates what soundness means); compress slightly
  - Examples: cut all
  - Proofs: preserve full -- canonical induction argument; include QR case (merge from exercise)

---

### fol/axd/ide — Derivation with Identity (Axiomatic)
- **Action**: CUT
- **Lean Chapter**: CH-DED
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. Adds identity axioms as a simple extension. The identity axioms are already specified as part of AX-DED003 (A6, A7) in the taxonomy's axiom schema list. No unique taxonomy items introduced. The soundness of identity axioms follows from the main soundness theorem.
- **Content Directives**:
  - Formal items to preserve: none -- identity axioms already in AX-DED003
  - Formal items to drop: all -- pedagogical extension
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### fol/axd/pro — Examples of Derivation (Axiomatic)
- **Action**: CUT
- **Lean Chapter**: CH-DED
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. Purely pedagogical worked examples showing how to construct Hilbert derivations. No taxonomy items introduced. The identity derivation (D -> D) is referenced by fol/axd/ded, but that proof can be stated inline.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: all examples -- pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### fol/axd/prq — Derivation with Quantifiers (Axiomatic)
- **Action**: CUT
- **Lean Chapter**: CH-DED
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. Worked examples of quantifier derivations in the Hilbert system. No taxonomy items.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: all examples -- pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### Chapter: natural-deduction

### fol/ntd/rul — Rules and Derivation (ND)
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.3: Natural Deduction (also contributes PRIM-DED009 to DED.1)
- **Rationale**: Signal is CORE-DEF. Introduces PRIM-DED009 (Assumption Discharge) and DEF-DED006 (Natural Deduction System). The assumption discharge concept is unique to ND and goes to DED.1 as a generic concept. The system-specific framing (tree-structured derivations, intro/elim pattern) goes to DED.3.
- **Content Directives**:
  - Formal items to preserve: `defn[Assumption]` (top-level sentence notion); explain block on discharge mechanism (PRIM-DED009); the intro/elim rule pattern description
  - Formal items to drop: none
  - Prose: preserve -- foundational framing for ND system
  - Examples: cut all
  - Proofs: N/A

---

### fol/ntd/prl — Propositional Rules (ND)
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.3: Natural Deduction
- **Rationale**: Signal is CORE-DEF. Sole defining occurrence of DEF-DED006 (Natural Deduction System, propositional part). Specifies all propositional intro/elim rule pairs. Essential system specification for DED.3.
- **Content Directives**:
  - Formal items to preserve: all rule displays (conjunction-I/E, disjunction-I/E, implication-I/E, negation-I/E, FalseInt, FalseCl)
  - Formal items to drop: none -- all are system specification
  - Prose: compress to intro + rule displays
  - Examples: cut all
  - Proofs: N/A

---

### fol/ntd/qrl — Quantifier Rules (ND)
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.3: Natural Deduction
- **Rationale**: Signal is CORE-DEF. Extends DEF-DED006 with quantifier rules. Introduces eigenvariable condition (PRIM-DED007 instance). FOL-only.
- **Content Directives**:
  - Formal items to preserve: all rule displays (forall-I/E, exists-I/E); eigenvariable condition statement
  - Formal items to drop: none
  - Prose: compress to intro + rule displays; preserve eigenvariable explanation
  - Examples: cut all
  - Proofs: N/A

---

### fol/ntd/der — Derivations (ND)
- **Action**: CONDENSE
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.3: Natural Deduction
- **Rationale**: Signal is CORE-DEF. Formal definition of PRIM-DED005 (Derivation, ND version) as tree structure. Contains a key `defn[Derivation]` block plus extensive examples. The definition is essential; the examples are pedagogical. Condense to definition only.
- **Content Directives**:
  - Formal items to preserve: `defn[Derivation]` (tree-structured derivation from assumptions -- PRIM-DED005 ND instantiation); the sentence defining $\Gamma \Proves !A$ notation
  - Formal items to drop: all examples (ex block) -- pedagogical
  - Prose: compress to intro + definition only
  - Examples: cut all -- pedagogical (conjunction-intro, implication-intro worked examples)
  - Proofs: N/A

---

### fol/ntd/ptn — Proof-Theoretic Notions (ND)
- **Action**: MERGE-INTO:fol/axd/ptn
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (absorbed by fol/axd/ptn)
- **Rationale**: Signal is CORE-DEF but REDUNDANT-WITH fol/axd/ptn. Defines identical concepts (Theorem, Derivability, Consistency) plus identical structural properties (reflexivity, monotonicity, transitivity, inconsistency characterization, compactness) for ND. By A1 decision, the generic definitions are authoritative in fol/axd/ptn. The ND-specific proof of transitivity (using implication-intro/elim instead of sequence concatenation) is noted as a remark in DED.3.
- **Content Directives**:
  - Formal items to preserve: none standalone -- all definitions absorbed by fol/axd/ptn
  - Formal items to drop: all definitions and propositions -- redundant with authoritative section
  - Prose: replace with cross-ref to DED.1; add one-line remark in DED.3 noting that transitivity in ND uses implication-intro + elim (the proof tree construction)
  - Examples: cut all
  - Proofs: cut (absorbed; ND transitivity proof noted as remark)

---

### fol/ntd/sou — Soundness (ND)
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.3: Natural Deduction
- **Rationale**: Signal is CORE-THM. Introduces CP-001 (Soundness) for ND. Per architectural decision, each system's soundness proof stays in its own section. The ND soundness proof is by induction on derivation tree structure with one case per rule (larger than AXD but structurally important).
- **Content Directives**:
  - Formal items to preserve: `thm[soundness]` (CP-001 ND variant) with proof; `cor[weak-soundness]`; `cor[consistency-soundness]`
  - Formal items to drop: exercises
  - Prose: compress explain block
  - Examples: cut all
  - Proofs: preserve full -- each rule case is a separate verification

---

### fol/ntd/prv — Derivability and Consistency (ND)
- **Action**: MERGE-INTO:fol/axd/prv
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (absorbed by fol/axd/prv)
- **Rationale**: Signal is STEPPING-STONE but REDUNDANT-WITH fol/axd/prv. Same 4 propositions proved for ND. By A1, the generic statements are authoritative in fol/axd/prv. ND-specific proof techniques noted as remarks.
- **Content Directives**:
  - Formal items to preserve: none standalone
  - Formal items to drop: all 4 propositions -- redundant
  - Prose: replace with cross-ref to DED.1
  - Examples: cut all
  - Proofs: cut (absorbed)

---

### fol/ntd/ppr — Derivability and Propositional Connectives (ND)
- **Action**: MERGE-INTO:fol/axd/ppr
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (absorbed by fol/axd/ppr as generic statement)
- **Rationale**: Signal is STEPPING-STONE but REDUNDANT-WITH fol/axd/ppr. Same connective derivability facts proved using ND rules instead of Hilbert axioms. By A1, the statements are generic (they hold for any adequate proof system). The ND-specific proofs are not needed since equivalence of systems guarantees the results.
- **Content Directives**:
  - Formal items to preserve: none standalone
  - Formal items to drop: all propositions -- redundant
  - Prose: replace with cross-ref
  - Examples: cut all
  - Proofs: cut

---

### fol/ntd/qpr — Derivability and Quantifiers (ND)
- **Action**: MERGE-INTO:fol/axd/qpr
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (absorbed by fol/axd/qpr as generic statement)
- **Rationale**: Signal is STEPPING-STONE but REDUNDANT-WITH fol/axd/qpr. Same quantifier derivability facts for ND. FOL-only.
- **Content Directives**:
  - Formal items to preserve: none standalone
  - Formal items to drop: all -- redundant
  - Prose: replace with cross-ref
  - Examples: cut all
  - Proofs: cut

---

### fol/ntd/ide — Derivation with Identity (ND)
- **Action**: CUT
- **Lean Chapter**: CH-DED
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. Adds identity intro/elim rules to ND. Simple extension pattern with no unique taxonomy items. Identity rules are specified generically in the taxonomy.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: all -- pedagogical extension
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### fol/ntd/sid — Soundness with Identity (ND)
- **Action**: MERGE-INTO:fol/ntd/sou
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.3: Natural Deduction
- **Rationale**: Signal is STEPPING-STONE. Extends ND soundness proof to handle identity rules. Should be merged as additional cases in the main ND soundness proof (fol/ntd/sou).
- **Content Directives**:
  - Formal items to preserve: identity rule soundness cases -- merge as additional cases in fol/ntd/sou proof
  - Formal items to drop: none
  - Prose: replace with cross-ref
  - Examples: cut all
  - Proofs: merge into fol/ntd/sou proof

---

### fol/ntd/pro — Examples of Derivation (ND)
- **Action**: CUT
- **Lean Chapter**: CH-DED
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. Purely pedagogical worked examples of ND proofs. No taxonomy items.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: all examples -- pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### fol/ntd/prq — Derivation with Quantifiers (ND)
- **Action**: CUT
- **Lean Chapter**: CH-DED
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. Worked examples of quantifier reasoning in ND. No taxonomy items.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: all examples -- pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### Chapter: sequent-calculus

### fol/seq/rul — Rules and Derivations (SC)
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.4: Sequent Calculus (also contributes PRIM-DED008 to DED.1)
- **Rationale**: Signal is CORE-DEF. Sole formal defining occurrence of PRIM-DED008 (Sequent) and DEF-DED007 (Sequent Calculus). Contains `defn[Sequent]` and `defn[Initial Sequent]`. The sequent concept is unique to SC and goes to DED.1 as a generic concept. The system-specific framing goes to DED.4.
- **Content Directives**:
  - Formal items to preserve: `defn[Sequent]` (PRIM-DED008: antecedent/succedent notation); `defn[Initial Sequent]` (axiom for PRIM-DED004); explain block on sequent intuition (conjunction-of-antecedents implies disjunction-of-succedents)
  - Formal items to drop: none
  - Prose: preserve -- foundational for SC system
  - Examples: cut all
  - Proofs: N/A

---

### fol/seq/prl — Propositional Rules (SC)
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.4: Sequent Calculus
- **Rationale**: Signal is CORE-DEF. Specifies all propositional left/right rules for LK. Essential system specification for DED.4.
- **Content Directives**:
  - Formal items to preserve: all rule displays (negation-L/R, conjunction-L/R, disjunction-L/R, implication-L/R)
  - Formal items to drop: none -- all are system specification
  - Prose: compress to intro + rule displays
  - Examples: cut all
  - Proofs: N/A

---

### fol/seq/srl — Structural Rules (SC)
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.4: Sequent Calculus (also contributes PRIM-DED007 to DED.1)
- **Rationale**: Signal is CORE-DEF. Sole formal defining occurrence of PRIM-DED007 (Structural Rules: Weakening, Contraction, Exchange) and the Cut rule (CP-010 stated informally as admissible). The structural rule concepts go to DED.1 as generic concepts. The specific SC formulations go to DED.4. Note: CP-010 (Cut Elimination / Hauptsatz) is only mentioned informally here; the full proof is absent from OL.
- **Content Directives**:
  - Formal items to preserve: all defish blocks (Weakening-L/R, Contraction-L/R, Exchange-L/R, Cut); remark that Cut is admissible (informal statement of THM-DED003)
  - Formal items to drop: none
  - Prose: preserve -- concise rule specifications
  - Examples: cut all
  - Proofs: N/A (no proofs in this section; Cut admissibility is stated without proof)

---

### fol/seq/qrl — Quantifier Rules (SC)
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.4: Sequent Calculus
- **Rationale**: Signal is CORE-DEF. Extends LK with quantifier left/right rules and eigenvariable conditions. FOL-only.
- **Content Directives**:
  - Formal items to preserve: all rule displays (forall-L/R, exists-L/R); eigenvariable condition statement
  - Formal items to drop: none
  - Prose: compress to intro + rule displays; preserve eigenvariable explanation
  - Examples: cut all
  - Proofs: N/A

---

### fol/seq/der — Derivations (SC)
- **Action**: CONDENSE
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.4: Sequent Calculus
- **Rationale**: Signal is CORE-DEF. Formal definition of PRIM-DED005 (Derivation, SC version) as tree of sequents. Contains definition plus worked examples. Condense to definition only.
- **Content Directives**:
  - Formal items to preserve: `defn[LK-derivation]` (PRIM-DED005 SC instantiation)
  - Formal items to drop: worked examples (ex block) -- pedagogical
  - Prose: compress to intro + definition only
  - Examples: cut all
  - Proofs: N/A

---

### fol/seq/ptn — Proof-Theoretic Notions (SC)
- **Action**: MERGE-INTO:fol/axd/ptn
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (absorbed by fol/axd/ptn)
- **Rationale**: Signal is CORE-DEF but REDUNDANT-WITH fol/axd/ptn. Defines identical concepts (Theorem, Derivability, Consistency) plus identical structural properties for SC. By A1 decision, absorbed by fol/axd/ptn. The SC-specific definition of derivability (via finite subsets and sequents rather than derivation sequences) is noted as a remark in DED.4. Also introduces DEF-DED003 (Deductive Closure) -- this is absorbed into the generic section.
- **Content Directives**:
  - Formal items to preserve: none standalone -- all absorbed by fol/axd/ptn; the SC-specific derivability definition (using sequent notation) is noted as a remark in DED.4
  - Formal items to drop: all -- redundant
  - Prose: replace with cross-ref to DED.1; add remark in DED.4 noting SC-specific derivability definition (via Gamma_0 Sequent A)
  - Examples: cut all
  - Proofs: cut (SC transitivity via Cut is noted as remark in DED.4)

---

### fol/seq/prv — Derivability and Consistency (SC)
- **Action**: MERGE-INTO:fol/axd/prv
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (absorbed by fol/axd/prv)
- **Rationale**: Signal is STEPPING-STONE but REDUNDANT-WITH fol/axd/prv. Same 4 consistency/derivability propositions for SC.
- **Content Directives**:
  - Formal items to preserve: none standalone
  - Formal items to drop: all -- redundant
  - Prose: replace with cross-ref
  - Examples: cut all
  - Proofs: cut

---

### fol/seq/ppr — Derivability and Propositional Connectives (SC)
- **Action**: MERGE-INTO:fol/axd/ppr
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (absorbed)
- **Rationale**: Signal is STEPPING-STONE but REDUNDANT-WITH fol/axd/ppr. Same connective derivability facts for SC.
- **Content Directives**:
  - Formal items to preserve: none standalone
  - Formal items to drop: all -- redundant
  - Prose: replace with cross-ref
  - Examples: cut all
  - Proofs: cut

---

### fol/seq/qpr — Derivability and Quantifiers (SC)
- **Action**: MERGE-INTO:fol/axd/qpr
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (absorbed)
- **Rationale**: Signal is STEPPING-STONE but REDUNDANT-WITH fol/axd/qpr. Same quantifier derivability facts for SC. FOL-only.
- **Content Directives**:
  - Formal items to preserve: none standalone
  - Formal items to drop: all -- redundant
  - Prose: replace with cross-ref
  - Examples: cut all
  - Proofs: cut

---

### fol/seq/sou — Soundness (SC)
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.4: Sequent Calculus
- **Rationale**: Signal is CORE-THM. Introduces CP-001 (Soundness) for SC. Per architectural decision, each system's soundness proof stays in its own section. Includes the definition of valid sequent (semantic notion specific to SC).
- **Content Directives**:
  - Formal items to preserve: `defn[valid sequent]` (semantic notion for sequents); `thm[sequent-soundness]` (CP-001 SC variant) with proof; `cor[weak-soundness]`; `cor[entailment-soundness]`; `cor[consistency-soundness]`
  - Formal items to drop: none
  - Prose: compress explain block
  - Examples: cut all
  - Proofs: preserve full -- induction on derivation structure

---

### fol/seq/ide — Derivations with Identity (SC)
- **Action**: CONDENSE
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.4: Sequent Calculus
- **Rationale**: Signal is CORE-DEF. Extends LK with identity initial sequents and rules. Unlike the AXD and NTD identity sections (which are PEDAGOGICAL), this section formally specifies the identity extension rules for SC, which have a distinctive form (initial sequents for =).
- **Content Directives**:
  - Formal items to preserve: `defn[Initial sequents for =]` (identity axiom for SC); identity rule defish blocks
  - Formal items to drop: worked examples (Leibniz's Law, symmetry, transitivity) -- pedagogical
  - Prose: compress to rule specification only
  - Examples: cut all
  - Proofs: cut all (identity properties)

---

### fol/seq/sid — Soundness with Identity (SC)
- **Action**: MERGE-INTO:fol/seq/sou
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.4: Sequent Calculus
- **Rationale**: Signal is STEPPING-STONE. Extends SC soundness to identity rules. Should be merged as additional cases in fol/seq/sou.
- **Content Directives**:
  - Formal items to preserve: identity rule soundness cases -- merge into fol/seq/sou proof
  - Formal items to drop: none
  - Prose: replace with cross-ref
  - Examples: cut all
  - Proofs: merge into fol/seq/sou

---

### fol/seq/pro — Examples of Derivations (SC)
- **Action**: CUT
- **Lean Chapter**: CH-DED
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. Worked examples of SC derivations. No taxonomy items.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: all examples and exercises -- pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### fol/seq/prq — Derivations with Quantifiers (SC)
- **Action**: CUT
- **Lean Chapter**: CH-DED
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. Worked examples of quantifier SC derivations. FOL-only. No taxonomy items.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: all examples and exercises -- pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### Chapter: tableaux

### fol/tab/rul — Rules and Tableaux
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.5: Tableaux
- **Rationale**: Signal is CORE-DEF. Introduces DEF-DED008 (Tableau System) and PRIM-DED005 (Tableau derivation). Defines signed formulas, closed branches, and closed tableaux. Essential system specification for DED.5.
- **Content Directives**:
  - Formal items to preserve: `defn` (signed formula: T:A and F:A); explain on closed branches and closed tableaux; explain on closed tableau for A (root F:A)
  - Formal items to drop: none
  - Prose: preserve -- foundational for tableau system
  - Examples: cut all
  - Proofs: N/A

---

### fol/tab/prl — Propositional Rules (Tableaux)
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.5: Tableaux
- **Rationale**: Signal is CORE-DEF. Specifies all propositional tableau rules. Essential system specification for DED.5.
- **Content Directives**:
  - Formal items to preserve: all defish blocks (T-negation, F-negation, T-conjunction, F-conjunction, T-disjunction, F-disjunction, T-implication, F-implication, Cut)
  - Formal items to drop: none -- all are system specification
  - Prose: compress to intro + rule displays; note Cut as admissible but included for convenience
  - Examples: cut all
  - Proofs: N/A

---

### fol/tab/qrl — Quantifier Rules (Tableaux)
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.5: Tableaux
- **Rationale**: Signal is CORE-DEF. Extends tableau with quantifier rules. FOL-only. Includes eigenvariable conditions.
- **Content Directives**:
  - Formal items to preserve: all defish blocks (T-forall, F-forall, T-exists, F-exists); eigenvariable condition statement
  - Formal items to drop: none
  - Prose: compress to intro + rule displays; preserve eigenvariable explanation
  - Examples: cut all
  - Proofs: N/A

---

### fol/tab/der — Tableaux (derivations)
- **Action**: CONDENSE
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.5: Tableaux
- **Rationale**: Signal is CORE-DEF. Formal definition of PRIM-DED005 (Derivation, tableau version) as tree of signed formulas with closure criterion. Contains definition plus worked examples. Condense to definition only.
- **Content Directives**:
  - Formal items to preserve: `defn[tableau]` (PRIM-DED005 tableau instantiation)
  - Formal items to drop: worked examples (ex block) -- pedagogical
  - Prose: compress to intro + definition only
  - Examples: cut all
  - Proofs: N/A

---

### fol/tab/ptn — Proof-Theoretic Notions (Tableaux)
- **Action**: MERGE-INTO:fol/axd/ptn
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (absorbed by fol/axd/ptn)
- **Rationale**: Signal is CORE-DEF (REDUNDANT-WITH fol/axd/ptn). Defines identical concepts (Theorem, Derivability, Consistency) plus identical structural properties for tableaux. By A1 decision, absorbed by fol/axd/ptn. The tableau-specific definitions (derivability via closed tableaux, consistency via absence of closed tableaux) are noted as remarks in DED.5. Particularly notable: tableau consistency is defined differently (no closed tableau for T-signed assumptions rather than non-derivability of falsum).
- **Content Directives**:
  - Formal items to preserve: none standalone -- absorbed by fol/axd/ptn; the tableau-specific derivability and consistency definitions are noted as remarks in DED.5
  - Formal items to drop: all -- redundant
  - Prose: replace with cross-ref to DED.1; add remark in DED.5 for the tableau-specific definition of consistency (closed tableau formulation)
  - Examples: cut all
  - Proofs: cut (tableau transitivity via Cut rule noted as remark in DED.5)

---

### fol/tab/prv — Derivability and Consistency (Tableaux)
- **Action**: MERGE-INTO:fol/axd/prv
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (absorbed by fol/axd/prv)
- **Rationale**: Signal is STEPPING-STONE (REDUNDANT-WITH fol/axd/prv). Same 4 consistency/derivability propositions for tableaux.
- **Content Directives**:
  - Formal items to preserve: none standalone
  - Formal items to drop: all -- redundant
  - Prose: replace with cross-ref
  - Examples: cut all
  - Proofs: cut

---

### fol/tab/ppr — Derivability and Propositional Connectives (Tableaux)
- **Action**: MERGE-INTO:fol/axd/ppr
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (absorbed)
- **Rationale**: Signal is STEPPING-STONE (REDUNDANT-WITH fol/axd/ppr). Same connective derivability facts for tableaux.
- **Content Directives**:
  - Formal items to preserve: none standalone
  - Formal items to drop: all -- redundant
  - Prose: replace with cross-ref
  - Examples: cut all
  - Proofs: cut

---

### fol/tab/qpr — Derivability and Quantifiers (Tableaux)
- **Action**: MERGE-INTO:fol/axd/qpr
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.1: Generic Proof-Theoretic Concepts (absorbed)
- **Rationale**: Signal is STEPPING-STONE (REDUNDANT-WITH fol/axd/qpr). Same quantifier derivability facts for tableaux. FOL-only.
- **Content Directives**:
  - Formal items to preserve: none standalone
  - Formal items to drop: all -- redundant
  - Prose: replace with cross-ref
  - Examples: cut all
  - Proofs: cut

---

### fol/tab/sou — Soundness (Tableaux)
- **Action**: KEEP
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.5: Tableaux
- **Rationale**: Signal is CORE-THM (REDUNDANT-WITH fol/seq/sou for the result, but proof strategy differs). Introduces CP-001 (Soundness) for tableaux. Per architectural decision, each system's soundness proof stays in its own section. The tableau soundness proof uses branch satisfaction (different from induction-on-derivation in other systems).
- **Content Directives**:
  - Formal items to preserve: `defn[satisfies signed formula]` (semantic notion specific to tableaux); `thm[tableau-soundness]` (CP-001 tableau variant) with proof; corollaries (weak-soundness, entailment-soundness, consistency-soundness)
  - Formal items to drop: none
  - Prose: compress explain block
  - Examples: cut all
  - Proofs: preserve full -- branch satisfaction argument is distinctive

---

### fol/tab/ide — Tableaux with Identity
- **Action**: CONDENSE
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.5: Tableaux
- **Rationale**: Signal is CORE-DEF (REDUNDANT-WITH fol/seq/ide for concepts, but tableau-specific formulation). Extends tableau with identity rules. The tableau identity rules (T=, F=) have a distinctive form that differs from SC identity rules.
- **Content Directives**:
  - Formal items to preserve: identity rule defish blocks (= rule, T=, F=)
  - Formal items to drop: worked examples (Leibniz's Law, symmetry, transitivity) -- pedagogical
  - Prose: compress to rule specification only
  - Examples: cut all
  - Proofs: cut all

---

### fol/tab/sid — Soundness with Identity (Tableaux)
- **Action**: MERGE-INTO:fol/tab/sou
- **Lean Chapter**: CH-DED
- **Lean Section**: DED.5: Tableaux
- **Rationale**: Signal is STEPPING-STONE (REDUNDANT-WITH fol/seq/sid). Extends tableau soundness to identity rules. Merge as additional cases in fol/tab/sou.
- **Content Directives**:
  - Formal items to preserve: identity rule soundness cases -- merge into fol/tab/sou proof
  - Formal items to drop: none
  - Prose: replace with cross-ref
  - Examples: cut all
  - Proofs: merge into fol/tab/sou

---

### fol/tab/pro — Examples of Tableaux
- **Action**: CUT
- **Lean Chapter**: CH-DED
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. Worked examples of propositional tableaux. No taxonomy items.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: all examples and exercises -- pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

### fol/tab/prq — Tableaux with Quantifiers (examples)
- **Action**: CUT
- **Lean Chapter**: CH-DED
- **Lean Section**: N/A
- **Rationale**: Signal is PEDAGOGICAL. Worked examples of quantifier tableaux. FOL-only. No taxonomy items.
- **Content Directives**:
  - Formal items to preserve: none
  - Formal items to drop: all examples and exercises -- pedagogical
  - Prose: cut all
  - Examples: cut all
  - Proofs: cut all

---

## Summary

### Action Counts

| Action | Count | Sections |
|--------|-------|----------|
| **KEEP** | 19 | fol/axd/rul, fol/axd/prp, fol/axd/qua, fol/axd/ded, fol/axd/prv, fol/axd/sou, fol/ntd/rul, fol/ntd/prl, fol/ntd/qrl, fol/ntd/sou, fol/seq/rul, fol/seq/prl, fol/seq/srl, fol/seq/qrl, fol/seq/sou, fol/tab/rul, fol/tab/prl, fol/tab/qrl, fol/tab/sou |
| **ABSORB** | 1 | fol/axd/ptn (absorbs fol/ntd/ptn, fol/seq/ptn, fol/tab/ptn) |
| **CONDENSE** | 9 | fol/prf/axd, fol/prf/ntd, fol/axd/ppr, fol/axd/qpr, fol/ntd/der, fol/seq/der, fol/seq/ide, fol/tab/der, fol/tab/ide |
| **MERGE-INTO** | 16 | fol/axd/ddq->ded, fol/ntd/ptn->axd/ptn, fol/ntd/prv->axd/prv, fol/ntd/ppr->axd/ppr, fol/ntd/qpr->axd/qpr, fol/ntd/sid->ntd/sou, fol/seq/ptn->axd/ptn, fol/seq/prv->axd/prv, fol/seq/ppr->axd/ppr, fol/seq/qpr->axd/qpr, fol/seq/sid->seq/sou, fol/tab/ptn->axd/ptn, fol/tab/prv->axd/prv, fol/tab/ppr->axd/ppr, fol/tab/qpr->axd/qpr, fol/tab/sid->tab/sou |
| **CUT** | 13 | fol/prf/int, fol/prf/seq, fol/prf/tab, fol/axd/ide, fol/axd/pro, fol/axd/prq, fol/ntd/ide, fol/ntd/pro, fol/ntd/prq, fol/seq/pro, fol/seq/prq, fol/tab/pro, fol/tab/prq |
| **Total** | **58** | (19 KEEP + 1 ABSORB + 9 CONDENSE + 16 MERGE-INTO + 13 CUT) |

Note: The ABSORB action (fol/axd/ptn) is functionally a KEEP that also absorbs 3 MERGE-INTO sources. The 16 MERGE-INTO entries are the sections being merged. The total 19 + 1 + 9 + 16 + 13 = 58 sections.

### Lean Section Distribution

| Lean Section | Sections Feeding In | Key Content |
|-------------|-------------------|-------------|
| **DED.1** Generic | fol/axd/rul (generic defs), fol/axd/ptn (ABSORB:3 ptn), fol/axd/prv (ABSORB:3 prv), fol/axd/ppr (ABSORB:3 ppr), fol/axd/qpr (ABSORB:3 qpr), fol/ntd/rul (PRIM-DED009), fol/seq/rul (PRIM-DED008), fol/seq/srl (PRIM-DED007) | Rule of inference, derivation, provability, theorem, consistency, structural properties, sequent, structural rules, assumption discharge |
| **DED.2** Axiomatic | fol/prf/axd, fol/axd/prp, fol/axd/qua, fol/axd/ded (+ddq), fol/axd/ppr, fol/axd/qpr, fol/axd/sou | Hilbert axiom schemas, MP, QR, Deduction Theorem, connective/quantifier facts, soundness |
| **DED.3** Natural Deduction | fol/prf/ntd, fol/ntd/rul, fol/ntd/prl, fol/ntd/qrl, fol/ntd/der, fol/ntd/sou (+sid) | ND rules (intro/elim), derivation definition, soundness |
| **DED.4** Sequent Calculus | fol/seq/rul, fol/seq/prl, fol/seq/srl, fol/seq/qrl, fol/seq/der, fol/seq/sou (+sid), fol/seq/ide | LK rules (left/right), structural rules, sequent derivation, soundness, identity rules |
| **DED.5** Tableaux | fol/tab/rul, fol/tab/prl, fol/tab/qrl, fol/tab/der, fol/tab/sou (+sid), fol/tab/ide | Signed formulas, tableau rules, tableau derivation, soundness, identity rules |

### Taxonomy Coverage

**Primitives covered** (10 of 10):
- PRIM-DED001 (Axiom Schema): fol/axd/prp (DED.2)
- PRIM-DED002 (Non-Logical Axiom): not in this batch (theories chapter)
- PRIM-DED003 (Rule of Inference): fol/axd/rul (DED.1)
- PRIM-DED004 (Proof System): implicit across DED.2-5
- PRIM-DED005 (Derivation): fol/axd/rul (DED.1 generic), instantiated in DED.2-5
- PRIM-DED006 (Provability): fol/axd/ptn (DED.1)
- PRIM-DED007 (Structural Rules): fol/seq/srl (DED.1/4)
- PRIM-DED008 (Sequent): fol/seq/rul (DED.1/4)
- PRIM-DED009 (Assumption Discharge): fol/ntd/rul (DED.1/3)
- PRIM-DED010 (Theorem): fol/axd/ptn (DED.1)

**Definitions covered** (8 of 10 in-scope):
- DEF-DED001 (Syntactic Consistency): fol/axd/ptn (DED.1)
- DEF-DED003 (Deductive Closure): fol/axd/ptn (DED.1, absorbed from fol/seq/ptn)
- DEF-DED005 (Hilbert-Style System): fol/axd/prp (DED.2)
- DEF-DED006 (ND System): fol/ntd/prl (DED.3)
- DEF-DED007 (SC System): fol/seq/rul (DED.4)
- DEF-DED008 (Tableau System): fol/tab/rul (DED.5)
- DEF-DED002 (Maximal Consistent Set): not in this batch (completeness chapter)
- DEF-DED004 (Conservative Extension): NEW-CONTENT

**Axioms covered** (3 of 3):
- AX-DED001 (MP): fol/axd/prp (DED.2)
- AX-DED002 (Gen): fol/axd/qua (DED.2)
- AX-DED003 (Axiom Schemas): fol/axd/prp + fol/axd/qua (DED.2)

**Theorems covered** (1 in-scope):
- THM-DED001 (Deduction Theorem): fol/axd/ded (DED.2)
- CP-001 (Soundness): fol/axd/sou (DED.2), fol/ntd/sou (DED.3), fol/seq/sou (DED.4), fol/tab/sou (DED.5)

**Composition patterns**:
- CP-009 (Deduction Theorem): fol/axd/ded (DED.2)
- CP-010 (Cut Elimination): fol/seq/srl (DED.4, informal statement only)

### Expected Redundancy Resolutions (19 of 19)

All 19 expected cross-system redundancies are resolved by the A1 architecture:

| Redundant Concept | Authoritative Home | Systems Merged |
|-------------------|-------------------|----------------|
| Provability (PRIM-DED006) | fol/axd/ptn | NTD, SC, Tab ptn |
| Theorem (PRIM-DED010) | fol/axd/ptn | NTD, SC, Tab ptn |
| Consistency (DEF-DED001) | fol/axd/ptn | NTD, SC, Tab ptn |
| Reflexivity | fol/axd/ptn | NTD, SC, Tab ptn |
| Monotonicity | fol/axd/ptn | NTD, SC, Tab ptn |
| Transitivity | fol/axd/ptn | NTD, SC, Tab ptn |
| Inconsistency characterization | fol/axd/ptn | NTD, SC, Tab ptn |
| Compactness | fol/axd/ptn | NTD, SC, Tab ptn |
| provability-contr | fol/axd/prv | NTD, SC, Tab prv |
| prov-incons | fol/axd/prv | NTD, SC, Tab prv |
| explicit-inc | fol/axd/prv | NTD, SC, Tab prv |
| provability-exhaustive | fol/axd/prv | NTD, SC, Tab prv |
| provability-land | fol/axd/ppr | NTD, SC, Tab ppr |
| provability-lor | fol/axd/ppr | NTD, SC, Tab ppr |
| provability-lif | fol/axd/ppr | NTD, SC, Tab ppr |
| strong-generalization | fol/axd/qpr | NTD, SC, Tab qpr |
| provability-quantifiers | fol/axd/qpr | NTD, SC, Tab qpr |
| Soundness identity ext (sid) | per-system sou | NTD, SC, Tab sid |
| Deductive Closure (DEF-DED003) | fol/axd/ptn | SC ptn |

### Generic Concept Assignments (DED.1)

See DED-GENERIC-ASSIGNMENTS.md for the full table. In summary:

- **fol/axd/rul** is authoritative for: PRIM-DED001 (Rule of Inference), PRIM-DED005 (Derivation)
- **fol/axd/ptn** is authoritative for: PRIM-DED006 (Provability), PRIM-DED010 (Theorem), DEF-DED001 (Consistency), DEF-DED003 (Deductive Closure), plus 5 structural properties
- **fol/axd/prv** is authoritative for: 4 consistency/derivability propositions
- **fol/ntd/rul** is authoritative for: PRIM-DED009 (Assumption Discharge)
- **fol/seq/rul** is authoritative for: PRIM-DED008 (Sequent)
- **fol/seq/srl** is authoritative for: PRIM-DED007 (Structural Rules)
