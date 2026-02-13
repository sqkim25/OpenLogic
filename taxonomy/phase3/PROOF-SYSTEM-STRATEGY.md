# PROOF-SYSTEM-STRATEGY: Architectural Decision A1

This document records the resolution of Architectural Decision A1 -- "Generic Proof Theory + Per-System Instantiation" -- which governs how the lean text handles the four proof systems (Axiomatic/Hilbert, Natural Deduction, Sequent Calculus, Tableaux) across ~58 DED sections.

---

## 1. Strategy Summary

**Decision**: The lean text defines proof-theoretic concepts ONCE at the generic level (DED.1), then presents each concrete proof system as an instantiation section (DED.2--DED.5). A concept is "generic" if its statement is proof-system-independent; it is "system-specific" if its formulation depends on the particular rules or derivation structure of one system.

**Rationale**:
- The OpenLogic textbook repeats identical definitions (provability, theorem, consistency, derivability structural properties) in each of its 4 proof-system chapters, creating 19 expected redundancies.
- The A1 architecture eliminates all 19 by defining each concept once in DED.1, with system-specific instantiation details noted as remarks in DED.2--5.
- This mirrors the standard mathematical practice (as in Troelstra & Schwichtenberg) of separating abstract proof theory from concrete calculi.

**Key refinement**: Soundness (CP-001) does NOT get a single generic proof. Each proof system's soundness argument is structurally different (induction on derivation length for Hilbert, induction on derivation tree for ND, permutation argument for SC, branch satisfaction for Tableaux). Each system's soundness proof stays in its own section (DED.2--5). META.1 consolidates them into a single theorem statement.

---

## 2. Generic vs. System-Specific Classification

### 2a. Generic DED Concepts (DED.1)

These concepts are defined once, proof-system-independently:

| Taxonomy ID | Concept | Authoritative OL Section | Notes |
|------------|---------|-------------------------|-------|
| PRIM-DED001 | Axiom Schema | fol/axd/prp | Generic notion; Hilbert schemas are an instantiation |
| PRIM-DED002 | Non-Logical Axiom | (theories chapter) | Not in DED batch; handled via DED.6 |
| PRIM-DED003 | Rule of Inference | fol/axd/rul | Most complete formal definition |
| PRIM-DED004 | Proof System | implicit | Instantiated by DEF-DED005--008 |
| PRIM-DED005 | Derivation | fol/axd/rul | Generic structured object; each system instantiates |
| PRIM-DED006 | Provability | fol/axd/ptn | Most explicit definition + all 5 structural properties |
| PRIM-DED007 | Structural Rules | fol/seq/srl | Defined in SC context but applicable generically |
| PRIM-DED008 | Sequent | fol/seq/rul | SC-specific notation but introduced in DED.1 for DED.4 |
| PRIM-DED009 | Assumption Discharge | fol/ntd/rul | ND-specific mechanism but introduced in DED.1 for DED.3 |
| PRIM-DED010 | Theorem | fol/axd/ptn | Derivation from empty set |
| DEF-DED001 | Syntactic Consistency | fol/axd/ptn | Non-derivability of falsum |
| DEF-DED002 | Maximal Consistent Set | fol/com/mcs | Used in completeness proof |
| DEF-DED003 | Deductive Closure | fol/axd/ptn | Absorbed from fol/seq/ptn |
| DEF-DED004 | Conservative Extension | NEW-CONTENT | Written from domain spec |
| DEF-DED009 | Derived Rule | FORMALIZE | Implicit in OL; formalized per A4 |
| DEF-DED010 | Admissible Rule | FORMALIZE | Implicit in OL; formalized per A4 |

### 2b. System-Specific Concepts

Each proof system contributes unique rules, derivation formats, and system-specific theorems:

**DED.2: Axiomatic (Hilbert) Systems**

| Item | Concept | OL Section |
|------|---------|-----------|
| DEF-DED005 | Hilbert-Style System definition | fol/axd/prp |
| AX-DED001 | Modus Ponens | fol/axd/prp |
| AX-DED002 | Generalization Rule | fol/axd/qua |
| AX-DED003 | Logical Axiom Schemas (A1--A6, Q6--Q8) | fol/axd/prp + fol/axd/qua |
| THM-DED001 | Deduction Theorem | fol/axd/ded |
| CP-009 | Deduction Theorem (formal) | fol/axd/ded |
| CP-001 (AX) | Soundness (axiomatic) | fol/axd/sou |

**DED.3: Natural Deduction**

| Item | Concept | OL Section |
|------|---------|-----------|
| DEF-DED006 | ND System definition | fol/ntd/prl |
| -- | Intro/Elim rules (propositional) | fol/ntd/prl |
| -- | Intro/Elim rules (quantifier) | fol/ntd/qrl |
| -- | ND derivation tree definition | fol/ntd/der |
| CP-001 (ND) | Soundness (ND) | fol/ntd/sou |

**DED.4: Sequent Calculus**

| Item | Concept | OL Section |
|------|---------|-----------|
| DEF-DED007 | SC System definition | fol/seq/rul |
| -- | Left/Right rules (propositional) | fol/seq/prl |
| -- | Left/Right rules (quantifier) | fol/seq/qrl |
| -- | Structural rules (Weakening, Contraction, Exchange, Cut) | fol/seq/srl |
| -- | SC derivation definition | fol/seq/der |
| -- | Identity rules for SC | fol/seq/ide |
| CP-010 | Cut Elimination (Gentzen's Hauptsatz) | fol/seq/srl (statement) |
| CP-001 (SC) | Soundness (SC) | fol/seq/sou |

**DED.5: Tableaux**

| Item | Concept | OL Section |
|------|---------|-----------|
| DEF-DED008 | Tableau System definition | fol/tab/rul |
| -- | Signed formula rules (propositional) | fol/tab/prl |
| -- | Signed formula rules (quantifier) | fol/tab/qrl |
| -- | Tableau derivation (tree of signed formulas) | fol/tab/der |
| -- | Tableau identity rules (T=, F=) | fol/tab/ide |
| CP-001 (Tab) | Soundness (tableaux, branch satisfaction) | fol/tab/sou |

---

## 3. Soundness Treatment (CP-001)

**Architecture**: Soundness is proven per-system in DED.2--5. META.1 states the unified theorem and cross-references the four proofs.

| System | OL Section | Proof Strategy | Distinctive Feature |
|--------|-----------|----------------|-------------------|
| Axiomatic | fol/axd/sou | Induction on derivation length | Base: axiom instances are valid. Step: MP/Gen preserve truth |
| Natural Deduction | fol/ntd/sou | Induction on derivation tree | Each intro/elim rule preserves truth under any assignment |
| Sequent Calculus | fol/seq/sou | Induction on derivation height | Each left/right rule preserves satisfaction of sequents |
| Tableaux | fol/tab/sou | Branch satisfaction argument | If assumptions are satisfiable, every rule extension preserves satisfiability |

**Identity extensions**: Each system's soundness proof is extended to cover identity rules. The identity-soundness sections (fol/axd/ide, fol/ntd/sid, fol/seq/sid, fol/tab/sid) are merged into their system's main soundness section:
- fol/axd/ide: CUT (identity axioms are logical axioms in Hilbert systems)
- fol/ntd/sid: MERGE-INTO fol/ntd/sou
- fol/seq/sid: MERGE-INTO fol/seq/sou
- fol/tab/sid: MERGE-INTO fol/tab/sou

---

## 4. Completeness Treatment (CP-002)

**Architecture**: Completeness is proved ONCE via the Henkin construction in META.2. The proof is proof-system-independent: it constructs a model from a maximal consistent set, and maximal consistency is defined generically in DED.1.

**Henkin proof chain** (preserved intact):
1. fol/com/ccs -- Complete consistent sets (DEF-SEM005) [KEEP]
2. fol/com/mcs -- Maximal consistent sets (DEF-DED002) [CONDENSE]
3. fol/com/hen -- Henkin expansion + saturation [KEEP]
4. fol/com/lin -- Lindenbaum's Lemma (THM-DED005) [KEEP]
5. fol/com/mod -- Term model + Truth Lemma [KEEP]
6. fol/com/ide -- Factored term model (identity) [KEEP]
7. fol/com/cth -- Completeness Theorem (CP-002) [KEEP]

The completeness proof uses provability (PRIM-DED006) and consistency (DEF-DED001) generically. It works for ANY sound and complete proof system, so it need not be repeated per system.

---

## 5. System-Specific Composition Patterns

| CP | System | Lean Section | Treatment |
|----|--------|-------------|-----------|
| CP-009 (Deduction Theorem) | Axiomatic only | DED.2 | Full proof preserved (fol/axd/ded). Applies only to Hilbert systems. |
| CP-010 (Cut Elimination) | Sequent Calculus only | DED.4 | Statement in fol/seq/srl. Full proof deferred (not in OL CORE). |

These are NOT consolidated into META because they are internal to a single proof system, not cross-domain composition patterns.

---

## 6. Impact Matrix: All 58 DED Sections

| OL Section | Action | Lean Section | Content Contribution |
|-----------|--------|-------------|---------------------|
| **fol/prf/int** | CUT | -- | Pedagogical overview of proof systems |
| **fol/prf/axd** | CONDENSE | DED.2 | System overview paragraph |
| **fol/prf/ntd** | CONDENSE | DED.3 | System overview paragraph |
| **fol/prf/seq** | CUT | -- | Pedagogical overview of sequent calculus |
| **fol/prf/tab** | CUT | -- | Pedagogical overview of tableaux |
| **fol/axd/rul** | KEEP | DED.1 | PRIM-DED003 (Rule of Inference), PRIM-DED005 (Derivation) |
| **fol/axd/prp** | KEEP | DED.2 | DEF-DED005, AX-DED001 (MP), AX-DED003 (Axiom Schemas) |
| **fol/axd/qua** | KEEP | DED.2 | AX-DED002 (Gen), AX-DED003 (Quantifier Schemas) |
| **fol/axd/ded** | KEEP | DED.2 | THM-DED001 (Deduction Theorem), CP-009 |
| **fol/axd/ddq** | MERGE-INTO:fol/axd/ded | DED.2 | Quantifier variant of deduction theorem |
| **fol/axd/ptn** | ABSORB:ntd/ptn,seq/ptn,tab/ptn | DED.1 | PRIM-DED006, PRIM-DED010, DEF-DED001, DEF-DED003 + 5 structural props |
| **fol/axd/prv** | KEEP (absorbs 3 prv) | DED.1 | 4 consistency/derivability propositions |
| **fol/axd/ppr** | CONDENSE (absorbs 3 ppr) | DED.1 | Connective derivability facts |
| **fol/axd/qpr** | CONDENSE (absorbs 3 qpr) | DED.1 | Quantifier derivability facts |
| **fol/axd/sou** | KEEP | DED.2 | CP-001 (Soundness, axiomatic) |
| **fol/axd/ide** | CUT | -- | Identity axioms (subsumed by axiom schemas) |
| **fol/axd/pro** | CUT | -- | Worked examples (pedagogical) |
| **fol/axd/prq** | CUT | -- | Quantifier examples (pedagogical) |
| **fol/ntd/rul** | KEEP | DED.1/DED.3 | PRIM-DED009 (Assumption Discharge) |
| **fol/ntd/prl** | KEEP | DED.3 | DEF-DED006, intro/elim rules (propositional) |
| **fol/ntd/qrl** | KEEP | DED.3 | Intro/elim rules (quantifier) |
| **fol/ntd/der** | CONDENSE | DED.3 | ND derivation tree definition |
| **fol/ntd/ptn** | MERGE-INTO:fol/axd/ptn | DED.1 | Redundant with fol/axd/ptn |
| **fol/ntd/prv** | MERGE-INTO:fol/axd/prv | DED.1 | Redundant with fol/axd/prv |
| **fol/ntd/ppr** | MERGE-INTO:fol/axd/ppr | DED.1 | Redundant with fol/axd/ppr |
| **fol/ntd/qpr** | MERGE-INTO:fol/axd/qpr | DED.1 | Redundant with fol/axd/qpr |
| **fol/ntd/sou** | KEEP | DED.3 | CP-001 (Soundness, ND) |
| **fol/ntd/ide** | CUT | -- | ND identity rules (brief, folded into DED.3 remark) |
| **fol/ntd/sid** | MERGE-INTO:fol/ntd/sou | DED.3 | Identity soundness cases for ND |
| **fol/ntd/pro** | CUT | -- | Worked examples (pedagogical) |
| **fol/ntd/prq** | CUT | -- | Quantifier examples (pedagogical) |
| **fol/seq/rul** | KEEP | DED.1/DED.4 | PRIM-DED008 (Sequent), DEF-DED007 |
| **fol/seq/prl** | KEEP | DED.4 | Left/right rules (propositional) |
| **fol/seq/srl** | KEEP | DED.1/DED.4 | PRIM-DED007 (Structural Rules), CP-010 statement |
| **fol/seq/qrl** | KEEP | DED.4 | Left/right rules (quantifier) |
| **fol/seq/der** | CONDENSE | DED.4 | SC derivation definition |
| **fol/seq/ptn** | MERGE-INTO:fol/axd/ptn | DED.1 | Redundant with fol/axd/ptn |
| **fol/seq/prv** | MERGE-INTO:fol/axd/prv | DED.1 | Redundant with fol/axd/prv |
| **fol/seq/ppr** | MERGE-INTO:fol/axd/ppr | DED.1 | Redundant with fol/axd/ppr |
| **fol/seq/qpr** | MERGE-INTO:fol/axd/qpr | DED.1 | Redundant with fol/axd/qpr |
| **fol/seq/sou** | KEEP | DED.4 | CP-001 (Soundness, SC) |
| **fol/seq/ide** | CONDENSE | DED.4 | Identity rules for SC |
| **fol/seq/sid** | MERGE-INTO:fol/seq/sou | DED.4 | Identity soundness cases for SC |
| **fol/seq/pro** | CUT | -- | Worked examples (pedagogical) |
| **fol/seq/prq** | CUT | -- | Quantifier examples (pedagogical) |
| **fol/tab/rul** | KEEP | DED.5 | DEF-DED008, signed formula rules |
| **fol/tab/prl** | KEEP | DED.5 | Signed formula rules (propositional) |
| **fol/tab/qrl** | KEEP | DED.5 | Signed formula rules (quantifier) |
| **fol/tab/der** | CONDENSE | DED.5 | Tableau derivation definition |
| **fol/tab/ptn** | MERGE-INTO:fol/axd/ptn | DED.1 | Redundant with fol/axd/ptn |
| **fol/tab/prv** | MERGE-INTO:fol/axd/prv | DED.1 | Redundant with fol/axd/prv |
| **fol/tab/ppr** | MERGE-INTO:fol/axd/ppr | DED.1 | Redundant with fol/axd/ppr |
| **fol/tab/qpr** | MERGE-INTO:fol/axd/qpr | DED.1 | Redundant with fol/axd/qpr |
| **fol/tab/sou** | KEEP | DED.5 | CP-001 (Soundness, tableaux) |
| **fol/tab/ide** | CONDENSE | DED.5 | Tableau identity rules (T=, F=) |
| **fol/tab/sid** | MERGE-INTO:fol/tab/sou | DED.5 | Identity soundness cases for tableaux |
| **fol/tab/pro** | CUT | -- | Worked examples (pedagogical) |
| **fol/tab/prq** | CUT | -- | Quantifier examples (pedagogical) |

### Action Summary

| Action | Count |
|--------|-------|
| KEEP | 19 |
| CONDENSE | 9 |
| ABSORB | 1 |
| MERGE-INTO | 16 |
| CUT | 13 |
| **Total** | **58** |

### Surviving Sections by Lean Section

| Lean Section | Surviving | Sections |
|-------------|-----------|---------|
| DED.1 | 8 | axd/rul, axd/ptn(+3), axd/prv(+3), axd/ppr(+3), axd/qpr(+3), ntd/rul, seq/rul, seq/srl |
| DED.2 | 6 | prf/axd, axd/prp, axd/qua, axd/ded(+ddq), axd/sou |
| DED.3 | 5 | prf/ntd, ntd/prl, ntd/qrl, ntd/der, ntd/sou(+sid) |
| DED.4 | 7 | seq/rul, seq/prl, seq/srl, seq/qrl, seq/der, seq/sou(+sid), seq/ide |
| DED.5 | 6 | tab/rul, tab/prl, tab/qrl, tab/der, tab/sou(+sid), tab/ide |
| **Total surviving** | **29** (from 58 original) | 50% compression |

---

## 7. Expected Redundancy Resolution Under A1

The A1 architecture resolves all 19 expected cross-system DED redundancies. These are concepts identically defined in all 4 proof systems. Under A1, each is defined ONCE in DED.1 (authoritative = fol/axd/* section), and the 3 system-specific versions MERGE-INTO the authoritative section.

See REDUNDANCY-RESOLUTION.md for the complete table of all 19 resolutions, including which formal items survive and which drop from each merged section.

---

## 8. Phase 4 Instructions for DED Chapter

1. **DED.1 (Generic)**: Copy formal definitions from authoritative sections. For each structural property (reflexivity, monotonicity, transitivity, compactness, inconsistency characterization), preserve the axiomatic-system proof as the canonical proof. Add one-line remarks noting that the same properties hold in ND, SC, and Tableaux with system-specific proof variations.

2. **DED.2--5 (Instantiations)**: Copy system-specific rule definitions and soundness proofs. Do NOT redefine provability, theorem, consistency, or structural properties -- instead cross-reference DED.1. Each section opens with "In the [system name], the generic concepts of DED.1 are instantiated as follows..." followed by the system's rule definitions.

3. **Identity handling**: Each system's identity rules are a brief subsection within its DED.N section. The identity-soundness proof is merged into the main soundness proof as additional cases.

4. **Worked examples**: All cut. The lean text provides definitions and proofs, not pedagogical worked examples. Phase 4 may add ONE minimal example per system if needed for clarity, but this is optional.

5. **CP-001 (Soundness)**: Each DED.N section contains its own soundness theorem and proof. META.1 states: "Theorem (Soundness). For each of the proof systems defined in DED.2--5, if Gamma |- phi then Gamma |= phi. Proof: See DED.2 (Axiomatic), DED.3 (ND), DED.4 (SC), DED.5 (Tableaux)."

6. **CP-002 (Completeness)**: Lives entirely in META.2. References DED.1 for consistency and provability definitions. The Henkin construction is proof-system-independent.
