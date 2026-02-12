# Taxonomy of Mathematical Logic

A lean, Metamath-inspired systematization of mathematical logic — every concept traceable to primitives, no redundancy, full dependency graph.

This is a **reference taxonomy** for readers with some logic exposure (at least one semester or equivalent). It prioritizes correctness and traceability over pedagogical sequencing, though guided learning paths are provided below.

## The 5+1 Domains

| Code | Domain | Irreducible Question | Items |
|------|--------|---------------------|-------|
| **BST** | Set-Bootstrap (Level-0) | What naive mathematical objects does the metalanguage use? | 16 PRIM + 5 DEF |
| **SYN** | Syntax | How are well-formed expressions constructed? | 18 PRIM + 8 DEF |
| **SEM** | Semantics | How is meaning assigned to expressions? | 15 PRIM + 16 DEF |
| **DED** | Deduction | How are truths derived from assumptions? | 10 PRIM + 10 DEF |
| **CMP** | Computation | What is effectively decidable/computable? | 12 PRIM + 10 DEF |
| **SET** | Set-Formal (Level-1) | What is the formal mathematical universe? | 3 PRIM + 11 DEF + 9 AX |

**Total: 134 primitives and definitions** across 6 domains, plus 13 composition patterns (metatheorems) at domain intersections.

**METATHEORY** is not a domain — it is the collection of composition patterns (soundness, completeness, compactness, incompleteness, etc.) that live at domain intersections. See CROSS-DOMAIN-MAP.md.

## Dependency Diagram

```
BST (Level-0 root — naive set theory metalanguage)
 |
 +-- SYN (Syntax: depends on BST)
 |    |
 |    +-- SEM (Semantics: depends on SYN, BST)
 |    |
 |    +-- DED (Deduction: depends on SYN, BST)
 |
 +-- CMP (Computation: depends on BST)
 |
 +-- SET (Formal Set Theory: depends on SYN, SEM, DED, BST)
```

**Key architectural decision**: BST (Level-0) provides the naive set-theoretic metalanguage used to *build* the formalism. SET (Level-1) is ZFC as a formal first-order theory *within* the formalism. The circularity dissolves because Level-0 sets are used to BUILD the system; Level-1 set theory is a SUBJECT OF the system.

SEM and DED are independent of each other — their deep connection (the completeness theorem) is a *composition pattern* (CP-002), not a dependency.

## Guided Learning Paths

### Path 1: Propositional Logic (entry point)

1. **BST**: sets, functions, sequences, induction (PRIM-BST001--016)
   - *Checkpoint*: Can define "a function from A to B" and "proof by induction"
2. **SYN-PL**: propositional variables, connectives, formulas (PRIM-SYN002--003, SYN012, AX-SYN003)
   - *Checkpoint*: Can determine if a string is a well-formed propositional formula
3. **SEM-PL**: truth-value assignments, truth tables, tautology, PL-consequence (PRIM-SEM015, DEF-SEM009--010)
   - *Checkpoint*: Can evaluate truth of a formula under an assignment; can determine if a formula is a tautology
4. **DED-PL**: propositional axioms/rules, proofs in PL (AX-DED001, AX-DED003 schemas A1--A3)
   - *Checkpoint*: Can construct a Hilbert-style proof of a propositional tautology
5. **CP-001(PL) + CP-002(PL)**: soundness and completeness for propositional logic
   - *Checkpoint*: Can state and sketch the proof of PL completeness

### Bridge: PL to FOL (key conceptual jumps)

- PL formulas are built from atomic propositions ($p, q, r$). FOL formulas are built from **terms** (naming objects) and **predicates** (stating properties). This is the shift from "true/false propositions" to "objects with properties and relationships."
- PL semantics uses truth-value assignments (a function from variables to $\{0,1\}$). FOL semantics uses **structures** (a domain of objects + interpretations of symbols). This is the shift from "which propositions are true?" to "what universe are we talking about?"
- PL proof systems use only propositional rules. FOL adds **quantifier rules** (generalization, instantiation) that manage the transition between "for all $x$" and specific instances.

### Path 2: First-Order Logic (lift from PL)

6. **SYN**: terms, quantifiers, formulas, substitution, sentences (PRIM-SYN004--018, DEF-SYN001--008)
   - *Checkpoint*: Can determine free/bound variables; can compute substitution $\varphi[t/x]$
7. **SEM**: structures, satisfaction, truth, validity, consequence, models (PRIM-SEM001--014, DEF-SEM001--008)
   - *Checkpoint*: Can evaluate $\mathfrak{A} \vDash \varphi[s]$ for a given structure and assignment
8. **DED**: quantifier rules, generalization, FOL proof systems (AX-DED002, DEF-DED005--008)
   - *Checkpoint*: Can construct a proof of a first-order validity
9. **CP-001 through CP-004**: soundness, completeness, compactness, Lowenheim-Skolem
   - *Checkpoint*: Can state all four; can sketch Henkin completeness proof; can apply compactness

### Path 3: Computation and Limits

10. **CMP**: recursive functions, Turing machines, Church-Turing thesis, undecidability (PRIM-CMP001--012, DEF-CMP001--010)
    - *Checkpoint*: Can prove halting problem unsolvable; can explain Church-Turing thesis
11. **CP-005 through CP-008**: incompleteness, undefinability, undecidability of validity
    - *Checkpoint*: Can state G1/G2; can explain role of arithmetization and diagonalization

### Path 4: Formal Set Theory and Extensions

12. **SET**: ZFC axioms, ordinals, cardinals (PRIM-SET001--003, AX-SET001--009, DEF-SET001--011)
13. **Extensions**: Modal, intuitionistic, many-valued, higher-order (via extension points in each domain spec)

## File Index

| File | Description |
|------|-------------|
| `README.md` | This file — overview, learning paths, file index |
| `CONVENTIONS.md` | Cross-domain conventions, ID scheme, boundary principles, primitive registry |
| `DOMAIN-SET-BOOTSTRAP.md` | BST — naive set theory metalanguage (Level-0 root) |
| `DOMAIN-SYNTAX.md` | SYN — formation of well-formed expressions |
| `DOMAIN-SEMANTICS.md` | SEM — meaning assignment, structures, truth, models |
| `DOMAIN-DEDUCTION.md` | DED — proof systems, derivations, provability |
| `DOMAIN-COMPUTATION.md` | CMP — computable functions, decidability, Turing machines |
| `DOMAIN-SET-FORMAL.md` | SET — ZFC as a first-order theory (Level-1) |
| `CROSS-DOMAIN-MAP.md` | Ownership table, dependency graph, 13 composition patterns, variant matrix |
| `GAP-ANALYSIS.md` | OL coverage mapping, domain sufficiency argument, gap identification |

## Relationship to OpenLogic

This taxonomy systematizes the conceptual content of the [OpenLogic](https://github.com/OpenLogicProject/OpenLogic) textbook. OpenLogic provides a comprehensive, modular logic textbook (~1000+ pages, 20 topic areas). This taxonomy provides the "periodic table" underneath — the irreducible concepts, their ownership, their dependencies, and the composition patterns that generate the major theorems.

Every OL chapter maps to one or more taxonomy domains and composition patterns (see GAP-ANALYSIS.md for the complete mapping). The taxonomy can serve as:
- A **concept index** for navigating OpenLogic by underlying structure
- A **dependency checker** for understanding prerequisites
- A **completeness certificate** showing that the domains cover all of OL's scope
- A **foundation** for future phases: compressing OL content against the taxonomy (Phase 3) and recomposing a lean textbook (Phase 4)
