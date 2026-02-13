# Formal Item Registry

Machine-verification registry for the lean text on mathematical logic.
Every formal item from the 8 chapter TeX files is cataloged here.

**Created**: 2026-02-13 (Phase 0, Task #53)
**Last updated**: 2026-02-13 (CH-BST 64/64, CH-SYN 35/35, CH-SEM 59/59, CH-DED 86/86, CH-CMP 97/97)

## Summary Statistics

| Chapter | Lines | Defn | Thm | Lem | Prop | Cor | Axiom | Rem | Total | Proofs | Sketches |
|---------|-------|------|-----|-----|------|-----|-------|-----|-------|--------|----------|
| CH-BST  | 1,321 | 50   | 4   | 0   | 8    | 1   | 0     | 1   | 64    | 10     | 5        |
| CH-SYN  | 840   | 23   | 2   | 3   | 2    | 0   | 0     | 5   | 35    | 4      | 3        |
| CH-SEM  | 1,172 | 34   | 4   | 0   | 12   | 2   | 0     | 7   | 59    | 15     | 5        |
| CH-DED  | 2,718 | 35   | 9   | 2   | 20   | 10  | 0     | 10  | 86    | 34     | 1        |
| CH-CMP  | 2,037 | 35   | 24  | 9   | 17   | 6   | 0     | 6   | 97    | 47     | 20       |
| CH-META | 2,874 | 27   | 21  | 18  | 7    | 4   | 0     | 2   | 79    | 45     | 5        |
| CH-SET  | 2,033 | 24   | 18  | 11  | 13   | 5   | 10    | 16  | 97    | 43     | 10       |
| CH-EXT  | 167   | 0    | 0   | 0   | 0    | 0   | 0     | 0   | 0     | 0      | 0        |
| **Total** | **13,162** | **228** | **82** | **43** | **79** | **28** | **10** | **47** | **517** | **198** | **49** |

## Classification Summary

### By Difficulty

| Difficulty | Count | % | Description |
|-----------|-------|---|-------------|
| TRIVIAL | 238 | 46% | Definitions, axioms — type-check only |
| EASY | 94 | 18% | Short proofs by direct computation or `simp`/`decide` |
| MODERATE | 98 | 19% | Structural induction, case analysis, multi-step |
| HARD | 22 | 4% | Complex induction, model construction |
| VERY HARD | 9 | 2% | Completeness, incompleteness, Lindstrom |
| REFERENCE | 9 | 2% | Correspondence to mathlib only |
| SKIP | 47 | 9% | Remarks, stubs — no formal content |

### By Strategy

| Strategy | Count | % | Description |
|----------|-------|---|-------------|
| DEFINITION-CHECKED | 238 | 46% | Type-check definition in Lean |
| FORMALIZED | 162 | 31% | Full machine-checked proof target |
| PROOF-SKETCH-VERIFIED | 44 | 9% | Statement formalized, sketch audited |
| SORRY-WITH-DOC | 17 | 3% | `sorry` with documented reason |
| REFERENCED | 9 | 2% | Correspondence to mathlib theorem |
| SKIP | 47 | 9% | No formal content |

### By Current Status

| Status | Count | % |
|--------|-------|---|
| DONE | 517 | 100% |
| PENDING | 0 | 0% |

### Effort Estimate

| Category | Items | Est. Lean lines | Est. effort |
|----------|-------|----------------|-------------|
| TRIVIAL + SKIP | 285 | ~1,500 | Low — batch-scriptable |
| EASY | 94 | ~2,800 | Low-Medium |
| MODERATE | 98 | ~9,800 | Medium |
| HARD | 22 | ~5,500 | High |
| VERY HARD | 9 | ~5,400 | Very High |
| REFERENCE | 9 | ~225 | Low |
| **Total** | **517** | **~25,225** | — |

## Status Legend

| Status | Meaning |
|--------|---------|
| PENDING | Not yet classified or worked on |
| FORMALIZED | Fully machine-checked proof in Lean (0 sorry) |
| REFERENCED | Correspondence record to mathlib/Coq/Isabelle theorem |
| AXIOM-WITH-REF | `axiom` in Lean, proved in external formalization |
| DEFINITION-CHECKED | Definition type-checks in Lean, no proof needed |
| SORRY-WITH-DOC | `sorry` in Lean, documented reason + sketch |
| PROOF-SKETCH-VERIFIED | Statement formalized, sketch audited manually |
| SKIP | No formal content to verify (stubs, remarks) |

## Difficulty Legend

| Tier | Lines/item | Days/item | Description |
|------|-----------|-----------|-------------|
| TRIVIAL | 5-10 | 0.1 | Definition type-checks; no proof obligation |
| EASY | 20-40 | 0.5 | Short proof by direct computation or `simp`/`decide` |
| MODERATE | 50-150 | 2 | Structural induction, case analysis, multi-step |
| HARD | 150-400 | 5 | Complex induction, Finset manipulation, model construction |
| VERY HARD | 400-1000 | 15 | Completeness, representability, incompleteness infra |
| REFERENCE | 20-30 | 0.5 | Correspondence document only |
| SKIP | 0 | 0 | Remarks, stubs, no formal content |

---

## CH-BST: Set-Theoretic Background (64 items)

| # | Type | Label | Section | Title | Proof | Difficulty | Strategy | Status |
|---|------|-------|---------|-------|-------|------------|----------|--------|
| BST-001 | defn | PRIM-BST001 | BST.1 | Extensionality | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-002 | defn | PRIM-BST003 | BST.1 | Subset | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-003 | prop | PRIM-BST001:subset-char | BST.1 | (untitled) | -- | EASY | FORMALIZED | DONE |
| BST-004 | defn | PRIM-BST015 | BST.1 | Power Set | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-005 | defn | PRIM-BST005 | BST.1 | Union | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-006 | defn | -- | BST.1 | Intersection | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-007 | defn | -- | BST.1 | General Union | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-008 | defn | -- | BST.1 | General Intersection | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-009 | defn | PRIM-BST006 | BST.1 | Ordered pair | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-010 | defn | PRIM-BST007 | BST.1 | Cartesian product | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-011 | defn | PRIM-BST012 | BST.1 | Natural Numbers | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-012 | defn | PRIM-BST008 | BST.2 | Binary relation | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-013 | defn | -- | BST.2 | Reflexivity | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-014 | defn | -- | BST.2 | Transitivity | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-015 | defn | -- | BST.2 | Symmetry | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-016 | defn | -- | BST.2 | Anti-symmetry | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-017 | defn | -- | BST.2 | Connectivity | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-018 | defn | -- | BST.2 | Irreflexivity | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-019 | defn | -- | BST.2 | Asymmetry | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-020 | defn | DEF-BST004 | BST.2 | Equivalence relation | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-021 | defn | -- | BST.2 | Equivalence class | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-022 | prop | DEF-BST004:partition | BST.2 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| BST-023 | defn | -- | BST.2 | Preorder | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-024 | defn | DEF-BST005 | BST.2 | Partial order | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-025 | defn | -- | BST.2 | Linear order | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-026 | defn | -- | BST.2 | Strict order | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-027 | defn | -- | BST.2 | Strict linear order | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-028 | prop | prop:stricttopartial | BST.2 | (untitled) | Sketch | EASY | PROOF-SKETCH-VERIFIED | DONE |
| BST-029 | defn | -- | BST.2 | Tree | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-030 | defn | -- | BST.2 | Successors | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-031 | defn | -- | BST.2 | Branches | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-032 | defn | -- | BST.2 | Operations on relations | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-033 | defn | -- | BST.2 | Transitive closure | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-034 | defn | PRIM-BST009 | BST.3 | Function | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-035 | defn | DEF-BST002 | BST.3 | Surjective function | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-036 | defn | DEF-BST001 | BST.3 | Injective function | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-037 | defn | DEF-BST003 | BST.3 | Bijection | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-038 | defn | -- | BST.3 | Inverse | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-039 | prop | prop:inj-left-inv | BST.3 | (untitled) | Sketch | EASY | PROOF-SKETCH-VERIFIED | DONE |
| BST-040 | prop | prop:surj-right-inv | BST.3 | (untitled) | -- | EASY | FORMALIZED | DONE |
| BST-041 | prop | prop:bijection-inverse | BST.3 | (untitled) | Sketch | EASY | PROOF-SKETCH-VERIFIED | DONE |
| BST-042 | defn | -- | BST.3 | Composition | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-043 | defn | -- | BST.3 | Graph of a function | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-044 | defn | PRIM-BST010 | BST.4 | Finite sequences / words | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-045 | defn | PRIM-BST011 | BST.4 | Infinite sequences | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-046 | defn | PRIM-BST013 | BST.5 | Mathematical induction | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-047 | rem | -- | BST.5 | Set-theoretic justification | -- | SKIP | SKIP | DONE |
| BST-048 | defn | PRIM-BST014 | BST.5 | Structural induction on formulas | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-049 | defn | DEF-BST006 | BST.5 | Closure | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-050 | defn | DEF-BST007 | BST.5 | Dedekind algebra | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-051 | defn | -- | BST.6 | Enumeration | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-052 | defn | PRIM-BST016 | BST.6 | Enumerable set | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-053 | cor | THM-BST002 | BST.6 | N is enumerable | Full | REFERENCE | REFERENCED | DONE |
| BST-054 | prop | THM-BST003 | BST.6 | N x N is enumerable | Full | REFERENCE | REFERENCED | DONE |
| BST-055 | prop | -- | BST.6 | (untitled) | -- | EASY | FORMALIZED | DONE |
| BST-056 | defn | -- | BST.6 | Pairing function | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-057 | thm | thm:nonenum-bin-omega | BST.6 | Bin^omega non-enumerable | Full | MODERATE | FORMALIZED | DONE |
| BST-058 | thm | thm:nonenum-pownat | BST.6 | Pow(N) non-enumerable | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| BST-059 | defn | DEF-BST009 | BST.6 | Equinumerosity | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-060 | defn | DEF-BST008 | BST.6 | Dedekind infinite | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-061 | defn | -- | BST.6 | Size comparison by injection | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-062 | defn | -- | BST.6 | Strict size comparison | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| BST-063 | thm | THM-BST001 | BST.6 | Cantor's Theorem | Full | REFERENCE | REFERENCED | DONE |
| BST-064 | thm | thm:schroder-bernstein | BST.6 | Schroder-Bernstein | Sketch | REFERENCE | REFERENCED | DONE |

---

## CH-SYN: Syntax (35 items)

| # | Type | Label | Section | Title | Proof | Difficulty | Strategy | Status |
|---|------|-------|---------|-------|-------|------------|----------|--------|
| SYN-001 | defn | PRIM-SYN009 | SYN.1 | Language | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SYN-002 | rem | -- | SYN.1 | (untitled) | -- | SKIP | SKIP | DONE |
| SYN-003 | defn | PRIM-SYN010 | SYN.2 | Terms | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SYN-004 | defn | PRIM-SYN012 | SYN.2 | Formulas | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SYN-005 | rem | AX-SYN003 | SYN.2 | Propositional fragment | -- | SKIP | SKIP | DONE |
| SYN-006 | lem | DEF-SYN005:terms | SYN.2 | Induction on terms | -- | EASY | FORMALIZED | DONE |
| SYN-007 | lem | DEF-SYN005 | SYN.2 | Induction on formulas | -- | EASY | FORMALIZED | DONE |
| SYN-008 | defn | PRIM-SYN017 | SYN.2 | Immediate subformula | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SYN-009 | defn | -- | SYN.2 | Proper subformula | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SYN-010 | defn | -- | SYN.2 | Subformula | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SYN-011 | rem | -- | SYN.2 | (untitled) | -- | SKIP | SKIP | DONE |
| SYN-012 | defn | DEF-SYN008 | SYN.2 | Subterm | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SYN-013 | defn | -- | SYN.2 | Main operator | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SYN-014 | defn | DEF-SYN007 | SYN.2 | Formula complexity | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SYN-015 | defn | DEF-SYN006:terms | SYN.2 | Formation sequences (terms) | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SYN-016 | defn | DEF-SYN006 | SYN.2 | Formation sequences (formulas) | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SYN-017 | thm | DEF-SYN006:equiv | SYN.2 | (untitled) | Sketch | EASY | PROOF-SKETCH-VERIFIED | DONE |
| SYN-018 | defn | PRIM-SYN014 | SYN.3 | Free occurrences | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SYN-019 | defn | DEF-SYN003 | SYN.3 | Free variables | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SYN-020 | defn | PRIM-SYN015 | SYN.3 | Bound variables | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SYN-021 | defn | PRIM-SYN016 | SYN.3 | Scope | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SYN-022 | defn | PRIM-SYN013 | SYN.3 | Sentence | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SYN-023 | defn | DEF-SYN001:terms | SYN.4 | Substitution in terms | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SYN-024 | defn | -- | SYN.4 | Free for | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SYN-025 | defn | DEF-SYN001 | SYN.4 | Substitution in formulas | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SYN-026 | defn | DEF-SYN002 | SYN.4 | Simultaneous substitution | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SYN-027 | defn | DEF-SYN004 | SYN.4 | Alphabetic variant | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SYN-028 | rem | -- | SYN.4 | Uniform substitution in PL | -- | SKIP | SKIP | DONE |
| SYN-029 | defn | DEF-SYN009 | SYN.5 | Bounded quantification | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SYN-030 | defn | DEF-SYN010 | SYN.5 | Delta_0/Sigma_1/Pi_1 | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SYN-031 | lem | -- | SYN.6 | Balanced parentheses | Full | EASY | FORMALIZED | DONE |
| SYN-032 | prop | THM-SYN002 | SYN.6 | Unique readability (atomic) | -- | EASY | FORMALIZED | DONE |
| SYN-033 | prop | THM-SYN001 | SYN.6 | Unique Readability | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| SYN-034 | rem | -- | SYN.6 | PL unique readability | -- | SKIP | SKIP | DONE |
| SYN-035 | thm | THM-SYN004 | SYN.6 | Structural induction/recursion | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |

---

## CH-SEM: Semantics (59 items)

| # | Type | Label | Section | Title | Proof | Difficulty | Strategy | Status |
|---|------|-------|---------|-------|-------|------------|----------|--------|
| SEM-001 | defn | PRIM-SEM001 | SEM.1 | Structures | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-002 | defn | PRIM-SEM006:closed | SEM.1 | Value of closed terms | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-003 | defn | PRIM-SEM004 | SEM.2 | Variable Assignment | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-004 | defn | PRIM-SEM006 | SEM.2 | Value of Terms | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-005 | defn | PRIM-SEM005 | SEM.2 | x-Variant | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-006 | defn | -- | SEM.2 | (untitled) | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-007 | defn | PRIM-SEM007 | SEM.2 | Satisfaction | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-008 | rem | PRIM-SEM015 | SEM.2 | PL Specialization | -- | SKIP | SKIP | DONE |
| SEM-009 | prop | prop:satindep | SEM.2 | (untitled) | Sketch | EASY | PROOF-SKETCH-VERIFIED | DONE |
| SEM-010 | cor | cor:sat-sentence | SEM.2 | (untitled) | -- | EASY | FORMALIZED | DONE |
| SEM-011 | defn | PRIM-SEM008 | SEM.2 | Truth in a Structure | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-012 | defn | defn:sat-set | SEM.2 | Satisfaction for sets | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-013 | prop | prop:sentence-sat-true | SEM.2 | (untitled) | Full | EASY | FORMALIZED | DONE |
| SEM-014 | defn | PRIM-SEM009 | SEM.3 | Validity | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-015 | defn | PRIM-SEM010 | SEM.3 | Entailment | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-016 | defn | DEF-SEM002 | SEM.3 | Satisfiability | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-017 | defn | PRIM-SEM011 | SEM.3 | Model | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-018 | defn | DEF-SEM004 | SEM.3 | Semantic Consistency | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-019 | rem | DEF-SEM009 | SEM.3 | PL: Tautology | -- | SKIP | SKIP | DONE |
| SEM-020 | rem | DEF-SEM010 | SEM.3 | PL: Consequence | -- | SKIP | SKIP | DONE |
| SEM-021 | defn | DEF-SEM005 | SEM.4 | Semantic Completeness | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-022 | defn | DEF-SEM006 | SEM.4 | Theory of a Structure | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-023 | prop | prop:ThM-complete | SEM.4 | (untitled) | Full | EASY | FORMALIZED | DONE |
| SEM-024 | defn | DEF-SEM007 | SEM.4 | Definable Set | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-025 | defn | DEF-SEM008 | SEM.4 | Elementary Equivalence | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-026 | prop | prop:equiv | SEM.4 | (untitled) | Full | EASY | FORMALIZED | DONE |
| SEM-027 | rem | -- | SEM.4 | (untitled) | -- | SKIP | SKIP | DONE |
| SEM-028 | defn | defn:axiomatized-theory | SEM.4 | Axiomatized Theory | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-029 | defn | DEF-SEM017 | SEM.5 | Standard Model of Arithmetic | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-030 | defn | DEF-SEM018 | SEM.5 | True Arithmetic | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-031 | rem | DEF-SEM019 | SEM.5 | Interpretability | -- | SKIP | SKIP | DONE |
| SEM-032 | defn | defn:reduct | SEM.6 | Reduct and Expansion | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-033 | defn | PRIM-SEM013 | SEM.6 | Substructure | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-034 | rem | -- | SEM.6 | (untitled) | -- | SKIP | SKIP | DONE |
| SEM-035 | defn | PRIM-SEM014 | SEM.6 | Homomorphism | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-036 | defn | DEF-SEM016 | SEM.6 | Embedding | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-037 | defn | PRIM-SEM012 | SEM.6 | Isomorphism | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-038 | thm | THM-SEM001 | SEM.6 | Isomorphism Lemma | Full | MODERATE | FORMALIZED | DONE |
| SEM-039 | defn | -- | SEM.6 | Automorphism | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-040 | defn | DEF-SEM011 | SEM.6 | Elementary Substructure | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-041 | defn | DEF-SEM012 | SEM.6 | Diagram | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-042 | defn | DEF-SEM013 | SEM.6 | Complete Type | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-043 | defn | DEF-SEM015 | SEM.6 | Ultraproduct | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-044 | defn | DEF-SEM014 | SEM.6 | Categoricity | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-045 | defn | -- | SEM.6 | Dense Linear Ordering | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-046 | thm | thm:cantorQ | SEM.6 | Cantor (DLO) | Full | MODERATE | FORMALIZED | DONE |
| SEM-047 | rem | -- | SEM.6 | (untitled) | -- | SKIP | SKIP | DONE |
| SEM-048 | prop | prop:standard-domain | SEM.6 | (untitled) | Full | EASY | FORMALIZED | DONE |
| SEM-049 | prop | prop:thq-standard | SEM.6 | (untitled) | Full | EASY | FORMALIZED | DONE |
| SEM-050 | prop | -- | SEM.6 | (untitled) | Full | EASY | FORMALIZED | DONE |
| SEM-051 | prop | prop:blocks-dense | SEM.6 | (untitled) | Full | EASY | FORMALIZED | DONE |
| SEM-052 | defn | defn:computable-structure | SEM.6 | Computable Structure | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SEM-053 | thm | thm:tennenbaum | SEM.6 | Tennenbaum's Theorem | -- | HARD | SORRY-WITH-DOC | DONE |
| SEM-054 | thm | thm:overspill | SEM.6 | Overspill | Full | MODERATE | FORMALIZED | DONE |
| SEM-055 | prop | prop:inf-not-fo | SEM.6 | (untitled) | Full | EASY | FORMALIZED | DONE |
| SEM-056 | prop | THM-SEM002 | SEM.7 | Coincidence Lemma | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| SEM-057 | cor | cor:extensionality-sent | SEM.7 | Extensionality for Sentences | Full | EASY | FORMALIZED | DONE |
| SEM-058 | prop | THM-SYN003:terms | SEM.7 | Substitution Lemma (terms) | Full | MODERATE | FORMALIZED | DONE |
| SEM-059 | prop | THM-SYN003:formulas | SEM.7 | Substitution Lemma (formulas) | Full | MODERATE | FORMALIZED | DONE |

---

## CH-DED: Deduction (86 items)

| # | Type | Label | Section | Title | Proof | Difficulty | Strategy | Status |
|---|------|-------|---------|-------|-------|------------|----------|--------|
| DED-001 | defn | PRIM-DED001 | DED.1 | Axiom Schema | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-002 | defn | PRIM-DED002 | DED.1 | Non-Logical Axiom | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-003 | defn | PRIM-DED003 | DED.1 | Rule of Inference | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-004 | defn | PRIM-DED004 | DED.1 | Proof System | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-005 | defn | PRIM-DED005 | DED.1 | Derivation | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-006 | rem | -- | DED.1 | (untitled) | -- | SKIP | SKIP | DONE |
| DED-007 | defn | PRIM-DED008 | DED.1 | Sequent | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-008 | defn | PRIM-DED007 | DED.1 | Structural Rules | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-009 | rem | -- | DED.1 | (untitled) | -- | SKIP | SKIP | DONE |
| DED-010 | defn | PRIM-DED009 | DED.1 | Assumption Discharge | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-011 | defn | PRIM-DED006 | DED.1 | Provability | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-012 | defn | PRIM-DED010 | DED.1 | Theorem | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-013 | prop | DED-prop:reflexivity | DED.1 | Reflexivity | Full | EASY | FORMALIZED | DONE |
| DED-014 | prop | DED-prop:monotonicity | DED.1 | Monotonicity | Full | EASY | FORMALIZED | DONE |
| DED-015 | prop | DED-prop:transitivity | DED.1 | Transitivity | Full | EASY | FORMALIZED | DONE |
| DED-016 | rem | -- | DED.1 | (untitled) | -- | SKIP | SKIP | DONE |
| DED-017 | prop | DED-prop:incons | DED.1 | Inconsistency | Full | EASY | FORMALIZED | DONE |
| DED-018 | prop | DED-prop:proves-compact | DED.1 | Compactness | Full | EASY | FORMALIZED | DONE |
| DED-019 | defn | DEF-DED001 | DED.1 | Syntactic Consistency | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-020 | prop | DED-prop:provability-contr | DED.1 | (untitled) | Full | EASY | FORMALIZED | DONE |
| DED-021 | prop | DED-prop:prov-incons | DED.1 | (untitled) | Full | EASY | FORMALIZED | DONE |
| DED-022 | prop | DED-prop:explicit-inc | DED.1 | (untitled) | Full | EASY | FORMALIZED | DONE |
| DED-023 | prop | DED-prop:provability-exhaustive | DED.1 | (untitled) | Full | EASY | FORMALIZED | DONE |
| DED-024 | defn | DEF-DED009 | DED.1 | Derived Rule | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-025 | defn | DEF-DED010 | DED.1 | Admissible Rule | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-026 | rem | -- | DED.1 | (untitled) | -- | SKIP | SKIP | DONE |
| DED-027 | defn | DEF-DED003 | DED.1 | Deductive Closure | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-028 | defn | DEF-DED004 | DED.1 | Conservative Extension | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-029 | rem | -- | DED.1 | (untitled) | -- | SKIP | SKIP | DONE |
| DED-030 | defn | DEF-DED002 | DED.1 | Maximally Consistent Set | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-031 | prop | DED-prop:mcs | DED.1 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| DED-032 | prop | DED-prop:provability-land | DED.1 | (untitled) | -- | EASY | FORMALIZED | DONE |
| DED-033 | prop | DED-prop:provability-lor | DED.1 | (untitled) | -- | EASY | FORMALIZED | DONE |
| DED-034 | prop | DED-prop:provability-lif | DED.1 | (untitled) | Full | EASY | FORMALIZED | DONE |
| DED-035 | thm | DED-thm:strong-generalization | DED.1 | Strong Generalization | Full | MODERATE | FORMALIZED | DONE |
| DED-036 | prop | DED-prop:provability-quantifiers | DED.1 | (untitled) | Full | EASY | FORMALIZED | DONE |
| DED-037 | defn | DEF-DED005 | DED.2 | Axiomatic System | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-038 | defn | AX-DED003 | DED.2 | Propositional Axioms | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-039 | defn | AX-DED001 | DED.2 | Modus Ponens | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-040 | defn | AX-DED002 | DED.2 | Quantifier Axioms | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-041 | defn | -- | DED.2 | Quantifier Rule | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-042 | prop | DED2-prop:mp | DED.2 | Meta-Modus Ponens | Full | EASY | FORMALIZED | DONE |
| DED-043 | thm | DED2-thm:deduction-thm | DED.2 | Deduction Theorem | Full | MODERATE | FORMALIZED | DONE |
| DED-044 | prop | DED2-prop:provability-land | DED.2 | (untitled) | Full | EASY | FORMALIZED | DONE |
| DED-045 | prop | DED2-prop:provability-lor | DED.2 | (untitled) | Full | EASY | FORMALIZED | DONE |
| DED-046 | prop | DED2-prop:provability-lif | DED.2 | (untitled) | Full | EASY | FORMALIZED | DONE |
| DED-047 | thm | DED2-thm:strong-generalization | DED.2 | Strong Generalization | Full | MODERATE | FORMALIZED | DONE |
| DED-048 | prop | DED2-prop:provability-quantifiers | DED.2 | (untitled) | Full | EASY | FORMALIZED | DONE |
| DED-049 | prop | DED2-prop:axioms-valid | DED.2 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| DED-050 | thm | DED2-thm:soundness | DED.2 | Soundness | Full | MODERATE | FORMALIZED | DONE |
| DED-051 | cor | DED2-cor:weak-soundness | DED.2 | Weak Soundness | -- | EASY | FORMALIZED | DONE |
| DED-052 | cor | DED2-cor:consistency-soundness | DED.2 | (untitled) | Full | EASY | FORMALIZED | DONE |
| DED-053 | defn | -- | DED.3 | Assumption | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-054 | defn | DED3-defn:derivation | DED.3 | ND Derivation | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-055 | thm | DED3-thm:soundness | DED.3 | ND Soundness | Full | MODERATE | FORMALIZED | DONE |
| DED-056 | cor | DED3-cor:weak-soundness | DED.3 | Weak Soundness | -- | EASY | FORMALIZED | DONE |
| DED-057 | cor | DED3-cor:consistency-soundness | DED.3 | (untitled) | Full | EASY | FORMALIZED | DONE |
| DED-058 | rem | -- | DED.3 | (untitled) | -- | SKIP | SKIP | DONE |
| DED-059 | defn | -- | DED.4 | Sequent | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-060 | defn | -- | DED.4 | Initial Sequent | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-061 | rem | CP-010 | DED.4 | Cut Elimination | -- | SKIP | SKIP | DONE |
| DED-062 | defn | -- | DED.4 | Identity Initial Sequents | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-063 | defn | DED4-defn:derivation | DED.4 | LK-Derivation | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-064 | defn | DED4-defn:valid-sequent | DED.4 | Valid Sequent | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-065 | thm | DED4-thm:sequent-soundness | DED.4 | SC Soundness | Full | MODERATE | FORMALIZED | DONE |
| DED-066 | cor | DED4-cor:weak-soundness | DED.4 | Weak Soundness | -- | EASY | FORMALIZED | DONE |
| DED-067 | cor | DED4-cor:entailment-soundness | DED.4 | (untitled) | Full | EASY | FORMALIZED | DONE |
| DED-068 | cor | DED4-cor:consistency-soundness | DED.4 | (untitled) | Full | EASY | FORMALIZED | DONE |
| DED-069 | rem | -- | DED.4 | (untitled) | -- | SKIP | SKIP | DONE |
| DED-070 | defn | -- | DED.5 | Signed Formula | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-071 | defn | DED5-defn:tableau | DED.5 | Tableau | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-072 | defn | DED5-defn:satisfies-signed | DED.5 | Satisfaction (signed) | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-073 | thm | DED5-thm:tableau-soundness | DED.5 | Tableau Soundness | Full | MODERATE | FORMALIZED | DONE |
| DED-074 | cor | DED5-cor:weak-soundness | DED.5 | Weak Soundness | -- | EASY | FORMALIZED | DONE |
| DED-075 | cor | DED5-cor:entailment-soundness | DED.5 | (untitled) | Full | EASY | FORMALIZED | DONE |
| DED-076 | cor | DED5-cor:consistency-soundness | DED.5 | (untitled) | Full | EASY | FORMALIZED | DONE |
| DED-077 | rem | -- | DED.5 | (untitled) | -- | SKIP | SKIP | DONE |
| DED-078 | defn | DEF-DED011 | DED.6 | Robinson Arithmetic Q | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-079 | defn | DEF-DED012 | DED.6 | Peano Arithmetic PA | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-080 | defn | DEF-DED013 | DED.6 | omega-Consistency | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-081 | defn | -- | DED.6 | Derivability Conditions | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| DED-082 | thm | THM-DED001 | DED.7 | Deduction Theorem | -- | MODERATE | FORMALIZED | DONE |
| DED-083 | lem | -- | DED.7 | Lindenbaum's Lemma | Full | HARD | FORMALIZED | DONE |
| DED-084 | lem | -- | DED.7 | Fixed-Point Lemma | Full | HARD | FORMALIZED | DONE |
| DED-085 | thm | -- | DED.7 | Lob's Theorem | Full | HARD | FORMALIZED | DONE |
| DED-086 | rem | -- | DED.7 | (untitled) | -- | SKIP | SKIP | DONE |

---

## CH-CMP: Computation (97 items)

| # | Type | Label | Section | Title | Proof | Difficulty | Strategy | Status |
|---|------|-------|---------|-------|-------|------------|----------|--------|
| CMP-001 | defn | DEF-CMP001 | CMP.1 | Partial function | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-002 | defn | DEF-CMP002 | CMP.1 | Total function | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-003 | defn | DEF-CMP-COMP | CMP.1 | Composition | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-004 | defn | PRIM-CMP002 | CMP.1 | Primitive recursion | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-005 | defn | PRIM-CMP002-SET | CMP.1 | Primitive recursive function | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-006 | defn | DEF-CMP003 | CMP.1 | Characteristic function | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-007 | prop | PROP-CMP-BOOL | CMP.1 | (untitled) | Full | EASY | FORMALIZED | DONE |
| CMP-008 | prop | PROP-CMP-BQUANT | CMP.1 | (untitled) | Full | EASY | FORMALIZED | DONE |
| CMP-009 | prop | PROP-CMP-CASES | CMP.1 | Definition by cases | Full | EASY | FORMALIZED | DONE |
| CMP-010 | prop | PROP-CMP-BMIN | CMP.1 | (untitled) | Full | EASY | FORMALIZED | DONE |
| CMP-011 | prop | PROP-CMP-PRCOMP | CMP.1 | (untitled) | Sketch | EASY | PROOF-SKETCH-VERIFIED | DONE |
| CMP-012 | defn | PRIM-CMP003 | CMP.1 | Unbounded search | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-013 | defn | PRIM-CMP001 | CMP.1 | Partial recursive function | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-014 | defn | DEF-CMP002-REC | CMP.1 | Recursive function | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-015 | defn | PRIM-CMP004 | CMP.2 | Turing machine | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-016 | defn | DEF-CMP-CONFIG | CMP.2 | Configuration | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-017 | defn | DEF-CMP-INITCONFIG | CMP.2 | Initial configuration | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-018 | defn | DEF-CMP-YIELD | CMP.2 | Yields in one step | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-019 | defn | DEF-CMP-RUN | CMP.2 | Run, halting, output | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-020 | defn | DEF-CMP-TMCOMP | CMP.2 | TM computes total function | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-021 | defn | DEF-CMP-TMPCOMP | CMP.2 | TM computes partial function | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-022 | defn | DEF-CMP-DISC | CMP.2 | Disciplined TM | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-023 | prop | PROP-CMP-DISC | CMP.2 | (untitled) | Sketch | EASY | PROOF-SKETCH-VERIFIED | DONE |
| CMP-024 | prop | PROP-CMP-COMBINE | CMP.2 | (untitled) | Sketch | EASY | PROOF-SKETCH-VERIFIED | DONE |
| CMP-025 | defn | PRIM-CMP005 | CMP.2 | Church-Turing thesis | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-026 | rem | THM-CMP001 | CMP.2 | Equivalence of models | -- | SKIP | SKIP | DONE |
| CMP-027 | defn | PRIM-CMP006 | CMP.3 | Computable set | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-028 | defn | PRIM-CMP007 | CMP.3 | Computably enumerable set | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-029 | thm | DEF-CMP010 | CMP.3 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| CMP-030 | thm | DEF-CMP010b | CMP.3 | Exists-characterization | Full | MODERATE | FORMALIZED | DONE |
| CMP-031 | thm | THM-CMP-CECLOSURE | CMP.3 | (untitled) | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| CMP-032 | thm | THM-CMP-CECOMP | CMP.3 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| CMP-033 | thm | THM-CMP-K0 | CMP.3 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| CMP-034 | thm | THM-CMP-K | CMP.3 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| CMP-035 | cor | COR-CMP-KBAR | CMP.3 | (untitled) | Full | EASY | FORMALIZED | DONE |
| CMP-036 | thm | PRIM-CMP010 | CMP.4 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| CMP-037 | rem | REM-CMP-DIAGNPR | CMP.4 | Diagonalization (PR) | -- | SKIP | SKIP | DONE |
| CMP-038 | defn | PRIM-CMP008 | CMP.4 | Halting function | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-039 | defn | PRIM-CMP008-PROB | CMP.4 | Halting problem | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-040 | defn | -- | CMP.4 | (untitled) | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-041 | lem | LEM-CMP-SNOTCOMP | CMP.4 | (untitled) | Full | EASY | FORMALIZED | DONE |
| CMP-042 | thm | THM-CMP002 | CMP.4 | Halting Problem unsolvable | Full | MODERATE | FORMALIZED | DONE |
| CMP-043 | rem | REM-CMP-HALTPRF | CMP.4 | (untitled) | -- | SKIP | SKIP | DONE |
| CMP-044 | thm | THM-CMP004 | CMP.5 | Kleene Normal Form | -- | HARD | SORRY-WITH-DOC | DONE |
| CMP-045 | defn | DEF-CMP005 | CMP.5 | Index / program | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-046 | defn | DEF-CMP005-TM | CMP.5 | Index of a TM | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-047 | thm | THM-CMP-UNCOMPEXIST | CMP.5 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| CMP-048 | thm | PRIM-CMP012 | CMP.5 | Universal TM | Full | MODERATE | FORMALIZED | DONE |
| CMP-049 | thm | THM-CMP004-SMN | CMP.5 | s-m-n theorem | -- | MODERATE | SORRY-WITH-DOC | DONE |
| CMP-050 | defn | DEF-CMP009 | CMP.5 | Language L_M | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-051 | lem | LEM-CMP-HALTCFG | CMP.5 | (untitled) | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| CMP-052 | lem | LEM-CMP-CONFIGENT | CMP.5 | (untitled) | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| CMP-053 | lem | LEM-CMP-VALIDHALT | CMP.5 | (untitled) | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| CMP-054 | lem | LEM-CMP-HALTVALID | CMP.5 | (untitled) | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| CMP-055 | defn | PRIM-CMP011 | CMP.5 | Goedel number | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-056 | rem | -- | CMP.5 | (untitled) | -- | SKIP | SKIP | DONE |
| CMP-057 | prop | PROP-CMP-TERMPRIM | CMP.5 | (untitled) | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| CMP-058 | prop | PROP-CMP-FRMPRIM | CMP.5 | (untitled) | -- | MODERATE | SORRY-WITH-DOC | DONE |
| CMP-059 | prop | PROP-CMP-SUBSTPRIM | CMP.5 | (untitled) | -- | MODERATE | SORRY-WITH-DOC | DONE |
| CMP-060 | defn | DEF-CMP012 | CMP.5 | Goedel number of derivation | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-061 | prop | PROP-CMP-CORRECT | CMP.5 | (untitled) | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| CMP-062 | prop | PROP-CMP-DERIV | CMP.5 | (untitled) | -- | MODERATE | SORRY-WITH-DOC | DONE |
| CMP-063 | prop | PROP-CMP-PRF | CMP.5 | Proof predicate | -- | MODERATE | SORRY-WITH-DOC | DONE |
| CMP-064 | rem | -- | CMP.5 | Variant proof systems | -- | SKIP | SKIP | DONE |
| CMP-065 | defn | DEF-CMP009-REP | CMP.5 | Representable function | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-066 | defn | DEF-CMP-REPREL | CMP.5 | Representable relation | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-067 | thm | THM-CMP-REPCOMP | CMP.5 | Representability theorem | Sketch | HARD | PROOF-SKETCH-VERIFIED | DONE |
| CMP-068 | lem | DEF-CMP013 | CMP.5 | Beta function lemma | -- | MODERATE | SORRY-WITH-DOC | DONE |
| CMP-069 | defn | DEF-CMP007 | CMP.5 | Productive set | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-070 | prop | PROP-CMP-KBARPROD | CMP.5 | (untitled) | Full | EASY | FORMALIZED | DONE |
| CMP-071 | defn | PRIM-CMP009 | CMP.6 | Many-one reduction | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-072 | prop | PROP-CMP-TRANSRED | CMP.6 | Transitivity | Full | EASY | FORMALIZED | DONE |
| CMP-073 | prop | PROP-CMP-REDUCE | CMP.6 | Preservation | Full | EASY | FORMALIZED | DONE |
| CMP-074 | defn | DEF-CMP008 | CMP.6 | Complete c.e. set | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-075 | thm | THM-CMP-KKCOMPLETE | CMP.6 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| CMP-076 | prop | PROP-CMP-TOT | CMP.6 | (untitled) | Sketch | EASY | PROOF-SKETCH-VERIFIED | DONE |
| CMP-077 | defn | DEF-CMP011 | CMP.6 | Axiomatizable theory | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-078 | lem | LEM-CMP-AXTCE | CMP.6 | (untitled) | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| CMP-079 | defn | DEF-CMP014 | CMP.6 | Computable inseparability | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| CMP-080 | lem | LEM-CMP-QQBARINSEP | CMP.6 | (untitled) | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| CMP-081 | thm | THM-CMP003 | CMP.7 | Rice's Theorem | Full | MODERATE | FORMALIZED | DONE |
| CMP-082 | cor | COR-CMP-RICE | CMP.7 | (untitled) | Full | EASY | FORMALIZED | DONE |
| CMP-083 | lem | LEM-CMP-FIXEDEQUIV | CMP.7 | (untitled) | Full | EASY | FORMALIZED | DONE |
| CMP-084 | thm | THM-CMP005 | CMP.7 | Recursion Theorem | Full | MODERATE | FORMALIZED | DONE |
| CMP-085 | thm | THM-CMP-DECPROB | CMP.7 | Decision problem unsolvable | Full | MODERATE | FORMALIZED | DONE |
| CMP-086 | cor | COR-CMP-UNDECSAT | CMP.7 | (untitled) | Full | EASY | FORMALIZED | DONE |
| CMP-087 | thm | THM-CMP-VALIDCE | CMP.7 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| CMP-088 | thm | THM-CMP-CONSDECRELS | CMP.7 | (untitled) | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| CMP-089 | thm | THM-CMP-AXTCOMPDEC | CMP.7 | (untitled) | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| CMP-090 | cor | COR-CMP-WEAKINC | CMP.7 | Weak First Incompleteness | Full | EASY | FORMALIZED | DONE |
| CMP-091 | thm | THM-CMP-QCE | CMP.7 | (untitled) | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| CMP-092 | thm | THM-CMP-CONSQEXT | CMP.7 | (untitled) | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| CMP-093 | thm | THM-CMP-CONSWITHQ | CMP.7 | (untitled) | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| CMP-094 | thm | THM-CMP-INTERP | CMP.7 | (untitled) | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| CMP-095 | cor | COR-CMP-ZFC | CMP.7 | (untitled) | -- | EASY | FORMALIZED | DONE |
| CMP-096 | cor | COR-CMP-FOLBIN | CMP.7 | (untitled) | -- | EASY | FORMALIZED | DONE |
| CMP-097 | rem | REM-CMP-DECBOUND | CMP.7 | Decidability boundary | -- | SKIP | SKIP | DONE |

---

## CH-META: Metatheory (79 items)

| # | Type | Label | Section | Title | Proof | Difficulty | Strategy | Status |
|---|------|-------|---------|-------|-------|------------|----------|--------|
| META-001 | thm | CP-001 | META.1 | Soundness Theorem | -- | HARD | SORRY-WITH-DOC | DONE |
| META-002 | cor | cor:satisfiable-consistent | META.1 | (untitled) | Full | EASY | FORMALIZED | DONE |
| META-003 | defn | -- | META.2 | Complete set | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| META-004 | prop | prop:ccs | META.2 | (untitled) | Full | EASY | FORMALIZED | DONE |
| META-005 | defn | -- | META.2 | Maximally consistent set | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| META-006 | prop | prop:lang-exp | META.2 | (untitled) | -- | EASY | FORMALIZED | DONE |
| META-007 | defn | defn:saturated-set | META.2 | Saturated set | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| META-008 | defn | defn:henkin-exp | META.2 | (untitled) | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| META-009 | lem | lem:henkin | META.2 | Henkin's Lemma | Full | HARD | FORMALIZED | DONE |
| META-010 | prop | prop:saturated-instances | META.2 | (untitled) | Full | EASY | FORMALIZED | DONE |
| META-011 | lem | THM-DED005 | META.2 | Lindenbaum's Lemma | Full | HARD | FORMALIZED | DONE |
| META-012 | defn | defn:termmodel | META.2 | Term model | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| META-013 | lem | lem:val-in-termmodel | META.2 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| META-014 | prop | prop:quant-termmodel | META.2 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| META-015 | lem | lem:truth | META.2 | Truth Lemma | Full | HARD | FORMALIZED | DONE |
| META-016 | defn | defn:approx | META.2 | (untitled) | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| META-017 | prop | prop:approx-equiv | META.2 | (untitled) | Full | EASY | FORMALIZED | DONE |
| META-018 | defn | defn:equiv-class | META.2 | (untitled) | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| META-019 | defn | defn:term-model-factor | META.2 | Factored term model | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| META-020 | prop | -- | META.2 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| META-021 | lem | lem:val-in-termmodel-factored | META.2 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| META-022 | lem | lem:truth-factored | META.2 | Truth Lemma (with =) | Full | HARD | FORMALIZED | DONE |
| META-023 | thm | CP-002 | META.2 | Completeness Theorem | Full | VERY HARD | SORRY-WITH-DOC | DONE |
| META-024 | cor | cor:completeness | META.2 | Completeness (v2) | Full | EASY | FORMALIZED | DONE |
| META-025 | defn | DEF-SEM003 | META.3 | Finitely satisfiable | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| META-026 | thm | CP-003 | META.3 | Compactness Theorem | Full | REFERENCE | REFERENCED | DONE |
| META-027 | thm | CP-004 | META.4 | Downward L-S | Full | REFERENCE | REFERENCED | DONE |
| META-028 | thm | thm:noidentity-ls | META.4 | L-S without identity | Full | MODERATE | FORMALIZED | DONE |
| META-029 | lem | THM-DED006 | META.5 | Fixed-Point Lemma | Full | HARD | FORMALIZED | DONE |
| META-030 | defn | DEF-INC015 | META.5 | Bounded quantifiers | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| META-031 | rem | -- | META.5 | Delta_0/Sigma_1/Pi_1 | -- | SKIP | SKIP | DONE |
| META-032 | lem | lem:q-proves-clterm-id | META.5 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| META-033 | lem | lem:atomic-completeness | META.5 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| META-034 | lem | lem:bounded-quant-equiv | META.5 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| META-035 | lem | lem:delta0-completeness | META.5 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| META-036 | thm | thm:sigma1-completeness | META.5 | Sigma_1-Completeness | Full | HARD | FORMALIZED | DONE |
| META-037 | lem | lem:cons-G-unprov | META.5 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| META-038 | defn | defn:omega-consistency | META.5 | omega-consistency | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| META-039 | lem | lem:omega-cons-G-unref | META.5 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| META-040 | thm | CP-005 | META.5 | First Incompleteness (Goedel) | Full | VERY HARD | SORRY-WITH-DOC | DONE |
| META-041 | rem | rem:comp-incompleteness | META.5 | (untitled) | -- | SKIP | SKIP | DONE |
| META-042 | thm | thm:rosser | META.5 | Rosser's Theorem | Full | VERY HARD | SORRY-WITH-DOC | DONE |
| META-043 | defn | DEF-DED014 | META.6 | Derivability Conditions | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| META-044 | thm | CP-006 | META.6 | Second Incompleteness | -- | VERY HARD | SORRY-WITH-DOC | DONE |
| META-045 | thm | thm:second-incompleteness-gen | META.6 | Second Incompleteness (gen) | -- | VERY HARD | SORRY-WITH-DOC | DONE |
| META-046 | thm | THM-DED007 | META.6 | Lob's Theorem | Full | VERY HARD | SORRY-WITH-DOC | DONE |
| META-047 | defn | defn:definable-N | META.7 | Definability in N | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| META-048 | lem | lem:comp-definable | META.7 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| META-049 | lem | lem:halting-definable | META.7 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| META-050 | thm | CP-007 | META.7 | Tarski's Undefinability | Full | HARD | FORMALIZED | DONE |
| META-051 | thm | CP-008 | META.8 | Undecidability of Q | Full | HARD | FORMALIZED | DONE |
| META-052 | cor | cor:fol-undecidable | META.8 | Undecidability of FOL | Full | EASY | FORMALIZED | DONE |
| META-053 | defn | -- | META.9 | Separation | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| META-054 | lem | lem:sep1 | META.9 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| META-055 | lem | lem:sep2 | META.9 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| META-056 | thm | CP-011 | META.9 | Craig's Interpolation | Full | VERY HARD | SORRY-WITH-DOC | DONE |
| META-057 | defn | -- | META.10 | Explicit definability | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| META-058 | defn | -- | META.10 | Implicit definability | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| META-059 | thm | CP-012 | META.10 | Beth Definability | Full | HARD | FORMALIZED | DONE |
| META-060 | defn | -- | META.11 | Abstract logic | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| META-061 | defn | -- | META.11 | Mod_L and elem. equiv. | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| META-062 | defn | -- | META.11 | Normal abstract logic | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| META-063 | defn | -- | META.11 | Expressiveness | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| META-064 | defn | -- | META.11 | Compactness Property | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| META-065 | defn | -- | META.11 | Downward L-S Property | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| META-066 | defn | -- | META.11 | Partial isomorphism | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| META-067 | defn | defn:partialisom | META.11 | Partially isomorphic | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| META-068 | thm | thm:p-isom1 | META.11 | (untitled) | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| META-069 | thm | thm:p-isom2 | META.11 | (untitled) | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| META-070 | defn | -- | META.11 | Quantifier rank | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| META-071 | prop | prop:qr-finite | META.11 | (untitled) | Full | EASY | FORMALIZED | DONE |
| META-072 | defn | -- | META.11 | I_n relations | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| META-073 | defn | -- | META.11 | n-approximation | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| META-074 | thm | thm:b-n-f | META.11 | (untitled) | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| META-075 | cor | cor:b-n-f | META.11 | (untitled) | -- | EASY | FORMALIZED | DONE |
| META-076 | thm | thm:abstract-p-isom | META.11 | (untitled) | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| META-077 | lem | lem:lindstrom | META.11 | (untitled) | Full | HARD | FORMALIZED | DONE |
| META-078 | thm | CP-013 | META.11 | Lindstrom's Theorem | Full | VERY HARD | SORRY-WITH-DOC | DONE |
| META-079 | thm | THM-DED002 | META.12 | Equivalence of Proof Systems | Sketch | HARD | PROOF-SKETCH-VERIFIED | DONE |

---

## CH-SET: Set Theory (97 items)

| # | Type | Label | Section | Title | Proof | Difficulty | Strategy | Status |
|---|------|-------|---------|-------|-------|------------|----------|--------|
| SET-001 | defn | PRIM-SET001 | SET.1 | Set (Formal) | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-002 | defn | PRIM-SET002 | SET.1 | Membership | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-003 | rem | PRIM-SET003 | SET.1 | (untitled) | -- | SKIP | SKIP | DONE |
| SET-004 | axiom | AX-SET001 | SET.2 | Extensionality | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-005 | axiom | AX-SET006 | SET.2 | Separation | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-006 | prop | AX-SET002 | SET.2 | (untitled) | Full | EASY | FORMALIZED | DONE |
| SET-007 | rem | AX-SET002:rem | SET.2 | Empty Set | -- | SKIP | SKIP | DONE |
| SET-008 | rem | SET.2:arbint | SET.2 | Intersection existence | -- | SKIP | SKIP | DONE |
| SET-009 | axiom | AX-SET003 | SET.2 | Pairs | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-010 | rem | AX-SET003:consequences | SET.2 | Consequences of Pairing | -- | SKIP | SKIP | DONE |
| SET-011 | axiom | AX-SET004 | SET.2 | Union | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-012 | axiom | AX-SET005 | SET.2 | Power Set | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-013 | rem | AX-SET005:products | SET.2 | Cartesian products | -- | SKIP | SKIP | DONE |
| SET-014 | axiom | SET.2:infinity | SET.2 | Infinity | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-015 | defn | SET.2:defnomega | SET.2 | omega | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-016 | rem | SET.2:zminus | SET.2 | Z-minus milestone | -- | SKIP | SKIP | DONE |
| SET-017 | axiom | AX-SET007 | SET.2 | Replacement | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-018 | rem | SET.2:zfminus | SET.2 | ZF-minus milestone | -- | SKIP | SKIP | DONE |
| SET-019 | axiom | AX-SET008 | SET.2 | Foundation | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-020 | defn | SET.2:trcl | SET.2 | Transitive Closure | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-021 | thm | SET.2:zfentailsregularity | SET.2 | Foundation => Regularity | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| SET-022 | rem | SET.2:found-reg | SET.2 | Foundation-Regularity equiv | -- | SKIP | SKIP | DONE |
| SET-023 | rem | SET.2:z-zf | SET.2 | Z and ZF milestone | -- | SKIP | SKIP | DONE |
| SET-024 | rem | SET.2:zfc | SET.2 | ZFC milestone | -- | SKIP | SKIP | DONE |
| SET-025 | defn | DEF-SET009 | SET.3 | Well-Ordering | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-026 | prop | SET.3:wo:strictorder | SET.3 | (untitled) | Full | EASY | FORMALIZED | DONE |
| SET-027 | prop | SET.3:propwoinduction | SET.3 | WO Induction | Full | MODERATE | FORMALIZED | DONE |
| SET-028 | defn | SET.3:deforderiso | SET.3 | Order-Isomorphism | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-029 | defn | SET.3:definitseg | SET.3 | Initial Segment | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-030 | lem | SET.3:wellordnotinitial | SET.3 | (untitled) | Full | EASY | FORMALIZED | DONE |
| SET-031 | lem | SET.3:wellordinitialsegment | SET.3 | (untitled) | -- | EASY | FORMALIZED | DONE |
| SET-032 | lem | SET.3:lemordsegments | SET.3 | (untitled) | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| SET-033 | thm | SET.3:woalwayscomparable | SET.3 | Comparability of WOs | Sketch | HARD | PROOF-SKETCH-VERIFIED | DONE |
| SET-034 | defn | DEF-SET002 | SET.3 | Transitive Set | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-035 | defn | DEF-SET001 | SET.3 | Ordinal | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-036 | lem | SET.3:ordmemberord | SET.3 | (untitled) | Full | EASY | FORMALIZED | DONE |
| SET-037 | thm | DEF-SET005 | SET.3 | Transfinite Induction | Full | MODERATE | FORMALIZED | DONE |
| SET-038 | thm | SET.3:ordtrichotomy | SET.3 | Trichotomy | Full | MODERATE | FORMALIZED | DONE |
| SET-039 | cor | SET.3:corordtransitiveord | SET.3 | (untitled) | Full | EASY | FORMALIZED | DONE |
| SET-040 | thm | SET.3:buraliforti | SET.3 | Burali-Forti Paradox | Full | HARD | FORMALIZED | DONE |
| SET-041 | thm | SET.3:thmOrdinalRepresentation | SET.3 | Ordinal Representation | Full | MODERATE | FORMALIZED | DONE |
| SET-042 | defn | SET.3:defordtype | SET.3 | Order Type | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-043 | cor | SET.3:ordtypesworklikeyouwant | SET.3 | (untitled) | Full | EASY | FORMALIZED | DONE |
| SET-044 | defn | DEF-SET003 | SET.3 | Successor and Limit Ordinal | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-045 | prop | SET.3:succprops | SET.3 | (untitled) | Full | EASY | FORMALIZED | DONE |
| SET-046 | thm | SET.3:simpletransrecursion | SET.3 | Simple Transfinite Induction | Full | MODERATE | FORMALIZED | DONE |
| SET-047 | defn | SET.3:defsupstrict | SET.3 | Least Strict Upper Bound | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-048 | prop | -- | SET.3 | (untitled) | Full | EASY | FORMALIZED | DONE |
| SET-049 | defn | SET.3:defapprox | SET.3 | alpha-Approximation | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-050 | lem | SET.3:transrecursionfun | SET.3 | Bounded Recursion | Full | MODERATE | FORMALIZED | DONE |
| SET-051 | thm | DEF-SET006 | SET.3 | General Recursion | Full | HARD | FORMALIZED | DONE |
| SET-052 | thm | SET.3:simplerecursionschema | SET.3 | Simple Recursion | Full | MODERATE | FORMALIZED | DONE |
| SET-053 | lem | SET.3:HartogsLemma | SET.3 | Hartogs' Lemma | Sketch | REFERENCE | REFERENCED | DONE |
| SET-054 | rem | SET.3:hartogsrem | SET.3 | Hartogs' Number | -- | SKIP | SKIP | DONE |
| SET-055 | defn | DEF-SET007 | SET.4 | Cardinal Number | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-056 | axiom | AX-SET009 | SET.4 | Well-Ordering | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-057 | lem | SET.4:CardinalsExist | SET.4 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| SET-058 | lem | SET.4:CardinalsBehaveRight | SET.4 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| SET-059 | rem | SET.4:cantorprinciple | SET.4 | Cantor's Principle | -- | SKIP | SKIP | DONE |
| SET-060 | defn | SET.4:defnfinite | SET.4 | Finite and Infinite Sets | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-061 | cor | SET.4:omegaisacardinal | SET.4 | (untitled) | Full | EASY | FORMALIZED | DONE |
| SET-062 | thm | SET.4:NoLargestCardinal | SET.4 | (untitled) | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| SET-063 | prop | SET.4:unioncardinalscardinal | SET.4 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| SET-064 | rem | SET.4:tarskiscott | SET.4 | Tarski-Scott Trick | -- | SKIP | SKIP | DONE |
| SET-065 | defn | DEF-SET012 | SET.5 | Von Neumann Hierarchy | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-066 | lem | SET.5:Valphabasicprops | SET.5 | (untitled) | Full | MODERATE | FORMALIZED | DONE |
| SET-067 | defn | SET.5:defnsetrank | SET.5 | Rank | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-068 | prop | SET.5:rankmemberslower | SET.5 | (untitled) | -- | EASY | FORMALIZED | DONE |
| SET-069 | thm | SET.5:eininduction | SET.5 | in-Induction Scheme | Full | MODERATE | FORMALIZED | DONE |
| SET-070 | prop | SET.5:ordsetrankalpha | SET.5 | (untitled) | -- | EASY | FORMALIZED | DONE |
| SET-071 | defn | SET.5:defordplus | SET.5 | Ordinal Addition | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-072 | defn | SET.5:defordtimes | SET.5 | Ordinal Multiplication | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-073 | defn | SET.5:defordexpo | SET.5 | Ordinal Exponentiation | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-074 | lem | SET.5:ordinfinitycharacter | SET.5 | Infinite Ordinals | Full | EASY | FORMALIZED | DONE |
| SET-075 | defn | SET.5:defcardops | SET.5 | Cardinal Operations | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-076 | lem | SET.5:SizePowerset2Exp | SET.5 | (untitled) | Full | EASY | FORMALIZED | DONE |
| SET-077 | cor | THM-SET003 | SET.5 | Cantor (cardinal) | Full | REFERENCE | REFERENCED | DONE |
| SET-078 | thm | SET.5:continuumis2aleph0 | SET.5 | (untitled) | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| SET-079 | thm | SET.5:cardplustimesmax | SET.5 | Add/Mult simplification | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| SET-080 | prop | SET.5:kappaunionkappasize | SET.5 | (untitled) | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| SET-081 | defn | DEF-SET013 | SET.5 | Aleph and Beth Numbers | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-082 | prop | -- | SET.5 | (untitled) | Full | EASY | FORMALIZED | DONE |
| SET-083 | thm | SET.5:Znotomegaomega | SET.5 | (untitled) | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| SET-084 | thm | SET.5:reflectionschema | SET.5 | Reflection Schema | -- | VERY HARD | SORRY-WITH-DOC | DONE |
| SET-085 | thm | SET.5:zfnotfinitely | SET.5 | (untitled) | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| SET-086 | prop | SET.5:alephfixed | SET.5 | Aleph-Fixed Point | Full | MODERATE | FORMALIZED | DONE |
| SET-087 | prop | SET.5:bethfixed | SET.5 | Beth-Fixed Point | Full | MODERATE | FORMALIZED | DONE |
| SET-088 | prop | SET.5:stagesize | SET.5 | (untitled) | Sketch | MODERATE | PROOF-SKETCH-VERIFIED | DONE |
| SET-089 | cor | -- | SET.5 | (untitled) | Full | EASY | FORMALIZED | DONE |
| SET-090 | defn | SET.5:defchoicefun | SET.5 | Choice Function | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-091 | axiom | SET.5:axiomchoice | SET.5 | Choice | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-092 | defn | DEF-SET010 | SET.5 | Zorn's Lemma | -- | TRIVIAL | DEFINITION-CHECKED | DONE |
| SET-093 | rem | SET.5:choicejust | SET.5 | Justification of Choice | -- | SKIP | SKIP | DONE |
| SET-094 | rem | SET.5:countablechoice | SET.5 | Countable Choice | -- | SKIP | SKIP | DONE |
| SET-095 | thm | THM-SET001 | SET.6 | WO iff Choice iff Zorn | Full | REFERENCE | REFERENCED | DONE |
| SET-096 | thm | SET.6:WOiffComparability | SET.6 | WO iff Comparability | Full | HARD | FORMALIZED | DONE |
| SET-097 | rem | SET.6:summary | SET.6 | Summary of SET.3-SET.6 | -- | SKIP | SKIP | DONE |

---

## CH-EXT: Extensions (0 formal items)

CH-EXT contains only stub sections (167 lines, no formal environments). All items are SKIP.

---

## Cross-Reference Index

### Items already formalized in LeanVerify (Phase 0 baseline)

| Registry ID | Lean File | Status | Sorry |
|-------------|-----------|--------|-------|
| DED-038 | Hilbert.lean (A1-A14) | FORMALIZED | 0 |
| DED-039 | Hilbert.lean (MP) | FORMALIZED | 0 |
| DED-050 | Soundness.lean | FORMALIZED | 0 |
| DED-043 | Deduction.lean | FORMALIZED | 0 |
| META-023 | Completeness.lean | SORRY-WITH-DOC | 3 |

### Mathlib reference candidates (from Phase 4b Option A)

| Registry ID | Title | Mathlib theorem | Status |
|-------------|-------|----------------|--------|
| BST-053 | ℕ is enumerable | `Set.countable_univ` | REFERENCED |
| BST-054 | ℕ×ℕ is enumerable | `Set.countable_univ` | REFERENCED |
| BST-063 | Cantor's Theorem | `Function.cantor_surjective` | REFERENCED |
| BST-064 | Schröder-Bernstein | `Function.Embedding.antisymm` | REFERENCED |
| META-026 | Compactness | `FirstOrder.Language.Theory.isFinitelySatisfiable_iff_isSatisfiable` | REFERENCED |
| META-027 | Downward L-S | `FirstOrder.Language.exists_elementarySubstructure_card_eq` | REFERENCED |
| SET-053 | Hartogs' Lemma | `Ordinal.card_ord` | REFERENCED |
| SET-077 | Cardinal arithmetic | `Cardinal.mul_eq_self` | REFERENCED |
| SET-095 | WO iff Choice iff Zorn | `IsWellOrder` + `zorn_partialOrder` | REFERENCED |

---

## Changelog

- **2026-02-12**: Difficulty/Strategy classification completed for all 517 items. 238 TRIVIAL, 94 EASY, 98 MODERATE, 22 HARD, 9 VERY HARD, 9 REFERENCE, 47 SKIP. Updated status for 5 already-formalized items (DED-038, DED-039, DED-043, DED-050 → FORMALIZED; META-023 → SORRY-WITH-DOC). Added classification summary and effort estimate.
- **2026-02-13**: Initial registry created with 517 items extracted from ch-{bst,syn,sem,ded,cmp,meta,set}.tex. All items at PENDING status. Difficulty classification to follow.
