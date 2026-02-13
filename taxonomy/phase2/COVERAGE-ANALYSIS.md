# D3: Coverage Analysis — Phase 3 Input Summary

Analysis of taxonomy coverage, redundancy, and compression potential across CORE tier.

---

## 1. Coverage Matrix

| ID | Concept | Defining Section(s) | Coverage | Redundancy |
|---|---|---|---|---|
| AX-DED001 | Modus Ponens | fol/axd/prp | FULL | None |
| AX-DED002 | Universal Generalization | fol/axd/qua | FULL | None |
| AX-DED003 | Logical Axiom Schemas | fol/axd/prp, fol/axd/qua | FULL | EXPECTED: Proof system variants (2 sections) |
| AX-SET001 | Extensionality | sth/story/extensionality | FULL | None |
| AX-SET002 | Pairing | sth/z/sep | FULL | None |
| AX-SET003 | Union | sth/z/pairs | FULL | None |
| AX-SET004 | Power Set | sth/z/union | FULL | None |
| AX-SET005 | Infinity | sth/z/power | FULL | None |
| AX-SET006 | Separation | sth/z/sep | FULL | None |
| AX-SET007 | Replacement | sth/ordinals/replacement | FULL | None |
| AX-SET008 | Foundation | sth/z/infinity-again | FULL | None |
| AX-SET009 | Choice | sth/cardinals/cardsasords, sth/choice/woproblem | FULL | COMPRESSION-TARGET (2 sections) |
| AX-SYN001 | Formation Rules for Terms | fol/syn/frm | FULL | None |
| AX-SYN002 | Formation Rules for Formulas | fol/syn/frm | FULL | None |
| AX-SYN003 | Formation Rules for PL Formulas | pl/syn/fml | FULL | None |
| CP-001 | Soundness | fol/axd/sou, fol/ntd/sou, fol/seq/sou +1 more | FULL | COMPRESSION-TARGET (4 sections) |
| CP-002 | Completeness | fol/com/hen, fol/com/mod, fol/com/mod +2 more | FULL | COMPRESSION-TARGET (5 sections) |
| CP-003 | Compactness | fol/com/com, fol/com/cpd | FULL | COMPRESSION-TARGET (2 sections) |
| CP-004 | Lowenheim-Skolem | fol/com/dls | FULL | None |
| CP-005 | First Incompleteness Theorem | inc/tcp/inc, inc/inp/1in | FULL | COMPRESSION-TARGET (2 sections) |
| CP-006 | Second Incompleteness Theorem | inc/inp/2in | FULL | None |
| CP-007 | Tarski's Undefinability | inc/inp/tar | FULL | None |
| CP-008 | Church's Undecidability | inc/req/und | FULL | None |
| CP-009 | Deduction Theorem (CP) | fol/axd/ded | FULL | None |
| CP-010 | Cut Elimination (CP) | fol/seq/srl | FULL | None |
| CP-011 | Craig's Interpolation | mod/int/prf | FULL | None |
| CP-012 | Beth's Definability | mod/int/def | FULL | None |
| CP-013 | Lindstrom's Theorem | mod/lin/alg, mod/lin/prf | FULL | COMPRESSION-TARGET (2 sections) |
| DEF-BST001 | Injection | sfr/fun/kin | FULL | None |
| DEF-BST002 | Surjection | sfr/fun/kin | FULL | None |
| DEF-BST003 | Bijection | sfr/fun/kin | FULL | None |
| DEF-BST004 | Equivalence Relation | sfr/rel/eqv | FULL | None |
| DEF-BST005 | Partial Order | sfr/rel/ord | FULL | None |
| DEF-CMP001 | Partial Function | cmp/tur/con | FULL | None |
| DEF-CMP002 | Total Function | cmp/rec/par | FULL | None |
| DEF-CMP003 | Characteristic Function | cmp/rec/prr | FULL | None |
| DEF-CMP004 | Enumeration | cmp/thy/int | FULL | None |
| DEF-CMP005 | Index (Program) | cmp/rec/nft, tur/und/enu | FULL | COMPRESSION-TARGET (2 sections) |
| DEF-CMP006 | Lambda-Definable Function | (none) | ABSENT | None |
| DEF-CMP007 | Productive Set | (none) | ABSENT | None |
| DEF-CMP008 | Creative Set | cmp/thy/cce | FULL | None |
| DEF-CMP009 | Representability | tur/und/rep, inc/int/def, inc/req/int | FULL | COMPRESSION-TARGET (3 sections) |
| DEF-CMP010 | Recursive Enumerability | cmp/thy/eqc | FULL | None |
| DEF-DED001 | Syntactic Consistency | fol/axd/ptn, fol/ntd/ptn, fol/seq/ptn +1 more | FULL | EXPECTED: Proof system variants (4 sections) |
| DEF-DED002 | Maximal Consistent Set | fol/com/mcs | FULL | None |
| DEF-DED003 | Deductive Closure | fol/seq/ptn, fol/mat/int | FULL | EXPECTED: Proof system variants (2 sections) |
| DEF-DED004 | Conservative Extension | (none) | ABSENT | None |
| DEF-DED005 | Hilbert-Style System | fol/axd/prp, fol/prf/axd | FULL | EXPECTED: Proof system variants (2 sections) |
| DEF-DED006 | Natural Deduction | fol/ntd/rul, fol/ntd/prl, fol/ntd/qrl +1 more | FULL | EXPECTED: Proof system variants (4 sections) |
| DEF-DED007 | Sequent Calculus | fol/seq/rul | FULL | None |
| DEF-DED008 | Tableau System | fol/tab/rul | FULL | None |
| DEF-DED009 | Derived Rule | (none) | ABSENT | None |
| DEF-DED010 | Admissible Rule | (none) | ABSENT | None |
| DEF-SEM001 | Tarski Satisfaction Definition | pl/syn/val, fol/syn/sat | FULL | EXPECTED: PL/FOL split (2 sections) |
| DEF-SEM002 | Satisfiable | pl/syn/sem, fol/syn/sem | FULL | EXPECTED: PL/FOL split (2 sections) |
| DEF-SEM003 | Finitely Satisfiable | fol/com/com | FULL | None |
| DEF-SEM004 | Semantic Consistency | fol/syn/sem | FULL | None |
| DEF-SEM005 | Semantic Completeness | fol/com/ccs | FULL | None |
| DEF-SEM006 | Theory of a Structure | mod/bas/dlo | FULL | None |
| DEF-SEM007 | Definable Set | fol/mat/int | FULL | None |
| DEF-SEM008 | Elementary Equivalence | mod/mar/cmp | FULL | None |
| DEF-SEM009 | Tautology (PL) | pl/syn/sem | FULL | None |
| DEF-SEM010 | PL Consequence | pl/syn/sem | FULL | None |
| DEF-SEM011 | Elementary Substructure | mod/bas/sub | FULL | None |
| DEF-SEM012 | Diagram | (none) | ABSENT | None |
| DEF-SEM013 | Type (Complete Type) | mod/bas/iso | FULL | None |
| DEF-SEM014 | Categoricity | (none) | ABSENT | None |
| DEF-SEM015 | Ultraproduct | (none) | ABSENT | None |
| DEF-SEM016 | Embedding | (none) | ABSENT | None |
| DEF-SET001 | Ordinal Number | sth/ordinals/vn | FULL | None |
| DEF-SET002 | Successor Ordinal | sth/ordinals/vn | FULL | None |
| DEF-SET003 | Limit Ordinal | sth/ordinals/vn | FULL | None |
| DEF-SET004 | omega | sth/ordinals/opps | FULL | None |
| DEF-SET005 | Transfinite Induction | sth/ordinals/opps | FULL | None |
| DEF-SET006 | Transfinite Recursion | sth/ordinals/basic | FULL | None |
| DEF-SET007 | Cardinal Number | sth/spine/recursion | FULL | None |
| DEF-SET008 | Cardinality (formal) | sth/cardinals/cp, sth/cardinals/cardsasords | FULL | COMPRESSION-TARGET (2 sections) |
| DEF-SET009 | Well-Ordering | sth/card-arithmetic/ch | FULL | None |
| DEF-SET010 | Zorn's Lemma | sth/card-arithmetic/ch | FULL | None |
| DEF-SET011 | Cantor's Theorem (formal) | (none) | ABSENT | None |
| DEF-SET012 | Von Neumann Hierarchy [Deferred] | (none) | DEFERRED | None |
| DEF-SET013 | Aleph Numbers [Deferred] | (none) | DEFERRED | None |
| DEF-SET014 | Cofinality [Deferred] | (none) | DEFERRED | None |
| DEF-SET015 | Continuum Hypothesis [Deferred] | (none) | DEFERRED | None |
| DEF-SYN001 | Substitution | fol/syn/sub | FULL | None |
| DEF-SYN002 | Simultaneous Substitution | (none) | ABSENT | None |
| DEF-SYN003 | Free Variables (FV) | fol/syn/fvs | FULL | None |
| DEF-SYN004 | Alphabetic Variant | (none) | ABSENT | None |
| DEF-SYN005 | Structural Induction on Formulas | fol/syn/frm | FULL | None |
| DEF-SYN006 | Structural Recursion | pl/syn/fseq, fol/syn/fseq | FULL | EXPECTED: PL/FOL split (2 sections) |
| DEF-SYN007 | Formula Complexity | (none) | ABSENT | None |
| DEF-SYN008 | Subterm | fol/syn/sbf | FULL | None |
| PRIM-BST001 | Set | sfr/set/bas | FULL | None |
| PRIM-BST002 | Membership | sfr/set/bas | FULL | None |
| PRIM-BST003 | Subset | sfr/set/sub | FULL | None |
| PRIM-BST004 | Empty Set | sfr/set/bas | FULL | None |
| PRIM-BST005 | Union/Intersection | sfr/set/uni | FULL | None |
| PRIM-BST006 | Ordered Pair | sfr/set/pai | FULL | None |
| PRIM-BST007 | Cartesian Product | sfr/set/pai | FULL | None |
| PRIM-BST008 | Relation | sfr/rel/set | FULL | None |
| PRIM-BST009 | Function | sfr/fun/bas | FULL | None |
| PRIM-BST010 | Sequence (Finite) | sfr/set/imp, sfr/set/pai | FULL | COMPRESSION-TARGET (2 sections) |
| PRIM-BST011 | Sequence (Infinite) | sfr/set/imp | FULL | None |
| PRIM-BST012 | Natural Number | sfr/set/imp | FULL | None |
| PRIM-BST013 | Mathematical Induction | sfr/ind/int, sfr/infinite/induction | FULL | COMPRESSION-TARGET (2 sections) |
| PRIM-BST014 | Inductive Definition | sfr/ind/int | FULL | None |
| PRIM-BST015 | Power Set (naive) | sfr/set/sub | FULL | None |
| PRIM-BST016 | Cardinality | sfr/siz/enm, sfr/siz/enm-alt | FULL | COMPRESSION-TARGET (2 sections) |
| PRIM-CMP001 | Computable Function | cmp/rec/par, tur/mac/int, tur/mac/una | FULL | COMPRESSION-TARGET (3 sections) |
| PRIM-CMP002 | Primitive Recursive Function | cmp/rec/pre, cmp/rec/prf | FULL | COMPRESSION-TARGET (2 sections) |
| PRIM-CMP003 | mu-Recursion | cmp/rec/par | FULL | None |
| PRIM-CMP004 | Turing Machine | tur/mac/int, tur/mac/tur | FULL | COMPRESSION-TARGET (2 sections) |
| PRIM-CMP005 | Church-Turing Thesis | tur/mac/ctt | FULL | None |
| PRIM-CMP006 | Decidable Set | cmp/thy/cps, tur/und/int, tur/und/dec | FULL | COMPRESSION-TARGET (3 sections) |
| PRIM-CMP007 | Semi-Decidable Set | cmp/thy/ces | FULL | None |
| PRIM-CMP008 | Halting Problem | cmp/rec/hlt, cmp/thy/hlt, tur/und/int +1 more | FULL | COMPRESSION-TARGET (4 sections) |
| PRIM-CMP009 | Many-One Reducibility | cmp/thy/red | FULL | None |
| PRIM-CMP010 | Diagonalization | cmp/rec/npr | FULL | None |
| PRIM-CMP011 | Godel Numbering | cmp/rec/seq, cmp/rec/nft, tur/und/enu | FULL | COMPRESSION-TARGET (3 sections) |
| PRIM-CMP012 | Universal Turing Machine | cmp/thy/int, cmp/thy/uni, tur/und/uni | FULL | COMPRESSION-TARGET (3 sections) |
| PRIM-DED001 | Axiom Schema | fol/axd/prp | FULL | None |
| PRIM-DED002 | Non-Logical Axiom | fol/mat/the | FULL | None |
| PRIM-DED003 | Rule of Inference | fol/ntd/prl, fol/ntd/qrl, fol/seq/prl +5 more | FULL | EXPECTED: Proof system variants (8 sections) |
| PRIM-DED004 | Proof System | fol/seq/rul, fol/tab/rul | FULL | EXPECTED: Proof system variants (2 sections) |
| PRIM-DED005 | Derivation | fol/axd/rul, fol/ntd/der, fol/seq/der +2 more | FULL | EXPECTED: Proof system variants (5 sections) |
| PRIM-DED006 | Provability | fol/axd/rul, fol/axd/ptn, fol/ntd/der +3 more | FULL | EXPECTED: Proof system variants (6 sections) |
| PRIM-DED007 | Structural Rule | fol/ntd/qrl, fol/seq/srl | FULL | EXPECTED: Proof system variants (2 sections) |
| PRIM-DED008 | Sequent | fol/seq/rul | FULL | None |
| PRIM-DED009 | Assumption Discharge | fol/ntd/rul, fol/ntd/prl | FULL | EXPECTED: Proof system variants (2 sections) |
| PRIM-DED010 | Theorem | fol/axd/rul, fol/axd/ptn, fol/ntd/ptn +2 more | FULL | EXPECTED: Proof system variants (5 sections) |
| PRIM-SEM001 | Structure | fol/syn/str | FULL | None |
| PRIM-SEM002 | Domain | fol/syn/str | FULL | None |
| PRIM-SEM003 | Interpretation | fol/syn/str | FULL | None |
| PRIM-SEM004 | Variable Assignment | fol/syn/sat | FULL | None |
| PRIM-SEM005 | x-Variant | fol/syn/sat | FULL | None |
| PRIM-SEM006 | Term Valuation | fol/syn/cov, fol/syn/sat | FULL | COMPRESSION-TARGET (2 sections) |
| PRIM-SEM007 | Satisfaction | pl/syn/val, fol/syn/sat | FULL | EXPECTED: PL/FOL split (2 sections) |
| PRIM-SEM008 | Truth in a Structure | fol/syn/ass | FULL | None |
| PRIM-SEM009 | Logical Validity | fol/syn/sem | FULL | None |
| PRIM-SEM010 | Logical Consequence | fol/syn/sem | FULL | None |
| PRIM-SEM011 | Model | fol/syn/sem, fol/mat/exs | FULL | COMPRESSION-TARGET (2 sections) |
| PRIM-SEM012 | Isomorphism | mod/bas/thm | FULL | None |
| PRIM-SEM013 | Substructure | mod/bas/iso | FULL | None |
| PRIM-SEM014 | Homomorphism | (none) | ABSENT | None |
| PRIM-SEM015 | Truth-Value Assignment (PL) | pl/syn/val | FULL | None |
| PRIM-SET001 | Set (formal) | (none) | ABSENT | None |
| PRIM-SET002 | Membership (formal) | (none) | IMPLICIT | None |
| PRIM-SET003 | Class | sth/ordinals/basic | FULL | None |
| PRIM-SYN001 | Symbol | fol/syn/fol | FULL | None |
| PRIM-SYN002 | Variable | pl/syn/fml, fol/syn/fol | FULL | EXPECTED: PL/FOL split (2 sections) |
| PRIM-SYN003 | Logical Connective | pl/syn/fml, fol/syn/fol | FULL | EXPECTED: PL/FOL split (2 sections) |
| PRIM-SYN004 | Quantifier | fol/syn/fol | FULL | None |
| PRIM-SYN005 | Constant Symbol | fol/syn/fol | FULL | None |
| PRIM-SYN006 | Function Symbol | fol/syn/fol | FULL | None |
| PRIM-SYN007 | Relation Symbol | fol/syn/fol | FULL | None |
| PRIM-SYN008 | Arity | fol/syn/fol | FULL | None |
| PRIM-SYN009 | Language | fol/syn/fol | FULL | None |
| PRIM-SYN010 | Term | fol/syn/frm | FULL | None |
| PRIM-SYN011 | Atomic Formula | fol/syn/frm | FULL | None |
| PRIM-SYN012 | Formula (wff) | pl/syn/fml, fol/syn/frm | FULL | EXPECTED: PL/FOL split (2 sections) |
| PRIM-SYN013 | Sentence | fol/syn/fvs | FULL | None |
| PRIM-SYN014 | Free Occurrence | fol/syn/fvs | FULL | None |
| PRIM-SYN015 | Bound Occurrence | fol/syn/fvs | FULL | None |
| PRIM-SYN016 | Scope | fol/syn/fvs | FULL | None |
| PRIM-SYN017 | Subformula | fol/syn/sbf | FULL | None |
| PRIM-SYN018 | Equality Symbol | fol/syn/fol | FULL | None |
| THM-BST001 | Cantor's Theorem (Naive) | sfr/siz/nen, sfr/siz/car, sfr/siz/nen-alt | FULL | COMPRESSION-TARGET (3 sections) |
| THM-BST002 | N is Countably Infinite | sfr/siz/enm | FULL | None |
| THM-BST003 | Countable Union of Countable Sets | sfr/siz/zigzag | FULL | None |
| THM-CMP001 | Equivalence of Computation Models | tur/mac/var | FULL | None |
| THM-CMP002 | Unsolvability of Halting Problem | tur/und/hal, tur/und/uns | FULL | COMPRESSION-TARGET (2 sections) |
| THM-CMP003 | Rice's Theorem | cmp/thy/rce | FULL | None |
| THM-CMP004 | s-m-n Theorem | cmp/rec/nft, cmp/thy/nfm, cmp/thy/smn | FULL | COMPRESSION-TARGET (3 sections) |
| THM-CMP005 | Recursion Theorem (Kleene) | cmp/thy/fix | FULL | None |
| THM-DED001 | Deduction Theorem | fol/axd/ded | FULL | None |
| THM-DED002 | Equivalence of Proof Systems | (none) | ABSENT | None |
| THM-DED003 | Cut Elimination | (none) | ABSENT | None |
| THM-DED004 | Normalization | (none) | ABSENT | None |
| THM-DED005 | Lindenbaum's Lemma | fol/com/lin | FULL | None |
| THM-SEM001 | Isomorphism Lemma | mod/bas/iso | FULL | None |
| THM-SEM002 | Coincidence Lemma | fol/syn/ext | FULL | None |
| THM-SEM003 | Los's Theorem | (none) | ABSENT | None |
| THM-SET001 | Well-Ordering iff Zorn iff AC | sth/choice/woproblem | FULL | None |
| THM-SET002 | Transfinite Recursion Theorem | sth/spine/recursion | FULL | None |
| THM-SET003 | Cantor's Theorem (ZFC) | sth/choice/justifications | FULL | None |
| THM-SYN001 | Unique Readability (Formulas) | fol/syn/unq | FULL | None |
| THM-SYN002 | Unique Readability (Terms) | fol/syn/unq | FULL | None |
| THM-SYN003 | Substitution Lemma | fol/syn/ext | FULL | None |
| THM-SYN004 | Structural Induction Principles | (none) | ABSENT | None |

**Coverage summary (pre-Phase 2.5)**: FULL=164, IMPLICIT=1, ABSENT=20, DEFERRED=4 (189 items)
**Coverage summary (post-Phase 2.5)**: FULL=183, IMPLICIT=6, ABSENT=4, EXTENSION-ONLY=8, REDUNDANT=2, DEFERRED=1, STEPPING-STONE=3 (205 items)
**Coverage rate**: 183/205 = 89.3% FULL (excluding extension-only and redundant: 183/195 = 93.8%)

## 2. Redundancy Report

Items introduced in 2+ sections:

### AX-DED003 — Logical Axiom Schemas
- **Sections**: fol/axd/prp, fol/axd/qua
- **Classification**: EXPECTED: Proof system variants (2 sections)
- **Recommendation**: Keep all — pedagogically motivated split

### AX-SET009 — Choice
- **Sections**: sth/cardinals/cardsasords, sth/choice/woproblem
- **Classification**: COMPRESSION-TARGET (2 sections)
- **Recommendation**: Designate one as primary, merge or compress others

### CP-001 — Soundness
- **Sections**: fol/axd/sou, fol/ntd/sou, fol/seq/sou, fol/tab/sou
- **Classification**: COMPRESSION-TARGET (4 sections)
- **Recommendation**: Designate one as primary, merge or compress others

### CP-002 — Completeness
- **Sections**: fol/com/hen, fol/com/mod, fol/com/mod, fol/com/ide, fol/com/cth
- **Classification**: COMPRESSION-TARGET (5 sections)
- **Recommendation**: Designate one as primary, merge or compress others

### CP-003 — Compactness
- **Sections**: fol/com/com, fol/com/cpd
- **Classification**: COMPRESSION-TARGET (2 sections)
- **Recommendation**: Designate one as primary, merge or compress others

### CP-005 — First Incompleteness Theorem
- **Sections**: inc/tcp/inc, inc/inp/1in
- **Classification**: COMPRESSION-TARGET (2 sections)
- **Recommendation**: Designate one as primary, merge or compress others

### CP-013 — Lindstrom's Theorem
- **Sections**: mod/lin/alg, mod/lin/prf
- **Classification**: COMPRESSION-TARGET (2 sections)
- **Recommendation**: Designate one as primary, merge or compress others

### DEF-CMP005 — Index (Program)
- **Sections**: cmp/rec/nft, tur/und/enu
- **Classification**: COMPRESSION-TARGET (2 sections)
- **Recommendation**: Designate one as primary, merge or compress others

### DEF-CMP009 — Representability
- **Sections**: tur/und/rep, inc/int/def, inc/req/int
- **Classification**: COMPRESSION-TARGET (3 sections)
- **Recommendation**: Designate one as primary, merge or compress others

### DEF-DED001 — Syntactic Consistency
- **Sections**: fol/axd/ptn, fol/ntd/ptn, fol/seq/ptn, fol/tab/ptn
- **Classification**: EXPECTED: Proof system variants (4 sections)
- **Recommendation**: Keep all — pedagogically motivated split

### DEF-DED003 — Deductive Closure
- **Sections**: fol/seq/ptn, fol/mat/int
- **Classification**: EXPECTED: Proof system variants (2 sections)
- **Recommendation**: Keep all — pedagogically motivated split

### DEF-DED005 — Hilbert-Style System
- **Sections**: fol/axd/prp, fol/prf/axd
- **Classification**: EXPECTED: Proof system variants (2 sections)
- **Recommendation**: Keep all — pedagogically motivated split

### DEF-DED006 — Natural Deduction
- **Sections**: fol/ntd/rul, fol/ntd/prl, fol/ntd/qrl, fol/prf/ntd
- **Classification**: EXPECTED: Proof system variants (4 sections)
- **Recommendation**: Keep all — pedagogically motivated split

### DEF-SEM001 — Tarski Satisfaction Definition
- **Sections**: pl/syn/val, fol/syn/sat
- **Classification**: EXPECTED: PL/FOL split (2 sections)
- **Recommendation**: Keep all — pedagogically motivated split

### DEF-SEM002 — Satisfiable
- **Sections**: pl/syn/sem, fol/syn/sem
- **Classification**: EXPECTED: PL/FOL split (2 sections)
- **Recommendation**: Keep all — pedagogically motivated split

### DEF-SET008 — Cardinality (formal)
- **Sections**: sth/cardinals/cp, sth/cardinals/cardsasords
- **Classification**: COMPRESSION-TARGET (2 sections)
- **Recommendation**: Designate one as primary, merge or compress others

### DEF-SYN006 — Structural Recursion
- **Sections**: pl/syn/fseq, fol/syn/fseq
- **Classification**: EXPECTED: PL/FOL split (2 sections)
- **Recommendation**: Keep all — pedagogically motivated split

### PRIM-BST010 — Sequence (Finite)
- **Sections**: sfr/set/imp, sfr/set/pai
- **Classification**: COMPRESSION-TARGET (2 sections)
- **Recommendation**: Designate one as primary, merge or compress others

### PRIM-BST013 — Mathematical Induction
- **Sections**: sfr/ind/int, sfr/infinite/induction
- **Classification**: COMPRESSION-TARGET (2 sections)
- **Recommendation**: Designate one as primary, merge or compress others

### PRIM-BST016 — Cardinality
- **Sections**: sfr/siz/enm, sfr/siz/enm-alt
- **Classification**: COMPRESSION-TARGET (2 sections)
- **Recommendation**: Designate one as primary, merge or compress others

### PRIM-CMP001 — Computable Function
- **Sections**: cmp/rec/par, tur/mac/int, tur/mac/una
- **Classification**: COMPRESSION-TARGET (3 sections)
- **Recommendation**: Designate one as primary, merge or compress others

### PRIM-CMP002 — Primitive Recursive Function
- **Sections**: cmp/rec/pre, cmp/rec/prf
- **Classification**: COMPRESSION-TARGET (2 sections)
- **Recommendation**: Designate one as primary, merge or compress others

### PRIM-CMP004 — Turing Machine
- **Sections**: tur/mac/int, tur/mac/tur
- **Classification**: COMPRESSION-TARGET (2 sections)
- **Recommendation**: Designate one as primary, merge or compress others

### PRIM-CMP006 — Decidable Set
- **Sections**: cmp/thy/cps, tur/und/int, tur/und/dec
- **Classification**: COMPRESSION-TARGET (3 sections)
- **Recommendation**: Designate one as primary, merge or compress others

### PRIM-CMP008 — Halting Problem
- **Sections**: cmp/rec/hlt, cmp/thy/hlt, tur/und/int, tur/und/hal
- **Classification**: COMPRESSION-TARGET (4 sections)
- **Recommendation**: Designate one as primary, merge or compress others

### PRIM-CMP011 — Godel Numbering
- **Sections**: cmp/rec/seq, cmp/rec/nft, tur/und/enu
- **Classification**: COMPRESSION-TARGET (3 sections)
- **Recommendation**: Designate one as primary, merge or compress others

### PRIM-CMP012 — Universal Turing Machine
- **Sections**: cmp/thy/int, cmp/thy/uni, tur/und/uni
- **Classification**: COMPRESSION-TARGET (3 sections)
- **Recommendation**: Designate one as primary, merge or compress others

### PRIM-DED003 — Rule of Inference
- **Sections**: fol/ntd/prl, fol/ntd/qrl, fol/seq/prl, fol/seq/qrl, fol/seq/ide, fol/tab/ide, fol/tab/prl, fol/tab/qrl
- **Classification**: EXPECTED: Proof system variants (8 sections)
- **Recommendation**: Keep all — pedagogically motivated split

### PRIM-DED004 — Proof System
- **Sections**: fol/seq/rul, fol/tab/rul
- **Classification**: EXPECTED: Proof system variants (2 sections)
- **Recommendation**: Keep all — pedagogically motivated split

### PRIM-DED005 — Derivation
- **Sections**: fol/axd/rul, fol/ntd/der, fol/seq/der, fol/tab/rul, fol/tab/der
- **Classification**: EXPECTED: Proof system variants (5 sections)
- **Recommendation**: Keep all — pedagogically motivated split

### PRIM-DED006 — Provability
- **Sections**: fol/axd/rul, fol/axd/ptn, fol/ntd/der, fol/ntd/ptn, fol/seq/ptn, fol/tab/ptn
- **Classification**: EXPECTED: Proof system variants (6 sections)
- **Recommendation**: Keep all — pedagogically motivated split

### PRIM-DED007 — Structural Rule
- **Sections**: fol/ntd/qrl, fol/seq/srl
- **Classification**: EXPECTED: Proof system variants (2 sections)
- **Recommendation**: Keep all — pedagogically motivated split

### PRIM-DED009 — Assumption Discharge
- **Sections**: fol/ntd/rul, fol/ntd/prl
- **Classification**: EXPECTED: Proof system variants (2 sections)
- **Recommendation**: Keep all — pedagogically motivated split

### PRIM-DED010 — Theorem
- **Sections**: fol/axd/rul, fol/axd/ptn, fol/ntd/ptn, fol/seq/ptn, fol/tab/ptn
- **Classification**: EXPECTED: Proof system variants (5 sections)
- **Recommendation**: Keep all — pedagogically motivated split

### PRIM-SEM006 — Term Valuation
- **Sections**: fol/syn/cov, fol/syn/sat
- **Classification**: COMPRESSION-TARGET (2 sections)
- **Recommendation**: Designate one as primary, merge or compress others

### PRIM-SEM007 — Satisfaction
- **Sections**: pl/syn/val, fol/syn/sat
- **Classification**: EXPECTED: PL/FOL split (2 sections)
- **Recommendation**: Keep all — pedagogically motivated split

### PRIM-SEM011 — Model
- **Sections**: fol/syn/sem, fol/mat/exs
- **Classification**: COMPRESSION-TARGET (2 sections)
- **Recommendation**: Designate one as primary, merge or compress others

### PRIM-SYN002 — Variable
- **Sections**: pl/syn/fml, fol/syn/fol
- **Classification**: EXPECTED: PL/FOL split (2 sections)
- **Recommendation**: Keep all — pedagogically motivated split

### PRIM-SYN003 — Logical Connective
- **Sections**: pl/syn/fml, fol/syn/fol
- **Classification**: EXPECTED: PL/FOL split (2 sections)
- **Recommendation**: Keep all — pedagogically motivated split

### PRIM-SYN012 — Formula (wff)
- **Sections**: pl/syn/fml, fol/syn/frm
- **Classification**: EXPECTED: PL/FOL split (2 sections)
- **Recommendation**: Keep all — pedagogically motivated split

### THM-BST001 — Cantor's Theorem (Naive)
- **Sections**: sfr/siz/nen, sfr/siz/car, sfr/siz/nen-alt
- **Classification**: COMPRESSION-TARGET (3 sections)
- **Recommendation**: Designate one as primary, merge or compress others

### THM-CMP002 — Unsolvability of Halting Problem
- **Sections**: tur/und/hal, tur/und/uns
- **Classification**: COMPRESSION-TARGET (2 sections)
- **Recommendation**: Designate one as primary, merge or compress others

### THM-CMP004 — s-m-n Theorem
- **Sections**: cmp/rec/nft, cmp/thy/nfm, cmp/thy/smn
- **Classification**: COMPRESSION-TARGET (3 sections)
- **Recommendation**: Designate one as primary, merge or compress others

**Summary**: 19 EXPECTED redundancies, 24 COMPRESSION-TARGETs

## 3. OL-Only Concepts

### Phase 2.5 Resolution: INC Domain Integration (RESOLVED)

The 25 DEF-INC items have been classified into existing domains per CONVENTIONS.md Principle 1.
Full details in `taxonomy/PHASE-2.5-RESOLUTION.md`.

**16 new taxonomy items created:**
- DED: DEF-DED011 (Robinson Q), DEF-DED012 (PA), DEF-DED013 (omega-consistency), DEF-DED014 (Derivability Conditions), THM-DED006 (Fixed-Point Lemma), THM-DED007 (Lob's Theorem)
- CMP: DEF-CMP011 (Axiomatizable Theory), DEF-CMP012 (Proof Predicate), DEF-CMP013 (Beta-Function), DEF-CMP014 (Computable Inseparability)
- SYN: DEF-SYN009 (Delta_0 Formula), DEF-SYN010 (Sigma_1 Formula), DEF-SYN011 (Pi_1 Formula)
- SEM: DEF-SEM017 (Standard Model N), DEF-SEM018 (True Arithmetic), DEF-SEM019 (Interpretability)

**5 subsumed under existing items:** DEF-INC001 -> DEF-DED003, DEF-INC007 -> DEF-SEM005, DEF-INC009 -> DEF-CMP009, DEF-INC010+011 -> PRIM-CMP011
**3 stepping stones (no taxonomy ID):** DEF-INC014, DEF-INC022, DEF-INC023
**1 merged pair:** DEF-INC004+INC008 -> DEF-CMP011

### ABSENT Items — Phase 2.5 Classification (RESOLVED)

**Internal redundancy (covered by existing mapped items, 2):**
- **DEF-SET011** (Cantor's Theorem formal) -> covered by THM-SET003 (Cantor's Theorem ZFC)
- **THM-DED003** (Cut Elimination) -> covered by CP-010 (Cut Elimination)

**Extension-only (correctly absent from CORE, 8):**
- **DEF-CMP006** (Lambda-Definable Function): In lambda-calculus extension
- **DEF-SEM012** (Diagram): Advanced model theory, not in OL
- **DEF-SEM014** (Categoricity): Advanced model theory, not in OL
- **DEF-SEM015** (Ultraproduct): Advanced model theory, not in OL
- **DEF-SEM016** (Embedding): Advanced model theory, not in OL
- **PRIM-SEM014** (Homomorphism): Not used in OL's model theory chapters
- **THM-SEM003** (Los's Theorem): Requires ultraproducts, not in OL
- **THM-DED004** (Normalization): In intuitionistic logic extension

**IMPLICIT (used but not formally defined, 5):**
- **DEF-CMP007** (Productive Set): Used in creative set section without dedicated definition
- **DEF-DED009** (Derived Rule): Used informally in proof system chapters
- **DEF-DED010** (Admissible Rule): Used informally
- **DEF-SYN007** (Formula Complexity): Used in induction proofs without formal definition
- **THM-SYN004** (Structural Induction Principles): Used extensively but not stated as named theorem

**Genuinely absent (taxonomy item with no OL coverage, 4):**
- **DEF-DED004** (Conservative Extension): Important concept, not in OL
- **DEF-SYN002** (Simultaneous Substitution): OL defines single substitution only
- **DEF-SYN004** (Alphabetic Variant): Not in OL
- **THM-DED002** (Equivalence of Proof Systems): OL proves per-system but not general equivalence

**Upgraded to IMPLICIT (from ABSENT, 1):**
- **PRIM-SET001** (Set formal): ZFC's sole primitive, implicitly assumed in all sth/ sections

### IMPLICIT Items (updated)

- **PRIM-SET001** (Set (formal)): Implicitly assumed as the sole sort in ZFC; not separately defined in sth/ sections
- **PRIM-SET002** (Membership (formal)): Upgraded to FULL — sth/story/extensionality explicitly axiomatizes membership. The Extensionality axiom (AX-SET001) defines sets in terms of membership.

### DEFERRED Items (updated)

- **DEF-SET012** (Von Neumann Hierarchy): **Upgraded to FULL** — defined in sth/spine/valpha
- **DEF-SET013** (Aleph Numbers): **Upgraded to FULL** — defined in sth/card-arithmetic/ch
- **DEF-SET014** (Cofinality): **Remains DEFERRED** — not explicitly defined in mapped sections
- **DEF-SET015** (Continuum Hypothesis): **Upgraded to FULL** — defined in sth/card-arithmetic/ch

## 4. Phase 3 Summary Statistics

| Topic Area | Sections | CORE-DEF | CORE-THM | STEPPING-STONE | PEDAGOGICAL | REDUNDANT | TANGENTIAL |
|---|---|---|---|---|---|---|---|
| sets-functions-relations | 48 | 19 | 3 | 9 | 12 | 0 | 5 |
| propositional-logic | 8 | 3 | 1 | 1 | 1 | 0 | 2 |
| first-order-logic | 109 | 36 | 12 | 23 | 31 | 0 | 7 |
| model-theory | 22 | 3 | 6 | 8 | 5 | 0 | 0 |
| computability | 42 | 11 | 15 | 3 | 12 | 0 | 1 |
| turing-machines | 18 | 4 | 3 | 5 | 5 | 0 | 1 |
| incompleteness | 44 | 3 | 10 | 25 | 6 | 0 | 0 |
| set-theory | 62 | 14 | 4 | 26 | 14 | 0 | 4 |

## 5. Quality Check Results

### QC-1: Coverage Completeness (updated post-Phase 2.5)
- Taxonomy items (post-Phase 2.5): 205 (192 PRIM/DEF/AX/THM + 13 CPs)
- FULL coverage: 183/205 (89.3%)
- Excluding extension-only (8) and internal redundancy (2): 183/195 = 93.8%
- Genuinely absent (no OL coverage, no reclassification): 4 items
  - DEF-DED004, DEF-SYN002, DEF-SYN004, THM-DED002
- **Status**: PASS (4 genuinely absent items are acceptable; all are documented)

### QC-2: Formal Item Classification (updated)
- Total taxonomy IDs in 'introduces' fields: 287 (271 original + 16 new items)
- Total taxonomy IDs in 'references' fields: 984
- Former INC-domain additions: 25 -> resolved into 16 new + 5 subsumed + 3 stepping stones + 1 merge
- **Status**: PASS

### QC-3: No Orphan Sections
- Sections with no taxonomy IDs (introduces or references): 14
- Orphans: sfr/siz/int, sfr/infinite/dedekindsproof, sfr/arith/ref, fol/byd/int, fol/byd/hol, fol/byd/il, fol/byd/mod, fol/byd/oth, sth/story/predicative, sth/story/approach, sth/story/urelements, sth/story/blv, sth/z/story, sth/ordinals/idea
- Classification: All 14 are DISCUSS or PEDAGOGICAL sections (introductions, historical context, beyond-FOL overviews). No taxonomy concepts expected.
- **Status**: PASS (orphan sections are all non-definitional)

### QC-5: Redundancy Documentation
- Items introduced in 2+ sections: 43
- All documented in Redundancy Report above: YES
- **Status**: PASS

### QC-7: Reverse Index Consistency
- D2 entries generated: 214 + 16 new = 230 (pending D2 update)
- Cross-check: every section listed in D2 maps back to D1: verified programmatically (pre-Phase 2.5)
- **Status**: PASS

## 6. Phase 2.5 Resolution Assessment

- **Phase 2.5 was triggered**: 25 INC-domain gap candidates (>5 threshold)
- **Phase 2.5 is now COMPLETE**:
  - 25 DEF-INC items classified into existing domains (16 new, 5 subsumed, 3 stepping stones, 1 merge)
  - 20 ABSENT items classified (2 redundant, 8 extension-only, 5 implicit, 1 upgraded to implicit, 4 genuinely absent)
  - 4 DEFERRED items resolved (3 upgraded to FULL, 1 remains DEFERRED)
  - 1 IMPLICIT item upgraded to FULL (PRIM-SET002)
  - 1 mapping error corrected (sth/card-arithmetic/ch)
  - Primitive Registry updated with 18 new rows
  - Full resolution details in `taxonomy/PHASE-2.5-RESOLUTION.md`
