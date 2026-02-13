# LEAN-OUTLINE: Lean Text Table of Contents

This document specifies the complete structure of the lean text, organized by chapter and section in taxonomy dependency order. Every section lists its source OL sections (with compression action), taxonomy items it must define or prove, prerequisite lean sections, and estimated page count.

**Total taxonomy items**: 205 (192 PRIM/DEF/AX/THM + 13 CPs)
**Estimated surviving sections**: ~200 (from 353 CORE + 10 NEW-CONTENT/FORMALIZE additions)
**Estimated total pages**: 250--350

---

## CH-BST: Set-Theoretic Foundations (Level-0)

Prerequisites: none (root chapter)

### BST.1: Sets and Membership
- **Sources**: sfr/set/bas (KEEP), sfr/set/sub (KEEP), sfr/set/uni (KEEP), sfr/set/pai (ABSORB:sfr/set/imp partial), sfr/set/imp (CONDENSE, for PRIM-BST012/011)
- **Taxonomy**: PRIM-BST001 (Set/Extensionality), PRIM-BST002 (Membership), PRIM-BST003 (Subset), PRIM-BST004 (Empty Set), PRIM-BST005 (Union/Intersection), PRIM-BST006 (Ordered Pair), PRIM-BST007 (Cartesian Product), PRIM-BST015 (Power Set)
- **Prerequisites**: none
- **Estimated pages**: 8

### BST.2: Relations
- **Sources**: sfr/rel/set (KEEP), sfr/rel/prp (KEEP), sfr/rel/eqv (KEEP), sfr/rel/ord (CONDENSE), sfr/rel/tre (CONDENSE), sfr/rel/ops (CONDENSE)
- **Taxonomy**: PRIM-BST008 (Relation), DEF-BST004 (Equivalence Relation), DEF-BST005 (Partial Order)
- **Prerequisites**: BST.1
- **Estimated pages**: 7

### BST.3: Functions
- **Sources**: sfr/fun/bas (KEEP), sfr/fun/kin (KEEP), sfr/fun/inv (KEEP), sfr/fun/cmp (KEEP), sfr/fun/rel (CONDENSE)
- **Taxonomy**: PRIM-BST009 (Function), DEF-BST001 (Injection), DEF-BST002 (Surjection), DEF-BST003 (Bijection)
- **Prerequisites**: BST.1, BST.2
- **Estimated pages**: 6

### BST.4: Sequences and Numbers
- **Sources**: sfr/set/pai (ABSORB, sequence content), sfr/set/imp (CONDENSE, N and infinite sequences)
- **Taxonomy**: PRIM-BST010 (Finite Sequence), PRIM-BST011 (Infinite Sequence), PRIM-BST012 (Natural Number)
- **Prerequisites**: BST.1, BST.3
- **Estimated pages**: 3

### BST.5: Induction and Recursion
- **Sources**: sfr/ind/int (ABSORB:sfr/infinite/induction)
- **Taxonomy**: PRIM-BST013 (Mathematical Induction), PRIM-BST014 (Inductive Definition)
- **Prerequisites**: BST.4
- **Estimated pages**: 4

### BST.6: Cardinality
- **Sources**: sfr/siz/enm (ABSORB:sfr/siz/enm-alt), sfr/siz/nen (ABSORB:sfr/siz/nen-alt), sfr/siz/zigzag (KEEP), sfr/siz/car (KEEP), sfr/siz/pai (CONDENSE), sfr/siz/red (CONDENSE), sfr/siz/equ (CONDENSE), sfr/siz/sb (CONDENSE), sfr/infinite/hilbert (CONDENSE), sfr/infinite/dedekind (CONDENSE), sfr/infinite/card-sb (CONDENSE)
- **Taxonomy**: PRIM-BST016 (Cardinality/Enumerability), THM-BST001 (Cantor's Theorem), THM-BST002 (N countably infinite), THM-BST003 (N x N enumerable)
- **Prerequisites**: BST.1--BST.5
- **Estimated pages**: 10

**CH-BST subtotal**: ~38 pages, 24 taxonomy items, 28 surviving sections

---

## CH-SYN: Syntax

Prerequisites: CH-BST

### SYN.1: Languages and Symbols
- **Sources**: fol/syn/fol (KEEP)
- **Taxonomy**: PRIM-SYN001 (Symbol), PRIM-SYN002 (Variable), PRIM-SYN003 (Logical Connective), PRIM-SYN004 (Quantifier), PRIM-SYN005 (Constant Symbol), PRIM-SYN006 (Function Symbol), PRIM-SYN007 (Relation Symbol), PRIM-SYN008 (Arity), PRIM-SYN009 (Language/Signature), PRIM-SYN018 (Equality Symbol)
- **Prerequisites**: BST.1
- **Estimated pages**: 4

### SYN.2: Terms and Formulas
- **Sources**: fol/syn/frm (ABSORB:pl/syn/fml), fol/syn/sbf (KEEP), fol/syn/fseq (CONDENSE)
- **Taxonomy**: PRIM-SYN010 (Term), PRIM-SYN011 (Atomic Formula), PRIM-SYN012 (Formula), PRIM-SYN017 (Subformula), AX-SYN001 (Term Formation), AX-SYN002 (Formula Formation), AX-SYN003 (PL Formation, remark), DEF-SYN005 (Structural Induction), DEF-SYN006 (Formation Sequences), DEF-SYN007 (Formula Complexity, FORMALIZE per A4), DEF-SYN008 (Subterm)
- **Prerequisites**: SYN.1
- **Estimated pages**: 6

### SYN.3: Variables and Scope
- **Sources**: fol/syn/fvs (KEEP)
- **Taxonomy**: PRIM-SYN013 (Sentence), PRIM-SYN014 (Free Occurrence), PRIM-SYN015 (Bound Occurrence), PRIM-SYN016 (Scope), DEF-SYN003 (Free Variables FV)
- **Prerequisites**: SYN.2
- **Estimated pages**: 3

### SYN.4: Substitution
- **Sources**: fol/syn/sub (KEEP)
- **Taxonomy**: DEF-SYN001 (Substitution), DEF-SYN002 (Simultaneous Substitution, NEW-CONTENT per A4), DEF-SYN004 (Alphabetic Variant, NEW-CONTENT per A4)
- **Prerequisites**: SYN.3
- **Estimated pages**: 3

### SYN.5: Arithmetic Hierarchy
- **Sources**: inc/inp/s1c (KEEP)
- **Taxonomy**: DEF-SYN009 (Bounded/Delta_0 Formula), DEF-SYN010 (Sigma_1 Formula), DEF-SYN011 (Pi_1 Formula)
- **Prerequisites**: SYN.2
- **Estimated pages**: 2

### SYN.6: Theorems
- **Sources**: fol/syn/unq (KEEP), pl/syn/pre (CONDENSE, remark)
- **Taxonomy**: THM-SYN001 (Unique Readability), THM-SYN002 (Unique Readability for Terms), THM-SYN004 (Structural Induction Principles, FORMALIZE per A4)
- **Prerequisites**: SYN.2
- **Estimated pages**: 3

**CH-SYN subtotal**: ~21 pages, 30 taxonomy items (18 PRIM + 9 DEF + 3 AX), 10 surviving sections

---

## CH-SEM: Semantics

Prerequisites: CH-SYN, CH-BST

### SEM.1: Structures
- **Sources**: fol/syn/str (KEEP), fol/syn/cov (CONDENSE)
- **Taxonomy**: PRIM-SEM001 (Structure), PRIM-SEM002 (Domain), PRIM-SEM003 (Interpretation)
- **Prerequisites**: SYN.1, BST.1--BST.3
- **Estimated pages**: 4

### SEM.2: Satisfaction and Truth
- **Sources**: fol/syn/sat (ABSORB:pl/syn/val), fol/syn/ass (CONDENSE)
- **Taxonomy**: PRIM-SEM004 (Variable Assignment), PRIM-SEM005 (x-Variant), PRIM-SEM006 (Term Valuation), PRIM-SEM007 (Satisfaction), PRIM-SEM008 (Truth in Structure), PRIM-SEM015 (Truth-Value Assignment PL, remark), DEF-SEM001 (Tarski Satisfaction Definition)
- **Prerequisites**: SEM.1, SYN.4
- **Estimated pages**: 6

### SEM.3: Validity and Consequence
- **Sources**: fol/syn/sem (ABSORB:pl/syn/sem), fol/syn/mai (CONDENSE)
- **Taxonomy**: PRIM-SEM009 (Logical Validity), PRIM-SEM010 (Logical Consequence), PRIM-SEM011 (Model), DEF-SEM002 (Satisfiable), DEF-SEM004 (Semantic Consistency), DEF-SEM009 (Tautology PL, remark), DEF-SEM010 (PL Consequence, remark)
- **Prerequisites**: SEM.2
- **Estimated pages**: 4

### SEM.4: Models and Theories
- **Sources**: fol/mat/int (DISTRIBUTE, DEF-SEM007 portion), fol/mat/exs (CONDENSE)
- **Taxonomy**: DEF-SEM005 (Semantic Completeness of theory, from fol/com/ccs), DEF-SEM006 (Theory of Structure), DEF-SEM007 (Definable Set), DEF-SEM008 (Elementary Equivalence)
- **Prerequisites**: SEM.3
- **Estimated pages**: 3

### SEM.5: Arithmetic Models
- **Sources**: inc/int/def (DISTRIBUTE, DEF-SEM017/018 portions)
- **Taxonomy**: DEF-SEM017 (Standard Model of Arithmetic), DEF-SEM018 (True Arithmetic), DEF-SEM019 (Interpretability, remark from inc/tcp/itp)
- **Prerequisites**: SEM.1, SYN.1
- **Estimated pages**: 2

### SEM.6: Model-Theoretic Concepts
- **Sources**: mod/bas/red (CONDENSE), mod/bas/sub (KEEP), mod/bas/ove (CONDENSE), mod/bas/iso (KEEP), mod/bas/thm (KEEP), mod/bas/dlo (KEEP), mod/mar/stm (CONDENSE), mod/mar/nst (CONDENSE), mod/mar/mpa (CONDENSE), mod/mar/cmp (CONDENSE)
- **Taxonomy**: PRIM-SEM012 (Isomorphism), PRIM-SEM013 (Substructure), PRIM-SEM014 (Homomorphism, NEW-CONTENT per A4), DEF-SEM006 (Theory of Structure, from mod/bas/thm), DEF-SEM008 (Elementary Equivalence), DEF-SEM011 (Elementary Substructure), DEF-SEM012 (Diagram, NEW-CONTENT), DEF-SEM013 (Type, NEW-CONTENT), DEF-SEM014 (Categoricity), DEF-SEM015 (Ultraproduct, NEW-CONTENT), DEF-SEM016 (Embedding, NEW-CONTENT), THM-SEM001 (Isomorphism Lemma)
- **Prerequisites**: SEM.3, BST.3, BST.6
- **Estimated pages**: 12

### SEM.7: Theorems
- **Sources**: fol/syn/ext (KEEP)
- **Taxonomy**: THM-SEM002 (Coincidence Lemma), THM-SYN003 (Substitution Lemma)
- **Prerequisites**: SEM.2, SYN.4
- **Estimated pages**: 3

**CH-SEM subtotal**: ~34 pages, 34 taxonomy items (15 PRIM + 16 DEF + 3 THM), 17 surviving sections

---

## CH-DED: Deduction

Prerequisites: CH-SYN, CH-SEM, CH-BST (DED.1 needs only SYN+BST; DED.2–5 need SEM for soundness proofs)

### DED.1: Generic Proof Theory
- **Sources**: fol/axd/rul (KEEP), fol/axd/ptn (ABSORB:ntd/ptn,seq/ptn,tab/ptn), fol/axd/prv (KEEP, absorbs 3 prv), fol/axd/ppr (CONDENSE, absorbs 3 ppr), fol/axd/qpr (CONDENSE, absorbs 3 qpr), fol/ntd/rul (KEEP, PRIM-DED009), fol/seq/rul (KEEP, PRIM-DED008), fol/seq/srl (KEEP, PRIM-DED007)
- **Taxonomy**: PRIM-DED001 (Axiom Schema), PRIM-DED002 (Non-Logical Axiom), PRIM-DED003 (Rule of Inference), PRIM-DED004 (Proof System), PRIM-DED005 (Derivation), PRIM-DED006 (Provability), PRIM-DED007 (Structural Rules), PRIM-DED008 (Sequent), PRIM-DED009 (Assumption Discharge), PRIM-DED010 (Theorem), DEF-DED001 (Syntactic Consistency), DEF-DED002 (Maximal Consistent Set, from fol/com/mcs), DEF-DED003 (Deductive Closure), DEF-DED004 (Conservative Extension, NEW-CONTENT per A4), DEF-DED009 (Derived Rule, FORMALIZE per A4), DEF-DED010 (Admissible Rule, FORMALIZE per A4)
- **Prerequisites**: SYN.2, SYN.3
- **Estimated pages**: 12

### DED.2: Axiomatic (Hilbert) Systems
- **Sources**: fol/prf/axd (CONDENSE), fol/axd/prp (KEEP), fol/axd/qua (KEEP), fol/axd/ded (KEEP), fol/axd/sou (KEEP)
- **Taxonomy**: DEF-DED005 (Hilbert-Style System), AX-DED001 (Modus Ponens), AX-DED002 (Generalization), AX-DED003 (Axiom Schemas), THM-DED001 (Deduction Theorem), CP-001 (Soundness, axiomatic variant), CP-009 (Deduction Theorem)
- **Prerequisites**: DED.1, SEM.2
- **Estimated pages**: 8

### DED.3: Natural Deduction
- **Sources**: fol/prf/ntd (CONDENSE), fol/ntd/rul (KEEP), fol/ntd/prl (KEEP), fol/ntd/qrl (KEEP), fol/ntd/der (CONDENSE), fol/ntd/sou (KEEP, absorbs fol/ntd/sid)
- **Taxonomy**: DEF-DED006 (Natural Deduction), CP-001 (Soundness, ND variant)
- **Prerequisites**: DED.1, SEM.2
- **Estimated pages**: 6

### DED.4: Sequent Calculus
- **Sources**: fol/seq/rul (KEEP), fol/seq/prl (KEEP), fol/seq/srl (KEEP), fol/seq/qrl (KEEP), fol/seq/der (CONDENSE), fol/seq/sou (KEEP, absorbs fol/seq/sid), fol/seq/ide (CONDENSE)
- **Taxonomy**: DEF-DED007 (Sequent Calculus), CP-001 (Soundness, SC variant), CP-010 (Cut Elimination)
- **Prerequisites**: DED.1, SEM.2
- **Estimated pages**: 7

### DED.5: Tableaux
- **Sources**: fol/tab/rul (KEEP), fol/tab/prl (KEEP), fol/tab/qrl (KEEP), fol/tab/der (CONDENSE), fol/tab/sou (KEEP, absorbs fol/tab/sid), fol/tab/ide (CONDENSE)
- **Taxonomy**: DEF-DED008 (Tableau System), CP-001 (Soundness, tableau variant)
- **Prerequisites**: DED.1, SEM.2
- **Estimated pages**: 5

### DED.6: Theories and Arithmetic
- **Sources**: inc/int/def (DISTRIBUTE, DEF-DED011/012 portions), inc/tcp/oqn (CONDENSE, DEF-DED013), inc/inp/prc (KEEP, DEF-DED014)
- **Taxonomy**: DEF-DED011 (Robinson Arithmetic Q), DEF-DED012 (Peano Arithmetic PA), DEF-DED013 (Omega-Consistency), DEF-DED014 (Derivability Conditions)
- **Prerequisites**: DED.1, SYN.5
- **Estimated pages**: 4

### DED.7: Theorems
- **Sources**: fol/axd/ded (KEEP, THM-DED001), inc/inp/fix (KEEP, THM-DED006), inc/inp/lob (KEEP, THM-DED007)
- **Taxonomy**: THM-DED001 (Deduction Theorem, also in DED.2), THM-DED005 (Lindenbaum's Lemma, from fol/com/lin), THM-DED006 (Fixed-Point Lemma), THM-DED007 (Lob's Theorem)
- **Prerequisites**: DED.1, DED.6
- **Estimated pages**: 6

**CH-DED subtotal**: ~48 pages, 30 taxonomy items (10 PRIM + 14 DEF + 3 AX + 3 THM), 29 surviving sections

---

## CH-CMP: Computation

Prerequisites: CH-BST

### CMP.1: Recursive Functions
- **Sources**: cmp/rec/prr (KEEP), cmp/rec/seq (KEEP), cmp/rec/par (KEEP), cmp/rec/prf (ABSORB:pre,com), cmp/rec/cmp (CONDENSE), cmp/rec/bmi (CONDENSE), cmp/rec/npr (CONDENSE)
- **Taxonomy**: PRIM-CMP001 (Computable Function), PRIM-CMP002 (Primitive Recursive Function), PRIM-CMP003 (mu-Recursion), DEF-CMP001 (Partial Function), DEF-CMP002 (Total Function), DEF-CMP003 (Characteristic Function)
- **Prerequisites**: BST.3, BST.4, BST.5
- **Estimated pages**: 10

### CMP.2: Turing Machines
- **Sources**: tur/mac/tur (KEEP), cmp/tur/con (KEEP), tur/mac/ctt (KEEP), tur/mac/una (CONDENSE), tur/mac/dis (CONDENSE), tur/mac/cmb (CONDENSE)
- **Taxonomy**: PRIM-CMP004 (Turing Machine), PRIM-CMP005 (Church-Turing Thesis)
- **Prerequisites**: CMP.1
- **Estimated pages**: 8

### CMP.3: Decidability
- **Sources**: cmp/thy/cps (KEEP), cmp/thy/ces (KEEP), cmp/thy/eqc (KEEP), cmp/thy/clo (CONDENSE), cmp/thy/tot (CONDENSE)
- **Taxonomy**: PRIM-CMP006 (Decidable Set), PRIM-CMP007 (Semi-Decidable Set), DEF-CMP004 (Enumeration), DEF-CMP010 (RE Equiv. Characterizations)
- **Prerequisites**: CMP.1, CMP.2
- **Estimated pages**: 6

### CMP.4: Diagonalization and Halting
- **Sources**: tur/und/hal (ABSORB:cmp/rec/hlt,cmp/thy/hlt), cmp/thy/nou (KEEP), cmp/rec/npr (CONDENSE)
- **Taxonomy**: PRIM-CMP008 (Halting Problem), PRIM-CMP010 (Diagonalization), THM-CMP002 (Halting Unsolvable)
- **Prerequisites**: CMP.2, CMP.3
- **Estimated pages**: 5

### CMP.5: Coding and Universality
- **Sources**: cmp/rec/nft (KEEP, absorbs cmp/thy/nfm), cmp/rec/seq (KEEP), tur/und/enu (KEEP), tur/und/uni (KEEP), tur/und/rep (CONDENSE), tur/und/ver (CONDENSE), inc/art/cod (CONDENSE), inc/art/trm (CONDENSE), inc/art/frm (CONDENSE), inc/art/sub (CONDENSE), inc/art/plk (ABSORB:pnd,pax), inc/int/def (DISTRIBUTE, DEF-CMP009 portion)
- **Taxonomy**: PRIM-CMP011 (Godel Numbering), PRIM-CMP012 (Universal TM), DEF-CMP005 (Index/Program), DEF-CMP006 (Lambda-Definable, reference), DEF-CMP007 (Productive Set, FORMALIZE per A4), DEF-CMP008 (Creative Set), DEF-CMP009 (Representability), DEF-CMP012 (Proof Predicate), DEF-CMP013 (Beta Function), THM-CMP004 (s-m-n / Normal Form)
- **Prerequisites**: CMP.1--CMP.4, SYN.2
- **Estimated pages**: 15

### CMP.6: Computability Theory
- **Sources**: cmp/thy/ncp (KEEP), cmp/thy/cmp (KEEP), cmp/thy/red (KEEP), cmp/thy/ppr (KEEP), cmp/thy/cce (KEEP), cmp/thy/rce (KEEP), cmp/thy/smn (KEEP), inc/int/def (DISTRIBUTE, DEF-CMP011 portion), inc/req/int (CONDENSE), inc/req/rpc (CONDENSE), inc/req/bet (CONDENSE), inc/req/pri (CONDENSE), inc/req/bre (CONDENSE), inc/req/cmp (CONDENSE), inc/req/min (CONDENSE), inc/req/crq (ABSORB:cee,cre), inc/req/rel (CONDENSE)
- **Taxonomy**: PRIM-CMP009 (Many-One Reducibility), DEF-CMP011 (Axiomatizable Theory), DEF-CMP014 (Computable Inseparability), DEF-CMP010 (RE Equiv., supplementary)
- **Prerequisites**: CMP.3, CMP.5
- **Estimated pages**: 12

### CMP.7: Theorems
- **Sources**: tur/und/uns (KEEP), cmp/thy/fix (KEEP), cmp/thy/rce (KEEP), tur/und/dec (CONDENSE), inc/tcp/qce (CONDENSE), inc/tcp/oqn (CONDENSE), inc/tcp/cqn (CONDENSE), inc/tcp/cax (CONDENSE), inc/tcp/cdc (CONDENSE), inc/tcp/ins (CONDENSE), inc/tcp/con (CONDENSE), inc/tcp/itp (CONDENSE)
- **Taxonomy**: THM-CMP001 (Equivalence of Models, remark), THM-CMP003 (Rice's Theorem), THM-CMP005 (Recursion Theorem)
- **Prerequisites**: CMP.4, CMP.5, CMP.6
- **Estimated pages**: 8

**CH-CMP subtotal**: ~64 pages, 28 taxonomy items (12 PRIM + 14 DEF + 2 THM), 36 surviving sections (from CMP batch) + 20 surviving sections (from INC batch feeding into CMP)

---

## CH-META: Metatheory (Composition Patterns)

Prerequisites: CH-SEM, CH-DED, CH-CMP

### META.1: Soundness (CP-001)
- **Sources**: (statement consolidating DED.2--5 per-system proofs)
- **Taxonomy**: CP-001 (Soundness)
- **Prerequisites**: DED.2--DED.5, SEM.3
- **Estimated pages**: 1 (unified statement + references to per-system proofs)

### META.2: Completeness (CP-002)
- **Sources**: fol/com/ccs (KEEP), fol/com/mcs (CONDENSE), fol/com/hen (KEEP), fol/com/lin (KEEP), fol/com/mod (KEEP), fol/com/ide (KEEP), fol/com/cth (KEEP)
- **Taxonomy**: CP-002 (Completeness Theorem), DEF-SEM005 (Complete Consistent Set), DEF-DED002 (Maximal Consistent Set), THM-DED005 (Lindenbaum's Lemma)
- **Prerequisites**: DED.1, SEM.3
- **Estimated pages**: 12

### META.3: Compactness (CP-003)
- **Sources**: fol/com/com (KEEP)
- **Taxonomy**: CP-003 (Compactness), DEF-SEM003 (Finitely Satisfiable)
- **Prerequisites**: META.2
- **Estimated pages**: 3

### META.4: Lowenheim-Skolem (CP-004)
- **Sources**: fol/com/dls (KEEP)
- **Taxonomy**: CP-004 (Lowenheim-Skolem)
- **Prerequisites**: META.2, BST.6
- **Estimated pages**: 3

### META.5: First Incompleteness (CP-005)
- **Sources**: inc/inp/fix (KEEP), inc/inp/1in (ABSORB:inc/tcp/inc), inc/inp/ros (KEEP)
- **Taxonomy**: CP-005 (First Incompleteness Theorem), THM-DED006 (Fixed-Point Lemma)
- **Prerequisites**: DED.6, CMP.5, SEM.5 (standard model, for semantic content of "true but unprovable")
- **Estimated pages**: 8

### META.6: Second Incompleteness (CP-006)
- **Sources**: inc/inp/prc (KEEP), inc/inp/2in (KEEP), inc/inp/lob (KEEP)
- **Taxonomy**: CP-006 (Second Incompleteness Theorem), DEF-DED014 (Derivability Conditions), THM-DED007 (Lob's Theorem)
- **Prerequisites**: META.5
- **Estimated pages**: 6

### META.7: Undefinability (CP-007)
- **Sources**: inc/inp/tar (KEEP)
- **Taxonomy**: CP-007 (Tarski's Undefinability of Truth)
- **Prerequisites**: META.5, SEM.5
- **Estimated pages**: 3

### META.8: Undecidability (CP-008)
- **Sources**: inc/req/und (KEEP)
- **Taxonomy**: CP-008 (Church's Undecidability of Validity)
- **Prerequisites**: CMP.4, SEM.3
- **Estimated pages**: 3

### META.9: Craig Interpolation (CP-011)
- **Sources**: mod/int/sep (CONDENSE), mod/int/prf (KEEP)
- **Taxonomy**: CP-011 (Craig's Interpolation Theorem)
- **Prerequisites**: META.2, SEM.6
- **Estimated pages**: 5

### META.10: Beth Definability (CP-012)
- **Sources**: mod/int/def (KEEP)
- **Taxonomy**: CP-012 (Beth's Definability Theorem)
- **Prerequisites**: META.9
- **Estimated pages**: 3

### META.11: Lindstrom's Theorem (CP-013)
- **Sources**: mod/lin/prf (ABSORB:mod/lin/alg,mod/lin/lsp), mod/bas/pis (CONDENSE)
- **Taxonomy**: CP-013 (Lindstrom's Theorem)
- **Prerequisites**: META.3, META.4, SEM.6
- **Estimated pages**: 5

### META.12: Equivalence of Proof Systems (THM-DED002)
- **Sources**: NEW-CONTENT (from DOMAIN-DEDUCTION.md)
- **Taxonomy**: THM-DED002 (Equivalence of Proof Systems)
- **Prerequisites**: DED.2--DED.5, META.2
- **Estimated pages**: 2

**CH-META subtotal**: ~54 pages, 13 CPs + supplementary items, 15 surviving sections + 8 from INC batch

---

## CH-SET: Formal Set Theory (Level-1)

Prerequisites: CH-SYN, CH-SEM, CH-DED, CH-BST

### SET.1: The Language of Set Theory
- **Sources**: sth/z/sep (KEEP, partial -- language introduction)
- **Taxonomy**: PRIM-SET001 (Set formal, FORMALIZE per A4), PRIM-SET002 (Membership formal), PRIM-SET003 (Class informal)
- **Prerequisites**: SYN.1
- **Estimated pages**: 2

### SET.2: ZFC Axioms
- **Sources**: sth/story/extensionality (KEEP), sth/z/sep (KEEP), sth/z/pairs (KEEP), sth/z/union (KEEP), sth/z/power (KEEP), sth/z/infinity (CONDENSE), sth/z/foundation (CONDENSE), sth/z/replacement (CONDENSE)
- **Taxonomy**: AX-SET001 (Extensionality), AX-SET002 (Empty Set), AX-SET003 (Pairing), AX-SET004 (Union), AX-SET005 (Power Set), AX-SET006 (Separation), AX-SET007 (Replacement), AX-SET008 (Foundation)
- **Prerequisites**: SET.1
- **Estimated pages**: 10

### SET.3: Ordinals
- **Sources**: sth/ordinals/vn (KEEP), sth/ordinals/opps (KEEP), sth/ordinals/basic (KEEP), sth/ordinals/wo (KEEP), sth/ordinals/successor (KEEP), sth/ordinals/replacement (KEEP), sth/ordinals/transfinite (CONDENSE), sth/ordinals/hartogs (CONDENSE)
- **Taxonomy**: DEF-SET001 (Ordinal), DEF-SET002 (Successor Ordinal), DEF-SET003 (Limit Ordinal), DEF-SET004 (omega), DEF-SET005 (Transfinite Induction), DEF-SET006 (Transfinite Recursion), DEF-SET009 (Well-Ordering)
- **Prerequisites**: SET.2, BST.2
- **Estimated pages**: 12

### SET.4: Cardinals
- **Sources**: sth/cardinals/cardsasords (ABSORB:cp partial), sth/cardinals/cp (CONDENSE), sth/cardinals/alephs (CONDENSE), sth/choice/tarskiscott (CONDENSE), sth/choice/hartogs (CONDENSE)
- **Taxonomy**: DEF-SET007 (Cardinal Number), DEF-SET008 (Cardinality formal), DEF-SET013 (Aleph Numbers)
- **Prerequisites**: SET.3
- **Estimated pages**: 8

### SET.5: Advanced Topics
- **Sources**: sth/spine/valpha (KEEP), sth/spine/recursion (KEEP), sth/spine/stages (CONDENSE), sth/spine/separation (CONDENSE), sth/spine/height (CONDENSE), sth/spine/replacement (CONDENSE), sth/replacement/* (CONDENSE, 4 sections), sth/ord-arithmetic/* (CONDENSE, 4 sections), sth/card-arithmetic/opps (KEEP), sth/card-arithmetic/alephs (CONDENSE), sth/card-arithmetic/cardarith (CONDENSE), sth/card-arithmetic/ch (KEEP), sth/card-arithmetic/ineq (CONDENSE), sth/choice/countablechoice (CONDENSE), sth/choice/justifications (CONDENSE)
- **Taxonomy**: DEF-SET010 (Zorn's Lemma), DEF-SET011 (Cantor's Theorem formal), DEF-SET012 (Von Neumann Hierarchy), DEF-SET014 (Cofinality, deferred), DEF-SET015 (Continuum Hypothesis)
- **Prerequisites**: SET.3, SET.4
- **Estimated pages**: 18

### SET.6: Theorems
- **Sources**: sth/choice/woproblem (KEEP)
- **Taxonomy**: AX-SET009 (Choice/Well-Ordering), THM-SET001 (WO iff Zorn iff AC), THM-SET002 (Transfinite Recursion Theorem), THM-SET003 (Cantor's Theorem in ZFC)
- **Prerequisites**: SET.3, SET.4, SET.5
- **Estimated pages**: 5

**CH-SET subtotal**: ~55 pages, 30 taxonomy items (3 PRIM + 15 DEF + 9 AX + 3 THM), 45 surviving sections

---

## CH-EXT: Extensions (Stubs)

Prerequisites: all core chapters

### EXT.1: Modal Logic
- **Sources**: 69 normal-modal-logic/ + 16 applied-modal-logic/ sections (all DEFER-TO-EXTENSION)
- **Pointer**: OL content/normal-modal-logic/ and content/applied-modal-logic/
- **Estimated pages**: 1 (stub)

### EXT.2: Intuitionistic Logic
- **Sources**: 34 intuitionistic-logic/ sections (all DEFER-TO-EXTENSION)
- **Pointer**: OL content/intuitionistic-logic/
- **Estimated pages**: 1 (stub)

### EXT.3: Many-Valued Logic
- **Sources**: 25 many-valued-logic/ sections (all DEFER-TO-EXTENSION)
- **Pointer**: OL content/many-valued-logic/
- **Estimated pages**: 1 (stub)

### EXT.4: Second-Order Logic
- **Sources**: 20 second-order-logic/ sections (all DEFER-TO-EXTENSION)
- **Pointer**: OL content/second-order-logic/
- **Estimated pages**: 1 (stub)

### EXT.5: Lambda Calculus
- **Sources**: 44 lambda-calculus/ sections (all DEFER-TO-EXTENSION)
- **Pointer**: OL content/lambda-calculus/
- **Estimated pages**: 1 (stub)

### EXT.6: Other Extensions
- **Sources**: 13 counterfactuals/ + 19 methods/ + 20 history/ + 3 reference/ sections (all DEFER-TO-EXTENSION)
- **Pointer**: OL remaining content areas
- **Estimated pages**: 1 (stub)

**CH-EXT subtotal**: 6 pages (stubs only), 263 extension sections deferred

---

## Global Summary

| Chapter | Taxonomy Items | Surviving Sections | Estimated Pages |
|---------|---------------|-------------------|-----------------|
| CH-BST | 24 | 28 | 38 |
| CH-SYN | 30 | 10 | 21 |
| CH-SEM | 34 | 17 | 34 |
| CH-DED | 30 | 29 | 48 |
| CH-CMP | 28 | 56 (CMP+INC) | 64 |
| CH-META | 13 CPs + supp. | 23 | 54 |
| CH-SET | 30 | 45 | 55 |
| CH-EXT | (pointers) | 6 stubs | 6 |
| **Total** | **205** | **~214** | **~320** |

**Dependency order**: CH-BST -> CH-SYN -> CH-SEM / CH-DED (parallel) -> CH-CMP -> CH-META -> CH-SET -> CH-EXT

**NEW-CONTENT items** (4, per A4): DEF-DED004 (DED.1), DEF-SYN002 (SYN.4), DEF-SYN004 (SYN.4), THM-DED002 (META.12)

**FORMALIZE items** (6, per A4): DEF-CMP007 (CMP.5), DEF-DED009 (DED.1), DEF-DED010 (DED.1), DEF-SYN007 (SYN.2), THM-SYN004 (SYN.6), PRIM-SET001 (SET.1)

**DISTRIBUTE sections** (2): inc/int/def -> DED.6 + SEM.5 + CMP.5 + CMP.6; fol/mat/int -> DED.1 + SEM.4
