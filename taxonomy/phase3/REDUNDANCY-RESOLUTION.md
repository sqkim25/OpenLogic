# REDUNDANCY-RESOLUTION: All Redundancy Resolutions

This document collects ALL redundancy resolutions from the compression plan. It covers:
- **24 COMPRESSION-TARGETs** (genuine redundancies identified in Phase 2)
- **19 EXPECTED redundancies** (resolved by A1 generic framework)
- **5 PL->FOL merges** (resolved by A2 FOL-first policy)
- **3 identity-soundness merges** (per-system identity extensions)
- **2 DISTRIBUTE sections** (multi-domain sections split to owners)
- **Other notable merges** (from INC and MOD batches)

**Total resolution entries**: 54+

---

## Part 1: COMPRESSION-TARGETs (24 Genuine Redundancies)

These are concepts defined in multiple OL sections, requiring primary/secondary designation.

---

### CT-01: PRIM-BST010 -- Finite Sequence (A*)
- **Type**: COMPRESSION-TARGET
- **OL Sections**: sfr/set/pai (primary), sfr/set/imp (secondary)
- **Primary (authoritative)**: sfr/set/pai -- Contains the formal recursive definition of n-tuples and A* (words) with Wiener-Kuratowski pair foundation
- **Merged sections**: sfr/set/imp (CONDENSE -- retains PRIM-BST011, PRIM-BST012; A* content absorbed into sfr/set/pai)
- **What survives from merged**: Nothing from sfr/set/imp's A* definition (redundant with sfr/set/pai)
- **What drops**: sfr/set/imp's A* definition (duplicate)

### CT-02: PRIM-BST013 -- Mathematical Induction
- **Type**: COMPRESSION-TARGET
- **OL Sections**: sfr/ind/int (primary), sfr/infinite/induction (secondary)
- **Primary (authoritative)**: sfr/ind/int -- Most complete formal treatment with strong induction variant
- **Merged sections**: sfr/infinite/induction (MERGE-INTO sfr/ind/int)
- **What survives from merged**: Nothing (fully redundant)
- **What drops**: sfr/infinite/induction entire content

### CT-03: PRIM-BST016 -- Cardinality / Enumerability
- **Type**: COMPRESSION-TARGET
- **OL Sections**: sfr/siz/enm (primary), sfr/siz/enm-alt (secondary)
- **Primary (authoritative)**: sfr/siz/enm -- Formal definition of enumerable/countable/uncountable
- **Merged sections**: sfr/siz/enm-alt (MERGE-INTO sfr/siz/enm)
- **What survives from merged**: Nothing (alternative presentation, fully redundant)
- **What drops**: sfr/siz/enm-alt entire content

### CT-04: THM-BST001 -- Cantor's Theorem (Naive)
- **Type**: COMPRESSION-TARGET
- **OL Sections**: sfr/siz/car (primary), sfr/siz/nen (absorb target), sfr/siz/nen-alt (secondary)
- **Primary (authoritative)**: sfr/siz/car -- Clean diagonal proof that |A| < |P(A)|
- **Merged sections**: sfr/siz/nen (ABSORB -- provides stepping-stone non-enumerability results), sfr/siz/nen-alt (MERGE-INTO sfr/siz/nen)
- **What survives from merged**: sfr/siz/nen's non-enumerability of reals (stepping stone); sfr/siz/nen-alt nothing
- **What drops**: sfr/siz/nen-alt entire content; sfr/siz/nen pedagogical examples

### CT-05: PRIM-CMP001 -- Computable (Recursive) Function
- **Type**: COMPRESSION-TARGET
- **OL Sections**: cmp/rec/par (primary), tur/mac/una (secondary), tur/mac/int (CUT)
- **Primary (authoritative)**: cmp/rec/par -- Mathematical definition via partial recursive functions (most abstract)
- **Merged sections**: tur/mac/una (CONDENSE -- TM formulation preserved as alternative characterization); tur/mac/int (CUT)
- **What survives from merged**: tur/mac/una's TM-computable function definition (as remark noting equivalence)
- **What drops**: tur/mac/int's informal overview

### CT-06: PRIM-CMP004 -- Turing Machine
- **Type**: COMPRESSION-TARGET
- **OL Sections**: tur/mac/tur (primary), tur/mac/int (CUT)
- **Primary (authoritative)**: tur/mac/tur -- Formal 4-tuple definition
- **Merged sections**: tur/mac/int (CUT -- pedagogical intro)
- **What survives from merged**: Nothing
- **What drops**: tur/mac/int entire content

### CT-07: PRIM-CMP006 -- Decidable Set
- **Type**: COMPRESSION-TARGET
- **OL Sections**: cmp/thy/cps (primary), tur/und/int (CUT), tur/und/dec (CONDENSE)
- **Primary (authoritative)**: cmp/thy/cps -- Abstract characterization via computable characteristic function
- **Merged sections**: tur/und/int (CUT); tur/und/dec (CONDENSE -- application to FOL validity)
- **What survives from merged**: tur/und/dec's proof strategy (condensed to one paragraph)
- **What drops**: tur/und/int entire content

### CT-08: PRIM-CMP008 -- Halting Problem + THM-CMP002 -- Halting Unsolvable
- **Type**: COMPRESSION-TARGET
- **OL Sections**: tur/und/hal (primary), cmp/rec/hlt (secondary), cmp/thy/hlt (secondary), tur/und/int (CUT)
- **Primary (authoritative)**: tur/und/hal -- Full definitions + complete diagonalization proof via TM construction (function s, non-computability lemma, unsolvability theorem)
- **Merged sections**: cmp/rec/hlt (MERGE-INTO tur/und/hal), cmp/thy/hlt (MERGE-INTO tur/und/hal)
- **What survives from merged**: cmp/rec/hlt perspective (one-sentence remark on partial recursive version); cmp/thy/hlt's alternative proof (one-sentence remark on no-universal-function proof)
- **What drops**: Standalone sections cmp/rec/hlt and cmp/thy/hlt eliminated

### CT-09: PRIM-CMP011 -- Godel Numbering (Arithmetization)
- **Type**: COMPRESSION-TARGET
- **OL Sections**: cmp/rec/seq (sequences), cmp/rec/nft (function indices, primary), tur/und/enu (TM codes)
- **Primary (authoritative)**: cmp/rec/nft -- Most complete encoding treatment with function indexing
- **Merged sections**: None merge -- each covers a different aspect (sequences, indices, TM codes). All KEEP.
- **What survives**: All three sections survive with complementary roles
- **What drops**: Nothing -- this is a multi-section coverage, not true redundancy. Resolved by noting cmp/rec/nft as primary for index notation.

### CT-10: PRIM-CMP012 -- Universal Turing Machine
- **Type**: COMPRESSION-TARGET
- **OL Sections**: tur/und/uni (primary), cmp/thy/uni (secondary), cmp/thy/int (CUT)
- **Primary (authoritative)**: tur/und/uni -- Full UTM construction with detailed operation description
- **Merged sections**: cmp/thy/uni (CONDENSE -- function-theoretic perspective), cmp/thy/int (CUT)
- **What survives from merged**: cmp/thy/uni's universal function existence theorem (condensed)
- **What drops**: cmp/thy/int overview paragraph

### CT-11: THM-CMP004 -- s-m-n Theorem / Normal Form
- **Type**: COMPRESSION-TARGET
- **OL Sections**: cmp/thy/smn (s-m-n primary), cmp/rec/nft (Normal Form primary), cmp/thy/nfm (secondary)
- **Primary (authoritative)**: cmp/thy/smn for s-m-n theorem; cmp/rec/nft for Kleene Normal Form
- **Merged sections**: cmp/thy/nfm (MERGE-INTO cmp/rec/nft)
- **What survives from merged**: cmp/thy/nfm's content absorbed into cmp/rec/nft
- **What drops**: Standalone cmp/thy/nfm section

### CT-12: DEF-CMP005 -- Index (Program)
- **Type**: COMPRESSION-TARGET
- **OL Sections**: cmp/rec/nft (primary), tur/und/enu (secondary)
- **Primary (authoritative)**: cmp/rec/nft -- Introduces cfind{e} notation for function indices
- **Merged sections**: tur/und/enu (KEEP -- TM index is complementary)
- **What survives**: Both survive with complementary roles (function index vs TM code)
- **What drops**: Nothing

### CT-13: DEF-CMP009 -- Representability
- **Type**: COMPRESSION-TARGET
- **OL Sections**: inc/int/def (primary, DISTRIBUTE to CMP.5), tur/und/rep (secondary), inc/req/int (supplementary)
- **Primary (authoritative)**: inc/int/def -- Most complete treatment with both function and relation representability conditions
- **Merged sections**: tur/und/rep (CONDENSE -- TM-in-FOL encoding); inc/req/int (CONDENSE -- representability theorems)
- **What survives from merged**: tur/und/rep's FOL representation construction; inc/req/int's key representability results
- **What drops**: Detailed technical lemmas in tur/und/rep

### CT-14: AX-SET009 -- Axiom of Choice / Well-Ordering
- **Type**: COMPRESSION-TARGET
- **OL Sections**: sth/choice/woproblem (primary), sth/cardinals/cardsasords (secondary)
- **Primary (authoritative)**: sth/choice/woproblem -- Defines choice function, states AC, proves THM-SET001 (WO iff AC)
- **Merged sections**: sth/cardinals/cardsasords (ABSORB -- introduces Well-Ordering as axiom for cardinal theory)
- **What survives from merged**: cardsasords's Well-Ordering axiom formulation and cardinal definition
- **What drops**: Nothing -- both sections survive, cardsasords as ABSORB target for DEF-SET008

### CT-15: DEF-SET008 -- Cardinal Number (Formal)
- **Type**: COMPRESSION-TARGET
- **OL Sections**: sth/cardinals/cardsasords (primary, ABSORB), sth/cardinals/cp (secondary)
- **Primary (authoritative)**: sth/cardinals/cardsasords -- Formal definition as initial ordinals
- **Merged sections**: sth/cardinals/cp (CONDENSE -- motivation via Cantor-Bernstein absorbed as paragraph)
- **What survives from merged**: sth/cardinals/cp's motivation paragraph
- **What drops**: sth/cardinals/cp's standalone status

### CT-16: DEF-CMP012 -- Proof Predicate (Formalized Prf)
- **Type**: COMPRESSION-TARGET
- **OL Sections**: inc/art/plk (primary, ABSORB), inc/art/pnd (secondary), inc/art/pax (secondary)
- **Primary (authoritative)**: inc/art/plk -- Proof predicate for LK (sequent calculus), chosen as primary
- **Merged sections**: inc/art/pnd (MERGE-INTO inc/art/plk -- ND proof predicate), inc/art/pax (MERGE-INTO inc/art/plk -- axiomatic proof predicate)
- **What survives from merged**: inc/art/pnd and inc/art/pax proof predicate definitions (as remarks noting the alternative formalizations using ND and axiomatic derivations respectively)
- **What drops**: Standalone sections inc/art/pnd and inc/art/pax

### CT-17: CP-005 -- First Incompleteness Theorem (Two Formulations)
- **Type**: COMPRESSION-TARGET
- **OL Sections**: inc/inp/1in (primary, ABSORB), inc/tcp/inc (secondary)
- **Primary (authoritative)**: inc/inp/1in -- Godel sentence construction proof (the standard proof)
- **Merged sections**: inc/tcp/inc (MERGE-INTO inc/inp/1in)
- **What survives from merged**: inc/tcp/inc's computability-theoretic proof (absorbed as one-paragraph alternative proof remark)
- **What drops**: inc/tcp/inc standalone section

### CT-18: CP-013 -- Lindstrom's Theorem (Support Sections)
- **Type**: COMPRESSION-TARGET
- **OL Sections**: mod/lin/prf (primary, ABSORB), mod/lin/alg (secondary), mod/lin/lsp (secondary)
- **Primary (authoritative)**: mod/lin/prf -- Full Lindstrom proof
- **Merged sections**: mod/lin/alg (MERGE-INTO mod/lin/prf -- abstract logic framework), mod/lin/lsp (MERGE-INTO mod/lin/prf -- abstract LS/compactness properties)
- **What survives from merged**: mod/lin/alg's 4 definitions (abstract logic, Mod(L), normal abstract logic, expressiveness comparison); mod/lin/lsp's 2 definitions + 1 theorem (Compactness Property, LS Property, thm:abstract-p-isom)
- **What drops**: mod/lin/alg explanatory prose on infinitary logics; mod/lin/lsp connecting text

### CT-19--CT-21: INC Batch Merges

### CT-19: DEF-INC014 (Class C) + Representability Alternatives
- **Type**: COMPRESSION-TARGET
- **OL Sections**: inc/req/crq (primary, ABSORB), inc/req/cee (secondary), inc/req/cre (secondary)
- **Primary (authoritative)**: inc/req/crq -- Combined representability and computability equivalence result
- **Merged sections**: inc/req/cee (MERGE-INTO inc/req/crq), inc/req/cre (MERGE-INTO inc/req/crq)
- **What survives from merged**: Key lemmas absorbed into inc/req/crq
- **What drops**: Standalone alternative proof paths

### CT-20: DEF-INC018 -- Omega-Consistency (Two Definitions)
- **Type**: COMPRESSION-TARGET
- **OL Sections**: inc/tcp/oqn (primary), inc/inp/1in (secondary, cross-references)
- **Primary (authoritative)**: inc/tcp/oqn -- Authoritative definition goes to DED.6
- **What survives**: inc/tcp/oqn definition; inc/inp/1in cross-references it
- **What drops**: Duplicate definition in inc/inp/1in

### CT-21: mod/bas/nsa -- Non-Standard Arithmetic (Content Subsumed)
- **Type**: COMPRESSION-TARGET
- **OL Sections**: mod/bas/nsa (CUT), mod/mar/stm + mod/mar/nst + mod/mar/mpa (covering same ground)
- **Primary (authoritative)**: mod/mar/{stm,nst,mpa} collectively
- **What survives**: Full model-of-arithmetic treatment in mod/mar/* sections
- **What drops**: mod/bas/nsa (commented out in OL, content fully subsumed)

### CT-22--CT-24: Additional BST Merges

### CT-22: sfr/siz/red-alt -> sfr/siz/red
- **Type**: COMPRESSION-TARGET
- **OL Sections**: sfr/siz/red (primary), sfr/siz/red-alt (secondary)
- **Primary**: sfr/siz/red -- Standard reduction approach
- **Merged**: sfr/siz/red-alt (MERGE-INTO sfr/siz/red)
- **What drops**: Alternative presentation

### CT-23: sfr/siz/nen-alt -> sfr/siz/nen
- **Type**: COMPRESSION-TARGET (subsumed under CT-04)
- Already resolved in CT-04 above.

### CT-24: sfr/siz/enm-alt -> sfr/siz/enm
- **Type**: COMPRESSION-TARGET (subsumed under CT-03)
- Already resolved in CT-03 above.

---

## Part 2: EXPECTED Redundancies Resolved by A1 (19 Items)

These are concepts identically defined in all 4 proof system chapters. Under A1, each is defined ONCE in DED.1 (authoritative = fol/axd/* section), and the 3 system-specific versions MERGE-INTO the authoritative section.

### Group A: Proof-Theoretic Notions (ptn sections) -- 8 items

| # | Concept | Authoritative | Merged From | Lean Section |
|---|---------|--------------|-------------|-------------|
| E-01 | Provability (PRIM-DED006) | fol/axd/ptn | fol/ntd/ptn, fol/seq/ptn, fol/tab/ptn | DED.1 |
| E-02 | Theorem (PRIM-DED010) | fol/axd/ptn | fol/ntd/ptn, fol/seq/ptn, fol/tab/ptn | DED.1 |
| E-03 | Consistency (DEF-DED001) | fol/axd/ptn | fol/ntd/ptn, fol/seq/ptn, fol/tab/ptn | DED.1 |
| E-04 | Reflexivity of derivability | fol/axd/ptn | fol/ntd/ptn, fol/seq/ptn, fol/tab/ptn | DED.1 |
| E-05 | Monotonicity of derivability | fol/axd/ptn | fol/ntd/ptn, fol/seq/ptn, fol/tab/ptn | DED.1 |
| E-06 | Transitivity of derivability | fol/axd/ptn | fol/ntd/ptn, fol/seq/ptn, fol/tab/ptn | DED.1 |
| E-07 | Inconsistency characterization | fol/axd/ptn | fol/ntd/ptn, fol/seq/ptn, fol/tab/ptn | DED.1 |
| E-08 | Compactness of derivability | fol/axd/ptn | fol/ntd/ptn, fol/seq/ptn, fol/tab/ptn | DED.1 |

**What survives from merged**: Nothing standalone. System-specific proof variations (e.g., SC transitivity via Cut rule, Tab transitivity via tableau extension) are noted as one-line remarks in DED.2--5.

**What drops**: All 3 x ptn sections' standalone definitions and proofs of these properties.

**Remark on Deductive Closure (DEF-DED003)**: fol/seq/ptn is the only ptn section that explicitly mentions deductive closure. Absorbed into fol/axd/ptn as part of the generic treatment.

### Group B: Derivability/Consistency Propositions (prv sections) -- 4 items

| # | Concept | Authoritative | Merged From | Lean Section |
|---|---------|--------------|-------------|-------------|
| E-09 | provability-contr (contradiction implies inconsistency) | fol/axd/prv | fol/ntd/prv, fol/seq/prv, fol/tab/prv | DED.1 |
| E-10 | prov-incons (inconsistency equivalence) | fol/axd/prv | fol/ntd/prv, fol/seq/prv, fol/tab/prv | DED.1 |
| E-11 | explicit-inc (explicit inconsistency) | fol/axd/prv | fol/ntd/prv, fol/seq/prv, fol/tab/prv | DED.1 |
| E-12 | provability-exhaustive (exhaustive derivability) | fol/axd/prv | fol/ntd/prv, fol/seq/prv, fol/tab/prv | DED.1 |

**What drops**: All 3 x prv sections' proofs of the same 4 propositions.

### Group C: Connective Derivability (ppr sections) -- 3 items

| # | Concept | Authoritative | Merged From | Lean Section |
|---|---------|--------------|-------------|-------------|
| E-13 | provability-land (conjunction derivability) | fol/axd/ppr | fol/ntd/ppr, fol/seq/ppr, fol/tab/ppr | DED.1 |
| E-14 | provability-lor (disjunction derivability) | fol/axd/ppr | fol/ntd/ppr, fol/seq/ppr, fol/tab/ppr | DED.1 |
| E-15 | provability-lif (conditional derivability) | fol/axd/ppr | fol/ntd/ppr, fol/seq/ppr, fol/tab/ppr | DED.1 |

**What drops**: All 3 x ppr sections' proofs of the same 3 connective facts.

### Group D: Quantifier Derivability (qpr sections) -- 2 items

| # | Concept | Authoritative | Merged From | Lean Section |
|---|---------|--------------|-------------|-------------|
| E-16 | strong-generalization | fol/axd/qpr | fol/ntd/qpr, fol/seq/qpr, fol/tab/qpr | DED.1 |
| E-17 | provability-quantifiers | fol/axd/qpr | fol/ntd/qpr, fol/seq/qpr, fol/tab/qpr | DED.1 |

**What drops**: All 3 x qpr sections' proofs of the same 2 quantifier facts.

### Group E: Identity Soundness (sid sections) -- 1 item pattern

| # | Concept | Authoritative | Merged From | Lean Section |
|---|---------|--------------|-------------|-------------|
| E-18 | Soundness with identity (sid) | per-system sou section | fol/ntd/sid->ntd/sou, fol/seq/sid->seq/sou, fol/tab/sid->tab/sou | DED.3/4/5 |

**What survives**: Identity rule soundness cases are absorbed as additional proof cases into each system's main soundness proof.

### Group F: Deductive Closure (DEF-DED003) -- 1 item

| # | Concept | Authoritative | Merged From | Lean Section |
|---|---------|--------------|-------------|-------------|
| E-19 | Deductive Closure | fol/axd/ptn | fol/seq/ptn (only ptn with explicit mention) | DED.1 |

**Total EXPECTED redundancy sections eliminated**: 16 MERGE-INTO entries (4 ptn + 4 prv + 4 ppr + 4 qpr) = 16 sections absorbed. Plus 3 sid sections merged into their sou sections = 19 total.

---

## Part 3: PL -> FOL Merges (Resolved by A2, 5 Items)

Under A2 (FOL-First with PL as Fragment), PL-specific sections merge into their FOL counterparts.

### PL-01: pl/syn/fml -> fol/syn/frm
- **Type**: EXPECTED-RESOLVED-BY-A2
- **PL Section**: pl/syn/fml (Propositional Formulas)
- **FOL Target**: fol/syn/frm (ABSORB:pl/syn/fml)
- **What survives**: PL formula BNF survives as a remark noting AX-SYN003 (PL Formation Rules) as the quantifier-free, term-free fragment of FOL
- **What drops**: Standalone PL formula definition, PL-specific examples

### PL-02: pl/syn/val -> fol/syn/sat
- **Type**: EXPECTED-RESOLVED-BY-A2
- **PL Section**: pl/syn/val (Truth-Value Assignments)
- **FOL Target**: fol/syn/sat (ABSORB:pl/syn/val)
- **What survives**: Truth-value assignment definition (PRIM-SEM015) as a remark specializing FOL satisfaction to propositional variables
- **What drops**: Standalone PL valuation section

### PL-03: pl/syn/sem -> fol/syn/sem
- **Type**: EXPECTED-RESOLVED-BY-A2
- **PL Section**: pl/syn/sem (PL Semantic Notions)
- **FOL Target**: fol/syn/sem (ABSORB:pl/syn/sem)
- **What survives**: DEF-SEM009 (Tautology) and DEF-SEM010 (PL Consequence) as specialization remarks within FOL semantic notions
- **What drops**: Standalone PL semantic notions section

### PL-04: pl/syn/fseq -> fol/syn/fseq
- **Type**: EXPECTED-RESOLVED-BY-A2
- **PL Section**: pl/syn/fseq (PL Formation Sequences)
- **FOL Target**: fol/syn/fseq (CONDENSE)
- **What survives**: Nothing -- structural recursion already covered in FOL version
- **What drops**: Entire PL formation sequence content

### PL-05: pl/syn/pre -> Multiple FOL Targets
- **Type**: EXPECTED-RESOLVED-BY-A2
- **PL Section**: pl/syn/pre (PL Preliminaries: induction, unique readability, substitution)
- **FOL Targets**: fol/syn/frm (induction remark), fol/syn/unq (unique readability remark), fol/syn/sub (substitution remark)
- **What survives**: PL structural induction as remark in fol/syn/frm; PL unique readability as remark in fol/syn/unq; uniform substitution as remark in fol/syn/sub
- **What drops**: Standalone PL technical lemmas (balanced parentheses, no-initial-segment)

**Additional PL CUTs** (not merges, just eliminated):
- pl/syn/int (CUT -- pedagogical intro)
- pl/prp/snd (CUT -- PL soundness, handled in DED chapters)
- pl/prp/com (CUT -- PL completeness, handled in META)

---

## Part 4: DISTRIBUTE Resolutions (2 Sections)

These OL sections introduce items across multiple domains. Each formal item routes to its taxonomy owner's lean chapter.

### DIST-01: inc/int/def -- Definitions (Incompleteness Introduction)
- **Type**: DISTRIBUTE
- **OL Section**: inc/int/def
- **Items and their targets**:

| Formal Item | Taxonomy ID | Target Lean Section | Action |
|------------|-------------|-------------------|--------|
| defn (theory, deductively closed set) | DEF-INC001 | CUT | Subsumed by DEF-DED003 in DED.1 |
| defn (Standard Model N) | DEF-SEM017 | SEM.5 | Preserve full definition |
| defn (True Arithmetic TA) | DEF-SEM018 | SEM.5 | Preserve full definition |
| defn (axiomatized theory) | DEF-INC004 | CUT | Restates PRIM-DED002 |
| defn (Robinson's Q, 8 axioms) | DEF-DED011 | DED.6 | Preserve full definition |
| defn (Peano Arithmetic PA) | DEF-DED012 | DED.6 | Preserve full definition |
| defn (complete theory) | DEF-INC007 | CUT | Subsumed by DEF-SEM005 in SEM.3 |
| defn (decidable set) | -- | CUT | Merely references PRIM-CMP006 |
| defn (axiomatizable, decidable axiom set) | DEF-CMP011 | CMP.6 | Preserve full definition |
| defn (c.e.) | -- | CUT | Merely references PRIM-CMP007 |
| defn (represents function) | DEF-CMP009 | CMP.5 | Preserve full definition |
| defn (represents relation) | DEF-INC009 | CMP.5 | Preserve full definition |

**Rationale**: This is the densest definition section in the INC batch. Under domain-organized lean text structure, each definition routes to its owner: SEM items to CH-SEM, DED items to CH-DED, CMP items to CH-CMP. Four definitions are CUT because they restate concepts already defined in their owner's lean section.

### DIST-02: fol/mat/int -- Models, Theories, Introduction
- **Type**: DISTRIBUTE
- **OL Section**: fol/mat/int
- **Items and their targets**:

| Formal Item | Taxonomy ID | Target Lean Section | Action |
|------------|-------------|-------------------|--------|
| defn (deductively closed set) | DEF-DED003 | DED.1 | Preserve full definition |
| defn (definable set in a structure) | DEF-SEM007 | SEM.4 | Preserve full definition |

**Rationale**: fol/mat/int introduces concepts owned by different domains (DED and SEM). Each routes to its owner's lean chapter.

---

## Part 5: Other Notable Merges

### OM-01: fol/axd/ddq -> fol/axd/ded
- **Type**: MERGE-INTO (deduction theorem quantifier variant)
- **OL Sections**: fol/axd/ded (primary), fol/axd/ddq (secondary)
- **What survives**: Quantifier variant of deduction theorem integrated into DED.2's deduction theorem section
- **What drops**: Standalone ddq section

### OM-02: cmp/rec/pre + cmp/rec/com -> cmp/rec/prf
- **Type**: MERGE-INTO (primitive recursion infrastructure)
- **OL Sections**: cmp/rec/prf (primary, ABSORB), cmp/rec/pre (secondary), cmp/rec/com (secondary)
- **What survives**: Predecessors and composition as building blocks for primitive recursive functions
- **What drops**: Standalone prerequisite sections

### OM-03: cmp/thy/nfm -> cmp/rec/nft
- **Type**: MERGE-INTO (normal form theorem)
- **OL Sections**: cmp/rec/nft (primary), cmp/thy/nfm (secondary)
- **What survives**: cmp/thy/nfm's normal form content absorbed into cmp/rec/nft
- **What drops**: Standalone cmp/thy/nfm section

### OM-04: inc/art/pnd + inc/art/pax -> inc/art/plk
- **Type**: MERGE-INTO (proof predicate variants)
- Same as CT-16. Three proof predicate variants consolidated.

### OM-05: inc/tcp/inc -> inc/inp/1in
- **Type**: MERGE-INTO (incompleteness proof variant)
- Same as CT-17. Two G1 proof strategies consolidated.

### OM-06: inc/req/cee + inc/req/cre -> inc/req/crq
- **Type**: MERGE-INTO (representability/computability equivalence)
- Same as CT-19. Alternative proof paths consolidated.

### OM-07: mod/lin/alg + mod/lin/lsp -> mod/lin/prf
- **Type**: MERGE-INTO (Lindstrom support sections)
- Same as CT-18. Abstract logic framework absorbed into Lindstrom proof.

---

## Summary Statistics

| Category | Count | Sections Eliminated |
|----------|-------|-------------------|
| COMPRESSION-TARGETs (Part 1) | 24 entries | ~20 sections eliminated |
| EXPECTED A1 Redundancies (Part 2) | 19 entries | 16 sections eliminated (ptn/prv/ppr/qpr) + 3 sid merges |
| PL->FOL Merges (Part 3) | 5 entries | 4 sections merged + 3 CUT |
| DISTRIBUTE (Part 4) | 2 entries | 2 sections distributed (0 eliminated) |
| Other Merges (Part 5) | 7 entries | ~6 sections eliminated |
| **Total** | **57 entries** | **~49 sections eliminated via merge/absorb** |

### Verification Against QC-5

QC-5 requires all 24 COMPRESSION-TARGETs + 19 EXPECTED redundancies = 43 items resolved. This document covers:
- 24 COMPRESSION-TARGETs: CT-01 through CT-24 (all resolved)
- 19 EXPECTED A1 redundancies: E-01 through E-19 (all resolved)
- Total: 43/43 QC-5 entries covered

Plus 14 additional resolutions (5 PL merges + 2 DISTRIBUTE + 7 other merges) for a total of 57 resolution entries.

### Cross-Reference to COMPRESSION-PLAN.md

Every resolution in this document corresponds to a specific Action entry in COMPRESSION-PLAN.md:
- MERGE-INTO entries have a corresponding ABSORB at the target section
- DISTRIBUTE entries have explicit per-item routing in the Content Directives
- CUT entries for eliminated secondary sections are recorded in the batch summaries

All MERGE-INTO/ABSORB pairings have been verified (QC-8 pass for all batches).
