# D2: Concept Index — Taxonomy ID to OL Sections

Reverse index from each taxonomy item to the OL sections that introduce or reference it.
**Taxonomy items (post-Phase 2.5)**: 205 (192 PRIM/DEF/AX/THM + 13 CPs)
**Phase 2.5 additions**: 16 new items (former DEF-INC -> assigned to existing domains)
**Phase 2.5 upgrades**: 3 DEFERRED -> FULL, 1 IMPLICIT -> FULL

---

## Deduction (DED)

### AX-DED001 — Modus Ponens
- **Defined in**: fol/axd/prp (primary)
- **Referenced in**: fol/axd/rul, fol/axd/ppr, fol/axd/ded, fol/axd/ide, fol/axd/ddq, fol/axd/pro, fol/axd/prq, fol/seq/ppr, fol/prf/axd
- **Coverage**: FULL
- **Redundancy**: None

### AX-DED002 — Universal Generalization
- **Defined in**: fol/axd/qua (primary)
- **Referenced in**: fol/axd/qpr, fol/seq/qpr
- **Coverage**: FULL
- **Redundancy**: None

### AX-DED003 — Logical Axiom Schemas
- **Defined in**: fol/axd/prp (primary)
- **Also introduced in**: fol/axd/qua
- **Referenced in**: fol/axd/pro, fol/prf/axd
- **Coverage**: FULL
- **Redundancy**: EXPECTED: Proof system variants (2 sections)

## Set-Formal (SET)

### AX-SET001 — Extensionality
- **Defined in**: sth/story/extensionality (primary)
- **Referenced in**: sth/story/rus, sth/z/sep, sth/z/pairs, sth/z/milestone, sth/z/arbintersections, sth/ordinals/zfm, sth/spine/zf, sth/cardinals/zfc
- **Coverage**: FULL
- **Redundancy**: None

### AX-SET002 — Pairing
- **Defined in**: sth/z/sep (primary)
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: None

### AX-SET003 — Union
- **Defined in**: sth/z/pairs (primary)
- **Referenced in**: sth/z/power, sth/z/infinity-again, sth/z/milestone, sth/ordinals/zfm
- **Coverage**: FULL
- **Redundancy**: None

### AX-SET004 — Power Set
- **Defined in**: sth/z/union (primary)
- **Referenced in**: sth/z/pairs, sth/z/milestone, sth/ordinals/zfm
- **Coverage**: FULL
- **Redundancy**: None

### AX-SET005 — Infinity
- **Defined in**: sth/z/power (primary)
- **Referenced in**: sth/z/milestone, sth/ordinals/zfm, sth/spine/valpha, sth/choice/woproblem
- **Coverage**: FULL
- **Redundancy**: None

### AX-SET006 — Separation
- **Defined in**: sth/z/sep (primary)
- **Referenced in**: sth/z/union, sth/z/power, sth/z/infinity-again, sth/z/milestone, sth/z/arbintersections, sth/ordinals/replacement, sth/ordinals/zfm, sth/replacement/refproofs, sth/choice/hartogs
- **Coverage**: FULL
- **Redundancy**: None

### AX-SET007 — Replacement
- **Defined in**: sth/ordinals/replacement (primary)
- **Referenced in**: sth/ordinals/zfm, sth/ordinals/ordtype, sth/spine/recursion, sth/replacement/intro, sth/replacement/strength, sth/replacement/extrinsic, sth/replacement/limofsize, sth/replacement/absinf, sth/replacement/ref, sth/replacement/refproofs, sth/replacement/finiteaxiomatizability, sth/cardinals/cardsasords, sth/card-arithmetic/fix, sth/choice/hartogs
- **Coverage**: FULL
- **Redundancy**: None

### AX-SET008 — Foundation
- **Defined in**: sth/z/infinity-again (primary)
- **Referenced in**: sth/z/milestone, sth/z/nat, sth/ordinals/intro, sth/ordinals/zfm, sth/spine/zf
- **Coverage**: FULL
- **Redundancy**: None

### AX-SET009 — Choice
- **Defined in**: sth/cardinals/cardsasords (primary)
- **Also introduced in**: sth/choice/woproblem
- **Referenced in**: sth/cardinals/zfc, sth/cardinals/classing, sth/choice/intro, sth/choice/woproblem, sth/choice/countablechoice, sth/choice/justifications, sth/choice/banach, sth/choice/vitali
- **Coverage**: FULL
- **Redundancy**: COMPRESSION-TARGET (2 sections)

## Syntax (SYN)

### AX-SYN001 — Formation Rules for Terms
- **Defined in**: fol/syn/frm (primary)
- **Referenced in**: fol/syn/fseq
- **Coverage**: FULL
- **Redundancy**: None

### AX-SYN002 — Formation Rules for Formulas
- **Defined in**: fol/syn/frm (primary)
- **Referenced in**: fol/syn/fseq, fol/syn/unq
- **Coverage**: FULL
- **Redundancy**: None

### AX-SYN003 — Formation Rules for PL Formulas
- **Defined in**: pl/syn/fml (primary)
- **Referenced in**: pl/syn/pre, pl/syn/fseq
- **Coverage**: FULL
- **Redundancy**: None

## Composition Patterns

### CP-001 — Soundness
- **Defined in**: fol/axd/sou (primary)
- **Also introduced in**: fol/ntd/sou, fol/seq/sou, fol/tab/sou
- **Referenced in**: fol/int/fol, fol/int/scp, fol/com/cth, fol/com/com, mod/int/prf
- **Coverage**: FULL
- **Redundancy**: COMPRESSION-TARGET (4 sections)

### CP-002 — Completeness
- **Defined in**: fol/com/hen (primary)
- **Also introduced in**: fol/com/mod, fol/com/mod, fol/com/ide, fol/com/cth
- **Referenced in**: fol/int/fol, fol/int/scp, fol/com/int, fol/com/out, fol/com/com, fol/com/dls, fol/byd/msl, fol/byd/sol, mod/lin/int, mod/lin/lsp, mod/lin/prf
- **Coverage**: FULL
- **Redundancy**: COMPRESSION-TARGET (5 sections)

### CP-003 — Compactness
- **Defined in**: fol/com/com (primary)
- **Also introduced in**: fol/com/cpd
- **Referenced in**: fol/int/mod, fol/int/scp, fol/com/int, fol/com/cpd, fol/mat/siz, fol/byd/sol, mod/bas/ove, mod/bas/nsa, mod/mar/int, mod/mar/nst, mod/int/sep, mod/int/prf, mod/int/def, mod/lin/int, mod/lin/lsp, ... (16 total)
- **Coverage**: FULL
- **Redundancy**: COMPRESSION-TARGET (2 sections)

### CP-004 — Lowenheim-Skolem
- **Defined in**: fol/com/dls (primary)
- **Referenced in**: fol/com/int, fol/mat/siz, fol/byd/sol
- **Coverage**: FULL
- **Redundancy**: None

### CP-005 — First Incompleteness Theorem
- **Defined in**: inc/tcp/inc (primary)
- **Also introduced in**: inc/inp/1in
- **Referenced in**: inc/int/ovr, inc/inp/int, inc/inp/ros
- **Coverage**: FULL
- **Redundancy**: COMPRESSION-TARGET (2 sections)

### CP-006 — Second Incompleteness Theorem
- **Defined in**: inc/inp/2in (primary)
- **Referenced in**: inc/int/ovr, inc/inp/int, inc/inp/lob
- **Coverage**: FULL
- **Redundancy**: None

### CP-007 — Tarski's Undefinability
- **Defined in**: inc/inp/tar (primary)
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: None

### CP-008 — Church's Undecidability
- **Defined in**: inc/req/und (primary)
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: None

### CP-009 — Deduction Theorem (CP)
- **Defined in**: fol/axd/ded (primary)
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: None

### CP-010 — Cut Elimination (CP)
- **Defined in**: fol/seq/srl (primary)
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: None

### CP-011 — Craig's Interpolation
- **Defined in**: mod/int/prf (primary)
- **Referenced in**: mod/int/int, mod/int/def
- **Coverage**: FULL
- **Redundancy**: None

### CP-012 — Beth's Definability
- **Defined in**: mod/int/def (primary)
- **Referenced in**: mod/int/int
- **Coverage**: FULL
- **Redundancy**: None

### CP-013 — Lindstrom's Theorem
- **Defined in**: mod/lin/alg (primary)
- **Also introduced in**: mod/lin/prf
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: COMPRESSION-TARGET (2 sections)

## Set-Bootstrap (BST)

### DEF-BST001 — Injection
- **Defined in**: sfr/fun/kin (primary)
- **Referenced in**: sfr/fun/inv, sfr/fun/cmp, sfr/siz/enm, sfr/siz/pai, sfr/siz/pai-alt, sfr/siz/red, sfr/siz/car, sfr/siz/sb, sfr/siz/enm-alt, sfr/siz/red-alt, sfr/infinite/hilbert, sfr/infinite/dedekind, sfr/infinite/card-sb
- **Coverage**: FULL
- **Redundancy**: None

### DEF-BST002 — Surjection
- **Defined in**: sfr/fun/kin (primary)
- **Referenced in**: sfr/fun/inv, sfr/fun/cmp, sfr/siz/enm, sfr/siz/nen, sfr/siz/red, sfr/siz/equ, sfr/siz/car, sfr/siz/enm-alt, sfr/siz/red-alt, sfr/infinite/card-sb
- **Coverage**: FULL
- **Redundancy**: None

### DEF-BST003 — Bijection
- **Defined in**: sfr/fun/kin (primary)
- **Referenced in**: sfr/fun/inv, sfr/fun/iso, sfr/siz/enm, sfr/siz/equ, sfr/siz/car, sfr/siz/sb, sfr/siz/enm-alt, sfr/siz/nen-alt, sfr/infinite/card-sb
- **Coverage**: FULL
- **Redundancy**: None

### DEF-BST004 — Equivalence Relation
- **Defined in**: sfr/rel/eqv (primary)
- **Referenced in**: sfr/siz/equ, sfr/arith/int, sfr/arith/rat, sfr/arith/check, sfr/arith/cauchy
- **Coverage**: FULL
- **Redundancy**: None

### DEF-BST005 — Partial Order
- **Defined in**: sfr/rel/ord (primary)
- **Referenced in**: sfr/rel/tre
- **Coverage**: FULL
- **Redundancy**: None

## Computation (CMP)

### DEF-CMP001 — Partial Function
- **Defined in**: cmp/tur/con (primary)
- **Referenced in**: cmp/rec/int, cmp/rec/par, cmp/thy/int, tur/mac/una
- **Coverage**: FULL
- **Redundancy**: None

### DEF-CMP002 — Total Function
- **Defined in**: cmp/rec/par (primary)
- **Referenced in**: cmp/rec/gen, cmp/thy/tot
- **Coverage**: FULL
- **Redundancy**: None

### DEF-CMP003 — Characteristic Function
- **Defined in**: cmp/rec/prr (primary)
- **Referenced in**: cmp/rec/int, cmp/rec/prr, cmp/thy/cps
- **Coverage**: FULL
- **Redundancy**: None

### DEF-CMP004 — Enumeration
- **Defined in**: cmp/thy/int (primary)
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: None

### DEF-CMP005 — Index (Program)
- **Defined in**: cmp/rec/nft (primary)
- **Also introduced in**: tur/und/enu
- **Referenced in**: cmp/rec/hlt, cmp/thy/cod, cmp/thy/nfm, cmp/thy/smn, tur/und/hal, tur/und/uni
- **Coverage**: FULL
- **Redundancy**: COMPRESSION-TARGET (2 sections)

### DEF-CMP006 — Lambda-Definable Function
- **Defined in**: (none)
- **Referenced in**: (none)
- **Coverage**: ABSENT
- **Redundancy**: None

### DEF-CMP007 — Productive Set
- **Defined in**: (none)
- **Referenced in**: (none)
- **Coverage**: ABSENT
- **Redundancy**: None

### DEF-CMP008 — Creative Set
- **Defined in**: cmp/thy/cce (primary)
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: None

### DEF-CMP009 — Representability
- **Defined in**: tur/und/rep (primary)
- **Also introduced in**: inc/int/def, inc/req/int
- **Referenced in**: tur/und/dec, tur/und/ver, tur/und/uns, tur/und/tra, inc/int/ovr, inc/int/dec, inc/req/int, inc/req/rpc, inc/req/bre, inc/req/cmp, inc/req/min, inc/req/crq, inc/req/cre, inc/req/rel, inc/tcp/int, ... (18 total)
- **Coverage**: FULL
- **Redundancy**: COMPRESSION-TARGET (3 sections)

### DEF-CMP010 — Recursive Enumerability
- **Defined in**: cmp/thy/eqc (primary)
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: None

## Deduction (DED)

### DEF-DED001 — Syntactic Consistency
- **Defined in**: fol/axd/ptn (primary)
- **Also introduced in**: fol/ntd/ptn, fol/seq/ptn, fol/tab/ptn
- **Referenced in**: fol/int/scp, fol/axd/prv, fol/axd/sou, fol/ntd/ppr, fol/ntd/sou, fol/ntd/prv, fol/seq/prv, fol/tab/prv, fol/prf/int, fol/com/ccs, fol/com/mcs, fol/com/hen, fol/com/lin, fol/com/mod, fol/com/ide, ... (30 total)
- **Coverage**: FULL
- **Redundancy**: EXPECTED: Proof system variants (4 sections)

### DEF-DED002 — Maximal Consistent Set
- **Defined in**: fol/com/mcs (primary)
- **Referenced in**: fol/com/out
- **Coverage**: FULL
- **Redundancy**: None

### DEF-DED003 — Deductive Closure
- **Defined in**: fol/seq/ptn (primary)
- **Also introduced in**: fol/mat/int
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: EXPECTED: Proof system variants (2 sections)

### DEF-DED004 — Conservative Extension
- **Defined in**: (none)
- **Referenced in**: (none)
- **Coverage**: ABSENT
- **Redundancy**: None

### DEF-DED005 — Hilbert-Style System
- **Defined in**: fol/axd/prp (primary)
- **Also introduced in**: fol/prf/axd
- **Referenced in**: fol/axd/sou, fol/com/ccs, fol/com/hen, fol/com/lin, fol/com/com
- **Coverage**: FULL
- **Redundancy**: EXPECTED: Proof system variants (2 sections)

### DEF-DED006 — Natural Deduction
- **Defined in**: fol/ntd/rul (primary)
- **Also introduced in**: fol/ntd/prl, fol/ntd/qrl, fol/prf/ntd
- **Referenced in**: fol/ntd/der, fol/ntd/sou, fol/ntd/ide, fol/ntd/pro
- **Coverage**: FULL
- **Redundancy**: EXPECTED: Proof system variants (4 sections)

### DEF-DED007 — Sequent Calculus
- **Defined in**: fol/seq/rul (primary)
- **Referenced in**: fol/seq/sou, fol/prf/seq
- **Coverage**: FULL
- **Redundancy**: None

### DEF-DED008 — Tableau System
- **Defined in**: fol/tab/rul (primary)
- **Referenced in**: fol/tab/sou, fol/prf/tab
- **Coverage**: FULL
- **Redundancy**: None

### DEF-DED009 — Derived Rule
- **Defined in**: (none)
- **Referenced in**: (none)
- **Coverage**: ABSENT
- **Redundancy**: None

### DEF-DED010 — Admissible Rule
- **Defined in**: (none)
- **Referenced in**: (none)
- **Coverage**: ABSENT
- **Redundancy**: None

## Semantics (SEM)

### DEF-SEM001 — Tarski Satisfaction Definition
- **Defined in**: pl/syn/val (primary)
- **Also introduced in**: fol/syn/sat
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: EXPECTED: PL/FOL split (2 sections)

### DEF-SEM002 — Satisfiable
- **Defined in**: pl/syn/sem (primary)
- **Also introduced in**: fol/syn/sem
- **Referenced in**: pl/prp/com, fol/com/com
- **Coverage**: FULL
- **Redundancy**: EXPECTED: PL/FOL split (2 sections)

### DEF-SEM003 — Finitely Satisfiable
- **Defined in**: fol/com/com (primary)
- **Referenced in**: fol/com/out, fol/com/cth, fol/com/cpd
- **Coverage**: FULL
- **Redundancy**: None

### DEF-SEM004 — Semantic Consistency
- **Defined in**: fol/syn/sem (primary)
- **Referenced in**: fol/com/int
- **Coverage**: FULL
- **Redundancy**: None

### DEF-SEM005 — Semantic Completeness
- **Defined in**: fol/com/ccs (primary)
- **Referenced in**: fol/com/mcs, fol/com/hen, fol/com/lin, fol/com/mod, fol/com/ide, fol/com/cpd, mod/bas/thm
- **Coverage**: FULL
- **Redundancy**: None

### DEF-SEM006 — Theory of a Structure
- **Defined in**: mod/bas/dlo (primary)
- **Referenced in**: fol/byd/sol, mod/bas/nsa, mod/mar/mpa
- **Coverage**: FULL
- **Redundancy**: None

### DEF-SEM007 — Definable Set
- **Defined in**: fol/mat/int (primary)
- **Referenced in**: fol/mat/the, fol/mat/set
- **Coverage**: FULL
- **Redundancy**: None

### DEF-SEM008 — Elementary Equivalence
- **Defined in**: mod/mar/cmp (primary)
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: None

### DEF-SEM009 — Tautology (PL)
- **Defined in**: pl/syn/sem (primary)
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: None

### DEF-SEM010 — PL Consequence
- **Defined in**: pl/syn/sem (primary)
- **Referenced in**: pl/prp/snd
- **Coverage**: FULL
- **Redundancy**: None

### DEF-SEM011 — Elementary Substructure
- **Defined in**: mod/bas/sub (primary)
- **Referenced in**: mod/lin/alg
- **Coverage**: FULL
- **Redundancy**: None

### DEF-SEM012 — Diagram
- **Defined in**: (none)
- **Referenced in**: (none)
- **Coverage**: ABSENT
- **Redundancy**: None

### DEF-SEM013 — Type (Complete Type)
- **Defined in**: mod/bas/iso (primary)
- **Referenced in**: mod/bas/thm, mod/bas/pis, mod/bas/dlo, mod/bas/nsa, mod/mar/int, mod/mar/stm, mod/mar/nst, mod/mar/mpa, mod/mar/cmp, mod/int/prf, mod/lin/lsp, mod/lin/prf
- **Coverage**: FULL
- **Redundancy**: None

### DEF-SEM014 — Categoricity
- **Defined in**: (none)
- **Referenced in**: (none)
- **Coverage**: ABSENT
- **Redundancy**: None

### DEF-SEM015 — Ultraproduct
- **Defined in**: (none)
- **Referenced in**: (none)
- **Coverage**: ABSENT
- **Redundancy**: None

### DEF-SEM016 — Embedding
- **Defined in**: (none)
- **Referenced in**: (none)
- **Coverage**: ABSENT
- **Redundancy**: None

## Set-Formal (SET)

### DEF-SET001 — Ordinal Number
- **Defined in**: sth/ordinals/vn (primary)
- **Referenced in**: sth/ordinals/basic, sth/ordinals/replacement, sth/ordinals/ordtype, sth/ordinals/opps, sth/spine/valpha, sth/spine/Valphabasic, sth/spine/foundation, sth/spine/rank, sth/replacement/strength, sth/ord-arithmetic/intro, sth/ord-arithmetic/add, sth/ord-arithmetic/using-addition, sth/ord-arithmetic/mult, sth/ord-arithmetic/expo, sth/cardinals/cp, ... (17 total)
- **Coverage**: FULL
- **Redundancy**: None

### DEF-SET002 — Successor Ordinal
- **Defined in**: sth/ordinals/vn (primary)
- **Referenced in**: sth/ordinals/basic
- **Coverage**: FULL
- **Redundancy**: None

### DEF-SET003 — Limit Ordinal
- **Defined in**: sth/ordinals/vn (primary)
- **Referenced in**: sth/ordinals/basic
- **Coverage**: FULL
- **Redundancy**: None

### DEF-SET004 — omega
- **Defined in**: sth/ordinals/opps (primary)
- **Referenced in**: sth/spine/valpha, sth/spine/Valphabasic, sth/ord-arithmetic/add, sth/ord-arithmetic/using-addition, sth/ord-arithmetic/mult
- **Coverage**: FULL
- **Redundancy**: None

### DEF-SET005 — Transfinite Induction
- **Defined in**: sth/ordinals/opps (primary)
- **Referenced in**: sth/spine/valpha, sth/spine/Valphabasic, sth/ord-arithmetic/add, sth/ord-arithmetic/using-addition, sth/ord-arithmetic/mult
- **Coverage**: FULL
- **Redundancy**: None

### DEF-SET006 — Transfinite Recursion
- **Defined in**: sth/ordinals/basic (primary)
- **Referenced in**: sth/ordinals/opps, sth/spine/recursion, sth/spine/rank
- **Coverage**: FULL
- **Redundancy**: None

### DEF-SET007 — Cardinal Number
- **Defined in**: sth/spine/recursion (primary)
- **Referenced in**: sth/ord-arithmetic/expo, sth/choice/woproblem
- **Coverage**: FULL
- **Redundancy**: None

### DEF-SET008 — Cardinality (formal)
- **Defined in**: sth/cardinals/cp (primary)
- **Also introduced in**: sth/cardinals/cardsasords
- **Referenced in**: sth/cardinals/classing, sth/cardinals/hp, sth/card-arithmetic/opps, sth/card-arithmetic/simp, sth/card-arithmetic/expotough, sth/card-arithmetic/ch, sth/choice/tarskiscott
- **Coverage**: FULL
- **Redundancy**: COMPRESSION-TARGET (2 sections)

### DEF-SET009 — Well-Ordering
- **Defined in**: sth/card-arithmetic/ch (primary)
- **Referenced in**: sth/card-arithmetic/fix
- **Coverage**: FULL
- **Redundancy**: None

### DEF-SET010 — Zorn's Lemma
- **Defined in**: sth/card-arithmetic/ch (primary)
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: None

### DEF-SET011 — Cantor's Theorem (formal)
- **Defined in**: (none)
- **Referenced in**: (none)
- **Coverage**: ABSENT
- **Redundancy**: None

### DEF-SET012 — Von Neumann Hierarchy [Deferred]
- **Defined in**: (none)
- **Referenced in**: (none)
- **Coverage**: DEFERRED
- **Redundancy**: None

### DEF-SET013 — Aleph Numbers [Deferred]
- **Defined in**: (none)
- **Referenced in**: (none)
- **Coverage**: DEFERRED
- **Redundancy**: None

### DEF-SET014 — Cofinality [Deferred]
- **Defined in**: (none)
- **Referenced in**: (none)
- **Coverage**: DEFERRED
- **Redundancy**: None

### DEF-SET015 — Continuum Hypothesis [Deferred]
- **Defined in**: (none)
- **Referenced in**: (none)
- **Coverage**: DEFERRED
- **Redundancy**: None

## Syntax (SYN)

### DEF-SYN001 — Substitution
- **Defined in**: fol/syn/sub (primary)
- **Referenced in**: pl/syn/pre, fol/syn/ext
- **Coverage**: FULL
- **Redundancy**: None

### DEF-SYN002 — Simultaneous Substitution
- **Defined in**: (none)
- **Referenced in**: (none)
- **Coverage**: ABSENT
- **Redundancy**: None

### DEF-SYN003 — Free Variables (FV)
- **Defined in**: fol/syn/fvs (primary)
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: None

### DEF-SYN004 — Alphabetic Variant
- **Defined in**: (none)
- **Referenced in**: (none)
- **Coverage**: ABSENT
- **Redundancy**: None

### DEF-SYN005 — Structural Induction on Formulas
- **Defined in**: fol/syn/frm (primary)
- **Referenced in**: pl/syn/pre, pl/syn/fseq, fol/syn/fseq
- **Coverage**: FULL
- **Redundancy**: None

### DEF-SYN006 — Structural Recursion
- **Defined in**: pl/syn/fseq (primary)
- **Also introduced in**: fol/syn/fseq
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: EXPECTED: PL/FOL split (2 sections)

### DEF-SYN007 — Formula Complexity
- **Defined in**: (none)
- **Referenced in**: (none)
- **Coverage**: ABSENT
- **Redundancy**: None

### DEF-SYN008 — Subterm
- **Defined in**: fol/syn/sbf (primary)
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: None

## Set-Bootstrap (BST)

### PRIM-BST001 — Set
- **Defined in**: sfr/set/bas (primary)
- **Referenced in**: sfr/set/sub, sfr/set/imp, sfr/set/uni, sfr/set/pai, sfr/set/rus, sfr/set/prf, sfr/fun/bas, sfr/fun/rel, sfr/rel/grp, sfr/ind/int, sfr/infinite/hilbert, sfr/infinite/dedekind, sfr/infinite/card-sb, sfr/arith/cuts
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-BST002 — Membership
- **Defined in**: sfr/set/bas (primary)
- **Referenced in**: sfr/set/sub, sfr/set/uni, sfr/set/rus, sfr/fun/bas, sfr/rel/ref, sfr/siz/enm, sfr/siz/nen, sfr/siz/car, sfr/siz/enm-alt
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-BST003 — Subset
- **Defined in**: sfr/set/sub (primary)
- **Referenced in**: sfr/set/imp, sfr/set/uni, sfr/set/prf, sfr/fun/rel, sfr/rel/ord, sfr/infinite/dedekind, sfr/infinite/card-sb, sfr/arith/cuts
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-BST004 — Empty Set
- **Defined in**: sfr/set/bas (primary)
- **Referenced in**: sfr/set/sub, sfr/set/uni, sfr/set/pai, sfr/rel/set, sfr/siz/enm, sfr/arith/cuts
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-BST005 — Union/Intersection
- **Defined in**: sfr/set/uni (primary)
- **Referenced in**: sfr/set/prf, sfr/siz/enm, sfr/infinite/dedekind
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-BST006 — Ordered Pair
- **Defined in**: sfr/set/pai (primary)
- **Referenced in**: sfr/fun/bas, sfr/fun/rel, sfr/rel/set, sfr/rel/ref, sfr/siz/zigzag, sfr/siz/pai, sfr/siz/pai-alt, sfr/arith/int, sfr/arith/rat
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-BST007 — Cartesian Product
- **Defined in**: sfr/set/pai (primary)
- **Referenced in**: sfr/fun/bas, sfr/rel/set, sfr/siz/zigzag, sfr/siz/pai, sfr/siz/pai-alt
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-BST008 — Relation
- **Defined in**: sfr/rel/set (primary)
- **Referenced in**: sfr/fun/rel, sfr/fun/iso, sfr/fun/par, sfr/rel/ref, sfr/rel/prp, sfr/rel/eqv, sfr/rel/ord, sfr/rel/grp, sfr/rel/ops
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-BST009 — Function
- **Defined in**: sfr/fun/bas (primary)
- **Referenced in**: sfr/fun/kin, sfr/fun/rel, sfr/fun/inv, sfr/fun/cmp, sfr/fun/iso, sfr/fun/par, sfr/ind/int, sfr/siz/enm, sfr/siz/enm-alt, sfr/infinite/dedekind, sfr/infinite/card-sb, sfr/arith/cauchy, cmp/rec/pre, cmp/rec/com, cmp/rec/prf, ... (17 total)
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-BST010 — Sequence (Finite)
- **Defined in**: sfr/set/imp (primary)
- **Also introduced in**: sfr/set/pai
- **Referenced in**: sfr/rel/tre, tur/mac/tur, cmp/tur/con, tur/und/enu
- **Coverage**: FULL
- **Redundancy**: COMPRESSION-TARGET (2 sections)

### PRIM-BST011 — Sequence (Infinite)
- **Defined in**: sfr/set/imp (primary)
- **Referenced in**: sfr/siz/nen, sfr/siz/red, sfr/siz/nen-alt, sfr/siz/red-alt, sfr/arith/cauchy
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-BST012 — Natural Number
- **Defined in**: sfr/set/imp (primary)
- **Referenced in**: sfr/rel/set, sfr/rel/tre, sfr/rel/ops, sfr/ind/int, sfr/siz/enm, sfr/siz/zigzag, sfr/siz/pai, sfr/siz/pai-alt, sfr/siz/enm-alt, sfr/siz/nen-alt, sfr/siz/red-alt, sfr/arith/int, sfr/arith/cauchy, cmp/rec/pre, cmp/rec/prf, ... (21 total)
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-BST013 — Mathematical Induction
- **Defined in**: sfr/ind/int (primary)
- **Also introduced in**: sfr/infinite/induction
- **Referenced in**: sfr/infinite/induction
- **Coverage**: FULL
- **Redundancy**: COMPRESSION-TARGET (2 sections)

### PRIM-BST014 — Inductive Definition
- **Defined in**: sfr/ind/int (primary)
- **Referenced in**: cmp/rec/prf
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-BST015 — Power Set (naive)
- **Defined in**: sfr/set/sub (primary)
- **Referenced in**: sfr/set/rus, sfr/siz/nen, sfr/siz/red, sfr/siz/car, sfr/siz/nen-alt, sfr/siz/red-alt
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-BST016 — Cardinality
- **Defined in**: sfr/siz/enm (primary)
- **Also introduced in**: sfr/siz/enm-alt
- **Referenced in**: sfr/siz/zigzag, sfr/siz/pai, sfr/siz/nen, sfr/siz/red, sfr/siz/equ, sfr/siz/car, sfr/siz/sb, sfr/siz/nen-alt, sfr/siz/red-alt, sfr/arith/real, tur/und/enu, tur/und/int
- **Coverage**: FULL
- **Redundancy**: COMPRESSION-TARGET (2 sections)

## Computation (CMP)

### PRIM-CMP001 — Computable Function
- **Defined in**: cmp/rec/par (primary)
- **Also introduced in**: tur/mac/int, tur/mac/una
- **Referenced in**: cmp/rec/int, cmp/rec/cmp, cmp/rec/npr, cmp/rec/nft, cmp/rec/hlt, cmp/rec/gen, cmp/thy/int, cmp/thy/cps, cmp/thy/ces, cmp/thy/eqc, cmp/thy/red, tur/mac/ctt, tur/mac/dis, tur/mac/cmb, tur/und/int, ... (28 total)
- **Coverage**: FULL
- **Redundancy**: COMPRESSION-TARGET (3 sections)

### PRIM-CMP002 — Primitive Recursive Function
- **Defined in**: cmp/rec/pre (primary)
- **Also introduced in**: cmp/rec/prf
- **Referenced in**: cmp/rec/com, cmp/rec/not, cmp/rec/cmp, cmp/rec/exa, cmp/rec/prr, cmp/rec/bmi, cmp/rec/pri, cmp/rec/seq, cmp/rec/tre, cmp/rec/ore, cmp/rec/npr, cmp/rec/par, cmp/rec/nft, cmp/thy/nfm, cmp/thy/smn, ... (16 total)
- **Coverage**: FULL
- **Redundancy**: COMPRESSION-TARGET (2 sections)

### PRIM-CMP003 — mu-Recursion
- **Defined in**: cmp/rec/par (primary)
- **Referenced in**: cmp/rec/nft, cmp/rec/gen
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-CMP004 — Turing Machine
- **Defined in**: tur/mac/int (primary)
- **Also introduced in**: tur/mac/tur
- **Referenced in**: tur/mac/hal, cmp/tur/con, tur/mac/una, tur/mac/var, tur/mac/ctt, tur/mac/rep, tur/mac/dis, tur/mac/cmb, tur/und/enu, tur/und/int, tur/und/hal, tur/und/rep, tur/und/ver, tur/und/uni, tur/und/uns
- **Coverage**: FULL
- **Redundancy**: COMPRESSION-TARGET (2 sections)

### PRIM-CMP005 — Church-Turing Thesis
- **Defined in**: tur/mac/ctt (primary)
- **Referenced in**: cmp/thy/int
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-CMP006 — Decidable Set
- **Defined in**: cmp/thy/cps (primary)
- **Also introduced in**: tur/und/int, tur/und/dec
- **Referenced in**: cmp/thy/ces, cmp/thy/ncp, cmp/thy/cmp, cmp/thy/ppr, tur/und/uns, tur/und/tra, inc/int/def, inc/int/dec, inc/req/und, inc/tcp/qce, inc/tcp/oqn, inc/tcp/cqn, inc/tcp/cdc, inc/tcp/ins, inc/tcp/con, ... (16 total)
- **Coverage**: FULL
- **Redundancy**: COMPRESSION-TARGET (3 sections)

### PRIM-CMP007 — Semi-Decidable Set
- **Defined in**: cmp/thy/ces (primary)
- **Referenced in**: cmp/thy/eqc, cmp/thy/ncp, cmp/thy/clo, cmp/thy/cmp, cmp/thy/ppr, cmp/thy/cce, tur/und/uns, inc/int/def, inc/tcp/qce, inc/tcp/cax
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-CMP008 — Halting Problem
- **Defined in**: cmp/rec/hlt (primary)
- **Also introduced in**: cmp/thy/hlt, tur/und/int, tur/und/hal
- **Referenced in**: cmp/thy/ncp, tur/und/dec, tur/und/uns, tur/und/tra
- **Coverage**: FULL
- **Redundancy**: COMPRESSION-TARGET (4 sections)

### PRIM-CMP009 — Many-One Reducibility
- **Defined in**: cmp/thy/red (primary)
- **Referenced in**: cmp/thy/ppr, cmp/thy/cce, cmp/thy/k1, cmp/thy/tot, cmp/thy/rce
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-CMP010 — Diagonalization
- **Defined in**: cmp/rec/npr (primary)
- **Referenced in**: cmp/rec/hlt, cmp/thy/nou, cmp/thy/hlt, cmp/thy/rus, tur/und/hal, inc/int/dec, inc/req/bet, inc/tcp/cqn, inc/tcp/ins, inc/inp/int, inc/inp/fix
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-CMP011 — Godel Numbering
- **Defined in**: cmp/rec/seq (primary)
- **Also introduced in**: cmp/rec/nft, tur/und/enu
- **Referenced in**: cmp/rec/tre, cmp/rec/npr, cmp/thy/cod, cmp/thy/nfm, tur/und/uni, inc/int/ovr, inc/art/int, inc/art/cod, inc/art/trm, inc/art/frm, inc/art/sub, inc/art/plk, inc/art/pnd, inc/art/pax, inc/req/rpc, ... (19 total)
- **Coverage**: FULL
- **Redundancy**: COMPRESSION-TARGET (3 sections)

### PRIM-CMP012 — Universal Turing Machine
- **Defined in**: cmp/thy/int (primary)
- **Also introduced in**: cmp/thy/uni, tur/und/uni
- **Referenced in**: cmp/thy/nou, cmp/thy/hlt, cmp/thy/fix
- **Coverage**: FULL
- **Redundancy**: COMPRESSION-TARGET (3 sections)

## Deduction (DED)

### PRIM-DED001 — Axiom Schema
- **Defined in**: fol/axd/prp (primary)
- **Referenced in**: fol/axd/rul, fol/axd/ide, fol/axd/qua, fol/prf/axd, fol/com/int, fol/com/out, fol/com/ccs, fol/com/mcs, fol/com/hen, fol/com/cth
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-DED002 — Non-Logical Axiom
- **Defined in**: fol/mat/the (primary)
- **Referenced in**: fol/mat/set, inc/int/def
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-DED003 — Rule of Inference
- **Defined in**: fol/ntd/prl (primary)
- **Also introduced in**: fol/ntd/qrl, fol/seq/prl, fol/seq/qrl, fol/seq/ide, fol/tab/ide, fol/tab/prl, fol/tab/qrl
- **Referenced in**: fol/axd/rul, fol/axd/prp, fol/axd/qua, fol/axd/ddq, fol/axd/prq, fol/ntd/rul, fol/ntd/ide, fol/seq/der, fol/seq/prq, fol/seq/sid, fol/tab/sid, fol/tab/der, fol/tab/prq, fol/prf/axd, fol/prf/ntd
- **Coverage**: FULL
- **Redundancy**: EXPECTED: Proof system variants (8 sections)

### PRIM-DED004 — Proof System
- **Defined in**: fol/seq/rul (primary)
- **Also introduced in**: fol/tab/rul
- **Referenced in**: fol/seq/prl, fol/seq/srl, fol/seq/qrl, fol/seq/der, fol/seq/ide, fol/tab/ide, fol/tab/prl, fol/tab/qrl, fol/tab/der, fol/prf/int
- **Coverage**: FULL
- **Redundancy**: EXPECTED: Proof system variants (2 sections)

### PRIM-DED005 — Derivation
- **Defined in**: fol/axd/rul (primary)
- **Also introduced in**: fol/ntd/der, fol/seq/der, fol/tab/rul, fol/tab/der
- **Referenced in**: fol/axd/pro, fol/axd/prq, fol/ntd/pro, fol/ntd/prq, fol/seq/pro, fol/seq/prq, fol/seq/ptn, fol/seq/sou, fol/seq/sid, fol/tab/ptn, fol/tab/sou, fol/tab/ide, fol/tab/sid, fol/tab/prl, fol/tab/qrl, ... (18 total)
- **Coverage**: FULL
- **Redundancy**: EXPECTED: Proof system variants (5 sections)

### PRIM-DED006 — Provability
- **Defined in**: fol/axd/rul (primary)
- **Also introduced in**: fol/axd/ptn, fol/ntd/der, fol/ntd/ptn, fol/seq/ptn, fol/tab/ptn
- **Referenced in**: fol/int/fol, fol/int/sub, fol/int/scp, fol/axd/prv, fol/axd/ppr, fol/axd/qpr, fol/axd/ded, fol/axd/ide, fol/axd/sou, fol/ntd/ppr, fol/ntd/qpr, fol/ntd/sou, fol/ntd/prv, fol/ntd/sid, fol/seq/prv, ... (30 total)
- **Coverage**: FULL
- **Redundancy**: EXPECTED: Proof system variants (6 sections)

### PRIM-DED007 — Structural Rule
- **Defined in**: fol/ntd/qrl (primary)
- **Also introduced in**: fol/seq/srl
- **Referenced in**: fol/seq/der, fol/prf/seq
- **Coverage**: FULL
- **Redundancy**: EXPECTED: Proof system variants (2 sections)

### PRIM-DED008 — Sequent
- **Defined in**: fol/seq/rul (primary)
- **Referenced in**: fol/seq/prl, fol/seq/srl, fol/seq/qrl, fol/seq/der, fol/seq/pro, fol/seq/ide, fol/prf/seq
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-DED009 — Assumption Discharge
- **Defined in**: fol/ntd/rul (primary)
- **Also introduced in**: fol/ntd/prl
- **Referenced in**: fol/ntd/der, fol/ntd/pro, fol/ntd/prq, fol/ntd/prv, fol/prf/ntd
- **Coverage**: FULL
- **Redundancy**: EXPECTED: Proof system variants (2 sections)

### PRIM-DED010 — Theorem
- **Defined in**: fol/axd/rul (primary)
- **Also introduced in**: fol/axd/ptn, fol/ntd/ptn, fol/seq/ptn, fol/tab/ptn
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: EXPECTED: Proof system variants (5 sections)

## Semantics (SEM)

### PRIM-SEM001 — Structure
- **Defined in**: fol/syn/str (primary)
- **Referenced in**: fol/syn/int, fol/syn/its, fol/syn/cov, fol/syn/sat, fol/syn/ext, fol/syn/sem, fol/int/fol, fol/int/sat, fol/int/sem, fol/int/mod, fol/com/mod, fol/com/ide, fol/com/dls, fol/mat/int, fol/mat/exs, ... (25 total)
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-SEM002 — Domain
- **Defined in**: fol/syn/str (primary)
- **Referenced in**: fol/syn/int, fol/syn/its, fol/syn/sat, fol/int/sat, mod/bas/red, mod/bas/sub, mod/bas/iso, mod/bas/pis
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-SEM003 — Interpretation
- **Defined in**: fol/syn/str (primary)
- **Referenced in**: fol/syn/its, fol/syn/cov, fol/syn/sat, fol/int/sat, mod/bas/red, mod/bas/sub
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-SEM004 — Variable Assignment
- **Defined in**: fol/syn/sat (primary)
- **Referenced in**: fol/syn/its, fol/syn/ext, fol/syn/ass, fol/int/sub, fol/int/sat, fol/int/sem
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-SEM005 — x-Variant
- **Defined in**: fol/syn/sat (primary)
- **Referenced in**: fol/int/fol, fol/int/sub, fol/int/sat, fol/int/sem, mod/bas/red, mod/bas/iso, mod/bas/thm, mod/mar/mdq, mod/lin/alg
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-SEM006 — Term Valuation
- **Defined in**: fol/syn/cov (primary)
- **Also introduced in**: fol/syn/sat
- **Referenced in**: fol/syn/ext, fol/syn/ass, fol/com/mod, fol/com/ide, fol/mat/exs, fol/mat/exr, fol/mat/siz
- **Coverage**: FULL
- **Redundancy**: COMPRESSION-TARGET (2 sections)

### PRIM-SEM007 — Satisfaction
- **Defined in**: pl/syn/val (primary)
- **Also introduced in**: fol/syn/sat
- **Referenced in**: pl/syn/int, pl/syn/sem, fol/syn/int, fol/syn/its, fol/syn/ext, fol/syn/sem, fol/syn/ass, fol/int/sem, fol/axd/sou, fol/ntd/sou, fol/ntd/sid
- **Coverage**: FULL
- **Redundancy**: EXPECTED: PL/FOL split (2 sections)

### PRIM-SEM008 — Truth in a Structure
- **Defined in**: fol/syn/ass (primary)
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-SEM009 — Logical Validity
- **Defined in**: fol/syn/sem (primary)
- **Referenced in**: fol/syn/int, fol/syn/its, fol/int/fol, fol/int/sub, fol/int/sem, fol/int/mod, fol/int/scp, fol/axd/ptn, fol/axd/sou, fol/ntd/ptn, fol/ntd/sou
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-SEM010 — Logical Consequence
- **Defined in**: fol/syn/sem (primary)
- **Referenced in**: fol/syn/int, fol/syn/its, fol/axd/ptn, fol/axd/sou, fol/ntd/ptn, fol/ntd/sou, fol/com/int, fol/com/out, fol/com/cth, fol/com/com, fol/mat/int
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-SEM011 — Model
- **Defined in**: fol/syn/sem (primary)
- **Also introduced in**: fol/mat/exs
- **Referenced in**: fol/int/mod, fol/mat/int, fol/mat/the, fol/mat/set
- **Coverage**: FULL
- **Redundancy**: COMPRESSION-TARGET (2 sections)

### PRIM-SEM012 — Isomorphism
- **Defined in**: mod/bas/thm (primary)
- **Referenced in**: fol/int/mod, inc/int/def, mod/bas/dlo, mod/bas/nsa, mod/mar/int, mod/mar/stm, mod/mar/nst, mod/mar/mdq, mod/mar/mpa
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-SEM013 — Substructure
- **Defined in**: mod/bas/iso (primary)
- **Referenced in**: fol/syn/sem, mod/bas/thm, mod/bas/pis, mod/bas/dlo, mod/bas/nsa, mod/lin/alg, mod/lin/lsp, mod/lin/prf
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-SEM014 — Homomorphism
- **Defined in**: (none)
- **Referenced in**: (none)
- **Coverage**: ABSENT
- **Redundancy**: None

### PRIM-SEM015 — Truth-Value Assignment (PL)
- **Defined in**: pl/syn/val (primary)
- **Referenced in**: pl/syn/int, pl/syn/val
- **Coverage**: FULL
- **Redundancy**: None

## Set-Formal (SET)

### PRIM-SET001 — Set (formal)
- **Defined in**: (none)
- **Referenced in**: (none)
- **Coverage**: ABSENT
- **Redundancy**: None

### PRIM-SET002 — Membership (formal)
- **Defined in**: (none)
- **Referenced in**: sth/story/extensionality, sth/story/rus, sth/z/sep, sth/z/union, sth/z/pairs, sth/z/power, sth/z/infinity-again, sth/ordinals/wo, sth/ordinals/iso, sth/ordinals/vn
- **Coverage**: IMPLICIT
- **Redundancy**: None

### PRIM-SET003 — Class
- **Defined in**: sth/ordinals/basic (primary)
- **Referenced in**: sth/replacement/limofsize
- **Coverage**: FULL
- **Redundancy**: None

## Syntax (SYN)

### PRIM-SYN001 — Symbol
- **Defined in**: fol/syn/fol (primary)
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-SYN002 — Variable
- **Defined in**: pl/syn/fml (primary)
- **Also introduced in**: fol/syn/fol
- **Referenced in**: fol/syn/int, fol/syn/itx, fol/syn/frm, fol/syn/fvs, fol/syn/sat, fol/int/syn, fol/int/fml
- **Coverage**: FULL
- **Redundancy**: EXPECTED: PL/FOL split (2 sections)

### PRIM-SYN003 — Logical Connective
- **Defined in**: pl/syn/fml (primary)
- **Also introduced in**: fol/syn/fol
- **Referenced in**: pl/syn/int, fol/int/syn, fol/int/fml, fol/int/snt, fol/axd/ppr, fol/axd/prp, fol/ntd/rul, fol/ntd/ppr, fol/ntd/prl, fol/com/hen, fol/com/mod, fol/mat/exr, fol/byd/msl
- **Coverage**: FULL
- **Redundancy**: EXPECTED: PL/FOL split (2 sections)

### PRIM-SYN004 — Quantifier
- **Defined in**: fol/syn/fol (primary)
- **Referenced in**: fol/syn/fvs, fol/int/syn, fol/int/fml, fol/int/snt, fol/int/sub, fol/int/sat, fol/axd/qpr, fol/axd/qua, fol/axd/prq, fol/ntd/qpr, fol/ntd/prq, fol/ntd/qrl
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-SYN005 — Constant Symbol
- **Defined in**: fol/syn/fol (primary)
- **Referenced in**: fol/syn/int, fol/syn/itx, fol/syn/frm, fol/syn/str, fol/int/syn, fol/int/fml, fol/int/sub, fol/int/sat
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-SYN006 — Function Symbol
- **Defined in**: fol/syn/fol (primary)
- **Referenced in**: fol/syn/int, fol/syn/itx, fol/syn/frm, fol/syn/str, fol/int/sub
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-SYN007 — Relation Symbol
- **Defined in**: fol/syn/fol (primary)
- **Referenced in**: fol/syn/int, fol/syn/itx, fol/syn/frm, fol/syn/str, fol/int/syn, fol/int/fml, fol/int/sat, fol/com/ide, fol/mat/siz
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-SYN008 — Arity
- **Defined in**: fol/syn/fol (primary)
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-SYN009 — Language
- **Defined in**: fol/syn/fol (primary)
- **Referenced in**: fol/syn/frm, fol/syn/str
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-SYN010 — Term
- **Defined in**: fol/syn/frm (primary)
- **Referenced in**: fol/syn/int, fol/syn/itx, fol/syn/fseq, fol/syn/sub, fol/syn/cov, fol/syn/sat, fol/int/sub
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-SYN011 — Atomic Formula
- **Defined in**: fol/syn/frm (primary)
- **Referenced in**: fol/syn/fseq, fol/syn/sat, fol/int/fol, fol/int/syn, fol/int/fml, fol/int/snt, fol/int/sub, fol/int/sat
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-SYN012 — Formula (wff)
- **Defined in**: pl/syn/fml (primary)
- **Also introduced in**: fol/syn/frm
- **Referenced in**: pl/syn/val, fol/syn/int, fol/syn/itx, fol/syn/fseq, fol/syn/unq, fol/syn/mai, fol/syn/sbf, fol/syn/fvs, fol/syn/sub, fol/syn/sat, fol/int/fml, fol/int/snt, fol/int/sem, fol/axd/rul, tur/und/rep, ... (16 total)
- **Coverage**: FULL
- **Redundancy**: EXPECTED: PL/FOL split (2 sections)

### PRIM-SYN013 — Sentence
- **Defined in**: fol/syn/fvs (primary)
- **Referenced in**: fol/syn/ass, fol/int/fol, fol/int/syn, fol/int/fml, fol/int/snt, fol/int/sem, fol/int/mod, fol/ntd/rul, tur/und/rep, tur/und/dec, tur/und/ver
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-SYN014 — Free Occurrence
- **Defined in**: fol/syn/fvs (primary)
- **Referenced in**: fol/syn/sub, fol/syn/ass
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-SYN015 — Bound Occurrence
- **Defined in**: fol/syn/fvs (primary)
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-SYN016 — Scope
- **Defined in**: fol/syn/fvs (primary)
- **Referenced in**: fol/syn/sub
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-SYN017 — Subformula
- **Defined in**: fol/syn/sbf (primary)
- **Referenced in**: fol/syn/fseq
- **Coverage**: FULL
- **Redundancy**: None

### PRIM-SYN018 — Equality Symbol
- **Defined in**: fol/syn/fol (primary)
- **Referenced in**: fol/syn/frm
- **Coverage**: FULL
- **Redundancy**: None

## Set-Bootstrap (BST)

### THM-BST001 — Cantor's Theorem (Naive)
- **Defined in**: sfr/siz/nen (primary)
- **Also introduced in**: sfr/siz/car, sfr/siz/nen-alt
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: COMPRESSION-TARGET (3 sections)

### THM-BST002 — N is Countably Infinite
- **Defined in**: sfr/siz/enm (primary)
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: None

### THM-BST003 — Countable Union of Countable Sets
- **Defined in**: sfr/siz/zigzag (primary)
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: None

## Computation (CMP)

### THM-CMP001 — Equivalence of Computation Models
- **Defined in**: tur/mac/var (primary)
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: None

### THM-CMP002 — Unsolvability of Halting Problem
- **Defined in**: tur/und/hal (primary)
- **Also introduced in**: tur/und/uns
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: COMPRESSION-TARGET (2 sections)

### THM-CMP003 — Rice's Theorem
- **Defined in**: cmp/thy/rce (primary)
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: None

### THM-CMP004 — s-m-n Theorem
- **Defined in**: cmp/rec/nft (primary)
- **Also introduced in**: cmp/thy/nfm, cmp/thy/smn
- **Referenced in**: cmp/thy/uni, cmp/thy/k1, cmp/thy/tot, cmp/thy/rce, cmp/thy/fix
- **Coverage**: FULL
- **Redundancy**: COMPRESSION-TARGET (3 sections)

### THM-CMP005 — Recursion Theorem (Kleene)
- **Defined in**: cmp/thy/fix (primary)
- **Referenced in**: cmp/thy/apf, cmp/thy/slf
- **Coverage**: FULL
- **Redundancy**: None

## Deduction (DED)

### THM-DED001 — Deduction Theorem
- **Defined in**: fol/axd/ded (primary)
- **Referenced in**: fol/axd/prv, fol/axd/ppr, fol/axd/qpr, fol/axd/ddq
- **Coverage**: FULL
- **Redundancy**: None

### THM-DED002 — Equivalence of Proof Systems
- **Defined in**: (none)
- **Referenced in**: (none)
- **Coverage**: ABSENT
- **Redundancy**: None

### THM-DED003 — Cut Elimination
- **Defined in**: (none)
- **Referenced in**: (none)
- **Coverage**: ABSENT
- **Redundancy**: None

### THM-DED004 — Normalization
- **Defined in**: (none)
- **Referenced in**: (none)
- **Coverage**: ABSENT
- **Redundancy**: None

### THM-DED005 — Lindenbaum's Lemma
- **Defined in**: fol/com/lin (primary)
- **Referenced in**: fol/com/cth
- **Coverage**: FULL
- **Redundancy**: None

## Semantics (SEM)

### THM-SEM001 — Isomorphism Lemma
- **Defined in**: mod/bas/iso (primary)
- **Referenced in**: mod/bas/ove, mod/bas/nsa, mod/mar/int, mod/mar/nst, mod/int/sep, mod/int/prf, mod/int/def, mod/lin/int, mod/lin/lsp, mod/lin/prf
- **Coverage**: FULL
- **Redundancy**: None

### THM-SEM002 — Coincidence Lemma
- **Defined in**: fol/syn/ext (primary)
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: None

### THM-SEM003 — Los's Theorem
- **Defined in**: (none)
- **Referenced in**: (none)
- **Coverage**: ABSENT
- **Redundancy**: None

## Set-Formal (SET)

### THM-SET001 — Well-Ordering iff Zorn iff AC
- **Defined in**: sth/choice/woproblem (primary)
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: None

### THM-SET002 — Transfinite Recursion Theorem
- **Defined in**: sth/spine/recursion (primary)
- **Referenced in**: sth/cardinals/classing, sth/card-arithmetic/opps, sth/card-arithmetic/ch
- **Coverage**: FULL
- **Redundancy**: None

### THM-SET003 — Cantor's Theorem (ZFC)
- **Defined in**: sth/choice/justifications (primary)
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: None

## Syntax (SYN)

### THM-SYN001 — Unique Readability (Formulas)
- **Defined in**: fol/syn/unq (primary)
- **Referenced in**: pl/syn/pre, fol/syn/mai
- **Coverage**: FULL
- **Redundancy**: None

### THM-SYN002 — Unique Readability (Terms)
- **Defined in**: fol/syn/unq (primary)
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: None

### THM-SYN003 — Substitution Lemma
- **Defined in**: fol/syn/ext (primary)
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: None

### THM-SYN004 — Structural Induction Principles
- **Defined in**: (none)
- **Referenced in**: (none)
- **Coverage**: ABSENT
- **Redundancy**: None

## Phase 2.5 Additions (Incompleteness Items — Resolved)

Former DEF-INC001–025 have been classified into existing domains.
Cross-reference table: DEF-INC → new ID mapping in `taxonomy/PHASE-2.5-RESOLUTION.md`.

### New SYN Items

### DEF-SYN009 — Bounded (Delta_0) Formula
- **Defined in**: inc/inp/s1c (primary)
- **Referenced in**: (used throughout inc/ sections)
- **Coverage**: FULL
- **Redundancy**: None
- **Former ID**: DEF-INC015

### DEF-SYN010 — Sigma_1 Formula
- **Defined in**: inc/inp/s1c (primary)
- **Referenced in**: inc/inp/1in, inc/inp/tar
- **Coverage**: FULL
- **Redundancy**: None
- **Former ID**: DEF-INC016

### DEF-SYN011 — Pi_1 Formula
- **Defined in**: inc/inp/s1c (primary)
- **Referenced in**: inc/inp/tar
- **Coverage**: FULL
- **Redundancy**: None
- **Former ID**: DEF-INC017

### New SEM Items

### DEF-SEM017 — Standard Model of Arithmetic (N)
- **Defined in**: inc/int/def (primary)
- **Referenced in**: inc/inp/s1c, inc/inp/tar
- **Coverage**: FULL
- **Redundancy**: None
- **Former ID**: DEF-INC002

### DEF-SEM018 — True Arithmetic (Th(N))
- **Defined in**: inc/int/def (primary)
- **Referenced in**: inc/inp/tar
- **Coverage**: FULL
- **Redundancy**: None
- **Former ID**: DEF-INC003

### DEF-SEM019 — Interpretability
- **Defined in**: inc/tcp/itp (primary)
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: None
- **Former ID**: DEF-INC020

### New DED Items

### DEF-DED011 — Robinson Arithmetic (Q)
- **Defined in**: inc/int/def (primary), inc/req/int (also introduced)
- **Referenced in**: inc/req/rpc, inc/req/bre, inc/req/cmp, inc/req/min, inc/req/crq, inc/req/cre, inc/req/rel, inc/req/und, inc/inp/s1c
- **Coverage**: FULL
- **Redundancy**: None
- **Former ID**: DEF-INC005

### DEF-DED012 — Peano Arithmetic (PA)
- **Defined in**: inc/int/def (primary)
- **Referenced in**: inc/req/int, inc/inp/prc, inc/inp/2in
- **Coverage**: FULL
- **Redundancy**: None
- **Former ID**: DEF-INC006

### DEF-DED013 — omega-Consistency
- **Defined in**: inc/tcp/oqn (primary)
- **Referenced in**: inc/inp/1in
- **Coverage**: FULL
- **Redundancy**: None
- **Former ID**: DEF-INC018

### DEF-DED014 — Derivability Conditions (Hilbert-Bernays-Lob)
- **Defined in**: inc/inp/prc (primary)
- **Referenced in**: inc/inp/2in, inc/inp/lob
- **Coverage**: FULL
- **Redundancy**: None
- **Former ID**: DEF-INC024

### THM-DED006 — Fixed-Point (Diagonal) Lemma
- **Defined in**: inc/inp/fix (primary)
- **Referenced in**: inc/inp/1in, inc/inp/ros, inc/inp/2in, inc/inp/lob, inc/inp/tar
- **Coverage**: FULL
- **Redundancy**: None
- **Former ID**: DEF-INC021

### THM-DED007 — Lob's Theorem
- **Defined in**: inc/inp/lob (primary)
- **Referenced in**: (none)
- **Coverage**: FULL
- **Redundancy**: None
- **Former ID**: DEF-INC025

### New CMP Items

### DEF-CMP011 — Axiomatizable Theory
- **Defined in**: inc/int/def (primary), inc/tcp/cax (also introduced)
- **Referenced in**: inc/int/ovr, inc/int/dec, inc/tcp/cdc, inc/tcp/inc
- **Coverage**: FULL
- **Redundancy**: None
- **Former IDs**: DEF-INC004 + DEF-INC008 (merged)

### DEF-CMP012 — Proof Predicate (Formalized)
- **Defined in**: inc/art/plk (primary), inc/art/pnd, inc/art/pax (proof system variants)
- **Referenced in**: inc/req/rpc, inc/req/und, inc/tcp/qce, inc/inp/1in, inc/inp/ros, inc/inp/prc
- **Coverage**: FULL
- **Redundancy**: None
- **Former ID**: DEF-INC012

### DEF-CMP013 — Beta-Function
- **Defined in**: inc/req/bet (primary)
- **Referenced in**: inc/req/pri, inc/inp/gop
- **Coverage**: FULL
- **Redundancy**: None
- **Former ID**: DEF-INC013

### DEF-CMP014 — Computable Inseparability
- **Defined in**: inc/tcp/ins (primary)
- **Referenced in**: inc/tcp/con
- **Coverage**: FULL
- **Redundancy**: None
- **Former ID**: DEF-INC019

### Subsumed Items (no new ID, redirected to existing)

| Former ID | Concept | Subsumed by | Notes |
|-----------|---------|-------------|-------|
| DEF-INC001 | Theory (deductively closed set) | DEF-DED003 | Already covered |
| DEF-INC007 | Complete Theory | DEF-SEM005 | Already covered |
| DEF-INC009 | Representability of Relations | DEF-CMP009 | Definition updated to include relations |
| DEF-INC010 | Symbol Code | PRIM-CMP011 | Sub-step of Godel numbering |
| DEF-INC011 | Godel Number of sequence | PRIM-CMP011 | Sub-step of Godel numbering |

### Stepping Stones (no taxonomy ID)

| Former ID | Concept | Used in |
|-----------|---------|---------|
| DEF-INC014 | Class C of functions | Representability proofs (pedagogical) |
| DEF-INC022 | Rosser provability predicate | CP-005 (stepping stone) |
| DEF-INC023 | Rosser sentence | CP-005 (stepping stone) |

### Upgraded SET Items

### DEF-SET012 — Von Neumann Hierarchy (V_alpha)
- **Defined in**: sth/spine/valpha (primary)
- **Referenced in**: sth/spine/Valphabasic, sth/spine/foundation, sth/spine/rank
- **Coverage**: FULL (upgraded from DEFERRED)
- **Redundancy**: None

### DEF-SET013 — Aleph Numbers
- **Defined in**: sth/card-arithmetic/ch (primary)
- **Referenced in**: sth/card-arithmetic/fix
- **Coverage**: FULL (upgraded from DEFERRED)
- **Redundancy**: None
- **Note**: Mapping correction — previously misattributed to DEF-SET009

### DEF-SET015 — Continuum Hypothesis
- **Defined in**: sth/card-arithmetic/ch (primary)
- **Referenced in**: (none)
- **Coverage**: FULL (upgraded from DEFERRED)
- **Redundancy**: None
- **Note**: Mapping correction — previously misattributed to DEF-SET010
