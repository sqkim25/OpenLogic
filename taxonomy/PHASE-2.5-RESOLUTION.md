# Phase 2.5 Resolution: INC Domain Integration + Gap Analysis

**Trigger**: COVERAGE-ANALYSIS.md found 25 INC-domain gap candidates (> 5 threshold).
**Scope**: Classify 25 DEF-INC items into existing domains, resolve 20 ABSENT items, resolve 4 DEFERRED items, fix 1 IMPLICIT item, correct mapping errors.

**Governing principle**: Per CONVENTIONS.md Principle 1, the domain catalog is closed (5 domains + BST). All INC items MUST be assigned to existing domains via boundary principles P1-P5.

---

## Part 1: INC Item Resolutions (25 items)

### Group A: New Taxonomy Items (16 new entries)

#### DED Domain (4 DEF + 2 THM = 6 new items)

| Old ID | New ID | Concept | Boundary | Justification |
|--------|--------|---------|----------|---------------|
| DEF-INC005 | DEF-DED011 | Robinson Arithmetic (Q) | P2 | Specific axiom system; defined as a set of non-logical axioms |
| DEF-INC006 | DEF-DED012 | Peano Arithmetic (PA) | P2 | First-order theory with induction schema; a proof-theoretic object |
| DEF-INC018 | DEF-DED013 | omega-Consistency | P2 | Strengthening of consistency; defined via derivability |
| DEF-INC024 | DEF-DED014 | Derivability Conditions (Hilbert-Bernays-Lob) | P2 | Conditions P1-P3 on formalized proof predicates |
| DEF-INC021 | THM-DED006 | Fixed-Point (Diagonal) Lemma | P2 | Metatheorem about provability: for any phi(x), exists sigma s.t. T |- sigma <-> phi(gn(sigma)) |
| DEF-INC025 | THM-DED007 | Lob's Theorem | P2 | If T |- (Bew(gn(phi)) -> phi) then T |- phi |

**DEF-DED011 — Robinson Arithmetic (Q)**
- Definition: The finite first-order theory Q in the language {0, S, +, x, <} with axioms: successor is injective, 0 is not a successor, every non-zero number is a successor, recursion equations for + and x, and basic < axioms.
- Depends: PRIM-DED002 (Non-Logical Axiom), PRIM-SYN009 (Language)
- OL sections: inc/int/def (primary), inc/req/int (referenced)
- Significance: Q is the minimal theory for which Godel's incompleteness theorems hold. It is weak enough to be finitely axiomatized yet strong enough that all computable functions are representable in it.

**DEF-DED012 — Peano Arithmetic (PA)**
- Definition: The first-order theory extending Q with the induction schema: for each formula phi(x), phi(0) & forall x(phi(x) -> phi(Sx)) -> forall x phi(x).
- Depends: DEF-DED011 (Q), PRIM-DED001 (Axiom Schema)
- OL sections: inc/int/def (primary), inc/inp/prc (referenced)
- Significance: PA is the standard first-order theory of arithmetic. The incompleteness theorems show PA is incomplete if consistent.

**DEF-DED013 — omega-Consistency**
- Definition: A theory T is omega-consistent if there is no formula phi(x) such that T |- phi(n-bar) for all n in N and T |- exists x not-phi(x). Stronger than consistency; needed for Godel's original proof (Rosser later weakened to consistency).
- Depends: DEF-DED001 (Syntactic Consistency), PRIM-DED006 (Provability)
- OL sections: inc/tcp/oqn (primary)

**DEF-DED014 — Derivability Conditions (Hilbert-Bernays-Lob)**
- Definition: Three conditions on a proof predicate Bew(x) that suffice for the Second Incompleteness Theorem:
  - D1: If T |- phi then T |- Bew(gn(phi))
  - D2: T |- Bew(gn(phi -> psi)) -> (Bew(gn(phi)) -> Bew(gn(psi)))
  - D3: T |- Bew(gn(phi)) -> Bew(gn(Bew(gn(phi))))
- Depends: DEF-CMP012 (Proof Predicate), PRIM-DED006 (Provability)
- OL sections: inc/inp/prc (primary)

**THM-DED006 — Fixed-Point (Diagonal) Lemma**
- Statement: For any formula phi(x) with one free variable, there exists a sentence sigma such that T |- sigma <-> phi(gn(sigma)).
- Depends: PRIM-CMP011 (Godel Numbering), DEF-CMP009 (Representability), DEF-SYN001 (Substitution)
- OL sections: inc/inp/fix (primary), inc/inp/1in, inc/inp/ros, inc/inp/2in, inc/inp/lob, inc/inp/tar (referenced)
- Significance: The master tool for self-reference. Godel's first and second incompleteness theorems, Tarski's undefinability, and Lob's theorem all follow from specific instantiations.

**THM-DED007 — Lob's Theorem**
- Statement: If T |- (Bew(gn(phi)) -> phi) then T |- phi. (If a theory proves "if phi is provable then phi is true," then the theory actually proves phi.)
- Depends: DEF-DED014 (Derivability Conditions), THM-DED006 (Fixed-Point Lemma)
- OL sections: inc/inp/lob (primary)

#### CMP Domain (4 new DEF items)

| Old ID | New ID | Concept | Boundary | Justification |
|--------|--------|---------|----------|---------------|
| DEF-INC004 + DEF-INC008 | DEF-CMP011 | Axiomatizable Theory | P3 | Effective property: axiom set is c.e. |
| DEF-INC012 | DEF-CMP012 | Proof Predicate (Formalized) | P3 | Representability of proof relation |
| DEF-INC013 | DEF-CMP013 | Beta-Function | P3 | Encoding technique for arithmetization |
| DEF-INC019 | DEF-CMP014 | Computable Inseparability | P3 | Two c.e. sets with no decidable separator |

**DEF-CMP011 — Axiomatizable Theory**
- Definition: A theory T is axiomatizable (effectively axiomatizable) if T = Cn(Sigma) for some c.e. set Sigma of sentences. T is decidably axiomatizable if Sigma can be chosen decidable. T is finitely axiomatizable if Sigma can be chosen finite.
- Depends: PRIM-CMP007 (Semi-Decidable Set), DEF-DED003 (Deductive Closure)
- Merges: DEF-INC004 (Axiomatized Theory) + DEF-INC008 (Axiomatizable Theory)
- OL sections: inc/int/def (primary), inc/tcp/cax (referenced)

**DEF-CMP012 — Proof Predicate (Formalized)**
- Definition: A Sigma_1 formula Prf(x,y) (or Prf_Gamma(x,y)) representing in a formal theory T the relation "y encodes a proof in T of the formula with Godel number x." The provability predicate is Bew(x) = exists y Prf(x,y).
- Depends: PRIM-CMP011 (Godel Numbering), DEF-CMP009 (Representability), PRIM-DED005 (Derivation)
- OL sections: inc/art/plk, inc/art/pnd, inc/art/pax (primary, with proof system variants)

**DEF-CMP013 — Beta-Function**
- Definition: Godel's beta function beta(c, d, i) = rem(c, 1 + (i+1)*d) where rem is the remainder function. Using the Chinese Remainder Theorem, for any finite sequence a_0, ..., a_n there exist c, d such that beta(c, d, i) = a_i for all i <= n. This allows encoding finite sequences within the language of arithmetic (without Godel's prime-power encoding).
- Depends: PRIM-CMP011 (Godel Numbering), PRIM-BST012 (Natural Number)
- OL sections: inc/req/bet (primary)

**DEF-CMP014 — Computable Inseparability**
- Definition: Two disjoint c.e. sets A, B are computably inseparable if there is no decidable set C with A subset C and B subset C-complement. Equivalently: no computable function correctly separates members of A from members of B.
- Depends: PRIM-CMP006 (Decidable Set), PRIM-CMP007 (Semi-Decidable Set)
- OL sections: inc/tcp/ins (primary)
- Significance: Used to prove that Q is essentially undecidable (no consistent extension is decidable).

#### SYN Domain (3 new DEF items)

| Old ID | New ID | Concept | Boundary | Justification |
|--------|--------|---------|----------|---------------|
| DEF-INC015 | DEF-SYN009 | Bounded (Delta_0) Formula | P1 | Purely syntactic: quantifier structure |
| DEF-INC016 | DEF-SYN010 | Sigma_1 Formula | P1 | Purely syntactic: quantifier prefix |
| DEF-INC017 | DEF-SYN011 | Pi_1 Formula | P1 | Purely syntactic: quantifier prefix |

**DEF-SYN009 — Bounded (Delta_0) Formula**
- Definition: A formula in the language of arithmetic in which all quantifiers are bounded: forall x < t and exists x < t for some term t. Delta_0 formulas define decidable properties of natural numbers.
- Depends: PRIM-SYN004 (Quantifier), PRIM-SYN010 (Term), PRIM-SYN012 (Formula)
- OL sections: inc/inp/s1c (primary)

**DEF-SYN010 — Sigma_1 Formula**
- Definition: A formula of the form exists x_1 ... exists x_n phi where phi is Delta_0. Sigma_1 formulas define c.e. (semi-decidable) properties.
- Depends: DEF-SYN009 (Delta_0), PRIM-SYN004 (Quantifier)
- OL sections: inc/inp/s1c (primary)
- Connection: PRIM-CMP007 (Semi-Decidable Set) — a set is c.e. iff it is Sigma_1-definable in N.

**DEF-SYN011 — Pi_1 Formula**
- Definition: A formula of the form forall x_1 ... forall x_n phi where phi is Delta_0. Pi_1 formulas define co-c.e. properties. Consistency statements are Pi_1.
- Depends: DEF-SYN009 (Delta_0), PRIM-SYN004 (Quantifier)
- OL sections: inc/inp/s1c (primary)

#### SEM Domain (3 new DEF items)

| Old ID | New ID | Concept | Boundary | Justification |
|--------|--------|---------|----------|---------------|
| DEF-INC002 | DEF-SEM017 | Standard Model of Arithmetic (N) | P1 | A specific structure (interpretation) |
| DEF-INC003 | DEF-SEM018 | True Arithmetic (Th(N)) | P1 | Theory of a structure: defined via truth |
| DEF-INC020 | DEF-SEM019 | Interpretability | P1 | About truth-preservation between theories |

**DEF-SEM017 — Standard Model of Arithmetic (N)**
- Definition: The intended structure N = <N, 0, S, +, x, <> for the language of arithmetic, where N = {0, 1, 2, ...}, S is successor, + and x have their usual meaning.
- Depends: PRIM-SEM001 (Structure), PRIM-BST012 (Natural Number)
- OL sections: inc/int/def (primary)
- Significance: The standard model is the "intended" interpretation of arithmetic. Non-standard models (guaranteed by compactness) contain "infinite" numbers beyond all standard naturals.

**DEF-SEM018 — True Arithmetic (Th(N))**
- Definition: Th(N) = {phi : N |= phi}, the set of all sentences true in the standard model. True arithmetic is a complete, consistent, undecidable theory.
- Depends: DEF-SEM017 (Standard Model), DEF-SEM006 (Theory of a Structure)
- OL sections: inc/int/def (primary), inc/inp/tar (referenced)
- Significance: Tarski's undefinability theorem shows Th(N) is not definable within N. Church's theorem shows Th(N) is not decidable.

**DEF-SEM019 — Interpretability**
- Definition: A theory T_1 is interpretable in T_2 if there exists a translation of the language of T_1 into the language of T_2 that preserves provability (and hence truth in models of T_2 satisfying the translation of T_1's axioms).
- Depends: PRIM-SEM001 (Structure), PRIM-DED006 (Provability)
- OL sections: inc/tcp/itp (primary)

### Group B: Subsumed Under Existing Items (5 items, no new IDs)

| Old ID | Concept | Resolution | Existing ID |
|--------|---------|------------|-------------|
| DEF-INC001 | Theory (deductively closed set) | Already covered | DEF-DED003 (Deductive Closure) |
| DEF-INC007 | Complete Theory | Already covered | DEF-SEM005 (Semantic Completeness of a theory) |
| DEF-INC009 | Representability of Relations | Subsume | DEF-CMP009 (Representability) — update to explicitly include relations |
| DEF-INC010 | Symbol Code | Sub-step | PRIM-CMP011 (Godel Numbering) — part of encoding construction |
| DEF-INC011 | Godel Number of sequence | Sub-step | PRIM-CMP011 (Godel Numbering) — part of encoding construction |

**Action for DEF-CMP009**: Update the definition in DOMAIN-COMPUTATION.md to explicitly state: "A relation R subset N^k is representable if its characteristic function is representable, equivalently if there exists phi(x_1,...,x_k) such that R(n_1,...,n_k) iff T |- phi(n-bar_1,...,n-bar_k)."

### Group C: Stepping Stones (3 items, no taxonomy ID)

| Old ID | Concept | Classification | Used in |
|--------|---------|---------------|---------|
| DEF-INC014 | Class C of functions | Pedagogical | Representability proofs |
| DEF-INC022 | Rosser provability predicate | Stepping stone | CP-005 (Rosser's improvement of Godel I) |
| DEF-INC023 | Rosser sentence | Stepping stone | CP-005 |

### Summary

| Category | Count | Items |
|----------|-------|-------|
| New taxonomy items | 16 | 6 DED + 4 CMP + 3 SYN + 3 SEM |
| Subsumed | 5 | Covered by existing DEF-DED003, DEF-SEM005, DEF-CMP009, PRIM-CMP011 |
| Stepping stones | 3 | Pedagogical or CP support, no ID needed |
| Merged pairs | 1 | INC004+INC008 -> DEF-CMP011 |
| **Total resolved** | **25** | |

---

## Part 2: ABSENT Item Resolutions (20 items)

### Already Covered (taxonomy redundancy) — 2 items

| ID | Concept | Resolution |
|----|---------|------------|
| DEF-SET011 | Cantor's Theorem (formal) | Redundant with THM-SET003 (Cantor's Theorem ZFC) which IS mapped and FULL |
| THM-DED003 | Cut Elimination | Redundant with CP-010 (Cut Elimination) which IS mapped and FULL |

**Action**: Mark DEF-SET011 as "Covered by THM-SET003" and THM-DED003 as "Covered by CP-010" in registry. These are internal taxonomy redundancies that should be consolidated.

### Extension-Only (correctly absent from CORE) — 7 items

| ID | Concept | Extension Location |
|----|---------|-------------------|
| DEF-CMP006 | Lambda-Definable Function | lambda-calculus extension (EXTENSION-MAP.md) |
| DEF-SEM015 | Ultraproduct | Advanced model theory (not in OL) |
| DEF-SEM016 | Embedding | Advanced model theory (not in OL) |
| THM-SEM003 | Los's Theorem | Requires ultraproducts (not in OL) |
| THM-DED004 | Normalization | Intuitionistic logic extension |
| DEF-SEM012 | Diagram (Atomic/Elementary) | Advanced model theory (not in OL's core chapters) |
| DEF-SEM014 | Categoricity | Advanced model theory (not in OL's core chapters) |

**Note**: DEF-SEM012, DEF-SEM014, DEF-SEM015, DEF-SEM016, and THM-SEM003 were included in the Phase 1 taxonomy under the model theory supplement (UNK-GLB003 resolution: "if SEM exceeds 30 items, split into core + model theory supplement"). These are legitimately absent from OL's coverage and should remain in the taxonomy as targets for any future model theory extension.

### IMPLICIT (used but not formally defined) — 6 items

| ID | Concept | Evidence | Resolution |
|----|---------|----------|------------|
| DEF-CMP007 | Productive Set | Concept used in creative set definition (cmp/thy/cce) but no dedicated section | Keep IMPLICIT |
| DEF-DED009 | Derived Rule | Used informally in proof system chapters | Keep IMPLICIT |
| DEF-DED010 | Admissible Rule | Used informally | Keep IMPLICIT |
| DEF-SYN007 | Formula Complexity | Used in induction proofs without formal definition | Keep IMPLICIT |
| PRIM-SEM014 | Homomorphism | OL's model theory uses isomorphism/substructure but not general homomorphisms | Keep ABSENT (not even implicit) |
| THM-SYN004 | Structural Induction Principles | Structural induction used extensively but not stated as a named theorem | Keep IMPLICIT |

**Correction**: PRIM-SEM014 should remain ABSENT, not IMPLICIT. OL genuinely does not use general homomorphisms. Reclassify as Extension-Only.

### Genuinely Absent (no OL coverage, taxonomy-only) — 5 items

| ID | Concept | Assessment |
|----|---------|------------|
| DEF-DED004 | Conservative Extension | Important concept not explicitly defined in OL. Retain in taxonomy. |
| DEF-SYN002 | Simultaneous Substitution | OL defines single substitution only. Retain in taxonomy as needed for SOL. |
| DEF-SYN004 | Alphabetic Variant | Not defined in OL. Retain in taxonomy. |
| THM-DED002 | Equivalence of Proof Systems | OL proves soundness/completeness per system but doesn't state general equivalence. Retain. |
| PRIM-SET001 | Set (formal) | ZFC's sole primitive — implicitly assumed in all sth/ sections. Upgrade to IMPLICIT. |

### Summary

| Resolution | Count | Items |
|-----------|-------|-------|
| Already covered (internal redundancy) | 2 | DEF-SET011, THM-DED003 |
| Extension-only | 8 | DEF-CMP006, DEF-SEM012, DEF-SEM014, DEF-SEM015, DEF-SEM016, PRIM-SEM014, THM-SEM003, THM-DED004 |
| IMPLICIT (upgrade) | 5 | DEF-CMP007, DEF-DED009, DEF-DED010, DEF-SYN007, THM-SYN004 |
| IMPLICIT (new) | 1 | PRIM-SET001 |
| Genuinely absent | 4 | DEF-DED004, DEF-SYN002, DEF-SYN004, THM-DED002 |
| **Total** | **20** | |

---

## Part 3: DEFERRED Item Resolutions (4 items)

| ID | Concept | OL Coverage | Resolution |
|----|---------|------------|------------|
| DEF-SET012 | Von Neumann Hierarchy (V_alpha) | sth/spine/valpha (formal definition), sth/spine/Valphabasic (properties) | **Upgrade to FULL** |
| DEF-SET013 | Aleph Numbers | sth/card-arithmetic/ch (defines aleph and beth numbers) | **Upgrade to FULL** |
| DEF-SET014 | Cofinality | Not explicitly defined in mapped sections | **Keep DEFERRED** |
| DEF-SET015 | Continuum Hypothesis | sth/card-arithmetic/ch (defines CH and GCH, states independence) | **Upgrade to FULL** |

---

## Part 4: IMPLICIT Item Resolution (1 item)

| ID | Concept | Current Status | Resolution |
|----|---------|---------------|------------|
| PRIM-SET002 | Membership (formal) | IMPLICIT | **Upgrade to FULL**: sth/story/extensionality explicitly axiomatizes membership as the primitive relation of set theory. The Extensionality axiom (AX-SET001) defines sets in terms of membership. |

---

## Part 5: Mapping Error Corrections

### Error 1: sth/card-arithmetic/ch ID Assignments

**Current mapping** (SECTION-MAP.md):
- `defn (aleph numbers, beth numbers) -> DEF-SET009`
- `defish[GCH] -> DEF-SET010`
- `defish[CH] -> DEF-SET010`

**Problem**: DEF-SET009 = Well-Ordering, DEF-SET010 = Zorn's Lemma. The section sth/card-arithmetic/ch does NOT define well-ordering or Zorn's lemma — it defines aleph numbers (DEF-SET013) and the Continuum Hypothesis (DEF-SET015).

**Correction**:
- `defn (aleph numbers, beth numbers)` -> **DEF-SET013** (Aleph Numbers, upgraded from DEFERRED)
- `defish[GCH]` -> **DEF-SET015** (Continuum Hypothesis, upgraded from DEFERRED)
- `defish[CH]` -> **DEF-SET015**
- Remove DEF-SET009 and DEF-SET010 from sth/card-arithmetic/ch "Introduces"

**Where are DEF-SET009 and DEF-SET010 actually defined?**
- DEF-SET009 (Well-Ordering): Should be in sth/choice/woproblem (which already maps to THM-SET001: Well-Ordering iff Zorn iff AC)
- DEF-SET010 (Zorn's Lemma): Should be in sth/choice/woproblem alongside THM-SET001

**Action**: Update sth/card-arithmetic/ch and sth/choice/woproblem entries in SECTION-MAP.

---

## Part 6: Updated Taxonomy Statistics

### Before Phase 2.5

| Metric | Count |
|--------|-------|
| Total taxonomy items | 189 (176 PRIM/DEF/AX/THM + 13 CPs) |
| FULL coverage | 164 (86.8%) |
| ABSENT | 20 |
| IMPLICIT | 1 |
| DEFERRED | 4 |

### After Phase 2.5

| Metric | Count |
|--------|-------|
| Total taxonomy items | 205 (192 PRIM/DEF/AX/THM + 13 CPs) |
| New items added | 16 |
| FULL coverage | 183 (89.3%) |
| IMPLICIT (upgrade from ABSENT) | 6 |
| EXTENSION-ONLY (reclassified from ABSENT) | 8 |
| Genuinely absent (taxonomy-only) | 4 |
| DEFERRED (remaining) | 1 (DEF-SET014 Cofinality) |
| Internal redundancies resolved | 2 (DEF-SET011, THM-DED003) |

### Item Count by Domain (after Phase 2.5)

| Domain | PRIM | DEF | AX | THM | Total |
|--------|------|-----|----|-----|-------|
| BST | 16 | 5 | 0 | 3 | 24 |
| SYN | 18 | 11 | 3 | 4 | 36 |
| SEM | 15 | 19 | 0 | 3 | 37 |
| DED | 10 | 14 | 3 | 7 | 34 |
| CMP | 12 | 14 | 0 | 5 | 31 |
| SET | 3 | 15 | 9 | 3 | 30 |
| **Total** | **74** | **78** | **15** | **25** | **192** |
| CPs | — | — | — | — | **13** |
| **Grand Total** | | | | | **205** |

---

## Part 7: Files Modified

1. **taxonomy/PHASE-2.5-RESOLUTION.md** (this file) — NEW
2. **taxonomy/CONVENTIONS.md** — UPDATE Primitive Registry (Section 9) with 16 new rows
3. **taxonomy/phase2/COVERAGE-ANALYSIS.md** — UPDATE coverage statistics and resolution summary
4. **taxonomy/phase2/CONCEPT-INDEX.md** — UPDATE with new item entries and resolved statuses
5. **taxonomy/phase2/SECTION-MAP.md** — CORRECTION of sth/card-arithmetic/ch mapping error

---

## Part 8: Implications for Phase 3

1. **16 new taxonomy items** add precision to the Incompleteness mapping. Phase 3 compression can now trace every INC section to specific taxonomy IDs rather than generic "DEF-INC" placeholders.

2. **The arithmetic hierarchy items (DEF-SYN009-011)** create a cross-domain bridge: SYN defines the formula classes, CMP characterizes the corresponding set complexity (Delta_0 = decidable, Sigma_1 = c.e., Pi_1 = co-c.e.).

3. **Specific theory items (DEF-DED011 Q, DEF-DED012 PA)** formalize the key objects of study in incompleteness. Phase 3 can now distinguish "sections that define Q/PA" from "sections that prove results about Q/PA."

4. **8 extension-only items** confirm that the Phase 1 taxonomy intentionally exceeds OL's core coverage (the model theory supplement was designed for future extension). These should NOT be counted as gaps.

5. **4 genuinely absent items** (DEF-DED004, DEF-SYN002, DEF-SYN004, THM-DED002) are legitimate taxonomy items without OL coverage. Phase 3 should note these as concepts the lean text should define even though OL doesn't.
