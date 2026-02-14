# Phase 3: COMPRESSION

> **Phase 3 of 4** | Prev: [02-MAPPING.md](02-MAPPING.md) | Next: [04-RECOMPOSITION.md](04-RECOMPOSITION.md)
> Templates: [06-TEMPLATES.md](06-TEMPLATES.md) §S4 | Quality gate: [05-QUALITY-GATES.md](05-QUALITY-GATES.md) §1 (Gate 3)

---

## 1. Goal

Phase 3 transforms the mapping artifacts from Phase 2 into a concrete compression plan. You are not writing prose yet -- you are deciding *what to do* with every section, *how to unify notation*, and *where cross-references will land*.

### Input

- **From Phase 2**: Section map, coverage matrix, redundancy resolution, gap analysis
- **From Phase 1**: Domain specs, item registry, dependency DAG, composition patterns

### Output

| Artifact | Description |
|----------|-------------|
| Per-section directives | One directive per source section: KEEP / MERGE / RELOCATE / CONDENSE / CUT / EXTRACT-PATTERN |
| Notation concordance | One row per notation variant, mapping to canonical form |
| Cross-reference plan | Table of forward/backward reference anchors |
| Lean outline | Chapter-and-section skeleton with estimated page counts |

### Exit Criterion

Proceed to Phase 4 when Quality Gate 3 ([05-QUALITY-GATES.md](05-QUALITY-GATES.md) §1, Gate 3) passes with zero blocking items and all notation conflicts resolved.

---

## 2. The Action Vocabulary

Every source section receives exactly one directive. Use these six actions and no others.

| Action | Meaning | When to Use | Math Logic Example | Organic Chemistry Example |
|--------|---------|-------------|-------------------|--------------------------|
| **KEEP** | Retain the section in place, with only notation normalization | The section is the canonical treatment of its item(s), is well-written, and sits at the correct dependency depth | OL `first-order-logic/syntax/terms-formulas/` is the canonical treatment of PRIM-SYN010 (Term) and PRIM-SYN012 (Formula) -- KEEP | Clayden Ch. 2 "Organic Structures" is the canonical treatment of PRIM-BOND (covalent bond) and PRIM-HYBRID (hybridization) -- KEEP |
| **MERGE** | Combine two or more sections treating the same item into one | Redundancy resolution in Phase 2 identified overlapping treatments | OL defines "consistency" in both `first-order-logic/completeness/` and `incompleteness/` -- MERGE into the DED chapter under DEF-DED001 | Clayden Ch. 8 and Ch. 19 both define "nucleophilicity" -- MERGE into the reactivity chapter |
| **RELOCATE** | Move the section to a different position in the lean text | The section treats a concept that belongs to a different domain or dependency layer | OL's `sets-functions-relations/` treatment of "countability" belongs in BST (Level-0), but currently follows FOL material -- RELOCATE to the BST chapter | A discussion of pKa values buried in the amines chapter belongs in the acids/bases chapter -- RELOCATE |
| **CONDENSE** | Shrink the section to a definition + one key theorem + one example | The section covers supplementary material that is not on the critical path but must be retained for completeness | OL's tableau completeness proof -- CONDENSE to statement + proof sketch, since the Hilbert-style completeness proof is canonical (CP-002) | A section on obscure name reactions -- CONDENSE to the named reaction, mechanism summary, and one application |
| **CUT** | Remove entirely; mark as out-of-scope or purely pedagogical | The section contains no formal content (pure motivation, historical narrative, or exercises with no new concepts) | OL `history/` sections that retell the biography of Godel without introducing any formal concept -- CUT | A "fun facts about benzene" sidebar with no structural content -- CUT |
| **EXTRACT-PATTERN** | Pull a cross-domain result out of a domain chapter into the composition-pattern catalog | The section proves or states a metatheorem that spans multiple domains | OL's proof of the Completeness Theorem in `first-order-logic/completeness/` is CP-002 (SEM x DED x BST) -- EXTRACT-PATTERN into composition-pattern chapter | A proof that SN2 rate depends on both nucleophilicity (reactivity domain) and steric effects (structure domain) -- EXTRACT-PATTERN into the cross-domain patterns chapter |

### Rules

1. Every source section MUST receive exactly one directive. Sections with no directive are a blocking defect.
2. MERGE directives MUST specify which section is the "survivor" (the one that absorbs the others). Mark non-survivors as MERGE-INTO with a pointer to the survivor.
3. RELOCATE directives MUST specify the target chapter and insertion point (after which section).
4. CUT directives MUST include a one-line justification proving no formal concept is lost.
5. EXTRACT-PATTERN directives MUST reference the composition pattern ID (CP-NNN).

---

## 3. The Triage Decision Tree

For each source section, walk this tree top-to-bottom. Stop at the first matching leaf.

```
Does the section introduce or prove a composition pattern (CP-NNN)?
  YES --> EXTRACT-PATTERN
  NO  --> continue

Is the section purely pedagogical, historical, or exercise-only (no PRIM/DEF/AX/THM)?
  YES --> CUT (with justification)
  NO  --> continue

Was this section flagged as redundant in Phase 2's redundancy resolution?
  YES --> Is this section the canonical treatment?
            YES --> KEEP (absorb the non-canonical material)
            NO  --> MERGE-INTO the canonical section
  NO  --> continue

Does the section sit at the wrong dependency depth (treats domain X material but lives in domain Y's chapter)?
  YES --> RELOCATE to the correct chapter
  NO  --> continue

Is the section on the critical path (defines items needed by >= 2 later items)?
  YES --> KEEP
  NO  --> CONDENSE
```

### Special Case: Partial Canonicity

A section may be the canonical treatment for *some* items but not others. In this case, split the directive:

- KEEP the canonical items in place.
- MERGE the non-canonical items into their respective canonical sections.
- Record this as a **split directive** in the per-section table.

**Math logic example**: OL's `first-order-logic/completeness/` is canonical for DEF-DED002 (Maximal Consistent Set) and THM-DED005 (Lindenbaum's Lemma), but it also restates DEF-SEM002 (Satisfiable) which is canonically owned by `first-order-logic/semantics/`. Split: KEEP the DED material, MERGE-INTO the SEM chapter for the satisfiability restatement.

**Organic chemistry example**: A chapter on "Reactions of Alcohols" is canonical for dehydration mechanisms but also restates acid-base equilibria from the acids chapter. Split: KEEP the dehydration material, MERGE-INTO the acids/bases chapter for the equilibria restatement.

---

## 4. Step 1: Per-Section Directives

Produce a table with one row per source section. Use the template from [06-TEMPLATES.md](06-TEMPLATES.md) section 4.

### Procedure

1. Open the section map from Phase 2.
2. For each row, walk the triage decision tree (Section 3 above).
3. Record the directive, the justification, and the taxonomy item IDs affected.
4. Flag any section where the decision is ambiguous as REVIEW-NEEDED. Do not guess.

### Table Format

| Source Section | Directive | Target (if MERGE/RELOCATE) | Items Affected | Justification |
|---------------|-----------|---------------------------|----------------|---------------|
| `first-order-logic/syntax/terms-formulas/` | KEEP | -- | PRIM-SYN010, PRIM-SYN012 | Canonical treatment; correct dependency depth |
| `first-order-logic/completeness/henkin/` | EXTRACT-PATTERN | CP-002 chapter | CP-002, DEF-DED002, THM-DED005 | Cross-domain metatheorem (SEM x DED x BST) |
| `incompleteness/representability-in-q/` | KEEP | -- | DEF-CMP009, DEF-DED011 | Canonical treatment of representability; correct depth |
| `history/hilbert/` | CUT | -- | (none) | Purely biographical; no PRIM/DEF/AX/THM introduced |
| `first-order-logic/beyond/compactness/` | EXTRACT-PATTERN | CP-003 chapter | CP-003, DEF-SEM002, DEF-SEM003 | Cross-domain metatheorem (SEM x BST) |
| `propositional-logic/semantics/tautologies/` | KEEP | -- | DEF-SEM009, DEF-SEM010 | Canonical PL semantics treatment |

**Math logic example (split directive)**: `first-order-logic/completeness/consistency/` -- Split: KEEP DEF-DED001 (syntactic consistency), MERGE-INTO `first-order-logic/semantics/` for restated DEF-SEM004 (semantic consistency). Justification: DED owns syntactic consistency; SEM owns semantic consistency; their connection is via CP-001/CP-002, not restatement.

**Organic chemistry example (split directive)**: "Substitution vs. Elimination" chapter -- Split: KEEP the SN2/SN1 mechanism material, MERGE-INTO the elimination chapter for E2/E1 material. Justification: each reaction type is canonically owned by its mechanism chapter.

### Completeness Check

After filling the table, verify:
- Every section from the Phase 2 section map has exactly one row.
- Every taxonomy item ID from the Phase 1 registry appears in at least one row.
- No row has a blank Directive cell.

---

## 5. Step 2: Notation Unification

Build the notation concordance: a table mapping every notation variant in the source corpus to one canonical form.

### Procedure

1. Scan the source corpus for every mathematical symbol, variable convention, and naming convention.
2. For each concept with multiple notation variants, choose one canonical form.
3. Record the canonical form, all variants, and the decision rationale.

### Decision Heuristic

When choosing the canonical notation, apply these criteria in order:

1. **Taxonomy precedent**: If the Phase 1 domain specs already use a notation, adopt it. This takes absolute priority.
2. **Frequency**: If no taxonomy precedent, choose the variant used most often in the source corpus.
3. **Standard reference**: If frequency is tied, follow the convention in the primary source (SRC-GLB001 through SRC-GLB015).
4. **Readability**: If all else is equal, prefer the notation that minimizes ambiguity and maximizes readability at the expression level.

### Concordance Table Format

| Concept | Canonical Form | Variant 1 | Variant 2 | Variant 3 | Rationale |
|---------|---------------|-----------|-----------|-----------|-----------|
| Satisfaction | $\mathfrak{A} \vDash \varphi[s]$ | $\mathfrak{A}, s \models \varphi$ | $M \models_v \varphi$ | $\mathcal{A} \Vdash \varphi[s]$ | Taxonomy precedent (PRIM-SEM007) |
| Provability | $\Gamma \vdash \varphi$ | $\Gamma \vdash_S \varphi$ | $\Gamma \Vdash \varphi$ | -- | Taxonomy precedent (PRIM-DED006); subscript S added only when proof system S is ambiguous |
| Structure | $\mathfrak{A}$ | $\mathcal{M}$ | $M$ | $\mathcal{A}$ | Taxonomy precedent (PRIM-SEM001); fraktur avoids collision with set notation |
| Godel number | $\ulcorner \varphi \urcorner$ | $\#(\varphi)$ | $\text{gn}(\varphi)$ | $\lceil \varphi \rceil$ | Frequency: corner quotes most common in OL and standard references |
| Substitution | $\varphi[t/x]$ | $\varphi^x_t$ | $S^x_t \varphi$ | $\varphi(t/x)$ | Taxonomy precedent (DEF-SYN001) |
| Deductive closure | $\text{Cn}(\Gamma)$ | $\text{Ded}(\Gamma)$ | $\overline{\Gamma}$ | -- | Taxonomy precedent (DEF-DED003) |

**Math logic example**: The source uses both $\mathcal{M}$ and $\mathfrak{A}$ for structures. The taxonomy specs use $\mathfrak{A}$. Choose $\mathfrak{A}$ as canonical. Replace every occurrence of $\mathcal{M}$ in the lean text.

**Organic chemistry example**: The source uses both "Nu" and "Nuc" as abbreviations for nucleophile. The IUPAC recommendation is "Nu". Choose "Nu" as canonical.

### Failure Mode: Overloaded Symbols

A single symbol sometimes means different things in different contexts. Do NOT resolve this by picking one meaning. Instead:

1. Identify the overload. Record it in the concordance with a CONFLICT flag.
2. Disambiguate by adding a subscript, superscript, or contextual qualifier in the lean text.
3. Add a disambiguation note to the notation index (Phase 4 artifact).

**Math logic example**: $\vDash$ means both "satisfaction" ($\mathfrak{A} \vDash \varphi$) and "logical consequence" ($\Gamma \vDash \varphi$). These are related but distinct (PRIM-SEM007 vs. PRIM-SEM010). Resolution: keep $\vDash$ for both, but always include the left-hand argument to disambiguate. Never write bare $\vDash \varphi$ without clarifying whether the context is "valid" (PRIM-SEM009) or "true in a structure."

**Organic chemistry example**: "R" means both an alkyl group (in mechanisms) and the gas constant (in thermodynamics). Resolution: use "R" for alkyl groups in structural formulas and "$R$" (italicized, with units) for the gas constant. Add a disambiguation note.

---

## 6. Step 3: Cross-Reference Plan

Map every forward reference and backward reference that will appear in the lean text. The goal is zero dangling references and zero circular dependencies within a dependency layer.

### Procedure

1. For each KEEP and MERGE-survivor section, list every taxonomy item it references that is defined elsewhere.
2. Classify each reference as **backward** (target is defined earlier in the lean outline) or **forward** (target is defined later).
3. Eliminate forward references by reordering. If reordering is impossible (mutual dependency), introduce a **forward declaration**: a one-sentence preview of the concept with a pointer to its full definition.

### Cross-Reference Table Format

| Source Section | References Item | Defined In | Direction | Resolution |
|---------------|----------------|------------|-----------|------------|
| DED Ch. 3: Provability | PRIM-SYN012 (Formula) | SYN Ch. 1 | Backward | No action needed |
| SEM Ch. 2: Satisfaction | PRIM-DED006 (Provability) | DED Ch. 3 | Forward | Forward-declare provability in SEM Ch. 2 preamble |
| CMP Ch. 5: Godel Numbering | PRIM-SYN012 (Formula) | SYN Ch. 1 | Backward | No action needed |
| CP Chapter: Completeness | DEF-DED002 (Max. Consistent Set) | DED Ch. 3 | Backward | No action needed |
| CP Chapter: Incompleteness | DEF-CMP009 (Representability) | CMP Ch. 5 | Backward | No action needed |

**Math logic example (forward reference)**: The Semantics chapter discusses "logical consequence" ($\Gamma \vDash \varphi$, PRIM-SEM010) and wants to mention that it will later be connected to provability ($\Gamma \vdash \varphi$, PRIM-DED006) via Soundness (CP-001). Since DED comes after SEM in the dependency order, insert a forward declaration: "We will show in Chapter N (Soundness, CP-001) that $\Gamma \vDash \varphi$ implies $\Gamma \vdash \varphi$."

**Organic chemistry example (forward reference)**: The bonding chapter wants to mention aromaticity (defined two chapters later). Insert a forward declaration: "We will formalize the concept of aromaticity in Chapter N using Huckel's rule."

### Rules

1. Backward references are always safe. Include them freely.
2. Forward references MUST be forward-declared. A bare forward reference (mentioning an undefined term without a forward declaration) is a blocking defect in Quality Gate 3.
3. The lean outline (Step 4) determines the ordering. If Step 3 reveals too many forward references, return to Step 4 and reorder.
4. Composition patterns (CP-NNN) inherently reference multiple domains. Place them AFTER all referenced domains in the lean outline. If a composition pattern must appear earlier (for pedagogical reasons), forward-declare the later-domain items it needs.

---

## 7. Step 4: Lean Outline

Assemble the chapter-and-section skeleton for the lean text. This is the table of contents for Phase 4.

### Ordering Principle

Follow the dependency DAG from Phase 1:

```
BST (Level-0 root)
 +-- SYN (depends: BST)
 |    +-- SEM (depends: SYN, BST)
 |    +-- DED (depends: SYN, BST)
 +-- CMP (depends: BST)
 +-- SET (depends: SYN, SEM, DED, BST)
 +-- Composition Patterns (depends: all of the above)
```

Within each domain chapter, order sections by the intra-domain dependency graph: a section defining item X comes before any section that depends on X.

### Outline Template

| Ch. | Title | Domain | Key Items | Est. Pages | Source Sections (Directive) |
|-----|-------|--------|-----------|------------|---------------------------|
| 0 | Metalanguage: Sets, Functions, Relations | BST | PRIM-BST001--016, DEF-BST001--005 | 15--20 | `sets-functions-relations/` (KEEP/CONDENSE) |
| 1 | Syntax | SYN | PRIM-SYN001--018, DEF-SYN001--011 | 20--25 | `first-order-logic/syntax/`, `propositional-logic/syntax/` (KEEP/MERGE) |
| 2 | Semantics | SEM | PRIM-SEM001--015, DEF-SEM001--019 | 25--30 | `first-order-logic/semantics/`, `propositional-logic/semantics/`, `model-theory/basics/` (KEEP/MERGE/CONDENSE) |
| 3 | Deduction | DED | PRIM-DED001--010, DEF-DED001--014 | 25--30 | `first-order-logic/proof-systems/`, `first-order-logic/natural-deduction/`, `first-order-logic/sequent-calculus/`, `first-order-logic/tableaux/` (KEEP/MERGE/CONDENSE) |
| 4 | Computation | CMP | PRIM-CMP001--012, DEF-CMP001--014 | 20--25 | `computability/`, `turing-machines/`, `lambda-calculus/` (KEEP/CONDENSE) |
| 5 | Set Theory (Formal) | SET | PRIM-SET001--003, AX-SET001--009, DEF-SET001--015 | 15--20 | `set-theory/` (KEEP/CONDENSE) |
| 6 | Metatheorems | CP-001--013 | All composition patterns | 30--40 | `first-order-logic/completeness/`, `first-order-logic/beyond/`, `incompleteness/`, `model-theory/interpolation/`, `model-theory/lindstrom/` (EXTRACT-PATTERN) |
| -- | Front Matter | -- | Preface, notation index, dependency diagram | 5--8 | (new) |
| -- | Back Matter | -- | Subject index, bibliography | 8--12 | `reference/` (KEEP/CONDENSE) |

**Math logic example**: The Completeness Theorem (CP-002) references items from SEM (PRIM-SEM010, DEF-SEM002), DED (DEF-DED001, DEF-DED002, THM-DED005), and BST (PRIM-BST016). Place it in Chapter 6 (Metatheorems), after Chapters 0--5 have defined all prerequisites. The Henkin construction proof appears in full here, not in Chapter 2 or Chapter 3.

**Organic chemistry example**: A chapter on "Thermodynamics vs. Kinetics of Reactions" references both the structure domain (bond energies) and the reactivity domain (activation energy). Place it after both prerequisite chapters, in a cross-domain results chapter.

### Estimated Totals

| Component | Pages |
|-----------|-------|
| Front matter | 5--8 |
| Chapters 0--5 | 120--150 |
| Chapter 6 (Metatheorems) | 30--40 |
| Back matter | 8--12 |
| **Total** | **163--210** |

Compare this against the source corpus size. A well-compressed lean text should be 30--50% of the original page count. If your estimate exceeds 50%, review your CONDENSE and CUT directives for additional compression opportunities. If it falls below 25%, verify that you have not over-deleted formal content.

---

## 8. Quality Gate 3 Checklist

Before proceeding to Phase 4, verify every item below. Mark each as PASS or FAIL. Any FAIL is a blocking defect -- resolve it before continuing.

| # | Check | PASS/FAIL |
|---|-------|-----------|
| 1 | Every source section has exactly one directive (no blanks, no "TBD") | |
| 2 | Every MERGE directive names the survivor section | |
| 3 | Every RELOCATE directive specifies target chapter and insertion point | |
| 4 | Every CUT directive includes a justification proving no formal content is lost | |
| 5 | Every EXTRACT-PATTERN directive references a valid CP-NNN ID | |
| 6 | Every taxonomy item (PRIM/DEF/AX/THM) from Phase 1 appears in at least one KEEP or MERGE-survivor section | |
| 7 | The notation concordance covers every symbol that has more than one variant in the source | |
| 8 | No overloaded symbol is left unresolved (all CONFLICT flags have a disambiguation) | |
| 9 | The cross-reference plan contains zero bare forward references (every forward reference is forward-declared) | |
| 10 | The lean outline follows the dependency DAG (no chapter references an item defined in a later chapter, except via forward declaration) | |
| 11 | Estimated lean text size is 30--50% of source corpus | |
| 12 | No REVIEW-NEEDED flags remain unresolved | |

**Scoring**: All 12 items must be PASS. If any item is FAIL, return to the relevant step and fix it. Re-run the full checklist after each fix -- a fix to one item can break another.

See [05-QUALITY-GATES.md](05-QUALITY-GATES.md) §1 (Gate 3) for the full rubric and audit procedure.

---

## Appendix: AI Prompt Block

Copy-paste the following prompt to an AI assistant to execute Phase 3 on a corpus. Replace the bracketed placeholders with your actual artifacts.

```
You are performing Phase 3 (COMPRESSION) of a knowledge compression pipeline.

INPUTS:
- Section map: [paste or attach Phase 2 section map]
- Coverage matrix: [paste or attach Phase 2 coverage matrix]
- Redundancy resolution: [paste or attach Phase 2 redundancy resolution]
- Domain specs: [paste or attach Phase 1 domain specs, or provide file paths]
- Item registry: [paste or attach the Primitive Registry from CONVENTIONS.md section 9]
- Dependency DAG: [paste or attach from CONVENTIONS.md section 10 or CROSS-DOMAIN-MAP.md section 2]
- Composition patterns: [paste or attach from CROSS-DOMAIN-MAP.md section 3]

TASK: Produce the four Phase 3 artifacts.

STEP 1 — PER-SECTION DIRECTIVES:
For each row in the section map, walk the triage decision tree:
  1. Does it introduce/prove a composition pattern? --> EXTRACT-PATTERN (cite CP-NNN).
  2. Is it purely pedagogical/historical/exercise-only? --> CUT (state justification).
  3. Was it flagged as redundant? --> If canonical: KEEP. If not: MERGE-INTO (cite survivor).
  4. Is it at the wrong dependency depth? --> RELOCATE (cite target chapter + insertion point).
  5. Is it on the critical path (>= 2 dependents)? --> KEEP.
  6. Otherwise --> CONDENSE.
Handle partial canonicity by issuing split directives.
Output a table: Source Section | Directive | Target | Items Affected | Justification.

STEP 2 — NOTATION CONCORDANCE:
Scan the source for every notation variant. For each variant group, choose canonical form using:
  1. Taxonomy precedent (from domain specs).
  2. Frequency in source.
  3. Standard reference (Enderton, Mendelson, etc.).
  4. Readability.
Flag overloaded symbols with CONFLICT and provide disambiguation.
Output a table: Concept | Canonical Form | Variants | Rationale.

STEP 3 — CROSS-REFERENCE PLAN:
For each KEEP/MERGE-survivor section, list every cross-domain reference.
Classify as backward or forward.
For every forward reference, write a one-sentence forward declaration.
Output a table: Source Section | References Item | Defined In | Direction | Resolution.

STEP 4 — LEAN OUTLINE:
Order chapters by the dependency DAG: BST -> SYN -> SEM / DED -> CMP -> SET -> Composition Patterns.
Within chapters, order by intra-domain dependency.
Estimate page counts. Verify total is 30-50% of source.
Output a table: Ch. | Title | Domain | Key Items | Est. Pages | Source Sections (Directive).

QUALITY GATE:
After producing all four artifacts, run the 12-item Quality Gate 3 checklist.
Report each item as PASS or FAIL. If any FAIL, fix it and re-run.

FORMAT: Use Markdown tables. Use taxonomy IDs (PRIM-SYN001, CP-002, etc.) throughout. Do not
introduce new notation or new IDs not in the registry.
```
