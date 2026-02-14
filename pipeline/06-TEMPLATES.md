# Templates

> **Reference** -- use alongside phases 1-4
> Referenced by: 01-TAXONOMY S4-5, 02-MAPPING S2, 03-COMPRESSION S4, 04-RECOMPOSITION S6

Previous: [05-QUALITY-GATES.md](05-QUALITY-GATES.md) | Next: [07-AI-COLLABORATION.md](07-AI-COLLABORATION.md)

---

Each template: (a) blank form, (b) logic example, (c) chemistry example, (d) validation rules.

## S1. Domain Specification Template

**(a) Blank form**

```
# DOMAIN-{CODE} v0.1
## 0. Sources & Assumptions
- SRC-{CODE}001: {Author, Title, edition, chapters}
- ASM-{CODE}001: {Assumption}. Justification: {why}
## 1. Domain Intent
- **Governing question**: {one question, ending with ?}
- **Scope**: {what is in scope}
- **Non-goals**: {out of scope, with owning domain}
- **Dissolution argument**: {>= 2 sentences on why this cannot merge into another domain}
## 2. Prerequisites
- DEP-{CODE}001: Requires {DOMAIN} for {imported PRIM/DEF IDs}
## 3. Primitive Notions
- PRIM-{CODE}001: **{Name}**
  - Description / Formal / Ownership: OWNS / Source / Referenced by / Fragment / Motivating example
## 4. Definitions
- DEF-{CODE}001: **{Name}**
  - Description / Formal / Depends / Ownership: OWNS / Source / Referenced by / Fragment / Motivating example
## 5. Axioms
- AX-{CODE}001: **{Name}** -- Statement / Description / Depends / Source / Normative: {MUST|SHOULD|MAY}
## 6. Extension Points
- EXT-{CODE}001: **{Name}** -- Type: {Additive|Replacement|Structural} / Description / Reserved range
```

**(b) Logic** -- DOMAIN-SYN: Governing question = "How are well-formed expressions constructed?" Scope = symbol manipulation prior to truth or meaning. PRIM-SYN001 **Symbol**: an element of a designated alphabet $\mathcal{A}$. Fragment: both. Example: in arithmetic, symbols include $0, S, +, <, =$.

**(c) Chemistry** -- DOMAIN-STR: Governing question = "How are molecular structures represented and classified?" Scope = connectivity, stereochemistry, functional groups. PRIM-STR001 **Covalent Bond**: a shared electron pair; formally an edge in molecular graph $G = (V, E)$. Example: the C-C bond in ethane.

**(d) Validation**

| Rule | Check |
|------|-------|
| Domain code | `^[A-Z]{3}$` |
| Governing question | Ends with `?` |
| Dissolution argument | >= 2 sentences |
| Every PRIM/DEF | 7 fields: Description, Formal, Ownership, Source, Referenced by, Fragment, Motivating example |
| ID format | `^(PRIM\|DEF\|AX\|EXT)-[A-Z]{3}\d{3}$` |
| No forward refs | Each DEF depends only on earlier PRIM/DEF |

---

## S2. Item Entry Template

**(a) Blank form**

```
- {TYPE}-{DOM}{NNN}: **{Concept Name}**
  - Description: {>= 1 sentence}
  - Formal: {LaTeX, e.g. $\forall x\, P(x)$}
  - Depends: {prerequisite IDs, or "none" for PRIMs}
  - Ownership: OWNS
  - Source: SRC-{CODE/GLB}NNN ({location})
  - Referenced by: {domain codes, or "---"}
  - Fragment: {PL | FOL | both}
  - Motivating example: {concrete instance}
```

Additional fields: AX/THM use **Statement** (replaces Formal); AX adds **Normative** (MUST/SHOULD/MAY); THM adds **Proof sketch**.

**(b) Logic** -- DEF-DED002: **Maximal Consistent Set**. $\Gamma$ is maximal consistent iff $\Gamma \nvdash \bot$ and for every $\varphi$, $\varphi \in \Gamma$ or $\neg\varphi \in \Gamma$. Depends: DEF-DED001, PRIM-DED006, PRIM-SYN013. Referenced by: SEM. Example: $\text{Th}(\mathfrak{N})$.

**(c) Chemistry** -- DEF-STR004: **Functional Group**. A subgraph $H \subseteq G$ matching a pattern from catalog $\mathcal{F}$. Depends: PRIM-STR001, PRIM-STR002. Referenced by: MECHANISM. Example: hydroxyl (-OH) in ethanol.

**(d) Validation**

| Rule | Check |
|------|-------|
| ID format | `^(PRIM\|DEF\|AX\|THM)-[A-Z]{3}\d{3}$` |
| DOM consistency | DOM in ID matches file's domain code |
| NNN sequencing | Sequential within each TYPE-DOM group |
| Description | Non-empty, contains a period |
| Formal | Contains `$...$` |
| Depends | Every listed ID exists in registry; no intra-domain forward refs |
| Fragment | One of `PL`, `FOL`, `both` |
| Cross-registry | ID appears in CONVENTIONS.md Primitive Registry |

---

## S3. Section Map Entry Template

**(a) Blank form**

```
### {source-path} --- {Short Title}
- **File**: {path to source file}
- **Domain**: {3-letter code}
- **Introduces**: {taxonomy IDs defined here}
- **References**: {taxonomy IDs used but defined elsewhere}
- **OL Formal Items**: {env label} -> {taxonomy ID} ({note})
- **Coverage**: {FULL | PARTIAL | MENTIONED}
- **Role**: {DEFINE | DISCUSS | PROVE | EXAMPLE}
- **Compression Signal**: {CORE-DEF | STEPPING-STONE | PEDAGOGICAL | REDUNDANT}
- **Ped. Prerequisites**: {prior source sections}
- **OL Cross-refs**: {internal cross-references}
- **Notes**: {observations for compression}
```

Coverage: **FULL** = canonical treatment, **PARTIAL** = one angle only, **MENTIONED** = referenced not treated.

**(b) Logic** -- fol/syn/fml: File = content/first-order-logic/syntax/formulas.tex. Domain SYN. Introduces PRIM-SYN011, PRIM-SYN012. Coverage FULL. Signal CORE-DEF. Notes: promote unique readability remark to lemma.

**(c) Chemistry** -- org/str/stereo: File = content/organic/structure/stereoisomers.tex. Domain STR. Introduces DEF-STR010 (enantiomer), DEF-STR011 (diastereomer). Coverage FULL. Signal CORE-DEF. Notes: drop Pasteur narrative.

**(d) Validation**

| Rule | Check |
|------|-------|
| Source path | Matches a real file in the corpus |
| Coverage | `FULL`, `PARTIAL`, or `MENTIONED` |
| Role | `DEFINE`, `DISCUSS`, `PROVE`, or `EXAMPLE` |
| Signal | `CORE-DEF`, `STEPPING-STONE`, `PEDAGOGICAL`, or `REDUNDANT` |
| No orphan items | Every taxonomy ID has >= 1 entry with Coverage = FULL |
| No double ownership | No ID has Coverage = FULL in more than one section |

---

## S4. Compression Directive Template

**Action vocabulary** (6 actions):

| Action | Meaning |
|--------|---------|
| **KEEP** | Retain essentially intact |
| **CONDENSE** | Preserve formal items; compress prose, cut redundant examples |
| **MERGE-INTO** | Fold this section's content into the canonical (survivor) section |
| **RELOCATE** | Move section to a different chapter to respect dependency order |
| **CUT** | Remove entirely (items covered elsewhere or out-of-scope) |
| **EXTRACT-PATTERN** | Pull cross-domain result into the composition-pattern chapter |

**(a) Blank form**

```
### {source-path} --- {Short Title}
- **Action**: {one of 6 above}
- **Lean Chapter**: CH-{CODE}
- **Lean Section**: {CODE.N: Title}
- **Rationale**: {why this action; which taxonomy items}
- **Content Directives**:
  - Formal items to preserve: {list}
  - Formal items to drop: {list + justification}
  - Prose: {preserve | compress | cut}
  - Examples: {keep best N of M, specify which | cut all}
  - Proofs: {preserve | sketch | cut}
```

**(b) Logic** -- fol/syn/fml: Action KEEP. CH-SYN, SYN.2: Formulas. Rationale: sole defining occurrence of PRIM-SYN011 + PRIM-SYN012. Preserve \begin{defn}[formula], \begin{defn}[atomic]. Examples: keep 1 of 3 (parse tree).

**(c) Chemistry** -- org/str/stereo: Action CONDENSE. CH-STR, STR.3: Stereochemistry. Rationale: sole occurrence of DEF-STR010 + DEF-STR011; cut Pasteur narrative. Examples: keep 1 of 4 ((R)/(S)-alanine).

**(d) Validation**

| Rule | Check |
|------|-------|
| Action | One of the 6 actions above |
| MERGE-INTO/RELOCATE targets | Target section exists in the section map |
| Lean Chapter | `^CH-[A-Z]{3}$` |
| Lean Section | `^[A-Z]{3}\.\d+:` |
| No item loss | Every FULL-coverage taxonomy ID in section map appears in one directive's "preserve" list |
| CUT justification | Rationale names alternate section or states out-of-scope |

---

## S5. Composition Pattern Template

**(a) Blank form**

```
### CP-{NNN}: **{Pattern Name}**
- **Domains**: {DOM1} x {DOM2} [x ...]
- **Statement**: {semi-formal, LaTeX math}
- **Natural language**: {>= 1 sentence}
- **Key dependencies**:
  - {DOM1}: {PRIM/DEF/AX IDs}
  - {DOM2}: {PRIM/DEF/AX IDs}
- **Proof sketch**: {outline or reference}
- **Source**: SRC-{CODE/GLB}NNN
- **Variant compatibility**: {which variants preserve this}
- **Significance**: {why it matters}
```

**(b) Logic** -- CP-002: **Completeness (Godel 1930)**. Domains: SEM x DED x BST. Statement: $\Gamma \vDash \varphi \Rightarrow \Gamma \vdash \varphi$. Dependencies: PRIM-SEM010, PRIM-SEM011, PRIM-DED006, DEF-DED002, PRIM-BST016. Proof sketch: Lindenbaum extension, term model construction, induction on complexity. Variant compatibility: classical FOL only; fails for full SOL.

**(c) Chemistry** -- CP-003: **Woodward-Hoffmann Rules**. Domains: ORBITAL x MECHANISM x THERMO. Statement: pericyclic reaction stereochemistry is determined by frontier MO symmetry. Dependencies: PRIM-ORB003 (HOMO), PRIM-ORB004 (LUMO), DEF-MEC012 (pericyclic reaction). Variant compatibility: all carbon-based pericyclic systems.

**(d) Validation**

| Rule | Check |
|------|-------|
| ID format | `^CP-\d{3}$` |
| Domains | >= 2 distinct domain codes |
| Key dependencies | Every ID exists in registry |
| Statement | Contains `$...$` (for formal projects) |
| Cross-domain | References items from >= 2 domains |

---

## S6. Audit Scorecard Templates

### S6a. Per-Chapter (8 dimensions, score 0-2 each)

```
## Audit: {CH-CODE} --- {Chapter Title}
| # | Dimension                          | Score | Evidence / Notes |
|---|------------------------------------|-------|------------------|
| 1 | Completeness (all items defined)   |   /2  |                  |
| 2 | Non-redundancy (no double defs)    |   /2  |                  |
| 3 | Dependency order (no forward refs) |   /2  |                  |
| 4 | Notation consistency               |   /2  |                  |
| 5 | Traceability (IDs cited)           |   /2  |                  |
| 6 | Example coverage (PRIMs + key DEFs)|   /2  |                  |
| 7 | Proof completeness                 |   /2  |                  |
| 8 | Cross-references correct           |   /2  |                  |
**Total: /16** -- Pass: >= 14, no zeros.
```

### S6b. Whole-Text Coherence (6 dimensions, score 0-2 each)

```
## Audit: Whole-Text Coherence
| # | Dimension                          | Score | Evidence / Notes |
|---|------------------------------------|-------|------------------|
| 1 | Global DAG acyclic                 |   /2  |                  |
| 2 | Item accounting (each in 1 chapter)|   /2  |                  |
| 3 | Notation concordance               |   /2  |                  |
| 4 | All CPs stated + proved/referenced |   /2  |                  |
| 5 | Index covers all items             |   /2  |                  |
| 6 | No orphan sections                 |   /2  |                  |
**Total: /12** -- Pass: >= 10, no zeros.
```

**(b) Logic** (per-chapter, CH-SYN): 15/16 PASS. All 18 PRIM-SYN + 11 DEF-SYN present. One notation issue: SYN.3 uses $Fv(\varphi)$ vs. concordance $\text{FV}(\varphi)$.

**(c) Chemistry** (whole-text): 11/12 PASS. DEF-MEC008 missing from CH-MEC. All 5 CPs stated. 142/142 items indexed.

**(d) Validation**

| Rule | Check |
|------|-------|
| Per-chapter scorecard | One per chapter, none skipped |
| Whole-text scorecard | Exactly one, after all chapters |
| Score range | 0, 1, or 2 only |
| Pass (chapter) | >= 14/16, no zeros |
| Pass (whole-text) | >= 10/12, no zeros |
| Evidence | Non-empty for any dimension < 2 |
| Remediation | Every 0 or 1 has a follow-up action |

---

## Quick-Reference: ID Regex Patterns

| Entity | Regex |
|--------|-------|
| Domain code | `^[A-Z]{3}$` |
| Item ID | `^(PRIM\|DEF\|AX\|THM)-[A-Z]{3}\d{3}$` |
| Composition pattern | `^CP-\d{3}$` |
| Source ref | `^SRC-(GLB\|[A-Z]{3})\d{3}$` |
| Assumption / Unknown | `^(ASM\|UNK)-(GLB\|[A-Z]{3})\d{3}$` |
| Dependency / Extension | `^(DEP\|EXT)-[A-Z]{3}\d{3}$` |
| Lean chapter | `^CH-[A-Z]{3}$` |
| Lean section | `^[A-Z]{3}\.\d+:` |
| Coverage | `^(FULL\|PARTIAL\|MENTIONED)$` |
| Compression action | `^(KEEP\|CONDENSE\|MERGE-INTO:.+\|RELOCATE:.+\|CUT\|EXTRACT-PATTERN:.+)$` |
| Fragment | `^(PL\|FOL\|both)$` |
