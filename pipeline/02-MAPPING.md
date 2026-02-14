# Phase 2: Mapping

> **Phase 2 of 4** | Prev: [01-TAXONOMY.md](01-TAXONOMY.md) | Next: [03-COMPRESSION.md](03-COMPRESSION.md)
> Templates: [06-TEMPLATES.md](06-TEMPLATES.md) §S3 | Quality gate: [05-QUALITY-GATES.md](05-QUALITY-GATES.md) §1 (Gate 2)

---

## Goal

Map every section of the source corpus onto the taxonomy built in Phase 1. When this phase is complete, every taxonomy item has a home in the source, every source section is accounted for, and all redundancies are resolved.

**Input**: Phase 1 deliverables (domain specs, item registry, dependency DAG) + the source corpus.

**Output**: Four artifacts:
1. **Section map** -- per-section records linking source sections to taxonomy items
2. **Coverage matrix** -- every taxonomy item mapped to its defining section(s)
3. **Redundancy resolution** -- for each item defined in 2+ sections, a canonical section is designated
4. **Gap analysis** -- items with no source coverage, and source sections with no taxonomy match

**Exit criterion**: Pass Quality Gate 2 (see [05-QUALITY-GATES.md](05-QUALITY-GATES.md) §1, Gate 2). Every taxonomy item is either FULL, IMPLICIT, EXTENSION-ONLY, or documented as genuinely absent. Every redundancy has a canonical section. Backtracking to Phase 1, if triggered, is complete.

---

## Step 1: Build the Section Inventory

Walk the source corpus and produce a flat list of every section (chapter, subchapter, named block). For each section, record:

| Field | Description |
|-------|-------------|
| **Section ID** | A short stable slug (e.g., `fol/syn/frm`, `sfr/set/bas`) |
| **File path** | Path to the source file |
| **Title** | Human-readable section title |
| **Topic area** | The top-level grouping (e.g., `first-order-logic`, `sets-functions-relations`) |

Do not classify sections yet. The inventory is a neutral census.

**Logic example**: Scanning the OpenLogic `content/` directory yields sections like `fol/syn/frm` (first-order logic, syntax, formation rules) and `inc/inp/1in` (incompleteness, incompleteness-provability, first incompleteness theorem).

**Chemistry example**: Scanning an organic chemistry textbook yields sections like `alkanes/nomenclature/iupac` (alkanes, nomenclature, IUPAC rules) and `stereochem/config/rs` (stereochemistry, configuration, R/S assignment).

**Procedure**:

1. List every source file that contains definitions, theorems, or substantive exposition.
2. Assign a section ID using the convention `topic/chapter/section`.
3. Skip purely administrative files (front matter, bibliography, formatting templates).
4. Record the count. You will use it in Step 3 to verify completeness.

---

## Step 2: Per-Section Tagging

For each section in the inventory, read the section and fill in the tagging record. Use the template in [06-TEMPLATES.md](06-TEMPLATES.md) SS3.

### 2.1 Tagging Record Fields

| Field | Description |
|-------|-------------|
| **Domain** | Primary taxonomy domain (e.g., SYN, SEM, DED) |
| **Introduces** | Taxonomy item IDs that this section defines for the first time |
| **References** | Taxonomy item IDs that this section uses but does not define |
| **OL Formal Items** | Every `\begin{defn}`, `\begin{thm}`, `\begin{prop}`, or equivalent, mapped to a taxonomy ID or marked OL-ONLY |
| **Role** | DEFINE, PROVE, DISCUSS, or APPLY |
| **Compression signal** | CORE-DEF, CORE-THM, STEPPING-STONE, PEDAGOGICAL, or TANGENTIAL |
| **Ped. prerequisites** | Section IDs that must be read before this section |
| **OL cross-refs** | Section IDs that this section explicitly references |
| **Notes** | Free-form annotation |

### 2.2 Coverage Level Decision Tree

For each taxonomy item encountered in a section, assign a coverage level:

```
Is the item given a formal definition or statement in this section?
  YES --> Does the definition match the taxonomy's formal statement?
    YES --> FULL
    NO  --> PARTIAL (note the discrepancy)
  NO  --> Is the item used without being defined?
    YES --> Is it clearly identifiable from context?
      YES --> IMPLICIT
      NO  --> ABSENT (flag for gap analysis)
    NO  --> ABSENT
```

**Logic example**: Section `fol/syn/frm` contains `\begin{defn}[Formation rules for formulas]` that matches PRIM-SYN012 (Formula). Coverage level: FULL.

**Chemistry example**: A section on E2 elimination reactions uses "steric hindrance" without defining it. The term is identifiable from context. Coverage level: IMPLICIT.

### 2.3 Synonym Detection

Source corpora often use different names for the same concept. Before creating a new taxonomy item, check for synonyms:

1. **Check the item registry** for alternate names listed in the `Also known as` field.
2. **Search the corpus** for the candidate name. If it appears in a section already tagged to an existing taxonomy item, it is a synonym, not a new item.
3. **Check notation variants**. The same concept may appear as $\Gamma \vDash \varphi$ in one chapter and $\Sigma \models \varphi$ in another.

**Logic example**: "Semantic entailment," "logical consequence," and "$\Gamma \vDash \varphi$" all refer to PRIM-SEM010. Do not create a second item.

**Chemistry example**: "Markovnikov's rule" and "Markownikoff's rule" are spelling variants of the same concept. Tag both occurrences to the same item.

If a term genuinely has no match in the registry, flag it as a **gap candidate** for Step 5.

### 2.4 Tagging Discipline

- Tag every formal item (`\begin{defn}`, `\begin{thm}`, etc.) in the section to exactly one taxonomy ID or mark it OL-ONLY.
- Mark an item OL-ONLY if it is a pedagogical stepping stone, a worked example, or a historical aside that does not correspond to any taxonomy item.
- If a section introduces items from multiple domains, list all domains in the Domain field, separated by commas.
- If you are uncertain which taxonomy item a formal block maps to, write `UNCERTAIN: [candidate IDs]` and resolve in Step 5.

---

## Step 3: Build the Coverage Matrix

Invert the section map. For each taxonomy item, list every section that introduces or references it.

| Column | Description |
|--------|-------------|
| **ID** | Taxonomy item ID |
| **Concept** | Human-readable name |
| **Defining section(s)** | Section IDs where the item is introduced |
| **Coverage** | FULL, IMPLICIT, ABSENT, EXTENSION-ONLY, or DEFERRED |
| **Redundancy** | None, EXPECTED, or COMPRESSION-TARGET |

### 3.1 Filling the Matrix

1. Initialize one row per taxonomy item (pull from the Phase 1 item registry).
2. Walk the section map. For each section's `Introduces` field, add that section to the corresponding row's `Defining section(s)`.
3. Set Coverage to FULL if at least one defining section provides a complete definition. Set to IMPLICIT if the item is used but never formally defined. Set to ABSENT if no section mentions it.
4. Set Redundancy to COMPRESSION-TARGET if the item is introduced in 2+ sections and the redundancy is not pedagogically justified. Set to EXPECTED if the redundancy is justified (e.g., PL/FOL parallel treatments, proof-system variants).

### 3.2 Backtracking Trigger

After filling the matrix, count the items with Coverage = ABSENT or UNCERTAIN.

```
ABSENT + UNCERTAIN count > 20% of total taxonomy items?
  YES --> STOP. Return to Phase 1.
         Your taxonomy is misaligned with the source corpus.
         Revise domain boundaries, add missing domains, or
         remove items that the corpus genuinely does not cover.
         Re-enter Phase 2 from Step 1 after revision.
  NO  --> Continue to Step 4.
```

This threshold prevents you from pressing forward with a taxonomy that does not match the source. Backtracking is normal. The pipeline is iterative at the phase level.

---

## Step 4: Redundancy Resolution

For every taxonomy item with 2+ defining sections, designate a **canonical section** and classify the remaining sections.

### 4.1 Canonical Section Decision Tree

```
How many sections define this item?
  1 --> No redundancy. Mark "None" and move on.
  2+ --> Are the sections in different proof systems or logic fragments
         (e.g., PL vs. FOL, Hilbert vs. Natural Deduction)?
    YES --> Mark redundancy as EXPECTED. Keep all sections.
            In Phase 3, compress each into its proof-system chapter.
    NO  --> Do the sections cover genuinely different aspects of the item?
      YES --> Designate the section with the formal definition as canonical.
              Mark the others as SUPPLEMENTARY.
      NO  --> Designate the most complete section as canonical.
              Mark the others as COMPRESSION-TARGET.
              In Phase 3, merge their content into the canonical section.
```

**Logic example**: CP-001 (Soundness) is proved in 4 sections -- one per proof system (Hilbert, natural deduction, sequent calculus, tableaux). Redundancy: EXPECTED. Each section is canonical for its proof system.

**Chemistry example**: "SN2 mechanism" appears in both the "nucleophilic substitution" chapter and the "stereochemistry" chapter. The nucleophilic substitution chapter gives the formal mechanism. Designate it as canonical. The stereochemistry chapter discusses the stereochemical implications -- mark it SUPPLEMENTARY.

### 4.2 Recording the Resolution

For each redundant item, record:

| Field | Description |
|-------|-------------|
| **Item ID** | Taxonomy ID |
| **Canonical section** | The authoritative section |
| **Other sections** | List with classification (EXPECTED, SUPPLEMENTARY, COMPRESSION-TARGET) |
| **Recommendation** | Action for Phase 3 (keep, merge, compress, drop) |

---

## Step 5: Gap Analysis

Identify and classify every gap between the taxonomy and the source corpus.

### 5.1 Taxonomy Items with No Source Coverage

Pull every row from the coverage matrix with Coverage = ABSENT. For each, determine:

```
Is this item needed for any composition pattern or dependency chain?
  YES --> Mark as GENUINELY-ABSENT. The lean text must define it
          even though the source does not. Note this for Phase 4.
  NO  --> Is this item an extension-only concept
          (modal, intuitionistic, higher-order)?
    YES --> Mark as EXTENSION-ONLY. Exclude from the core lean text.
    NO  --> Mark as OUT-OF-SCOPE. Remove from the item registry
            or move to a supplement.
```

**Logic example**: DEF-DED004 (Conservative Extension) has no coverage in the OpenLogic corpus. It is needed in the dependency chain for composition patterns involving theory extensions. Classification: GENUINELY-ABSENT. The lean text must define it independently.

**Chemistry example**: "Photochemical Woodward-Hoffmann rules" have no coverage in a textbook focused on introductory organic chemistry. The item is not needed for any core reaction mechanism. Classification: OUT-OF-SCOPE.

### 5.2 Source Sections with No Taxonomy Match

Pull every section from the inventory with no `Introduces` entries and no `References` entries. These are **orphan sections**. For each, determine:

- Is it pedagogical or historical? Mark as NON-DEFINITIONAL.
- Does it introduce a concept the taxonomy missed? Flag as **gap candidate** and evaluate whether to add a new taxonomy item (backtrack to Phase 1 if many candidates accumulate).
- Is it purely administrative? Remove from the section map.

### 5.3 Failure Mode: Concept Explosion

If the gap analysis produces more than 5 gap candidates that require new taxonomy items, do not add them ad hoc. Instead:

1. Collect all gap candidates into a resolution document.
2. For each candidate, attempt to assign it to an existing domain using the boundary principles from Phase 1.
3. If the candidate decomposes into existing primitives, subsume it under an existing item or document it as a composition pattern.
4. If the candidate is genuinely new, add it to the taxonomy with a proper ID and run the self-audit checklist on the affected domain spec.
5. If more than 20% of candidates resist assignment, return to Phase 1 and revise the domain structure.

This is the "Phase 2.5" resolution pattern. It preserves the closed domain catalog while allowing the item catalog to grow.

---

## Quality Gate 2

Pass all items before proceeding to Phase 3. See [05-QUALITY-GATES.md](05-QUALITY-GATES.md) §1, Gate 2 for the full rubric.

| Check | Criterion | Pass condition |
|-------|-----------|----------------|
| QG2-1 | Coverage completeness | Every taxonomy item has Coverage != ABSENT, or is documented as GENUINELY-ABSENT, EXTENSION-ONLY, or OUT-OF-SCOPE |
| QG2-2 | No orphan sections | Every section in the inventory has at least one `Introduces` or `References` entry, or is marked NON-DEFINITIONAL |
| QG2-3 | Redundancy resolution | Every item with 2+ defining sections has a canonical section designated |
| QG2-4 | Formal item classification | Every `\begin{defn}`, `\begin{thm}`, etc. in the corpus is tagged to a taxonomy ID or marked OL-ONLY |
| QG2-5 | Backtracking threshold | ABSENT + UNCERTAIN count <= 20% of total taxonomy items |
| QG2-6 | Gap resolution | All gap candidates are resolved (assigned, subsumed, or documented) |
| QG2-7 | Reverse index consistency | Every section listed in the coverage matrix maps back to a valid section in the section map |

If any check fails, resolve the failure before proceeding. Backtrack to Phase 1 if QG2-5 fails.

---

## AI Prompt Block

Copy and paste the following prompt to have an AI assistant execute Phase 2 on your corpus.

```
You are performing Phase 2 (Mapping) of a knowledge compression pipeline.

INPUT:
- The Phase 1 taxonomy: domain specs, item registry (with IDs for every
  PRIM, DEF, AX, THM, and CP), and the dependency DAG.
- The source corpus in [FORMAT], consisting of [N] sections organized
  into [M] topic areas.

TASK:
1. SECTION INVENTORY: Walk every source section. For each, record:
   section ID, file path, title, and topic area. Do not classify yet.

2. PER-SECTION TAGGING: For each section, read it and record:
   - Domain (primary taxonomy domain)
   - Introduces (taxonomy IDs this section defines)
   - References (taxonomy IDs this section uses but does not define)
   - Formal items (every definition/theorem block, mapped to a taxonomy
     ID or marked SOURCE-ONLY)
   - Role (DEFINE / PROVE / DISCUSS / APPLY)
   - Compression signal (CORE-DEF / CORE-THM / STEPPING-STONE /
     PEDAGOGICAL / TANGENTIAL)
   Use the synonym detection procedure: before creating a new ID,
   search the registry for alternate names and notation variants.

3. COVERAGE MATRIX: Invert the section map. For each taxonomy item,
   list its defining section(s), coverage level (FULL / IMPLICIT /
   ABSENT), and redundancy status (None / EXPECTED / COMPRESSION-TARGET).

4. REDUNDANCY RESOLUTION: For every item with 2+ defining sections,
   designate a canonical section using the decision tree:
   - Different proof systems or fragments -> EXPECTED (keep all)
   - Different aspects -> canonical = formal definition section
   - True duplicates -> canonical = most complete; others = COMPRESSION-TARGET

5. GAP ANALYSIS: Identify taxonomy items with no source coverage
   (GENUINELY-ABSENT, EXTENSION-ONLY, or OUT-OF-SCOPE) and source
   sections with no taxonomy match (NON-DEFINITIONAL or gap candidate).

6. QUALITY GATE 2: Verify all 7 checks pass. Report any failures.

OUTPUT FORMAT:
- Section map (one record per section)
- Coverage matrix (one row per taxonomy item)
- Redundancy resolution table
- Gap analysis (absent items + orphan sections)
- Quality gate 2 results (pass/fail per check)

CONSTRAINTS:
- Do NOT invent new taxonomy domains. The domain catalog is closed.
- Do NOT skip sections. Every section must appear in the section map.
- If ABSENT + UNCERTAIN > 20% of taxonomy items, STOP and report.
  The taxonomy needs revision before mapping can continue.
- Flag any concept that appears to need a new taxonomy item as a
  gap candidate. Do not silently add IDs.
```
