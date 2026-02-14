# Quality Gates & Audit Rubrics

> **📍 Use between and after phases**
> Prev: [04-RECOMPOSITION.md](04-RECOMPOSITION.md) | Next: [06-TEMPLATES.md](06-TEMPLATES.md) | Templates: [06-TEMPLATES.md](06-TEMPLATES.md) §S6

---

## 1. Phase-End Quality Gates

Every phase ends with a mandatory quality gate. Do not advance to the next phase until the gate passes. If a gate fails, follow the recovery protocol below.

### 1.1 Gate Summary

| Gate | Phase | Pass Criterion | Backtracking Trigger |
|------|-------|---------------|---------------------|
| G1 — Taxonomy | Phase 1 | Every item has a unique ID; dependency DAG is acyclic; every PRIM is truly primitive (not definable from others); self-audit checklist passes 12/12 | >15% of items fail the self-audit checklist, or a cycle exists in the dependency DAG |
| G2 — Mapping | Phase 2 | Every source section maps to at least one taxonomy item; coverage matrix has no uncovered items (unless explicitly marked out-of-scope with justification); every redundancy is resolved | >20% of source sections do not map cleanly to any taxonomy item |
| G3 — Compression | Phase 3 | Every section has a compression directive; notation concordance is complete; lean outline accounts for every item in the taxonomy; no item lost between Phase 2 and Phase 3 | >10% of items lack directives, or notation concordance has unresolved conflicts |
| G4 — Recomposition | Phase 4 | Lean text compiles without errors; no forward references; structural audit ≥24/30; coherence audit ≥14/18; prose audit ≥18/24 | Any audit dimension scores 0, or total score falls below threshold on any rubric |

### 1.2 Recovery Protocol Decision Tree

```
Gate fails
 ├─ Severity: MINOR (1–2 dimensions below threshold, no structural issues)
 │   └─ Fix in place: patch the failing dimensions, re-run the gate
 │
 ├─ Severity: MODERATE (3+ dimensions below threshold, or one dimension scores 0)
 │   └─ Partial backtrack: return to the failing phase's midpoint,
 │      revise affected artifacts, re-run the gate
 │
 └─ Severity: SEVERE (systematic failure, >20% of items affected)
     └─ Full backtrack: return to the PREVIOUS phase,
        revise foundational artifacts, cascade forward, re-run all subsequent gates
```

Record every backtrack in a `BACKTRACK-LOG.md` file with: date, gate, severity, root cause, fix applied, and re-run result.

---

## 2. Structural Audit Rubric

Use this rubric after Phase 4 (and optionally after Phase 3 as a dry run). Score each dimension 0--3.

**Pass threshold:** Every dimension ≥2 AND total ≥24/30.

| # | Dimension | 0 — Absent | 1 — Deficient | 2 — Adequate | 3 — Exemplary |
|---|-----------|-----------|--------------|-------------|--------------|
| S1 | **ID Coverage** | >10% of items lack IDs | 5–10% lack IDs | <5% lack IDs; all PRIMs and DEFs have IDs | 100% ID coverage; IDs follow naming convention exactly |
| S2 | **DAG Acyclicity** | Cycles present in dependency graph | Suspected cycles not verified | DAG verified acyclic by manual inspection | DAG verified acyclic by automated tool; visualization included |
| S3 | **Single Ownership** | Multiple items have duplicate owners | 3+ ownership conflicts unresolved | ≤2 minor ownership ambiguities documented | Zero ownership conflicts; every item has exactly one owner |
| S4 | **Forward References** | >5 forward references in lean text | 3–5 forward references | 1–2 forward references with justification | Zero forward references; strict dependency ordering throughout |
| S5 | **Cross-Reference Integrity** | >10% of cross-refs are broken or point to wrong targets | 5–10% broken | <5% broken; all critical paths verified | 100% cross-refs validated; automated link checker passes |
| S6 | **Notation Consistency** | >5 notation conflicts across chapters | 3–5 conflicts | 1–2 minor variants documented in concordance | Single canonical notation used everywhere; concordance complete |
| S7 | **Fragment Coherence** | PL fragment not extractable as self-contained sub-taxonomy | PL fragment extractable but missing items | PL fragment self-coherent with minor gaps documented | PL and FOL fragments both fully self-coherent and tested |
| S8 | **Extension Points** | No extension points documented | Extension points listed but incomplete | Extension points cover additive, replacement, structural types | Extension points tested with at least one non-classical logic variant |
| S9 | **Completeness vs. Source** | >10% of source concepts missing from lean text | 5–10% missing | <5% missing; all gaps justified as out-of-scope | 100% coverage; every source concept mapped and accounted for |
| S10 | **Compilation** | Lean text does not compile (LaTeX errors or broken Markdown) | Compiles with warnings | Compiles cleanly with no warnings | Compiles cleanly; CI pipeline validates on every commit |

### Scoring Procedure

1. Run the automated checks in §5 first to populate S2, S5, S10.
2. Score S1, S3, S4, S6 by manual inspection of the lean text and taxonomy artifacts.
3. Score S7, S8 by attempting to extract the PL fragment and instantiate one extension.
4. Score S9 by comparing the coverage matrix (Phase 2) against the lean text table of contents.
5. Sum the scores. If total < 24 or any dimension < 2, the structural audit fails.

---

## 3. Coherence Audit Rubric

Use this rubric to verify that the lean text is internally consistent — that the pieces fit together as a unified whole.

**Pass threshold:** Every dimension ≥2 AND total ≥14/18.

| # | Dimension | What It Measures | How to Check | 0 | 1 | 2 | 3 |
|---|-----------|-----------------|-------------|---|---|---|---|
| C1 | **Dependency Ordering** | Every concept appears after all its prerequisites | Trace 10 random DEFs back to their PRIMs; verify each prerequisite appears earlier in the text | Prerequisites appear after dependents | 3+ ordering violations found | ≤2 minor violations | Zero violations in full trace |
| C2 | **Definition-Use Consistency** | Every term is used exactly as defined — no silent redefinition | Search for 10 key terms; compare usage in later chapters against the canonical definition | Terms used inconsistently in >3 places | 2–3 inconsistencies | ≤1 minor inconsistency | Every usage matches the definition exactly |
| C3 | **Cross-Domain Handoffs** | When a concept crosses domain boundaries, the handoff is explicit and correct | Check all CP (composition pattern) entries; verify both domains' items are correctly cited | Handoffs missing or incorrect for >3 CPs | 2–3 CPs with unclear handoffs | ≤1 minor ambiguity | All CPs explicitly cite both domains' items with correct IDs |
| C4 | **Level Separation** | Level-0 (BST) and Level-1 (SET) are never conflated | Search for "set" in all domains; verify each usage is tagged as BST or SET | Level-0 and Level-1 conflated in >3 places | 2–3 conflations | ≤1 minor ambiguity | Clean separation throughout; every occurrence tagged |
| C5 | **Notation Stability** | The same symbol means the same thing everywhere | Pick 10 symbols (e.g., $\vDash$, $\vdash$, $\mathfrak{A}$); verify consistent meaning across chapters | >3 symbols used with different meanings | 2–3 symbols ambiguous | ≤1 symbol with minor variant | All symbols univocal throughout |
| C6 | **Theorem Traceability** | Every theorem can be traced to its axioms and primitives | Pick 5 theorems; trace each back to axioms | >2 theorems cannot be traced | 1–2 theorems with incomplete traces | All theorems traceable with minor gaps in proof sketches | All theorems fully traceable with complete dependency chains |

### Checking Procedure

1. Select the sample items (10 DEFs, 10 terms, all CPs, 10 symbols, 5 theorems) before starting. Use stratified random sampling: pick at least one from each domain.
2. Perform each check independently. Record findings in a checklist.
3. Score each dimension. If total < 14 or any dimension < 2, the coherence audit fails.
4. Attach the completed checklist to the audit report.

---

## 4. Prose Audit Rubric

Use this rubric to evaluate the quality of the recomposed lean text as written exposition. Score each dimension 0--3.

**Pass threshold:** Every dimension ≥2 AND total ≥18/24.

The eight dimensions are coded AC, PR, EX, MO, FL, DN, AL, NO.

| # | Code | Dimension | 0 — Absent | 1 — Deficient | 2 — Adequate | 3 — Exemplary |
|---|------|-----------|-----------|--------------|-------------|--------------|
| P1 | **AC** | **Accuracy** | Formal errors present (wrong definitions, incorrect theorem statements) | 2+ minor inaccuracies (e.g., missing side conditions) | ≤1 minor inaccuracy | Zero errors; every formal statement verified against sources |
| P2 | **PR** | **Precision** | Ambiguous language in >5 places (undefined terms, vague quantifiers) | 3–5 ambiguous passages | 1–2 minor ambiguities | Every statement is unambiguous; quantifiers explicit; no hedging without justification |
| P3 | **EX** | **Examples** | No motivating examples for PRIMs or key DEFs | <50% of PRIMs have examples | ≥80% of PRIMs have examples; key DEFs illustrated | Every PRIM and key DEF has ≥1 concrete example; examples build on each other |
| P4 | **MO** | **Motivation** | No explanation of why concepts matter; definitions appear unmotivated | Sporadic motivation (some chapters lack "why this matters" framing) | Most chapters open with motivation; key definitions contextualized | Every chapter opens with a motivating problem or question; the reader always knows why the next concept is needed |
| P5 | **FL** | **Flow** | Text reads as a list of definitions with no connecting prose | Transitions between sections are mechanical ("Next, we define...") | Sections connect logically; transitions indicate dependency relationships | Narrative flows naturally; each section builds on the previous one; the reader never wonders "why am I reading this now?" |
| P6 | **DN** | **Density** | Text is either impenetrable (no prose, only symbols) or bloated (5 pages for one definition) | Uneven density: some sections too dense, others too sparse | Consistent density; each concept gets proportional space | Optimal density: formal content and prose explanation balanced throughout; a reader with one semester of logic can follow without external references |
| P7 | **AL** | **Accessibility** | Requires expert knowledge to parse; no concessions to non-specialists | Accessible to specialists only; jargon used without introduction | Accessible to advanced undergraduates with effort | Accessible to anyone with one semester of logic; difficult passages have explicit "intuition" paragraphs |
| P8 | **NO** | **Notation Introduction** | Symbols used before being introduced | 3+ symbols used before introduction | ≤2 symbols used slightly before formal introduction (with forward note) | Every symbol introduced before first use; notation index cross-referenced |

### Scoring Procedure

1. Read the lean text cover to cover (or assign sections to multiple reviewers).
2. Score each dimension independently. Record specific passages that justify scores below 3.
3. Sum the scores. If total < 18 or any dimension < 2, the prose audit fails.
4. For each dimension scoring below 2, fill in the remediation template below.

### Remediation Template

For each failing dimension, record:

```
Dimension:  [code and name, e.g., "FL — Flow"]
Score:      [0 or 1]
Evidence:   [list specific sections/passages where the problem occurs]
Root cause: [why this dimension failed — e.g., "chapters written independently without transition planning"]
Fix plan:   [concrete steps to bring the score to ≥2]
Owner:      [person responsible]
Deadline:   [date]
```

---

## 5. Verification Automation

Run these checks before every quality gate. They automate portions of the structural audit (S2, S5, S10) and catch mechanical errors early.

### 5.1 LaTeX Compilation Check

Verify that the lean text compiles without errors or warnings.

```bash
# Full compilation (run twice for cross-references)
pdflatex -interaction=nonstopmode -halt-on-error lean-text.tex \
  && pdflatex -interaction=nonstopmode -halt-on-error lean-text.tex

# Check for warnings (undefined references, multiply-defined labels)
pdflatex -interaction=nonstopmode lean-text.tex 2>&1 \
  | grep -E "Warning|Undefined|multiply"
```

### 5.2 Markdown Link Validation

Verify that all internal links in pipeline and taxonomy Markdown files resolve.

```bash
# Find all markdown links and check targets exist
for f in pipeline/*.md taxonomy/*.md; do
  grep -oP '\[.*?\]\(\K[^)]+' "$f" | while read -r link; do
    # Skip external URLs
    if echo "$link" | grep -qE '^https?://'; then continue; fi
    # Resolve relative to file's directory
    dir=$(dirname "$f")
    target="$dir/$link"
    # Strip anchor
    target=$(echo "$target" | sed 's/#.*//')
    if [ ! -f "$target" ] && [ ! -d "$target" ]; then
      echo "BROKEN LINK in $f: $link"
    fi
  done
done
```

### 5.3 ID Uniqueness Check

Verify that every traceability ID is unique across all taxonomy files.

```bash
# Extract all IDs matching the pattern TYPE-DOMAINCODE###
grep -rohP '(PRIM|DEF|AX|THM|CP)-[A-Z]{2,3}\d{3}' taxonomy/*.md \
  | sort | uniq -d
# Output should be empty. Any output indicates duplicate IDs.
```

### 5.4 Dependency Cycle Detection

Verify that the dependency DAG is acyclic. Extract edges and check for cycles.

```bash
# Extract dependency edges (item → dependency)
grep -rP 'Depends:.*?(PRIM|DEF|AX|THM)-[A-Z]{2,3}\d{3}' taxonomy/*.md \
  | sed -E 's/.*((PRIM|DEF|AX|THM)-[A-Z]{2,3}[0-9]{3}).*Depends:.*((PRIM|DEF|AX|THM)-[A-Z]{2,3}[0-9]{3})/\1 \3/' \
  > /tmp/dep-edges.txt

# Use tsort to detect cycles (tsort exits nonzero if cycle found)
tsort /tmp/dep-edges.txt > /dev/null 2>&1
if [ $? -ne 0 ]; then
  echo "CYCLE DETECTED in dependency graph:"
  tsort /tmp/dep-edges.txt 2>&1 | head -20
else
  echo "DAG is acyclic."
fi
```

### 5.5 Cross-Reference Integrity Check

Verify that every cross-domain reference points to an ID that exists.

```bash
# Collect all defined IDs
grep -rohP '(PRIM|DEF|AX|THM|CP)-[A-Z]{2,3}\d{3}' taxonomy/*.md \
  | sort -u > /tmp/defined-ids.txt

# Collect all referenced IDs (in Depends, Imports, cross-refs)
grep -rohP '(PRIM|DEF|AX|THM|CP)-[A-Z]{2,3}\d{3}' taxonomy/*.md pipeline/*.md \
  | sort -u > /tmp/referenced-ids.txt

# Find references to undefined IDs
comm -23 /tmp/referenced-ids.txt /tmp/defined-ids.txt
# Output should be empty. Any output indicates dangling references.
```

### 5.6 Forward Reference Detection

Check that the lean text never references a concept before it is defined.

```bash
# Extract ordered list of first-definition lines and first-usage lines per ID
# Compare: if any ID's first usage < first definition, flag it
grep -nP '(PRIM|DEF|AX|THM)-[A-Z]{2,3}\d{3}' taxonomy/phase4/*.tex \
  | awk -F: '{print $2, $1, $3}' \
  | sort -k1,1 -k2,2n \
  | awk '{
      if (!seen[$1]) { seen[$1]=$2; type[$1]="first-use" }
    }
    /\\(def|prim|axiom)/ { def[$1]=$2 }
    END {
      for (id in seen) {
        if (def[id] && seen[id] < def[id])
          print "FORWARD REF: " id " used at line " seen[id] " but defined at line " def[id]
      }
    }'
```

---

## 6. Failure Remediation Workflow

When any audit fails, follow this decision tree to determine the correct response.

### 6.1 Decision Tree

```
Audit fails
 │
 ├─ Q1: Is the failure in compilation/mechanical checks only?
 │   ├─ YES → Fix mechanical errors (broken links, LaTeX errors, duplicate IDs)
 │   │         Re-run §5 automated checks. If pass → re-score rubric. Done.
 │   └─ NO  → Continue to Q2.
 │
 ├─ Q2: Is the failure in ≤2 dimensions, all scoring 1 (not 0)?
 │   ├─ YES → MINOR severity. Fix in place:
 │   │         1. Identify specific passages/items causing the low score.
 │   │         2. Revise those passages.
 │   │         3. Re-run only the failing rubric. If pass → Done.
 │   └─ NO  → Continue to Q3.
 │
 ├─ Q3: Is any dimension scoring 0, OR are ≥3 dimensions below threshold?
 │   ├─ YES, but root cause is localized (one chapter, one domain) →
 │   │   MODERATE severity. Partial backtrack:
 │   │         1. Identify the root cause chapter/domain.
 │   │         2. Return to that chapter's compression directive (Phase 3).
 │   │         3. Revise the directive and recompose the chapter.
 │   │         4. Re-run all three rubrics on the revised text. If pass → Done.
 │   │
 │   └─ YES, and root cause is systemic (affects >20% of items) →
 │       SEVERE severity. Full backtrack:
 │         1. Identify the originating phase (usually Phase 1 or Phase 2).
 │         2. Return to that phase and revise foundational artifacts.
 │         3. Cascade changes forward through all subsequent phases.
 │         4. Re-run all quality gates from the revised phase onward.
 │
 └─ Q4: Have you backtracked to the same phase >2 times?
     ├─ YES → Escalate. The project needs a design review.
     │         Possible causes: scope too broad, domain boundaries wrong,
     │         source material fundamentally incompatible with the pipeline.
     │         Convene a review session before further work.
     └─ NO  → Continue with the prescribed backtrack.
```

### 6.2 Remediation Log Format

Record every remediation in `BACKTRACK-LOG.md`:

```
## Remediation [N]

- **Date:** YYYY-MM-DD
- **Gate/Rubric:** [G1/G2/G3/G4 + Structural/Coherence/Prose]
- **Severity:** [MINOR / MODERATE / SEVERE]
- **Failing dimensions:** [list with scores]
- **Root cause:** [1–2 sentence description]
- **Action taken:** [what was fixed and where]
- **Backtrack target:** [phase and artifact, or "none — fixed in place"]
- **Re-run result:** [PASS / FAIL — if FAIL, link to next remediation entry]
```

### 6.3 Escalation Criteria

Escalate to a full project review if any of the following hold:

- The same gate has failed 3 times despite remediation.
- A SEVERE backtrack reaches Phase 1 from Phase 4.
- Two different rubrics fail simultaneously with overlapping root causes.
- The remediation log exceeds 10 entries for a single phase.

---

## Appendix: Copy-Paste AI Audit Prompt

Use the following prompt to instruct an AI assistant to perform all three audits on a completed lean text. Paste it directly into your AI conversation.

```
You are auditing a lean text produced by a knowledge compression pipeline.
Perform three audits and report scores.

INPUT: The lean text (attached or pasted below), plus the taxonomy files
(CONVENTIONS.md, DOMAIN-*.md, CROSS-DOMAIN-MAP.md).

AUDIT 1 — STRUCTURAL (10 dimensions, each 0–3):
S1  ID Coverage: What percentage of items have unique IDs?
S2  DAG Acyclicity: Is the dependency graph acyclic?
S3  Single Ownership: Does every item have exactly one owning domain?
S4  Forward References: Are there any forward references in the lean text?
S5  Cross-Reference Integrity: Do all cross-references resolve to valid targets?
S6  Notation Consistency: Is notation uniform across chapters?
S7  Fragment Coherence: Is the PL fragment self-contained?
S8  Extension Points: Are extension points documented for all three types?
S9  Completeness vs. Source: What percentage of source concepts are accounted for?
S10 Compilation: Does the text compile without errors?
Pass: all ≥2, total ≥24/30.

AUDIT 2 — COHERENCE (6 dimensions, each 0–3):
C1  Dependency Ordering: Trace 10 random DEFs; do prerequisites appear first?
C2  Definition-Use Consistency: Are terms used exactly as defined?
C3  Cross-Domain Handoffs: Are composition pattern handoffs explicit?
C4  Level Separation: Are BST (Level-0) and SET (Level-1) cleanly separated?
C5  Notation Stability: Does each symbol mean the same thing everywhere?
C6  Theorem Traceability: Can 5 random theorems be traced to axioms?
Pass: all ≥2, total ≥14/18.

AUDIT 3 — PROSE (8 dimensions, each 0–3):
P1  AC Accuracy: Are formal statements correct?
P2  PR Precision: Is language unambiguous?
P3  EX Examples: Do PRIMs and key DEFs have motivating examples?
P4  MO Motivation: Is every concept motivated before introduction?
P5  FL Flow: Do sections connect logically with meaningful transitions?
P6  DN Density: Is the ratio of formal content to prose balanced?
P7  AL Accessibility: Can a reader with one semester of logic follow?
P8  NO Notation Introduction: Is every symbol introduced before first use?
Pass: all ≥2, total ≥18/24.

OUTPUT FORMAT:
For each audit, produce:
1. A score table (dimension, score, evidence).
2. A pass/fail verdict with total.
3. For any dimension scoring <2, a remediation recommendation.
Then produce a combined summary: overall pass/fail, top 3 strengths,
top 3 weaknesses, and recommended next action.
```
