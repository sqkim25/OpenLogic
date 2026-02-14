# Phase 4: Recomposition

> **Phase 4 of 4** | Prev: [03-COMPRESSION.md](03-COMPRESSION.md) | Next: [05-QUALITY-GATES.md](05-QUALITY-GATES.md) (final audit)
> Templates: [06-TEMPLATES.md](06-TEMPLATES.md) §S5--S6 | Quality gate: [05-QUALITY-GATES.md](05-QUALITY-GATES.md) §1 (Gate 4)

---

## 1. Goal

Assemble the lean text from the compressed artifacts produced in Phase 3. Every chapter draft, transition, cross-reference, and front/back matter element is written during this phase.

### Input

- **Per-section compression directives** (from Phase 3)
- **Notation concordance** (unified notation table from Phase 3)
- **Lean outline** (chapter/section ordering from Phase 3)
- **Item registry** (all PRIM, DEF, AX, CP items with IDs from Phase 1)
- **Dependency DAG** (from Phase 1, refined in Phase 2)

### Output

- **Compiled lean text** (one document, LaTeX or Markdown)
- **Preface** explaining the compression methodology
- **Notation index** listing every symbol with its definition location
- **Subject index** covering all technical terms
- **Bibliography** referencing the original source corpus

### Exit criterion

The lean text compiles without errors, contains zero forward references, and every item in the registry appears exactly once in the body text. Pass [05-QUALITY-GATES.md](05-QUALITY-GATES.md) §1, Gate 4 before declaring Phase 4 complete.

---

## 2. Ordering Principle

Draft chapters in **dependency order**: a chapter may reference only items defined in earlier chapters or in the current chapter's preceding sections. Never introduce an item before its prerequisites.

Concretely, follow the topological sort of the dependency DAG. If the DAG has this structure:

```
SYNTAX -> SEMANTICS -> DEDUCTION -> METATHEORY
   |                       |
   v                       v
SET FOUNDATIONS      COMPUTATION -> INCOMPLETENESS
```

then draft Set Foundations first (no prerequisites), then Syntax, then Semantics, then Deduction, then Computation and Metatheory (in either order, since both depend only on earlier nodes), then Incompleteness last.

### When stuck

If two chapters form a mutual dependency (A needs a result from B, B needs a definition from A), break the cycle:

1. **Extract the shared item** into a standalone preliminary section placed before both chapters.
2. **Forward-declare with a stub**: state the result without proof, mark it `[proof: Ch. N]`, and complete the proof in the later chapter.
3. **Merge the two chapters** if the mutual dependency is pervasive (>3 shared items).

Choose option 1 when possible. Resort to option 2 only for isolated results. Use option 3 as a last resort.

> **Mathematical logic example.** Syntax defines "formula" (SYN-PRIM-001), but Semantics needs it for truth definitions, and Deduction needs it for derivation rules. No cycle: Syntax is drafted first, then both Semantics and Deduction reference it. However, if a metatheorem about derivations (DED) requires a semantic concept (completeness from SEM), extract the completeness statement into a preliminary section before the Metatheory chapter.

> **Organic chemistry example.** Bonding theory defines "covalent bond," but stereochemistry needs it for chirality, and reaction mechanisms need it for electron flow. No cycle: draft Bonding first. But if a named reaction (mechanisms chapter) requires a stereochemical concept (e.g., Walden inversion), extract the stereochemical prerequisite into a shared preliminary section.

---

## 3. Step 1 -- Chapter Drafting

For each chapter in the lean outline, execute the following actions in order.

### Action table

| # | Action | Input | Output | Verify |
|---|--------|-------|--------|--------|
| 1 | Collect all compression directives for this chapter | Phase 3 directives | Directive bundle | Every section in the lean outline for this chapter has a directive |
| 2 | Order sections by intra-chapter dependencies | Directive bundle + DAG | Ordered section list | No section references an item defined later in the same chapter |
| 3 | Draft each section using the canonical source and directive | Ordered section list + source corpus | Section drafts | Every item ID from the directive appears in the draft |
| 4 | Apply the notation concordance | Section drafts + concordance | Notation-unified drafts | Zero notation variants remain; every symbol matches the concordance |
| 5 | Insert dependency annotations | Notation-unified drafts | Annotated drafts | Every non-primitive item cites its prerequisites by ID |
| 6 | Run the per-chapter checklist (below) | Annotated drafts | Validated chapter draft | All checklist items pass |

### Per-chapter checklist

Run this checklist after drafting each chapter. Do not proceed to the next chapter until every item passes.

- [ ] **Coverage**: every item ID assigned to this chapter (per the lean outline) appears in the body text.
- [ ] **No forward references**: every item referenced in this chapter is either (a) defined earlier in this chapter or (b) defined in a preceding chapter.
- [ ] **No redundancy**: no item is defined in this chapter that was already defined in a preceding chapter.
- [ ] **Notation consistency**: every symbol in this chapter matches the notation concordance exactly.
- [ ] **Dependency annotation**: every theorem or definition cites its prerequisite item IDs (e.g., "By SYN-DEF-003 and SEM-PRIM-002...").
- [ ] **Prose quality**: every formal statement has at least one sentence of natural language explanation and one motivating example.
- [ ] **Length target**: the chapter is within +/-20% of the target length from the lean outline.

### Example: mathematical logic

**Chapter: Propositional Syntax** (directive says: define SYN-PRIM-001 through SYN-DEF-012, merge OpenLogic sections 2.1--2.4 into one narrative, eliminate the redundant re-definition of "formula" in section 2.3).

Draft action sequence:
1. Collect directives for SYN-PRIM-001..SYN-DEF-012.
2. Order: propositional variables first, then connectives, then formation rules, then formula.
3. Draft each section. For SYN-DEF-007 (formula), write the single canonical definition using the BNF grammar from the chosen source, not the prose-plus-examples version from section 2.3.
4. Replace all `\mathcal{L}` with `\mathcal{L}_0` per concordance.
5. Annotate: "Definition (Formula, SYN-DEF-007). Depends on: SYN-PRIM-001 (propositional variable), SYN-PRIM-002 (connective)."
6. Run checklist. Confirm 12 items present, no forward references, no duplicates.

### Example: organic chemistry

**Chapter: Alkene Reactions** (directive says: define REACT-DEF-014 through REACT-DEF-022, merge McMurry sections 7.1--7.6, unify "Markovnikov addition" / "Markownikoff addition" to single spelling).

Draft action sequence:
1. Collect directives for REACT-DEF-014..REACT-DEF-022.
2. Order: electrophilic addition mechanism first, then regiochemistry, then stereochemistry of addition, then specific reactions.
3. Draft each section. For REACT-DEF-017 (Markovnikov's rule), write the single canonical statement referencing carbocation stability (BOND-DEF-009).
4. Replace all "Markownikoff" with "Markovnikov" per concordance.
5. Annotate: "Rule (Markovnikov's Rule, REACT-DEF-017). Depends on: BOND-DEF-009 (carbocation stability), REACT-PRIM-001 (electrophile)."
6. Run checklist. Confirm 9 items present, no forward references, no duplicates.

---

## 4. Step 2 -- Transition Writing

After drafting all chapters, write transitions between consecutive chapters. Each transition occupies 1--3 paragraphs at the end of the earlier chapter or the beginning of the later chapter (choose consistently and keep the same placement throughout the text).

### Transition formula

Every transition follows this template:

> **Recap** (1--2 sentences): In Chapter N, we established [key results by ID].
> **Bridge** (1--2 sentences): These results leave open the question of [motivation for next chapter].
> **Preview** (1 sentence): Chapter N+1 answers this by introducing [key new items by ID].

### Example: mathematical logic

> In Chapter 3 (Semantics), we established truth-value assignments for propositional formulas (SEM-DEF-004) and proved the coincidence lemma (SEM-DEF-008). These results give us a criterion for validity but no *procedure* for establishing it. Chapter 4 (Deduction) answers this by introducing a formal proof system (DED-PRIM-001) and proving its soundness with respect to the semantic notion of validity (CP-003).

### Example: organic chemistry

> In Chapter 4 (Stereochemistry), we established the criteria for chirality (STEREO-DEF-003) and proved that enantiomers have identical physical properties in achiral environments (STEREO-DEF-007). These results leave open how stereochemistry constrains *reactivity*. Chapter 5 (Substitution Reactions) answers this by introducing the SN2 mechanism (REACT-DEF-025), whose concerted backside attack produces obligatory inversion of configuration.

---

## 5. Step 3 -- Cross-Reference Resolution

Resolve every internal cross-reference in the lean text. This step converts informal references ("as we saw earlier," "recall the definition from Chapter 2") into precise, machine-checkable references.

### Procedure

1. **Search** the full text for vague references: "as before," "recall," "previously defined," "see above," "as we saw."
2. **Replace** each vague reference with a precise one: "by SYN-DEF-007 (Chapter 2, Section 2.3)" or, in LaTeX, `\ref{syn-def-007}`.
3. **Search** for all item IDs (grep for the pattern `[A-Z]{2,4}-(PRIM|DEF|AX|CP)-\d{3}`) and verify each references an item that exists in the registry.
4. **Search** for orphan items: items in the registry that appear zero times in the body text. Every item must appear at least once (its definition site).
5. **Build a cross-reference index**: a table mapping each item ID to the chapter and section where it is defined and all chapters where it is referenced.

### Verification commands

For Markdown lean texts:

```bash
# Find vague references
grep -n -E "(as before|recall that|previously defined|see above|as we saw)" lean-text/*.md

# Find all item IDs and count occurrences
grep -o -E "[A-Z]{2,4}-(PRIM|DEF|AX|CP)-[0-9]{3}" lean-text/*.md | sort | uniq -c | sort -n

# Find IDs that appear only once (potential orphans -- the one occurrence is the definition)
grep -o -E "[A-Z]{2,4}-(PRIM|DEF|AX|CP)-[0-9]{3}" lean-text/*.md | sort | uniq -c | awk '$1 == 1'
```

For LaTeX lean texts:

```bash
# Find undefined references
grep -n "\\\\ref{" lean-text/*.tex | sed 's/.*\\ref{\([^}]*\)}.*/\1/' | sort -u > refs.txt
grep -n "\\\\label{" lean-text/*.tex | sed 's/.*\\label{\([^}]*\)}.*/\1/' | sort -u > labels.txt
comm -23 refs.txt labels.txt   # references with no matching label
```

---

## 6. Step 4 -- Front and Back Matter

Draft the following elements. Use the templates in [06-TEMPLATES.md](06-TEMPLATES.md) sections 5--6.

### Front matter

1. **Title page**: title, author(s), date, version number.
2. **Preface** (1--2 pages): explain the compression methodology, state the source corpus, list the domains, and describe what the reader gains over the original text.
3. **Table of contents**: auto-generated from chapter/section headings.
4. **How to read this text**: describe the dependency annotations, the notation index, and the item ID system so that a reader encountering the lean text for the first time can navigate it.

### Back matter

5. **Notation index**: list every symbol used in the text, its meaning, and the chapter/section where it is first defined. Sort alphabetically by symbol name (e.g., $\land$ under "conjunction," $\vdash$ under "turnstile"). Use the notation concordance from Phase 3 as the source.
6. **Subject index**: list every technical term, the item ID, and all page/section references. Generate automatically where possible; manually verify for completeness.
7. **Bibliography**: cite the original source corpus (every section referenced), plus any additional references introduced during recomposition. Use a consistent citation style (e.g., author-year).
8. **Item registry appendix** (optional but recommended): reproduce the full item registry as an appendix, so the reader can look up any ID and find its definition, domain, and dependencies.

---

## 7. Step 5 -- Compilation and Verification

Compile the lean text and run automated checks. Fix every error before proceeding to Step 6.

### LaTeX compilation

```bash
# Full compilation (run twice for cross-references)
pdflatex lean-text.tex && pdflatex lean-text.tex

# Check for undefined references and citations
grep -c "undefined" lean-text.log

# Check for overfull/underfull boxes (formatting issues)
grep -c "Overfull\|Underfull" lean-text.log

# Build the index
makeindex lean-text.idx && pdflatex lean-text.tex

# Build the bibliography
bibtex lean-text && pdflatex lean-text.tex && pdflatex lean-text.tex
```

### Markdown compilation

```bash
# Convert to HTML and check for broken links
pandoc lean-text.md -o lean-text.html --toc --number-sections
grep -n "\\[.*\\](.*)" lean-text.md | while read line; do
  url=$(echo "$line" | grep -oP '\]\(\K[^)]+')
  if [[ "$url" != http* ]] && [[ ! -f "$url" ]]; then
    echo "BROKEN: $line"
  fi
done

# Validate all item IDs resolve
python3 -c "
import re, sys
text = open('lean-text.md').read()
ids = re.findall(r'[A-Z]{2,4}-(PRIM|DEF|AX|CP)-\d{3}', text)
from collections import Counter
counts = Counter(ids)
orphans = [k for k,v in counts.items() if v < 2]
if orphans:
    print(f'WARNING: {len(orphans)} items appear only once (may be orphans):')
    for o in orphans: print(f'  {o}')
    sys.exit(1)
else:
    print(f'OK: all {len(counts)} items referenced at least twice')
"
```

### Automated checks summary

| Check | Tool | Pass criterion |
|-------|------|----------------|
| Compiles without error | `pdflatex` / `pandoc` | Exit code 0 |
| Zero undefined references | `grep` on log | Count = 0 |
| Zero broken internal links | Link checker script | Count = 0 |
| All item IDs valid | ID validation script | Every ID matches registry |
| No orphan items | Orphan checker | Every registry item appears >= 2 times in text |
| No forward references | Ordering checker | Every reference points to an earlier or same-chapter section |

---

## 8. Step 6 -- Iterative Refinement

Perform two passes over the compiled lean text: a prose audit and a publication preparation pass.

### Pass 1: Prose audit

Read the lean text end-to-end as a *reader*, not an author. For each chapter:

1. **Clarity**: can a reader with one semester of the subject follow the argument? If not, add explanation or examples.
2. **Flow**: do the transitions (Step 2) read naturally? Revise any transition that feels mechanical.
3. **Density**: is any section too dense (wall of definitions with no motivation)? Interleave motivation and examples.
4. **Redundancy**: does any explanation repeat what was said in an earlier chapter? Cut it and replace with a cross-reference.
5. **Completeness**: does the text feel like it is missing a key result that any standard reference would include? If so, check the gap analysis from Phase 2 and either add it or note it as out-of-scope in the preface.

### Pass 2: Publication preparation

1. **Spell-check** the entire text. Use `aspell` or equivalent.
2. **Grammar check**: run a grammar checker or have a second reader review.
3. **Formatting consistency**: verify heading levels, theorem numbering, font choices, and margin sizes are uniform.
4. **Figure/table numbering**: verify sequential numbering with no gaps.
5. **Page breaks**: ensure no chapter starts mid-page; no orphan lines at the top of a page; no widow lines at the bottom.
6. **Final compilation**: run the full compilation pipeline one last time (Step 5) after all edits.

```bash
# Spell-check (LaTeX)
aspell --mode=tex check lean-text.tex

# Spell-check (Markdown)
aspell --mode=markdown check lean-text.md

# Word count (verify compression ratio)
wc -w lean-text.md    # or: texcount lean-text.tex
```

Compute the **compression ratio**: word count of lean text divided by word count of original corpus. A typical target is 30--50% of the original. If the lean text exceeds 60%, return to Phase 3 and tighten compression directives.

---

## 9. Quality Gate 4

Pass every item below before declaring Phase 4 complete. Record results in [05-QUALITY-GATES.md](05-QUALITY-GATES.md) §1, Gate 4.

- [ ] **Compilation**: the lean text compiles without errors (LaTeX: zero errors in log; Markdown: pandoc exit code 0).
- [ ] **Zero undefined references**: no `\ref` or `\cite` points to a nonexistent label; no item ID in the text is absent from the registry.
- [ ] **Zero forward references**: every item referenced in chapter N is defined in chapter N or earlier.
- [ ] **Full coverage**: every item in the registry appears at least once in the body text.
- [ ] **No redundancy**: no item is defined more than once in the body text.
- [ ] **Notation uniformity**: every symbol matches the notation concordance; zero variant spellings or notations remain.
- [ ] **Transitions present**: every consecutive chapter pair has a transition (Step 2).
- [ ] **Front matter complete**: title page, preface, table of contents, and "how to read" section are present.
- [ ] **Back matter complete**: notation index, subject index, bibliography, and (optionally) item registry appendix are present.
- [ ] **Prose audit passed**: the end-to-end read (Step 6, Pass 1) found no blocking issues.
- [ ] **Compression ratio**: the lean text is <= 60% of the original corpus word count.
- [ ] **Spell-check clean**: zero uncorrected spelling errors.

---

## Appendix: Copy-Paste AI Prompt for Per-Chapter Drafting

Use this prompt when delegating chapter drafting to an AI assistant. Fill in the bracketed fields for each chapter.

~~~
You are drafting Chapter [N]: [CHAPTER TITLE] of a lean text produced by
knowledge compression. Follow these instructions exactly.

**Inputs provided:**
- Compression directives for this chapter (attached below)
- Notation concordance (attached below)
- Preceding chapters (attached or summarized below, for dependency context)

**Your task:**
1. Draft all sections of Chapter [N] in dependency order.
2. For each item ID in the directive, write:
   - A formal statement using the notation concordance (no variant symbols).
   - At least one sentence of natural language explanation.
   - At least one motivating example.
   - A dependency annotation listing prerequisite item IDs.
3. Do NOT introduce any item not listed in the directive.
4. Do NOT reference any item that has not been defined in this chapter or a
   preceding chapter. If you are unsure whether an item has been defined,
   ask rather than guessing.
5. Use imperative, active voice. Avoid hedging ("it can be shown that...").
   Write "We prove that..." or state the result directly.
6. Target length: [TARGET] words (+/- 20%).

**Notation concordance (excerpt):**
[PASTE RELEVANT ROWS FROM THE CONCORDANCE]

**Compression directives for Chapter [N]:**
[PASTE THE DIRECTIVES]

**Preceding chapter summaries (items already defined):**
[LIST ITEM IDS DEFINED IN EARLIER CHAPTERS, OR ATTACH THE CHAPTERS]

After drafting, run the per-chapter checklist:
- [ ] Every item ID from the directive appears in the draft.
- [ ] No forward references to items in later chapters.
- [ ] No item defined here was already defined in a preceding chapter.
- [ ] Every symbol matches the notation concordance.
- [ ] Every theorem/definition cites prerequisite item IDs.
- [ ] Every formal statement has natural language explanation + example.
- [ ] Word count is within +/- 20% of target.
~~~
