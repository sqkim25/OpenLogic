# AI Collaboration Strategies

> **📍 Reference** -- use throughout all phases
> Prev: [06-TEMPLATES.md](06-TEMPLATES.md) | Prerequisite: Read [00-OVERVIEW.md](00-OVERVIEW.md) first

---

## 1. Why AI Helps

Knowledge compression is labor-intensive but highly structured. The work divides cleanly between tasks that benefit from breadth and speed (AI) and tasks that require judgment and domain authority (human).

### Division of Labor

| Task | AI Role | Human Role |
|------|---------|------------|
| **Domain discovery** | Propose candidate domains by scanning table of contents and cross-references across the entire corpus | Accept, reject, or merge proposed domains; enforce the closed-domain principle |
| **Item enumeration** | Extract every definition, theorem, and axiom from source chapters; propose PRIM/DEF/AX classification | Verify classification; resolve contested ownership using boundary principles P1--P5 |
| **Mapping** | Match source sections to taxonomy items; flag unmapped sections and redundant treatments | Adjudicate mapping conflicts; decide canonical section for each item |
| **Compression** | Draft per-section compression directives (keep/merge/relocate/cut); identify notation variants | Approve directives; make final calls on what is cut vs. relegated to appendix |
| **Drafting** | Write chapter drafts following the lean outline; maintain notation concordance | Review drafts for correctness; verify every theorem statement and proof sketch |
| **Auditing** | Run mechanical checks (ID uniqueness, DAG acyclicity, cross-reference integrity, forward-reference detection) | Interpret audit results; decide whether failures require backtracking or local fixes |

**Rule of thumb:** AI proposes, human disposes. Every AI output is a draft until the human accepts it. Never merge AI-generated taxonomy items or text into the canonical artifacts without human review.

---

## 2. Prompt Patterns by Phase

Each phase begins with a **bootstrap prompt** that sets the AI's role, scope, and output format. Copy these into your AI session at the start of each phase. Adjust the corpus-specific details (bracketed) before use.

### Phase 1: Taxonomy Bootstrap

```
You are building a primitive taxonomy for [CORPUS NAME].

The corpus covers [BRIEF DESCRIPTION, e.g., "mathematical logic from
propositional through incompleteness"]. It has [N] chapters across
[M] topic areas.

Task: Propose a set of irreducible domains. For each domain, provide:
1. A 3-letter code
2. A governing question (one sentence)
3. 5-10 candidate primitives (concepts that cannot be defined from
   simpler concepts within this domain)
4. The domain's imports (which other domains it depends on)

Constraints:
- Every concept must have exactly one owning domain
- The domain dependency graph must be acyclic
- Prefer fewer domains (5-7) over more

Output format: Markdown table with columns
[Code | Governing Question | Candidate Primitives | Imports]
```

**Expected output:** A table with 5--7 rows. Each row names a domain and lists candidate primitives. Review for: (a) are the domains truly irreducible? (b) is the dependency graph acyclic? (c) are any primitives actually definable from others?

### Phase 2: Mapping Bootstrap

```
You are mapping source material onto an existing taxonomy.

The taxonomy has [N] domains with [M] total items (PRIM + DEF + AX).
The domain specs are provided below.

[PASTE OR ATTACH DOMAIN SPECS]

Task: For each source section listed below, identify:
1. Which taxonomy items it covers (by ID)
2. Whether it is the best (canonical) treatment of each item
3. Any items it covers that are NOT in the taxonomy (gaps)
4. Any notation variants vs. the taxonomy's canonical notation

Source sections:
[LIST OF SECTION TITLES AND BRIEF DESCRIPTIONS]

Output format: One row per source section with columns
[Section | Items Covered (IDs) | Canonical? | Gaps | Notation Variants]
```

**Expected output:** A table mapping every source section to taxonomy items. Review for: (a) are any taxonomy items left uncovered? (b) are redundancies correctly identified? (c) are gap proposals genuine gaps or misclassifications?

### Phase 3: Compression Bootstrap

```
You are compressing source material against a taxonomy.

For each source section, you have: the taxonomy items it covers, whether
it is canonical, and the notation concordance.

[PASTE OR ATTACH SECTION MAP AND NOTATION CONCORDANCE]

Task: For each source section, produce a compression directive:
- KEEP: Section is canonical; rewrite to match taxonomy notation
- CONDENSE: Section is canonical but verbose; compress prose, keep formal content
- MERGE-INTO: Fold into [canonical section] (this section is non-canonical)
- RELOCATE: Move content to [chapter] to respect dependency order
- CUT: Content is redundant or out-of-scope; remove entirely
- EXTRACT-PATTERN: Cross-domain result; move to composition-pattern chapter

For KEEP and MERGE sections, also provide:
1. The dependency-ordered sequence of items to present
2. Any forward references that must be eliminated
3. Notation changes required

Output format: One row per section with columns
[Section | Directive | Target | Item Sequence | Notes]
```

**Expected output:** A directive for every source section. Review for: (a) does any CUT directive remove content not fully covered elsewhere? (b) do RELOCATE directives create a valid dependency order? (c) are MERGE targets logically coherent?

### Phase 4: Recomposition Bootstrap

```
You are drafting a lean text chapter.

Chapter: [CHAPTER TITLE]
Position in lean outline: Chapter [N] of [M]
Items to cover (in order): [LIST OF ITEM IDS WITH NAMES]
Notation concordance: [PASTE RELEVANT ENTRIES]
Prior chapters already define: [LIST OF ITEMS FROM EARLIER CHAPTERS]

Task: Write the chapter following these rules:
1. Define each item exactly once, in the listed order
2. Use only canonical notation from the concordance
3. Never use a concept before it is defined (no forward references)
4. Include a proof sketch for every theorem
5. Mark every cross-reference with its taxonomy ID in the margin

Target length: [N] pages
Style: Terse, precise, dependency-ordered. No motivational preamble
unless the item's entry includes a required example.
```

**Expected output:** A chapter draft in LaTeX or Markdown. Review for: (a) does the order match the dependency DAG? (b) is every notation consistent with the concordance? (c) are all theorem statements correct?

---

## 3. Parallelization Strategy

### Sequential vs. Parallel Steps

Not all work within a phase must be sequential. The following diagram shows which steps can run in parallel.

```
PHASE 1: TAXONOMY
  [Scan corpus TOC] ──sequential──> [Propose domains]
                                        |
                          ┌─────────────┼─────────────┐
                          ▼             ▼             ▼
                     [Domain A     [Domain B     [Domain C    ... parallel
                      spec]         spec]         spec]          per domain
                          └─────────────┼─────────────┘
                                        ▼
                               [Reconciliation pass] ──sequential

PHASE 2: MAPPING
  [Load taxonomy] ──sequential──> [Divide source into chunks]
                                        |
                          ┌─────────────┼─────────────┐
                          ▼             ▼             ▼
                     [Chunk 1      [Chunk 2      [Chunk 3     ... parallel
                      mapping]      mapping]      mapping]       per chunk
                          └─────────────┼─────────────┘
                                        ▼
                               [Merge + deduplicate] ──sequential
                                        ▼
                               [Gap analysis] ──sequential

PHASE 3: COMPRESSION
  [Load section map] ──sequential──> [Notation concordance] ──sequential
                                        |
                          ┌─────────────┼─────────────┐
                          ▼             ▼             ▼
                     [Block 1      [Block 2      [Block 3     ... parallel
                      directives]   directives]   directives]    per block
                          └─────────────┼─────────────┘
                                        ▼
                               [Lean outline] ──sequential

PHASE 4: RECOMPOSITION
  [Load lean outline] ──sequential──> [Front matter]
                                        |
                          ┌─────────────┼─────────────┐
                          ▼             ▼             ▼
                     [Chapter 1    [Chapter 2    [Chapter 3   ... parallel
                      draft]        draft]        draft]         per chapter
                          └─────────────┼─────────────┘
                                        ▼
                               [Cross-reference audit] ──sequential
                                        ▼
                               [Index + bibliography] ──sequential
```

### Scaling by Corpus Size

| Corpus Size | Phase 1 Agents | Phase 2 Agents | Phase 3 Agents | Phase 4 Agents | Total Sessions |
|-------------|---------------|---------------|---------------|---------------|----------------|
| Small (<200 pp) | 1 | 1 | 1 | 1 | 4--8 |
| Medium (200--1,000 pp) | 1 | 2--3 (one per topic cluster) | 2--3 (one per block) | 2--4 (one per chapter pair) | 12--25 |
| Large (1,000+ pp) | 1--2 | 4--6 (one per topic cluster) | 4--6 (one per block) | 6--10 (one per chapter) | 30--60 |

Phase 1 is always low-parallelism because domains must be globally coherent. Phase 2 and Phase 4 offer the most parallelism because chunks/chapters are largely independent after the shared artifacts (taxonomy, lean outline) are established.

### Multi-Session Strategy

Each AI session has a finite context window. Plan sessions to fit within it:

1. **One session = one deliverable.** A single domain spec, a single chunk mapping, a single chapter draft. Do not try to produce the entire taxonomy in one session.
2. **Front-load context.** Start every session by loading: (a) CONVENTIONS.md, (b) the relevant phase bootstrap prompt, (c) any artifacts the session depends on (e.g., domain specs for a mapping session).
3. **End every session with a commit.** The deliverable goes into version control before the next session starts. This prevents context loss.
4. **Chain sessions via artifacts, not memory.** The output of session N is the input of session N+1. Never rely on the AI "remembering" a prior session.

---

## 4. Agent Architecture

For larger projects, specialize AI sessions into four agent types. Each type has a distinct prompt pattern and a narrow responsibility.

### Explorer Agent

**Role:** Scan the corpus and extract raw information.

**When to use:** Phase 1 (domain discovery), Phase 2 (section scanning), any time you need to survey unfamiliar material.

```
You are an Explorer agent. Your job is to scan source material and
extract structured information. You do NOT make decisions about
taxonomy structure or ownership.

Source material: [PASTE OR DESCRIBE SOURCE]

Extract:
1. Every defined term (with page/section reference)
2. Every stated theorem or lemma (with dependencies)
3. Every notation convention
4. Any concept that appears without explicit definition

Output: Raw extraction table. Do not classify or assign IDs.
```

**Output goes to:** Human for triage, then to Worker agent for classification.

### Worker Agent

**Role:** Produce specific deliverables (domain specs, section maps, chapter drafts).

**When to use:** The bulk of every phase. One Worker per deliverable.

```
You are a Worker agent producing [DELIVERABLE NAME].

You have been given:
- The taxonomy conventions (CONVENTIONS.md)
- The relevant phase guide ([01/02/03/04]-*.md)
- Prior artifacts: [LIST]

Produce: [SPECIFIC DELIVERABLE] following the template in
06-TEMPLATES.md.

Constraints:
- Use only IDs from the existing registry (do not invent new IDs)
- Flag any item that does not fit the existing taxonomy as a GAP
- Mark any uncertainty with [UNCERTAIN: reason]
```

**Output goes to:** Auditor agent for mechanical checks, then human for approval.

### Auditor Agent

**Role:** Run mechanical quality checks on deliverables.

**When to use:** After every Worker output, before human review. Also at quality gates.

```
You are an Auditor agent. Your job is to check deliverables for
mechanical correctness. You do NOT judge content quality — only
structural integrity.

Deliverable to audit: [PASTE DELIVERABLE]
Checklist:
1. Every item has a valid ID in the format {TYPE}-{DOM}{NNN}
2. No duplicate IDs
3. Every cross-reference points to an existing item
4. The dependency graph is acyclic (list any cycles found)
5. No forward references (item X depends on item Y defined later)
6. Notation matches the concordance (list any deviations)
7. Every required field is present (per template)

Output: Pass/fail per checklist item. For each failure, list the
specific items that fail and why.
```

**Output goes to:** Fixer agent (if failures) or human (if pass).

### Fixer Agent

**Role:** Resolve specific, well-defined issues flagged by the Auditor.

**When to use:** When the Auditor reports failures that have mechanical fixes (e.g., broken cross-references, missing fields, notation mismatches).

```
You are a Fixer agent. You have been given a deliverable and a list
of specific failures from an audit.

Deliverable: [PASTE DELIVERABLE]
Failures: [PASTE AUDIT REPORT]

Task: Fix each failure. For each fix, state:
1. What was wrong
2. What you changed
3. Why the fix is correct

Do NOT make changes beyond the listed failures. Do NOT reorganize,
rephrase, or "improve" content that passed the audit.
```

**Output goes to:** Auditor agent for re-check, then human for approval.

### Agent Pipeline

For a single deliverable, the flow is:

```
Explorer --> Human triage --> Worker --> Auditor --> [pass?] --> Human review
                                            |                       |
                                            v (fail)                v
                                          Fixer --> Auditor     Merge to repo
```

---

## 5. Context Management

AI sessions have limited context windows and no persistent memory between sessions. These practices prevent information loss.

### Memory Files

Maintain a small set of files that capture session-to-session state:

| File | Contents | Updated |
|------|----------|---------|
| `MEMORY.md` | Project-level decisions, approach, domain list, phase status | After each phase milestone |
| `STATUS.md` | Current phase, next deliverable, blocking issues, open questions | After every session |
| `CONVENTIONS.md` | ID scheme, notation, normative language, registry | After Phase 1; rarely thereafter |

Load `MEMORY.md` and `STATUS.md` at the start of every session. They replace the context the AI cannot carry over.

### Status Document Protocol

At the end of every AI session, update `STATUS.md` with:

```
## Session [DATE]
- Phase: [current phase]
- Deliverable produced: [name and location]
- Items completed: [list of IDs or section names]
- Items remaining: [list]
- Open questions: [list, each with enough context to be understood without prior session]
- Next action: [specific instruction for the next session]
```

### Commit Frequently

Every deliverable gets its own commit. Do not batch multiple deliverables into a single commit. Tag phase completions:

```
git commit -m "Phase 1: Add DOMAIN-SYNTAX spec (PRIM-SYN001 through PRIM-SYN018)"
git tag PHASE1-COMPLETE   # only when all Phase 1 deliverables pass the quality gate
```

This creates rollback points. If a Phase 2 mapping session reveals a taxonomy problem, you can inspect the exact state at `PHASE1-COMPLETE`.

### Front-Load Exploration

At the start of a new phase, spend one full session on exploration before producing deliverables:

1. **Phase 1:** Scan the entire table of contents. List every chapter, its topic, and its rough dependency on other chapters. Do not classify anything yet.
2. **Phase 2:** Read every domain spec and the full item registry. List every item. Do not start mapping yet.
3. **Phase 3:** Read the complete section map and coverage matrix. List every redundancy and every gap. Do not write directives yet.
4. **Phase 4:** Read the lean outline and notation concordance end to end. List every chapter's item sequence. Do not draft yet.

This exploration session produces a "lay of the land" document that all subsequent Worker sessions load as context.

### Explicit Handoff

When passing work between sessions (or between agents), include an explicit handoff block:

```
## Handoff
- Deliverable: [what was produced, with file path]
- Depends on: [which prior artifacts this deliverable assumes]
- Consumed by: [which next step needs this deliverable]
- Known issues: [anything the next session should watch for]
- Verification: [how to confirm the deliverable is correct]
```

Never assume the next session will "figure out" what happened. Write the handoff as if the next session has zero prior knowledge.

---

## 6. Common Pitfalls and Recovery

| Pitfall | Symptom | Prevention | Recovery |
|---------|---------|------------|----------|
| **Notation drift** | The same concept uses different symbols in different chapters (e.g., $\vDash$ vs. $\models$ vs. $\Vdash$) | Build the notation concordance in Phase 3 before any drafting; load it into every Phase 4 session | Run a global search-and-replace pass using the concordance; re-audit all affected chapters |
| **Over-cutting** | A Phase 3 CUT directive removes content that is not fully covered by the canonical section (subtle variant or edge case lost) | For every CUT, require the Auditor to verify that every item in the cut section appears in the canonical section's item list | Restore the cut section from version control; reclassify as MERGE-INTO or CONDENSE instead of CUT |
| **Over-writing** | AI drafts add explanatory material, examples, or context not present in the source, inflating the lean text | Include word/page budgets in every Phase 4 prompt; instruct the AI to flag any added material with `[ADDED]` | Diff the draft against the compression directive; delete any paragraph not traceable to a directive item |
| **Forward references** | Chapter N uses a concept defined in Chapter N+2; the dependency order is violated | The Auditor agent checks every cross-reference against the lean outline's item sequence; flag any reference to a later item | Either move the referenced definition earlier (update lean outline) or restructure the chapter to defer the dependent content |
| **Line-number drift** | After editing a file, previously recorded line numbers in mapping or directive artifacts become stale | Reference items by ID and section heading, never by line number; use anchors, not offsets | Re-run the mapping on the current file to update references; add a note in STATUS.md that line references have shifted |
| **Compilation errors** | LaTeX fails to compile after chapter edits (missing packages, broken cross-references, undefined commands) | Compile after every chapter draft, not just at the end; keep a minimal preamble that all chapters share | Read the compiler log; fix errors in dependency order (undefined commands first, then cross-references, then formatting) |
| **Agent hallucination** | AI invents a theorem, misattributes a result, or fabricates a source reference | Always cite by taxonomy ID; require the Auditor to verify every theorem statement against the source corpus; never accept a source reference without checking it exists | Flag the hallucinated content; revert to the source text; add a note in STATUS.md to watch for the specific hallucination pattern in future sessions |

### Recovery Protocol

When any pitfall is detected:

1. **Stop.** Do not continue producing deliverables until the issue is resolved.
2. **Assess scope.** Is this a local issue (one chapter, one section) or systemic (affects the entire phase output)?
3. **Fix at the source.** If notation drifted, fix the concordance first, then propagate. If a forward reference exists, fix the lean outline first, then re-draft.
4. **Re-audit.** After fixing, run the Auditor on all potentially affected deliverables, not just the one where the issue was found.
5. **Document.** Add the issue and resolution to STATUS.md so future sessions know to watch for recurrence.
