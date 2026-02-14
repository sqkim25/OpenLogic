# Grand Plan: Discovery-Driven Rewrite of the Chemistry Textbook

## Context

The chemistry textbook (65,000 words, 6 chapters, 163-page PDF) is technically complete but reads like a taxonomy delivery system. Every concept is correct and traceable, but the voice is declarative — "here are the 62 reasoning moves, arranged by dependency." The user's critique: it reads like "a real estate book" — dogmatic, top-down, lifeless. No sense that chemistry is a living discipline discovered by real people through struggle, failure, and insight.

**The goal**: Rewrite the textbook so students walk alongside the scientists who discovered chemistry — Lavoisier weighing his retorts, Mendeleev shuffling element cards on a train, Rutherford stunned by bouncing alpha particles. Content and story become inseparable. The reasoning moves still land, but they emerge from narrative rather than being delivered from above.

## What Changes vs. What's Preserved

### Preserved (load-bearing infrastructure)
- 62 reasoning moves (PRIM/DEF) — the moves themselves are sound
- 5-domain taxonomy (COM, STR, NRG, SCL, CHG) — primitives stay as-is
- Dependency DAG — cannot violate prerequisite ordering
- 7 Composition Patterns — cross-domain applications
- Notation concordance — 10 categories of style decisions
- Non-majors depth ceiling — no calculus, no ICE tables
- Licensing decisions — CC-BY 4.0, WRITE-ORIGINAL for NC-SA items
- ~35-40% of existing prose — worked examples, tables, practice questions

### Changed (everything else)
- **Chapter structure**: 6 domain-per-chapter → 10 discovery-driven thematic chapters
- **Voice**: Declarative delivery → continuous narrative (no "voice flips")
- **Openings**: Consumer-object hooks → historical puzzles and genuine uncertainties
- **Reasoning moves**: Delivered as definitions → emerge from discovery narratives
- **Human stories**: Absent → ~15-20 major discovery narratives woven into main text
- **Wrong ideas**: Absent → phlogiston, plum pudding, caloric theory shown with respect
- **Student role**: Knowledge recipient → witness to and participant in discovery

## The 10-Chapter Structure

| Ch | Title | Discovery Anchors | Domains | Primitives |
|----|-------|-------------------|---------|------------|
| 1 | What Is the World Made Of? | Lavoisier (conservation), Dalton (atoms) | COM | COM001-006, COM004-005, DEF-COM partial |
| 2 | Sorting the Elements | Mendeleev (periodic table, card game, predicted elements) | COM | COM003, COM007, DEF-COM001-002, DEF-COM005 |
| 3 | Inside the Atom | Thomson (electron), Rutherford (gold foil), Bohr (shells) | COM→STR | STR001, STR002, DEF-STR001 |
| 4 | Why Do Things Have Properties? | Pauling (electronegativity), Kekule (benzene ring) | STR | STR003-005, DEF-STR002-004, DEF-STR006, DEF-STR010 |
| 5 | The Architecture of Carbon | Wohler (urea, demolishing vitalism), Franklin (Photo 51) | STR + MULTI | DEF-STR005, DEF-STR007-008, CP-007 |
| 6 | Fire and Ice | Rumford (heat is motion), Joule (mechanical equivalent), Gibbs, Haber (dual legacy) | NRG | NRG001-006, DEF-NRG001-003, DEF-NRG005 |
| 7 | Counting the Invisible | Avogadro (hypothesis), Cannizzaro (revival), Perrin (proving atoms are real) | SCL | SCL001-002, SCL004-006 |
| 8 | Mixing and Measuring | Paracelsus ("dose makes poison"), Flint water crisis, Ramsay (noble gases) | SCL | SCL003, DEF-SCL001-002, DEF-SCL005, CP-005 |
| 9 | When Substances Transform | Lavoisier (overthrows phlogiston), Le Chatelier, Scheele/Priestley (oxygen) | CHG | CHG001-005, DEF-CHG001-003, CP-002, CP-003 |
| 10 | Electrons in Motion | Volta (battery), Curie (radioactivity), Arrhenius (acids vindicated) | CHG | CHG006-007, DEF-CHG004-005, COM008, CP-001, CP-004, CP-006 |

**Dependency verification**: Zero violations. COM (Ch 1-2) → STR (Ch 3-5) → NRG (Ch 6) → SCL (Ch 7-8) → CHG (Ch 9-10). All cross-domain references are backward. Verified against the taxonomy DAG.

**Word count target**: 80,000-92,000 words (~260-320 pages). The ~15-20% increase over current 65,000 accommodates discovery narratives without cutting content.

## The Five Voice Rules

**Rule 1: Enter every topic through a question a real person asked.**
Not "You are holding a bottle of water" but "In 1772, Lavoisier sealed a glass retort, weighed it, and set it over a flame. He was trying to answer a question that had troubled chemists for decades..."

**Rule 2: Let the wrong idea have its full say.**
Phlogiston was not stupid. It explained why things lost weight when burned. Show its logic, then show what broke it. Students see that science progresses by surpassing reasonable theories, not discarding foolish ones.

**Rule 3: The reasoning move emerges from the story.**
Discovery-then-Name protocol: (1) story creates the need, (2) reasoning is shown in action, (3) move is named and generalized, (4) move is applied to a modern problem, (5) taxonomy ID appears in a margin reference box.

**Rule 4: Never switch to textbook register mid-narrative.**
No "Now let's examine the formal definition..." The technical content is woven into continuous prose. Rutherford's gold foil experiment IS the explanation of the nuclear model — not a story followed by a definition.

**Rule 5: Show the human cost and the human joy.**
At least one genuinely human detail per chapter, integrated into the main text: Mendeleev's mother dying after walking him to Moscow, Curie's hands scarred by radium, Lavoisier's execution, Haber's wife Clara opposing chemical weapons.

## Chapter Narrative Arc Template

Each chapter follows:
1. **Inciting question** — a real puzzle scientists faced
2. **Context** — what was believed, who was involved, stakes
3. **The method/experiment** — what approach was taken
4. **The surprise/crisis** — what contradicted expectations
5. **Resolution & implications** — how the idea was accepted
6. **Limitations & revision** — what was later revised (avoids Whig history)
7. **Conceptual synthesis** — the reasoning moves that emerged, named and portable

## Reasoning Move Integration: The "Discovery-then-Name" Protocol

**Step 1**: The story creates the need (scientist faces a problem)
**Step 2**: The reasoning is shown in action (student watches it happen)
**Step 3**: The move is named ("What Lavoisier did here is a move we call atomic composition analysis")
**Step 4**: Applied to a modern context (food label, water quality report)
**Step 5**: Formal reference appears in a styled margin box (taxonomy ID + "Given X, do Y to determine Z")

## Anti-Patterns to Actively Avoid

- **Whig history**: Don't present past scientists as "wrong" — show their reasoning as serious
- **Sidebar syndrome**: Stories are the text, not colored boxes alongside it
- **Voice flip**: Never tell a story then switch to "Now let's examine..." textbook mode
- **Hero worship**: Show collaboration, mistakes, politics — not just eureka moments
- **Info-dump**: Discovery narratives must always advance content, never pause it
- **Narrative cap**: 1,500 words max per discovery story to prevent pacing bloat

## Execution Plan

### Phase 0: Foundation (1 session)
- Create `recomposition-v2/` directory
- Write `DISCOVERY-REWRITE-GUIDE.md` — voice rules, anti-patterns, the Discovery-then-Name protocol
- Write `CHAPTER-MAP-V2.md` — 10-chapter structure with primitive assignments and dependency verification
- Write `STORY-RESEARCH.md` — primary/secondary sources for each discovery narrative (2+ sources per story)

### Phase 1: Pilot Chapter (1-2 sessions)
- Write Chapter 1 ("What Is the World Made Of?") from scratch
- This sets the voice, pacing, and integration model for all subsequent chapters
- ~8,000-9,000 words
- Quality gate: compare side-by-side with current CH-01-COM.md

### Phase 2: Chapters 2-5 — Elements, Atoms, Structure, Carbon (3-4 sessions)
- Mendeleev, Rutherford, Pauling, Franklin narratives
- Reuse worked examples from current CH-02-STR.md (Lewis structures, VSEPR, IMF)
- ~32,000-36,000 words
- Can parallelize: 2 agents per session (Ch 2+3 then Ch 4+5)

### Phase 3: Chapters 6-8 — Energy and Scale (2-3 sessions)
- Rumford, Joule, Gibbs, Avogadro, Paracelsus narratives
- Adapt content from current CH-03-NRG.md and CH-04-SCL.md
- ~24,000-28,000 words

### Phase 4: Chapters 9-10 — Change and Synthesis (2-3 sessions)
- Lavoisier (combustion), Le Chatelier, Volta, Curie, Arrhenius narratives
- Adapt content from current CH-05-CHG.md
- Deploy remaining CPs; synthesize PRIM-COM008
- ~18,000-22,000 words

### Phase 5: Front/Back Matter and Integration (1-2 sessions)
- Rewrite preface (discovery-journey framing)
- Update toolkit, glossary, notation guide
- New "Timeline of Discoveries" back-matter section
- Full cross-reference verification pass

### Phase 6: LaTeX Conversion and Compilation (1-2 sessions)
- Convert all 10 chapters to LaTeX
- Add new environments: `\discoverystory{}`, `\wrongturn{}`, margin reasoning boxes
- Update `chem-textbook.tex` for 10-chapter structure
- Compile to PDF

**Total: ~11-17 sessions**

## Quality Gates (per chapter)

1. **DAG check**: No primitive appears before its dependencies
2. **Coverage check**: All assigned primitives are introduced
3. **Voice check**: First 500 words read as story, not textbook
4. **Integration check**: Every reasoning move introduced via Discovery-then-Name protocol
5. **Anti-pattern check**: No voice flips, sidebar syndrome, Whig history, or hero worship
6. **Salvage check**: Reusable content from current text actually reused
7. **Word count check**: Chapter within ±15% of target

## Critical Files

| File | Role |
|------|------|
| `chem-textbook/taxonomy/CONVENTIONS.md` | Authoritative primitive registry + dependency DAG |
| `chem-textbook/compression/00-STRATEGIC-DECISIONS.md` | Depth ceiling, notation concordance, licensing |
| `chem-textbook/compression/01-CHAPTER-ARCHITECTURE.md` | Current architecture (reference for salvage) |
| `chem-textbook/recomposition/CH-01-COM.md` through `CH-06-MULTI.md` | Current text (source for adaptation) |
| `chem-textbook/recomposition/ANSWERS-*.md` | Answer keys (adapt for new chapter numbering) |
| `chem-textbook/latex/chem-preamble.sty` | LaTeX environments (extend for narrative elements) |

## Risks

| Risk | Mitigation |
|------|------------|
| Stories slow pacing | 1,500-word cap per narrative; stories must advance content |
| Voice drifts across sessions | DISCOVERY-REWRITE-GUIDE.md as style anchor; re-read before every session |
| Historical accuracy errors | 2+ sources per story in STORY-RESEARCH.md; flag uncertain claims |
| Word count balloons | Cut E-tier material if needed; enforce per-chapter targets |
| DAG violations from interleaving | Run verification after every chapter against CONVENTIONS.md |
| Loss of "portable toolkit" identity | Margin reasoning boxes + "Looking Back" synthesis at chapter ends |
