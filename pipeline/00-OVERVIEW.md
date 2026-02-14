# Knowledge Compression Pipeline

> **📍 You are here: 00-OVERVIEW (start here)**
> Next: → [01-TAXONOMY.md](01-TAXONOMY.md)

---

## What is Knowledge Compression?

Large corpora — textbooks, technical manuals, regulatory documents — accumulate redundancy over time. The same concept is defined in multiple places, notation varies between chapters, and the dependency structure is implicit. Readers cannot trace a theorem back to its primitives without flipping between sections.

**Knowledge compression** is the systematic elimination of redundancy from a corpus while preserving every formal concept and making every dependency explicit.

The output is a **lean text**: a single, dependency-ordered, single-narrative document where every concept is defined exactly once, every theorem is traceable to its primitives, and the dependency graph is explicit throughout.

---

## When to Use This Pipeline

### Good candidates

- **Textbooks** (200+ pages) with modular structure
- **Technical reference manuals** covering related but overlapping topics
- **Legal/regulatory corpora** where traceability is essential
- **Standards documents** with cross-referencing requirements
- Any corpus where **non-redundancy and traceability** matter

### Not suitable for

- Fiction, opinion pieces, or editorial content
- Short documents (<100 pages) — the overhead isn't worth it
- Corpora without formal structure (no definitions, theorems, or specifications)

### Mixed-format corpora

If your source is split across LaTeX, HTML, and PDF, convert everything to a single searchable format (Markdown recommended) before starting Phase 1. The pipeline assumes you can search and cross-reference across the entire corpus.

### Upper bound

For corpora exceeding 5,000 pages, split into sub-corpora first (by volume or topic cluster), compress each independently, then merge the lean outputs in a final integration pass.

### Scaling Guide

| Corpus size | Team | Timeline | Notes |
|-------------|------|----------|-------|
| Small (<200 pp) | 1 person + AI | 1–2 weeks | Single-pass, ~5 domains |
| Medium (200–1,000 pp) | 1–2 people + AI | 3–6 weeks | May need 2 taxonomy iterations |
| Large (1,000+ pp) | Team of 3+ with AI | 2–4 months | Requires formal project management |

---

## The 4-Phase Pipeline

```
Phase 1: TAXONOMY ──→ Phase 2: MAPPING ──→ Phase 3: COMPRESSION ──→ Phase 4: RECOMPOSITION
     │                    │                      │                        │
     ▼                    ▼                      ▼                        ▼
Domain specs         Section map           Compression plan          Lean text
Item registry        Coverage matrix       Notation concordance      Front/back matter
Dep. graph           Gap analysis          Lean outline              Index + bibliography
```

Each phase has a **quality gate** (see [05-QUALITY-GATES.md](05-QUALITY-GATES.md)). You must pass the gate before proceeding to the next phase.

**Backtracking rule:** If Phase 2 reveals your taxonomy is wrong (>20% of source sections don't map cleanly), return to Phase 1 and revise domains. Backtracking is normal — the pipeline is iterative at the phase level, even though the phases are sequential.

---

## Prerequisites

Before starting, you need:

1. **The source corpus** in a single searchable format (PDF, LaTeX, HTML, or Markdown)
2. **A rough sense of the domain's subfields** — reading the table of contents suffices
3. **An AI assistant** (Claude, GPT-4, etc.) or a dedicated team — see [07-AI-COLLABORATION.md](07-AI-COLLABORATION.md) for collaboration strategies
4. **A version-controlled repository** for artifacts — every deliverable goes into version control

### Version control strategy

Commit after each sub-phase (e.g., after domain specs, after section map, after each chapter draft). Tag major milestones:

```
git tag PHASE1-COMPLETE
git tag PHASE2-COMPLETE
git tag PHASE3-COMPLETE
git tag PHASE4-COMPLETE
```

This creates save points for backtracking. If Phase 2 reveals taxonomy problems, you can return to `PHASE1-COMPLETE` and revise.

---

## Expected Outputs

| Phase | Artifacts | Quality Gate |
|-------|-----------|-------------|
| 1 — Taxonomy | Domain specs (1 per domain), item registry, dependency DAG | All items have IDs; DAG is acyclic; every PRIM is truly primitive |
| 2 — Mapping | Section map, coverage matrix, redundancy resolution, gap analysis | Every item covered or marked out-of-scope; every redundancy resolved |
| 3 — Compression | Per-section directives, notation concordance, lean outline | Every section has a directive; no item lost; notation unified |
| 4 — Recomposition | Compiled lean text, preface, notation index, subject index, bibliography | Compiles without errors; no forward references; index covers all terms |

---

## How to Use These Files

### File index

| File | Purpose | When to use |
|------|---------|-------------|
| [00-OVERVIEW.md](00-OVERVIEW.md) | Master guide (this file) | Read first |
| [01-TAXONOMY.md](01-TAXONOMY.md) | Phase 1: Build the taxonomy | During Phase 1 |
| [02-MAPPING.md](02-MAPPING.md) | Phase 2: Map source material | During Phase 2 |
| [03-COMPRESSION.md](03-COMPRESSION.md) | Phase 3: Compress against taxonomy | During Phase 3 |
| [04-RECOMPOSITION.md](04-RECOMPOSITION.md) | Phase 4: Recompose the lean text | During Phase 4 |
| [05-QUALITY-GATES.md](05-QUALITY-GATES.md) | Quality rubrics and audits | Between and after phases |
| [06-TEMPLATES.md](06-TEMPLATES.md) | Fill-in-the-blank templates | Reference throughout |
| [07-AI-COLLABORATION.md](07-AI-COLLABORATION.md) | AI collaboration strategies | Reference throughout |

### Reading paths

**First-timer:**
```
00 → 06 (templates) → 01 → 05 (gate 1) → 02 → 05 (gate 2) → 03 → 05 (gate 3) → 04 → 05 (gate 4)
```

**Experienced:**
```
00 → 01 → 02 → 03 → 04 (check 05 only when stuck)
```

---

## Glossary

| Term | Definition |
|------|-----------|
| **Domain** | An irreducible subject area answering one governing question |
| **PRIM** | A primitive concept, taken as given within its domain |
| **DEF** | A concept defined from PRIMs and earlier DEFs |
| **AX** | An axiom, accepted without proof |
| **CP** | A composition pattern — a cross-domain result (metatheorem) |
| **Lean text** | The compressed output: single narrative, no redundancy, full dependency graph |
| **Quality gate** | A pass/fail checkpoint between phases |
| **Canonical section** | The source section chosen as the authoritative treatment of an item |
| **Notation concordance** | A table mapping notation variants to one canonical form |
