# Chemistry for Non-Majors: Domain-Primitive Textbook Project

## The Opportunity

~90% of chemistry textbooks copy each other. The field has converged on an **empirical-to-theory** progression. The historical alternative — **first-principles/physics-first** — failed because non-majors lack the math. Context-led/applications-first texts (_Chemistry in Context_) boost engagement but don't transfer. No existing textbook uses a domain-primitive architecture for non-majors.

Two structural forces lock in the status quo: (1) standardized exams (ACS, AP, MCAT) whose sequencing mirrors the canon, and (2) faculty adoption friction. But non-majors courses face **less** of both pressures — no MCAT prerequisite, no organic chemistry follow-on, weaker incumbent loyalty.

## What We're Building

A one-semester chemistry textbook for non-science majors, organized around **irreducible reasoning domains** with typed primitives and explicit composition patterns. Not a topic march. Not an applications grab-bag. A course that teaches students to **think like a chemist** — to decompose unfamiliar chemical claims into known reasoning patterns and evaluate them.

## What We Did With Logic (Precedent)

We compressed a 1,200-page mathematical logic textbook into a 221-page lean text using a 4-phase pipeline (taxonomy → mapping → compression → recomposition). The pipeline is now productized in `pipeline/` as 8 domain-agnostic instruction files. We're applying the same methodology here, but **designing a new taxonomy from scratch** rather than compressing an existing text.

## Key Research Findings

(Full research in `01-RESEARCH-SYNTHESIS.md`)

1. **Domain-primitive approaches work.** Modeling Instruction (physics): 6.73x odds of success. CLUE (chemistry): higher grades, lower DFW, better causal reasoning. Chemical Thinking (Talanquer): outperforms on ACS exams AND conceptual inventories.
2. **Non-majors retain frameworks, not facts.** Conceptual understanding shows "only a few percent decline" at 6-18 months (Deslauriers & Wieman). Factual knowledge drops 50%+ by year 2 (Custers). Teach reasoning primitives, not content.
3. **Applications-first engages but doesn't transfer.** Bennett et al. (2007): "understanding comparable to conventional approaches." The situatedness paradox binds learning to the specific application context.
4. **The fix: applications as deployment exercises for named primitives.** Explicit "bridging" (Perkins & Salomon): name the primitive, apply it, then apply the same primitive to a different context. This solves the transfer problem.
5. **No competitor exists.** CLUE and Chemical Thinking target STEM majors. No structural/ontological approach has been built for non-majors.
6. **Adoption path: OER → community colleges → NSF IUSE → scale.**

## Design Constraints

- **Audience:** Non-science majors, one semester (~14 weeks, ~42 contact hours)
- **Goal:** Chemical literacy — decompose and evaluate chemical claims, not solve quantitative STEM problems
- **Math ceiling:** No calculus. Algebra and proportional reasoning only.
- **Domain count:** 4-6 irreducible reasoning domains
- **Primitive count:** ~60-80 total (enough for depth, not overwhelming)
- **Assessment:** Must co-develop instruments that measure reasoning deployment, not factual recall
- **ACS alignment:** Map coverage after design, not during — don't let exam content drive architecture
- **Publication:** OER (OpenStax/LibreTexts), enabling rapid iteration and community-college adoption

## Phase Plan

| Phase | Task | Status |
|-------|------|--------|
| Phase 1 | Taxonomy: identify domains, primitives, dependency DAG, composition patterns | **IN PROGRESS** |
| Phase 2 | Mapping: map existing source materials (OpenStax, Chemistry in Context, CLUE) onto taxonomy | Pending |
| Phase 3 | Compression: triage existing content against taxonomy, build notation concordance | Pending |
| Phase 4 | Recomposition: draft the lean text, write transitions, compile | Pending |
| Phase 5 | Pilot: test at 2-3 institutions, measure retention at 6mo and 2yr | Pending |
