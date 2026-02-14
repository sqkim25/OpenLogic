# Design Prompt: Phase 1 Taxonomy for Non-Majors Chemistry

> This is the working prompt for Phase 1. Execute using the methodology in `pipeline/01-TAXONOMY.md`.

---

## Context

We have a proven knowledge compression pipeline (see `pipeline/` files) that identifies irreducible domains, catalogs primitives, and builds dependency graphs. We have deep research (`01-RESEARCH-SYNTHESIS.md`) establishing that: (a) domain-primitive approaches work dramatically better than topic-sequenced instruction, (b) non-majors retain reasoning frameworks but not facts, (c) the non-majors chemistry market has no structural competitor. We now need to execute Phase 1 for chemistry.

## Target Audience

Non-science majors taking a one-semester chemistry course. They will never take organic chemistry. They need chemical literacy — the ability to decompose an unfamiliar chemical claim (in a news article, a product label, a policy debate) into known reasoning patterns and evaluate it. They do not need to solve quantitative problems at the level of a STEM major.

---

## Task 1 — Identify 4-6 Irreducible Reasoning Domains

Start from four CER source frameworks:

1. **Talanquer's 7 reasoning dimensions**: composition, structure, energy, time-scale, etc.
2. **Cooper's 4 CLUE core ideas**: structure/properties, bonding/interactions, energy, change/stability
3. **Johnstone's triplet + Mahaffy's tetrahedron**: macro, submicro, symbolic, human context
4. **Talanquer's 5 threshold schemas**: additive→emergent, continuous→discrete, static→dynamic, deterministic→probabilistic, centralized→decentralized

Synthesize into 4-6 domains where each:
- Answers exactly one governing question
- Passes the dissolution test (cannot be merged into another domain without losing explanatory power)
- Is needed for chemical literacy at the non-majors level (not just for STEM preparation)

**For each domain, provide:**
- Name (short, intuitive — not jargon)
- 3-letter code
- Governing question
- What is NOT in this domain (boundary statement)
- Why a non-major needs this (1 sentence)
- Dissolution argument (why this can't merge into another domain)

## Task 2 — Draw the Dependency DAG

Which domains require which others? The DAG determines chapter order.

Pay special attention to:
- Whether "Structure" or "Energy" comes first (mirrors the atoms-first vs. empirical-first debate, but at the reasoning level)
- Whether "Representation" (Johnstone's triplet) is its own domain or a crosscutting skill
- Where "Change/Reactivity" sits relative to structure and energy

Verify: the DAG is acyclic. For each edge, name at least one concept in the dependent domain that requires the prerequisite domain.

## Task 3 — For Each Domain, Enumerate 5-10 Candidate Primitives

These should be **reasoning moves**, not chemistry topics.

Example: in a "Structure→Property" domain, a primitive might be:
> **"Intermolecular force hierarchy"**: Given a molecular structure, identify the dominant intermolecular forces (London dispersion < dipole-dipole < hydrogen bonding < ionic) and predict the direction of a macroscopic property (boiling point, solubility, viscosity).

Each primitive should be:
- Statable in one sentence
- Deployable across multiple chemical contexts
- Teachable without calculus
- Typed as PRIM (irreducible) or DEF (derivable from other primitives in the domain)

Target: ~60-80 primitives total across all domains.

## Task 4 — Identify 3-5 Composition Patterns

Cross-domain reasoning chains that explain real phenomena a non-major might encounter.

**Example:** "Why does ice float?"
- Structure domain: Hydrogen bonding geometry creates an open lattice in solid water
- Energy domain: The entropy cost of ordering is offset by the enthalpy gain of hydrogen bonding below 0°C
- Emergence domain: Bulk density is an emergent property — the solid is less dense than the liquid because of molecular arrangement

**For each composition pattern, provide:**
- A real-world question a non-major might ask
- The domains involved
- The primitives composed
- A 2-3 sentence walkthrough of the reasoning chain

## Task 5 — The "Application Deployment" Pattern

For each composition pattern from Task 4, sketch:

1. **Name the primitives** being composed (make them visible to the student)
2. **Present the real-world question** (the hook)
3. **Walk through the composition** (show how primitives combine to answer the question)
4. **Give a second, different application** that uses the **same** composition (the "bridging" move that solves the situatedness paradox — students see the pattern transfer)

This is the pedagogical core: applications as exercises for named primitives, not as the organizational backbone.

---

## Constraints

- **4-6 domains**, each with 10-15 primitives → ~60-80 total
- **No calculus.** Algebra and proportional reasoning only.
- **One semester**: ~14 weeks, ~42 contact hours
- **ACS alignment**: Map coverage after design, not during
- **Language**: Domain names should be intuitive to a first-year student, not jargon ("How stuff is built" > "Molecular Architecture")

## Output Format

Follow `pipeline/06-TEMPLATES.md` §S1 for domain specs. Produce:
1. Domain spec table (name, code, question, boundary, dissolution argument)
2. Dependency DAG (ASCII)
3. Preliminary item list per domain (ID, name, type, 1-sentence description)
4. 3-5 composition patterns (template from `pipeline/06-TEMPLATES.md` §S5)
5. 3-5 worked application deployment patterns (Task 5)
