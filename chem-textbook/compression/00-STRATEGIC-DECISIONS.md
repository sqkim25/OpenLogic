# Phase 3: Strategic Decisions

**Date:** 2026-02-14
**Depends on:** Phase 2 deliverables (mapping/00-05), Phase 1 taxonomy (taxonomy/*)
**Purpose:** Resolve 5 open questions from Phase 2 Section 7 + establish notation concordance. All downstream Phase 3 artifacts (chapter architecture, content directives) depend on these decisions.

---

## Decision 1: NC-SA Licensing Strategy

### Problem

Three taxonomy items have canonical sources under CC-BY-NC-SA licenses:

| Item | Canonical Source | License | Why Canonical |
|------|-----------------|---------|--------------|
| DEF-STR008 (polymer reasoning) | Saylor GOB Ch 15-19 | CC-BY-NC-SA | OS SKIPped this at non-majors level |
| DEF-STR009 (metallic structure, E) | CLUE 3.3 | CC-BY-NC-SA | OS SKIPped Ch 18 entirely |
| DEF-SCL005 (safety/risk reasoning) | Saylor GOB Ch 11 | CC-BY-NC-SA | OS covers radiation only; needs broadening |

If we adapt NC-SA content, the derivative work inherits the NC-SA license, constraining the textbook's reuse.

### Resolution: WRITE-ORIGINAL for all 3

**Rationale**: Keeping the entire textbook under CC-BY 4.0 maximizes adoption and remix potential. The 3 affected items are well-specified in the taxonomy — each has a reasoning-move formulation, dependencies, real-world hook, and semi-formal statement in the domain spec. This provides sufficient input for original writing without needing to adapt NC-SA prose.

**Clean-room protocol**: For WRITE-ORIGINAL items, Phase 4 writers MUST NOT read the NC-SA source text during writing. Use only:
1. The taxonomy item spec (DOMAIN-{CODE}.md)
2. General chemistry knowledge
3. CC-BY sources (OS) for background context

This avoids unconscious structural copying.

### SYNTHESIZE Licensing Rule

For items where SYNTHESIZE combines CC-BY (OS) + CC-BY-NC-SA (CLUE/SAY):
- Written content MUST be based on OS (CC-BY) material
- CLUE/SAY inform the pedagogical approach (which aspects to emphasize, how to frame the reasoning move) only
- No prose borrowed from NC-SA sources
- **Threshold**: Ideas and pedagogical strategies are not copyrightable. Selection, arrangement, and expression of content are. Use OS for content; CLUE/SAY for emphasis decisions.

---

## Decision 2: REWRITE Depth Calibration

### Problem

16 OpenStax sections need simplification for non-majors (REWRITE signal in Phase 2). Without a calibration standard, Phase 4 writers will make inconsistent depth decisions across chapters.

### Resolution: Non-Majors Depth Ceiling

**Mathematical operations allowed**:
- Proportional reasoning (e.g., "if you double the concentration, the rate increases")
- Basic algebra (solve for x in simple equations)
- Logarithms — pH only (pH = -log[H+], explained conceptually as "each pH unit is a tenfold change")
- Balanced chemical equations (qualitative reading: "one molecule of X produces two of Y")
- Unit conversions with dimensional analysis

**Mathematical operations stripped**:
- Calculus-based derivations (rate laws, integrated rate expressions)
- ICE tables (equilibrium calculations)
- Integrated rate laws (first/second order kinetics)
- Ksp, Ka, Kb calculations
- Molecular orbital diagrams and calculations
- Electron configurations beyond valence count (no aufbau, Hund's rule)
- Quantitative ΔG = ΔH - TΔS (retain direction only)
- Stoichiometric mole-to-mole calculations (retain concept, strip multi-step calculations)

**Concepts retained qualitatively**:
- ΔG direction: "this process is spontaneous" / "this process is not spontaneous" — without computing ΔG
- Equilibrium shift: Le Chatelier's principle (qualitative direction only, no Kc manipulation)
- Bond energy comparison: "stronger bonds store more energy" — no kJ/mol calculations
- Reaction rates: "higher temperature = faster reaction" — no rate law equations
- Enthalpy: "energy in > energy out = exothermic" — no Hess's law summations

### Anchor REWRITE Example

**OS Section 5.3 (Enthalpy)** — REWRITE from:
- Full Hess's law with multi-step enthalpy calculations, standard enthalpies of formation tables, ΔH°rxn = ΣΔH°f(products) - ΣΔH°f(reactants)

To:
- Conceptual: "Every chemical bond stores energy. Breaking bonds costs energy (endothermic); forming bonds releases energy (exothermic). If the energy released by forming new bonds exceeds the energy cost of breaking old bonds, the overall reaction is exothermic — the system releases energy to the surroundings."
- One energy diagram (reactants vs. products energy levels, ΔH arrow)
- Real-world hook: "Why does a campfire give off heat?"
- No Hess's law, no formation tables, no multi-step calculations

---

## Decision 3: PRIM-COM008 Scaffolding

### Problem

PRIM-COM008 (causal chain reasoning) is the only item with META status in the coverage matrix — no source text has a standalone section teaching it. Yet it is referenced by all 4 downstream domains (STR, NRG, CHG, SCL).

### Resolution: Distributed Scaffolding

PRIM-COM008 is not a content topic — it is a metacognitive skill. It does not get its own dedicated chapter section (which would feel like "how to think" instruction divorced from chemistry). Instead:

**Scaffolding approach**:
1. **Introduction in COM.5**: A brief "Thinking in Chains" section at the end of Chapter 1 (COM) that names the reasoning pattern: "Given an observation, identify the relevant primitives, connect them in a causal sequence, and arrive at a conclusion."
2. **"Questions to Answer" prompts**: Every subsequent domain chapter includes 2-3 prompts that model the causal chain explicitly. Format: "Why does [observation]?" → Step 1: Name the relevant primitive → Step 2: Apply it → Step 3: Connect to the next primitive → Step 4: Arrive at the conclusion.
3. **Worked examples**: 2-3 fully worked causal chain examples spread across Chapters 2-5, marked with a distinctive icon/label ("Reasoning Chain"). These make the metacognitive process visible.
4. **CP deployment as capstone chains**: Composition patterns (CP-001 through CP-006) ARE multi-step causal chains. Each CP deployment section IS a PRIM-COM008 exercise. No separate treatment needed — the CPs are the scaffolding.

---

## Decision 4: CP Deployment Plan

### Problem

7 composition patterns must be placed in the chapter sequence. Each CP requires all its participating domains to have been introduced. The linearization COM → STR → NRG → SCL → CHG constrains placement.

### Resolution: End-of-Chapter Capstones

CPs deploy as **capstone sections at the end of the chapter that completes their dependency chain**. This keeps domain content contiguous (no mid-chapter fragmentation) and frames CPs as "now apply what you learned."

| CP | Name | Domains | Deploys At | Section Type |
|----|------|---------|-----------|--------------|
| CP-001 | Structure-to-Property Prediction | STR x SCL | End of Ch 4 (SCL) | Capstone |
| CP-004 | Greenhouse Effect | STR x NRG x SCL | End of Ch 4 (SCL) | Capstone |
| CP-002 | Energy-Driven Transformation | NRG x CHG | End of Ch 5 (CHG) | Capstone |
| CP-003 | Acid-Base in the Body | STR x CHG x SCL | End of Ch 5 (CHG) | Capstone |
| CP-005 | Dose Makes the Poison | STR x CHG x SCL | End of Ch 5 (CHG) | Capstone |
| CP-006 | Food Chemistry | COM x NRG x CHG x SCL | End of Ch 5 (CHG) | Capstone |
| CP-007 | Biochemistry Connection | STR x CHG x SCL | Ch 6 (standalone, E-tier) | Standalone |

### Dependency Verification

| CP | Prerequisite Domains | Available at deployment? |
|----|---------------------|------------------------|
| CP-001 | STR (Ch 2), SCL (Ch 4) | Ch 4 end: STR ✓, SCL ✓ |
| CP-004 | STR (Ch 2), NRG (Ch 3), SCL (Ch 4) | Ch 4 end: all ✓ |
| CP-002 | NRG (Ch 3), CHG (Ch 5) | Ch 5 end: all ✓ |
| CP-003 | STR (Ch 2), CHG (Ch 5), SCL (Ch 4) | Ch 5 end: all ✓ |
| CP-005 | STR (Ch 2), CHG (Ch 5), SCL (Ch 4) | Ch 5 end: all ✓ |
| CP-006 | COM (Ch 1), NRG (Ch 3), CHG (Ch 5), SCL (Ch 4) | Ch 5 end: all ✓ |
| CP-007 | STR (Ch 2), CHG (Ch 5), SCL (Ch 4) | Ch 6: all ✓ |

**Zero dependency violations.**

### Pedagogical Rationale

- **End-of-chapter** (not mid-chapter): Students need all domain primitives before seeing how they compose. Interleaving CPs mid-chapter fragments the domain narrative and confuses students about whether they're learning new content or applying existing content.
- **Ch 4 gets 2 CPs** (CP-001, CP-004): Both become available when SCL completes the chain. CP-001 (boiling point prediction) is the simplest cross-domain pattern; CP-004 (greenhouse effect) is the most personally relevant. Placing them back-to-back in Ch 4 demonstrates that the same reasoning framework (STR + SCL) extends to completely different phenomena.
- **Ch 5 gets 4 CPs**: CHG is the terminal domain — it unlocks the most cross-domain patterns. The 4 CPs (acid-base, energy-driven transformation, dose/toxicity, food chemistry) form a thematic set: "chemistry in your daily life." This is the climactic payoff of the course.
- **Ch 6 standalone**: CP-007 (biochemistry) is E-tier and requires extended setup (polymer reasoning, macromolecule structure). Courses with time can include it; others can omit Ch 6 entirely without breaking the Core.

### ADP Deployment

Each CP capstone section uses its corresponding Application Deployment Pattern (ADP-001 through ADP-007) from APPLICATION-PATTERNS.md. The four-step pedagogy (name primitives → hook → walkthrough → bridge) is the uniform format for all CP capstone sections.

---

## Decision 5: E-Tier Inclusion and Expendability

### Problem

8 E-tier items have source coverage but may be cut under 14-week semester time pressure. Need a prioritized cut order so instructors know which to drop first.

### E-Tier Registry

| Rank | ID | Name | Domain | Sources | CP Use | Expendability |
|------|-----|------|--------|---------|--------|---------------|
| 1 | DEF-CHG005 | Precipitation | CHG | OS only (1) | None | **Most expendable**: single source, absent from all reformed curricula, no downstream dependents |
| 2 | DEF-STR009 | Metallic structure | STR | CLUE, SAY (2) | None | No downstream Core dependents; OS gap; NC-SA licensing |
| 3 | DEF-SCL003 | Ideal gas reasoning | SCL | OS, SAY (2) | None | Absent from CLUE and CIC; quantitative PV=nRT may exceed scope |
| 4 | DEF-SCL004 | Colligative properties | SCL | OS, SAY (2) | None | Absent from CLUE and CIC; specialized application; but strong real-world hooks |
| 5 | DEF-NRG004 | Free energy (conceptual) | NRG | OS, CLUE (2) | None directly | PRIM-NRG005 (Core) already provides spontaneity reasoning; DEF-NRG004 formalizes without adding new logic |
| 6 | DEF-COM004 | Percent composition | COM | OS, SAY (2) | None | Absent from CLUE, CIC; narrow quantitative focus |
| 7 | DEF-COM003 | Molecular vs. empirical formula | COM | OS, SAY (2) | None | DEF-COM004 depends on this; if both cut, remove as pair |
| 8 | PRIM-CHG007 | Nuclear change reasoning | CHG | OS, SAY, CIC (3) | None | Strong real-world relevance (nuclear power, medical imaging); highest student interest among E-tier; **least expendable** |

Plus **CP-007** (Biochemistry Connection, E-tier pattern) — cut with Ch 6 as a unit.

### Expendability Criteria

1. **CP participation**: Items used by no CP → more expendable (all 8 E-tier items have zero CP participation)
2. **Source coverage**: Single-source items → more expendable (DEF-CHG005 is the weakest)
3. **Reformed curriculum validation**: Items absent from CLUE AND CIC → more expendable (CLUE and CIC are the most pedagogically aligned sources)
4. **Student engagement**: Narrow/technical topics → more expendable; personally relevant topics → less expendable
5. **Dependency chain**: Items with E-tier dependents form expendable pairs (DEF-COM003 + DEF-COM004)

### Resolution

**Keep all 8 in the architecture** — each gets a section and a content directive. Mark each as "E-tier: may be omitted without breaking Core dependency chains." The cut order above guides instructors making time-constrained decisions.

**Core-only mode**: A 12-week fast-track version of the course would include Ch 1-5 with only Core items (54 items, 6 Core CPs). Ch 6 and all 8 E-tier sections would be omitted. This produces a complete, dependency-coherent sub-textbook.

---

## Notation Concordance

### Purpose

Ensure consistent terminology and notation across all Phase 4 writing. All writers reference this concordance.

### Concordance Table (10 categories)

| # | Category | Decision | Rationale |
|---|----------|----------|-----------|
| 1 | **Formula representation** | Molecular formulas (H₂O, CO₂, NaCl) throughout. Lewis structures in STR chapter only (STR.2-STR.3). Skeletal/line structures for organic molecules in STR.5 only. | Non-majors need readable formulas. Lewis structures serve a specific pedagogical purpose (visualizing electron sharing) and should not appear before they are taught. |
| 2 | **Charge notation** | Superscript: Na⁺, Cl⁻, Ca²⁺. For polyatomic ions: SO₄²⁻. Never Na+, Na(1+). | Standard chemistry convention; superscript is visually cleaner. |
| 3 | **Energy units** | kJ for thermochemistry. Calories (capital C = kcal) for food/metabolism contexts. Always include units. Never bare numbers for energy. | Dual system matches student experience: kJ is the scientific standard, Calories appear on food labels. First use of either includes parenthetical equivalence. |
| 4 | **Enthalpy notation** | ΔH for all enthalpy changes. No subscripts (rxn, f, etc.) unless explicitly comparing reaction vs. formation enthalpy. Standard conditions (25 °C, 1 atm) assumed unless stated. | Simplified for non-majors. The ΔH°rxn vs ΔH°f distinction is a MAJORS concern. |
| 5 | **Concentration** | "concentration" in prose. M (with explanation "moles per liter") in equations and quantitative contexts. mol/L parenthetical on first use of M. Square brackets [X] NOT used (MAJORS convention). | M is the standard shorthand. Square brackets are equilibrium-expression notation that non-majors do not need. |
| 6 | **Dilute quantities** | ppm (parts per million) throughout for trace concentrations. mg/L parenthetical on first use (noting 1 ppm ≈ 1 mg/L in dilute aqueous solutions). ppb for very low concentrations (e.g., contaminants). | ppm is the public-facing unit (EPA water reports, air quality indices). Students encounter ppm in daily life. |
| 7 | **Temperature** | °C for everyday and laboratory contexts. K (kelvin) only when required by a specific relationship (gas laws, thermodynamics). First use of K includes the conversion: K = °C + 273. | Non-majors think in Celsius. Kelvin is introduced as needed, not used by default. |
| 8 | **Electron representation** | Dots for lone pairs in Lewis structures. Lines (—) for covalent bonds. Double lines (=) for double bonds. Triple lines (≡) for triple bonds. Partial charges as δ+ and δ−. | Standard Lewis structure convention. δ notation is widely used and intuitive. |
| 9 | **Typesetting** | Unicode subscripts/superscripts in running text (H₂O, Na⁺). Standard chemical equation formatting: reactants → products (right arrow, not equals sign). State symbols (s), (l), (g), (aq) in parentheses after formulas in equations. | Right arrow emphasizes that chemical change is a process, not an algebraic equality. |
| 10 | **Element symbols and naming** | Standard IUPAC 1-2 letter symbols (H, He, Na, Cl). Full element name on first use in each chapter. Common names for familiar compounds: "water" (not "dihydrogen monoxide"), "table salt" (not "sodium chloride") in introductory contexts; systematic name provided parenthetically. | Non-majors respond to common names. Systematic naming is out of scope (see Phase 2 gap analysis §1b). |

### Potential Overloaded Symbols

| Symbol | Meaning 1 | Meaning 2 | Resolution |
|--------|-----------|-----------|------------|
| R | Gas constant (8.314 J/mol·K) | Generic organic group in structural formulas | Use italic *R* with units for gas constant; non-italic R- for organic groups. Context disambiguates in practice; this is standard chemistry usage. |
| M | Molar mass (g/mol) | Molarity (mol/L) | Use "molar mass" written out; M only for molarity. This avoids confusion. |
| n | Number of moles | Principal quantum number | Non-majors text does not use quantum numbers (out of scope). No ambiguity in practice. |

---

## Summary of Decisions

| # | Decision | Resolution | Impact |
|---|----------|-----------|--------|
| 1 | NC-SA licensing | WRITE-ORIGINAL for DEF-STR008, DEF-STR009, DEF-SCL005 | Textbook remains CC-BY 4.0 |
| 2 | REWRITE depth | Explicit ceiling: allow proportional reasoning + pH logarithms; strip all calculus, ICE tables, integrated rate laws | Consistent depth across 16 REWRITE sections |
| 3 | COM008 scaffolding | Distributed: COM.5 introduction + "Questions to Answer" prompts + worked reasoning chains + CPs as capstone chains | No standalone metacognition section; skill woven throughout |
| 4 | CP deployment | End-of-chapter capstones: 2 CPs at end of Ch 4, 4 CPs at end of Ch 5, CP-007 in Ch 6 (E-tier) | Domain content stays contiguous; CPs as application payoff |
| 5 | E-tier inclusion | All 8 kept; prioritized cut order for time-constrained courses; Core-only mode documented | Instructors can make informed cuts |
