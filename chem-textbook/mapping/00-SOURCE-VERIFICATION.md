# Phase 2 Step 0: Source Verification Report

**Date:** 2026-02-14
**Gate status:** PASS (all 5 sources verified)

---

## Source Summary

| # | Source | Code | License | Format | Chapters | Sections | Status |
|---|--------|------|---------|--------|----------|----------|--------|
| 1 | OpenStax Chemistry 2e | OS | CC-BY 4.0 | CNXML (XML) | 21 | 114 content | GO |
| 2 | CLUE (Cooper & Klymkowsky) | CLUE | CC-BY-NC-SA 4.0 | HTML (Pressbooks) | 9 | 48 | GO |
| 3 | Saylor GOB (Ball et al.) | SAY | CC-BY-NC-SA | HTML (GitHub Pages) | 20 | ~224 files | GO |
| 4 | Chemistry in Context 10e (ACS) | CIC | Proprietary | TOC only | 14 | N/A | GO |
| 5 | ACS Exams content areas | ACS | Reference only | Web | N/A | N/A | GO |

---

## 0a. OpenStax Chemistry 2e

**Repo:** `openstax/osbooks-chemistry-bundle`
**Local path:** `chem-textbook/sources/openstax/osbooks-chemistry-bundle/`
**Collection file:** `collections/chemistry-2e.collection.xml`

### Module Breakdown
- Preface: 1
- Introductions: 21 (one per chapter)
- Content sections: 114
- Appendices: 13
- **Total in collection:** 149

### CNXML Structure
Modules are in `modules/m{NNNNN}/index.cnxml`. Key tags:
- `<document>` (root, with `class` attribute: content/introduction/appendix/preface)
- `<title>` — section title
- `<metadata>` — content-id, abstract (learning objectives), uuid
- `<content>` — body container
- `<section>` — subsections within a module
- `<para>`, `<list>`, `<table>`, `<figure>`, `<equation>` — content elements
- `<term>` — vocabulary terms (feeds glossary)
- `<example>`, `<exercise>`, `<problem>`, `<solution>` — pedagogical elements
- `<note>` — callout boxes
- `<m:math>` (MathML namespace) — 143 of 176 modules use MathML

### Media
- 1,543 media files (images: JPG, PNG, SVG)
- Referenced via `../../media/` relative paths

### License
CC-BY 4.0 International (maximum remix freedom)

### Sample Content Verified
Module `m68685` ("Early Ideas in Atomic Theory"): full prose readable, learning objectives extractable from `<md:abstract>`, Dalton's postulates with figures and examples. Content quality: high, suitable for adaptation.

---

## 0b. CLUE (Chemistry, Life, the Universe and Everything)

**URL:** https://openbooks.lib.msu.edu/clue/
**Curriculum site:** https://www.chemistry.msu.edu/clue/
**Authors:** Melanie Cooper & Michael Klymkowsky

### 4 Core Ideas
1. **Structure and Properties** — How does the structure of matter determine its properties?
2. **Bonding and Interactions** — What forces cause matter to interact?
3. **Energy** — What energy changes are involved in chemical processes?
4. **Change and Stability** — How and why do chemical systems change or remain stable?

Core ideas are woven throughout every chapter (NOT 1:1 mapped to chapters).

### Chapter List (9 chapters, 48 sections)

| Ch | Title | Sections |
|----|-------|----------|
| 1 | Atoms | 8 |
| 2 | Electrons and Orbitals | 7 |
| 3 | Elements, Bonding, and Physical Properties | 3 |
| 4 | Heterogeneous Compounds | 6 |
| 5 | Systems Thinking | 7 |
| 6 | Solutions | 6 |
| 7 | A Field Guide to Chemical Reactions | 6 |
| 8 | How Far? How Fast? | 6 |
| 9 | Reaction Systems | 5 |

### Key Differences from Traditional Texts
- Atoms-first approach
- Deliberately omits stoichiometry and electrochemistry
- Emphasizes causal mechanistic reasoning over algorithmic problem-solving
- Designed via iterative design research (not author expertise alone)
- "Questions to Answer" + "Questions to Ponder" embedded throughout

### Relevance to Our Project
CLUE's 4 core ideas map remarkably well to our domain taxonomy:
- Structure and Properties ≈ STR
- Bonding and Interactions ≈ STR (cross-domain with NRG)
- Energy ≈ NRG
- Change and Stability ≈ CHG (+ SCL for equilibrium aspects)

This alignment validates our domain decomposition independently.

---

## 0c. Saylor GOB (Basics of General, Organic, and Biological Chemistry)

**URL:** https://saylordotorg.github.io/text_the-basics-of-general-organic-and-biological-chemistry/
**GitHub:** `saylordotorg/text_the-basics-of-general-organic-and-biological-chemistry`
**Authors:** David W. Ball, John W. Hill, Rhonda J. Scott
**Format:** 224 HTML files, organized into numbered section directories
**License:** CC-BY-NC-SA (via Saylor Foundation / FlatWorld v1.0)

### Chapter List (20 chapters)

| Ch | Title | Domain Coverage |
|----|-------|----------------|
| 1 | Chemistry, Matter, and Measurement | General |
| 2 | Elements, Atoms, and the Periodic Table | General |
| 3 | Ionic Bonding and Simple Ionic Compounds | General |
| 4 | Covalent Bonding and Simple Molecular Compounds | General |
| 5 | Introduction to Chemical Reactions | General |
| 6 | Quantities in Chemical Reactions | General |
| 7 | Energy and Chemical Processes | General |
| 8 | Solids, Liquids, and Gases | General |
| 9 | Solutions | General |
| 10 | Acids and Bases | General |
| 11 | Nuclear Chemistry | General |
| 12 | Organic Chemistry: Alkanes and Halogenated Hydrocarbons | Organic |
| 13 | Unsaturated and Aromatic Hydrocarbons | Organic |
| 14 | Organic Compounds of Oxygen | Organic |
| 15 | Organic Acids and Bases and Some of Their Derivatives | Organic |
| 16 | Carbohydrates | Biological |
| 17 | Lipids | Biological |
| 18 | Amino Acids, Proteins, and Enzymes | Biological |
| 19 | Nucleic Acids | Biological |
| 20 | Energy Metabolism | Biological |

### Relevance
- One-semester non-majors text, audience-calibrated
- General chapters (1-11) overlap heavily with our taxonomy scope
- Organic/bio chapters (12-20) may map to E-tier items or application patterns
- Useful for validating non-majors scope boundaries

---

## 0d. Chemistry in Context, 10th Edition (ACS)

**Publisher:** McGraw-Hill / ACS
**License:** Proprietary (chapter-level mapping only, no content adaptation)

### Chapter List (14 chapters)

| Ch | Title | Societal Context | Core Chemistry Topics |
|----|-------|-----------------|----------------------|
| 1 | Portable Electronics: The Periodic Table in the Palm of Your Hand | Consumer electronics | Atoms, elements, periodic table, isotopes, ions, metals |
| 2 | The Air We Breathe | Air quality, pollution | Molecules, chemical formulas, Lewis structures, naming compounds |
| 3 | Radiation from the Sun | UV, ozone layer | EM spectrum, wavelength/frequency/energy, photochemistry |
| 4 | Climate Change | Global warming, carbon footprint | Greenhouse gases, molecular shapes, IR absorption, carbon cycle, ppm |
| 5 | Energy from Combustion | Fossil fuels | Thermochemistry, enthalpy, exo/endothermic, hydrocarbons, combustion |
| 6 | Energy from Alternative Sources | Solar, nuclear, hydrogen | Nuclear chemistry, fission/fusion, radioactivity, half-life |
| 7 | Energy Storage | Batteries, fuel cells | Electrochemistry, oxidation-reduction, voltaic cells |
| 8 | Water Everywhere: A Most Precious Resource | Water quality, access | Solutions, concentration, solubility, acids/bases, pH, H-bonding |
| 9 | The World of Polymers and Plastics | Plastics, recycling | Organic chemistry, polymerization, functional groups |
| 10 | Brewing and Chewing | Fermentation, food | Organic reactions, alcohols, acids, esters |
| 11 | Nutrition | Diet, food labels | Carbohydrates, fats, proteins, amino acids, food energy |
| 12 | Health and Medicine | Pharmaceuticals | Drug chemistry, chirality, drug mechanisms |
| 13 | Genes and Life | Genetics, GMOs | DNA, RNA, nucleotides, protein synthesis, genetic code |
| 14 | Who Killed Dr. Thompson? A Forensic Mystery | Forensic science | Integration of all prior chemistry |

### Pedagogical Approach
Chemistry is introduced on a "need-to-know" basis. Each chapter opens with a societal issue; chemistry required to understand it is taught in that chapter. Core topics are distributed across chapters rather than front-loaded.

### Relevance
CIC is the gold standard for non-majors chemistry. Its 14-chapter context-driven structure validates our composition patterns (CP-001 through CP-007) and application deployment patterns. The "need-to-know" approach aligns with our reasoning-move framing.

---

## 0e. ACS Exam Content Areas

### Most Appropriate Exam for Non-Majors
**CT09 — Chemistry in Context (2009)**: 48 items, core from Ch 1-6 of CIC. This is the only ACS exam specifically designed for CiC-style courses. However, it dates from 2009 and may not align perfectly with the 10e reorganization.

**Alternative:** PC25 — Preparatory Chemistry (2025): 50 items, 60 min. 9 content areas (measurement/matter, atomic structure, electronic structure, bonding, formula calculations, stoichiometry, solutions, gases, heat).

**Not appropriate:** GOB exams (GB25D etc.) — designed for nursing/allied health, not liberal-arts non-majors.

### ACS General Chemistry Content Areas (16 topics, for reference)

| # | Content Area |
|---|-------------|
| 1 | Atomic Structure (atoms, molecules, ions) |
| 2 | Electronic Structure |
| 3 | Formula Calculations and the Mole |
| 4 | Stoichiometry |
| 5 | Solutions and Aqueous Reactions, Part 1 |
| 6 | Heat and Enthalpy |
| 7 | Structure and Bonding |
| 8 | States of Matter |
| 9 | Solutions and Aqueous Reactions, Part 2 |
| 10 | Kinetics |
| 11 | Equilibrium |
| 12 | Acids and Bases |
| 13 | Solubility Equilibria |
| 14 | Thermodynamics |
| 15 | Electrochemistry |
| 16 | Nuclear Chemistry |

### ACS Anchoring Concepts Content Map (ACCM) — 10 Big Ideas
1. Atoms
2. Bonding
3. Structure and Function
4. Intermolecular Forces
5. Reactions
6. Energy and Thermodynamics
7. Kinetics
8. Equilibrium
9. Measurement and Data
10. Visualization and Scale

### Mapping to Our Taxonomy Domains

| ACCM Concept | Our Domain(s) |
|-------------|--------------|
| Atoms | COM |
| Bonding | STR |
| Structure and Function | STR, COM |
| Intermolecular Forces | STR |
| Reactions | CHG |
| Energy and Thermodynamics | NRG |
| Kinetics | CHG |
| Equilibrium | CHG, SCL |
| Measurement and Data | SCL |
| Visualization and Scale | SCL, COM |

This rough mapping shows good alignment between the 10 ACCM concepts and our 5 domains. All domains have ACCM coverage.

---

## Gate Decision

| Criterion | Required | Result |
|-----------|----------|--------|
| OpenStax accessible + section-readable | MUST | PASS |
| CIC chapter list obtained | MUST | PASS |
| CLUE structure obtained | SHOULD | PASS |
| Saylor accessible | NICE TO HAVE | PASS |
| ACS content areas identified | SHOULD | PASS |

**VERDICT: ALL PASS. Proceed to Step 1 (Section Inventories + Chapter Triage).**
